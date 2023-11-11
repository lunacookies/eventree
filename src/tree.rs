mod tag;

use self::tag::Tag;
use crate::{SyntaxNode, SyntaxToken, TextRange, TreeConfig};
use std::fmt;
use std::marker::PhantomData;
use std::num::NonZeroU32;
use std::ops::{Add, AddAssign, Deref};
use std::sync::atomic::{AtomicU32, Ordering};

/// `SyntaxTreeBuf` owns the syntax tree allocation.
/// To construct a tree, see [`SyntaxBuilder`].
/// To access its contents, see [`SyntaxTree`]’s methods.
pub struct SyntaxTreeBuf<C> {
    data: Box<SyntaxTree<C>>,
}

/// `SyntaxTree` stores the syntax tree.
/// To construct a tree, see [`SyntaxBuilder`].
/// To access its contents, see [`SyntaxTree::root`].
///
/// `SyntaxTree`, like all other `Syntax*` types, is generic over a [`TreeConfig`],
/// which specifies how the kinds of nodes and tokens
/// can be converted between the library consumer’s custom enum and a raw concrete type.
///
/// # Format
///
/// The in-memory format of the syntax tree as described below
/// is subject to change and an implementation detail.
///
/// The tree has four sections:
///
/// - `u32` ID
/// - `u32` length of text
/// - `[u8]` UTF-8 encoded text
/// - `[u8]` events
///
/// These are stored contiguously in one memory allocation.
/// Nodes and tokens are a `u32` byte index into this allocation.
/// All numerical types are stored in the target platform’s native endianness.
///
/// ## ID
///
/// To ensure nodes and tokens are only used with the tree they were created from,
/// every tree is assigned a `u32` ID from an atomic global counter.
/// Nodes and tokens both store the ID of their tree,
/// which is checked when node or token data is accessed.
///
/// ## Text
///
/// The text of the entire source file must be provided upfront,
/// allowing it to be stored efficiently all in one place.
/// This makes getting the text of nodes and tokens incredibly cheap:
/// we can just index into the text section of the tree
/// using the range of the node or token.
///
/// ## Events
///
/// Following the name of this library,
/// the tree is stored as a flat sequence of events.
/// The encoding is as follows:
///
/// - *start node* (14 bytes):
///   - `u16` tag
///   - `u32` index of first event following the end of this node
///   - `u32` range start
///   - `u32` range end
/// - *add token* (10 bytes):
///   - `u16` tag
///   - `u32` range start
///   - `u32` range end
///
/// A separate *finish node* event kind is unnecessary
/// because *start node* events store where such an event would be located.
///
/// ### Tag
///
/// Simplistically, the tag is the following type,
/// but packed into a single `u16`.
///
/// ```
/// # type Kind = u16;
/// enum Tag { StartNode(Kind), AddToken(Kind) }
/// ```
///
/// *start node* or *add token* are distinguished by the highest bit:
/// `1` means *start node*, and `0` means *add token*.
/// The remaining fifteen bits store the kind.
#[repr(transparent)]
pub struct SyntaxTree<C> {
    phantom: PhantomData<C>,
    data: [u8],
}

/// This type is used to construct a [`SyntaxTree`].
///
/// Due to the custom in-memory format used for [`SyntaxTree`],
/// the text of your entire input must be provided up-front in [`SyntaxBuilder::new`].
pub struct SyntaxBuilder<C> {
    data: Vec<u8>,
    is_root_set: bool,
    current_len: u32,
    start_node_idxs: Vec<usize>,
    nesting: u32,
    phantom: PhantomData<C>,
}

pub(crate) const START_NODE_SIZE: EventSize = EventSize(std::mem::size_of::<RawStartNode>() as u32);
pub(crate) const ADD_TOKEN_SIZE: EventSize = EventSize(std::mem::size_of::<RawAddToken>() as u32);

const FINISH_NODE_IDX_PLACEHOLDER: u32 = 0;

fn gen_tree_id() -> u32 {
    static CURRENT: AtomicU32 = AtomicU32::new(0);
    CURRENT.fetch_add(1, Ordering::Relaxed)
}

impl<C: TreeConfig> SyntaxBuilder<C> {
    /// Constructs a new empty `SyntaxBuilder` with the provided source text.
    pub fn new(text: &str) -> Self {
        Self::with_capacity(text, 0, 0)
    }

    /// Constructs a new empty `SyntaxBuilder` with the provided source text
    /// and room for the specified event counts.
    ///
    /// Make sure to benchmark before switching to this method
    /// because precomputing event counts can be slow,
    /// even slower than just using [`SyntaxBuilder::new`].
    pub fn with_capacity(text: &str, start_nodes: usize, add_tokens: usize) -> Self {
        assert!(text.len() < u32::MAX as usize);

        let id = gen_tree_id();

        let mut data = Vec::with_capacity(
            4 + 4
                + text.len()
                + start_nodes * START_NODE_SIZE.to_usize()
                + add_tokens * ADD_TOKEN_SIZE.to_usize(),
        );

        data.extend_from_slice(&id.to_ne_bytes());
        data.extend_from_slice(&(text.len() as u32).to_ne_bytes());
        data.extend_from_slice(text.as_bytes());

        Self {
            data,
            is_root_set: false,
            current_len: 0,
            start_node_idxs: Vec::new(),
            nesting: 0,
            phantom: PhantomData,
        }
    }

    /// Starts a new node with the specified kind.
    ///
    /// # Panics
    ///
    /// - if you have finished creating a root node and try to create another
    #[inline(always)]
    pub fn start_node(&mut self, kind: C::NodeKind) {
        if self.is_root_set {
            assert_ne!(self.nesting, 0, "root node already created");
        } else {
            self.is_root_set = true;
        }

        self.nesting += 1;

        self.start_node_idxs.push(self.data.len());

        self.data.reserve(START_NODE_SIZE.to_usize());
        unsafe {
            self.end_ptr().cast::<RawStartNode>().write_unaligned(RawStartNode {
                tag: Tag::start_node::<C>(kind),
                finish_node_idx: FINISH_NODE_IDX_PLACEHOLDER,
                start: self.current_len,
                end: self.current_len,
            });

            self.data.set_len(self.data.len() + START_NODE_SIZE.to_usize());
        }
    }

    /// Adds a token with the provided kind and range to the current node.
    ///
    /// # Panics
    ///
    /// - if you try to add a token before starting a node
    /// - if the provided range is out of bounds
    /// - if the provided range does not lie on a UTF-8 character boundary
    #[inline(always)]
    pub fn add_token(&mut self, kind: C::TokenKind, range: TextRange) {
        assert!(self.nesting > 0, "cannot add token before starting node");

        assert!(
            u32::from(range.end()) <= self.text_len(),
            "token is out of range: range is {range:?}, but text is 0..{}",
            self.text_len()
        );

        let all_text = self.all_text();
        assert!(
            all_text.is_char_boundary(u32::from(range.start()) as usize)
                && all_text.is_char_boundary(u32::from(range.end()) as usize),
            "tried to create token that does not lie on UTF-8 character boundary"
        );

        let start = u32::from(range.start());
        let end = u32::from(range.end());
        self.current_len = end;

        self.data.reserve(ADD_TOKEN_SIZE.to_usize());

        unsafe {
            self.end_ptr().cast::<RawAddToken>().write_unaligned(RawAddToken {
                tag: Tag::add_token::<C>(kind),
                start,
                end,
            });

            self.data.set_len(self.data.len() + ADD_TOKEN_SIZE.to_usize());
        }
    }

    /// Completes the current node and makes the parent node current.
    ///
    /// # Panics
    ///
    /// - if all outstanding nodes have already been finished
    #[inline(always)]
    pub fn finish_node(&mut self) {
        assert!(self.nesting > 0, "no nodes are yet to be finished");
        self.nesting -= 1;

        let start_node_idx = self.start_node_idxs.pop().unwrap();
        let finish_node_idx = self.data.len() as u32;

        unsafe {
            let ptr = &mut *self.data.as_mut_ptr().add(start_node_idx).cast::<RawStartNode>();
            debug_assert_eq!(ptr.tag.event_kind(), EventKind::StartNode);

            // debug_assert_eq tries to take a reference to the field,
            // which isn’t allowed since it’s packed,
            // so we use a manual debug_assert instead
            debug_assert!(ptr.finish_node_idx == FINISH_NODE_IDX_PLACEHOLDER);

            ptr.finish_node_idx = finish_node_idx;
            ptr.end = self.current_len;
        }
    }

    /// Completes the tree and freezes it into the read-only [`SyntaxTreeBuf`] type.
    ///
    /// # Panics
    ///
    /// - if no nodes have been created
    /// - if there are nodes which have not been finished
    pub fn finish(self) -> SyntaxTreeBuf<C> {
        let Self { data, is_root_set, current_len: _, start_node_idxs: _, nesting, phantom: _ } =
            self;

        assert!(is_root_set, "no nodes created");

        assert_eq!(nesting, 0, "did not finish all nodes ({nesting} unfinished nodes)");

        // into_boxed_slice calls shrink_to_fit for us
        SyntaxTreeBuf {
            data: unsafe {
                std::mem::transmute::<Box<[u8]>, Box<SyntaxTree<C>>>(data.into_boxed_slice())
            },
        }
    }

    fn all_text(&self) -> &str {
        let len = self.text_len() as usize;
        unsafe {
            let s = self.data.get_unchecked(8..len + 8);

            // has to stay unchecked even in debug mode
            // since this method is called every time a token is added
            //
            // if we perform an operation in this method that depends on the input size,
            // then tree construction becomes O(n^2)
            // (since input size and the number of tokens are roughly proportional)
            std::str::from_utf8_unchecked(s)
        }
    }

    fn text_len(&self) -> u32 {
        unsafe { self.data.as_ptr().cast::<u32>().add(1).read_unaligned() }
    }

    fn end_ptr(&mut self) -> *mut u8 {
        unsafe { self.data.as_mut_ptr().add(self.data.len()) }
    }
}

impl<C: TreeConfig> SyntaxTree<C> {
    /// Returns the root node of this tree.
    pub fn root(&self) -> SyntaxNode<C> {
        unsafe { SyntaxNode::new(self.root_idx(), self.id()) }
    }

    /// Returns an iterator over the events stored in this tree.
    ///
    /// The difference between this method and [`SyntaxTree::raw_events`] is that
    /// this method returns [`SyntaxNode`]s and [`SyntaxToken`]s,
    /// while [`SyntaxTree::raw_events`] returns the data actually stored in the tree.
    pub fn events(&self) -> impl Iterator<Item = Event<C>> + '_ {
        Events { idx: self.root_idx(), tree: self, finish_node_idxs: Vec::new() }
    }

    /// Returns an iterator over the raw events stored in this tree.
    ///
    /// As compared to [`SyntaxTree::events`],
    /// this method emits the data actually stored in the tree,
    /// as opposed to handles to that data ([`SyntaxNode`]s and [`SyntaxToken`]s).
    ///
    /// This method does not compute any more information
    /// than what is stored in the tree.
    /// The only difference between the [`RawEvent`]s returned by this method
    /// and what is stored inside the tree
    /// is that the events returned by this method are fixed-length and typed,
    /// while the tree’s internal storage is variable-length and untyped.
    pub fn raw_events(&self) -> impl Iterator<Item = RawEvent<C>> + '_ {
        RawEvents { idx: self.root_idx(), tree: self, finish_node_idxs: Vec::new() }
    }

    pub(crate) fn root_idx(&self) -> EventIdx {
        unsafe {
            let text_len = self.data.as_ptr().cast::<u32>().add(1).read_unaligned();
            EventIdx::new(text_len + 8)
        }
    }

    pub(crate) fn id(&self) -> u32 {
        unsafe { self.data.as_ptr().cast::<u32>().read_unaligned() }
    }

    pub(crate) unsafe fn get_text(&self, start: u32, end: u32) -> &str {
        let start = start as usize + 8;
        let end = end as usize + 8;

        let slice = self.data.get_unchecked(start..end);

        if cfg!(debug_assertions) {
            std::str::from_utf8(slice).unwrap()
        } else {
            std::str::from_utf8_unchecked(slice)
        }
    }

    pub(crate) unsafe fn get_start_node(&self, idx: EventIdx) -> StartNode<C> {
        let idx = idx.0.get() as usize;
        debug_assert!(idx + START_NODE_SIZE.to_usize() <= self.data.len());

        let ptr = self.data.as_ptr().add(idx).cast::<RawStartNode>();
        let raw = ptr.read_unaligned();

        StartNode {
            kind: raw.tag.get_start_node_kind::<C>(),
            finish_node_idx: EventIdx::new(raw.finish_node_idx),
            start: raw.start,
            end: raw.end,
        }
    }

    pub(crate) unsafe fn get_add_token(&self, idx: EventIdx) -> AddToken<C> {
        let idx = idx.0.get() as usize;
        debug_assert!(idx + ADD_TOKEN_SIZE.to_usize() <= self.data.len());

        let ptr = self.data.as_ptr().add(idx).cast::<RawAddToken>();
        let raw = ptr.read_unaligned();

        AddToken { kind: raw.tag.get_add_token_kind::<C>(), start: raw.start, end: raw.end }
    }

    pub(crate) unsafe fn event_kind(&self, idx: EventIdx) -> EventKind {
        self.tag_at_idx(idx).event_kind()
    }

    fn tag_at_idx(&self, idx: EventIdx) -> Tag {
        let idx = idx.0.get() as usize;
        debug_assert!(idx < self.data.len());
        unsafe { self.data.as_ptr().add(idx).cast::<Tag>().read_unaligned() }
    }
}

impl<C> SyntaxTreeBuf<C> {
    /// Returns a reference to the contained syntax tree data.
    pub fn as_tree(&self) -> &SyntaxTree<C> {
        &self.data
    }
}

impl<C> Deref for SyntaxTreeBuf<C> {
    type Target = SyntaxTree<C>;

    fn deref(&self) -> &Self::Target {
        self.as_tree()
    }
}

#[repr(C, packed)]
pub(crate) struct StartNode<C: TreeConfig> {
    pub(crate) kind: C::NodeKind,
    pub(crate) finish_node_idx: EventIdx,
    pub(crate) start: u32,
    pub(crate) end: u32,
}

#[repr(C, packed)]
struct RawStartNode {
    tag: Tag,
    finish_node_idx: u32,
    start: u32,
    end: u32,
}

#[repr(C, packed)]
pub(crate) struct AddToken<C: TreeConfig> {
    pub(crate) kind: C::TokenKind,
    pub(crate) start: u32,
    pub(crate) end: u32,
}

#[repr(C, packed)]
struct RawAddToken {
    tag: Tag,
    start: u32,
    end: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EventIdx(NonZeroU32);

impl EventIdx {
    pub(crate) unsafe fn new(idx: u32) -> Self {
        if cfg!(debug_assertions) {
            Self(NonZeroU32::new(idx).unwrap())
        } else {
            Self(NonZeroU32::new_unchecked(idx))
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct EventSize(u32);

impl EventSize {
    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl Add<EventSize> for EventIdx {
    type Output = Self;

    fn add(self, rhs: EventSize) -> Self::Output {
        unsafe { Self::new(self.0.get() + rhs.0) }
    }
}

impl AddAssign<EventSize> for EventIdx {
    fn add_assign(&mut self, rhs: EventSize) {
        *self = *self + rhs;
    }
}

#[derive(Debug, PartialEq)]
pub(crate) enum EventKind {
    StartNode,
    AddToken,
}

struct Events<'a, C> {
    idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    finish_node_idxs: Vec<EventIdx>,
}

impl<C: TreeConfig> Iterator for Events<'_, C> {
    type Item = Event<C>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finish_node_idxs.last().copied() == Some(self.idx) {
            self.finish_node_idxs.pop();
            return Some(Event::FinishNode);
        }

        if self.idx.0.get() >= self.tree.data.len() as u32 {
            return None;
        }

        match unsafe { self.tree.event_kind(self.idx) } {
            EventKind::StartNode => {
                let node = unsafe { SyntaxNode::new(self.idx, self.tree.id()) };
                let finish_node_idx = unsafe { self.tree.get_start_node(self.idx).finish_node_idx };
                self.finish_node_idxs.push(finish_node_idx);
                self.idx += START_NODE_SIZE;
                Some(Event::StartNode(node))
            }
            EventKind::AddToken => {
                let token = unsafe { SyntaxToken::new(self.idx, self.tree.id()) };
                self.idx += ADD_TOKEN_SIZE;
                Some(Event::AddToken(token))
            }
        }
    }
}

struct RawEvents<'a, C> {
    idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    finish_node_idxs: Vec<EventIdx>,
}

impl<C: TreeConfig> Iterator for RawEvents<'_, C> {
    type Item = RawEvent<C>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finish_node_idxs.last().copied() == Some(self.idx) {
            self.finish_node_idxs.pop();
            return Some(RawEvent::FinishNode);
        }

        if self.idx.0.get() >= self.tree.data.len() as u32 {
            return None;
        }

        match unsafe { self.tree.event_kind(self.idx) } {
            EventKind::StartNode => {
                let start_node = unsafe { self.tree.get_start_node(self.idx) };
                let range = TextRange::new(start_node.start.into(), start_node.end.into());
                self.finish_node_idxs.push(start_node.finish_node_idx);
                self.idx += START_NODE_SIZE;
                Some(RawEvent::StartNode { kind: start_node.kind, range })
            }
            EventKind::AddToken => {
                let add_token = unsafe { self.tree.get_add_token(self.idx) };
                let range = TextRange::new(add_token.start.into(), add_token.end.into());
                self.idx += ADD_TOKEN_SIZE;
                Some(RawEvent::AddToken { kind: add_token.kind, range })
            }
        }
    }
}

/// The events in a syntax tree, as emitted by [`SyntaxTree::events`].
/// See that method’s documentation for more.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Event<C> {
    #[allow(missing_docs)]
    StartNode(SyntaxNode<C>),
    #[allow(missing_docs)]
    AddToken(SyntaxToken<C>),
    #[allow(missing_docs)]
    FinishNode,
}

/// The events in a syntax tree, as emitted by [`SyntaxTree::raw_events`].
/// See that method’s documentation for more.
///
/// All data here is exactly as it is stored in the tree, with nothing extra computed.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum RawEvent<C: TreeConfig> {
    #[allow(missing_docs)]
    StartNode { kind: C::NodeKind, range: TextRange },
    #[allow(missing_docs)]
    AddToken { kind: C::TokenKind, range: TextRange },
    #[allow(missing_docs)]
    FinishNode,
}

impl<C: TreeConfig> fmt::Debug for SyntaxTreeBuf<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_tree().fmt(f)
    }
}

impl<C: TreeConfig> fmt::Debug for SyntaxTree<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !f.alternate() {
            return f.debug_struct("SyntaxTree").field("data", &&self.data).finish();
        }

        let mut indentation_level = 0_usize;

        for event in self.events() {
            match event {
                Event::StartNode(node) => {
                    for _ in 0..indentation_level {
                        write!(f, "  ")?;
                    }
                    indentation_level += 1;
                    let kind = node.kind(self);
                    let range = node.range(self);
                    writeln!(f, "{kind:?}@{range:?}")?;
                }
                Event::AddToken(token) => {
                    for _ in 0..indentation_level {
                        write!(f, "  ")?;
                    }
                    let kind = token.kind(self);
                    let range = token.range(self);
                    let text = token.text(self);
                    writeln!(f, "{kind:?}@{range:?} {text:?}")?;
                }
                Event::FinishNode => indentation_level -= 1,
            }
        }

        Ok(())
    }
}

impl<C: TreeConfig> fmt::Debug for RawEvent<C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StartNode { kind, range } => write!(f, "START_NODE {kind:?} {range:?}"),
            Self::AddToken { kind, range } => write!(f, "ADD_TOKEN {kind:?} {range:?}"),
            Self::FinishNode => write!(f, "FINISH_NODE"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;
    use std::sync::OnceLock;

    #[derive(Debug, PartialEq)]
    #[repr(u8)]
    enum NodeKind {
        Root,
        Block,
        Function,
    }

    #[derive(Debug, PartialEq)]
    #[repr(u8)]
    enum TokenKind {
        Arrow,
        Comment,
        FncKw,
        Ident,
        LBrace,
        LetKw,
        RBrace,
        Semicolon,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum TreeConfig {}

    unsafe impl crate::TreeConfig for TreeConfig {
        type NodeKind = NodeKind;
        type TokenKind = TokenKind;

        fn node_kind_to_raw(node_kind: Self::NodeKind) -> u16 {
            node_kind as u16
        }

        fn token_kind_to_raw(token_kind: Self::TokenKind) -> u16 {
            token_kind as u16
        }

        unsafe fn node_kind_from_raw(raw: u16) -> Self::NodeKind {
            std::mem::transmute(raw as u8)
        }

        unsafe fn token_kind_from_raw(raw: u16) -> Self::TokenKind {
            std::mem::transmute(raw as u8)
        }
    }

    enum D {
        U16(u16),
        U32(u32),
        Text(&'static str),
    }

    fn check<const N: usize>(
        input: &str,
        f: impl Fn(&mut SyntaxBuilder<TreeConfig>),
        data: [D; N],
    ) {
        let mut builder = SyntaxBuilder::new(input);
        f(&mut builder);
        let tree = builder.finish();

        let data: Vec<_> = data
            .into_iter()
            .flat_map(|num| match num {
                D::U16(n) => n.to_ne_bytes().to_vec(),
                D::U32(n) => n.to_ne_bytes().to_vec(),
                D::Text(s) => s.as_bytes().to_vec(),
            })
            .collect();

        // don’t include tag in tests
        assert_eq!(tree.as_tree().data[4..], data);
    }

    fn big_tree() -> &'static SyntaxTree<TreeConfig> {
        static BUF: OnceLock<SyntaxTreeBuf<TreeConfig>> = OnceLock::new();

        BUF.get_or_init(|| {
            let mut builder = SyntaxBuilder::new("# foo\nfncbar->{};");

            builder.start_node(NodeKind::Root);
            builder.add_token(TokenKind::Comment, TextRange::new(0.into(), 6.into()));
            builder.start_node(NodeKind::Function);
            builder.add_token(TokenKind::FncKw, TextRange::new(6.into(), 9.into()));
            builder.add_token(TokenKind::Ident, TextRange::new(9.into(), 12.into()));
            builder.add_token(TokenKind::Arrow, TextRange::new(12.into(), 14.into()));
            builder.start_node(NodeKind::Block);
            builder.add_token(TokenKind::LBrace, TextRange::new(14.into(), 15.into()));
            builder.add_token(TokenKind::RBrace, TextRange::new(15.into(), 16.into()));
            builder.finish_node();
            builder.add_token(TokenKind::Semicolon, TextRange::new(16.into(), 17.into()));
            builder.finish_node();
            builder.finish_node();

            builder.finish()
        })
    }

    #[test]
    fn just_root() {
        check(
            "",
            |b| {
                b.start_node(NodeKind::Root);
                b.finish_node();
            },
            [D::U32(0), D::U16(NodeKind::Root as u16 | 1 << 15), D::U32(22), D::U32(0), D::U32(0)],
        );
    }

    #[test]
    fn add_token() {
        check(
            "let",
            |b| {
                b.start_node(NodeKind::Root);
                b.add_token(TokenKind::LetKw, TextRange::new(0.into(), 3.into()));
                b.finish_node();
            },
            [
                D::U32(3),
                D::Text("let"),
                D::U16(NodeKind::Root as u16 | 1 << 15),
                D::U32(35),
                D::U32(0),
                D::U32(3),
                D::U16(TokenKind::LetKw as u16),
                D::U32(0),
                D::U32(3),
            ],
        );
    }

    #[test]
    fn debug_empty() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.finish_node();

        let tree = builder.finish();
        expect![[r##"
            Root@0..0
        "##]]
        .assert_eq(&format!("{tree:#?}"));
    }

    #[test]
    fn debug_complex() {
        expect![[r##"
            Root@0..17
              Comment@0..6 "# foo\n"
              Function@6..17
                FncKw@6..9 "fnc"
                Ident@9..12 "bar"
                Arrow@12..14 "->"
                Block@14..16
                  LBrace@14..15 "{"
                  RBrace@15..16 "}"
                Semicolon@16..17 ";"
        "##]]
        .assert_eq(&format!("{:#?}", big_tree()));
    }

    #[test]
    fn events() {
        let tree = big_tree();
        let mut events = tree.events();

        let root = match events.next() {
            Some(Event::StartNode(root)) => root,
            _ => unreachable!(),
        };
        assert_eq!(root.kind(tree), NodeKind::Root);

        assert!(matches!(events.next(), Some(Event::AddToken(_))));
        assert!(matches!(events.next(), Some(Event::StartNode(_))));
        assert!(matches!(events.next(), Some(Event::AddToken(_))));
        assert!(matches!(events.next(), Some(Event::AddToken(_))));
        assert!(matches!(events.next(), Some(Event::AddToken(_))));
        assert!(matches!(events.next(), Some(Event::StartNode(_))));
        assert!(matches!(events.next(), Some(Event::AddToken(_))));
        assert!(matches!(events.next(), Some(Event::AddToken(_))));
        assert!(matches!(events.next(), Some(Event::FinishNode)));

        let semicolon = match events.next() {
            Some(Event::AddToken(semicolon)) => semicolon,
            _ => unreachable!(),
        };
        assert_eq!(semicolon.kind(tree), TokenKind::Semicolon);

        assert!(matches!(events.next(), Some(Event::FinishNode)));
        assert!(matches!(events.next(), Some(Event::FinishNode)));
        assert!(events.next().is_none());
    }

    #[test]
    fn raw_events() {
        expect![[r#"
            [
                START_NODE Root 0..17,
                ADD_TOKEN Comment 0..6,
                START_NODE Function 6..17,
                ADD_TOKEN FncKw 6..9,
                ADD_TOKEN Ident 9..12,
                ADD_TOKEN Arrow 12..14,
                START_NODE Block 14..16,
                ADD_TOKEN LBrace 14..15,
                ADD_TOKEN RBrace 15..16,
                FINISH_NODE,
                ADD_TOKEN Semicolon 16..17,
                FINISH_NODE,
                FINISH_NODE,
            ]
        "#]]
        .assert_debug_eq(&big_tree().raw_events().collect::<Vec<_>>());
    }

    #[test]
    #[should_panic(expected = "no nodes are yet to be finished")]
    fn no_start_node() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.finish_node();
    }

    #[test]
    #[should_panic(expected = "did not finish all nodes (1 unfinished nodes)")]
    fn no_finish_node() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "did not finish all nodes (2 unfinished nodes)")]
    fn too_many_start_node_calls() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.start_node(NodeKind::Function);
        builder.start_node(NodeKind::Block);
        builder.start_node(NodeKind::Block);
        builder.finish_node();
        builder.finish_node();
        builder.finish();
    }

    #[test]
    #[should_panic(expected = "no nodes are yet to be finished")]
    fn too_many_finish_node_calls() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.start_node(NodeKind::Function);
        builder.start_node(NodeKind::Block);
        builder.finish_node();
        builder.finish_node();
        builder.finish_node();
        builder.finish_node();
    }

    #[test]
    #[should_panic(expected = "root node already created")]
    fn second_root() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.finish_node();
        builder.start_node(NodeKind::Block);
    }

    #[test]
    #[should_panic(expected = "no nodes created")]
    fn empty_without_text() {
        SyntaxBuilder::<TreeConfig>::new("").finish();
    }

    #[test]
    #[should_panic(expected = "no nodes created")]
    fn empty_with_text() {
        SyntaxBuilder::<TreeConfig>::new("foo").finish();
    }

    #[test]
    #[should_panic(expected = "cannot add token before starting node")]
    fn add_token_before_starting_node() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("let");
        builder.add_token(TokenKind::LetKw, TextRange::new(0.into(), 3.into()));
    }

    #[test]
    #[should_panic(expected = "token is out of range: range is 0..1, but text is 0..0")]
    fn add_token_with_out_of_bounds_range() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.add_token(TokenKind::LetKw, TextRange::new(0.into(), 1.into()));
    }

    #[test]
    #[should_panic(
        expected = "tried to access node data from tree other than the one this node is from"
    )]
    fn access_node_data_from_other_tree() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.finish_node();
        let tree = builder.finish();

        let mut builder = SyntaxBuilder::<TreeConfig>::new("");
        builder.start_node(NodeKind::Root);
        builder.finish_node();
        let tree2 = builder.finish();

        tree.root().text(&tree2);
    }

    #[test]
    #[should_panic(
        expected = "tried to access token data from tree other than the one this token is from"
    )]
    fn access_token_data_from_other_tree() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("->");
        builder.start_node(NodeKind::Root);
        builder.add_token(TokenKind::Arrow, TextRange::new(0.into(), 2.into()));
        builder.finish_node();
        let tree = builder.finish();

        let mut builder = SyntaxBuilder::new("");
        builder.start_node(NodeKind::Root);
        builder.finish_node();
        let tree2 = builder.finish();

        let arrow_token = tree.root().child_tokens(&tree).next().unwrap();
        arrow_token.text(&tree2);
    }

    #[test]
    #[should_panic(
        expected = "tried to create token that does not lie on UTF-8 character boundary"
    )]
    fn create_token_not_on_utf8_char_boundary() {
        let mut builder = SyntaxBuilder::<TreeConfig>::new("å");
        builder.start_node(NodeKind::Root);
        builder.add_token(TokenKind::Ident, TextRange::new(1.into(), 2.into()));
    }
}
