use crate::tree::{EventIdx, EventKind, ADD_TOKEN_SIZE, START_NODE_SIZE};
use crate::{SyntaxElement, SyntaxToken, SyntaxTree, TextRange, TreeConfig};
use std::hash::Hash;
use std::marker::PhantomData;

/// A handle to a specific node in a specific [`SyntaxTree`].
///
/// A syntax tree’s root node can be obtained by calling [`SyntaxTree::root`].
///
/// All accessor methods will panic if used with a tree
/// other than the one this node is from.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxNode<C> {
    idx: EventIdx,
    tree_id: u32,
    phantom: PhantomData<C>,
}

static_assertions::assert_eq_size!(SyntaxNode<()>, Option<SyntaxNode<()>>, u64);

impl<C: TreeConfig> SyntaxNode<C> {
    #[inline(always)]
    pub(crate) unsafe fn new(idx: EventIdx, tree_id: u32) -> Self {
        Self { idx, tree_id, phantom: PhantomData }
    }

    /// Returns the kind of this node.
    pub fn kind(self, tree: &SyntaxTree<C>) -> C::NodeKind {
        self.verify_tree(tree);
        unsafe { tree.get_start_node(self.idx).kind }
    }

    /// Returns an iterator over the direct child nodes and tokens of this node.
    pub fn children(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxElement<C>> + '_ {
        self.verify_tree(tree);
        Children {
            idx: self.idx + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx).finish_node_idx },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the direct child nodes of this node.
    pub fn child_nodes(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxNode<C>> + '_ {
        self.verify_tree(tree);
        ChildNodes {
            idx: self.idx + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx).finish_node_idx },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the direct child tokens of this node.
    pub fn child_tokens(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxToken<C>> + '_ {
        self.verify_tree(tree);
        ChildTokens {
            idx: self.idx + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx).finish_node_idx },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the descendant nodes and tokens of this node
    /// in depth-first order.
    pub fn descendants(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxElement<C>> + '_ {
        self.verify_tree(tree);
        Descendants {
            idx: self.idx + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx).finish_node_idx },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the descendant nodes of this node
    /// in depth-first order.
    pub fn descendant_nodes(
        self,
        tree: &SyntaxTree<C>,
    ) -> impl Iterator<Item = SyntaxNode<C>> + '_ {
        self.verify_tree(tree);
        DescendantNodes {
            idx: self.idx + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx).finish_node_idx },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the descendant tokens of this node
    /// in depth-first order.
    pub fn descendant_tokens(
        self,
        tree: &SyntaxTree<C>,
    ) -> impl Iterator<Item = SyntaxToken<C>> + '_ {
        self.verify_tree(tree);
        DescendantTokens {
            idx: self.idx + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx).finish_node_idx },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns the range this node spans in the original input.
    pub fn range(self, tree: &SyntaxTree<C>) -> TextRange {
        self.verify_tree(tree);
        let start_node = unsafe { tree.get_start_node(self.idx) };
        TextRange::new(start_node.start.into(), start_node.end.into())
    }

    /// Returns the text of all the tokens this node contains.
    pub fn text(self, tree: &SyntaxTree<C>) -> &str {
        self.verify_tree(tree);
        unsafe {
            let start_node = tree.get_start_node(self.idx);
            tree.get_text(start_node.start, start_node.end)
        }
    }

    fn verify_tree(self, tree: &SyntaxTree<C>) {
        assert_eq!(
            self.tree_id,
            tree.id(),
            "tried to access node data from tree other than the one this node is from"
        );
    }
}

struct Children<'a, C> {
    idx: EventIdx,
    finish_idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for Children<'_, C> {
    type Item = SyntaxElement<C>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finish_idx <= self.idx {
            return None;
        }

        unsafe {
            match self.tree.event_kind(self.idx) {
                EventKind::StartNode => {
                    let finish_node_idx = self.tree.get_start_node(self.idx).finish_node_idx;
                    let element = SyntaxElement::Node(SyntaxNode::new(self.idx, self.tree_id));
                    self.idx = finish_node_idx;
                    Some(element)
                }
                EventKind::AddToken => {
                    let element = SyntaxElement::Token(SyntaxToken::new(self.idx, self.tree_id));
                    self.idx += ADD_TOKEN_SIZE;
                    Some(element)
                }
            }
        }
    }
}

struct ChildNodes<'a, C> {
    idx: EventIdx,
    finish_idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for ChildNodes<'_, C> {
    type Item = SyntaxNode<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                match self.tree.event_kind(self.idx) {
                    EventKind::StartNode => {
                        let finish_node_idx = self.tree.get_start_node(self.idx).finish_node_idx;
                        let node = SyntaxNode::new(self.idx, self.tree_id);
                        self.idx = finish_node_idx;
                        return Some(node);
                    }
                    EventKind::AddToken => {
                        self.idx += ADD_TOKEN_SIZE;
                        continue;
                    }
                }
            }
        }

        None
    }
}

struct ChildTokens<'a, C> {
    finish_idx: EventIdx,
    idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for ChildTokens<'_, C> {
    type Item = SyntaxToken<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                match self.tree.event_kind(self.idx) {
                    EventKind::StartNode => {
                        let finish_node_idx = self.tree.get_start_node(self.idx).finish_node_idx;
                        self.idx = finish_node_idx;
                        continue;
                    }
                    EventKind::AddToken => {
                        let token = SyntaxToken::new(self.idx, self.tree_id);
                        self.idx += ADD_TOKEN_SIZE;
                        return Some(token);
                    }
                }
            }
        }

        None
    }
}

struct Descendants<'a, C> {
    finish_idx: EventIdx,
    idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for Descendants<'_, C> {
    type Item = SyntaxElement<C>;

    fn next(&mut self) -> Option<Self::Item> {
        debug_assert!(self.idx <= self.finish_idx);
        if self.idx == self.finish_idx {
            return None;
        }

        unsafe {
            match self.tree.event_kind(self.idx) {
                EventKind::StartNode => {
                    let element = SyntaxElement::Node(SyntaxNode::new(self.idx, self.tree_id));
                    self.idx += START_NODE_SIZE;
                    Some(element)
                }
                EventKind::AddToken => {
                    let element = SyntaxElement::Token(SyntaxToken::new(self.idx, self.tree_id));
                    self.idx += ADD_TOKEN_SIZE;
                    Some(element)
                }
            }
        }
    }
}

struct DescendantNodes<'a, C> {
    finish_idx: EventIdx,
    idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for DescendantNodes<'_, C> {
    type Item = SyntaxNode<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                match self.tree.event_kind(self.idx) {
                    EventKind::StartNode => {
                        let node = SyntaxNode::new(self.idx, self.tree_id);
                        self.idx += START_NODE_SIZE;
                        return Some(node);
                    }
                    EventKind::AddToken => {
                        self.idx += ADD_TOKEN_SIZE;
                        continue;
                    }
                }
            }
        }

        None
    }
}

struct DescendantTokens<'a, C> {
    finish_idx: EventIdx,
    idx: EventIdx,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for DescendantTokens<'_, C> {
    type Item = SyntaxToken<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                match self.tree.event_kind(self.idx) {
                    EventKind::StartNode => {
                        self.idx += START_NODE_SIZE;
                        continue;
                    }
                    EventKind::AddToken => {
                        let token = SyntaxToken::new(self.idx, self.tree_id);
                        self.idx += ADD_TOKEN_SIZE;
                        return Some(token);
                    }
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SyntaxBuilder, SyntaxTreeBuf};
    use std::sync::OnceLock;

    #[derive(Debug, PartialEq)]
    #[repr(u8)]
    enum NodeKind {
        Root,
        BinaryExpr,
        Call,
    }

    #[derive(Debug, PartialEq)]
    #[repr(u8)]
    enum TokenKind {
        Asterisk,
        Ident,
        IntLiteral,
        Plus,
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

    fn example_tree() -> &'static SyntaxTree<TreeConfig> {
        static BUF: OnceLock<SyntaxTreeBuf<TreeConfig>> = OnceLock::new();

        BUF.get_or_init(|| {
            let mut builder = SyntaxBuilder::new("2*5+10foo");

            builder.start_node(NodeKind::Root);
            {
                builder.start_node(NodeKind::BinaryExpr);
                {
                    builder.start_node(NodeKind::BinaryExpr);
                    builder.add_token(TokenKind::IntLiteral, TextRange::new(0.into(), 1.into()));
                    builder.add_token(TokenKind::Asterisk, TextRange::new(1.into(), 2.into()));
                    builder.add_token(TokenKind::IntLiteral, TextRange::new(2.into(), 3.into()));
                    builder.finish_node();
                }
                builder.add_token(TokenKind::Plus, TextRange::new(3.into(), 4.into()));
                builder.add_token(TokenKind::IntLiteral, TextRange::new(4.into(), 6.into()));
                builder.finish_node();
            }
            {
                builder.start_node(NodeKind::Call);
                builder.add_token(TokenKind::Ident, TextRange::new(6.into(), 9.into()));
                builder.finish_node();
            }
            builder.finish_node();

            builder.finish()
        })
    }

    #[test]
    fn children() {
        let tree = example_tree();
        let root = tree.root();

        let mut children = root.children(tree);
        let binary_expr = children.next().unwrap().unwrap_node();
        assert_eq!(binary_expr.kind(tree), NodeKind::BinaryExpr);
        let call = children.next().unwrap().unwrap_node();
        assert_eq!(call.kind(tree), NodeKind::Call);
        assert!(children.next().is_none());

        let mut children = binary_expr.children(tree);
        assert_eq!(children.next().unwrap().unwrap_node().kind(tree), NodeKind::BinaryExpr);
        assert_eq!(children.next().unwrap().unwrap_token().kind(tree), TokenKind::Plus);
        assert_eq!(children.next().unwrap().unwrap_token().kind(tree), TokenKind::IntLiteral);
        assert!(children.next().is_none());

        let mut children = call.children(tree);
        assert_eq!(children.next().unwrap().unwrap_token().kind(tree), TokenKind::Ident);
        assert!(children.next().is_none());
    }

    #[test]
    fn child_nodes() {
        let tree = example_tree();
        let root = tree.root();

        let mut child_nodes = root.child_nodes(tree);
        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(tree), NodeKind::BinaryExpr);
        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(tree), NodeKind::Call);
        assert!(child_nodes.next().is_none());

        let mut child_nodes = binary_expr.child_nodes(tree);
        assert_eq!(child_nodes.next().unwrap().kind(tree), NodeKind::BinaryExpr);
        assert!(child_nodes.next().is_none());

        let mut child_nodes = call.child_nodes(tree);
        assert!(child_nodes.next().is_none());
    }

    #[test]
    fn child_tokens() {
        let tree = example_tree();
        let root = tree.root();

        let mut child_tokens = root.child_tokens(tree);
        assert!(child_tokens.next().is_none());

        let mut child_nodes = root.child_nodes(tree);
        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(tree), NodeKind::BinaryExpr);
        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(tree), NodeKind::Call);
        assert!(child_nodes.next().is_none());

        let mut child_tokens = binary_expr.child_tokens(tree);
        assert_eq!(child_tokens.next().unwrap().kind(tree), TokenKind::Plus);
        assert_eq!(child_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert!(child_tokens.next().is_none());

        let mut child_tokens = call.child_tokens(tree);
        assert_eq!(child_tokens.next().unwrap().kind(tree), TokenKind::Ident);
        assert!(child_tokens.next().is_none());
    }

    #[test]
    fn descendants() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendants = root.descendants(tree);
        let binary_expr = descendants.next().unwrap().unwrap_node();
        assert_eq!(binary_expr.kind(tree), NodeKind::BinaryExpr);

        let binary_expr_2 = descendants.next().unwrap().unwrap_node();
        assert_eq!(binary_expr_2.kind(tree), NodeKind::BinaryExpr);
        assert_eq!(descendants.next().unwrap().unwrap_token().kind(tree), TokenKind::IntLiteral);
        assert_eq!(descendants.next().unwrap().unwrap_token().kind(tree), TokenKind::Asterisk);
        assert_eq!(descendants.next().unwrap().unwrap_token().kind(tree), TokenKind::IntLiteral);

        assert_eq!(descendants.next().unwrap().unwrap_token().kind(tree), TokenKind::Plus);
        assert_eq!(descendants.next().unwrap().unwrap_token().kind(tree), TokenKind::IntLiteral);

        let call = descendants.next().unwrap().unwrap_node();
        assert_eq!(call.kind(tree), NodeKind::Call);
        assert_eq!(descendants.next().unwrap().unwrap_token().kind(tree), TokenKind::Ident);
        assert!(descendants.next().is_none());

        let mut descendants = binary_expr.child_nodes(tree);
        assert_eq!(descendants.next().unwrap().kind(tree), NodeKind::BinaryExpr);
        assert!(descendants.next().is_none());

        let mut descendant_nodes = call.child_nodes(tree);
        assert!(descendant_nodes.next().is_none());
    }

    #[test]
    fn descendant_nodes() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendant_nodes = root.descendant_nodes(tree);
        let binary_expr = descendant_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(tree), NodeKind::BinaryExpr);
        let binary_expr_2 = descendant_nodes.next().unwrap();
        assert_eq!(binary_expr_2.kind(tree), NodeKind::BinaryExpr);
        let call = descendant_nodes.next().unwrap();
        assert_eq!(call.kind(tree), NodeKind::Call);
        assert!(descendant_nodes.next().is_none());

        let mut descendant_nodes = binary_expr.child_nodes(tree);
        assert_eq!(descendant_nodes.next().unwrap().kind(tree), NodeKind::BinaryExpr);
        assert!(descendant_nodes.next().is_none());

        let mut descendant_nodes = call.child_nodes(tree);
        assert!(descendant_nodes.next().is_none());
    }

    #[test]
    fn descendant_tokens() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendant_tokens = root.descendant_tokens(tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::Asterisk);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::Plus);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::Ident);
        assert!(descendant_tokens.next().is_none());

        let mut child_nodes = root.child_nodes(tree);

        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(tree), NodeKind::BinaryExpr);
        let mut descendant_tokens = binary_expr.descendant_tokens(tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::Asterisk);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::Plus);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::IntLiteral);
        assert!(descendant_tokens.next().is_none());

        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(tree), NodeKind::Call);
        let mut descendant_tokens = call.descendant_tokens(tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(tree), TokenKind::Ident);
        assert!(descendant_tokens.next().is_none());

        assert!(child_nodes.next().is_none());
    }
}
