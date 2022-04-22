use crate::tree::{ADD_TOKEN_SIZE, FINISH_NODE_SIZE, START_NODE_SIZE};
use crate::{SyntaxElement, SyntaxToken, SyntaxTree, TextRange, TreeConfig};
use std::hash::Hash;
use std::marker::PhantomData;
use std::num::NonZeroU32;

/// A handle to a specific node in a specific [`SyntaxTree`].
///
/// A syntax tree’s root node can be obtained by calling [`SyntaxTree::root`].
///
/// All accessor methods will panic if used with a tree
/// other than the one this node is from.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxNode<C> {
    idx: NonZeroU32,
    tree_id: u32,
    phantom: PhantomData<C>,
}

static_assertions::assert_eq_size!(SyntaxNode<()>, Option<SyntaxNode<()>>, u64);

impl<C: TreeConfig> SyntaxNode<C> {
    #[inline(always)]
    pub(crate) unsafe fn new(idx: u32, tree_id: u32) -> Self {
        Self {
            idx: if cfg!(debug_assertions) {
                NonZeroU32::new(idx).unwrap()
            } else {
                NonZeroU32::new_unchecked(idx)
            },
            tree_id,
            phantom: PhantomData,
        }
    }

    /// Returns the kind of this node.
    pub fn kind(self, tree: &SyntaxTree<C>) -> C::NodeKind {
        self.verify_tree(tree);
        unsafe { tree.get_start_node(self.idx.get()).0 }
    }

    /// Returns an iterator over the direct child nodes and tokens of this node.
    pub fn children(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxElement<C>> + '_ {
        self.verify_tree(tree);
        Children {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the direct child nodes of this node.
    pub fn child_nodes(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxNode<C>> + '_ {
        self.verify_tree(tree);
        ChildNodes {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the direct child tokens of this node.
    pub fn child_tokens(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxToken<C>> + '_ {
        self.verify_tree(tree);
        ChildTokens {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns an iterator over the descendant nodes and tokens of this node
    /// in depth-first order.
    pub fn descendants(self, tree: &SyntaxTree<C>) -> impl Iterator<Item = SyntaxElement<C>> + '_ {
        self.verify_tree(tree);
        Descendants {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
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
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
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
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    /// Returns the range this node spans in the original input.
    pub fn range(self, tree: &SyntaxTree<C>) -> TextRange {
        self.verify_tree(tree);
        let (_, _, start, end) = unsafe { tree.get_start_node(self.idx.get()) };
        TextRange::new(start.into(), end.into())
    }

    /// Returns the text of all the tokens this node contains.
    pub fn text(self, tree: &SyntaxTree<C>) -> &str {
        self.verify_tree(tree);
        unsafe {
            let (_, _, start, end) = tree.get_start_node(self.idx.get());
            tree.get_text(start, end)
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
    idx: u32,
    finish_idx: u32,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for Children<'_, C> {
    type Item = SyntaxElement<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                if self.tree.is_start_node(self.idx) {
                    let (_, finish_node_idx, _, _) = self.tree.get_start_node(self.idx);
                    let element = SyntaxElement::Node(SyntaxNode::new(self.idx, self.tree_id));
                    self.idx = finish_node_idx + FINISH_NODE_SIZE;
                    return Some(element);
                }

                if self.tree.is_add_token(self.idx) {
                    let element = SyntaxElement::Token(SyntaxToken::new(self.idx, self.tree_id));
                    self.idx += ADD_TOKEN_SIZE;
                    return Some(element);
                }
            }

            unreachable!()
        }

        None
    }
}

struct ChildNodes<'a, C> {
    idx: u32,
    finish_idx: u32,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for ChildNodes<'_, C> {
    type Item = SyntaxNode<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                if self.tree.is_start_node(self.idx) {
                    let (_, finish_node_idx, _, _) = self.tree.get_start_node(self.idx);
                    let node = SyntaxNode::new(self.idx, self.tree_id);
                    self.idx = finish_node_idx + FINISH_NODE_SIZE;
                    return Some(node);
                }

                if self.tree.is_add_token(self.idx) {
                    self.idx += ADD_TOKEN_SIZE;
                    continue;
                }
            }

            unreachable!()
        }

        None
    }
}

struct ChildTokens<'a, C> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for ChildTokens<'_, C> {
    type Item = SyntaxToken<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                if self.tree.is_start_node(self.idx) {
                    let (_, finish_node_idx, _, _) = self.tree.get_start_node(self.idx);
                    self.idx = finish_node_idx + FINISH_NODE_SIZE;
                    continue;
                }

                if self.tree.is_add_token(self.idx) {
                    let token = SyntaxToken::new(self.idx, self.tree_id);
                    self.idx += ADD_TOKEN_SIZE;
                    return Some(token);
                }
            }

            unreachable!()
        }

        None
    }
}

struct Descendants<'a, C> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for Descendants<'_, C> {
    type Item = SyntaxElement<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                if self.tree.is_start_node(self.idx) {
                    let element = SyntaxElement::Node(SyntaxNode::new(self.idx, self.tree_id));
                    self.idx += START_NODE_SIZE;
                    return Some(element);
                }

                if self.tree.is_add_token(self.idx) {
                    let element = SyntaxElement::Token(SyntaxToken::new(self.idx, self.tree_id));
                    self.idx += ADD_TOKEN_SIZE;
                    return Some(element);
                }

                if self.tree.is_finish_node(self.idx) {
                    self.idx += FINISH_NODE_SIZE;
                    continue;
                }
            }

            unreachable!()
        }

        None
    }
}

struct DescendantNodes<'a, C> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for DescendantNodes<'_, C> {
    type Item = SyntaxNode<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                if self.tree.is_start_node(self.idx) {
                    let node = SyntaxNode::new(self.idx, self.tree_id);
                    self.idx += START_NODE_SIZE;
                    return Some(node);
                }

                if self.tree.is_add_token(self.idx) {
                    self.idx += ADD_TOKEN_SIZE;
                    continue;
                }

                if self.tree.is_finish_node(self.idx) {
                    self.idx += FINISH_NODE_SIZE;
                    continue;
                }
            }

            unreachable!()
        }

        None
    }
}

struct DescendantTokens<'a, C> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<C>,
    tree_id: u32,
}

impl<C: TreeConfig> Iterator for DescendantTokens<'_, C> {
    type Item = SyntaxToken<C>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            unsafe {
                if self.tree.is_add_token(self.idx) {
                    let token = SyntaxToken::new(self.idx, self.tree_id);
                    self.idx += ADD_TOKEN_SIZE;
                    return Some(token);
                }

                if self.tree.is_start_node(self.idx) {
                    self.idx += START_NODE_SIZE;
                    continue;
                }

                if self.tree.is_finish_node(self.idx) {
                    self.idx += FINISH_NODE_SIZE;
                    continue;
                }
            }

            unreachable!()
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SyntaxBuilder;

    #[derive(Debug, PartialEq)]
    enum NodeKind {
        Root,
        BinaryExpr,
        Call,
        __Last,
    }

    unsafe impl crate::SyntaxKind for NodeKind {
        const LAST: u16 = Self::__Last as u16;

        fn to_raw(self) -> u16 {
            self as u16
        }

        unsafe fn from_raw(raw: u16) -> Self {
            std::mem::transmute(raw as u8)
        }
    }

    #[derive(Debug, PartialEq)]
    enum TokenKind {
        Asterisk,
        Ident,
        IntLiteral,
        Plus,
        __Last,
    }

    unsafe impl crate::SyntaxKind for TokenKind {
        const LAST: u16 = Self::__Last as u16;

        fn to_raw(self) -> u16 {
            self as u16
        }

        unsafe fn from_raw(raw: u16) -> Self {
            std::mem::transmute(raw as u8)
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    enum TreeConfig {}

    impl crate::TreeConfig for TreeConfig {
        type NodeKind = NodeKind;
        type TokenKind = TokenKind;
    }

    fn example_tree() -> SyntaxTree<TreeConfig> {
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
    }

    #[test]
    fn children() {
        let tree = example_tree();
        let root = tree.root();

        let mut children = root.children(&tree);
        let binary_expr = children.next().unwrap().assert_node();
        assert_eq!(binary_expr.kind(&tree), NodeKind::BinaryExpr);
        let call = children.next().unwrap().assert_node();
        assert_eq!(call.kind(&tree), NodeKind::Call);
        assert!(children.next().is_none());

        let mut children = binary_expr.children(&tree);
        assert_eq!(children.next().unwrap().assert_node().kind(&tree), NodeKind::BinaryExpr);
        assert_eq!(children.next().unwrap().assert_token().kind(&tree), TokenKind::Plus);
        assert_eq!(children.next().unwrap().assert_token().kind(&tree), TokenKind::IntLiteral);
        assert!(children.next().is_none());

        let mut children = call.children(&tree);
        assert_eq!(children.next().unwrap().assert_token().kind(&tree), TokenKind::Ident);
        assert!(children.next().is_none());
    }

    #[test]
    fn child_nodes() {
        let tree = example_tree();
        let root = tree.root();

        let mut child_nodes = root.child_nodes(&tree);
        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(&tree), NodeKind::BinaryExpr);
        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), NodeKind::Call);
        assert!(child_nodes.next().is_none());

        let mut child_nodes = binary_expr.child_nodes(&tree);
        assert_eq!(child_nodes.next().unwrap().kind(&tree), NodeKind::BinaryExpr);
        assert!(child_nodes.next().is_none());

        let mut child_nodes = call.child_nodes(&tree);
        assert!(child_nodes.next().is_none());
    }

    #[test]
    fn child_tokens() {
        let tree = example_tree();
        let root = tree.root();

        let mut child_tokens = root.child_tokens(&tree);
        assert!(child_tokens.next().is_none());

        let mut child_nodes = root.child_nodes(&tree);
        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(&tree), NodeKind::BinaryExpr);
        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), NodeKind::Call);
        assert!(child_nodes.next().is_none());

        let mut child_tokens = binary_expr.child_tokens(&tree);
        assert_eq!(child_tokens.next().unwrap().kind(&tree), TokenKind::Plus);
        assert_eq!(child_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert!(child_tokens.next().is_none());

        let mut child_tokens = call.child_tokens(&tree);
        assert_eq!(child_tokens.next().unwrap().kind(&tree), TokenKind::Ident);
        assert!(child_tokens.next().is_none());
    }

    #[test]
    fn descendants() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendants = root.descendants(&tree);
        let binary_expr = descendants.next().unwrap().assert_node();
        assert_eq!(binary_expr.kind(&tree), NodeKind::BinaryExpr);

        let binary_expr_2 = descendants.next().unwrap().assert_node();
        assert_eq!(binary_expr_2.kind(&tree), NodeKind::BinaryExpr);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), TokenKind::IntLiteral);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), TokenKind::Asterisk);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), TokenKind::IntLiteral);

        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), TokenKind::Plus);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), TokenKind::IntLiteral);

        let call = descendants.next().unwrap().assert_node();
        assert_eq!(call.kind(&tree), NodeKind::Call);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), TokenKind::Ident);
        assert!(descendants.next().is_none());

        let mut descendants = binary_expr.child_nodes(&tree);
        assert_eq!(descendants.next().unwrap().kind(&tree), NodeKind::BinaryExpr);
        assert!(descendants.next().is_none());

        let mut descendant_nodes = call.child_nodes(&tree);
        assert!(descendant_nodes.next().is_none());
    }

    #[test]
    fn descendant_nodes() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendant_nodes = root.descendant_nodes(&tree);
        let binary_expr = descendant_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(&tree), NodeKind::BinaryExpr);
        let binary_expr_2 = descendant_nodes.next().unwrap();
        assert_eq!(binary_expr_2.kind(&tree), NodeKind::BinaryExpr);
        let call = descendant_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), NodeKind::Call);
        assert!(descendant_nodes.next().is_none());

        let mut descendant_nodes = binary_expr.child_nodes(&tree);
        assert_eq!(descendant_nodes.next().unwrap().kind(&tree), NodeKind::BinaryExpr);
        assert!(descendant_nodes.next().is_none());

        let mut descendant_nodes = call.child_nodes(&tree);
        assert!(descendant_nodes.next().is_none());
    }

    #[test]
    fn descendant_tokens() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendant_tokens = root.descendant_tokens(&tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::Asterisk);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::Plus);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::Ident);
        assert!(descendant_tokens.next().is_none());

        let mut child_nodes = root.child_nodes(&tree);

        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(&tree), NodeKind::BinaryExpr);
        let mut descendant_tokens = binary_expr.descendant_tokens(&tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::Asterisk);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::Plus);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::IntLiteral);
        assert!(descendant_tokens.next().is_none());

        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), NodeKind::Call);
        let mut descendant_tokens = call.descendant_tokens(&tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), TokenKind::Ident);
        assert!(descendant_tokens.next().is_none());

        assert!(child_nodes.next().is_none());
    }
}
