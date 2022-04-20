use crate::tree::{ADD_TOKEN_SIZE, FINISH_NODE_SIZE, START_NODE_SIZE};
use crate::{SyntaxElement, SyntaxKind, SyntaxToken, SyntaxTree};
use std::hash::Hash;
use std::marker::PhantomData;
use std::num::NonZeroU32;
use text_size::TextRange;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxNode<K> {
    idx: NonZeroU32,
    tree_id: u32,
    phantom: PhantomData<K>,
}

static_assertions::assert_eq_size!(SyntaxNode<()>, Option<SyntaxNode<()>>, u64);

impl<K: SyntaxKind> SyntaxNode<K> {
    #[inline(always)]
    pub(crate) fn new(idx: u32, tree_id: u32) -> Self {
        Self {
            idx: if cfg!(debug_assertions) {
                NonZeroU32::new(idx).unwrap()
            } else {
                unsafe { NonZeroU32::new_unchecked(idx) }
            },
            tree_id,
            phantom: PhantomData,
        }
    }

    pub fn kind(self, tree: &SyntaxTree<K>) -> K {
        self.verify_tree(tree);
        unsafe { tree.get_start_node(self.idx.get()).0 }
    }

    pub fn children(self, tree: &SyntaxTree<K>) -> impl Iterator<Item = SyntaxElement<K>> + '_ {
        self.verify_tree(tree);
        Children {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    pub fn child_nodes(self, tree: &SyntaxTree<K>) -> impl Iterator<Item = SyntaxNode<K>> + '_ {
        self.verify_tree(tree);
        ChildNodes {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    pub fn child_tokens(self, tree: &SyntaxTree<K>) -> impl Iterator<Item = SyntaxToken<K>> + '_ {
        self.verify_tree(tree);
        ChildTokens {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    pub fn descendants(self, tree: &SyntaxTree<K>) -> impl Iterator<Item = SyntaxElement<K>> + '_ {
        self.verify_tree(tree);
        Descendants {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    pub fn descendant_nodes(
        self,
        tree: &SyntaxTree<K>,
    ) -> impl Iterator<Item = SyntaxNode<K>> + '_ {
        self.verify_tree(tree);
        DescendantNodes {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    pub fn descendant_tokens(
        self,
        tree: &SyntaxTree<K>,
    ) -> impl Iterator<Item = SyntaxToken<K>> + '_ {
        self.verify_tree(tree);
        DescendantTokens {
            idx: self.idx.get() + START_NODE_SIZE,
            finish_idx: unsafe { tree.get_start_node(self.idx.get()).1 },
            tree,
            tree_id: self.tree_id,
        }
    }

    pub fn range(self, tree: &SyntaxTree<K>) -> TextRange {
        self.verify_tree(tree);
        let (_, _, start, end) = unsafe { tree.get_start_node(self.idx.get()) };
        TextRange::new(start.into(), end.into())
    }

    pub fn text(self, tree: &SyntaxTree<K>) -> &str {
        self.verify_tree(tree);
        unsafe {
            let (_, _, start, end) = tree.get_start_node(self.idx.get());
            tree.get_text(start, end)
        }
    }

    fn verify_tree(self, tree: &SyntaxTree<K>) {
        assert_eq!(
            self.tree_id,
            tree.id(),
            "tried to access node data from tree other than the one this node is from"
        );
    }
}

struct Children<'a, K> {
    idx: u32,
    finish_idx: u32,
    tree: &'a SyntaxTree<K>,
    tree_id: u32,
}

impl<K: SyntaxKind> Iterator for Children<'_, K> {
    type Item = SyntaxElement<K>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            if unsafe { self.tree.is_start_node(self.idx) } {
                let (_, finish_node_idx, _, _) = unsafe { self.tree.get_start_node(self.idx) };
                let element = SyntaxElement::Node(SyntaxNode::new(self.idx, self.tree_id));
                self.idx = finish_node_idx + FINISH_NODE_SIZE;
                return Some(element);
            }

            if unsafe { self.tree.is_add_token(self.idx) } {
                let element = SyntaxElement::Token(SyntaxToken::new(self.idx, self.tree_id));
                self.idx += ADD_TOKEN_SIZE;
                return Some(element);
            }

            unreachable!()
        }

        None
    }
}

struct ChildNodes<'a, K> {
    idx: u32,
    finish_idx: u32,
    tree: &'a SyntaxTree<K>,
    tree_id: u32,
}

impl<K: SyntaxKind> Iterator for ChildNodes<'_, K> {
    type Item = SyntaxNode<K>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            if unsafe { self.tree.is_start_node(self.idx) } {
                let (_, finish_node_idx, _, _) = unsafe { self.tree.get_start_node(self.idx) };
                let node = SyntaxNode::new(self.idx, self.tree_id);
                self.idx = finish_node_idx + FINISH_NODE_SIZE;
                return Some(node);
            }

            if unsafe { self.tree.is_add_token(self.idx) } {
                self.idx += ADD_TOKEN_SIZE;
                continue;
            }

            unreachable!()
        }

        None
    }
}

struct ChildTokens<'a, K> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<K>,
    tree_id: u32,
}

impl<K: SyntaxKind> Iterator for ChildTokens<'_, K> {
    type Item = SyntaxToken<K>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            if unsafe { self.tree.is_start_node(self.idx) } {
                let (_, finish_node_idx, _, _) = unsafe { self.tree.get_start_node(self.idx) };
                self.idx = finish_node_idx + FINISH_NODE_SIZE;
                continue;
            }

            if unsafe { self.tree.is_add_token(self.idx) } {
                let token = SyntaxToken::new(self.idx, self.tree_id);
                self.idx += ADD_TOKEN_SIZE;
                return Some(token);
            }

            unreachable!()
        }

        None
    }
}

struct Descendants<'a, K> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<K>,
    tree_id: u32,
}

impl<K: SyntaxKind> Iterator for Descendants<'_, K> {
    type Item = SyntaxElement<K>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            if unsafe { self.tree.is_start_node(self.idx) } {
                let element = SyntaxElement::Node(SyntaxNode::new(self.idx, self.tree_id));
                self.idx += START_NODE_SIZE;
                return Some(element);
            }

            if unsafe { self.tree.is_add_token(self.idx) } {
                let element = SyntaxElement::Token(SyntaxToken::new(self.idx, self.tree_id));
                self.idx += ADD_TOKEN_SIZE;
                return Some(element);
            }

            if unsafe { self.tree.is_finish_node(self.idx) } {
                self.idx += FINISH_NODE_SIZE;
                continue;
            }

            unreachable!()
        }

        None
    }
}

struct DescendantNodes<'a, K> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<K>,
    tree_id: u32,
}

impl<K: SyntaxKind> Iterator for DescendantNodes<'_, K> {
    type Item = SyntaxNode<K>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            if unsafe { self.tree.is_start_node(self.idx) } {
                let node = SyntaxNode::new(self.idx, self.tree_id);
                self.idx += START_NODE_SIZE;
                return Some(node);
            }

            if unsafe { self.tree.is_add_token(self.idx) } {
                self.idx += ADD_TOKEN_SIZE;
                continue;
            }

            if unsafe { self.tree.is_finish_node(self.idx) } {
                self.idx += FINISH_NODE_SIZE;
                continue;
            }

            unreachable!()
        }

        None
    }
}

struct DescendantTokens<'a, K> {
    finish_idx: u32,
    idx: u32,
    tree: &'a SyntaxTree<K>,
    tree_id: u32,
}

impl<K: SyntaxKind> Iterator for DescendantTokens<'_, K> {
    type Item = SyntaxToken<K>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.finish_idx {
            if unsafe { self.tree.is_add_token(self.idx) } {
                let token = SyntaxToken::new(self.idx, self.tree_id);
                self.idx += ADD_TOKEN_SIZE;
                return Some(token);
            }

            if unsafe { self.tree.is_start_node(self.idx) } {
                self.idx += START_NODE_SIZE;
                continue;
            }

            if unsafe { self.tree.is_finish_node(self.idx) } {
                self.idx += FINISH_NODE_SIZE;
                continue;
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

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(u16)]
    enum SyntaxKind {
        Root,
        Asterisk,
        BinaryExpr,
        Call,
        Ident,
        IntLiteral,
        Plus,
        __Last,
    }

    unsafe impl crate::SyntaxKind for SyntaxKind {
        const LAST: u16 = Self::__Last as u16;

        fn to_raw(self) -> u16 {
            self as u16
        }

        unsafe fn from_raw(raw: u16) -> Self {
            std::mem::transmute(raw)
        }
    }

    fn example_tree() -> SyntaxTree<SyntaxKind> {
        let mut builder = SyntaxBuilder::new("2*5+10foo");

        builder.start_node(SyntaxKind::Root);
        {
            builder.start_node(SyntaxKind::BinaryExpr);
            {
                builder.start_node(SyntaxKind::BinaryExpr);
                builder.add_token(SyntaxKind::IntLiteral, TextRange::new(0.into(), 1.into()));
                builder.add_token(SyntaxKind::Asterisk, TextRange::new(1.into(), 2.into()));
                builder.add_token(SyntaxKind::IntLiteral, TextRange::new(2.into(), 3.into()));
                builder.finish_node();
            }
            builder.add_token(SyntaxKind::Plus, TextRange::new(3.into(), 4.into()));
            builder.add_token(SyntaxKind::IntLiteral, TextRange::new(4.into(), 6.into()));
            builder.finish_node();
        }
        {
            builder.start_node(SyntaxKind::Call);
            builder.add_token(SyntaxKind::Ident, TextRange::new(6.into(), 9.into()));
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
        assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);
        let call = children.next().unwrap().assert_node();
        assert_eq!(call.kind(&tree), SyntaxKind::Call);
        assert!(children.next().is_none());

        let mut children = binary_expr.children(&tree);
        assert_eq!(children.next().unwrap().assert_node().kind(&tree), SyntaxKind::BinaryExpr);
        assert_eq!(children.next().unwrap().assert_token().kind(&tree), SyntaxKind::Plus);
        assert_eq!(children.next().unwrap().assert_token().kind(&tree), SyntaxKind::IntLiteral);
        assert!(children.next().is_none());

        let mut children = call.children(&tree);
        assert_eq!(children.next().unwrap().assert_token().kind(&tree), SyntaxKind::Ident);
        assert!(children.next().is_none());
    }

    #[test]
    fn child_nodes() {
        let tree = example_tree();
        let root = tree.root();

        let mut child_nodes = root.child_nodes(&tree);
        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);
        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), SyntaxKind::Call);
        assert!(child_nodes.next().is_none());

        let mut child_nodes = binary_expr.child_nodes(&tree);
        assert_eq!(child_nodes.next().unwrap().kind(&tree), SyntaxKind::BinaryExpr);
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
        assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);
        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), SyntaxKind::Call);
        assert!(child_nodes.next().is_none());

        let mut child_tokens = binary_expr.child_tokens(&tree);
        assert_eq!(child_tokens.next().unwrap().kind(&tree), SyntaxKind::Plus);
        assert_eq!(child_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert!(child_tokens.next().is_none());

        let mut child_tokens = call.child_tokens(&tree);
        assert_eq!(child_tokens.next().unwrap().kind(&tree), SyntaxKind::Ident);
        assert!(child_tokens.next().is_none());
    }

    #[test]
    fn descendants() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendants = root.descendants(&tree);
        let binary_expr = descendants.next().unwrap().assert_node();
        assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);

        let binary_expr_2 = descendants.next().unwrap().assert_node();
        assert_eq!(binary_expr_2.kind(&tree), SyntaxKind::BinaryExpr);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), SyntaxKind::IntLiteral);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), SyntaxKind::Asterisk);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), SyntaxKind::IntLiteral);

        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), SyntaxKind::Plus);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), SyntaxKind::IntLiteral);

        let call = descendants.next().unwrap().assert_node();
        assert_eq!(call.kind(&tree), SyntaxKind::Call);
        assert_eq!(descendants.next().unwrap().assert_token().kind(&tree), SyntaxKind::Ident);
        assert!(descendants.next().is_none());

        let mut descendants = binary_expr.child_nodes(&tree);
        assert_eq!(descendants.next().unwrap().kind(&tree), SyntaxKind::BinaryExpr);
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
        assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);
        let binary_expr_2 = descendant_nodes.next().unwrap();
        assert_eq!(binary_expr_2.kind(&tree), SyntaxKind::BinaryExpr);
        let call = descendant_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), SyntaxKind::Call);
        assert!(descendant_nodes.next().is_none());

        let mut descendant_nodes = binary_expr.child_nodes(&tree);
        assert_eq!(descendant_nodes.next().unwrap().kind(&tree), SyntaxKind::BinaryExpr);
        assert!(descendant_nodes.next().is_none());

        let mut descendant_nodes = call.child_nodes(&tree);
        assert!(descendant_nodes.next().is_none());
    }

    #[test]
    fn descendant_tokens() {
        let tree = example_tree();
        let root = tree.root();

        let mut descendant_tokens = root.descendant_tokens(&tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::Asterisk);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::Plus);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::Ident);
        assert!(descendant_tokens.next().is_none());

        let mut child_nodes = root.child_nodes(&tree);

        let binary_expr = child_nodes.next().unwrap();
        assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);
        let mut descendant_tokens = binary_expr.descendant_tokens(&tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::Asterisk);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::Plus);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::IntLiteral);
        assert!(descendant_tokens.next().is_none());

        let call = child_nodes.next().unwrap();
        assert_eq!(call.kind(&tree), SyntaxKind::Call);
        let mut descendant_tokens = call.descendant_tokens(&tree);
        assert_eq!(descendant_tokens.next().unwrap().kind(&tree), SyntaxKind::Ident);
        assert!(descendant_tokens.next().is_none());

        assert!(child_nodes.next().is_none());
    }
}
