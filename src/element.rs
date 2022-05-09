use crate::{SyntaxNode, SyntaxToken};

/// An element of a syntax tree.
/// Either a node or a token.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntaxElement<C> {
    #[allow(missing_docs)]
    Node(SyntaxNode<C>),
    #[allow(missing_docs)]
    Token(SyntaxToken<C>),
}

impl<C> SyntaxElement<C> {
    /// Asserts this element is a node. Panics if it was actually a token.
    pub fn unwrap_node(self) -> SyntaxNode<C> {
        match self {
            Self::Node(node) => node,
            Self::Token(_) => panic!("expected node"),
        }
    }

    /// Asserts this element is a token. Panics if it was actually a node.
    pub fn unwrap_token(self) -> SyntaxToken<C> {
        match self {
            Self::Node(_) => panic!("expected token"),
            Self::Token(token) => token,
        }
    }
}
