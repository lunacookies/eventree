use crate::{SyntaxNode, SyntaxToken};

/// An element of a syntax tree.
/// Either a node or a token.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntaxElement<N, T> {
    #[allow(missing_docs)]
    Node(SyntaxNode<N>),
    #[allow(missing_docs)]
    Token(SyntaxToken<T>),
}

impl<N, T> SyntaxElement<N, T> {
    /// Asserts this element is a node. Panics if it was actually a token.
    pub fn assert_node(self) -> SyntaxNode<N> {
        match self {
            Self::Node(node) => node,
            Self::Token(_) => panic!("expected node"),
        }
    }

    /// Asserts this element is a token. Panics if it was actually a node.
    pub fn assert_token(self) -> SyntaxToken<T> {
        match self {
            Self::Node(_) => panic!("expected token"),
            Self::Token(token) => token,
        }
    }
}
