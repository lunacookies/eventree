use crate::{SyntaxNode, SyntaxToken};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SyntaxElement<K> {
    Node(SyntaxNode<K>),
    Token(SyntaxToken<K>),
}

impl<K> SyntaxElement<K> {
    pub fn assert_node(self) -> SyntaxNode<K> {
        match self {
            Self::Node(node) => node,
            Self::Token(_) => panic!("expected node"),
        }
    }

    pub fn assert_token(self) -> SyntaxToken<K> {
        match self {
            Self::Node(_) => panic!("expected token"),
            Self::Token(token) => token,
        }
    }
}
