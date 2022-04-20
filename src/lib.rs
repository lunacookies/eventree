#![doc = include_str!("../README.md")]

mod element;
mod kind;
mod node;
mod token;
mod tree;

pub use self::element::SyntaxElement;
pub use self::kind::SyntaxKind;
pub use self::node::SyntaxNode;
pub use self::token::SyntaxToken;
pub use self::tree::{SyntaxBuilder, SyntaxTree};
