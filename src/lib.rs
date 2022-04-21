//! ###### A Rust library for creating lossless syntax trees.
//!
//! Let’s construct a syntax tree that can represent the following expression:
//!
//! ```text
//! foo+10*20
//! ```
//!
//! This is the tree we want to build:
//!
//! ```text
//! Root
//!   BinaryExpr
//!     Ident "foo"
//!     Plus "+"
//!     BinaryExpr
//!       Number "10"
//!       Star "*"
//!       Number "20"
//! ```
//!
//! What kinds of nodes and tokens do we have here?
//!
//! ```
//! enum SyntaxKind {
//!     Root,
//!     BinaryExpr,
//!     Number,
//!     Ident,
//!     Plus,
//!     Star,
//! }
//! ```
//!
//! We need some extra boilerplate, though.
//! Don’t let the `unsafe` scare you away just yet!
//!
//! ```
//! #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! #[repr(u16)]
//! enum SyntaxKind {
//!     Root,
//!     BinaryExpr,
//!     Number,
//!     Ident,
//!     Plus,
//!     Star,
//!     #[doc(hidden)]
//!     __Last,
//! }
//!
//! unsafe impl eventree::SyntaxKind for SyntaxKind {
//!     const LAST: u16 = Self::__Last as u16;
//!
//!     fn to_raw(self) -> u16 {
//!         self as u16
//!     }
//!
//!     unsafe fn from_raw(raw: u16) -> Self {
//!         unsafe { std::mem::transmute(raw) }
//!     }
//! }
//! ```
//!
//! Continue by creating a [`SyntaxBuilder`],
//! which lets you construct syntax trees:
//!
//! ```
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! # #[repr(u16)]
//! # enum SyntaxKind { Root, BinaryExpr, Number, Ident, Plus, Star, __Last }
//! # unsafe impl eventree::SyntaxKind for SyntaxKind {
//! #     const LAST: u16 = Self::__Last as u16;
//! #     fn to_raw(self) -> u16 { self as u16 }
//! #     unsafe fn from_raw(raw: u16) -> Self { unsafe { std::mem::transmute(raw) } }
//! # }
//! let mut builder = eventree::SyntaxBuilder::new("foo+10*20");
//! # builder.start_node(SyntaxKind::Root); // to infer type
//! ```
//!
//! eventree, as the name implies (thanks [Quirl](https://github.com/domenicquirl/)!),
//! is based around *events.*
//! To explain what that means, let me bring back that syntax tree from earlier:
//!
//! ```text
//! Root
//!   BinaryExpr
//!     Ident "foo"
//!     Plus "+"
//!     BinaryExpr
//!       Number "10"
//!       Star "*"
//!       Number "20"
//! ```
//!
//! And now as events:
//!
//! ```text
//! START_NODE Root
//!   START_NODE BinaryExpr
//!     ADD_TOKEN Ident "foo"
//!     ADD_TOKEN Plus "+"
//!     START_NODE BinaryExpr
//!       ADD_TOKEN Number "10"
//!       ADD_TOKEN Star "*"
//!       ADD_TOKEN Number "20"
//!     FINISH_NODE
//!   FINISH_NODE
//! FINISH_NODE
//! ```
//!
//! What’s great about this is that we’ve transformed a tree structure into a flat sequence.
//! Maybe it’s a bit more obvious if I show it like this:
//!
//! ```text
//! [
//!     START_NODE Root,
//!     START_NODE BinaryExpr,
//!     ADD_TOKEN Ident "foo",
//!     ADD_TOKEN Plus "+",
//!     START_NODE BinaryExpr,
//!     ADD_TOKEN Number "10",
//!     ADD_TOKEN Star "*",
//!     ADD_TOKEN Number "20",
//!     FINISH_NODE,
//!     FINISH_NODE,
//!     FINISH_NODE,
//! ]
//! ```
//!
//! What eventree does is it stores a sequence of events like the one above
//! in an [efficient format][`SyntaxTree#format`],
//! while providing convenient APIs for traversing the tree.
//!
//! Before we get too ahead of ourselves, let’s construct the tree:
//!
//! ```
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! # #[repr(u16)]
//! # enum SyntaxKind { Root, BinaryExpr, Number, Ident, Plus, Star, __Last }
//! # unsafe impl eventree::SyntaxKind for SyntaxKind {
//! #     const LAST: u16 = Self::__Last as u16;
//! #     fn to_raw(self) -> u16 { self as u16 }
//! #     unsafe fn from_raw(raw: u16) -> Self { unsafe { std::mem::transmute(raw) } }
//! # }
//! use eventree::SyntaxBuilder;
//! use text_size::TextRange;
//!
//! let mut builder = SyntaxBuilder::new("foo+10*20");
//! builder.start_node(SyntaxKind::Root);
//! builder.start_node(SyntaxKind::BinaryExpr);
//! builder.add_token(SyntaxKind::Ident, TextRange::new(0.into(), 3.into()));
//! builder.add_token(SyntaxKind::Plus, TextRange::new(3.into(), 4.into()));
//! builder.start_node(SyntaxKind::BinaryExpr);
//! builder.add_token(SyntaxKind::Number, TextRange::new(4.into(), 6.into()));
//! builder.add_token(SyntaxKind::Star, TextRange::new(6.into(), 7.into()));
//! builder.add_token(SyntaxKind::Number, TextRange::new(7.into(), 9.into()));
//! builder.finish_node();
//! builder.finish_node();
//! builder.finish_node();
//! ```
//!
//! Note how rather than specifying the text of each token directly
//! we’re instead just passing the range of each one in the original input.
//!
//! The last thing we’ll go over is some examples of the APIs eventree provides.
//!
//! ```
//! # #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
//! # #[repr(u16)]
//! # enum SyntaxKind { Root, BinaryExpr, Number, Ident, Plus, Star, __Last }
//! # unsafe impl eventree::SyntaxKind for SyntaxKind {
//! #     const LAST: u16 = Self::__Last as u16;
//! #     fn to_raw(self) -> u16 { self as u16 }
//! #     unsafe fn from_raw(raw: u16) -> Self { unsafe { std::mem::transmute(raw) } }
//! # }
//! # use text_size::TextRange;
//! use eventree::{SyntaxBuilder, SyntaxNode, SyntaxToken, SyntaxTree};
//!
//! let mut builder = SyntaxBuilder::new("foo+10*20");
//! builder.start_node(SyntaxKind::Root);
//! // ...
//! # builder.start_node(SyntaxKind::BinaryExpr);
//! # builder.add_token(SyntaxKind::Ident, TextRange::new(0.into(), 3.into()));
//! # builder.add_token(SyntaxKind::Plus, TextRange::new(3.into(), 4.into()));
//! # builder.start_node(SyntaxKind::BinaryExpr);
//! # builder.add_token(SyntaxKind::Number, TextRange::new(4.into(), 6.into()));
//! # builder.add_token(SyntaxKind::Star, TextRange::new(6.into(), 7.into()));
//! # builder.add_token(SyntaxKind::Number, TextRange::new(7.into(), 9.into()));
//! # builder.finish_node();
//! # builder.finish_node();
//! builder.finish_node();
//!
//! // type annotations are just for demonstration -- you don’t actually need them!
//!
//! let tree: SyntaxTree<_> = builder.finish();
//!
//! // let’s get the root of the tree
//! let root: SyntaxNode<_> = tree.root();
//!
//! // we can get the kind, text and range of nodes
//! assert_eq!(root.kind(&tree), SyntaxKind::Root);
//! assert_eq!(root.text(&tree), "foo+10*20");
//! assert_eq!(root.range(&tree), TextRange::new(0.into(), 9.into()));
//!
//! // we can get the child nodes in the root; there’s just one, the BinaryExpr
//! let mut child_nodes = root.child_nodes(&tree);
//! let binary_expr: SyntaxNode<_> = child_nodes.next().unwrap();
//! assert_eq!(binary_expr.kind(&tree), SyntaxKind::BinaryExpr);
//! assert!(child_nodes.next().is_none());
//!
//! // let’s look at the descendant tokens of the BinaryExpr
//! let mut descendant_tokens = binary_expr.descendant_tokens(&tree);
//!
//! // we can also get the kind, text and range of tokens
//! let ident: SyntaxToken<_> = descendant_tokens.next().unwrap();
//! assert_eq!(ident.kind(&tree), SyntaxKind::Ident);
//! assert_eq!(ident.text(&tree), "foo");
//! assert_eq!(ident.range(&tree), TextRange::new(0.into(), 3.into()));
//!
//! // let’s finish off by going through all descendant tokens
//! // until we reach the end
//! assert_eq!(descendant_tokens.next().unwrap().text(&tree), "+");
//! assert_eq!(descendant_tokens.next().unwrap().text(&tree), "10");
//! assert_eq!(descendant_tokens.next().unwrap().text(&tree), "*");
//! assert_eq!(descendant_tokens.next().unwrap().text(&tree), "20");
//! assert!(descendant_tokens.next().is_none());
//! ```
//!
//! I hope this was helpful!

#![warn(missing_docs, unreachable_pub, rust_2018_idioms)]

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
