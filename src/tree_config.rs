use crate::SyntaxKind;
use std::fmt::Debug;
use std::hash::Hash;

/// Ties together the types used to identify kinds of nodes and kinds of tokens.
///
/// Since a `TreeConfig` is never actually constructed
/// and exists just to connect a `NodeKind` and a `TokenKind`,
/// an *uninhabitable type* such as `enum Foo {}`
/// can be used. For instance:
///
/// ```
/// # #[derive(Debug, PartialEq)]
/// # enum MyNodeKind { Root, __Last }
/// # #[derive(Debug, PartialEq)]
/// # enum MyTokenKind { Foo, __Last }
/// # unsafe impl eventree::SyntaxKind for MyNodeKind { const LAST: u16 = Self::__Last as u16; fn to_raw(self) -> u16 { self as u16 } unsafe fn from_raw(raw: u16) -> Self { unsafe { std::mem::transmute(raw as u8) } } }
/// # unsafe impl eventree::SyntaxKind for MyTokenKind { const LAST: u16 = Self::__Last as u16; fn to_raw(self) -> u16 { self as u16 } unsafe fn from_raw(raw: u16) -> Self { unsafe { std::mem::transmute(raw as u8) } } }
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// enum TreeConfig {}
///
/// impl eventree::TreeConfig for TreeConfig {
///     type NodeKind = MyNodeKind;
///     type TokenKind = MyTokenKind;
/// }
/// ```
///
/// See [`SyntaxKind`] for details on creating a `NodeKind` and `TokenKind`.
pub trait TreeConfig: Debug + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// The kind of nodes in the syntax tree.
    type NodeKind: SyntaxKind;

    /// The kind of tokens in the syntax tree.
    type TokenKind: SyntaxKind;
}
