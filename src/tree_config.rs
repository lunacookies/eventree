use std::fmt::Debug;
use std::hash::Hash;

/// A trait for converting between eventree’s
/// [internal kind representation][`crate::SyntaxTree#tag`]
/// and your own custom enums for the kinds of nodes and tokens.
///
/// Since a `TreeConfig` is never actually constructed
/// and exists just to connect a `NodeKind` and a `TokenKind`,
/// an *uninhabitable type* such as `enum Foo {}`
/// can be used. For instance:
///
/// ```
/// #[derive(Debug, PartialEq)]
/// #[repr(u8)]
/// enum MyNodeKind { Root, Foo }
///
/// #[derive(Debug, PartialEq)]
/// #[repr(u8)]
/// enum MyTokenKind { Bar, Baz }
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// enum TreeConfig {}
///
/// // SAFETY:
/// // - we have less than 0b0111_1111_1111_1110 (32,766) enum variants
/// // - values returned by to_raw can be passed into from_raw safely
/// unsafe impl eventree::TreeConfig for TreeConfig {
///     type NodeKind = MyNodeKind;
///     type TokenKind = MyTokenKind;
///
///     fn node_kind_to_raw(node_kind: Self::NodeKind) -> u16 {
///         node_kind as u16
///     }
///
///     fn token_kind_to_raw(token_kind: Self::TokenKind) -> u16 {
///         token_kind as u16
///     }
///
///     unsafe fn node_kind_from_raw(raw: u16) -> Self::NodeKind {
///         std::mem::transmute(raw as u8)
///     }
///
///     unsafe fn token_kind_from_raw(raw: u16) -> Self::TokenKind {
///         std::mem::transmute(raw as u8)
///     }
/// }
/// ```
///
/// # Safety
///
/// This trait is `unsafe` to implement
/// because you must satisfy the following requirements:
///
/// - all values returned by [`TreeConfig::node_kind_to_raw`] and [`TreeConfig::token_kind_to_raw`]
///   must be less than or equal to `0b0111_1111_1111_1110`
/// - values must be roundtrippable through the `to_raw` methods
///   and back through the `from_raw` methods
///
/// Not fulfilling these requirements can result in undefined behaviour.
pub unsafe trait TreeConfig:
    Debug + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash
{
    /// The kind of nodes in the syntax tree.
    type NodeKind: Debug;

    /// The kind of tokens in the syntax tree.
    type TokenKind: Debug;

    /// Converts your custom type to a `u16`.
    ///
    /// # Suggested implementation
    /// Generally you will implement this by casting your enum using `as` syntax.
    /// Putting any more complex logic than that here will result in worse tree performance.
    ///
    /// # Contract
    /// Part of this trait’s contract is that all values returned by this method
    /// are less than or equal to `0b0111_1111_1111_1110`.
    fn node_kind_to_raw(node_kind: Self::NodeKind) -> u16;

    /// Converts your custom type to a `u16`.
    ///
    /// # Suggested implementation
    /// Generally you will implement this by casting your enum using `as` syntax.
    /// Putting any more complex logic than that here will result in worse tree performance.
    ///
    /// # Contract
    /// Part of this trait’s contract is that all values returned by this method
    /// are less than or equal to `0b0111_1111_1111_1110`.
    fn token_kind_to_raw(token_kind: Self::TokenKind) -> u16;

    /// Turns a raw `u16` back into your custom type.
    ///
    /// # Safety
    /// This method must only be called with values returned by [`TreeConfig::node_kind_to_raw`];
    /// if it isn’t, your implementation is allowed to invoke undefined behaviour
    /// (which is why this method is `unsafe`).
    ///
    /// # Suggested implementation
    /// One way to implement this method is to use [`std::mem::transmute`]
    /// (given that your [`TreeConfig::node_kind_to_raw`] method just returns your enum’s value).
    /// Make sure to specify the representation of your enum (e.g. with `#[repr(u8)]`)
    /// since [transmuting non-primitive types without a specified representation
    /// is undefined behaviour][ref].
    ///
    /// Any expensive operations performed here will result in
    /// a degradation in tree performance.
    ///
    /// [ref]: https://doc.rust-lang.org/reference/type-layout.html#the-default-representation
    unsafe fn node_kind_from_raw(raw: u16) -> Self::NodeKind;

    /// Turns a raw `u16` back into your custom type.
    ///
    /// # Safety
    /// This method must only be called with values returned by [`TreeConfig::token_kind_to_raw`];
    /// if it isn’t, your implementation is allowed to invoke undefined behaviour
    /// (which is why this method is `unsafe`).
    ///
    /// # Suggested implementation
    /// One way to implement this method is to use [`std::mem::transmute`]
    /// (given that your [`TreeConfig::token_kind_to_raw`] method just returns your enum’s value).
    /// Make sure to specify the representation of your enum (e.g. with `#[repr(u8)]`)
    /// since [transmuting non-primitive types without a specified representation
    /// is undefined behaviour][ref].
    ///
    /// Any expensive operations performed here will result in
    /// a degradation in tree performance.
    ///
    /// [ref]: https://doc.rust-lang.org/reference/type-layout.html#the-default-representation
    unsafe fn token_kind_from_raw(raw: u16) -> Self::TokenKind;
}
