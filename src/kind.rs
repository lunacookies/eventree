use std::fmt::Debug;

/// A trait for converting between eventree’s
/// [internal kind representation][`crate::SyntaxTree#tag`]
/// and your own custom enums for the kinds of nodes and tokens.
///
/// # Safety
///
/// This trait is `unsafe` to implement
/// because you must satisfy the following requirements:
///
/// - all values returned by [`SyntaxKind::to_raw`]
///   must be less than or equal to `0b0111_1111_1111_1110`
///   ([why?][`crate::SyntaxTree#tag`])
/// - values must be roundtrippable through [`SyntaxKind::to_raw`],
///   [`SyntaxKind::from_raw`] and back
///
/// Not fulfilling these requirements can result in undefined behaviour.
///
/// # Example
///
/// ```
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// #[repr(u8)]
/// enum NodeKind {
///     Root,
///     Function,
///     Struct,
///     BinaryExpr,
///     CallExpr,
/// }
///
/// // SAFETY:
/// // - we have less than 0b0111_1111_1111_1110 (32,766) enum variants
/// // - values returned by to_raw can be passed into from_raw safely
/// unsafe impl eventree::SyntaxKind for NodeKind {
///     fn to_raw(self) -> u16 {
///         self as u16
///     }
///
///     unsafe fn from_raw(raw: u16) -> Self {
///         std::mem::transmute(raw as u8)
///     }
/// }
/// ```
pub unsafe trait SyntaxKind: Debug {
    /// Converts your custom type to a `u16`.
    ///
    /// # Suggested implementation
    /// Generally you will implement this by casting your enum using `as` syntax.
    /// Putting any more complex logic than that here will result in worse tree performance.
    ///
    /// # Contract
    /// Part of this trait’s contract is that all values returned by this method
    /// are less than or equal to `0b0111_1111_1111_1110`.
    fn to_raw(self) -> u16;

    /// Turns a raw `u16` back into your custom type.
    ///
    /// # Safety
    /// This method must only be called with values returned by [`SyntaxKind::to_raw`];
    /// if it isn’t, your implementation is allowed to invoke undefined behaviour
    /// (which is why this method is `unsafe`).
    ///
    /// # Suggested implementation
    /// One way to implement this method is to use [`std::mem::transmute`]
    /// (given that your [`SyntaxKind::to_raw`] method just returns your enum’s value).
    /// Any expensive operations performed here will result in
    /// a degradation in tree performance.
    unsafe fn from_raw(raw: u16) -> Self;
}
