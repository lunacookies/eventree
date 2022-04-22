use std::fmt::Debug;
use std::hash::Hash;

/// A trait for converting between eventree’s
/// [internal kind representation][`crate::SyntaxTree#tag`]
/// and your own custom enums for the kinds of nodes and tokens.
///
/// # Safety
///
/// This trait is `unsafe` to implement
/// because you must satisfy the following requirements:
///
/// - all values returned by [`SyntaxKind::to_raw`] must be less than [`SyntaxKind::LAST`]
/// - [`SyntaxKind::LAST`] must be less than or equal to `0b0111_1111_1111_1110`
///   ([why?][`crate::SyntaxTree#tag`])
/// - values must be roundtrippable through [`SyntaxKind::to_raw`], [`SyntaxKind::from_raw`]
///   and back
///
/// Not fulfilling these requirements can result in undefined behaviour.
///
/// # Example
///
/// ```
/// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// #[repr(u16)]
/// enum NodeKind {
///     Root,
///     Function,
///     Struct,
///     BinaryExpr,
///     CallExpr,
///     #[doc(hidden)]
///     __Last, // ⚠️ NOTE ⚠️ passing this variant into to_raw would technically violate
/// }           // the trait’s contract, but we’ll pretend it’s fine
///             // because it has two underscores so no one will use it, right??
///
/// // SAFETY:
/// // - we have less than 0b0111_1111_1111_1110 (32,766) enum variants
/// // - LAST is larger than all variants
/// // - values returned by to_raw can be passed into from_raw safely
/// unsafe impl eventree::SyntaxKind for NodeKind {
///     const LAST: u16 = Self::__Last as u16;
///
///     fn to_raw(self) -> u16 {
///         self as u16
///     }
///
///     unsafe fn from_raw(raw: u16) -> Self {
///         unsafe { std::mem::transmute(raw) }
///     }
/// }
/// ```
pub unsafe trait SyntaxKind:
    Debug + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash
{
    /// A value larger than all values of your enum.
    ///
    /// # Suggested implementation
    /// It is intended to be your last enum variant,
    /// so as you add more variants its value increases automatically.
    ///
    /// # Contract
    /// It is up to you, the trait implementor,
    /// to ensure that this value is less than or equal to `0b0111_1111_1111_1110`.
    const LAST: u16;

    /// Converts your custom type to a `u16`.
    ///
    /// # Suggested implementation
    /// Generally you will impement this by casting your enum using `as` syntax.
    /// Putting any more complex logic than that here will result in worse tree performance.
    ///
    /// # Contract
    /// Part of this trait’s contract is that all values returned by this method
    /// are less than [`SyntaxKind::LAST`].
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
    /// a degredation in tree performance.
    unsafe fn from_raw(raw: u16) -> Self;
}
