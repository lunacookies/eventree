#![allow(clippy::missing_safety_doc)]

use std::fmt::Debug;
use std::hash::Hash;

pub unsafe trait SyntaxKind:
    Debug + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Hash
{
    const LAST: u16;
    fn to_raw(self) -> u16;
    unsafe fn from_raw(raw: u16) -> Self;
}
