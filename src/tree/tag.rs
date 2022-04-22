use crate::{SyntaxKind, TreeConfig};

#[derive(Clone, Copy)]
#[repr(transparent)]
pub(super) struct Tag(u16);

impl Tag {
    pub(crate) const MAX_KIND: u16 = (u16::MAX >> 1) - 1; // all 1s apart from first and last

    pub(super) fn start_node<C: TreeConfig>(kind: C::NodeKind) -> Self {
        let raw = kind.to_raw();
        debug_assert!(raw < C::NodeKind::LAST);
        debug_assert!(raw <= Self::MAX_KIND);
        Self(raw | 1 << 15) // set high bit to 1
    }

    pub(super) fn add_token<C: TreeConfig>(kind: C::TokenKind) -> Self {
        let raw = kind.to_raw();
        debug_assert!(raw < C::TokenKind::LAST);
        debug_assert!(raw <= Self::MAX_KIND);
        Self(raw)
    }

    pub(super) fn finish_node() -> Self {
        Self(u16::MAX)
    }

    pub(super) fn is_start_node(self) -> bool {
        self.high_bit_is_1() && !self.is_finish_node()
    }

    pub(super) fn is_add_token(self) -> bool {
        !self.high_bit_is_1()
    }

    pub(super) fn is_finish_node(self) -> bool {
        self.0 == u16::MAX
    }

    pub(super) fn get_start_node_kind<C: TreeConfig>(self) -> C::NodeKind {
        debug_assert!(self.is_start_node());
        let raw = self.0 & u16::MAX >> 1; // zero out high bit
        debug_assert!(raw < C::NodeKind::LAST);
        debug_assert!(raw <= Self::MAX_KIND);
        unsafe { C::NodeKind::from_raw(raw) }
    }

    pub(super) fn get_add_token_kind<C: TreeConfig>(self) -> C::TokenKind {
        debug_assert!(self.is_add_token());
        debug_assert!(self.0 < C::TokenKind::LAST);
        debug_assert!(self.0 <= Self::MAX_KIND);
        unsafe { C::TokenKind::from_raw(self.0) }
    }

    fn high_bit_is_1(self) -> bool {
        self.0 & 1 << 15 != 0
    }
}
