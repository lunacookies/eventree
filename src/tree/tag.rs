use super::EventKind;
use crate::TreeConfig;

#[derive(Clone, Copy)]
#[repr(transparent)]
pub(super) struct Tag(u16);

impl Tag {
    const MAX_KIND: u16 = (u16::MAX >> 1) - 1; // all 1s apart from first and last

    pub(super) fn start_node<C: TreeConfig>(kind: C::NodeKind) -> Self {
        let raw = C::node_kind_to_raw(kind);
        debug_assert!(raw <= Self::MAX_KIND);
        Self(raw | 1 << 15) // set high bit to 1
    }

    pub(super) fn add_token<C: TreeConfig>(kind: C::TokenKind) -> Self {
        let raw = C::token_kind_to_raw(kind);
        debug_assert!(raw <= Self::MAX_KIND);
        Self(raw)
    }

    pub(super) fn finish_node() -> Self {
        Self(u16::MAX)
    }

    pub(super) fn event_kind(self) -> EventKind {
        if self.high_bit_is_1() {
            if self.0 == u16::MAX {
                EventKind::FinishNode
            } else {
                EventKind::StartNode
            }
        } else {
            EventKind::AddToken
        }
    }

    pub(super) fn get_start_node_kind<C: TreeConfig>(self) -> C::NodeKind {
        debug_assert_eq!(self.event_kind(), EventKind::StartNode);
        let raw = self.0 & u16::MAX >> 1; // zero out high bit
        debug_assert!(raw <= Self::MAX_KIND);
        unsafe { C::node_kind_from_raw(raw) }
    }

    pub(super) fn get_add_token_kind<C: TreeConfig>(self) -> C::TokenKind {
        debug_assert_eq!(self.event_kind(), EventKind::AddToken);
        debug_assert!(self.0 <= Self::MAX_KIND);
        unsafe { C::token_kind_from_raw(self.0) }
    }

    fn high_bit_is_1(self) -> bool {
        self.0 & 1 << 15 != 0
    }
}
