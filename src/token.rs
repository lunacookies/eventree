use crate::tree::EventIdx;
use crate::{SyntaxTree, TextRange, TreeConfig};
use std::marker::PhantomData;

/// A handle to a specific token in a specific [`SyntaxTree`].
///
/// All accessor methods will panic if used with a tree
/// other than the one this token is from.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxToken<C> {
    idx: EventIdx,
    tree_id: u32,
    phantom: PhantomData<C>,
}

static_assertions::assert_eq_size!(SyntaxToken<()>, Option<SyntaxToken<()>>, u64);

impl<C: TreeConfig> SyntaxToken<C> {
    #[inline(always)]
    pub(crate) unsafe fn new(idx: EventIdx, tree_id: u32) -> Self {
        Self { idx, tree_id, phantom: PhantomData }
    }

    /// Returns the kind of this token.
    pub fn kind(self, tree: &SyntaxTree<C>) -> C::TokenKind {
        self.verify_tree(tree);
        unsafe { tree.get_add_token(self.idx).kind }
    }

    /// Returns the text associated with this token.
    pub fn text(self, tree: &SyntaxTree<C>) -> &str {
        self.verify_tree(tree);
        unsafe {
            let add_token = tree.get_add_token(self.idx);
            tree.get_text(add_token.start, add_token.end)
        }
    }

    /// Returns the range this token spans in the original input.
    pub fn text_range(self, tree: &SyntaxTree<C>) -> TextRange {
        self.verify_tree(tree);
        let add_token = unsafe { tree.get_add_token(self.idx) };
        TextRange::new(add_token.start.into(), add_token.end.into())
    }

    fn verify_tree(self, tree: &SyntaxTree<C>) {
        assert_eq!(
            self.tree_id,
            tree.id(),
            "tried to access token data from tree other than the one this token is from"
        );
    }
}
