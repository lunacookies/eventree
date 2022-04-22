use crate::{SyntaxTree, TreeConfig};
use std::marker::PhantomData;
use std::num::NonZeroU32;
use text_size::TextRange;

/// A handle to a specific token in a specific [`SyntaxTree`].
///
/// All accessor methods will panic if used with a tree
/// other than the one this token is from.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxToken<C> {
    idx: NonZeroU32,
    tree_id: u32,
    phantom: PhantomData<C>,
}

static_assertions::assert_eq_size!(SyntaxToken<()>, Option<SyntaxToken<()>>, u64);

impl<C: TreeConfig> SyntaxToken<C> {
    #[inline(always)]
    pub(crate) fn new(idx: u32, tree_id: u32) -> Self {
        Self {
            idx: if cfg!(debug_assertions) {
                NonZeroU32::new(idx).unwrap()
            } else {
                unsafe { NonZeroU32::new_unchecked(idx) }
            },
            tree_id,
            phantom: PhantomData,
        }
    }

    /// Returns the kind of this token.
    pub fn kind(self, tree: &SyntaxTree<C>) -> C::TokenKind {
        self.verify_tree(tree);
        unsafe { tree.get_add_token(self.idx.get()).0 }
    }

    /// Returns the text associated with this token.
    pub fn text(self, tree: &SyntaxTree<C>) -> &str {
        self.verify_tree(tree);
        unsafe {
            let (_, start, end) = tree.get_add_token(self.idx.get());
            tree.get_text(start, end)
        }
    }

    /// Returns the range this token spans in the original input.
    pub fn range(self, tree: &SyntaxTree<C>) -> TextRange {
        self.verify_tree(tree);
        let (_, start, end) = unsafe { tree.get_add_token(self.idx.get()) };
        TextRange::new(start.into(), end.into())
    }

    fn verify_tree(self, tree: &SyntaxTree<C>) {
        assert_eq!(
            self.tree_id,
            tree.id(),
            "tried to access token data from tree other than the one this token is from"
        );
    }
}
