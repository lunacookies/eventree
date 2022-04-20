use crate::{SyntaxKind, SyntaxTree};
use std::marker::PhantomData;
use std::num::NonZeroU32;
use text_size::TextRange;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxToken<K> {
    idx: NonZeroU32,
    tree_id: u32,
    phantom: PhantomData<K>,
}

static_assertions::assert_eq_size!(SyntaxToken<()>, Option<SyntaxToken<()>>, u64);

impl<K: SyntaxKind> SyntaxToken<K> {
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

    pub fn kind(self, tree: &SyntaxTree<K>) -> K {
        self.verify_tree(tree);
        unsafe { tree.get_add_token(self.idx.get()).0 }
    }

    pub fn text(self, tree: &SyntaxTree<K>) -> &str {
        self.verify_tree(tree);
        unsafe {
            let (_, start, end) = tree.get_add_token(self.idx.get());
            tree.get_text(start, end)
        }
    }

    pub fn range(self, tree: &SyntaxTree<K>) -> TextRange {
        self.verify_tree(tree);
        let (_, start, end) = unsafe { tree.get_add_token(self.idx.get()) };
        TextRange::new(start.into(), end.into())
    }

    fn verify_tree(self, tree: &SyntaxTree<K>) {
        assert_eq!(
            self.tree_id,
            tree.id(),
            "tried to access token data from tree other than the one this token is from"
        );
    }
}
