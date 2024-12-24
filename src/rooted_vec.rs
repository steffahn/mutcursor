
use core::{marker::PhantomData, ops::DerefMut, ptr::NonNull};
use maybe_dangling::MaybeDangling;
use stable_deref_trait::StableDeref;

/// Similar to [`MutCursorVec`](crate::MutCursorVec), but provides for a `RootT` type at the bottom of the
/// stack that is different from the `NodeT` types above it
///
/// Usage Note: This type owns (as opposed to borrows) the root object from which the rest of the
/// stack descends, therefore, it can be used without an associated lifetime. For API soundness,
/// you still have to define a “lower bound” for type validity.
///
/// In many cases, you can however simply use
/// `MutCursorRootedVec<'static, RootT, NodeT>`. This requires `RootT: 'static` and `NodeT: 'static`
/// which are validity bound on the *types* but these don't imply that any data must *actually* life that long
/// at run-time.
///
/// To give another example: If `RootT` is a container type `SomeRoot<'a>` containing `&'a mut NoteT`
/// that you want to [`advance`][MutCursorRootedVec::advance_if_empty] into,
/// you could use `MutCursorRootedVec<'a, SomeRoot<'a>, NodeT>`.
///
/// `MutCursorRootedVec` doesn't implement [`Deref`](core::ops::Deref), and accessors return [`Option`], so therefore it is
/// allowed to be empty, unlike some of the other types in this crate.
///
/// `MutCursorRootedVec` is not available if the [`alloc`](crate::features#alloc) feature is disabled.
/// (The feature is enabled by default.)
pub struct MutCursorRootedVec<'l, RootT: 'l, NodeT: ?Sized + 'l> {
    top: Option<NonNull<NodeT>>,
    root: MaybeDangling<Option<RootT>>,
    stack: alloc::vec::Vec<NonNull<NodeT>>,
    _marker: PhantomData<(&'l RootT, &'l mut NodeT)>, // root covariant, node invariant
}

unsafe impl<'l, RootT, NodeT: ?Sized> Sync for MutCursorRootedVec<'l, RootT, NodeT>
where
    RootT: Sync,
    NodeT: Sync,
{
}
unsafe impl<'l, RootT, NodeT: ?Sized> Send for MutCursorRootedVec<'l, RootT, NodeT>
where
    RootT: Send,
    NodeT: Send,
{
}

impl<'l, RootT: 'l, NodeT: ?Sized + 'l> MutCursorRootedVec<'l, RootT, NodeT> {
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root
    #[inline]
    pub fn new(root: RootT) -> Self {
        Self {
            top: None,
            root: MaybeDangling::new(Some(root)),
            stack: alloc::vec::Vec::new(),
            _marker: PhantomData,
        }
    }
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root, and an allocated
    /// buffer for `capacity` references
    #[inline]
    pub fn new_with_capacity(root: RootT, capacity: usize) -> Self {
        Self {
            top: None,
            root: MaybeDangling::new(Some(root)),
            stack: alloc::vec::Vec::with_capacity(capacity),
            _marker: PhantomData,
        }
    }
    /// Returns `true` if the stack contains only the root, otherwise returns `false` if the stack
    /// contains one or more node references
    #[inline]
    pub fn is_root(&self) -> bool {
        self.top.is_none()
    }
    /// Returns a const reference from the mutable reference to the root, or `None` if the stack
    /// contains additional nodes obscuring the root
    #[inline]
    pub fn root(&self) -> Option<&RootT> {
        if self.top.is_none() {
            self.root.as_ref()
        } else {
            None
        }
    }
    /// Returns a const reference from the mutable reference on the top of the stack, or `None` if the
    /// stack contains only the root
    #[inline]
    pub fn top(&self) -> Option<&NodeT> {
        self.top.map(|node_ptr| unsafe{ node_ptr.as_ref() })
    }
    /// Returns the mutable reference on the root of the stack, or `None` if the stack contains additional
    /// references obscuring the root
    #[inline]
    pub fn root_mut(&mut self) -> Option<&mut RootT> {
        if self.top.is_none() {
            self.root.as_mut()
        } else {
            None
        }
    }
    /// Removes and returns the mutable reference on the root of the stack, or `None` if the
    /// root has already been taken
    ///
    /// This method effectively dumps the entire stack contents.
    #[inline]
    pub fn take_root(&mut self) -> Option<RootT> {
        self.to_root();
        self.root.take()
    }
    /// Replaces the root of the stack with the provided value
    ///
    /// Panics if the stack contains any references above the root
    #[inline]
    pub fn replace_root(&mut self, root: RootT) {
        if self.top.is_none() {
            *self.root = Some(root);
        } else {
            panic!("Illegal operation, unable to replace borrowed root");
        }
    }
    /// Returns the mutable reference on the top of the stack, or `None` if the stack contains only the root
    #[inline]
    pub fn top_mut(&mut self) -> Option<&mut NodeT> {
        self.top.map(|mut node_ptr| unsafe{ node_ptr.as_mut() })
    }
    /// Returns the mutable reference on the top of the stack.  If the stack contains only the root, this
    /// method will behave as if [`advance_if_empty`](Self::advance_if_empty) was called prior
    /// to [`top_mut`](Self::top_mut).
    ///
    /// Panics if the root has been taken via [`Self::take_root`]
    #[inline]
    pub fn top_or_advance_mut<F, NodeRef>(&mut self, step_f: F) -> &mut NodeT
    where
        F: FnOnce(&mut RootT) -> &mut NodeRef,
        NodeRef: DerefMut<Target = NodeT> + StableDeref + 'l,
        // Due to the effects of implied bounds, this   ^^^^  is important for soundness
    {
        match &self.top {
            Some(mut node_ptr) => unsafe{ node_ptr.as_mut() },
            None => {
                debug_assert_eq!(self.stack.len(), 0);
                let new_node_stable_ref = step_f(self.root.as_mut().unwrap());
                let mut node_ptr = NonNull::from(&mut **new_node_stable_ref);
                self.top = Some(node_ptr);
                unsafe{ node_ptr.as_mut() }
            }
        }
    }
    /// Returns the mutable reference on the top of the stack.  If the stack contains only the root, this
    /// method will behave as if [`advance_if_empty_twostep`](Self::advance_if_empty_twostep) was called prior
    /// to [`top_mut`](Self::top_mut).
    ///
    /// Panics if the root has been taken via [`Self::take_root`]
    ///
    /// This version of [`top_or_advance_mut`][Self::top_or_advance_mut] supports
    /// a second step, when the `RootT` doesn't contain any stable pointers
    /// *directly* to a `NodeT`.
    #[inline]
    pub fn top_or_advance_mut_twostep<F, G, IntermediateRef>(&mut self, step_f1: F, step_f2: G) -> &mut NodeT
    where
        F: FnOnce(&mut RootT) -> &mut IntermediateRef,
        IntermediateRef: DerefMut + StableDeref + 'l,
        // Due to the effects of implied bounds ^^^^ this is important for soundness
        G: FnOnce(&mut IntermediateRef::Target) -> &mut NodeT,
    {
        match &self.top {
            Some(mut node_ptr) => unsafe{ node_ptr.as_mut() },
            None => {
                debug_assert_eq!(self.stack.len(), 0);
                let intermediate_stable_ref = step_f1(self.root.as_mut().unwrap());
                let new_node = step_f2(intermediate_stable_ref);
                let mut node_ptr = NonNull::from(new_node);
                self.top = Some(node_ptr);
                unsafe{ node_ptr.as_mut() }
            }
        }
    }
    /// Returns the mutable reference on the root of the stack, consuming the stack
    ///
    /// Panics if the root of the stack has already been taken via [`Self::take_root`]
    #[inline]
    pub fn into_root(self) -> RootT {
        MaybeDangling::into_inner(self.root).unwrap()
    }
    /// Returns the number of node references stored in the stack, which corresponds to the number of
    /// times [backtrack](Self::backtrack) may be called before the stack is empty
    ///
    /// The root does not count, so a `MutCursorRootedVec` containing only the `RootT` will return
    /// `depth() == 0`.
    #[inline]
    pub fn depth(&self) -> usize {
        if self.top.is_some() {
            self.stack.len() + 1
        } else {
            0
        }
    }
    /// Returns the number of node references the stack is capable of holding without reallocation
    #[inline]
    pub fn capacity(&self) -> usize {
        self.stack.capacity() + 1
    }
    /// Begins the traversal if the stack contains only the root, otherwise does nothing
    ///
    /// Panics if the root has been taken via [`Self::take_root`]
    #[inline]
    pub fn advance_if_empty<F, NodeRef>(&mut self, step_f: F)
    where
        F: FnOnce(&mut RootT) -> &mut NodeRef,
        NodeRef: DerefMut<Target = NodeT> + StableDeref + 'l,
        // Due to the effects of implied bounds, this   ^^^^  is important for soundness
    {
        self.advance_if_empty_twostep(step_f, |node| node);
    }
    /// Begins the traversal if the stack contains only the root, otherwise does nothing
    ///
    /// Panics if the root has been taken via [`Self::take_root`]
    ///
    /// This version of [`advance_if_empty`][Self::advance_if_empty] supports
    /// a second step, when the `RootT` doesn't contain any stable pointers
    /// *directly* to a `NodeT`.
    #[inline]
    pub fn advance_if_empty_twostep<F, G, IntermediateRef>(&mut self, step_f1: F, step_f2: G)
    where
        F: FnOnce(&mut RootT) -> &mut IntermediateRef,
        IntermediateRef: DerefMut + StableDeref + 'l,
        // Due to the effects of implied bounds ^^^^ this is important for soundness
        G: FnOnce(&mut IntermediateRef::Target) -> &mut NodeT,
    {
        if self.top.is_none() {
            debug_assert_eq!(self.stack.len(), 0);
            let intermediate_stable_ref = step_f1(self.root.as_mut().unwrap());
            let new_node = step_f2(intermediate_stable_ref);
            let node_ptr = NonNull::from(new_node);
            self.top = Some(node_ptr);
        }
    }
    /// Begins the traversal by stepping from the root to the first node, pushing the first node
    /// reference onto the stack. Always resets the stack.
    ///
    /// If the `step_f` closure returns `Some` the existing stack will be replaced with the new node.
    /// If the `step_f` closure returns `None` the stack will be left completely empty.
    ///
    /// Panics if the root has been taken via [`Self::take_root`]
    #[inline]
    pub fn advance_from_root<F, NodeRef>(&mut self, step_f: F) -> bool
    where
        F: FnOnce(&mut RootT) -> Option<&mut NodeRef>,
        NodeRef: DerefMut<Target = NodeT> + StableDeref + 'l,
        // Due to the effects of implied bounds, this   ^^^^  is important for soundness
    {
        self.advance_from_root_twostep(step_f, |node| Some(node))
    }
    /// Begins the traversal by stepping from the root to the first node, pushing the first node
    /// reference onto the stack. Always resets the stack.
    ///
    /// If either of the `step_f…` closures returns `Some` the existing stack will be replaced with the new node.
    /// If either of the `step_f…` closures returns `None` the stack will be left completely empty.
    ///
    /// Panics if the root has been taken via [`Self::take_root`]
    ///
    /// This version of [`advance_from_root`][Self::advance_from_root] supports
    /// a second step, when the `RootT` doesn't contain any stable pointers
    /// *directly* to a `NodeT`.
    #[inline]
    pub fn advance_from_root_twostep<F, G, IntermediateRef>(&mut self, step_f1: F, step_f2: G) -> bool
    where
        F: FnOnce(&mut RootT) -> Option<&mut IntermediateRef>,
        IntermediateRef: DerefMut + StableDeref + 'l,
        // Due to the effects of implied bounds ^^^^ this is important for soundness
        G: FnOnce(&mut IntermediateRef::Target) -> Option<&mut NodeT>,
    {
        self.to_root();
        if let Some(intermediate_stable_ref) = step_f1(self.root.as_mut().unwrap()) {
            if let Some(new_node) = step_f2(intermediate_stable_ref) {
                let node_ptr = NonNull::from(new_node);
                self.top = Some(node_ptr);
                return true;
            }
        }
        false
    }
    /// Steps deeper into the traversal, pushing a new reference onto the top of the stack
    ///
    /// If the `step_f` closure returns `Some()`, the contained reference is pushed onto the stack and
    /// this method returns `true`.  If the closure returns `None` then the stack is unmodified and this
    /// method returns `false`.
    ///
    /// This method will panic if the stack contains only the root.  Use [Self::advance_from_root]
    #[inline]
    pub fn advance<F>(&mut self, step_f: F) -> bool
        where
        F: FnOnce(&mut NodeT) -> Option<&mut NodeT>,
    {
        match step_f(self.top_mut().expect("Cursor at root. Must call `advance_from_root` before `advance`")) {
            Some(new_node) => {
                let new_ptr = NonNull::from(new_node);
                if let Some(old_top) = self.top.replace(new_ptr) {
                    self.stack.push(old_top);
                }
                true
            },
            None => false
        }
    }
    /// Pops a reference from the stack, exposing the prior reference as the new [`top`](Self::top)
    ///
    /// If the last node entry has been removed, only the root will remain. This method will panic if
    /// it is called when the stack contains only the root
    #[inline]
    pub fn backtrack(&mut self) {
        match self.stack.pop() {
            Some(top_ptr) => {
                self.top = Some(top_ptr);
            },
            None => {
                if self.top.is_some() {
                    self.top = None;
                } else {
                    panic!("MutCursor must contain valid reference")
                }
            }
        }
    }
    /// Pops a reference from the stack, exposing prior reference as the new [`top`](Self::top),
    /// but, unlike [`backtrack`](Self::backtrack) this method will not pop the bottom NodeT reference,
    /// and will never panic!()
    ///
    /// This method will do nothing if it is called when [`depth`](Self::depth) is `<= 1`
    #[inline]
    pub fn try_backtrack_node(&mut self) {
        match self.stack.pop() {
            Some(top_ptr) => {
                self.top = Some(top_ptr);
            },
            None => {}
        }
    }
    /// Pops all references from the stack, exposing the root reference via [`root`](Self::root)
    ///
    /// This method does nothing if the stack is already at the root.
    #[inline]
    pub fn to_root(&mut self) {
        self.top = None;
        self.stack.clear();
    }
    /// Pops all references beyond the first from the stack, exposing the first reference
    /// created by [`advance_from_root`](Self::advance_from_root) as the [`top`](Self::top)
    ///
    /// This method does nothing if the stack is already at the root or the first node reference.
    #[inline]
    pub fn to_bottom(&mut self) {
        if self.stack.len() > 0 {
            self.stack.truncate(1);
            match self.stack.pop() {
                Some(top_ptr) => self.top = Some(top_ptr),
                None => debug_assert!(self.top.is_none())
            }
        }
    }
}


#[cfg(test)]
mod test {
    use std::*;
    use std::boxed::*;
    use std::vec::Vec;

    use crate::*;

    struct TreeNode {
        val: usize,
        next: Option<Box<TreeNode>>
    }
    impl TreeNode {
        fn new(count: usize) -> Self {
            if count > 0 {
                Self {val: count, next: Some(Box::new(Self::new(count-1)))}
            } else {
                Self {val: 0, next: None}
            }
        }
        fn traverse_to_box(&mut self) -> Option<&mut Box<Self>> {
            self.next.as_mut()
        }
        fn traverse(&mut self) -> Option<&mut Self> {
            self.traverse_to_box().map(|boxed| boxed as _)
        }
    }

    #[test]
    fn rooted_vec_basics() {
        let tree = TreeNode::new(10);
        let mut node_stack: MutCursorRootedVec::<TreeNode, TreeNode> = MutCursorRootedVec::new(tree);
        node_stack.advance_from_root(|root| root.traverse_to_box());

        while node_stack.advance(|node| {
            node.traverse()
        }) {}

        assert_eq!(node_stack.top().unwrap().val, 0);
        assert_eq!(node_stack.depth(), 10);

        node_stack.backtrack();
        assert_eq!(node_stack.top().unwrap().val, 1);
        assert_eq!(node_stack.depth(), 9);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().unwrap().val, 4);
        assert_eq!(node_stack.depth(), 6);

        while node_stack.advance(|node| {
            node.traverse()
        }) {}
        assert_eq!(node_stack.top().unwrap().val, 0);
        assert_eq!(node_stack.depth(), 10);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().unwrap().val, 6);
        assert_eq!(node_stack.depth(), 4);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().unwrap().val, 9);
        assert_eq!(node_stack.depth(), 1);

        node_stack.backtrack();
        assert!(node_stack.top().is_none());
        assert_eq!(node_stack.root().unwrap().val, 10);
        assert_eq!(node_stack.into_root().val, 10);
    }

    use std::{thread, thread::ScopedJoinHandle};
    #[test]
    fn rooted_vec_multi_thread_test() {

        let thread_cnt = 128;
        let mut data: Vec<TreeNode> = vec![];
        for _ in 0..thread_cnt {
            data.push(TreeNode::new(10));
        }

        thread::scope(|scope| {

            let mut threads: Vec<ScopedJoinHandle<()>> = Vec::with_capacity(thread_cnt);

            //Spawn all the threads
            for _ in 0..thread_cnt {
                let tree = data.pop().unwrap();
                let mut node_stack: MutCursorRootedVec::<TreeNode, TreeNode> = MutCursorRootedVec::new(tree);

                let thread = scope.spawn(move || {

                    node_stack.advance_from_root(|root| root.traverse_to_box());

                    while node_stack.advance(|node| {
                        node.traverse()
                    }) {}

                    assert_eq!(node_stack.top().unwrap().val, 0);
                    assert_eq!(node_stack.depth(), 10);

                    node_stack.backtrack();
                    assert_eq!(node_stack.top().unwrap().val, 1);
                    assert_eq!(node_stack.depth(), 9);

                    node_stack.backtrack();
                    node_stack.backtrack();
                    node_stack.backtrack();
                    assert_eq!(node_stack.top().unwrap().val, 4);
                    assert_eq!(node_stack.depth(), 6);

                    while node_stack.advance(|node| {
                        node.traverse()
                    }) {}
                    assert_eq!(node_stack.top().unwrap().val, 0);
                    assert_eq!(node_stack.depth(), 10);

                    node_stack.backtrack();
                    node_stack.backtrack();
                    node_stack.backtrack();
                    node_stack.backtrack();
                    node_stack.backtrack();
                    node_stack.backtrack();
                    assert_eq!(node_stack.top().unwrap().val, 6);
                    assert_eq!(node_stack.depth(), 4);

                    node_stack.backtrack();
                    node_stack.backtrack();
                    node_stack.backtrack();
                    assert_eq!(node_stack.top().unwrap().val, 9);
                    assert_eq!(node_stack.depth(), 1);

                    node_stack.backtrack();
                    assert!(node_stack.top().is_none());
                    assert_eq!(node_stack.root().unwrap().val, 10);
                    assert_eq!(node_stack.into_root().val, 10);
                });
                threads.push(thread);
            };

            //Wait for them to finish
            for thread in threads {
                thread.join().unwrap();
            }
        });
    }
}
