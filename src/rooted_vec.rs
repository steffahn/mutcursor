
use core::ptr::NonNull;
extern crate alloc;

/// Similar to [MutCursorVec](crate::MutCursorVec), but provides for a `RootT` type at the bottom of the
/// stack that is different from the `NodeT` types above it
///
/// **WARNING** If `RootT` is not a smart-pointer (e.g. when it owns the memory it references)
/// `MutCursorRootedVec` will definitely do UB! See <https://github.com/luketpeterson/mutcursor/issues/2>
///
/// Usage Note: This type owns (as opposed to borrows) the root object from which the rest of the
/// stack descends, therefore, it has no associated lifetime.  Often the RootT type is a pointer
/// itself, in which case it is the responsibility of the crate's user to maintain proper variance.
///
/// `MutCursorRootedVec` doesn't implement [Deref](core::ops::Deref), and accessors return [Option], so therefore it is
/// allowed to be empty, unlike some of the other types in this crate.
///
/// `MutCursorRootedVec` is not available if the `alloc` feature is disabled. (The feature is enabled by default.)
pub struct MutCursorRootedVec<RootT, NodeT: ?Sized> {
    top: Option<NonNull<NodeT>>,
    root: Option<RootT>,
    stack: alloc::vec::Vec<NonNull<NodeT>>,
}

unsafe impl<RootT, NodeT> Sync for MutCursorRootedVec<RootT, NodeT> where RootT: Sync, NodeT: Sync, NodeT: ?Sized {}
unsafe impl<RootT, NodeT> Send for MutCursorRootedVec<RootT, NodeT> where RootT: Send, NodeT: Send, NodeT: ?Sized {}

impl<RootT, NodeT: ?Sized> MutCursorRootedVec<RootT, NodeT> {
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root
    ///
    /// **Warning** This type has serious safety limits, so constructing it is unsafe.  `RootT` must
    /// be a smart-pointer type, e.g. [Arc](alloc::sync::Arc).
    #[inline]
    pub unsafe fn new(root: RootT) -> Self {
        Self {
            top: None,
            root: Some(root),
            stack: alloc::vec::Vec::new(),
        }
    }
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root, and an allocated
    /// buffer for `capacity` references
    #[inline]
    pub fn new_with_capacity(root: RootT, capacity: usize) -> Self {
        Self {
            top: None,
            root: Some(root),
            stack: alloc::vec::Vec::with_capacity(capacity),
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
        let mut root = None;
        core::mem::swap(&mut self.root, &mut root);
        self.top = None;
        self.stack.clear();
        Some(root.unwrap())
    }
    /// Replaces the root of the stack with the provided value
    ///
    /// Panics if the stack contains any references above the root
    #[inline]
    pub fn replace_root(&mut self, root: RootT) {
        if self.top.is_none() {
            self.root = Some(root);
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
    /// method will behave as if [advance_if_empty](Self::advance_if_empty) was called prior to [top_mut](Self::top_mut)
    ///
    /// Panics if the root has been taken via [Self::take_root]
    #[inline]
    pub fn top_or_advance_mut<F>(&mut self, step_f: F) -> &mut NodeT
        where F: FnOnce(&mut RootT) -> &mut NodeT
    {
        match &self.top {
            Some(mut node_ptr) => unsafe{ node_ptr.as_mut() },
            None => {
                let new_node = step_f(self.root.as_mut().unwrap());
                debug_assert_eq!(self.stack.len(), 0);
                let mut node_ptr = NonNull::from(new_node);
                self.top = Some(node_ptr);
                unsafe{ node_ptr.as_mut() }
            }
        }
    }
    /// Returns the mutable reference on the root of the stack, consuming the stack
    ///
    /// Panics if the root of the stack has already been taken via [Self::take_root]
    #[inline]
    pub fn into_root(self) -> RootT {
        self.root.unwrap()
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
    /// Panics if the root has been taken via [Self::take_root]
    #[inline]
    pub fn advance_if_empty<F>(&mut self, step_f: F)
        where F: FnOnce(&mut RootT) -> &mut NodeT
    {
        if self.top.is_none() {
            let new_node = step_f(self.root.as_mut().unwrap());
            debug_assert_eq!(self.stack.len(), 0);
            let node_ptr = NonNull::from(new_node);
            self.top = Some(node_ptr);
        }
    }
    /// Begins the traversal by stepping from the root to the first node, pushing the first node
    /// reference onto the stack.  Effectively resets the stack
    ///
    /// If the `step_f` closure returns `Some` the existing stack will be replaced.
    /// If the `step_f` closure returns `None`, the stack will not be modified.
    ///
    /// Panics if the root has been taken via [Self::take_root]
    #[inline]
    pub fn advance_from_root<F>(&mut self, step_f: F) -> bool
        where F: FnOnce(&mut RootT) -> Option<&mut NodeT>
    {
        match step_f(self.root.as_mut().unwrap()) {
            Some(new_node) => {
                self.stack.clear();
                self.top = Some(NonNull::from(new_node));
                true
            },
            None => false
        }
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
                let mut old_top = Some(NonNull::from(new_node));
                core::mem::swap(&mut old_top, &mut self.top);
                if let Some(old_top) = old_top {
                    self.stack.push(NonNull::from(old_top));
                }
                true
            },
            None => false
        }
    }
    /// Pops a reference from the stack, exposing the prior reference as the new [top](Self::top)
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
    /// Pops a reference from the stack, exposing prior reference as the new [top](Self::top),
    /// but, unlike [backtrack](Self::backtrack) this method will not pop the bottom NodeT reference,
    /// and will never panic!()
    ///
    /// This method will do nothing if it is called when [depth](Self::depth) is `<= 1`
    #[inline]
    pub fn try_backtrack_node(&mut self) {
        match self.stack.pop() {
            Some(top_ptr) => {
                self.top = Some(top_ptr);
            },
            None => {}
        }
    }
    /// Pops all references from the stack, exposing the root reference via [root](Self::root)
    ///
    /// This method does nothing if the stack is already at the root.
    #[inline]
    pub fn to_root(&mut self) {
        self.stack.clear();
        self.top = None;
    }
    /// Pops all references beyond the first from the stack, exposing the first reference
    /// created by [advance_from_root](Self::advance_from_root) as the [top](Self::top)
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
    extern crate std;
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
        fn traverse(&mut self) -> Option<&mut Self> {
            self.next.as_mut().map(|boxed| &mut **boxed)
        }
    }

    #[test]
    fn rooted_vec_basics() {
        let tree = TreeNode::new(10);
        let mut node_stack: MutCursorRootedVec::<TreeNode, TreeNode> = unsafe{ MutCursorRootedVec::new(tree) };
        node_stack.advance_from_root(|root| root.traverse());

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
                let mut node_stack: MutCursorRootedVec::<TreeNode, TreeNode> = unsafe{ MutCursorRootedVec::new(tree) };

                let thread = scope.spawn(move || {

                    node_stack.advance_from_root(|root| root.traverse());

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
