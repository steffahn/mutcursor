
extern crate alloc;

/// Similar to [MutCursorVec](crate::MutCursorVec), but provides for a `RootT` type at the bottom of the
/// stack that is different from the `NodeT` types above it
///
/// `MutCursorRootedVec` doesn't implement [Deref](core::ops::Deref), and accessors return [Option], so therefore it is
/// allowed to be empty, unlike some of the other types in this crate.
///
/// `MutCursorRootedVec` is not available if the `no_std` feature is set
pub struct MutCursorRootedVec<'root, RootT: ?Sized + 'root, NodeT: ?Sized + 'root> {
    top: Option<&'root mut NodeT>,
    root: Option<*mut RootT>,
    stack: alloc::vec::Vec<*mut NodeT>,
}

unsafe impl<'a, RootT, NodeT> Sync for MutCursorRootedVec<'a, RootT, NodeT> where &'a mut RootT: Sync + Send, RootT: ?Sized, &'a mut NodeT: Sync + Send, NodeT: ?Sized {}
unsafe impl<'a, RootT, NodeT> Send for MutCursorRootedVec<'a, RootT, NodeT> where &'a mut RootT: Sync + Send, RootT: ?Sized, &'a mut NodeT: Sync + Send, NodeT: ?Sized {}

impl<'root, RootT: ?Sized + 'root, NodeT: ?Sized + 'root> MutCursorRootedVec<'root, RootT, NodeT> {
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root
    #[inline]
    pub fn new(root: &'root mut RootT) -> Self {
        Self {
            top: None,
            root: Some(root),
            stack: alloc::vec::Vec::new(),
        }
    }
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root, and an allocated
    /// buffer for `capacity` references
    #[inline]
    pub fn new_with_capacity(root: &'root mut RootT, capacity: usize) -> Self {
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
            Some(unsafe{ &**self.root.as_ref().unwrap() })
        } else {
            None
        }
    }
    /// Returns a const reference from the mutable reference on the top of the stack, or `None` if the
    /// stack contains only the root
    #[inline]
    pub fn top(&self) -> Option<&NodeT> {
        self.top.as_deref()
    }
    /// Returns the mutable reference on the root of the stack, or `None` if the stack contains additional
    /// references obscuring the root
    #[inline]
    pub fn root_mut(&self) -> Option<&mut RootT> {
        if self.top.is_none() {
            match self.root {
                Some(root) => Some(unsafe{ &mut *root }),
                None => None
            }
        } else {
            None
        }
    }
    /// Removes and returns the mutable reference on the root of the stack, or `None` if the
    /// root has already been taken
    ///
    /// This method effectively dumps the entire stack contents.
    #[inline]
    pub fn take_root(&mut self) -> Option<&'root mut RootT> {
        if self.root.is_some() {
            let mut root = None;
            core::mem::swap(&mut self.root, &mut root);
            self.top = None;
            self.stack.clear();
            Some(unsafe{ &mut *root.unwrap() })
        } else {
            None
        }
    }
    /// Replaces the root of the stack with the provided value
    ///
    /// Panics if the stack contains any references above the root
    #[inline]
    pub fn replace_root(&mut self, root: &'root mut RootT) {
        if self.top.is_none() {
            self.root = Some(root);
        } else {
            panic!("Illegal operation, unable to replace borrowed root");
        }
    }
    /// Returns the mutable reference on the top of the stack, or `None` if the stack contains only the root
    #[inline]
    pub fn top_mut(&mut self) -> Option<&mut NodeT> {
        self.top.as_deref_mut()
    }
    /// Returns the mutable reference on the root of the stack, consuming the stack
    ///
    /// Panics if the root of the stack has already been taken via [Self::take_root]
    #[inline]
    pub fn into_root(self) -> &'root mut RootT {
        unsafe{ &mut *self.root.unwrap() }
    }
    /// Returns the mutable reference on the top of the stack, consuming the stack, or `None` if the stack
    /// contains only the root
    #[inline]
    pub fn into_mut(self) -> Option<&'root mut NodeT> {
        self.top
    }
    /// Consumes the stack and returns a mutable reference to an object with the `'root` lifetime,
    /// if a closure returns `Ok`, otherwise returns the stack and a custom error value
    ///
    /// This method will panic if the stack contains only the root
    ///
    /// NOTE: Usage is othewise identical to [MutCursor::try_map_into_mut](crate::MutCursor::try_map_into_mut)
    #[inline]
    pub fn try_map_into_mut<U, E, F>(mut self, f: F) -> Result<&'root mut U, (Self, E)>
        where for<'r> F: FnOnce(&'r mut NodeT) -> Result<&'r mut U, E>
    {
        let top_ref = unsafe{ self.top_mut_internal().unwrap() };
        match f(top_ref) {
            Ok(r) => Ok(r),
            Err(e) => Err((self, e))
        }
    }
    /// Returns the number of node references stored in the stack, which corresponds to the number of
    /// times [backtrack](Self::backtrack) may be called before the stack is empty
    #[inline]
    pub fn depth(&self) -> usize {
        self.stack.len() + 1
    }
    /// Returns the number of node references the stack is capable of holding without reallocation
    #[inline]
    pub fn capacity(&self) -> usize {
        self.stack.capacity() + 1
    }
    /// Begins the traversal by stepping from the root to the first node, pushing the first node reference
    /// onto the stack
    ///
    /// If the `step_f` closure returns `None`, the stack will not be modified
    ///
    /// Panics if the root has been taken via [Self::take_root]
    #[inline]
    pub fn advance_from_root<F>(&mut self, step_f: F) -> bool
        where F: FnOnce(&'root mut RootT) -> Option<&'root mut NodeT>
    {
        match step_f(unsafe{ &mut **self.root.as_ref().unwrap() }) {
            Some(new_node) => {
                unsafe{ self.push(new_node); }
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
        where F: FnOnce(&'root mut NodeT) -> Option<&'root mut NodeT>
    {
        match step_f(unsafe{ self.top_mut_internal().expect("Cursor at root. Must call `advance_from_root` before `advance`") }) {
            Some(new_node) => {
                unsafe{ self.push(new_node); }
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
                self.top = Some( unsafe{ &mut *top_ptr } );
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
    /// Pops all references from the stack, exposing the root reference as the [top](Self::top)
    ///
    /// This method does nothing if the stack is already at the root
    #[inline]
    pub fn to_root(&mut self) {
        self.stack.clear();
        self.top = None;
    }
    /// Private
    #[inline]
    unsafe fn top_mut_internal(&mut self) -> Option<&'root mut NodeT> {
        self.top.as_deref_mut().map(|top| &mut *(top as *mut NodeT))
    }
    /// Private
    #[inline]
    unsafe fn push(&mut self, t_ref: &'root mut NodeT) {
        let mut old_top = Some(t_ref);
        core::mem::swap(&mut old_top, &mut self.top);
        if let Some(old_top) = old_top {
            self.stack.push(old_top as *mut NodeT);
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
        let mut tree = TreeNode::new(10);
        let mut node_stack = MutCursorRootedVec::<TreeNode, TreeNode>::new(&mut tree);
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
        let mut data_refs: Vec<&mut TreeNode> = data.iter_mut().collect();

        thread::scope(|scope| {

            let mut threads: Vec<ScopedJoinHandle<()>> = Vec::with_capacity(thread_cnt);

            //Spawn all the threads
            for _ in 0..thread_cnt {
                let tree = data_refs.pop().unwrap();
                let mut node_stack = MutCursorRootedVec::<TreeNode, TreeNode>::new(tree);

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
