
use core::ptr::NonNull;
use core::marker::PhantomData;
extern crate alloc;

/// Similar to [MutCursor](crate::MutCursor), but allows for a dynamically growing stack
///
/// `MutCursorVec` is not available if the `no_std` feature is set
pub struct MutCursorVec<'root, T: ?Sized + 'root> {
    top: NonNull<T>,
    stack: alloc::vec::Vec<NonNull<T>>,
    phantom: PhantomData<&'root mut T>, //Variance
}

unsafe impl<'a, T> Sync for MutCursorVec<'a, T> where T: Sync, T: ?Sized {}
unsafe impl<'a, T> Send for MutCursorVec<'a, T> where T: Send, T: ?Sized {}

impl<'root, T: ?Sized + 'root> MutCursorVec<'root, T> {
    /// Returns a new `MutCursorVec` with a reference to the specified root
    #[inline]
    pub fn new(root: &'root mut T) -> Self {
        Self {
            top: root.into(),
            stack: alloc::vec::Vec::new(),
            phantom: PhantomData::default(),
        }
    }
    /// Returns a new `MutCursorVec` with a reference to the specified root, and an allocated buffer
    /// for `capacity` references
    #[inline]
    pub fn new_with_capacity(root: &'root mut T, capacity: usize) -> Self {
        Self {
            top: root.into(),
            stack: alloc::vec::Vec::with_capacity(capacity),
            phantom: PhantomData::default(),
        }
    }
    /// Returns a const reference from the mutable reference on the top of the stack
    #[inline]
    pub fn top(&self) -> &T {
        unsafe{ self.top.as_ref() }
    }
    /// Returns the mutable reference on the top of the stack 
    #[inline]
    pub fn top_mut(&mut self) -> &mut T {
        unsafe{ self.top.as_mut() }
    }
    /// Returns the mutable reference on the top of the stack, consuming the stack
    #[inline]
    pub fn into_mut(mut self) -> &'root mut T {
        unsafe{ self.top.as_mut() }
    }
    /// Consumes the stack and returns a mutable reference to an object with the `'root` lifetime,
    /// if a closure returns `Ok`, otherwise returns the stack and a custom error value
    ///
    /// NOTE: Usage is identical to [MutCursor::try_map_into_mut](crate::MutCursor::try_map_into_mut)
    #[inline]
    pub fn try_map_into_mut<U, E, F>(mut self, f: F) -> Result<&'root mut U, (Self, E)>
        where for<'r> F: FnOnce(&'r mut T) -> Result<&'r mut U, E>
    {
        let top_ref = unsafe{ self.top_mut_internal() };
        match f(top_ref) {
            Ok(r) => Ok(r),
            Err(e) => Err((self, e))
        }
    }
    /// Returns the number of excess references stored in the stack, which corresponds to the number of
    /// times [backtrack](Self::backtrack) may be called
    #[inline]
    pub fn depth(&self) -> usize {
        self.stack.len()
    }
    /// Returns the number of references the stack is capable of holding without reallocation
    #[inline]
    pub fn capacity(&self) -> usize {
        self.stack.capacity() + 1
    }
    /// Steps deeper into the traversal, pushing a new reference onto the top of the stack
    ///
    /// If the `step_f` closure returns `Some()`, the contained reference is pushed onto the stack and
    /// this method returns `true`.  If the closure returns `None` then the stack is unmodified and this
    /// method returns `false`.
    #[inline]
    pub fn advance<F>(&mut self, step_f: F) -> bool
        where F: FnOnce(&mut T) -> Option<&mut T>
    {
        match step_f(unsafe{ self.top_mut_internal() }) {
            Some(new_node) => {
                unsafe{ self.push(new_node); }
                true
            },
            None => false
        }
    }
    /// Pops a reference from the stack, exposing the prior reference as the new [top](Self::top)
    ///
    /// This method will panic if the stack contains only 1 entry
    #[inline]
    pub fn backtrack(&mut self) {
        match self.stack.pop() {
            Some(top_ptr) => {
                self.top = top_ptr;
            },
            None => panic!("MutCursor must contain valid reference")
        }
    }
    /// Pops all references from the stack, exposing the root reference as the [top](Self::top)
    ///
    /// This method does nothing if the stack is already at the root
    #[inline]
    pub fn to_root(&mut self) {
        if self.stack.len() > 0 {
            self.stack.truncate(1);
            self.top = self.stack.pop().unwrap();
        }
    }
    /// Private
    #[inline]
    unsafe fn top_mut_internal(&mut self) -> &'root mut T {
        unsafe{ self.top.as_mut() }
    }
    /// Private
    #[inline]
    unsafe fn push(&mut self, t_ref: &'root mut T) {
        let mut top_ptr: NonNull<T> = t_ref.into();
        core::mem::swap(&mut top_ptr, &mut self.top);
        self.stack.push(top_ptr);
    }
}

impl<'root, T: ?Sized> core::ops::Deref for MutCursorVec<'root, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.top()
    }
}

impl<'root, T: ?Sized> core::ops::DerefMut for MutCursorVec<'root, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.top_mut()
    }
}

#[cfg(test)]
mod test {
    extern crate std;
    use std::*;
    use std::boxed::*;

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
    fn basics_vec() {
        let mut tree = TreeNode::new(10);
        let mut node_stack = MutCursorVec::<TreeNode>::new(&mut tree);

        while node_stack.advance(|node| {
            node.traverse()
        }) {}

        assert_eq!(node_stack.top().val, 0);
        assert_eq!(node_stack.depth(), 10);

        node_stack.backtrack();
        assert_eq!(node_stack.top().val, 1);
        assert_eq!(node_stack.depth(), 9);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().val, 4);
        assert_eq!(node_stack.depth(), 6);

        while node_stack.advance(|node| {
            node.traverse()
        }) {}
        assert_eq!(node_stack.top().val, 0);
        assert_eq!(node_stack.depth(), 10);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().val, 6);
        assert_eq!(node_stack.depth(), 4);

        assert_eq!(node_stack.into_mut().val, 6);
    }

    /// See https://github.com/luketpeterson/mutcursor/issues/1#issuecomment-2549242493
    #[test]
    fn miri_tagging_issue() {
        let x = &mut 0;
        let mut c = MutCursorVec::new(x);
        c.advance(|x| Some(x));
        c.backtrack();
        println!("{}", c.top());
    }
}
