#![doc = include_str!("../README.md")]

#![no_std]

use core::mem::MaybeUninit;
use core::marker::PhantomData;

/// Stores a stack of `&mut` references, only allowing access to the top element on the stack
///
/// The `MutCursor` stores `N` `&mut T` references, but only allows access to the [top](Self::top)
pub struct MutCursor<'a, T: ?Sized, const N: usize> {
    cnt: usize, //The last item cannot be removed, so cnt==0 means there is 1 item
    top: usize,
    stack: [MaybeUninit<*mut T>; N],
    phantom: PhantomData<&'a T>,
}

impl<'a, T: ?Sized, const N: usize> MutCursor<'a, T, N> {
    /// Returns a new `MutCursor` with a reference to the specified root
    #[inline]
    pub fn new(root: &'a mut T) -> Self {
        debug_assert!(N > 0);
        let mut stack = Self {
            cnt: 0,
            top: 0,
            stack: [MaybeUninit::uninit(); N],
            phantom: PhantomData::default(),
        };
        unsafe{ *stack.stack.get_unchecked_mut(0) = MaybeUninit::new(root); }
        stack
    }
    /// Returns a const reference from the mutable reference on the top of the stack
    #[inline]
    pub fn top(&self) -> &T {
        unsafe{ &**self.stack.get_unchecked(self.top).as_ptr() }
    }
    /// Returns the mutable reference on the top of the stack 
    #[inline]
    pub fn top_mut(&mut self) -> &mut T {
        unsafe{ self.top_mut_internal() }
    }
    /// Returns the mutable reference on the top of the stack, consuming the stack
    #[inline]
    pub fn into_mut(mut self) -> &'a mut T {
        unsafe{ self.top_mut_internal() }
    }
    /// Returns the number of excess references stored in the stack, which corresponds to the number of
    /// times [backtrack](Self::backtrack) may be called
    #[inline]
    pub fn depth(&self) -> usize {
        self.cnt
    }
    /// Returns the number of references the stack is capable of holding
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }
    /// Steps deeper into the traversal, pushing a new reference onto the top of the stack
    ///
    /// If the `step_f` closure returns `Some()`, the contained reference is pushed onto the stack and
    /// this method returns `true`.  If the closure returns `None` then the stack is unmodified and this
    /// method returns `false`.
    ///
    /// If the number of references in the stack exceeds the capacity, the reference at the bottom of the
    /// stack will be lost.
    #[inline]
    pub fn advance<F>(&mut self, step_f: F) -> bool
        where F: FnOnce(&'a mut T) -> Option<&'a mut T>
    {
        match step_f(unsafe{ self.top_mut_internal() }) {
            Some(new_node) => {
                let node_ptr = new_node as *mut T;
                unsafe{ self.push(node_ptr); }
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
        if self.cnt < 1 {
            panic!("MutCursor must contain valid reference")
        }
        if self.top < 1 {
            self.top = N-1;
        } else {
            self.top -= 1;
        }
        self.cnt -= 1;
    }
    /// Private
    #[inline]
    unsafe fn top_mut_internal(&mut self) -> &'a mut T {
        unsafe{ &mut **self.stack[self.top].as_mut_ptr() }
    }
    /// Private
    #[inline]
    unsafe fn push(&mut self, t: *mut T) {
        if self.top + 1 < N {
            self.top = self.top + 1;
        } else {
            self.top = 0;
        }
        *self.stack.get_unchecked_mut(self.top) = MaybeUninit::new(t);
        if self.cnt < N-1 {
            self.cnt += 1;
        }
    }
}

impl<'a, T: ?Sized, const N: usize> core::ops::Deref for MutCursor<'a, T, N> {
    type Target = T;
    fn deref(&self) -> &T {
        self.top()
    }
}

impl<'a, T: ?Sized, const N: usize> core::ops::DerefMut for MutCursor<'a, T, N> {
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
    fn basics() {
        let mut tree = TreeNode::new(10);
        let mut node_stack = MutCursor::<TreeNode, 7>::new(&mut tree);

        while node_stack.advance(|node| {
            node.traverse()
        }) {}

        assert_eq!(node_stack.top().val, 0);
        assert_eq!(node_stack.depth(), 6);

        node_stack.backtrack();
        assert_eq!(node_stack.top().val, 1);
        assert_eq!(node_stack.depth(), 5);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().val, 4);
        assert_eq!(node_stack.depth(), 2);

        while node_stack.advance(|node| {
            node.traverse()
        }) {}
        assert_eq!(node_stack.top().val, 0);
        assert_eq!(node_stack.depth(), 6);

        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        node_stack.backtrack();
        assert_eq!(node_stack.top().val, 6);
        assert_eq!(node_stack.depth(), 0);

        assert_eq!(node_stack.into_mut().val, 6);
    }
}
