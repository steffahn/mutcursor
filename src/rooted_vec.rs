
extern crate alloc;

/// Similar to [MutCursorVec](crate::MutCursorVec), but provides for a `RootT` type at the bottom of the
/// stack that is different from the `NodeT` types above it
///
/// `MutCursorRootedVec` is not available if the `no_std` feature is set
pub struct MutCursorRootedVec<'root, RootT: ?Sized + 'root, NodeT: ?Sized + 'root> {
    top: Option<&'root mut NodeT>,
    root: *mut RootT,
    stack: alloc::vec::Vec<*mut NodeT>,
}

impl<'root, RootT: ?Sized + 'root, NodeT: ?Sized + 'root> MutCursorRootedVec<'root, RootT, NodeT> {
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root
    #[inline]
    pub fn new(root: &'root mut RootT) -> Self {
        Self {
            top: None,
            root,
            stack: alloc::vec::Vec::new(),
        }
    }
    /// Returns a new `MutCursorRootedVec` with a reference to the specified root, and an allocated
    /// buffer for `capacity` references
    #[inline]
    pub fn new_with_capacity(root: &'root mut RootT, capacity: usize) -> Self {
        Self {
            top: None,
            root,
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
            Some(unsafe{ &*self.root })
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
    /// nodes obscuring the root
    #[inline]
    pub fn root_mut(&self) -> Option<&mut RootT> {
        if self.top.is_none() {
            Some(unsafe{ &mut *self.root })
        } else {
            None
        }
    }
    /// Returns the mutable reference on the top of the stack, or `None` if the stack contains only the root
    #[inline]
    pub fn top_mut(&mut self) -> Option<&mut NodeT> {
        self.top.as_deref_mut()
    }
    /// Returns the mutable reference on the root of the stack, consuming the stack
    #[inline]
    pub fn into_root(self) -> &'root mut RootT {
        unsafe{ &mut *self.root }
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
    /// times [backtrack](Self::backtrack) may be called
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
    #[inline]
    pub fn advance_from_root<F>(&mut self, step_f: F) -> bool
        where F: FnOnce(&'root mut RootT) -> Option<&'root mut NodeT>
    {
        match step_f(unsafe{ &mut *self.root }) {
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
        match step_f(unsafe{ self.top_mut_internal().unwrap() }) {
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
