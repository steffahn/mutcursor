
# mutcursor

This crate provides a type to safely store mutable references to parent nodes, for backtracking during traversal of tree & graph structures.

## Usage
```rust
use mutcursor::MutCursor;

let mut tree = TreeNode::new(5);
let mut node_stack = MutCursor::<TreeNode, 2>::new(&mut tree);

// Traverse to the last node
while node_stack.advance(|node| {
    node.traverse()
}) {}

assert_eq!(node_stack.top().val, 0);
assert_eq!(node_stack.depth(), 1);

node_stack.backtrack();
assert_eq!(node_stack.top().val, 1);
assert_eq!(node_stack.depth(), 0);

/// A simple stand-in for a recursive graph structure
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
```

## Alternative(s)

This crate basically does the same thing as [generic-cursors](https://crates.io/crates/generic-cursors). However, this crate opts for a fixed-size stack while `generic-cursors` uses a `Vec`.  That means this crate has lower overhead but `generic-cursors` permits arbitrarily-deep backtracking.

## Safety Thesis

Each `&mut` reference stored by a [MutCursor] mutably borrows the reference beneath it in the stack.  The stack root takes a mutable (and therefore exclusive) borrow of the node itself.  Therefore the stack's [top](MutCursor::top) is an exclusive borrow.

You can imagine unrolling tree traversal into something like the code below, but this isn't amenable to looping.  In essence each `level` variable is preserved, but inaccessible because the level above is mutably borrowing it.  The [MutCursor] object contains all the `level` variables but only provides access to the [top](MutCursor::top)

```rust ignore
let level_1 = &mut root;
{
    let level_2 = level_1.traverse().unwrap();
    {
        match level_2.traverse() {
            Some(level_3) => {} // Do something with level_3
            None => {} // Fall back to work level_2 or level_1
        }
    }
}
```