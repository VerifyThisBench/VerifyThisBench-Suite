use vstd::prelude::*;
fn main() {}
verus! {

struct Tree {
    val: i32,
    left: Option<Box<Tree>>,
    right: Option<Box<Tree>>,
}

impl Tree {
    pub closed spec fn maximum(&self) -> int
        decreases self,
    {
        TODO
    }
}

fn max(a: i32, b: i32) -> (v: i32)
    ensures
        TODO
{
    if a >= b {
        a
    } else {
        b
    }
}

#[allow(unused)]
fn tree_max(t: &Tree) -> (max_value: i32)
    ensures
        TODO,
    decreases t,
{
    match (&t.left, &t.right) {
        (None, None) => t.val,
        (Some(l), None) => max(t.val, tree_max(l)),
        (None, Some(r)) => max(t.val, tree_max(r)),
        (Some(l), Some(r)) => max(t.val, max(tree_max(l), tree_max(r))),
    }
}

} // verus!
