use vstd::prelude::*;

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
        v >= a && v >= b,
        v == a || v == b,
{
    TODO
}

#[allow(unused)]
fn tree_max(t: &Tree) -> (max_value: i32)
    ensures
        max_value == t.maximum(),
    decreases t,
{
    TODO
}

} // verus!
