use vstd::prelude::*;
fn main() {}
verus! {

spec fn lcp_subarray(a: Seq<i32>, x: int, y: int) -> nat
    decreases a.len() - x, a.len() - y,
{
    TODO
}

// Main challenge 1
#[allow(unused)]
fn lcp(arr: &Vec<i32>, x: usize, y: usize) -> (result: u64)
    requires
        arr.len() < usize::MAX,
        x < arr.len() && y < arr.len(),
    ensures
        result == lcp_subarray(arr@, x as int, y as int),
{
    TODO
}

} // verus!
