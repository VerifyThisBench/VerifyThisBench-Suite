use vstd::prelude::*;
fn main() {}
verus! {

#[allow(unused)]
pub fn max(a: &[i32]) -> (max_idx: usize)
    requires
        0 < a.len() <= usize::MAX,
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[max_idx as int] >= a[i],
{
    let mut x = 0usize;
    let mut y = a.len() - 1;

    while x != y
        invariant TODO,
        decreases y - x,
    {
        if a[x] <= a[y] {
            x += 1;
        } else {
            y -= 1;
        }
    }

    x
}

} // verus!
