use vstd::prelude::*;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

spec fn occurrences(s: Seq<i32>, x: i32) -> nat
    decreases s,
{
    if s.len() == 0 {
        0
    } else {
        let summand: nat = if s.first() == x {
            1
        } else {
            0
        };
        summand + occurrences(s.drop_first(), x)
    }
}

spec fn occurrences_parent(s: Seq<i32>, x: i32) -> nat {
    occurrences(s, x)
}

fn main() {
    assert(min(10, 20) == 10);
    assert(min(-10, -20) == -20);
    assert(forall|i: int, j: int| min(i, j) <= i && min(i, j) <= j);
    assert(forall|i: int, j: int| min(i, j) == i || min(i, j) == j);
    assert(forall|i: int, j: int| min(i, j) == min(j, i));
}

} // verus!
