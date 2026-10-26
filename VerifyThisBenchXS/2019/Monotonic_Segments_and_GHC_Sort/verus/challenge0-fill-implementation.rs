use vstd::prelude::*;
fn main() {}
verus! {

spec fn ordered(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] <= s[k]
}

spec fn increasing(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] < s[k]
}

spec fn decreasing(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] >= s[k]
}

spec fn monotonic(s: Seq<i32>) -> bool {
    increasing(s) || decreasing(s)
}

spec fn monotonic_cuts(s: Seq<i32>, c: Seq<usize>) -> bool {
    let c_as_seq_i32: Seq<i32> = c.map_values(|element: usize| element as i32);
    increasing(c_as_seq_i32) && c.len() > 0 && (forall|k: int|
        0 <= k < c.len() ==> 0 <= #[trigger] c[k] <= s.len()) && (c[0] == 0 && c[c.len() - 1]
        == s.len()) && (forall|k: int|
        0 < k < c.len() ==> monotonic(s.subrange(c[k - 1] as int, #[trigger] c[k] as int)))
}

spec fn maximal_cuts(s: Seq<i32>, c: Seq<usize>) -> bool {
    monotonic_cuts(s, c) && (forall|k: int|
        0 < k < c.len() - 1 ==> !monotonic(s.subrange(#[trigger] c[k - 1] as int, c[k] + 1)))
}


// Challenge 1
#[allow(unused)]
fn monotonic_cutpoints(a: &Vec<i32>) -> (c: Vec<usize>)
    requires
        a@.len() < i32::MAX - 1,
    ensures
        monotonic_cuts(a@, c@),
        maximal_cuts(a@, c@),
{
   TODO
}

} // verus!
