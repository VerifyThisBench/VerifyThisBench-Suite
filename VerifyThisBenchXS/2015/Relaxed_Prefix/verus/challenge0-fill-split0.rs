use vstd::prelude::*;
fn main() {}
verus! {

spec fn eq_array(a1: Seq<i32>, ofs1: int, a2: Seq<i32>, ofs2: int, len: int) -> bool {
    0 <= len && 0 <= ofs1 && 0 <= ofs2 && ofs1 + len <= a1.len() && ofs2 + len <= a2.len()
        && forall|i: int| 0 <= i < len ==> #[trigger] a1[ofs1 + i] == a2[ofs2 + i]
}

spec fn spec_is_relaxed_prefix(pat: Seq<i32>, a: Seq<i32>) -> bool {
    let n = pat.len() as int;
    eq_array(pat, 0, a, 0, n) || exists|i: int|
        0 <= i && i < n && eq_array(pat, 0, a, 0, i) && eq_array(pat, i + 1, a, i, n - i - 1)
}

#[allow(unused)]
exec fn is_relaxed_prefix(pat: &Vec<i32>, a: &Vec<i32>) -> (res: bool)
    ensures
        res == spec_is_relaxed_prefix(pat@, a@),
{
    TODO
}

} // verus!
