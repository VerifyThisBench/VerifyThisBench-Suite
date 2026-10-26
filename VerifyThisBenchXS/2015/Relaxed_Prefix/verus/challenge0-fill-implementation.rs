use vstd::prelude::*;
fn main() {}
verus! {

spec fn eq_array(a1: Seq<i32>, ofs1: int, a2: Seq<i32>, ofs2: int, len: int) -> bool {
   TODO
}

spec fn spec_is_relaxed_prefix(pat: Seq<i32>, a: Seq<i32>) -> bool {
   TODO
}

#[allow(unused)]
exec fn is_relaxed_prefix(pat: &Vec<i32>, a: &Vec<i32>) -> (res: bool)
    ensures
        res == spec_is_relaxed_prefix(pat@, a@),
{
   TODO
}

} // verus!
