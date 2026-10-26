use vstd::prelude::*;
fn main() {}
verus! {

spec fn valid_sequence(s: Seq<bool>, n: int) -> bool {
    &&& s.len() == n
    &&& forall|i: int|
        #![trigger s[i]]
        0 <= i < n ==> (s[i] ==> ((i >= 2 && s[i - 2] && s[i - 1]) || (i >= 1 && i < n - 1 && s[i
            - 1] && s[i + 1]) || (i < n - 2 && s[i + 1] && s[i + 2])))
}

spec fn unique_s(s: Seq<Seq<bool>>) -> bool {
    forall|i: int|
        0 <= i < s.len() ==> (forall|j: int|
            0 <= j < s.len() ==> ((#[trigger] s[i]) =~= (#[trigger] s[j]) ==> i == j))
}

spec fn has_false_in_prefix(s: Seq<bool>, k: int) -> bool {
    exists|y: int| 0 <= y < k + 1 && y < s.len() && s[y] == false
}

spec fn find_first_diff_index(left: Seq<bool>, right: Seq<bool>, i: int) -> int
    recommends
        0 <= i <= left.len() && left.len() == right.len(),
    decreases left.len() - i,
{
    TODO
}


#[verifier::external_body]
fn default_vec_with_length<T>(length: usize, default_value: T) -> (result: Vec<T>) where T: Copy
    ensures
        result@.len() == length,
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result[i] == default_value,
{
    vec![default_value; length]
}

spec fn v(s: Vec<Vec<bool>>) -> Seq<Seq<bool>> {
    s@.map_values(|ss: Vec<bool>| ss@)
}

spec fn vv(s: Vec<Vec<Vec<bool>>>) -> Seq<Seq<Seq<bool>>> {
    s@.map_values(|ss: Vec<Vec<bool>>| v(ss))
}

spec fn sum(count: Seq<u64>) -> int
    decreases count,
{
    if count.len() == 0 {
        0
    } else {
        count.last() + sum(count.drop_last())
    }
}

#[allow(unused)]
fn count_sequences(i: usize) -> u64
    requires
        4 <= i <= 81,
{
    TODO
}

} // verus!
