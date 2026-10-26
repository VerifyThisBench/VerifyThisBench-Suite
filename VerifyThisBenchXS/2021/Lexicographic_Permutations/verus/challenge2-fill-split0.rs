use vstd::prelude::*;
fn main() {}
verus! {

spec fn is_sorted(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
}



#[verifier::external_body]
fn sort(v: &mut Vec<i32>)
    ensures
        old(v)@.to_multiset() =~= v@.to_multiset(),
        is_sorted(v@),
        old(v)@.len() =~= v@.len(),
{
    v.sort();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
#[allow(unused)]
fn permut(a: &mut Vec<i32>) -> (result: Vec<Vec<i32>>)
    requires
        old(a)@.len() <= i32::MAX,
{
    if a.len() == 0 {
        Vec::new()
    } else {
        let mut result: Vec<Vec<i32>> = Vec::new();

        sort(a);
        result.push(a.clone());

        while !next(a).0
            invariant
                a@.len() <= i32::MAX,
        {
            result.push(a.clone());
        }

        result
    }
}

spec fn non_increasing(v: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] >= v[j]
}


fn next(a: &mut Vec<i32>) -> (result: (bool, Ghost<int>))
    requires
        old(a)@.len() <= i32::MAX,
    ensures
        !result.0 ==> a@ =~= old(a)@,
        a@.len() =~= old(a)@.len(),
        !result.0 ==> forall|i: int, j: int|
            0 <= i <= j < a@.len() - 1 && j == i + 1 ==> a[i] >= a[j],
        forall|i: int| 0 <= i < (result.1 as int) < a@.len() ==> old(a)@[i] == a@[i],
        result.0 ==> 0 <= (result.1 as int) < a@.len(),
        result.0 ==> a@[result.1 as int] > old(a)@[result.1 as int],
        result.0 ==> forall|k1: int, k2: int|
            (result.1 as int) < k1 <= k2 < a@.len() && k2 == k1 + 1 ==> old(a)@[k1] >= old(
                a,
            )@[k2],
{
    TODO
}

} // verus!
