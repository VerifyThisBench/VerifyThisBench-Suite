use vstd::prelude::*;
fn main() {}
verus! {

spec fn lcp_subarray(a: Seq<i32>, x: int, y: int) -> nat
    decreases a.len() - x, a.len() - y,
{
    TODO
}

proof fn lemma_lcp_definition(arr: Seq<i32>, x: int, y: int, l: int)
    requires
        TODO,
    ensures
        TODO,
    decreases l,
{
    if l == 0 {
    } else {
        assert(arr[x + 0] == arr[y + 0]);

        assert forall|j: int|
            #![trigger arr[x + 1 + j], arr[y + 1 + j]]
            (0 <= j < l - 1) implies arr[x + 1 + j] == arr[y + 1 + j] by {
            if 0 <= j < l - 1 {
                let j_pp_trigger = j + 1;
                assert(arr[x + j_pp_trigger] == arr[y + j_pp_trigger]);
            } 
        };

        // I.H.
        lemma_lcp_definition(arr, x + 1, y + 1, l - 1);
    }
}

// Main challenge 1
#[allow(unused)]
fn lcp(arr: &Vec<i32>, x: usize, y: usize) -> (result: u64)
    requires
        TODO,
    ensures
        TODO,
{
    let mut l: usize = 0;
    while (x + l < arr.len() && y + l < arr.len() && arr[x + l] == arr[y + l])
        invariant
            x + l <= arr.len(),
            y + l <= arr.len(),
            forall|i: nat| #![trigger arr[x + i], arr[y + i]] i < l ==> arr@[x + i] == arr@[y + i],
        decreases arr.len() - l,
    {
        l += 1;
    };

    assert(l == lcp_subarray(arr@, x as int, y as int)) by {
        lemma_lcp_definition(arr@, x as int, y as int, l as int);
    };

    l as u64
}

} // verus!
