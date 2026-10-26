use vstd::prelude::*;
fn main() {}
verus! {









struct Sr {
    runs: Vec<usize>,
    data: Vec<u32>,
}






spec fn correct_run_properties(runs: Seq<usize>, data: Seq<u32>) -> bool {
    &&& runs.len() <= data.len()
    &&& forall|i: int| 0 <= i < runs.len() ==> runs[i] > 0
    &&& forall|i: int| 0 <= i < runs.len() ==> runs[i] <= data.len()
    &&& forall|i: int, j: int| 0 <= i < j < runs.len() ==> runs[i] < runs[j]

}


#[allow(unused)]
#[verifier::loop_isolation(false)]
fn merge(r_1: &Sr, r_2: &Sr) -> (res: Sr)
    requires
        correct_run_properties(r_1.runs@, r_1.data@),
        correct_run_properties(
            r_2.runs@,
            r_2.data@,
        ),
    ensures
        correct_run_properties(res.runs@, res.data@),
{
    TODO
}

#[verifier::loop_isolation(false)]
#[allow(unused)]
fn msort(a: &Vec<u32>, l: usize, h: usize) -> (result: Sr)
    requires
        l <= h <= a.len(),
    ensures
        correct_run_properties(result.runs@, result.data@),
    decreases
        h - l
{
    TODO
}

} 
