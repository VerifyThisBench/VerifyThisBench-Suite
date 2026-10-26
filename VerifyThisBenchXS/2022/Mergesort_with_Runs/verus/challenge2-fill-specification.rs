use vstd::prelude::*;
fn main() {}
verus! {


struct Sr {
    runs: Vec<usize>,
    data: Vec<u32>,
}

spec fn correct_run_properties(runs: Seq<usize>, data: Seq<u32>) -> bool {
    TODO
}


#[allow(unused)]
#[verifier::loop_isolation(false)]
fn merge(r_1: &Sr, r_2: &Sr) -> (res: Sr)
    requires
        TODO
    ensures
        TODO
    let mut runs: Vec<usize> = Vec::new();
    let mut data: Vec<u32> = Vec::new();

    
    let mut di_1 = 0usize;
    let mut di_2 = 0usize;
    
    let mut ri_1 = 0usize;
    let mut ri_2 = 0usize;

    while ri_1 < r_1.runs.len() || ri_2 < r_2.runs.len()
        
        
        
        
        invariant
            
            
            0 <= ri_1 <= r_1.runs@.len(),
            0 <= ri_2 <= r_2.runs@.len(),
            0 <= di_1 <= r_1.data@.len(),
            0 <= di_2 <= r_2.data@.len(),

            
            correct_run_properties(runs@, data@),
            
            
            
            
            
            
            
            
            
            ri_1 < r_1.runs@.len() ==> di_1 < r_1.runs@[ri_1 as int],
            ri_2 < r_2.runs@.len() ==> di_2 < r_2.runs@[ri_2 as int],
            
            
            
            
            data@.len() == di_1 + di_2,
        decreases (r_1.runs.len() - ri_1) + (r_2.runs.len() - ri_2),
    {
        let t_1 = ri_1 < r_1.runs.len() && (ri_2 == r_2.runs.len() || r_1.data[di_1] <= r_2.data[di_2]);
    
        let t_2 = ri_2 < r_2.runs.len() && (ri_1 == r_1.runs.len() || r_2.data[di_2] <= r_1.data[di_1]);

        if t_1 {
            while di_1 < r_1.runs[ri_1]
                invariant
                    
                    0 <= di_1 <= r_1.runs@[ri_1 as int],
                    
                    data@.len() == di_1 + di_2,
                decreases r_1.runs[ri_1 as int] - di_1,
            {
                data.push(r_1.data[di_1]);
                di_1 += 1;
            }
            ri_1 += 1;
        }
    
        if t_2 {
            while di_2 < r_2.runs[ri_2]
                invariant
                    
                    0 <= di_2 <= r_2.runs@[ri_2 as int],
                    
                    data@.len() == di_1 + di_2,
                decreases r_2.runs[ri_2 as int] - di_2,
            {
                data.push(r_2.data[di_2]);
                di_2 += 1;
            }
            ri_2 += 1;
        }

        runs.push(data.len());
    }

    Sr { runs, data }
}


#[verifier::loop_isolation(false)]
#[allow(unused)]
fn msort(a: &Vec<u32>, l: usize, h: usize) -> (result: Sr)
    requires
        TODO
    ensures
        TODO
    decreases
        h - l
{
    if l == h {
        Sr { runs: Vec::new(), data: Vec::new() }
    } else if h - l == 1 {
        Sr { runs: vec![1], data: vec![a[l]] }
    } else {
        let m = l + (h - l) / 2;

        let res_1 = msort(a, l, m);
        let res_2 = msort(a, m, h);

        merge(&res_1, &res_2)
    }
}

} 
