use vstd::prelude::*;
fn main() {}
verus! {


/////////// SPEC FUNCTIONS

spec fn even(x: int) -> bool {
    TODO
}

spec fn occ(x: int, row: Seq<i32>, start: int, end: int) -> nat
    decreases end - start,
{
    TODO
}

spec fn mocc(x: int, m: Seq<Vec<i32>>, row: int, column: int) -> int
    decreases row,
{
    TODO
}

spec fn lt(i: int, j: int, k: int, l: int) -> bool {
    TODO
}

spec fn snake_order(m: Seq<Vec<i32>>, rows: int, columns: int) -> bool {
    TODO
}

spec fn inversions(m: Seq<Vec<i32>>, rows: int, columns: int) -> int
    decreases rows, columns, rows, columns,
{
    TODO
}

spec fn sum_i(m: Seq<Vec<i32>>, rows: int, columns: int, i: int) -> int
    decreases rows - i,
{
    TODO
}

spec fn sum_j(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int) -> int
    decreases columns - j,
{
    TODO
}

spec fn sum_k(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int) -> int
    decreases rows - k,
{
    TODO
}

spec fn numof_l(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int, l: int) -> int
    decreases columns - l,
{
    TODO
}


spec fn sorted_row(m: Seq<Vec<i32>>, rows: int, columns: int, row: int, ascending: bool) -> bool {
    TODO
}

spec fn sorted_column(m: Seq<Vec<i32>>, rows: int, columns: int, column: int) -> bool {
    TODO
}


proof fn inv_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int)
    requires
        TODO,
    ensures
        TODO,
{
    sum_i_nonneg(m, rows, columns, 0);
}

proof fn numof_l_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int, l: int)
    requires
        TODO,
    ensures
        TODO,
    decreases columns - l,
{
    if l >= columns {
    } else {
        numof_l_nonneg(m, rows, columns, i, j, k, l + 1);
    }
}

proof fn sum_k_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int)
    requires
        TODO,
    ensures
        TODO,
    decreases rows - k,
{
    if k >= rows {
    } else {
        numof_l_nonneg(m, rows, columns, i, j, k, 0);
        sum_k_nonneg(m, rows, columns, i, j, k + 1);
    }
}

proof fn sum_j_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int)
    requires
        TODO,
    ensures
        TODO,
    decreases columns - j,
{
    if j >= columns {
    } else {
        sum_k_nonneg(m, rows, columns, i, j, 0);
        sum_j_nonneg(m, rows, columns, i, j + 1);
    }
}

proof fn sum_i_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int)
    requires
        TODO,
    ensures
        TODO,
    decreases rows - i,
{
    if i >= rows {
    } else {
        sum_j_nonneg(m, rows, columns, i, 0);
        sum_i_nonneg(m, rows, columns, i + 1);
    }
}

        
// Challenge 3
#[allow(unused)]
fn shearsort(n: usize, m: &mut Vec<Vec<i32>>)
    requires
        TODO
    ensures
       TODO
{

    loop
        invariant
            forall|x: int| #[trigger]
                mocc(x, m@, n as int, n as int) == #[trigger] mocc(x, old(m)@, n as int, n as int),
            m.len() == n,
            forall|i: int| 0 <= i < n ==> #[trigger] m[i].len() == n,
        decreases inversions(m@, n as int, n as int)
    {
        let ghost l1_inv = inversions(m@, n as int, n as int);

        for i in 0..n
            invariant
                forall|k: int|
                    0 <= k < i ==> sorted_row(m@, n as int, n as int, k, #[trigger] even(k)),
                forall|x: int| #[trigger]
                    mocc(x, m@, n as int, n as int) == #[trigger] mocc(
                        x,
                        old(m)@,
                        n as int,
                        n as int,
                    ),
                inversions(m@, n as int, n as int) <= l1_inv,
                m.len() == n,
                
                forall|j: int| 0 <= j < n ==> (#[trigger] m[j]).len() == n,
        {
            sort_row(m, n, n, i, i % 2 == 0);
        }

        let ghost l2_m = m@;
        let ghost l2_inv = inversions(m@, n as int, n as int);
        let mut nochange = true;

        for j in 0..n
            invariant
                nochange ==> forall|i: int, j: int|
                    0 <= i < n && 0 <= j < n ==> #[trigger] m[i][j] == l2_m[i][j],
                forall|l: int| 0 <= l < j ==> #[trigger] sorted_column(m@, n as int, n as int, l),
                forall|x: int| #[trigger]
                    mocc(x, m@, n as int, n as int) == #[trigger] mocc(
                        x,
                        old(m)@,
                        n as int,
                        n as int,
                    ),
                inversions(m@, n as int, n as int) <= l2_inv,
                !nochange ==> inversions(m@, n as int, n as int) < l2_inv,
                m@.len() == n,
                forall|k: int| 0 <= k < n ==> #[trigger] m[k]@.len() == n,
        {
            let nch = sort_column(m, n, n, j);
            if !nch {
                nochange = false;
            }
        }

        if nochange {
            proof {
                lemma_sorted_snake_order(m@, n as int);
            }
            return;
        }

        proof {
            
            inv_nonneg(m@, n as int, n as int);
        }
    }
}

proof fn lemma_sorted_snake_order(m: Seq<Vec<i32>>, n: int)
    requires
        TODO,
    ensures
        TODO,
{
    assert forall|i: int, j: int, k: int, l: int|
        0 <= i < n && 0 <= j < n && 0 <= k < n && 0 <= l < n && lt(i, j, k, l)
        implies m[i][j] <= m[k][l]
    by {
        if i != k {
            if j == l {
                assert(sorted_column(m, n, n, j));
            } else if j < l {
                if even(i) {
                    assert(sorted_column(m, n, n, l));
                } else {
                    assert(sorted_column(m, n, n, j));
                    
                    if !even(k) {
                        if i + 1 < n {
                            assert(even(i + 1));
                            assert(sorted_row(m, n, n, i + 1, true));
                        }
                    }
                }
            } else {
                if even(i) {
                    assert(sorted_column(m, n, n, j));
                    if even(k) {
                        if i + 1 < n {
                            assert(!even(i + 1));
                            assert(m[i][j] <= m[i + 1][j]);
                            
                            assert(sorted_column(m, n, n, l));
                        }
                    }
                }
            }
        }
    }
}



} // verus!
