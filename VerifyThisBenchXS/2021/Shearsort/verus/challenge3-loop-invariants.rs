use vstd::prelude::*;
fn main() {}
verus! {













spec fn even(x: int) -> bool {
    x % 2 == 0
}


spec fn occ(x: int, row: Seq<i32>, start: int, end: int) -> nat
    decreases end - start,
{
    if start >= end {
        0
    } else {
        (if row[start] == x {
            1nat
        } else {
            0
        }) + occ(x, row, start + 1, end)
    }
}




spec fn mocc(x: int, m: Seq<Vec<i32>>, row: int, column: int) -> int
    decreases row,
{
    if row <= 0 {
        0
    } else {
        occ(x, m[row - 1]@, 0, column) + mocc(x, m, row - 1, column)
    }
}





spec fn lt(i: int, j: int, k: int, l: int) -> bool {
    i < k || (i == k && if even(i) {
        j < l
    } else {
        l < j
    })
}


spec fn snake_order(m: Seq<Vec<i32>>, rows: int, columns: int) -> bool {
    forall|i: int, j: int, k: int, l: int|
        0 <= i < rows && 0 <= j < columns && 0 <= k < rows && 0 <= l < columns && lt(i, j, k, l)
            ==> m[i][j] <= m[k][l]
}


spec fn inversions(m: Seq<Vec<i32>>, rows: int, columns: int) -> int
    decreases rows, columns, rows, columns,
{
    sum_i(m, rows, columns, 0)
}

spec fn sum_i(m: Seq<Vec<i32>>, rows: int, columns: int, i: int) -> int
    decreases rows - i,
{
    if i >= rows {
        0
    } else {
        sum_j(m, rows, columns, i, 0) + sum_i(m, rows, columns, i + 1)
    }
}

spec fn sum_j(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int) -> int
    decreases columns - j,
{
    if j >= columns {
        0
    } else {
        sum_k(m, rows, columns, i, j, 0) + sum_j(m, rows, columns, i, j + 1)
    }
}

spec fn sum_k(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int) -> int
    decreases rows - k,
{
    if k >= rows {
        0
    } else {
        numof_l(m, rows, columns, i, j, k, 0) + sum_k(m, rows, columns, i, j, k + 1)
    }
}

spec fn numof_l(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int, l: int) -> int
    decreases columns - l,
{
    if l >= columns {
        0
    } else {
        let count: int = if lt(i, j, k, l) && m[i][j] > m[k][l] {
            1
        } else {
            0
        };
        count + numof_l(m, rows, columns, i, j, k, l + 1)
    }
}




spec fn sorted_row(m: Seq<Vec<i32>>, rows: int, columns: int, row: int, ascending: bool) -> bool {
    0 <= row < rows && m.len() == rows && (forall|i: int|
        0 <= i < rows ==> (#[trigger] m[i]).len() == columns) && if ascending {
        forall|j: int, l: int| 0 <= j <= l < columns ==> m[row][j] <= m[row][l]
    } else {
        forall|j: int, l: int| 0 <= j <= l < columns ==> m[row][j] >= m[row][l]
    }
}



spec fn sorted_column(m: Seq<Vec<i32>>, rows: int, columns: int, column: int) -> bool {
    0 <= column < columns && m.len() == rows && (forall|i: int|
        0 <= i < rows ==> (#[trigger] m[i]).len() == columns) && forall|i: int, k: int|
        0 <= i <= k < rows ==> (#[trigger] m[i])[column] <= (#[trigger] m[k])[column]
}



proof fn inv_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int)
    requires
        rows >= 0,
        columns >= 0,
        m.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] m[i].len() == columns,
    ensures
        inversions(m, rows, columns) >= 0,
{
    sum_i_nonneg(m, rows, columns, 0);
}

proof fn numof_l_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int, l: int)
    requires
        rows >= 0,
        columns >= 0,
        l <= columns,
    ensures
        numof_l(m, rows, columns, i, j, k, l) >= 0,
    decreases columns - l,
{
    
    if l >= columns {
    } else {
        numof_l_nonneg(m, rows, columns, i, j, k, l + 1);
    }
}

proof fn sum_k_nonneg(m: Seq<Vec<i32>>, rows: int, columns: int, i: int, j: int, k: int)
    requires
        rows >= 0,
        columns >= 0,
        k <= rows,
    ensures
        sum_k(m, rows, columns, i, j, k) >= 0,
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
        rows >= 0,
        columns >= 0,
        j <= columns,
    ensures
        sum_j(m, rows, columns, i, j) >= 0,
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
        rows >= 0,
        columns >= 0,
        i <= rows,
    ensures
        sum_i(m, rows, columns, i) >= 0,
    decreases rows - i,
{
    
    if i >= rows {
    } else {
        sum_j_nonneg(m, rows, columns, i, 0);
        sum_i_nonneg(m, rows, columns, i + 1);
    }
}





#[allow(unused)]
fn sort_row(m: &mut Vec<Vec<i32>>, rows: usize, columns: usize, row: usize, ascending: bool)
    requires
        0 <= row < rows,
        old(m)@.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] old(m)[i].len() == columns,
    ensures
        
        forall|i: int, j: int|
            0 <= i < rows && 0 <= j < columns && i != row ==> m[i][j] == old(m)[i][j],
        
        forall|x: int|
            mocc(x, m@, rows as int, columns as int) == mocc(
                x,
                old(m)@,
                rows as int,
                columns as int,
            ),
        
        sorted_row(m@, rows as int, columns as int, row as int, ascending),
        
        inversions(m@, rows as int, columns as int) <= inversions(
            old(m)@,
            rows as int,
            columns as int,
        ),
        
        m.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] m[i].len() == columns,
{
    external_fn()
}




#[allow(unused)]
fn sort_column(m: &mut Vec<Vec<i32>>, rows: usize, columns: usize, column: usize) -> (nochange: bool)
    requires
        0 <= column < columns,
        old(m)@.len() == rows,
        forall|i: int| 0 <= i < rows ==> #[trigger] old(m)[i].len() == columns,
    ensures
        
        forall|i: int, j: int|
            0 <= i < rows && 0 <= j < columns && j != column ==> m[i][j] == old(m)[i][j],
        
        forall|c: int| 0 <= c < columns && c != column && sorted_column(old(m)@, rows as int, columns as int, c) ==> 
            sorted_column(m@, rows as int, columns as int, c),
        
        forall|x: int|
            mocc(x, m@, rows as int, columns as int) == mocc(
                x,
                old(m)@,
                rows as int,
                columns as int,
            ),
        
        nochange ==> forall|i: int|
            0 <= i < rows ==> (#[trigger] m[i])[column as int] == old(m)[i][column as int],
        
        sorted_column(m@, rows as int, columns as int, column as int),
        
        inversions(m@, rows as int, columns as int) <= inversions(
            old(m)@,
            rows as int,
            columns as int,
        ),
        
        !nochange ==> inversions(m@, rows as int, columns as int) < inversions(
            old(m)@,
            rows as int,
            columns as int,
        ),
        
        m.len() == rows,
        forall|i: int| 0 <= i < rows ==> (#[trigger] m[i]).len() == columns,
{
    external_fn()
}



























#[allow(unused)]
fn shearsort(n: usize, m: &mut Vec<Vec<i32>>)
    requires
        0 <= n <= usize::MAX,
        old(m).len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] old(m)[i].len() == n,
    ensures
        
        forall|x: int| mocc(x, m@, n as int, n as int) == mocc(x, old(m)@, n as int, n as int),
        
        snake_order(m@, n as int, n as int),
{
    
    
    
    
    
    
    
    

    loop
        invariant
            TODO,
        decreases inversions(m@, n as int, n as int)
        
    {
        let ghost l1_inv = inversions(m@, n as int, n as int);

        for i in 0..n
            invariant
                TODO,
        {
            sort_row(m, n, n, i, i % 2 == 0);
        }

        let ghost l2_m = m@;
        let ghost l2_inv = inversions(m@, n as int, n as int);
        let mut nochange = true;

        for j in 0..n
            invariant
                TODO,
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
        m.len() == n >= 0,
        forall|i: int| 0 <= i < n ==> #[trigger] m[i].len() == n,
        forall|k: int| 0 <= k < n ==> sorted_row(m, n, n, k, #[trigger] even(k)),
        forall|l: int| 0 <= l < n ==> sorted_column(m, n, n, l),
    ensures
        snake_order(m, n, n),
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










#[verifier::external_body]
fn external_fn<A>() -> (x: A)
    ensures
        false,
{
    unimplemented!();
}

} 
