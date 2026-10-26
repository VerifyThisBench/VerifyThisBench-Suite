use vstd::prelude::*;
fn main() {}
verus! {


/////////// SPEC FUNCTIONS

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


//// Main challenge
// Challenge 3
#[allow(unused)]
fn shearsort(n: usize, m: &mut Vec<Vec<i32>>)
    requires
        0 <= n <= usize::MAX,
        old(m).len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] old(m)[i].len() == n,
    ensures
        // task 2
        forall|x: int| mocc(x, m@, n as int, n as int) == mocc(x, old(m)@, n as int, n as int),
        // task 3
        snake_order(m@, n as int, n as int),
{

    TODO
}


} // verus!
