use vstd::prelude::*;
fn main() {}
verus! {

type Matrix = Vec<Vec<i32>>;

#[allow(unused)]  
type MatrixView = Seq<Seq<i32>>;

spec fn mv(m: &Matrix) -> MatrixView {
    m@.map(|i: int, row: Vec<i32>| row@)
}

#[verifier::external_body]
fn safe_set_2d(v: &mut Matrix, i: usize, j: usize, value: i32)
    requires
        i < old(v).len(),
        j < old(v)[i as int].len(),
        valid_matrix(mv(old(v))),
    ensures
        mv(v).len() == mv(old(v)).len(),
        forall|ri: int| #![trigger v[ri]] 0 <= ri < v.len() ==> v[ri].len() == old(v)[ri].len(),
        mv(v)[i as int][j as int] == value,
        forall|ri: int, rj: int|
            #![trigger mv(v)[ri][rj]]
            0 <= ri < v.len() && 0 <= rj < mv(v)[ri].len() && !(ri == i && rj == j) ==> mv(
                v,
            )[ri][rj] == mv(old(v))[ri][rj],
        valid_matrix(mv(v)),
{
    v[i][j] = value;
}

#[verifier::external_body]
fn two_d_vec_with_capacity(n: usize) -> (result: Matrix)
    ensures
        result@.len() == n,
        forall|i: int| #![trigger result[i]] 0 <= i < n ==> result@[i]@.len() == n,
        forall|i: int, j: int|
            #![trigger mv(&result)[i][j]]
            0 <= i < n && 0 <= j < n ==> mv(&result)[i][j] == 0,
{
    vec![vec![0; n]; n]
}

spec fn valid_matrix(m: MatrixView) -> bool {
    &&& m.len() > 0
    &&& forall|i: int| #![trigger m[i]] 0 <= i < m.len() ==> m[i].len() == m.len()
}

spec fn valid_multiplication(a: MatrixView, b: MatrixView, c: MatrixView) -> bool
    recommends
        valid_matrix(a),
        valid_matrix(b),
        valid_matrix(c),
        a.len() == b.len() == c.len(),
{
    &&& valid_matrix(a) && valid_matrix(b) && valid_matrix(c) && a.len() == b.len() == c.len()
    &&& forall|i: int, j: int|
        0 <= i < a.len() && 0 <= j < a.len() ==> #[trigger] c[i][j] == matrix_sum(a, b, i, j)
}

spec fn matrix_sum(a: MatrixView, b: MatrixView, i: int, j: int) -> int
    recommends
        valid_matrix(a),
        valid_matrix(b),
        a.len() == b.len(),
        i < a.len(),
        j < b.len(),
{
    sum(a, b, i, j, a.len())
}

spec fn sum(a: MatrixView, b: MatrixView, i: int, j: int, k: nat) -> int
    recommends
        valid_matrix(a),
        valid_matrix(b),
        0 <= i < a.len(),
        0 <= j < b.len(),
        0 <= k <= a.len(),
    decreases k,
{
    if k == 0 {
        0
    } else {
        a[i][k - 1] * b[k - 1][j] + sum(a, b, i, j, (k - 1) as nat)
    }
}


// Challenge 1
#[allow(unused)]
#[verifier::loop_isolation(false)]
fn matrix_multiply(a: &Matrix, b: &Matrix) -> (c: Matrix)
    requires
        valid_matrix(mv(&a)),
        valid_matrix(mv(&b)),
        mv(a).len() == mv(b).len(),
        mv(a).len() <= i32::MAX,
        forall|i: int, k: int, j: int|
            #![trigger a[i][k], b[k][j]]
            0 <= i < mv(a).len() && 0 <= k < mv(a).len() && 0 <= j < mv(b).len() ==> i32::MIN < mv(
                a,
            )[i][k] * mv(b)[k][j] < i32::MAX,
        forall|i: int, j: int, k: nat|
            0 <= i < mv(a).len() && 0 <= j < mv(b).len() && 0 <= k <= mv(a).len() ==> i32::MIN
                < #[trigger] sum(mv(a), mv(b), i, j, k) < i32::MAX,
    ensures
        valid_matrix(mv(&c)),
        mv(a).len() == mv(b).len() == mv(&c).len(),
        valid_multiplication(mv(a), mv(b), mv(&c)),
{
    let n = a.len();

    let mut result = two_d_vec_with_capacity(n);

    for i in 0..n
        invariant
            0 <= i <= n,
            mv(&result).len() == n,
            valid_matrix(mv(&result)),
            forall|ir: int, jr: int|
                0 <= ir < i && 0 <= jr < n ==> #[trigger] mv(&result)[ir][jr] == matrix_sum(
                    mv(a),
                    mv(b),
                    ir,
                    jr,
                ),
            forall|ir: int, jr: int|
                i <= ir < n && 0 <= jr < n ==> #[trigger] mv(&result)[ir][jr] == 0,
    {
        for k in 0..n
            invariant
                0 <= k <= n,
                mv(&result).len() == n,
                valid_matrix(mv(&result)),
                forall|ir: int, jr: int|
                    0 <= ir < i && 0 <= jr < n ==> #[trigger] mv(&result)[ir][jr] == matrix_sum(
                        mv(a),
                        mv(b),
                        ir,
                        jr,
                    ),
                forall|ir: int, jr: int|
                    i < ir < n && 0 <= jr < n ==> #[trigger] mv(&result)[ir][jr] == 0,
                forall|jr: int|
                    0 <= jr < n ==> #[trigger] mv(&result)[i as int][jr] == sum(
                        mv(a),
                        mv(b),
                        i as int,
                        jr,
                        k as nat,
                    ),
        {
            for j in 0..n
                invariant
                    TODO,
            {
                assert(j < mv(&result)[i as int].len());

                assert(a[i as int].len() == b[k as int].len() == a.len()) by {
                    assert(mv(&a)[i as int].len() == mv(a).len());
                    assert(mv(&b)[k as int].len() == mv(b).len());
                };

                let product = a[i][k] * b[k][j];
                let current_value = result[i][j];

                assert(current_value + product == sum(
                    mv(a),
                    mv(b),
                    i as int,
                    j as int,
                    (k + 1) as nat,
                ));
                safe_set_2d(&mut result, i, j, current_value + product);
            }
        }
    }

    result
}

} // verus!
