use vstd::prelude::*;
fn main() {}
verus! {

spec fn ordered(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] <= s[k]
}

spec fn increasing(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] < s[k]
}

spec fn decreasing(s: Seq<i32>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] >= s[k]
}

spec fn monotonic(s: Seq<i32>) -> bool {
    increasing(s) || decreasing(s)
}

spec fn monotonic_cuts(s: Seq<i32>, c: Seq<usize>) -> bool {
    TODO
}

spec fn maximal_cuts(s: Seq<i32>, c: Seq<usize>) -> bool {
    monotonic_cuts(s, c) && (forall|k: int|
        0 < k < c.len() - 1 ==> !monotonic(s.subrange(#[trigger] c[k - 1] as int, c[k] + 1)))
}

proof fn extend_cuts(s: Seq<i32>, c: Seq<usize>, d: int)
    requires
        0 <= d < s.len() <= i32::MAX,
        monotonic_cuts(s.subrange(0, d), c),
        monotonic(s.subrange(d, s.len() as int)),
    ensures
        monotonic_cuts(s, c + Seq::empty().push(s.len() as usize)),
{
    let c2 = c + Seq::empty().push(s.len() as usize);

    let c2_as_seq_i32: Seq<i32> = c2.map_values(|element: usize| element as i32);
    assert(increasing(c2_as_seq_i32)) by {
        let c_as_seq_i32: Seq<i32> = c.map_values(|element: usize| element as i32);
        assert forall|j: int, k: int| 0 <= j < k < c2_as_seq_i32.len() implies c2_as_seq_i32[j]
            < c2_as_seq_i32[k] by {
            if k < c2_as_seq_i32.len() - 1 {
                assert(c_as_seq_i32[j] < c_as_seq_i32[k]);
            } else {
                assert(k == c2_as_seq_i32.len() - 1);
            }
        };
    };

    assert forall|k: int| 0 < k < c2.len() implies monotonic(
        s.subrange(c2[k - 1] as int, #[trigger] c2[k] as int),
    ) by {
        if k < c2.len() - 1 {
            assert(s.subrange(0, d).subrange(c[k - 1] as int, c[k] as int) =~= s.subrange(
                c[k - 1] as int,
                c[k] as int,
            )) by {
                assert(c[k - 1] <= c[k]) by {
                    let c_as_seq_i32: Seq<i32> = c.map_values(|element: usize| element as i32);
                    assert(c_as_seq_i32[k - 1] < c_as_seq_i32[k]);
                };
                assert(c[k] as int <= s.subrange(0, d).len());
            };
        }
    };
}

proof fn extend_max(s: Seq<i32>, x: int, y: int)
    requires
        0 <= x < y < s.len() <= usize::MAX,
        monotonic(s.subrange(x, y)),
        increasing(s.subrange(x, y)) ==> s[y - 1] >= s[y],
        decreasing(s.subrange(x, y)) ==> s[y - 1] < s[y],
    ensures
        !monotonic(s.subrange(x, y + 1)),
{
    if increasing(s.subrange(x, y)) {
        assert(s.subrange(x, y + 1)[y - 1 - x] == s[y - 1]);
        assert(s.subrange(x, y + 1)[y - x] == s[y]);

        if s.subrange(x, y).len() > 1 {
            assert(s.subrange(x, y)[0] == s[x]);
            assert(s.subrange(x, y)[1] == s[x + 1]);
            assert(s.subrange(x, y + 1)[0] == s[x]);
            assert(s.subrange(x, y + 1)[1] == s[x + 1]);
            assert(!decreasing(s.subrange(x, y + 1)));
        }
    } else {
        assert(!decreasing(s.subrange(x, y + 1))) by {
            assert(s.subrange(x, y + 1)[y - 1 - x] == s[y - 1]);
            assert(s.subrange(x, y + 1)[y - x] == s[y]);
        }

        if s.subrange(x, y).len() > 1 {
            assert(s.subrange(x, y)[0] == s[x]);
            assert(s.subrange(x, y)[1] == s[x + 1]);
            assert(s.subrange(x, y + 1)[0] == s[x]);
            assert(s.subrange(x, y + 1)[1] == s[x + 1]);
            assert(!increasing(s.subrange(x, y + 1)));
        }
    }
}

// Challenge 1
#[allow(unused)]
fn monotonic_cutpoints(a: &Vec<i32>) -> (c: Vec<usize>)
    requires
        a@.len() < i32::MAX - 1,
    ensures
        monotonic_cuts(a@, c@),
        maximal_cuts(a@, c@),
{
    let mut c = vec![0];
    let (mut x, mut y) = (0, 1);
    let ghost p = 0int;

    while y < a.len()
        invariant
            0 <= x < y <= a@.len() + 1 < i32::MAX,
            y == x + 1,
            0 <= p <= x,
            monotonic_cuts(a@.subrange(0, x as int), c@),
            forall|k: int|
                #![trigger c[k]]
                0 < k < c@.len() - 1 ==> !monotonic(a@.subrange(c[k - 1] as int, c[k] + 1)),
            0 < x < a@.len() ==> !monotonic(a@.subrange(p, x + 1)),
            c@.len() > 1 ==> c@[c@.len() - 2] == p,
            c@.len() > 1 ==> x > 0,
            x == c@[c@.len() - 1] as int,
        decreases a.len() - x,
    {
        let inc: bool = a[x] < a[y];

        proof {
            assert(a@.subrange(0, y as int).subrange(0, x as int) =~= a@.subrange(0, x as int));
            extend_cuts(a@.subrange(0, y as int), c@, x as int);
        }

        while y < a.len() && ((a[y - 1] < a[y]) == inc)
            invariant
                a@.len() < i32::MAX - 1,
                0 <= x < y <= a@.len(),
                monotonic_cuts(a@.subrange(0, x as int), c@),
                monotonic(a@.subrange(x as int, y as int)),
                monotonic_cuts(a@.subrange(0, y as int), c@ + seq![y]),
                inc <==> (a@[x as int] < a@[x + 1]),
                inc ==> increasing(a@.subrange(x as int, y as int)),
                !inc ==> decreasing(a@.subrange(x as int, y as int)),
                y > x + 1 ==> ((a@[y - 2] < a@[y - 1]) <==> inc),
            decreases a.len() - y,
        {
            y += 1;
            proof {
                let old_subrange = a@.subrange(x as int, (y - 1) as int);
                let new_subrange = a@.subrange(x as int, y as int);

                assert(new_subrange =~= old_subrange + Seq::empty().push(a@[y - 1]));

                if !inc {
                    assert forall|i: int, j: int|
                        0 <= i < j < new_subrange.len() implies new_subrange[i]
                        >= new_subrange[j] by {
                        if j >= old_subrange.len() && i != old_subrange.len() - 1 {
                            vstd::calc! {
                                (>=)
                                new_subrange[i]; (==) { assert(new_subrange[i] == old_subrange[i]); }
                                old_subrange[i]; (>=) { assert(old_subrange[i] >= old_subrange[old_subrange.len() - 1]); }
                                old_subrange[old_subrange.len() - 1];
                            }
                        }
                    };
                }


                assert(a@.subrange(0, y as int).subrange(0, x as int) =~= a@.subrange(0, x as int));

                let s = a@.subrange(0, y as int);
                assert(s.subrange(x as int, s.len() as int) =~= new_subrange);
                assert(monotonic(s.subrange(x as int, s.len() as int)));
                extend_cuts(s, c@, x as int);
            }
        }
        assert(monotonic(a@.subrange(x as int, y as int)));

        proof {
            if y < a.len() {
                if !inc {
                    vstd::assert_by_contradiction!(!increasing(a@.subrange(x as int, y as int)), {
                        if a@.subrange(x as int, y as int).len() > 1 {
                            assert(a@.subrange(x as int, y as int)[0] < a@.subrange(x as int, y as int)[1]);
                        }
                    });
                }
                extend_max(a@, x as int, y as int);
            }
        }

        let ghost old_c = c@;
        c.push(y);

        proof {
            p = x as int;
        }

        assert(monotonic_cuts(a@.subrange(0, y as int), c@)) by {
            assert(a@.subrange(0, y as int).subrange(0, x as int) =~= a@.subrange(0, x as int));


            assert(old_c + Seq::empty().push(y) =~= c@);
        }

        x = y;
        y = x + 1;

    }

    if x < a.len() {
        let ghost initial_c = c@;

        c.push(a.len());
        assert(monotonic_cuts(a@, c@)) by {
            let c_new = initial_c + Seq::empty().push(a@.len() as usize);
            extend_cuts(a@, initial_c, x as int);
            assert(c_new =~= c@);
        }
    }  

    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }

    c
}

} // verus!
