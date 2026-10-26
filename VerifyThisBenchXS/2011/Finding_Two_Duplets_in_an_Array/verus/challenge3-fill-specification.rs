use vstd::prelude::*;
fn main() {}
verus! {

proof fn lemma_transitive_contains(s: Seq<i32>, x: i32)
    requires
        TODO,
    ensures
        TODO,
    decreases s,
{
    let index = choose|i: int| 0 <= i < s.len() && s[i] == x;
    assert(s.drop_first()[index - 1] == x);
}

proof fn occurrences_concat_transitive(x: i32, s: Seq<i32>, y: i32)
    ensures
        occurrences(Seq::empty().push(x) + s, y) == (if x == y {
            1nat
        } else {
            0
        }) + occurrences(s, y),
    decreases s,
{
    if s.len() == 0 {
        reveal_with_fuel(occurrences, 2);
    } else {
        // I.H.
        occurrences_concat_transitive(x, s.drop_first(), y);

        assert(occurrences(Seq::empty().push(x) + s, y) == (if x == y {
            1nat
        } else {
            0
        }) + occurrences(s, y)) by {
            assert((Seq::empty().push(x) + s).drop_first() == s);
        };
    }
}

proof fn occurrences_remove(s: Seq<i32>, x: i32, y: i32)
    ensures
        occurrences(s, y) >= occurrences(remove_spec(s, x), y),
    decreases s,
{
    if s.len() == 0 {
        // Base case
    } else {
        // I.H.
        occurrences_remove(s.drop_first(), x, y);

        if s.first() == x {
        } else {
            let first_is_y: nat = if s.first() == y {
                1
            } else {
                0
            };

            assert(occurrences(remove_spec(s, x), y) == first_is_y + occurrences(
                remove_spec(s.drop_first(), x),
                y,
            )) by {
                let first_removed = remove_spec(s.drop_first(), x);
                assert(remove_spec(s, x) == Seq::empty().push(s.first()) + first_removed);

                occurrences_concat_transitive(s.first(), first_removed, y);
            };
        }
    }
}

proof fn lemma_drop_first_concat(p: Seq<i32>, q: Seq<i32>)
    requires
        TODO
    ensures
        TODO,
    decreases p,
{
    assert((p + q).drop_first() == p.drop_first() + q)
}

proof fn lemma_remove_spec_append(p: Seq<i32>, x: i32, a: i32)
    ensures
        remove_spec(p + Seq::empty().push(a), x) =~= remove_spec(p, x) + if a == x {
            Seq::empty()
        } else {
            Seq::empty().push(a)
        },
    decreases p,
{
    if p.len() == 0 {
        if a == x {
            assert(remove_spec(Seq::empty().push(a), x) =~= Seq::<i32>::empty()) by {
                reveal_with_fuel(remove_spec, 2);
            };
        } else {
            assert(remove_spec(Seq::empty().push(a), x) == Seq::empty().push(a)) by {
                reveal_with_fuel(remove_spec, 2);
            }
        }
    } else {
        lemma_remove_spec_append(p.drop_first(), x, a);
        lemma_drop_first_concat(p, Seq::empty().push(a));
    }
}

proof fn lemma_remove_prefix(s: Seq<i32>, x: i32, n: nat)
    requires
        TODO,
    ensures
        TODO,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_remove_prefix(s, x, (n - 1) as nat);

        let a = s[n - 1];

        assert(s.take(n as int) == s.take((n - 1) as int) + Seq::empty().push(a));
        lemma_remove_spec_append(s.take((n - 1) as int), x, a);
    }
}

proof fn lemma_remove_prefix_all_equiv(s: Seq<i32>, x: i32)
    ensures
        remove_spec(s, x) == remove_with_prefix(s, x, s.len()),
{
    lemma_remove_prefix(s, x, s.len());
    assert(s.take(s.len() as int) =~= s);
}

exec fn remove(v: Vec<i32>, x: i32) -> (result: Vec<i32>)
    ensures
        !result@.contains(x),
        v.len() >= result.len(),
        result@ =~= remove_spec(v@, x),
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            result.len() <= i <= v.len(),
            forall|j: int| 0 <= j < result@.len() ==> result@[j as int] != x,
            result@ =~= remove_with_prefix(v@, x, i as nat),
        decreases v.len() - i,
    {
        if v[i] != x {
            result.push(v[i]);
        }
        i += 1;
    }

    proof {
        lemma_remove_prefix_all_equiv(v@, x);
    }

    result
}

fn first_dropped(v: &Vec<i32>) -> (result: Vec<i32>)
    requires
        TODO,
    ensures
        TODO,
{
    let mut new_v = Vec::new();
    let mut i: usize = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            new_v@ =~= v@.subrange(1, i as int),
        decreases v.len() - i,
    {
        new_v.push(v[i]);
        i += 1;
    }
    new_v
}

fn contains(v: &Vec<i32>, x: i32) -> (found: bool)
    ensures
        found == v@.contains(x),
{
    let mut i: usize = 0;
    let mut result: bool = false;
    while i < v.len() && !result
        invariant
            0 <= i <= v.len(),
            result == exists|j: int| 0 <= j < i && v@[j] == x,
        decreases v.len() - i,
    {
        if v[i] == x {
            result = true;
        }
        i += 1;
    }
    result
}

// ============================================
// ===== Main lemmas/specs from Dafny Team ====
// ============================================
spec fn first_duplicate_spec(s: Seq<i32>) -> i32
    recommends
        has_duplicates(s),
    decreases s,
{
    TODO
}

spec fn has_duplicates(s: Seq<i32>) -> bool
    decreases s,
{
    TODO
}

spec fn occurrences(s: Seq<i32>, x: i32) -> nat
    decreases s,
{
   TODO
}

spec fn remove_spec(s: Seq<i32>, x: i32) -> (removed: Seq<i32>)
    decreases s,
{
    TODO
}

spec fn remove_with_prefix(s: Seq<i32>, x: i32, n: nat) -> Seq<i32>
    decreases n,
{
   TODO
}

proof fn multiple_occurences(s: Seq<i32>)
    requires
        TODO,
    ensures
        TODO,
    decreases s,
{
    if s.drop_first().contains(s.first()) {
        occurrences_when_present(s.drop_first(), s.first());
    } else {
        multiple_occurences(s.drop_first());
    }
}

proof fn occurrences_when_present(s: Seq<i32>, x: i32)
    requires
        TODO,
    ensures
        TODO,
    decreases s,
{
    if x != s.first() {
        lemma_transitive_contains(s, x);
        occurrences_when_present(s.drop_first(), x);
    }
}

exec fn first_duplicate(s: Vec<i32>) -> (result: i32)
    requires
        TODO,
    ensures
        TODO,
    decreases s.len(),
{
    let first = s[0];
    let rest = first_dropped(&s);
    if contains(&rest, first) {
        first
    } else {
        proof { assert(rest.len() < s.len()) }
        first_duplicate(rest)
    }
}

// Main challenge 3
#[allow(unused)]
fn find_two_duplicates(a: &Vec<i32>) -> (results: (i32, i32))
    requires
        TODO,
    ensures
        TODO,
{
    let x = first_duplicate(a.clone());
    proof {
        multiple_occurences(a@);
    }

    let x_removed = remove(a.clone(), x);

    let y = first_duplicate(x_removed);
    proof {
        multiple_occurences(x_removed@);
        occurrences_remove(a@, x, y);
    }

    (x, y)
}

} // verus!
