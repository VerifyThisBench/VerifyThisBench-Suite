use vstd::prelude::*;
fn main() {}
verus! {


exec fn remove(v: Vec<i32>, x: i32) -> (result: Vec<i32>)
    ensures
        !result@.contains(x),
        v.len() >= result.len(),
        result@ =~= remove_spec(v@, x),
{
    TODO
}

fn first_dropped(v: &Vec<i32>) -> (result: Vec<i32>)
    requires
        v.len() > 0,
    ensures
        v@.drop_first() == result@,
{
    TODO
}

fn contains(v: &Vec<i32>, x: i32) -> (found: bool)
    ensures
        found == v@.contains(x),
{
    TODO
}

spec fn first_duplicate_spec(s: Seq<i32>) -> i32
    recommends
        has_duplicates(s),
    decreases s,
{
    if s.len() == 0 {
        0
    } else {
        let first = s.first();
        if s.drop_first().contains(first) {
            first
        } else {
            first_duplicate_spec(s.drop_first())
        }
    }
}

spec fn has_duplicates(s: Seq<i32>) -> bool
    decreases s,
{
    if s.len() == 0 {
        false
    } else {
        let first = s.first();
        s.drop_first().contains(first) || has_duplicates(s.drop_first())
    }
}

spec fn occurrences(s: Seq<i32>, x: i32) -> nat
    decreases s,
{
    if s.len() == 0 {
        0
    } else {
        let summand: nat = if s.first() == x {
            1
        } else {
            0
        };
        summand + occurrences(s.drop_first(), x)
    }
}

spec fn remove_spec(s: Seq<i32>, x: i32) -> (removed: Seq<i32>)
    decreases s,
{
    if s.len() == 0 {
        s
    } else {
        if s.first() == x {
            remove_spec(s.drop_first(), x)
        } else {
            Seq::empty().push(s.first()) + remove_spec(s.drop_first(), x)
        }
    }
}

spec fn remove_with_prefix(s: Seq<i32>, x: i32, n: nat) -> Seq<i32>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        remove_with_prefix(s, x, (n - 1) as nat) + if s[n - 1] == x {
            Seq::empty()
        } else {
            Seq::empty().push(s[n - 1])
        }
    }
}


exec fn first_duplicate(s: Vec<i32>) -> (result: i32)
    requires
        has_duplicates(s@),
    ensures
        s@.contains(result),
        result == first_duplicate_spec(s@),
    decreases s.len(),
{
    TODO
}

// Main challenge 3
#[allow(unused)]
fn find_two_duplicates(a: &Vec<i32>) -> (results: (i32, i32))
    requires
        a.len() >= 4,
        has_duplicates(a@),
        has_duplicates(remove_spec(a@, first_duplicate_spec(a@))),
    ensures
        occurrences(a@, results.0) > 1,
        occurrences(a@, results.1) > 1,
        results.0 != results.1,
{
    TODO
}

} // verus!
