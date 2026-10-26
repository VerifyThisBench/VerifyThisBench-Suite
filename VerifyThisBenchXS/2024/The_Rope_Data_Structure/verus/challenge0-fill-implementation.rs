use vstd::prelude::*;
fn main() {}
verus! {


pub struct Rope {
    pub left: Option<Box<Rope>>,
    pub right: Option<Box<Rope>>,
    pub value: Vec<u8>,
    pub weight: usize,
}


impl Clone for Rope {
    fn clone(&self) -> (result: Self)
        ensures
            self.well_formed() <==> result.well_formed(),
            self.represents()
                =~= result.represents(),  

        decreases self,
    {
        TODO
    }
}


fn vec_subrange(v: &Vec<u8>, start: usize, end: usize) -> (result: Vec<u8>)
    requires
        start <= end,
        end <= v.len(),
    ensures
        result@ == v@.subrange(start as int, end as int),
        result.len() == end - start,
{
   TODO
}

impl Rope {
    pub open spec fn well_formed(self) -> bool
        decreases self,
    {
        &&& self.value@.len() > 0 ==> self.left.is_none() && self.right.is_none()
        &&& self.weight == 0 ==> self.left.is_none()
        &&& self.left.is_some() ==> self.left.unwrap().well_formed()
        &&& self.right.is_some() ==> self.right.unwrap().well_formed()
        &&& self.weight == match self.left {
            Some(left_rope) => left_rope.str_len_spec(),
            None => self.value@.len(),
        }
    }

    pub open spec fn represents(self) -> Seq<u8>
        decreases self,
    {
        if self.value@.len() > 0 {
            self.value@
        } else {
            match (self.left, self.right) {
                (None, None) => Seq::empty(),
                (None, Some(s)) => s.represents(),
                (Some(s), None) => s.represents(),
                (Some(left), Some(right)) => left.represents() + right.represents(),
            }
        }
    }

    pub open spec fn str_len_spec(self) -> nat {
        self.represents().len()
    }

    
    
    
    
    
    #[allow(unused)]
    fn to_str(&self) -> (result: Vec<u8>)
        requires
            self.well_formed(),
        ensures
            self.represents() == result@,
            self.well_formed(),
    {
        TODO
    }

    
    #[allow(unused)]
    fn str_len(&self) -> (result: usize)
        requires
            self.well_formed(),
            self.str_len_spec() < usize::MAX,
        ensures
            self.str_len_spec() == result,
            self.well_formed(),
        decreases self,
    {
        TODO
    }

    
    
    
    
    #[allow(unused)]
    fn concat(left: Rope, right: Rope) -> (result: Rope)
        requires
            left.well_formed(),
            right.well_formed(),
            left.str_len_spec() < i32::MAX,
            right.str_len_spec() < i32::MAX,
        ensures
            left.well_formed(),
            right.well_formed(),
            result.well_formed(),
            result.represents() == left.represents() + right.represents(),
    {
        TODO
    }

    
    
    
    #[allow(unused)]
    fn delete(rope: &Rope, i: usize, len: usize) -> (result: Rope)
        requires
            rope.well_formed(),
            i + len <= rope.str_len_spec() < i32::MAX,
        ensures
            result.well_formed(),
            result.represents() =~= rope.represents().subrange(0, i as int)
                + rope.represents().subrange((i + len) as int, rope.str_len_spec() as int),
            result.str_len_spec() == rope.str_len_spec() - len,
    {
        TODO
    }

    fn split(rope: Rope, i: usize) -> (results: (Rope, Rope))
        requires
            rope.well_formed(),
            0 <= i <= rope.str_len_spec() < i32::MAX,
        ensures
            results.0.well_formed(),
            results.1.well_formed(),
            results.0.represents() + results.1.represents() =~= rope.represents(),
            results.0.str_len_spec() == i,
            results.1.str_len_spec() == rope.str_len_spec() - i,
            results.0.represents() =~= rope.represents().subrange(0, i as int),
            results.1.represents() =~= rope.represents().subrange(
                i as int,
                rope.str_len_spec() as int,
            ),
        decreases rope,
    {
        TODO
    }

    fn make_leaf(value: Vec<u8>) -> (result: Rope)
        requires
            value@.len() < i32::MAX,
        ensures
            result.well_formed(),
            result.represents() =~= value@,
    {
        TODO
    }

    fn to_str_recurse(&self, string: &mut Vec<u8>)
        requires
            self.well_formed(),
        ensures
            string@ =~= old(string)@ + self.represents(),
            self.well_formed(),
        decreases self,
    {
        TODO
    }
}

} 
