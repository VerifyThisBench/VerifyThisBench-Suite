use vstd::prelude::*;
fn main() {}
verus! {



#[derive(Eq, PartialEq, Clone, Copy)]
struct Point {
    x: u32,
    y: u32,
    z: u32,
}

impl Point {
    
    
    fn add(self, rhs: Self) -> (result: Self)
        requires
            self.x + rhs.x <= u32::MAX,
            self.y + rhs.y <= u32::MAX,
            self.z + rhs.z <= u32::MAX,
        ensures
            result.x == self.x + rhs.x,
            result.y == self.y + rhs.y,
            result.z == self.z + rhs.z,
    {
        Point { x: self.x + rhs.x, y: self.y + rhs.y, z: self.z + rhs.z }
    }

    fn div_by(self, rhs: u32) -> (result: Self)
        requires
            rhs != 0,
    {
        Point { x: self.x / rhs, y: self.y / rhs, z: self.z / rhs }
    }

    
    
    
    fn default() -> (result: Self)
        ensures
            result.x == 0,
            result.y == 0,
            result.z == 0,
    {
        Point { x: 0, y: 0, z: 0 }
    }
}




macro_rules! max_by_what {
    ($name:ident, $field:ident) => {
        verus! {
            
            
            
            fn $name(p: &Vec<Point>) -> (result: Point)
            requires
                p.len() > 0
            ensures
                p@.contains(result),
                forall|i: int| #![trigger p[i]] !(0 <= i < p@.len()) || p[i].$field <= result.$field
        {
            let mut max = p[0];
            let ghost mut max_idx = 0int;

            for i in 0..p.len()
                invariant
                    forall|j: int| #![trigger p[j]] !(0 <= j < i) || p@[j].$field <= max.$field,
                    0 <= max_idx < p.len() && p[max_idx] == max
            {
                if p[i].$field >= max.$field {
                    max = p[i];
                    proof { max_idx = i as int; }
                }
            }
            max
        }}
    };
}

macro_rules! min_by_what {
    ($name:ident, $field:ident) => {
        verus! {
            
            
            
            fn $name(p: &Vec<Point>) -> (result: Point)
            requires
                p.len() > 0
            ensures
                p@.contains(result),
                forall|i: int| #![trigger p[i]] !(0 <= i < p@.len()) || p[i].$field >= result.$field
        {
            let mut max = p[0];
            let ghost mut max_idx = 0int;

            for i in 0..p.len()
                invariant
                    forall|j: int| #![trigger p[j]] !(0 <= j < i) || p@[j].$field >= max.$field,
                    0 <= max_idx < p.len() && p[max_idx] == max
            {
                if p[i].$field <= max.$field {
                    max = p[i];
                    proof { max_idx = i as int; }
                }
            }
            max
        }}
    };
}

max_by_what!(array_max_by_x, x);

max_by_what!(array_max_by_y, y);

max_by_what!(array_max_by_z, z);

min_by_what!(array_min_by_x, x);

min_by_what!(array_min_by_y, y);

min_by_what!(array_min_by_z, z);

fn abs(x: i32) -> (result: u32)
    requires
        x != i32::MIN,  

    ensures
        result == vstd::math::abs(x as int),
{
    if x >= 0 {
        x as u32
    } else {
        (-x) as u32
    }
}


















pub open spec fn div_ceil(a: u32, b: u32) -> u32
    recommends
        b > 0,
{
    if a % b == 0 {
        a / b
    } else {
        (a / b + 1) as u32
    }
}






#[verifier::external_body]
fn three_d_vec_with_capacity<T>(
    outer: usize,
    middle: usize,
    inner: usize,
    default_value: T,
) -> (result: Vec<Vec<Vec<T>>>) where T: Copy
    ensures
        result@.len() == outer,
        forall|i: int| #![trigger result@[i]] 0 <= i < outer ==> result@[i]@.len() == middle,
        forall|i: int, j: int|
            #![trigger result@[i]@[j]]
            0 <= i < outer && 0 <= j < middle ==> result@[i]@[j]@.len() == inner,
        forall|i: int, j: int, k: int|
            #![trigger result@[i]@[j]@[k]]
            0 <= i < outer && 0 <= j < middle && 0 <= k < inner ==> result@[i]@[j]@[k]
                == default_value,
{
    vec![vec![vec![default_value; inner]; middle]; outer]
}




#[verifier::external_body]
fn safe_set_3d<T>(v: &mut Vec<Vec<Vec<T>>>, i: usize, j: usize, k: usize, value: T)
    requires
        
        i < old(v)@.len(),
        
        j < old(v)@[i as int]@.len(),
        
        k < old(v)@[i as int]@[j as int]@.len(),
    ensures
        
        v@.len() == old(v)@.len(),
        
        forall|ri: int| #![trigger v@[ri]] 0 <= ri < v@.len() ==> v@[ri].len() == old(v)@[ri].len(),
        
        forall|ri: int, rj: int|
            #![trigger v@[ri][rj]]
            0 <= ri < v@.len() && 0 <= rj < v@[ri].len() ==> v@[ri][rj].len() == old(
                v,
            )@[ri][rj].len(),
        
        v@[i as int][j as int][k as int] == value,
        
        v@[i as int]@[j as int]@.contains(value),
        
        forall|ri: int, rj: int, rk: int|
            #![trigger v@[ri][rj][rk]]
        
            0 <= ri < v@.len() && 0 <= rj < v@[ri].len() && 0 <= rk < v@[ri][rj].len() && !(ri == i
                && rj == j && rk == k) ==> v@[ri][rj][rk] == old(v)@[ri][rj][rk],
{
    v[i][j][k] = value;
}

spec fn valid_3d_array_structure<T>(
    array: Seq<Vec<Vec<T>>>,
    outer: int,
    middle: int,
    inner: int,
) -> bool {
    &&& array.len() == outer
    &&& forall|i: int| #![trigger array[i]] 0 <= i < outer ==> array[i].len() == middle
    &&& forall|i: int, j: int|
        #![trigger array[i][j]]
        0 <= i < outer && 0 <= j < middle ==> array[i][j].len() == inner
}

proof fn lemma_floor_bounds(coord_diff: u32, coord_range: nat, voxel_size: u32)
    requires
        coord_diff <= coord_range,
        voxel_size > 0,
    ensures
        coord_diff / voxel_size <= coord_range / voxel_size as nat,
{
    TODO
}

spec fn count_nonzeros_3d(v: Seq<Vec<Vec<u32>>>) -> nat
    decreases v,
{
    if v.len() == 0 {
        0
    } else {
        count_nonzeros_2d(v.first()@) + count_nonzeros_3d(v.drop_first())
    }
}

spec fn count_nonzeros_2d(v: Seq<Vec<u32>>) -> nat
    decreases v,
{
    if v.len() == 0 {
        0
    } else {
        count_nonzeros_1d(v.first()@) + count_nonzeros_2d(v.drop_first())
    }
}

spec fn count_nonzeros_1d(v: Seq<u32>) -> nat
    decreases v,
{
    if v.len() == 0 {
        0
    } else {
        let first_is_zero = if v.first() != 0 {
            1nat
        } else {
            0
        };

        first_is_zero + count_nonzeros_1d(v.drop_first())
    }
}



spec fn no_input_overflows(p: Seq<Point>) -> bool {
    
    
    
    &&& forall|i: int|
        0 <= i < p.len() ==> {
            &&& #[trigger] p[i].x <= u16::MAX
            &&& #[trigger] p[i].y <= u16::MAX
            &&& #[trigger] p[i].z <= u16::MAX
        }
    &&& p.len() <= (u32::MAX as int / u16::MAX as int) as usize
}


#[verifier::loop_isolation(false)]
#[allow(unused)]
fn downsample(p: Vec<Point>, voxel_size: u32) -> (result: Vec<Point>)
    requires
        no_input_overflows(p@),
        voxel_size > 0,
        0 < p.len(),
        p.len() * u16::MAX as int <= i32::MAX,
        p.len() * u16::MAX as int <= i32::MAX,
{
    TODO
}

} 
