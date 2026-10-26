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
            TODO,
        ensures
            TODO,
    {
        Point { x: self.x + rhs.x, y: self.y + rhs.y, z: self.z + rhs.z }
    }

    fn div_by(self, rhs: u32) -> (result: Self)
        requires
            TODO,
    {
        Point { x: self.x / rhs, y: self.y / rhs, z: self.z / rhs }
    }

    
    
    
    fn default() -> (result: Self)
        ensures
            TODO,
    {
        Point { x: 0, y: 0, z: 0 }
    }
}



















































macro_rules! max_by_what {
    ($name:ident, $field:ident) => {
        verus! {
            
            
            
            fn $name(p: &Vec<Point>) -> (result: Point)
            requires
                TODO
            ensures
                TODO
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
                TODO
            ensures
                TODO
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
        TODO

    ensures
        TODO
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
        TODO
    ensures
        TODO,
{
    v[i][j][k] = value;
}

spec fn valid_3d_array_structure<T>(
    array: Seq<Vec<Vec<T>>>,
    outer: int,
    middle: int,
    inner: int,
) -> bool {
    TODO
}

proof fn lemma_floor_bounds(coord_diff: u32, coord_range: nat, voxel_size: u32)
    requires
        TODO,
    ensures
        TODO,
{
    
    assert(coord_diff / voxel_size <= coord_range / voxel_size as nat) by (nonlinear_arith)
        requires
            TODO,
    ;
}

spec fn count_nonzeros_3d(v: Seq<Vec<Vec<u32>>>) -> nat
    decreases v,
{
   TODO
}

spec fn count_nonzeros_2d(v: Seq<Vec<u32>>) -> nat
    decreases v,
{
    TODO
}

spec fn count_nonzeros_1d(v: Seq<u32>) -> nat
    decreases v,
{
    TODO
}


spec fn no_input_overflows(p: Seq<Point>) -> bool {
    
    
    
    TODO
}


#[verifier::loop_isolation(false)]
#[allow(unused)]
fn downsample(p: Vec<Point>, voxel_size: u32) -> (result: Vec<Point>)
    requires
        TODO
    
    
    
{
    let (x_max_pt, y_max_pt, z_max_pt) = (
        array_max_by_x(&p),
        array_max_by_y(&p),
        array_max_by_z(&p),
    );
    let (x_min_pt, y_min_pt, z_min_pt) = (
        array_min_by_x(&p),
        array_min_by_y(&p),
        array_min_by_z(&p),
    );

    let (x_max, y_max, z_max) = (x_max_pt.x, y_max_pt.y, z_max_pt.z);
    let (x_min, y_min, z_min) = (x_min_pt.x, y_min_pt.y, z_min_pt.z);

    
    
    
    
    
    
    
    
    
    
    let (num_vox_x, num_vox_y, num_vox_z) = (
        abs(x_max as i32 - x_min as i32) / (voxel_size) + 1,
        abs(y_max as i32 - y_min as i32) / (voxel_size) + 1,
        abs(z_max as i32 - z_min as i32) / (voxel_size) + 1,
    );

    let mut voxel_array = three_d_vec_with_capacity(
        num_vox_x as usize,
        num_vox_y as usize,
        num_vox_z as usize,
        Point::default(),
    );

    let mut count_array = three_d_vec_with_capacity(
        num_vox_x as usize,
        num_vox_y as usize,
        num_vox_z as usize,
        0u32,
    );

    
    
    

    
    
    
    
    let ghost mut total_nonzeros: nat = 0;
    for i in 0..p.len()
        invariant
            valid_3d_array_structure(
                voxel_array@,
                num_vox_x as int,
                num_vox_y as int,
                num_vox_z as int,
            ),
            valid_3d_array_structure(
                count_array@,
                num_vox_x as int,
                num_vox_y as int,
                num_vox_z as int,
            ),
            total_nonzeros <= i,
            forall|vi: int, vj: int, vk: int|
                #![trigger voxel_array@[vi][vj][vk]]
                0 <= vi < num_vox_x && 0 <= vj < num_vox_y && 0 <= vk < num_vox_z ==> {
                    &&& voxel_array@[vi][vj][vk].x <= i * u16::MAX
                    &&& voxel_array@[vi][vj][vk].y <= i * u16::MAX
                    &&& voxel_array@[vi][vj][vk].z <= i * u16::MAX
                    &&& count_array@[vi][vj][vk] <= i
                },
    {
        let x_diff = (p[i].x - x_min) as u32;
        let y_diff = (p[i].y - y_min) as u32;
        let z_diff = (p[i].z - z_min) as u32;

        let (x_floored, y_floored, z_floored) = (
            x_diff / voxel_size,
            y_diff / voxel_size,
            z_diff / voxel_size,
        );

        proof {
            
            
            
            
            
            let x_range = vstd::math::abs(x_max - x_min);
            lemma_floor_bounds(x_diff, x_range, voxel_size);

            let y_range = vstd::math::abs(y_max - y_min);
            lemma_floor_bounds(y_diff, y_range, voxel_size);

            let z_range = vstd::math::abs(z_max - z_min);
            lemma_floor_bounds(z_diff, z_range, voxel_size);
        }

        let current_pt = voxel_array[x_floored as usize][y_floored as usize][z_floored as usize];
        let current_count = count_array[x_floored as usize][y_floored as usize][z_floored as usize];

        
        
        safe_set_3d(
            &mut voxel_array,
            x_floored as usize,
            y_floored as usize,
            z_floored as usize,
            current_pt.add(p[i]),
        );

        proof {
            total_nonzeros =
            total_nonzeros + if current_count == 0 {
                1nat
            } else {
                0nat
            };
        }

        safe_set_3d(
            &mut count_array,
            x_floored as usize,
            y_floored as usize,
            z_floored as usize,
            current_count + 1,
        );
    }

    assert(total_nonzeros <= p.len());
    
    let mut pd = Vec::new();
    let ghost mut line_executions = 0nat;
    for i in 0..num_vox_x as usize
        invariant
            pd.len() == line_executions,
    {
        for j in 0..num_vox_y as usize
            invariant
                pd.len() == line_executions,
        {
            for k in 0..num_vox_z as usize
                invariant
                    pd.len() == line_executions,
            {
                if count_array[i][j][k] != 0 {
                    proof { line_executions = line_executions + 1 };
                    pd.push(voxel_array[i][j][k].div_by(count_array[i][j][k]));
                }
            }
        }
    }
    
    assert(pd.len() == line_executions);

    
    
    
    pd
}

} 
