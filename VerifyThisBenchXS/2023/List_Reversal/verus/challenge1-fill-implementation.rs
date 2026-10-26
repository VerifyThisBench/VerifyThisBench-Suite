use vstd::prelude::*;
fn main() {}
verus! {

struct Cell {
    #[allow(unused)]
    value: i32,
    next: Option<Box<Cell>>,
}

spec fn cell_len(cell: Option<Cell>) -> nat
    decreases cell,
{
    match cell {
        Some(c) => 1 + cell_len(unbox_ptr(c.next)),
        None => 0,
    }
}

spec fn unbox_ptr(cell: Option<Box<Cell>>) -> Option<Cell> {
    match cell {
        Some(c) => Some(*c),
        None => None,
    }
}

spec fn box_ptr(c: Option<Cell>) -> Option<Box<Cell>> {
    match c {
        Some(mut inner) => { Some(Box::new(inner)) },
        None => None,
    }
}



spec fn reversed(cell: Option<Cell>, remaining: Option<Box<Cell>>) -> Option<Cell>
    decreases remaining,
{
    TODO
}

fn list_reversal_helper(
    mut head: Option<Box<Cell>>,
    Ghost(original_head): Ghost<Option<Box<Cell>>>,
) -> (new_ptr: Option<Box<Cell>>)
    requires
        original_head == head,
    ensures
        
        
        
        ({ reversed(None, original_head) =~= unbox_ptr(new_ptr) }),
{
    TODO
}


#[allow(unused)]
fn list_reversal(head: Option<Box<Cell>>) -> (new_ptr: Option<Box<Cell>>)
    ensures
        reversed(None, head) =~= unbox_ptr(new_ptr),
{
    TODO
}

} 
