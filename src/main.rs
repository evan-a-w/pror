use pror::cdcl::*;

pub fn main() {
    let res = State::<FirstSetConfig>::solve(vec![vec![1]]);
    println! {"res: {:?}", res};
}
