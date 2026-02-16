// Git operations as vertex algebra
// Every git command = composition of vertex operators

use crate::vertex_ops::VertexOp;

// git commit = S(K(I(message)))
pub fn commit(message: &str) -> Vec<VertexOp> {
    vec![VertexOp::S, VertexOp::K, VertexOp::I]
}

// git merge = Y(B(C(branch1, branch2)))
pub fn merge(branch1: &str, branch2: &str) -> Vec<VertexOp> {
    vec![VertexOp::Y, VertexOp::B, VertexOp::C]
}

// git rebase = W(T(base))
pub fn rebase(base: &str) -> Vec<VertexOp> {
    vec![VertexOp::W, VertexOp::T]
}

// git log = Y(A(E(count)))
pub fn log(count: usize) -> Vec<VertexOp> {
    vec![VertexOp::Y, VertexOp::A, VertexOp::E]
}

// git diff = C(W(file1, file2))
pub fn diff(file1: &str, file2: &str) -> Vec<VertexOp> {
    vec![VertexOp::C, VertexOp::W]
}

// git branch = B(K(name))
pub fn branch(name: &str) -> Vec<VertexOp> {
    vec![VertexOp::B, VertexOp::K]
}

// git checkout = L(U(ref))
pub fn checkout(ref_name: &str) -> Vec<VertexOp> {
    vec![VertexOp::L, VertexOp::U]
}

// git push = A(E(M(remote)))
pub fn push(remote: &str) -> Vec<VertexOp> {
    vec![VertexOp::A, VertexOp::E, VertexOp::M]
}

// git pull = Y(M(E(remote)))
pub fn pull(remote: &str) -> Vec<VertexOp> {
    vec![VertexOp::Y, VertexOp::M, VertexOp::E]
}

// git reset = N(I(ref))
pub fn reset(ref_name: &str) -> Vec<VertexOp> {
    vec![VertexOp::N, VertexOp::I]
}

// git stash = F(K(changes))
pub fn stash() -> Vec<VertexOp> {
    vec![VertexOp::F, VertexOp::K]
}

// git cherry-pick = S(C(commit))
pub fn cherry_pick(commit: &str) -> Vec<VertexOp> {
    vec![VertexOp::S, VertexOp::C]
}

// Compose vertex operators (function composition)
pub fn compose(ops: &[VertexOp]) -> u64 {
    ops.iter().fold(1u64, |acc, op| (acc * (*op as u64)) % 71)
}

// Apply FRACTRAN to git operation
pub fn apply_fractran(ops: &[VertexOp], input: u64) -> u64 {
    let mut state = input;
    for op in ops {
        state = (state * (*op as u64)) % 71;
    }
    state
}
