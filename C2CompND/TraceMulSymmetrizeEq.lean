import C2CompND.Preamble
/-- Against a symmetric matrix `A`, symmetrizing the second factor does not change the trace:
`Tr (A ((1/2) (B + B^T))) = Tr (A B)`. This is the matrix fact behind the paper's remark, just
after `eq:maineq`, that the equation may equivalently be written with the symmetrized
sub-elliptic second derivative. -/
theorem TraceMulSymmetrizeEq {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsSymm)
    (B : Matrix (Fin m) (Fin m) ℝ) :
    (A * ((1 / 2 : ℝ) • (B + B.transpose))).trace = (A * B).trace := by
  have ht : (A * B.transpose).trace = (A * B).trace := by
    rw [← Matrix.trace_transpose (A * B.transpose), Matrix.transpose_mul,
      Matrix.transpose_transpose, hA.eq, Matrix.trace_mul_comm]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, ht, smul_eq_mul]
  ring
