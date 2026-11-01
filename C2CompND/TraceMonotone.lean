import C2CompND.Preamble
open scoped MatrixOrder
/-- `eq:matmon`: `Tr (A Y) <= Tr (A X)` for `A >= 0` and `Y <= X`. -/
theorem TraceMonotone {m : ℕ} {A X Y : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.PosSemidef) (hXY : (X - Y).PosSemidef) :
    (A * Y).trace ≤ (A * X).trace := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hXY.nonneg
  have key : (0 : ℝ) ≤ (A * (X - Y)).trace := by
    rw [hB, Matrix.star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    exact (hA.mul_mul_conjTranspose_same B).trace_nonneg
  have hsub : (A * X).trace - (A * Y).trace = (A * (X - Y)).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  linarith [key, hsub]
