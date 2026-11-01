import C2CompND.HGrad
import C2CompND.HHess
/-- The operator `eq:maineq`: `L u = -Tr (a (X u) * XX u)`. -/
noncomputable def SubellipticOp {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -(a (HGrad σ u x) * HHess σ u x).trace
