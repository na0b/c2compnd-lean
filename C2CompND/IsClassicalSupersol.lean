import C2CompND.HGrad
import C2CompND.SubellipticOp
/-- `def:classical`, super-solution half: `L u >= 0` at every point of `U` where the
horizontal gradient does not vanish. -/
def IsClassicalSupersol {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ U, HGrad σ u x ≠ 0 → 0 ≤ SubellipticOp σ a u x
