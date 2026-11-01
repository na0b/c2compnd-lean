import C2CompND.HHess
open Matrix
/-- The symmetrized horizontal second derivative `XXs u = (1/2) (XX u + (XX u)^T)`
of Section 2.1. -/
noncomputable def HHessSym {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 / 2 : ℝ) • (HHess σ u x + (HHess σ u x)ᵀ)
