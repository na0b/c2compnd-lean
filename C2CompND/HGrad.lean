import C2CompND.Preamble
/-- The horizontal (sub-elliptic) gradient `X u = (X_1 u, ..., X_m u)` of Section 2.1,
for `X_i = sigma^i(x) . grad`. -/
noncomputable def HGrad {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Fin m → ℝ :=
  fun i => fderiv ℝ u x (σ i x)
