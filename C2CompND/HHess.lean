import C2CompND.Preamble
/-- The horizontal second derivative matrix `XX u = (X_j X_i u)_{i,j}` of Section 2.1:
entry `(i, j)` is `X_j X_i u`. Not symmetric in general. -/
noncomputable def HHess {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => fderiv ℝ (fun y => fderiv ℝ u y (σ i y)) x (σ j x)
