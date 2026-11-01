import C2CompND.HHess
/-- `eq:sigrad` / `eq:Mxz` entrywise: `X_j X_i u = D^2 u [sigma^j, sigma^i] + Du [D sigma^i
sigma^j]`. -/
theorem HHessEntryFormula {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin m)
    (hu : ContDiffAt ℝ 2 u x) (hσ : ContDiffAt ℝ 1 (σ i) x) :
    HHess σ u x i j
      = fderiv ℝ (fderiv ℝ u) x (σ j x) (σ i x)
        + fderiv ℝ u x (fderiv ℝ (σ i) x (σ j x)) := by
  have hu' : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hσ' : DifferentiableAt ℝ (σ i) x := hσ.differentiableAt (by norm_num)
  simp only [HHess, Matrix.of_apply]
  rw [fderiv_clm_apply hu' hσ']
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring
