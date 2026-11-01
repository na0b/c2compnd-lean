import C2CompND.Preamble
/-- At a local maximum point of `u - v` the Frechet derivatives of `u` and `v` agree. -/
theorem FDerivEqAtLocalMaxSub {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hu : DifferentiableAt ℝ u x₀) (hv : DifferentiableAt ℝ v x₀)
    (hmax : IsLocalMax (u - v) x₀) : fderiv ℝ u x₀ = fderiv ℝ v x₀ :=
  sub_eq_zero.mp ((fderiv_sub hu hv).symm.trans hmax.fderiv_eq_zero)
