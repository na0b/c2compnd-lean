import C2CompND.Preamble
/-- One-dimensional second-derivative necessary condition at a local maximum.
Not available in Mathlib: `DerivativeTest.lean` only has the sufficient direction. -/
theorem SecondDerivTestOneDim {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContDiffAt ℝ 2 g t₀) (hmax : IsLocalMax g t₀) :
    deriv (deriv g) t₀ ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hd : deriv g t₀ = 0 := hmax.deriv_eq_zero
  have hmin : IsLocalMin g t₀ :=
    isLocalMin_of_deriv_deriv_pos hpos hd hg.continuousAt
  have heq : g =ᶠ[nhds t₀] fun _ => g t₀ := by
    filter_upwards [hmax, hmin] with x hx1 hx2
    exact le_antisymm hx1 hx2
  have h1 : deriv g =ᶠ[nhds t₀] fun _ => (0 : ℝ) := by
    filter_upwards [heq.eventuallyEq_nhds] with x hx
    rw [hx.deriv_eq]
    simp
  have h2 : deriv (deriv g) t₀ = 0 := by
    rw [h1.deriv_eq]; simp
  rw [h2] at hpos
  exact lt_irrefl 0 hpos
