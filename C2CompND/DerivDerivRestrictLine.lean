import C2CompND.Preamble
/-- The second derivative at `0` of the restriction `t |-> f (x0 + t w)` of `f` to the line
through `x0` in direction `w` is `D^2 f(x0) [w, w]`. -/
theorem DerivDerivRestrictLine {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x₀)
    (w : EuclideanSpace ℝ (Fin n)) :
    deriv (deriv fun t : ℝ => f (x₀ + t • w)) 0 = fderiv ℝ (fderiv ℝ f) x₀ w w := by
  have hzero : x₀ + (0 : ℝ) • w = x₀ := by simp
  have hγd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x₀ + s • w) w t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x₀
  have hγcd : ContDiff ℝ 2 (fun t : ℝ => x₀ + t • w) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hten : Filter.Tendsto (fun t : ℝ => x₀ + t • w) (nhds 0) (nhds x₀) := by
    have h := hγcd.continuous.tendsto (0 : ℝ)
    rwa [hzero] at h
  -- the first derivative of the restriction, on a neighbourhood of `0`
  have hevt : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 2 f (x₀ + t • w) :=
    hten.eventually (hf.eventually (by norm_num))
  have heq : deriv (fun t : ℝ => f (x₀ + t • w))
      =ᶠ[nhds 0] fun t : ℝ => fderiv ℝ f (x₀ + t • w) w := by
    filter_upwards [hevt] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hγd t)).deriv
  -- differentiate that formula once more at `0`
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x₀) (x₀ + (0 : ℝ) • w) := by
    rw [hzero]
    exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ f (x₀ + t • w))
      (fderiv ℝ (fderiv ℝ f) x₀ w) 0 := hfd.comp_hasDerivAt (0 : ℝ) (hγd 0)
  have hc2 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x₀ + t • w) w)
      (fderiv ℝ (fderiv ℝ f) x₀ w w) 0 := by
    simpa using hc.clm_apply (hasDerivAt_const (0 : ℝ) w)
  rw [heq.deriv_eq]
  exact hc2.deriv
