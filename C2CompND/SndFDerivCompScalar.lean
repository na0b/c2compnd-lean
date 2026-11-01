import C2CompND.Preamble
import Mathlib.Analysis.Calculus.ContDiff.Deriv
/-- Second-order chain rule for a scalar outer function:
`D^2 (h . w) [z1, z2] = h''(w) Dw[z1] Dw[z2] + h'(w) D^2 w [z1, z2]`. -/
theorem SndFDerivCompScalar {n : ℕ} {h : ℝ → ℝ} {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hh : ContDiff ℝ 2 h) (hw : ContDiffAt ℝ 2 w x)
    (z₁ z₂ : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (h ∘ w)) x z₁ z₂
      = deriv (deriv h) (w x) * fderiv ℝ w x z₁ * fderiv ℝ w x z₂
        + deriv h (w x) * fderiv ℝ (fderiv ℝ w) x z₁ z₂ := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hwd : DifferentiableAt ℝ w x := hw.differentiableAt (by norm_num)
  -- first-order chain rule, pointwise wherever `w` is differentiable
  have hone : ∀ y, DifferentiableAt ℝ w y →
      HasFDerivAt (h ∘ w) (deriv h (w y) • fderiv ℝ w y) y := fun y hy =>
    HasDerivAt.comp_hasFDerivAt y (hhd (w y)).hasDerivAt hy.hasFDerivAt
  have hevw : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 w y := hw.eventually (by norm_num)
  have hevEq : fderiv ℝ (h ∘ w)
      =ᶠ[nhds x] (fun y => deriv h (w y)) • (fun y => fderiv ℝ w y) := by
    filter_upwards [hevw] with y hy
    simpa using (hone y (hy.differentiableAt (by norm_num))).fderiv
  -- the two factors of that product are differentiable at `x`
  have hc' : HasFDerivAt (fun y => deriv h (w y))
      (deriv (deriv h) (w x) • fderiv ℝ w x) x :=
    HasDerivAt.comp_hasFDerivAt (h₂ := deriv h) x
      (ContDiff.differentiable_deriv_two hh (w x)).hasDerivAt hwd.hasFDerivAt
  have hf' : HasFDerivAt (fun y => fderiv ℝ w y) (fderiv ℝ (fderiv ℝ w) x) x :=
    ((hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  rw [hevEq.fderiv_eq, (hc'.smul hf').fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring
