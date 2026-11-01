import C2CompND.HHessEntryFormula
import C2CompND.HGrad
import C2CompND.SndFDerivCompScalar
open Matrix
/-- The two chain-rule identities opening the proof of `lem:tech`:
`X (h . w) = h'(w) X w` and `XX (h . w) = h'(w) XX w + h''(w) (X w) tensor (X w)`. -/
theorem HGradHHessComp {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (h : ℝ → ℝ) (w : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hh : ContDiff ℝ 2 h) (hw : ContDiffAt ℝ 2 w x)
    (hσ : ∀ i, ContDiffAt ℝ 1 (σ i) x) :
    HGrad σ (h ∘ w) x = deriv h (w x) • HGrad σ w x
      ∧ HHess σ (h ∘ w) x
          = deriv h (w x) • HHess σ w x
            + deriv (deriv h) (w x) • Matrix.vecMulVec (HGrad σ w x) (HGrad σ w x) := by
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hcw : ContDiffAt ℝ 2 (h ∘ w) x := hh.contDiffAt.comp x hw
  have hwd : DifferentiableAt ℝ w x := hw.differentiableAt (by norm_num)
  -- `.tex` equation (1), pointwise wherever `w` is differentiable
  have hone : ∀ y, DifferentiableAt ℝ w y →
      HasFDerivAt (h ∘ w) (deriv h (w y) • fderiv ℝ w y) y := fun y hy =>
    HasDerivAt.comp_hasFDerivAt y (hhd (w y)).hasDerivAt hy.hasFDerivAt
  refine ⟨?_, ?_⟩
  -- Step 1: the first identity
  · funext i
    simp only [HGrad, (hone x hwd).fderiv, Pi.smul_apply, _root_.smul_apply, smul_eq_mul]
  -- Step 3: the second identity, entrywise
  · ext i j
    rw [HHessEntryFormula σ (h ∘ w) x i j hcw (hσ i),
      SndFDerivCompScalar hh hw (σ j x) (σ i x), (hone x hwd).fderiv]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, HGrad,
      _root_.smul_apply, smul_eq_mul, HHessEntryFormula σ w x i j hw (hσ i)]
    ring
