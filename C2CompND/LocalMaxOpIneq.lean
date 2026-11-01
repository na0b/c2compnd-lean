import C2CompND.FDerivEqAtLocalMaxSub
import C2CompND.HGradEqAtLocalMax
import C2CompND.SndFDerivLeAtLocalMaxSub
import C2CompND.HGradHHessComparison
import C2CompND.TraceMonotone
import C2CompND.TraceMulSymmetrizeEq
import C2CompND.SubellipticOp
open scoped ContDiff
/-- First assertion of `lem:vweak`: at an interior local maximum of `u - v` with
`X u != 0` the horizontal gradients agree, `XXs u <= XXs v`, and `L v <= L u`. -/
theorem LocalMaxOpIneq {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hσ : ∀ i, ContDiff ℝ ∞ (σ i))
    (hpsd : ∀ ξ ≠ 0, (a ξ).PosSemidef)
    (hUo : IsOpen U) (hx₀ : x₀ ∈ U)
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hmax : IsLocalMax (u - v) x₀) (hne : HGrad σ u x₀ ≠ 0) :
    HGrad σ v x₀ = HGrad σ u x₀
      ∧ (HHessSym σ v x₀ - HHessSym σ u x₀).PosSemidef
      ∧ SubellipticOp σ a v x₀ ≤ SubellipticOp σ a u x₀ := by
  -- lift the regularity hypotheses to the point x₀
  have hu' : ContDiffAt ℝ 2 u x₀ := hu.contDiffAt (hUo.mem_nhds hx₀)
  have hv' : ContDiffAt ℝ 2 v x₀ := hv.contDiffAt (hUo.mem_nhds hx₀)
  have hσ' : ∀ i, ContDiffAt ℝ 1 (σ i) x₀ := fun i => (hσ i).contDiffAt.of_le (by norm_num)
  have hud : DifferentiableAt ℝ u x₀ := hu'.differentiableAt (by norm_num)
  have hvd : DifferentiableAt ℝ v x₀ := hv'.differentiableAt (by norm_num)
  -- Step 1
  have hstep1 : HGrad σ v x₀ = HGrad σ u x₀ :=
    (HGradEqAtLocalMax σ u v x₀ hud hvd hmax).symm
  -- Step 2
  have hgrad : fderiv ℝ u x₀ = fderiv ℝ v x₀ := FDerivEqAtLocalMaxSub hud hvd hmax
  -- Step 3
  have hhess := SndFDerivLeAtLocalMaxSub hUo hx₀ hu hv hmax
  -- Step 4
  have hstep4 : (HHessSym σ v x₀ - HHessSym σ u x₀).PosSemidef :=
    (HGradHHessComparison σ u v x₀ hu' hv' hσ' hgrad hhess).2
  -- Step 5
  have hA : (a (HGrad σ u x₀)).PosSemidef := hpsd _ hne
  have hstep5 : (a (HGrad σ u x₀) * HHessSym σ u x₀).trace
      ≤ (a (HGrad σ u x₀) * HHessSym σ v x₀).trace := TraceMonotone hA hstep4
  -- Step 6: symmetrization does not change the trace against a symmetric matrix
  have hAsymm : (a (HGrad σ u x₀)).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hSu : (a (HGrad σ u x₀) * HHessSym σ u x₀).trace
      = (a (HGrad σ u x₀) * HHess σ u x₀).trace := by
    simp only [HHessSym]
    exact TraceMulSymmetrizeEq hAsymm (HHess σ u x₀)
  have hSv : (a (HGrad σ u x₀) * HHessSym σ v x₀).trace
      = (a (HGrad σ u x₀) * HHess σ v x₀).trace := by
    simp only [HHessSym]
    exact TraceMulSymmetrizeEq hAsymm (HHess σ v x₀)
  -- Step 7
  refine ⟨hstep1, hstep4, ?_⟩
  simp only [SubellipticOp]
  rw [hstep1]
  linarith [hstep5, hSu, hSv]
