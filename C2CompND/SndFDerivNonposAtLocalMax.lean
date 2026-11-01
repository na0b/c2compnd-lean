import C2CompND.DerivDerivRestrictLine
import C2CompND.SecondDerivTestOneDim
/-- Second-derivative necessary condition at a local maximum, in the direction `w`. -/
theorem SndFDerivNonposAtLocalMax {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hf : ContDiffAt ℝ 2 f x₀)
    (hmax : IsLocalMax f x₀) (w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ f) x₀ w w ≤ 0 := by
  have hzero : x₀ + (0 : ℝ) • w = x₀ := by simp
  have hγcd : ContDiff ℝ 2 (fun t : ℝ => x₀ + t • w) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  -- Step 1
  have h1 : ContDiffAt ℝ 2 (fun t : ℝ => f (x₀ + t • w)) 0 := by
    have hf' : ContDiffAt ℝ 2 f (x₀ + (0 : ℝ) • w) := by rw [hzero]; exact hf
    exact hf'.comp (0 : ℝ) hγcd.contDiffAt
  -- Step 2
  have hten : Filter.Tendsto (fun t : ℝ => x₀ + t • w) (nhds 0) (nhds x₀) := by
    have h := hγcd.continuous.tendsto (0 : ℝ)
    rwa [hzero] at h
  have h2 : IsLocalMax (fun t : ℝ => f (x₀ + t • w)) 0 := by
    have hmax' : IsMaxFilter f (nhds x₀) (x₀ + (0 : ℝ) • w) := by rw [hzero]; exact hmax
    exact IsMaxFilter.comp_tendsto (g := fun t : ℝ => x₀ + t • w) (b := (0 : ℝ)) hmax' hten
  -- Step 3
  have hle := SecondDerivTestOneDim h1 h2
  rwa [DerivDerivRestrictLine hf w] at hle
