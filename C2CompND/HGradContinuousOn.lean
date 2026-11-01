import C2CompND.HGrad
open scoped ContDiff
/-- The paper's "by assumption and continuity of `X u`" at the start of the proof of
Proposition `lem:comp0`: the horizontal gradient of a `C^2` function is continuous. -/
theorem HGradContinuousOn {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hσ : ∀ i, ContDiff ℝ ∞ (σ i)) (hΩo : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) :
    ContinuousOn (HGrad σ u) Ω := by
  have hfd : ContinuousOn (fderiv ℝ u) Ω :=
    hu.continuousOn_fderiv_of_isOpen hΩo (by norm_num)
  rw [continuousOn_pi]
  intro i
  exact hfd.clm_apply (hσ i).continuous.continuousOn
