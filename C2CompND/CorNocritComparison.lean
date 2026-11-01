import C2CompND.ComparisonNondeg
import C2CompND.HGradEqAtLocalMax
open scoped ContDiff
/-- Corollary `cor:nocrit`, comparison assertion: if `v`, or `u`, has no horizontal critical
point in `Omega`, then `u <= v` in `Omega`. -/
theorem CorNocritComparison {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hσ : ∀ i, ContDiff ℝ ∞ (σ i))
    (hhor : HormanderRank σ)
    (ha : ContinuousOn a {ξ : Fin m → ℝ | ξ ≠ 0})
    (hsymm : ∀ ξ ≠ 0, (a ξ).IsSymm)
    (hpsd : ∀ ξ ≠ 0, (a ξ).PosSemidef)
    (hell : ∀ ξ ≠ 0, 0 < EllipticityFn a ξ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, a (t • ξ) = (t ^ β) • a ξ)
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hsub : IsClassicalSubsol σ a u Ω) (hsup : IsClassicalSupersol σ a v Ω)
    (hnc : (∀ x ∈ Ω, HGrad σ v x ≠ 0) ∨ (∀ x ∈ Ω, HGrad σ u x ≠ 0))
    (hbd : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x := by
  refine ComparisonNondeg σ a β Ω u v hσ hhor ha hsymm hpsd hell hhom hΩo hΩb hu hv huc hvc
    hsub hsup ?_ hbd
  intro x hx hmax
  rcases hnc with hvnc | hunc
  · -- the `v`-alternative: `X u x = X v x` at the interior maximum, by HGradEqAtLocalMax
    have hud : DifferentiableAt ℝ u x :=
      (hu.contDiffAt (hΩo.mem_nhds hx)).differentiableAt (by norm_num)
    have hvd : DifferentiableAt ℝ v x :=
      (hv.contDiffAt (hΩo.mem_nhds hx)).differentiableAt (by norm_num)
    have hloc : IsLocalMax (u - v) x := by
      filter_upwards [hΩo.mem_nhds hx] with y hy
      exact hmax hy
    rw [HGradEqAtLocalMax σ u v x hud hvd hloc]
    exact hvnc x hx
  · -- the `u`-alternative: immediate
    exact hunc x hx
