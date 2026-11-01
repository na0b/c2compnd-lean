import C2CompND.CorNocritComparison
open scoped ContDiff
/-- Corollary `cor:nocrit`, uniqueness assertion: a solution without horizontal critical
points coincides on the closure with any solution having the same boundary values. -/
theorem CorNocritUniqueness {n m : ℕ}
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
    (hsubu : IsClassicalSubsol σ a u Ω) (hsupu : IsClassicalSupersol σ a u Ω)
    (hsubv : IsClassicalSubsol σ a v Ω) (hsupv : IsClassicalSupersol σ a v Ω)
    (hvnc : ∀ x ∈ Ω, HGrad σ v x ≠ 0)
    (hbd : ∀ x ∈ frontier Ω, u x = v x) :
    ∀ x ∈ closure Ω, u x = v x := by
  -- Step 1: `u <= v` in `Omega`, with `u` the sub-solution and `v` the super-solution.
  -- For that role assignment `hvnc` is the hypothesis on the super-solution, the LEFT disjunct.
  have hstep1 : ∀ x ∈ Ω, u x ≤ v x :=
    CorNocritComparison σ a β Ω u v hσ hhor ha hsymm hpsd hell hhom hΩo hΩb hu hv huc hvc
      hsubu hsupv (Or.inl hvnc) (fun x hx => le_of_eq (hbd x hx))
  -- Step 2: `v <= u` in `Omega`, with the roles exchanged.  The disjunction now reads
  -- `(X u != 0) \/ (X v != 0)`, so the same `hvnc` is the RIGHT disjunct.
  have hstep2 : ∀ x ∈ Ω, v x ≤ u x :=
    CorNocritComparison σ a β Ω v u hσ hhor ha hsymm hpsd hell hhom hΩo hΩb hv hu hvc huc
      hsubv hsupu (Or.inr hvnc) (fun x hx => le_of_eq (hbd x hx).symm)
  -- Step 3: extend `u = v` from `Omega` to `closure Omega`.
  intro x hx
  rcases (closure_eq_interior_union_frontier Ω).subset hx with hint | hfr
  · rw [hΩo.interior_eq] at hint
    exact le_antisymm (hstep1 x hint) (hstep2 x hint)
  · exact hbd x hfr
