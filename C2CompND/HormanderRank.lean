import C2CompND.HorFamily
/-- The Hoermander rank condition `eq:horcond`: at every point the evaluations of the
iterated commutators of the frame span the whole tangent space. -/
def HormanderRank {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    Submodule.span ℝ {v : EuclideanSpace ℝ (Fin n) | ∃ V, HorFamily σ V ∧ V x = v} = ⊤
