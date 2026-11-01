import C2CompND.Preamble
/-- Stability of the location of maximizers under uniform perturbation: a compactness-gap
argument replacing the subsequence extraction in the proof of Proposition `lem:comp0`. -/
theorem MaxSetStability {X : Type*} [TopologicalSpace X]
    {K : Set X} {f : X → ℝ} {W : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hf : ContinuousOn f K) (hW : IsOpen W)
    (hmax : ∀ x ∈ K, IsMaxOn f K x → x ∈ W) :
    ∃ ε > 0, ∀ g : X → ℝ, (∀ x ∈ K, |g x - f x| ≤ ε) →
      ∀ x ∈ K, IsMaxOn g K x → x ∈ W := by
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMaxOn hne hf
  by_cases hKW : (K \ W).Nonempty
  · have hcKW : IsCompact (K \ W) := hK.diff hW
    obtain ⟨x₁, hx₁, hx₁max⟩ := hcKW.exists_isMaxOn hKW (hf.mono Set.sdiff_subset)
    have hlt : f x₁ < f x₀ := by
      have hle : f x₁ ≤ f x₀ := hx₀ hx₁.1
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (hmax x₁ hx₁.1 (fun y hy => h ▸ hx₀ hy)) hx₁.2
    refine ⟨(f x₀ - f x₁) / 3, by linarith, fun g hg x hxK hxmax => ?_⟩
    by_contra hxW
    have h1 : f x₀ - (f x₀ - f x₁) / 3 ≤ g x := by
      obtain ⟨hlo, -⟩ := abs_le.mp (hg x₀ hx₀K)
      have hge : g x₀ ≤ g x := hxmax hx₀K
      linarith
    have h2 : g x ≤ f x₁ + (f x₀ - f x₁) / 3 := by
      obtain ⟨-, hhi⟩ := abs_le.mp (hg x hxK)
      have hle : f x ≤ f x₁ := hx₁max (Set.mem_sdiff x |>.mpr ⟨hxK, hxW⟩)
      linarith
    linarith
  · refine ⟨1, one_pos, fun g _ x hxK _ => ?_⟩
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hKW
    exact hKW hxK
