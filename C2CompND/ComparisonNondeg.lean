import C2CompND.LocalMaxOpIneq
import C2CompND.PerturbationIdentity
import C2CompND.MaxSetStability
import C2CompND.HGradHHessComp
import C2CompND.IsClassicalSubsol
import C2CompND.IsClassicalSupersol
import C2CompND.HormanderRank
import C2CompND.HGrad
import C2CompND.EllipticityFn
import C2CompND.HGradContinuousOn
import C2CompND.QuadraticPerturbDeriv
open scoped ContDiff
/-- Theorem `thm:comp`, equivalently Proposition `lem:comp0`: the comparison principle for
smooth sub- and super-solutions in the non-degenerate case. -/
theorem ComparisonNondeg {n m : ℕ}
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
    (hnd : ∀ x ∈ Ω, IsMaxOn (u - v) Ω x → HGrad σ u x ≠ 0)
    (hbd : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨xb, hxbΩ, hxb⟩ := hcon
  -- `K = closure Ω` is a non-empty compact set and `f = u - v` is continuous on it
  have hKc : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hKne : (closure Ω).Nonempty := ⟨xb, subset_closure hxbΩ⟩
  have hfc : ContinuousOn (u - v) (closure Ω) := huc.sub hvc
  obtain ⟨x₀, hx₀K, hx₀max⟩ := hKc.exists_isMaxOn hKne hfc
  have hM₀ : 0 < (u - v) x₀ := by
    have h1 : (u - v) xb ≤ (u - v) x₀ := hx₀max (subset_closure hxbΩ)
    have h2 : 0 < (u - v) xb := by simp only [Pi.sub_apply]; linarith
    linarith
  -- Step 2: `U` is open
  have hgc : ContinuousOn (HGrad σ u) Ω := HGradContinuousOn σ u Ω hσ hΩo hu
  have hsetopen : IsOpen {ξ : Fin m → ℝ | ξ ≠ 0} := by
    have he : {ξ : Fin m → ℝ | ξ ≠ 0} = ({(0 : Fin m → ℝ)} : Set (Fin m → ℝ))ᶜ := by
      ext ξ; simp
    rw [he]
    exact isOpen_compl_singleton
  have hUo : IsOpen (Ω ∩ HGrad σ u ⁻¹' {ξ : Fin m → ℝ | ξ ≠ 0}) :=
    hgc.isOpen_inter_preimage hΩo hsetopen
  -- Step 1: every maximum point of `f` on `K` lies in `U`
  have hstep1 : ∀ x ∈ closure Ω, IsMaxOn (u - v) (closure Ω) x →
      x ∈ Ω ∩ HGrad σ u ⁻¹' {ξ : Fin m → ℝ | ξ ≠ 0} := by
    intro x hxK hxmax
    have hpos : 0 < (u - v) x := lt_of_lt_of_le hM₀ (hxmax hx₀K)
    have hxΩ : x ∈ Ω := by
      rcases (closure_eq_interior_union_frontier Ω).subset hxK with hint | hfr
      · rwa [hΩo.interior_eq] at hint
      · exfalso
        have hle := hbd x hfr
        simp only [Pi.sub_apply] at hpos
        linarith
    have hmaxΩ : IsMaxOn (u - v) Ω x := fun y hy => hxmax (subset_closure hy)
    exact ⟨hxΩ, hnd x hxΩ hmaxΩ⟩
  -- Step 3: `u₀ = min_K u` and `u₁ = max_K u`
  obtain ⟨p₀, hp₀K, hp₀⟩ := hKc.exists_isMinOn hKne huc
  obtain ⟨p₁, hp₁K, hp₁⟩ := hKc.exists_isMaxOn hKne huc
  -- Step 4: the stability radius, then the choice of `λ`
  obtain ⟨ε, hε, hstab⟩ := MaxSetStability hKc hKne hfc hUo hstep1
  obtain ⟨lam, hlam, hlamb⟩ : ∃ lam : ℝ, 0 < lam ∧ lam * (u p₁ - u p₀) ^ 2 ≤ ε := by
    by_cases hEq : u p₁ = u p₀
    · exact ⟨1, one_pos, by simp [hEq, hε.le]⟩
    · have h2 : (0:ℝ) < (u p₁ - u p₀) ^ 2 := by
        have : u p₁ - u p₀ ≠ 0 := sub_ne_zero.mpr hEq
        positivity
      refine ⟨ε / (u p₁ - u p₀) ^ 2, div_pos hε h2, ?_⟩
      have hcancel : ε / (u p₁ - u p₀) ^ 2 * (u p₁ - u p₀) ^ 2 = ε := by
        field_simp
      linarith [hcancel]
  -- the perturbation `h_λ`, kept opaque apart from the four facts we need
  obtain ⟨H, hHC2, hH1, hH2, hHval⟩ : ∃ H : ℝ → ℝ, ContDiff ℝ 2 H ∧
      (∀ s, deriv H s = 1 + 2 * lam * (s - u p₀)) ∧
      (∀ s, deriv (deriv H) s = 2 * lam) ∧
      (∀ s, H s = s + lam * (s - u p₀) ^ 2) :=
    ⟨fun s => s + lam * (s - u p₀) ^ 2, (QuadraticPerturbDeriv lam (u p₀)).1,
      (QuadraticPerturbDeriv lam (u p₀)).2.1, (QuadraticPerturbDeriv lam (u p₀)).2.2,
      fun _ => rfl⟩
  -- the perturbed difference `g = u_λ - v` is uniformly `ε`-close to `f` on `K`
  have hgf : ∀ x ∈ closure Ω, |(H ∘ u - v) x - (u - v) x| ≤ ε := by
    intro x hxK
    have hlo : u p₀ ≤ u x := hp₀ hxK
    have hhi : u x ≤ u p₁ := hp₁ hxK
    have hval : (H ∘ u - v) x - (u - v) x = lam * (u x - u p₀) ^ 2 := by
      simp only [Pi.sub_apply, Function.comp_apply, hHval]
      ring
    rw [hval, abs_of_nonneg (by positivity)]
    have hmono : (u x - u p₀) ^ 2 ≤ (u p₁ - u p₀) ^ 2 := by
      apply sq_le_sq' <;> linarith
    calc lam * (u x - u p₀) ^ 2 ≤ lam * (u p₁ - u p₀) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono hlam.le
      _ ≤ ε := hlamb
  have hgc2 : ContinuousOn (H ∘ u - v) (closure Ω) :=
    (hHC2.continuous.comp_continuousOn huc).sub hvc
  obtain ⟨xl, hxlK, hxlmax⟩ := hKc.exists_isMaxOn hKne hgc2
  have hxlU := hstab (H ∘ u - v) hgf xl hxlK hxlmax
  have hxlΩ : xl ∈ Ω := hxlU.1
  have hxlne : HGrad σ u xl ≠ 0 := hxlU.2
  -- Step 5: `xl` is a local maximum point of `u_λ - v`
  have hlocmax : IsLocalMax (H ∘ u - v) xl := by
    filter_upwards [hΩo.mem_nhds hxlΩ] with y hy
    exact hxlmax (subset_closure hy)
  -- Step 6: `L u_λ (xl) ≥ 0`
  have huLOm : ContDiffOn ℝ 2 (H ∘ u) Ω := hHC2.comp_contDiffOn hu
  have ht1 : (1:ℝ) ≤ deriv H (u xl) := by
    rw [hH1]
    have : u p₀ ≤ u xl := hp₀ hxlK
    nlinarith [hlam.le]
  have htpos : 0 < deriv H (u xl) := lt_of_lt_of_le one_pos ht1
  have hcd := HGradHHessComp σ H u xl hHC2 (hu.contDiffAt (hΩo.mem_nhds hxlΩ))
      (fun i => (hσ i).contDiffAt.of_le (by norm_num))
  have hXuLne : HGrad σ (H ∘ u) xl ≠ 0 := by
    rw [hcd.1]
    exact smul_ne_zero (ne_of_gt htpos) hxlne
  obtain ⟨hXv, -, hLle⟩ :=
    LocalMaxOpIneq σ a Ω (H ∘ u) v xl hσ hpsd hΩo hxlΩ huLOm hv hlocmax hXuLne
  have hLvnn : 0 ≤ SubellipticOp σ a v xl :=
    hsup xl hxlΩ (by rw [hXv]; exact hXuLne)
  have hstep6 : 0 ≤ SubellipticOp σ a (H ∘ u) xl := le_trans hLvnn hLle
  -- Step 7: `L u_λ (xl) < 0`
  have hLu : SubellipticOp σ a u xl ≤ 0 := hsub xl hxlΩ hxlne
  have hPI := PerturbationIdentity σ a β H Ω u xl hσ hhom hΩo hxlΩ hHC2 hu hxlne htpos
  rw [hH2] at hPI
  have hEpos : 0 < EllipticityFn a (HGrad σ u xl) := hell _ hxlne
  have htb : 0 < deriv H (u xl) ^ β := Real.rpow_pos_of_pos htpos β
  have hbr : 0 < 2 * lam * EllipticityFn a (HGrad σ u xl)
      - deriv H (u xl) * SubellipticOp σ a u xl := by
    have h1 : 0 < 2 * lam * EllipticityFn a (HGrad σ u xl) := by positivity
    have h2 : 0 ≤ deriv H (u xl) * (-(SubellipticOp σ a u xl)) :=
      mul_nonneg htpos.le (neg_nonneg.mpr hLu)
    nlinarith [h1, h2]
  have hstep7 : SubellipticOp σ a (H ∘ u) xl < 0 := by
    rw [hPI]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr htb) hbr
  linarith [hstep6, hstep7]
