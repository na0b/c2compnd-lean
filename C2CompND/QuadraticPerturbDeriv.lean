import C2CompND.Preamble
/-- The perturbation calculus for the quadratic `h_lambda (s) = s + lambda (s - u_0) ^ 2` of
the proof of Proposition `lem:comp0`: it is `C^2`, with `h' (s) = 1 + 2 lambda (s - u_0)` and
`h'' (s) = 2 lambda`. -/
theorem QuadraticPerturbDeriv (lam u₀ : ℝ) :
    ContDiff ℝ 2 (fun s : ℝ => s + lam * (s - u₀) ^ 2)
      ∧ (∀ s : ℝ, deriv (fun r : ℝ => r + lam * (r - u₀) ^ 2) s = 1 + 2 * lam * (s - u₀))
      ∧ (∀ s : ℝ, deriv (deriv (fun r : ℝ => r + lam * (r - u₀) ^ 2)) s = 2 * lam) := by
  have hsub : ∀ s : ℝ, HasDerivAt (fun r : ℝ => r - u₀) 1 s :=
    fun s => (hasDerivAt_id s).sub_const u₀
  have hsq : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (r - u₀) ^ 2) (2 * (s - u₀)) s := by
    intro s
    have hm : HasDerivAt (fun r : ℝ => (r - u₀) * (r - u₀))
        (1 * (s - u₀) + (s - u₀) * 1) s := (hsub s).mul (hsub s)
    have efun : (fun r : ℝ => (r - u₀) * (r - u₀)) = fun r : ℝ => (r - u₀) ^ 2 := by
      funext r; ring
    have eval : 1 * (s - u₀) + (s - u₀) * 1 = 2 * (s - u₀) := by ring
    rw [efun, eval] at hm
    exact hm
  have hd : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => r + lam * (r - u₀) ^ 2) (1 + lam * (2 * (s - u₀))) s :=
    fun s => (hasDerivAt_id s).add ((hsq s).const_mul lam)
  have hd' : ∀ s : ℝ,
      HasDerivAt (fun r : ℝ => r + lam * (r - u₀) ^ 2) (1 + 2 * lam * (s - u₀)) s := by
    intro s
    have e : 1 + lam * (2 * (s - u₀)) = 1 + 2 * lam * (s - u₀) := by ring
    exact e ▸ hd s
  have hderiv : deriv (fun r : ℝ => r + lam * (r - u₀) ^ 2)
      = fun s : ℝ => 1 + 2 * lam * (s - u₀) := funext fun s => (hd' s).deriv
  refine ⟨by fun_prop, fun s => (hd' s).deriv, fun s => ?_⟩
  have h3 : HasDerivAt (fun r : ℝ => 1 + 2 * lam * (r - u₀)) (2 * lam * 1) s :=
    ((hsub s).const_mul (2 * lam)).const_add 1
  rw [hderiv, h3.deriv]
  ring
