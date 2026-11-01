import C2CompND.SndFDerivNonposAtLocalMax
/-- Second-order half of the sentence opening the proof of `lem:vweak`: at a local maximum of
`u - v` interior to `U` one has `D^2 u(x0) <= D^2 v(x0)`. -/
theorem SndFDerivLeAtLocalMaxSub {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {x₀ : EuclideanSpace ℝ (Fin n)}
    (hUo : IsOpen U) (hx₀ : x₀ ∈ U)
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hmax : IsLocalMax (u - v) x₀) :
    ∀ w : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ u) x₀ w w ≤ fderiv ℝ (fderiv ℝ v) x₀ w w := by
  have hu' : ContDiffAt ℝ 2 u x₀ := hu.contDiffAt (hUo.mem_nhds hx₀)
  have hv' : ContDiffAt ℝ 2 v x₀ := hv.contDiffAt (hUo.mem_nhds hx₀)
  -- the first derivatives subtract on all of `U`, hence near `x₀`
  have hev : fderiv ℝ (u - v) =ᶠ[nhds x₀] fun y => fderiv ℝ u y - fderiv ℝ v y := by
    filter_upwards [hUo.mem_nhds hx₀] with y hy
    exact fderiv_sub ((hu.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by norm_num))
      ((hv.contDiffAt (hUo.mem_nhds hy)).differentiableAt (by norm_num))
  -- so the second derivatives subtract at `x₀`
  have hsplit : fderiv ℝ (fderiv ℝ (u - v)) x₀
      = fderiv ℝ (fderiv ℝ u) x₀ - fderiv ℝ (fderiv ℝ v) x₀ := by
    rw [hev.fderiv_eq]
    exact fderiv_sub ((hu'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hv'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have huv : ContDiffAt ℝ 2 (u - v) x₀ := hu'.sub hv'
  intro w
  have hle := SndFDerivNonposAtLocalMax huv hmax w
  simp only [hsplit, _root_.sub_apply] at hle
  linarith
