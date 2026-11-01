import C2CompND.Preamble
open Matrix
/-- A continuous bilinear form `W` with `W z z >= 0`, sampled along a finite family of vectors
`s` and symmetrized, yields a positive semidefinite matrix. -/
theorem PosSemidefSymmQuadForm {n m : ℕ}
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (s : Fin m → EuclideanSpace ℝ (Fin n))
    (hW : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ W z z) :
    (Matrix.of fun i j => (1 / 2 : ℝ) * (W (s j) (s i) + W (s i) (s j))).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  -- the matrix is symmetric
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.of_apply]
    ring
  · intro ξ
    set z : EuclideanSpace ℝ (Fin n) := ∑ i, ξ i • s i with hzdef
    -- bilinear expansion of `W z z`
    have hexp : W z z = ∑ i, ∑ j, ξ i * ξ j * W (s j) (s i) := by
      rw [hzdef]
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
        Finset.mul_sum, mul_assoc]
    -- the symmetrization contributes nothing to the quadratic form
    have hswap : ∑ i, ∑ j, ξ i * ξ j * W (s j) (s i)
        = ∑ i, ∑ j, ξ i * ξ j * W (s i) (s j) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hsplit : ∑ i : Fin m, ∑ j : Fin m,
          ((1 / 2 : ℝ) * (ξ i * ξ j * W (s j) (s i))
            + (1 / 2 : ℝ) * (ξ i * ξ j * W (s i) (s j)))
        = (1 / 2 : ℝ) * (∑ i, ∑ j, ξ i * ξ j * W (s j) (s i))
          + (1 / 2 : ℝ) * (∑ i, ∑ j, ξ i * ξ j * W (s i) (s j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    have hquad : star ξ ⬝ᵥ
        ((Matrix.of fun i j => (1 / 2 : ℝ) * (W (s j) (s i) + W (s i) (s j))) *ᵥ ξ)
        = ∑ i, ∑ j, ξ i * ξ j * W (s j) (s i) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      have key : ∀ p q : Fin m,
          star ξ p * (Matrix.of fun i j => (1 / 2 : ℝ) * (W (s j) (s i) + W (s i) (s j))) p q
              * ξ q
            = (1 / 2 : ℝ) * (ξ p * ξ q * W (s q) (s p))
              + (1 / 2 : ℝ) * (ξ p * ξ q * W (s p) (s q)) := by
        intro p q
        simp only [Matrix.of_apply, Pi.star_apply, star_trivial]
        ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => key i j, hsplit]
      linarith [hswap]
    rw [hquad, ← hexp]
    exact hW z
