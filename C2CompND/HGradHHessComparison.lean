import C2CompND.HGrad
import C2CompND.HHessSym
import C2CompND.HHessEntryFormula
import C2CompND.PosSemidefSymmQuadForm
open Matrix
/-- Last sentence of Section 2.1: `grad u = grad v` and `D^2 u <= D^2 v` at `x` imply
`X u = X v` and `XXs u <= XXs v` at `x`. -/
theorem HGradHHessComparison {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hσ : ∀ i, ContDiffAt ℝ 1 (σ i) x)
    (hgrad : fderiv ℝ u x = fderiv ℝ v x)
    (hhess : ∀ w : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ u) x w w ≤ fderiv ℝ (fderiv ℝ v) x w w) :
    HGrad σ u x = HGrad σ v x ∧ (HHessSym σ v x - HHessSym σ u x).PosSemidef := by
  refine ⟨?_, ?_⟩
  · funext i
    simp only [HGrad, hgrad]
  · set W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
      fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ u) x with hWdef
    -- Step 2: entries of the difference of the unsymmetrized matrices
    have hD : ∀ i j, HHess σ v x i j - HHess σ u x i j = W (σ j x) (σ i x) := by
      intro i j
      rw [HHessEntryFormula σ u x i j hu (hσ i), HHessEntryFormula σ v x i j hv (hσ i), hgrad,
        hWdef]
      simp only [_root_.sub_apply]
      ring
    -- Step 4: the difference of the symmetrized matrices as a symmetrized quadratic form
    have hP : HHessSym σ v x - HHessSym σ u x
        = Matrix.of fun i j => (1 / 2 : ℝ) * (W (σ j x) (σ i x) + W (σ i x) (σ j x)) := by
      ext i j
      have h1 := hD i j
      have h2 := hD j i
      simp only [HHessSym, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.transpose_apply, smul_eq_mul, Matrix.of_apply]
      linarith [h1, h2]
    -- Step 5: the quadratic form of that matrix is nonnegative
    rw [hP]
    refine PosSemidefSymmQuadForm W (fun i => σ i x) (fun z => ?_)
    rw [hWdef]
    simp only [_root_.sub_apply]
    linarith [hhess z]
