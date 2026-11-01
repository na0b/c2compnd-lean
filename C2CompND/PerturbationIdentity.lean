import C2CompND.HGradHHessComp
import C2CompND.SubellipticOp
import C2CompND.EllipticityFn
open scoped ContDiff
/-- `lem:tech` / `eq:estLh`: the exact value of `L (h . w)` at a point where the horizontal
gradient of `w` does not vanish and `h' (w x) > 0`. -/
theorem PerturbationIdentity {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (h : ℝ → ℝ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hσ : ∀ i, ContDiff ℝ ∞ (σ i))
    (hhom : ∀ t : ℝ, 0 < t → ∀ ξ ≠ 0, a (t • ξ) = (t ^ β) • a ξ)
    (hUo : IsOpen U) (hx : x ∈ U)
    (hh : ContDiff ℝ 2 h) (hw : ContDiffOn ℝ 2 w U)
    (hne : HGrad σ w x ≠ 0) (hpos : 0 < deriv h (w x)) :
    SubellipticOp σ a (h ∘ w) x
      = -(deriv h (w x) ^ β)
          * (deriv (deriv h) (w x) * EllipticityFn a (HGrad σ w x)
              - deriv h (w x) * SubellipticOp σ a w x) := by
  have hw' : ContDiffAt ℝ 2 w x := hw.contDiffAt (hUo.mem_nhds hx)
  have hσ' : ∀ i, ContDiffAt ℝ 1 (σ i) x := fun i => (hσ i).contDiffAt.of_le (by norm_num)
  -- Step 1: the two chain-rule identities
  obtain ⟨hg, hH⟩ := HGradHHessComp σ h w x hh hw' hσ'
  -- Step 2: homogeneity of `a` at the perturbed horizontal gradient
  have ha : a (HGrad σ (h ∘ w) x) = (deriv h (w x) ^ β) • a (HGrad σ w x) := by
    rw [hg]
    exact hhom _ hpos _ hne
  -- Step 4a: the ellipticity trace
  have hE : (a (HGrad σ w x) * Matrix.vecMulVec (HGrad σ w x) (HGrad σ w x)).trace
      = EllipticityFn a (HGrad σ w x) := by
    rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, EllipticityFn,
      dotProduct_comm]
  -- Step 4b: the operator at `w`
  have hLw : (a (HGrad σ w x) * HHess σ w x).trace = -SubellipticOp σ a w x := by
    rw [SubellipticOp, neg_neg]
  -- Steps 3 and 5
  rw [SubellipticOp, ha, hH, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, hE, hLw]
  simp only [smul_eq_mul]
  ring
