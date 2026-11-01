import C2CompND.FDerivEqAtLocalMaxSub
import C2CompND.HGrad
/-- At a local maximum of `u - v` the horizontal gradients agree: the paper's sentence
"At every point of argmax(u - v) we have grad u = grad v, hence X u = X v". -/
theorem HGradEqAtLocalMax {n m : ℕ}
    (σ : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hu : DifferentiableAt ℝ u x₀) (hv : DifferentiableAt ℝ v x₀)
    (hmax : IsLocalMax (u - v) x₀) :
    HGrad σ u x₀ = HGrad σ v x₀ := by
  funext i; simp only [HGrad, FDerivEqAtLocalMaxSub hu hv hmax]
