import C2CompND.Preamble
open Matrix
/-- The ellipticity function `E (xi) = <a xi . xi, xi>` of `eq:ell`. -/
noncomputable def EllipticityFn {m : ℕ}
    (a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ) (ξ : Fin m → ℝ) : ℝ :=
  ξ ⬝ᵥ (a ξ *ᵥ ξ)
