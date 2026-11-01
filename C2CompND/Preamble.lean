-- Preamble: shared imports for all tablet nodes.
-- Specific Mathlib imports only (never `import Mathlib`).

-- Calculus: Frechet derivatives, C^k regularity, local extrema, symmetry of D^2,
-- the one-dimensional derivative tests, and Lie brackets of vector fields.
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.VectorField

-- The ambient space `EuclideanSpace R (Fin n)` and its metric/compactness theory.
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact

-- Matrices: the Loewner order, positive semidefiniteness and the CFC square root.
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

-- Real powers `t ^ beta` with `beta : R` (`Real.rpow`), for the homogeneity exponent.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
