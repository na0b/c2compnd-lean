# A comparison principle for degenerate sub-elliptic equations, in Lean 4

This repository contains a Lean 4 formalization, built on [Mathlib](https://github.com/leanprover-community/mathlib4), of Theorem 1.3 and Corollary 1.4 of

> Juan J. Manfredi and Shirsho Mukherjee,
> *A note on the comparison principle for degenerate sub-elliptic equations*, manuscript, 2026.

These are the comparison principle for C² sub- and super-solutions in the non-degenerate case and its corollary for functions without horizontal critical points, including the uniqueness statement. Both are stated and proved, together with everything their proofs use. The development contains no `sorry` and no axioms: every result depends only on the three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`).

<!-- TODO: remove once both authors have read the Lean statements below against the paper. -->

## Results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.3, comparison when X u ≠ 0 on argmax(u − v) | `ComparisonNondeg` | [`C2CompND/ComparisonNondeg.lean`](C2CompND/ComparisonNondeg.lean) |
| Corollary 1.4, comparison when u or v has no horizontal critical points | `CorNocritComparison` | [`C2CompND/CorNocritComparison.lean`](C2CompND/CorNocritComparison.lean) |
| Corollary 1.4, uniqueness for the Dirichlet problem | `CorNocritUniqueness` | [`C2CompND/CorNocritUniqueness.lean`](C2CompND/CorNocritUniqueness.lean) |

The proofs follow Section 3.1 of the paper: Lemma 3.1 is `LocalMaxOpIneq`, Lemma 3.2 is `PerturbationIdentity`, and Proposition 3.3 is `ComparisonNondeg` itself. Theorem 1.5 (admissible pairs) and the results of Sections 3.2–3.4 are not formalized.

## Setting: general Hörmander frames

The paper works on a Carnot group 𝔾 = (ℝⁿ, ∗) with X₁, …, Xₘ a basis of the first layer. The formalization proves the results in a more general setting: X<sub>i</sub> = σ<sup>i</sup>(x) · ∇ for an **arbitrary** family σ = (σ¹, …, σᵐ) of smooth vector fields on ℝⁿ satisfying Hörmander's rank condition (1.1). No group law, left-invariance, homogeneity or linear independence is assumed. The argument of Section 3.1 uses none of these, so nothing is lost; a basis of the first layer of a Carnot group is a special case. Hörmander's condition is kept as a hypothesis, as in the paper, although the proof does not use it. The Carnot-group structure itself is not formalized (Mathlib has none).

## Definitions

| Paper | Lean | Meaning |
|---|---|---|
| X u = (X₁u, …, Xₘu) | `HGrad σ u x` | `fun i => fderiv ℝ u x (σ i x)` |
| XX u = (X<sub>j</sub>X<sub>i</sub>u)<sub>i,j</sub> | `HHess σ u x` | entry (i, j) is the derivative of X<sub>i</sub>u in the direction σ<sup>j</sup>(x) |
| ℒu = −Tr(a(X u) XX u), (1.2) | `SubellipticOp σ a u x` | `-(a (HGrad σ u x) * HHess σ u x).trace` |
| ℰ(ξ) = ⟨a(ξ)ξ, ξ⟩, (1.3) | `EllipticityFn a ξ` | `ξ ⬝ᵥ (a ξ *ᵥ ξ)` |
| Hörmander's condition (1.1) | `HormanderRank σ` | at every x, the values at x of the iterated Lie brackets of the σ<sup>i</sup> (`HorFamily σ`) span ℝⁿ |
| Definition 1.2, sub-solution | `IsClassicalSubsol σ a u U` | ℒu(x) ≤ 0 at every x ∈ U with X u(x) ≠ 0 |
| Definition 1.2, super-solution | `IsClassicalSupersol σ a u U` | ℒu(x) ≥ 0 at every x ∈ U with X u(x) ≠ 0 |

ℝⁿ is `EuclideanSpace ℝ (Fin n)`. The coefficient matrix is a function `a : (Fin m → ℝ) → Matrix (Fin m) (Fin m) ℝ`; all hypotheses on it are imposed only for ξ ≠ 0, so its value at 0 is irrelevant, as in the paper. "u ∈ C²(Ω) ∩ C(Ω̄)" is `ContDiffOn ℝ 2 u Ω ∧ ContinuousOn u (closure Ω)`, and ∂Ω is `frontier Ω`.

## Theorem 1.3

```lean
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
    ∀ x ∈ Ω, u x ≤ v x
```

The hypothesis `hnd` is "X u(x) ≠ 0 for every x ∈ argmax<sub>Ω</sub>(u − v)": `IsMaxOn (u - v) Ω x` says that x is a maximum point of u − v over Ω.

## Corollary 1.4

```lean
theorem CorNocritComparison {n m : ℕ}
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
    (hnc : (∀ x ∈ Ω, HGrad σ v x ≠ 0) ∨ (∀ x ∈ Ω, HGrad σ u x ≠ 0))
    (hbd : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x
```

```lean
theorem CorNocritUniqueness {n m : ℕ}
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
    (hsubu : IsClassicalSubsol σ a u Ω) (hsupu : IsClassicalSupersol σ a u Ω)
    (hsubv : IsClassicalSubsol σ a v Ω) (hsupv : IsClassicalSupersol σ a v Ω)
    (hvnc : ∀ x ∈ Ω, HGrad σ v x ≠ 0)
    (hbd : ∀ x ∈ frontier Ω, u x = v x) :
    ∀ x ∈ closure Ω, u x = v x
```

The second statement is the uniqueness sentence of Corollary 1.4: if u and v are both solutions (sub- and super-solutions), v has no horizontal critical points and u = v on ∂Ω, then u = v on Ω̄.

## What is and is not checked by Lean

The Lean kernel checks that the three theorems above follow from their definitions and Mathlib, using only the three standard axioms. Lean does not check that the definitions and the statements say what the paper says. That was reviewed during the formalization (see below), but readers who rely on the result should compare the statements and the definitions they use against the paper themselves. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration, cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) (18 pages). To rebuild it, run `pdflatex blueprint.tex` three times in that directory.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> c2compnd-lean
cd c2compnd-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by each main result
```

The project is pinned to Lean `v4.33.0` and the Mathlib commit recorded in `lakefile.lean`. Continuous integration rebuilds the project and checks the axioms on every push.

## Layout

```
C2CompND.lean          root module, imports the main results
C2CompND/              one file per definition, lemma or theorem (31 files)
Axioms.lean            #print axioms for the main results
blueprint/blueprint.tex  natural-language companion (inputs blueprint/nodes/*.tex)
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline; the Lean proofs and the blueprint were written by AI agents (Claude, by Anthropic) under the Trellis protocol. Each node was reviewed automatically for soundness of its natural-language proof, for faithfulness to the paper, and for agreement between its Lean statement and its natural-language statement. Juan J. Manfredi chose the targets and approved the statements at the Trellis gate, including the generalization to arbitrary Hörmander frames. The Lean kernel checks every proof.

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib. See [`LICENSE`](LICENSE).
