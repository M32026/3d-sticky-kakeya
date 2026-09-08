/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# `hfac`, named — the third open row of the `GeometricCoreAt` closure

After the line-ED drop  the factor hypothesis of the
`(F)` terminal engine carries no `Kakeya.VeryNotSticky.LineEDLevelsAt` row.  What is left is,
row for row, the factor hypothesis of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels`
(`SpineRungWiring.lean:1103`) with `Cu ≤ Cu₀` in place of `Cu ≤ max C 4`, followed by the four
refined-`(F)` rows.  This file gives both texts a name and adjudicates that reading with the
compiler rather than with prose.

* `Kakeya.ML2Core.HfacPostDrop` — the post-drop `hfac` of
  `Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`, verbatim.
* `Kakeya.ML2Core.HfacLevels` — the `hfac` of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels`,
  verbatim.
* `Kakeya.ML2Core.hfacPostDrop_of_hfacLevels` — the closure site's text implies the floor route's
  text at `Cu₀ := max C 4`, by dropping the four `(F)` antecedents.  **One producer serves both
  consumers**, which is what "the drop restores the interface" means operationally.

The two `example`s below are the checks: each named text is fed to its own consumer's `hfac`
slot and must be accepted by `exact`-grade unification.

## The wiring theorem, and its quantifier order

`Kakeya.ML2Core.geometricCoreAt_of_hfac_witness_payload` closes `ML2Assembly.GeometricCoreAt` from
three named obligations — `Kakeya.ML2Core.HfacPostDrop`, `Kakeya.ML2Core.SiteWitness`,
`Kakeya.ML2Core.FloorPayload` — plus a list of scalar side conditions, all of them **inside** the
`∀ β ϖ gain dens` binder.

That order is load-bearing and is the ``.  The tightened uniformity
binder of the middle factor carries the threshold `δ' ≤ (ssfUniformConst 3)^(-1/ηd)`, and `ηd`
shrinks with `β`; a statement that hoisted `∀ᶠ δ` outside `∀ β` would need one scale threshold
serving every `β` at once, and there is none.  `Kakeya.ML2Core.not_eventually_forall_exponent_le`
is the refutation of exactly that hoist, against
`Kakeya.ML2Core.eventually_const_le_rpow_neg_of_pos` in the admissible order.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## The two texts -/

open Classical in
/-- **The post-drop `hfac`**, verbatim the factor hypothesis of
`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha` after the estimate. -/
def HfacPostDrop.{u} (β ϖ ε₁ ηin η' εf εc κc : ℝ) (gm gain dens : ℝ → ℝ) (Cu₀ : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
            NNReal)
          (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
          (Cstar : ENNReal) (a b m : ℕ),
          ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
            (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
          (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
              (EuclideanSpace ℝ (Fin 3))) 1) →
          (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
              Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
          (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
          (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
          (a ≠ 0 → ∀ k ∈ t₀,
            ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
                3))) 1) →
          (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
          u.Nonempty →
          Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
          ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
          ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
          (δ : NNReal) ^ ηin / 2 ≤ lam →
          (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
          Cstar ≤ (δ : ENNReal) ^ (-κc) →
          Cu ≤ Cu₀ →
          0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
          δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
          Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
          Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
          -- the refined (F): the genuine parent level, its density, and the count floor
          ∀ p : ℕ, a ≤ p →
            (∀ m' : ℕ, a < m' → m' < b →
              ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
                ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
              (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
                ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
              p < m') →
            (∀ jθ ∈ 𝒰.cover.indexSet a,
              Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
                ≤ (δ : ENNReal) ^ (-(2 * η'))) →
            (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
              ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
                ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
              (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
                ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
              p < m' →
              ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                  / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                    ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
                ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
          ∃ (tτ' tθ' : Finset ι)
          (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
          (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
          (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
          tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
          ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
              i).toShadedBody)
              ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                  | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                    ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                      tτ'.card
                      (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
                * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                    𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
                * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                    = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
                * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
          ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              ≤ (δ : ENNReal) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
          ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
              Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                    ι)).card : ENNReal) ^ β ∧
          ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
              ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((tθ'.card : ℕ) : ENNReal) ^ β

open Classical in
/-- **The closure site's `hfac`**, verbatim the factor hypothesis of
`Kakeya.ML2Core.dichotomy_of_rungFactors_levels` (`SpineRungWiring.lean:1103`). -/
def HfacLevels.{u} (β ϖ ε₁ ηin εf εc κc : ℝ) (gm gain dens : ℝ → ℝ) (C : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
            NNReal)
          (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
          (Cstar : ENNReal) (a b m : ℕ),
          ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
            (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
          (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
              (EuclideanSpace ℝ (Fin 3))) 1) →
          (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
              Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
          (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
          (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
          (a ≠ 0 → ∀ k ∈ t₀,
            ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
                3))) 1) →
          (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
          u.Nonempty →
          Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
          ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
          ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
          (δ : NNReal) ^ ηin / 2 ≤ lam →
          (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
          Cstar ≤ (δ : ENNReal) ^ (-κc) →
          Cu ≤ max C 4 →
          0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
          δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
          Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
          Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
          ∃ (tτ' tθ' : Finset ι)
          (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
          (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
          (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jθ : ι),
          tτ' ⊆ t₁ ∧ tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧
          ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
              i).toShadedBody)
              ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                  | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                    ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                      tτ'.card
                      (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
                * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                    𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
                * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j
                    = jθ} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
                * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
          ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              ≤ (δ : ENNReal) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
          ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} :
              Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                    ι)).card : ENNReal) ^ β ∧
          ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
              ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((tθ'.card : ℕ) : ENNReal) ^ β

open Classical in
/-- **The post-cut `hfac` slot of the guarded
`Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`** — the four-way split
`Kakeya.ML2Core.HfacPostDrop` is kept **unchanged** above as the *pre-cut* record: it is what
`Kakeya.ML2Core.middleGain_nonpos_of_hfacPostDrop` refutes, and that refutation is the reason the
seam moved.  This is the text after the move — the seam at `(p, b)`, the new-parent factor at
`(a, p)` in defect shape, a third `spineScaleLoss` at the parent scale, and the parent level cut
at `p ≤ b`.  Feeding this text to either `middleGain_nonpos_*` refutation does not typecheck; that
is  Bar 2.

**Family/shading:** `(u, T)` under `𝒰`, with the split's four shadings.
**Level pairs:** fine `b → leaf`, middle `(p, b)`, new parent `(a, p)`, outer level `a`. -/
def HfacPostDropFour.{u} (β ϖ ε₁ ηin η' εf εp εc κc : ℝ) (gm gain dens : ℝ → ℝ) (Cu₀ : NNReal) :
    Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-κc) →
        Cu ≤ Cu₀ →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        -- the refined (F): the genuine parent level, its density, and the count floor
        ∀ p : ℕ, a ≤ p → p ≤ b →
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') →
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) →
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
        ∃ (tτ' tp' tθ' : Finset ι)
        (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
        (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p) (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jp jθ : ι),
        tτ' ⊆ t₁ ∧ tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p ∧
          tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧ tp'.Nonempty ∧
        ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
            i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ({i ∈ u
                | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tp'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) p) : NNReal) : ENNReal)
              * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
              * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j
                  = jp} : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k
                  = jθ} : Finset ι) (fun k ↦ (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
        ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            𝒰.cover.assign b i = jτ} : Finset ι) (fun i ↦ (Y' i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} :
            Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset
                  ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
            Finset ι) (fun k ↦ (Yp k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εp))
              * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset
                  ι)).card : ENNReal) ^ β ∧
        ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((tθ'.card : ℕ) : ENNReal) ^ β

/-! ## The two texts are the two consumers' own slots  -/

section Slots

variable {β ϖ : ℝ} {gain dens : ℝ → ℝ} {ε₁ ηin : ℝ} {C : NNReal} {Kl cl : ℕ}
  {Cu₀ : NNReal} {η' h : ℝ} {gm : ℝ → ℝ} {εf εp εc κc κ' θ₁ θ₂ : ℝ}

/-- **floor side.**  `Kakeya.ML2Core.HfacPostDrop` is accepted, unchanged, in the `hfac`
slot of the guarded `Kakeya.ML2Core.trialOutcome_middle_of_floorFactors_alpha`. -/
example (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hε₁ : 0 < ε₁) (hC : 1 ≤ C) (hCu₀ : 1 ≤ Cu₀)
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₂ : 0 < θ₂) (hεp : 0 < εp) (Λf : NNReal → ℝ≥0∞)
    (hres : ∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
      κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η')
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin ≤ gm X - εf - εp - (εc + X) - κ')
    (hfac : HfacPostDropFour.{u} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀) : True := by
  have := trialOutcome_middle_of_floorFactors_alpha (Kl := Kl) (cl := cl) (h := h) (η' := η')
    hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc hκ' hθ₂ hεp hres Λf hexp hfac
  trivial

/-- **closure side.**  `Kakeya.ML2Core.HfacLevels` is accepted, unchanged, in the `hfac`
slot of `Kakeya.ML2Core.dichotomy_of_rungFactors_levels`.  `hpkg` is left as a lambda binder so
that the check reads the site's own statement rather than a transcription of it. -/
example (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hε₁ : 0 < ε₁) (hηinν : ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens) (hC : 1 ≤ C)
    (hκc : 0 < κc) (hκ' : 0 < κ') (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂)
    (hexp : ∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
      6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₁ + θ₂ + 2 * ηin ≤ gm X - εf - (εc + X) - κ')
    (hfac : HfacLevels.{u} β ϖ ε₁ ηin εf εc κc gm gain dens C) : True := by
  have := fun hpkg => dichotomy_of_rungFactors_levels (Kl := Kl) (cl := cl)
    hβ0 hβ1 hϖ hgain hdens hε₁ hηinν hC hpkg hκc hκ' hθ₁ hθ₂ hexp hfac
  trivial

end Slots

/-! ## One producer for both consumers -/

open Classical in
/-- **The closure site's factor hypothesis implies the floor route's**, at `Cu₀ := max C 4`.

The only differences between the two texts are the constant in the uniformity row and the four
refined-`(F)` antecedents, which the floor engine adds and the site does not: so a producer of
`Kakeya.ML2Core.HfacLevels` discharges `Kakeya.ML2Core.HfacPostDrop` by dropping four hypotheses,
and there is no second obligation to build. -/
theorem hfacPostDrop_of_hfacLevels {β ϖ ε₁ ηin η' εf εc κc : ℝ} {gm gain dens : ℝ → ℝ}
    {C : NNReal} (h : HfacLevels.{u} β ϖ ε₁ ηin εf εc κc gm gain dens C) :
    HfacPostDrop.{u} β ϖ ε₁ ηin η' εf εc κc gm gain dens (max C 4) := by
  filter_upwards [h] with δ hδ
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16 h17 h18 h19 _p _hp _hF1 _hF2 _hF3
  exact hδ u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 h16 h17 h18 h19

/-! ## the threshold order, and why it may not be hoisted -/

/-- **The admissible order.**  With the exponent fixed first, a scale threshold exists.  This is
`Kakeya.ML2Reduction.exists_threshold_coe_const_le_rpow_neg` read as an eventuality. -/
theorem eventually_const_le_rpow_neg_of_pos {Cst : NNReal} (hC : 1 ≤ Cst) {ηd : ℝ} (hηd : 0 < ηd) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (Cst : ENNReal) ≤ (δ : ENNReal) ^ (-ηd) := by
  obtain ⟨δ₀, hδ₀0, hbd⟩ := ML2Reduction.exists_threshold_coe_const_le_rpow_neg hC hηd
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < δ₀ from hδ₀0)] with δ hδ
  exact hbd δ hδ.1 (le_of_lt hδ.2)

/-- **The per-scale refutation of the hoist.**  At any fixed positive `δ` the threshold row fails
for small enough exponents: raising `Cst ≤ δ ^ (-1/n)` to the `n`-th power gives `Cst ^ n ≤ δ⁻¹`
for every `n`, which no constant `> 1` survives. -/
theorem not_forall_pos_const_le_rpow_neg {Cst : NNReal} (hC : 1 < Cst) {δ : NNReal}
    (hδ0 : 0 < δ) : ¬ ∀ ηd : ℝ, 0 < ηd → (Cst : ENNReal) ≤ (δ : ENNReal) ^ (-ηd) := by
  intro hall
  have hne : (δ : NNReal) ≠ 0 := ne_of_gt hδ0
  have key : ∀ n : ℕ, Cst ^ (n + 1) ≤ δ⁻¹ := by
    intro n
    have hn0 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    have h1 := hall ((n : ℝ) + 1)⁻¹ hpos
    rw [← ENNReal.coe_rpow_of_ne_zero hne, ENNReal.coe_le_coe] at h1
    have h2 : Cst ^ (n + 1) ≤ (δ ^ (-((n : ℝ) + 1)⁻¹)) ^ (n + 1) :=
      pow_le_pow_left' h1 (n + 1)
    have h3 : (δ ^ (-((n : ℝ) + 1)⁻¹)) ^ (n + 1) = δ⁻¹ := by
      rw [← NNReal.rpow_natCast (δ ^ (-((n : ℝ) + 1)⁻¹)) (n + 1), ← NNReal.rpow_mul]
      have : -((n : ℝ) + 1)⁻¹ * ((n : ℕ) + 1 : ℕ) = -1 := by
        push_cast
        field_simp
      rw [this, NNReal.rpow_neg_one]
    exact h3 ▸ h2
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (δ⁻¹) hC
  exact absurd (key n) (not_le.mpr (lt_of_lt_of_le hn (pow_le_pow_right₀ hC.le (Nat.le_succ n))))

/-- **.**  The hoisted order — one scale threshold serving every exponent at once —
is refuted.  Read against `Kakeya.ML2Core.eventually_const_le_rpow_neg_of_pos`, this is what forces
the wiring theorem below to keep every `∀ᶠ (δ : NNReal)` **inside** the `∀ β ϖ gain dens` binder:
`ηd` shrinks with `β`, so an outer `∀ᶠ δ` would have to serve all of them. -/
theorem not_eventually_forall_exponent_le {Cst : NNReal} (hC : 1 < Cst) :
    ¬ ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ ηd : ℝ, 0 < ηd → (Cst : ENNReal) ≤ (δ : ENNReal) ^ (-ηd) := by
  intro hev
  obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  exact not_forall_pos_const_le_rpow_neg hC hδ0 hδ

/-- **`1 < ssfUniformConst n`.**  The uniformiser's own constant is at least `4`. -/
theorem one_lt_ssfUniformConst (n : ℕ) : 1 < ShadedTube.ssfUniformConst n := by
  unfold ShadedTube.ssfUniformConst
  exact lt_of_lt_of_le (by norm_num : (1 : NNReal) < 4) (le_max_right _ _)

/-- **The first conjunct of the tightened `huni`, in the admissible order.**

 specified the middle factor's uniformity binder into the folded conjunct
`(ssfUniformConst 3 : ENNReal) ≤ δ'^(-ηd) ∧ Nonempty (ShadedUniformTubeSet …)`.  Its first
component is a scale threshold, and this is that threshold **with `ηd` fixed before `δ'`** — the
only order in which it holds. -/
theorem eventually_ssfUniformConst_le_rpow_neg {ηd : ℝ} (hηd : 0 < ηd) :
    ∀ᶠ (δ' : NNReal) in 𝓝[>] 0,
      ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) :=
  eventually_const_le_rpow_neg_of_pos (ShadedTube.one_le_ssfUniformConst 3) hηd

/-- **at the constant that actually appears**: the same threshold with the quantifiers
swapped is false.  `ηd` shrinks with `β`, so a wiring that hoisted `∀ᶠ δ'` outside the `β`
quantifier would be demanding exactly this. -/
theorem not_eventually_forall_exponent_ssfUniformConst :
    ¬ ∀ᶠ (δ' : NNReal) in 𝓝[>] 0, ∀ ηd : ℝ, 0 < ηd →
        ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) :=
  not_eventually_forall_exponent_le (one_lt_ssfUniformConst 3)

/-! ## The wiring theorem -/

/-- **`ML2Assembly.GeometricCoreAt` from `hfac`, the site witness and the floor payload.**

Every hypothesis of the closure, named.  Three of them carry mathematics —
`Kakeya.ML2Core.HfacPostDrop`, `Kakeya.ML2Core.SiteWitness`, `Kakeya.ML2Core.FloorPayload` — and
the rest are scalar side conditions.

**Quantifier order.**  The parameter package, and with it every
`∀ᶠ (δ : NNReal) in 𝓝[>] 0` obligation, sits **inside** `∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ)`: for each
`β` a fresh scale threshold is allowed.  The opposite order is not merely inconvenient, it is false;
`Kakeya.ML2Core.not_eventually_forall_exponent_le` refutes it at the shape the middle factor's
tightened uniformity binder needs.

The `(F)` absorption row `hΛf` is *not* a hypothesis: it is produced by
`Kakeya.ML2Core.eventually_hΛf_polylogLoss` at `Λf := Kakeya.ML2Core.polylogLoss K'`. -/
theorem geometricCoreAt_of_hfac_witness_payload.{v} (K' : ℕ)
    (hsup : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v} β ϖ gain dens →
      KatzTaoEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v} (EuclideanSpace ℝ (Fin 3)) β →
      0 < ϖ ∧ (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ (Cu₀ C : NNReal) (Kl cl : ℕ) (ηin aL η' εf εp εc κc κ' θ₂ : ℝ) (gm : ℝ → ℝ),
        0 < aL ∧ 1 ≤ C ∧ 1 ≤ Cu₀ ∧ 0 < κc ∧ 0 < κ' ∧ 0 < θ₂ ∧ 0 < εp ∧
        (∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
          κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') ∧
        (∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
          6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
            ≤ gm X - εf - εp - (εc + X) - κ') ∧
        HfacPostDropFour.{v} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀ ∧
        SiteWitness.{v} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
        FloorPayload.{v} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens (polylogLoss K')) :
    ML2Assembly.GeometricCoreAt.{v} := by
  refine geometricCoreAt_of_witness_and_trial K' (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp, hfac, hwit, hfloor⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, ηin, aL, haL, hwit,
    trialSupplier_of_floorRoute
      (trialOutcome_middle_of_floorFactors_alpha (Kl := Kl) (cl := cl)
        (h := defectH β ϖ ε₁ gain dens) (η' := η')
        hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc hκ' hθ₂ hεp hres (polylogLoss K') hexp hfac)
      (eventually_hΛf_polylogLoss K' hβ0 hϖ hε₁ hgain hdens) hfloor⟩

end Kakeya.ML2Core

end
