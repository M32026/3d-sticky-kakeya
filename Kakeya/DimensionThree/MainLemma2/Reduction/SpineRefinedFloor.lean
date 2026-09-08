/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct

/-!
# The refined source's count floor (H) and line-based essential distinctness

Source of record: the professor's refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex`, mapped 

Two of its objects are stated here in the tree's vocabulary, **as hypotheses and definitions,
not as theorems**:

* **line-based essential distinctness** (refined l.153–163), the notion the refined text uses
  for every level of its towers in place of the tree's pairwise `IsEssentiallyDistinct`.  The
  definition is E0 of the source map, at the name and namespace fixed for it
  (`Kakeya.VeryNotSticky.IsLineEssDistinct`), so that the two unify when E0 lands;
* **the per-cell count floor**, alternative (F) of `lem:ml2-window-refinement`
  (refined l.4086–4104) restated at its point of use as `eq:ml2-count-floor` (l.4476–4482):
  "for every retained `p`-cell and every named middle-window level `m > p`,
  `#𝕊''_m⟨T_p⟩ ≥ (ρ_p/ρ_m)^{2+4ζ}`".  Its derivation in the source is the six-line sketch
  l.4128–4145 (parent-density and Frostman comparisons).  It is **isolated** below as the
  hypothesis `hfloor` of `Kakeya.ML2Core.geometricCoreAt_of_floor_middleFactor`, in the
  exact-containment vocabulary of `Tube.UniformTubeSet.nodesUnder` (the tree's cells), and the
  middle-factor hypothesis of the wiring gains it as a binder — the cardinality lower bound that
   item H asked for and that `not_middleFactor_hypothesis`'s singleton lacks.

Nothing here derives the floor; `Kakeya.ML2Core.two_le_card_nodesUnder_of_spineWindow` is the
fragment of it the window's density lower bound gives for free (two cells rather than
`(ρ_p/ρ_m)^{2+4ζ}`).
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

/-! ### Line-based essential distinctness

`Kakeya.VeryNotSticky.IsLineEssDistinct` is imported from
`Kakeya.DimensionThree.MainLemma2.LineEssDistinct`, following the refined
source's definition in lines 153-163.
-/

namespace Kakeya.ML2Core

universe u


/-! ## The count floor, isolated, and the middle factor that receives it -/

section Floor

open Classical in
/-- **[DEAD ROUTE — see `Kakeya.ML2Core.SpineCountFloorObstruction`.]**

**`GeometricCoreAt` from the refined count floor and the middle factor that receives it.**

Two hypotheses, both stated on the block of `Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor`
(the spine-pinned window, the seam, the package's numeric facts).

* **`hfloor` — alternative (F) of `lem:ml2-window-refinement`, refined l.4086–4104, isolated.**
  For the window `a < b` at rung `m` on the constructed spine there is a *genuine parent level*
  `p` with `a ≤ p` and `p < m'` for every middle-window level `m'` (the levels `a < m' < b` with
  `(ρ_b/ρ_a)^{1-e} ≤ ρ_b/ρ_{m'} ≤ (ρ_b/ρ_a)^{e}`, refined l.4046–4050) such that
  (i) the parent density is bounded, `Δ_max(𝕊_p⟨S⟩) ≤ δ^{-2η'}` for every coarse node `S`
  (l.4092–4094), and (ii) **the count floor** `eq:ml2-count-floor` (l.4476–4482): for every
  coarse node `S`, every `p`-cell `T_p` under it and every middle-window level `m' > p`,
  `#𝕊_{m'}⟨T_p⟩ ≥ (ρ_p/ρ_{m'})^{2+4ζ}` with `ζ = η_{m+1}/16` (l.4009: `τ = η_{J+1}`,
  `ζ = τ/16`).  Cells are read as `Tube.UniformTubeSet.nodesUnder` (exact containment, the
  tree's `𝕋_b[T_a]`).  What is **not** carried from (F): the shading refinement
  `(𝕊'', Z'')` and its mass retention `Λ_f^{-1}` (l.4108–4112) — the floor is asked of the
  window's own hierarchy.  This is the six-line sketch l.4128–4145, stated as an assumption.
* **`hmid` — the middle factor at the rung, receiving the floor.**  The block of
  `geometricCoreAt_of_rungMiddleFactor` plus the binders `p`, `a ≤ p`, `p < m'` on the window,
  the parent density and the floor; the conclusion is unchanged (the `∃` over the split with the
  bound `δ^{47 η_m/5}`).  This is item H of  in the refined shape: the
  singleton configuration of `not_middleFactor_hypothesis` violates the floor at once.

The body only routes: `hfloor`'s output is handed to `hmid` inside the block, and the result is
`Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor`. -/
theorem geometricCoreAt_of_floor_middleFactor
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {η' : ℝ}
    (hfloor : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
        Cu ≤ Cu₀ →
        ∃ p : ℕ, a ≤ p ∧
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') ∧
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) ∧
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
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)))
    (hmid : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
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
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
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
      ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ 𝒰.cover.indexSet a,
        ∃ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
          (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
          (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jθ : ι),
          (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) ∧
          (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) ∧
          (∀ i, (Y' i).toTube = ((T i).translate v).toTube) ∧
          (a ≠ 0 → ∀ k ∈ tθ', (Yθ k).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3)))
              1) ∧
          tτ'.Nonempty ∧ tθ'.Nonempty ∧
          ShadedBody.IsCRefinement
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i ∈ tτ'} :
                Finset ι)
            (fun i ↦ (Y' i).toShadedBody) ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ ((T i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
                𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ)⁻¹ ∧
          (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
              𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
              ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
                  i).toShadedBody)
            ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
          (∀ jτ ∈ tτ', ∀ jθ ∈ tθ',
            ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
                i).toShadedBody)
              ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈
                  u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ *
                    ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                        tτ'.card
                      (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
                * ShadedBody.multiplicity
                    ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i =
                        jτ} : Finset ι)
                    (fun i ↦ (Y' i).toShadedBody)
                * ShadedBody.multiplicity
                    ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
                    (fun j ↦ (Yτ' j).toShadedBody)
                * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)) ∧
          jθ ∈ tθ' ∧
          ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ}
              : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (47 * ML2Spine.spineRung β ϖ ε₁ gain dens m / 5)
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β) :
    ML2Assembly.GeometricCoreAt.{u} := by
  classical
  refine geometricCoreAt_of_rungMiddleFactor hSFE ?_
  intro β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν Cu₀
  filter_upwards [hfloor β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν Cu₀,
    hmid β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν Cu₀] with δ hfl hmd
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hballu hune
    hmaxu hdense hcomp hlamlow hcardu hCstar hCu hmasspos hδτ hτθ hθ1
  obtain ⟨p, hap, hpm, hpar, hflo⟩ :=
    hfl u T Cu lam 𝒰 Cstar a b m hwin hballu hune hmaxu hdense hcomp hlamlow hcardu hCstar hCu
  exact hmd u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt hballs ht₀ hcn hballt₀ hballu hune
    hmaxu hdense hcomp hlamlow hcardu hCstar hCu hmasspos hδτ hτθ hθ1 p hap hpm hpar hflo

end Floor

/-! ## Control: the floor excludes a one-node cell by itself -/

section FloorControl

/-- **A cell obeying the count floor at any strictly finer window level has at least two nodes.**

The floor `(ρ_p/ρ_{m'})^{2+4ζ} ≤ #𝕊_{m'}⟨T_p⟩` with `p < m'` (so `ρ_p > ρ_{m'}`) and `ζ ≥ 0` has
a left-hand side strictly above `1`, so the cell cannot be a singleton.  This is the
cardinality content of `eq:ml2-count-floor` at its weakest, and it is what the singleton
configuration of `Kakeya.ML2Core.not_middleFactor_hypothesis` violates once a window level lies
strictly between the parent and the fine scale.  (The other exclusion, from the pinned spine's
density lower bound, is `Kakeya.ML2Core.two_le_card_nodesUnder_of_spineWindow`; the two are
independent.) -/
theorem two_le_card_of_countFloor {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {N p m' : ℕ}
    (hpm : p < m') (hm'N : m' ≤ N) {ζ : ℝ} (hζ : 0 ≤ ζ) {n : ℕ}
    (hfloor : ((Tube.gridScale δ N p : ℝ) / (Tube.gridScale δ N m' : ℝ)) ^ (2 + 4 * ζ)
      ≤ (n : ℝ)) :
    2 ≤ n := by
  have hδ1' : δ ≤ 1 := hδ1.le
  have hm'0 : 0 < Tube.gridScale δ N m' :=
    lt_of_lt_of_le hδ0 (delta_le_gridScale hδ0 hδ1' hm'N)
  have hm'r : (0 : ℝ) < (Tube.gridScale δ N m' : ℝ) := hm'0
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le (Nat.zero_lt_of_lt hpm) hm'N
    exact_mod_cast this
  have hlt : Tube.gridScale δ N m' < Tube.gridScale δ N p := by
    unfold Tube.gridScale
    apply NNReal.rpow_lt_rpow_of_exponent_gt hδ0 hδ1
    exact div_lt_div_of_pos_right (by exact_mod_cast hpm) hN0
  have hratio : (1 : ℝ) < (Tube.gridScale δ N p : ℝ) / (Tube.gridScale δ N m' : ℝ) := by
    rw [one_lt_div hm'r]
    exact_mod_cast hlt
  have hpow : (1 : ℝ) < ((Tube.gridScale δ N p : ℝ) / (Tube.gridScale δ N m' : ℝ)) ^ (2 + 4 * ζ) :=
    Real.one_lt_rpow hratio (by linarith)
  have h1 : (1 : ℝ) < (n : ℝ) := lt_of_lt_of_le hpow hfloor
  have h1' : 1 < n := by exact_mod_cast h1
  omega

end FloorControl

end Kakeya.ML2Core

end
