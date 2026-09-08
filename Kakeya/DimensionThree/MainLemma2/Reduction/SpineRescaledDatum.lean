/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRungWiring

/-!
# rescaled datum, built from the wiring's block

`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` — the producer-side interface of the
middle factor — opens with the estimate group of binders: the outer rescaling situation
`Tube.IsRescalingSituation θ τ δ̃ Rout 3` at the window's two scales, the coarse node `Tθ`, the
fibre `fib` of `τ`-tubes inside it with `hsubOut`, the ratio bound `τ/θ ≤ 4 δ̃`, and the transport
exponent `hsep : δ̃ ≤ δ^{w}`.   lists "the outer rescaling datum
`hsitOut`" as one of the four objects the producer still owes.

This file builds it from exactly the data the block of
`Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor` hands a producer: the spine-pinned window,
the translation `v`, the retained level-`b` nodes, a coarse node `jθ`, and the two tube
identities of the split.  It also transports the two facts GWZ read on the rescaled family
`(𝕋̃, Ỹ)` at `δ̃ = τ/θ`:

* `upperBdDeltaMaxTildeTT`: `Δ_max(𝕋̃) ≤ outerLoss · C⋆ · (θ/τ)^{η_m}` — the window's
  `middle_maxDensity_le` transported by `Kakeya.ML2Reduction.outerFamily_maxDensity_le`
  (translation invariance of `Δ_max` and monotonicity under `fib ⊆ 𝕋_{τ∣θ}[T_θ]` in between);
* the multiplicity is **unchanged** by the rescaling (`outerFamily_multiplicity`, an equality) and
  the fullness drops by at most `outerLoss` (`outerFamily_le_fullness`).

What it does **not** transport is the density lower bound `tildeDeltaLargeDeltamax` at the
intermediate scales, GWZ (`section9.tex:112`): that statement is about the `σ`-fattening of the
rescaled family, and the rescaling map is anisotropic, so the fattening of the image is not the
image of the fattening.  No existing lemma compares the two; it is named as an separate comparison
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

section RescaledDatum

open Classical in
/-- **rescaled datum: the outer rescaling situation at the window's two scales, the fibre
inside the coarse node, and the transported density/multiplicity/fullness facts.**

`δ̃ := τ/θ` with `τ = gridScale δ N b`, `θ = gridScale δ N a`; `Rout` is any radius past
`Tube.normalization.C 3` and past `1`.  The one threshold is `δ^{e} ≤ 1/4` (`hquarter`), which
puts `δ̃ ≤ δ^{e}` (the window's `scale_sep`) under the situation's truncation `δ̃ ≤ 1/4`.

The conclusions are, in order: the ratio bound `τ/θ ≤ 4 δ̃` (an equality), the transport exponent
`δ̃ ≤ δ^{e}`, the fibre containment `hsubOut` (`fibre_carrier_subset_coarseNode`), the unit-ball
normalisation of the rescaled family, `upperBdDeltaMaxTildeTT`, the multiplicity identity and the
fullness floor.  Every one of them is a binder or an input of
`Kakeya.ML2Core.middle_factor_of_edNodes_sharp`'s the estimate group or of `hmax`. -/
theorem exists_rescaledMiddleDatum
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    {δ Cu : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} {u : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m)
    (hquarter : ((δ ^ ML2Spine.spineDiv ϖ ε₁ : NNReal) : ℝ) ≤ 1 / 4)
    {Rout : ℝ} (hRout : 0 < Rout) (hR1 : 1 ≤ Rout)
    (hRC : (Tube.normalization.C 3 : ℝ) ≤ Rout)
    (v : EuclideanSpace ℝ (Fin 3)) {tτ' : Finset ι}
    (htτ : tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b)
    {jθ : ι} (hjθ : jθ ∈ 𝒰.cover.indexSet a)
    {Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3))}
    {Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3))}
    (hYτ' : ∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v)
    (hYθ : ∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) :
    ∃ hsitOut : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) a)
        (Tube.gridScale δ (Tube.ssfGridLen δ) b)
        (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
        Rout 3,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          ≤ 4 * ((Tube.gridScale δ (Tube.ssfGridLen δ) b
              / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ∧
      Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a
          ≤ δ ^ ML2Spine.spineDiv ϖ ε₁ ∧
      (∀ j ∈ ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι),
        (Yτ' j).carrier ⊆ (Yθ jθ).toTube.carrier) ∧
      (∀ j ∈ ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι),
        (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
            (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
            Yτ' j).carrier ⊆ Metric.closedBall 0 1) ∧
      Kakeya.maxDensity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
          (fun j ↦ (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
            (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
            Yτ' j).toConvexSpaceBody)
        ≤ (ML2Reduction.outerLoss Rout : ENNReal)
          * (Cstar * ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ))
                ^ ML2Spine.spineRung β ϖ ε₁ gain dens m)) ∧
      ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
          (fun j ↦ (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
            (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
            Yτ' j).toShadedBody)
        = ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
          (fun j ↦ (Yτ' j).toShadedBody) ∧
      (ML2Reduction.outerLoss Rout)⁻¹
          * ShadedBody.fullness
            ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
            (fun j ↦ (Yτ' j).toShadedBody)
        ≤ ShadedBody.fullness
            ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
            (fun j ↦ (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
              (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
              Yτ' j).toShadedBody) := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨hδτ, hτθ, hθ1⟩ := window_scales hδ0 hδ1 hwin
  have hτ0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) b := lt_of_lt_of_le hδ0 hδτ
  have hθ0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) a := lt_of_lt_of_le hτ0 hτθ
  have hθr : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := hθ0
  have hδtr : ((Tube.gridScale δ (Tube.ssfGridLen δ) b
      / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ)
      = (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := NNReal.coe_div _ _
  have hδt0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a :=
    div_pos hτ0 hθ0
  -- the transport exponent: `δ̃ ≤ δ^{e}` is the window's `scale_sep`
  have hsep : Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a
      ≤ δ ^ ML2Spine.spineDiv ϖ ε₁ := by
    rw [← NNReal.coe_le_coe, hδtr, NNReal.coe_rpow, div_le_iff₀ hθr]
    exact hwin.scale_sep
  have hδt4 : ((Tube.gridScale δ (Tube.ssfGridLen δ) b
      / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ≤ 1 / 4 :=
    le_trans (by exact_mod_cast hsep) hquarter
  have hsitOut : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) a)
      (Tube.gridScale δ (Tube.ssfGridLen δ) b)
      (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a) Rout 3 :=
    { pos_ambient := hθ0
      inner_le_ambient := hτθ
      ambient_le_one := hθ1
      pos_out := hδt0
      out_le_quarter := hδt4
      out_le_ratio := le_of_eq hδtr
      normalizationConst_le_radius := hRC }
  have hτθ4 : (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
      ≤ 4 * ((Tube.gridScale δ (Tube.ssfGridLen δ) b
          / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) := by
    rw [hδtr]
    have h0 : (0 : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by positivity
    linarith
  have hsubOut := fibre_carrier_subset_coarseNode (jθ := jθ) 𝒰.cover.toChain hwin.coarse_lt_fine.le
    hwin.fine_le_gridLen htτ v hYτ' hYθ
  -- the fibre sits under the coarse node in the hierarchy's own terms
  have hfibsub : ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
      ⊆ 𝒰.nodesUnder b a jθ := by
    intro j hj
    obtain ⟨hjt, hjc⟩ := Finset.mem_filter.mp hj
    rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff]
    refine ⟨ML2Reduction.activeNodes_subset _ _ (htτ hjt), ?_⟩
    have h := ML2Reduction.tube_le_coarseNode 𝒰.cover.toChain hwin.coarse_lt_fine.le
      hwin.fine_le_gridLen (htτ hjt)
    rwa [hjc] at h
  refine ⟨hsitOut, hτθ4, hsep, hsubOut,
    ML2Reduction.outerFamily_carrier_subset_closedBall hn hsitOut hRout hτθ4 hsubOut, ?_,
    ML2Reduction.outerFamily_multiplicity hn hsitOut hRout hτθ4 hsubOut,
    ML2Reduction.outerFamily_le_fullness hn hsitOut hRout hR1 hτθ4 hsubOut⟩
  -- `upperBdDeltaMaxTildeTT`
  refine (ML2Reduction.outerFamily_maxDensity_le hn hsitOut hRout hR1 hτθ4 hsubOut).trans ?_
  refine mul_le_mul' le_rfl ?_
  have h1 : Kakeya.maxDensity
        ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
        (fun j ↦ (Yτ' j).toConvexSpaceBody)
      = Kakeya.maxDensity
        ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
        (fun j ↦ ((𝒰.cover.tube b j).translate v).toConvexSpaceBody) :=
    Kakeya.maxDensity_congr (fun j _ => congrArg Tube.toConvexSpaceBody (hYτ' j))
  rw [h1, StickyKakeya.maxDensity_tube_translate]
  exact (Kakeya.maxDensity_mono _ hfibsub).trans (hwin.middle_maxDensity_le jθ hjθ)

end RescaledDatum

/-! ## input: the essentially distinct, plank-scale-uniform refinement of `𝕋̃` -/

section EdUniform

/-- **The essentially distinct refinement of the rescaled family, uniformised at the plank scale.**

Both branches of the estimate act on a family that is pairwise essentially distinct (`eccentric_of_leafUnitBall` asks it of its leaves; GWZ's `𝕋̃` is a set of essentially distinct
tubes by convention) and carries a single-scale uniformity structure at a radius `≥ plankScale σ ε₂`
(`exists_plankFactoringData_of_isUniformAtScale_of_leafBall`).  Neither is what the rescaling hands
over — the `b`-nodes of the ambient hierarchy are grid-net tubes, not essentially distinct.  Two existing selections supply them, each at a cardinality retention:

* `Kakeya.ML2Inputs.exists_essDistinct_subfamily` at the loss `edLoss 3 D` with `D` any bound on
  `Δ_max(𝕋̃)` — for the rescaled middle family, `upperBdDeltaMaxTildeTT`
  (`Kakeya.ML2Core.exists_rescaledMiddleDatum`), so the loss is `≈ C⋆ (θ/τ)^{η_m}`, a
  `δ̃^{-η_m}`-power that the middle exponent `47 η_m/(5e)` absorbs;
* `Kakeya.ML2Core.exists_isUniformAtScale_on_subfamily` at the free exponent `α`.

The uniformity is bound to the doubly-refined `s''` and to nothing larger (the pinning trap); the
two retentions are what comes back.  Converting them into the shading-mass retention `hret` wants is `Kakeya.ML2Core.sum_shade_retention`, whose `HasComparableDensities` input the
re-cut block now carries. -/
theorem exists_edUniform_of_rescaled {ε₂ : ℝ} (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1)
    (K₀ : ℕ) {α : ℝ} (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {σ : NNReal}, 0 < σ → σ ≤ δ₀ →
      ∀ (fib : Finset ι) (Z : ι → ShadedTube σ (EuclideanSpace ℝ (Fin 3))) {D : ENNReal},
        (∀ i ∈ fib, (Z i).carrier ⊆ Metric.closedBall 0 1) →
        Kakeya.maxDensity fib (fun i ↦ (Z i).toConvexSpaceBody) ≤ D →
        (fib.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) →
        ∃ uED ⊆ fib, ∃ s'' ⊆ uED,
          ((uED : Set ι).Pairwise
            fun i j ↦ _root_.IsEssentiallyDistinct (Z i).carrier (Z j).carrier) ∧
          ((s'' : Set ι).Pairwise
            fun i j ↦ _root_.IsEssentiallyDistinct (Z i).carrier (Z j).carrier) ∧
          (fib.card : ENNReal)
            ≤ ML2Inputs.edLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) D
              * (uED.card : ENNReal) ∧
          (uED.card : ℝ) ≤ (σ : ℝ) ^ (-α) * (s''.card : ℝ) ∧
          ∃ ρ : NNReal, ML2Reduction.plankScale σ ε₂ ≤ ρ ∧
            Nonempty (Tube.IsUniformAtScale s'' (fun i ↦ (Z i).toTube) ρ
              (Tube.uniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ^ 2)
              (Tube.uniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) := by
  classical
  obtain ⟨δ₀, hδ₀0, hδ₀1, huni⟩ :=
    exists_isUniformAtScale_on_subfamily.{u} (E := EuclideanSpace ℝ (Fin 3)) K₀ α hα hε₂0 hε₂1
  refine ⟨δ₀, hδ₀0, hδ₀1, ?_⟩
  intro ι σ hσ0 hσδ₀ fib Z D hball hD hcard
  have hσ1 : σ ≤ 1 := hσδ₀.trans hδ₀1
  obtain ⟨uED, huED, hEDu, hcardED⟩ :=
    ML2Inputs.exists_essDistinct_subfamily (E := EuclideanSpace ℝ (Fin 3)) hσ0 hσ1 fib
      (fun i ↦ (Z i).toTube) hD
  have hballu : ∀ i ∈ uED, ((Z i).toTube).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3))
      1 := fun i hi ↦ hball i (huED hi)
  have hcardu : (uED.card : ℝ) ≤ (σ : ℝ) ^ (-(K₀ : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card huED) hcard
  obtain ⟨s'', hs'', hret, ρ, hρ, hPS⟩ :=
    huni hσ0 hσδ₀ uED (fun i ↦ (Z i).toTube) hballu hcardu
  exact ⟨uED, huED, s'', hs'', hEDu, ML2Inputs.pairwise_essDistinct_subset hs'' hEDu, hcardED,
    hret, ρ, hρ, hPS⟩

end EdUniform

/-! ## The two composed, at the block's own data -/

section Composed

open Classical in
/-- **input family, produced from the block of
`Kakeya.ML2Core.geometricCoreAt_of_rungMiddleFactor` alone, below a threshold on `δ`.**

`Kakeya.ML2Core.exists_rescaledMiddleDatum` composed with
`Kakeya.ML2Core.exists_edUniform_of_rescaled` at `σ = δ̃ = τ/θ`, `ε₂ = spineEps₂ ϖ ε₁`,
`D = outerLoss · C⋆ · (θ/τ)^{η_m}` and `K₀ = ⌈4/e⌉₊`.  The two thresholds of the ingredients —
`δ̃ ≤ δ₁` for the uniformiser and `δ̃ ≤ 1/4` for the rescaling situation — become thresholds on
`δ` alone through the window's `scale_sep` (`δ̃ ≤ δ^{e}`): `δ ≤ min (δ₁^{1/e}) ((1/4)^{1/e})`.  The
crude cardinality input `#𝕋̃ ≤ δ̃^{-K₀}` is the block's `#u ≤ δ^{-4}` read through
`card_activeNodes_le_card` and `δ̃^{K₀} ≤ δ^{e K₀} ≤ δ^{4}`.

The output is the leaf family both branches of the estimate act on: pairwise essentially distinct,
inside `B̄(0,1)`, carrying `IsUniformAtScale` at a radius `≥ plankScale δ̃ ε₂`, with the two
cardinality retentions.  `hsitOut` is returned so that the family is literally
`outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout δ̃ Yτ'`, the family every the estimate
binder of `middle_factor_of_edNodes_sharp` is stated on. -/
theorem exists_edUniform_rescaledMiddle
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    {α : ℝ} (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ {δ Cu : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ {ι : Type u} {u : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {Cstar : ENNReal} {a b m : ℕ},
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        ∀ {Rout : ℝ} (hRout : 0 < Rout), 1 ≤ Rout → (Tube.normalization.C 3 : ℝ) ≤ Rout →
        ∀ (v : EuclideanSpace ℝ (Fin 3)) {tτ' : Finset ι},
          tτ' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        ∀ {jθ : ι}, jθ ∈ 𝒰.cover.indexSet a →
        ∀ {Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3))}
          {Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3))},
          (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) →
          (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) →
        ∃ hsitOut : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) a)
            (Tube.gridScale δ (Tube.ssfGridLen δ) b)
            (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
            Rout 3,
          ∃ uED ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι),
          ∃ s'' ⊆ uED,
            ((uED : Set ι).Pairwise fun i j ↦ _root_.IsEssentiallyDistinct
              (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
                (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
                Yτ' i).carrier
              (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
                (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
                Yτ' j).carrier) ∧
            ((s'' : Set ι).Pairwise fun i j ↦ _root_.IsEssentiallyDistinct
              (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
                (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
                Yτ' i).carrier
              (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
                (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
                Yτ' j).carrier) ∧
            ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)).card
                : ENNReal)
              ≤ ML2Inputs.edLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                  ((ML2Reduction.outerLoss Rout : ENNReal)
                    * (Cstar * ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
                        / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ))
                          ^ ML2Spine.spineRung β ϖ ε₁ gain dens m)))
                * (uED.card : ENNReal) ∧
            (uED.card : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b
                  / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ^ (-α)
                * (s''.card : ℝ) ∧
            ∃ ρ : NNReal,
              ML2Reduction.plankScale
                (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a)
                (ML2Spine.spineEps₂ ϖ ε₁) ≤ ρ ∧
              Nonempty (Tube.IsUniformAtScale s''
                (fun j ↦ (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
                  (Tube.gridScale δ (Tube.ssfGridLen δ) b
                    / Tube.gridScale δ (Tube.ssfGridLen δ) a) Yτ' j).toTube) ρ
                (Tube.uniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) ^ 2)
                (Tube.uniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) := by
  classical
  have hsp := ML2Spine.spineRung_isSpine hβ0 hβ1 hϖ hε₁ hgain hdens
  have he0 : 0 < ML2Spine.spineDiv ϖ ε₁ := hsp.div_pos
  have hε₂0 : 0 ≤ ML2Spine.spineEps₂ ϖ ε₁ := (ML2Spine.spineEps₂_pos hϖ hε₁).le
  have hε₂1 : ML2Spine.spineEps₂ ϖ ε₁ ≤ 1 := ML2Spine.spineEps₂_le_half.trans (by norm_num)
  -- the crude cardinality exponent at the rescaled scale
  set K₀ : ℕ := ⌈4 / ML2Spine.spineDiv ϖ ε₁⌉₊ with hK₀
  have hK₀e : 4 ≤ ML2Spine.spineDiv ϖ ε₁ * (K₀ : ℝ) := by
    have h := Nat.le_ceil (4 / ML2Spine.spineDiv ϖ ε₁)
    rw [hK₀]
    rw [div_le_iff₀ he0] at h
    linarith
  obtain ⟨δ₁, hδ₁0, hδ₁1, hmain⟩ :=
    exists_edUniform_of_rescaled.{u} hε₂0 hε₂1 K₀ hα
  -- the threshold on `δ`: `δ^{e} ≤ min δ₁ (1/4)`
  have hinv0 : (0 : ℝ) < 1 / ML2Spine.spineDiv ϖ ε₁ := by positivity
  refine ⟨min (δ₁ ^ (1 / ML2Spine.spineDiv ϖ ε₁)) ((1 / 4 : NNReal) ^ (1 / ML2Spine.spineDiv ϖ ε₁)),
    lt_min (NNReal.rpow_pos hδ₁0) (NNReal.rpow_pos (by norm_num)), ?_⟩
  intro δ Cu hδ0 hδδ₀ ι u T 𝒰 Cstar a b m hwin hcardu Rout hRout hR1 hRC v tτ' htτ jθ hjθ Yτ' Yθ
    hYτ' hYθ
  have hpow : ∀ c : NNReal, δ ≤ c ^ (1 / ML2Spine.spineDiv ϖ ε₁) →
      δ ^ ML2Spine.spineDiv ϖ ε₁ ≤ c := by
    intro c hc
    calc δ ^ ML2Spine.spineDiv ϖ ε₁ ≤ (c ^ (1 / ML2Spine.spineDiv ϖ ε₁)) ^ ML2Spine.spineDiv ϖ ε₁ :=
          NNReal.rpow_le_rpow hc he0.le
      _ = c := by
          rw [← NNReal.rpow_mul, one_div, inv_mul_cancel₀ he0.ne', NNReal.rpow_one]
  have hδe₁ : δ ^ ML2Spine.spineDiv ϖ ε₁ ≤ δ₁ := hpow _ (hδδ₀.trans (min_le_left _ _))
  have hδe4 : δ ^ ML2Spine.spineDiv ϖ ε₁ ≤ 1 / 4 := hpow _ (hδδ₀.trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by
    have h : δ ≤ (1 / 4 : NNReal) ^ (1 / ML2Spine.spineDiv ϖ ε₁) := hδδ₀.trans (min_le_right _ _)
    have h14 : (1 / 4 : NNReal) ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : NNReal) < 4)]
      norm_num
    exact h.trans (NNReal.rpow_le_one h14 hinv0.le)
  have hquarter : ((δ ^ ML2Spine.spineDiv ϖ ε₁ : NNReal) : ℝ) ≤ 1 / 4 := by
    have := hδe4
    rw [← NNReal.coe_le_coe] at this
    simpa using this
  -- the datum
  obtain ⟨hsitOut, hτθ4, hsep, hsubOut, hball, hmax, -, -⟩ :=
    exists_rescaledMiddleDatum (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain) (dens := dens)
      hδ0 hδ1 𝒰 hwin hquarter hRout hR1 hRC v htτ hjθ hYτ' hYθ
  refine ⟨hsitOut, ?_⟩
  -- the rescaled scale is below the uniformiser's threshold
  have hδt0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a :=
    hsitOut.pos_out
  have hδtδ₁ : Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a
      ≤ δ₁ := hsep.trans hδe₁
  -- the crude cardinality bound at the rescaled scale
  have hcardfib :
      ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)).card : ℝ)
      ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b
          / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ^ (-(K₀ : ℝ)) := by
    have h1 : ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι).card
        ≤ u.card :=
      le_trans (Finset.card_le_card (Finset.filter_subset _ _))
        (le_trans (Finset.card_le_card htτ)
          (card_activeNodes_le_card (E := EuclideanSpace ℝ (Fin 3)) 𝒰.cover.toChain b))
    have h2 : (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) := by
      have := hcardu
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow] at this
      simpa using this
    have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
    have hδr1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
    have hδtr0 : (0 : ℝ) < ((Tube.gridScale δ (Tube.ssfGridLen δ) b
        / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) := hδt0
    have hsepr : ((Tube.gridScale δ (Tube.ssfGridLen δ) b
        / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ)
        ≤ (δ : ℝ) ^ ML2Spine.spineDiv ϖ ε₁ := by
      have := hsep
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow] at this
      exact this
    -- `δ̃^{K₀} ≤ δ^{e K₀} ≤ δ^{4}`
    have h3 : ((Tube.gridScale δ (Tube.ssfGridLen δ) b
        / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ^ (K₀ : ℝ)
        ≤ (δ : ℝ) ^ (4 : ℝ) := by
      calc ((Tube.gridScale δ (Tube.ssfGridLen δ) b
            / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ^ (K₀ : ℝ)
          ≤ ((δ : ℝ) ^ ML2Spine.spineDiv ϖ ε₁) ^ (K₀ : ℝ) :=
            Real.rpow_le_rpow hδtr0.le hsepr (by positivity)
        _ = (δ : ℝ) ^ (ML2Spine.spineDiv ϖ ε₁ * (K₀ : ℝ)) := by
            rw [← Real.rpow_mul hδr.le]
        _ ≤ (δ : ℝ) ^ (4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hδr hδr1 hK₀e
    calc ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)).card : ℝ)
        ≤ (u.card : ℝ) := by exact_mod_cast h1
      _ ≤ (δ : ℝ) ^ (-(4 : ℝ)) := h2
      _ = ((δ : ℝ) ^ (4 : ℝ))⁻¹ := Real.rpow_neg hδr.le _
      _ ≤ (((Tube.gridScale δ (Tube.ssfGridLen δ) b
            / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ^ (K₀ : ℝ))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos hδtr0 _) h3
      _ = ((Tube.gridScale δ (Tube.ssfGridLen δ) b
            / Tube.gridScale δ (Tube.ssfGridLen δ) a : NNReal) : ℝ) ^ (-(K₀ : ℝ)) :=
          (Real.rpow_neg hδtr0.le _).symm
  obtain ⟨uED, huED, s'', hs'', hEDu, hEDs, hcardED, hret, ρ, hρ, hPS⟩ :=
    hmain hδt0 hδtδ₁ ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
      (ML2Reduction.outerFamily hsitOut.pos_ambient (Yθ jθ).toTube hRout
        (Tube.gridScale δ (Tube.ssfGridLen δ) b / Tube.gridScale δ (Tube.ssfGridLen δ) a) Yτ')
      hball hmax hcardfib
  exact ⟨uED, huED, s'', hs'', hEDu, hEDs, hcardED, hret, ρ, hρ, hPS⟩

end Composed

end Kakeya.ML2Core

end
