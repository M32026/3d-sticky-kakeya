/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleResidues
public import Kakeya.DimensionThree.MainLemma2.AScaleRounding
public import Kakeya.DimensionThree.MainLemma2.AScaleInterface
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# Guardrails for the two Section-3/Section-5 residues of the scale-`r` layer

`Kakeya.DimensionThree.MainLemma2.AScaleResidues` carries two scale estimates. This file records counterexamples to stronger variants and checks the hypotheses needed for the quantitative estimates.

The file is deliberately part of the `Kakeya` target. An earlier guardrail of exactly this
kind lived outside the build and was deleted without anything failing.

## Contents

* `Kakeya.VeryNotSticky.rescaleDensity` — the symmetry `(lam, Cd) ↦ (t·lam, t·Cd)`, `1 ≤ t`,
  of `Kakeya.VeryNotSticky`. It is the reason the pair `(lam, Cd)` is pinned by the structure
  only through the combination `Cd⁻¹ · lam`, and hence the reason both the field
  `Kakeya.VeryNotSticky.lam_ge` and the fullness conjunct of
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` are stated the way they are.
* `Kakeya.VeryNotSticky.CoarseShadedFamilyStatement` and
  `Kakeya.VeryNotSticky.coarseShadedFamilyStatement_uninhabits` — the **refuted** earlier form
  of `exists_coarseShadedFamilyAtGrid`, whose fullness conjunct read
  `C⁻¹ · lam ≤ λ(𝕋_ρ, Y_{𝕋_ρ})` at the bare `lam`. Since
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` that conjunct read
  `lam ≤ λ(𝕋_ρ, Y_{𝕋_ρ}) ≤ 1` against the unconditional `Kakeya.ShadedBody.fullness_le_one`,
  and `rescaleDensity` pushes `lam` past `1`. The theorem derives `False` from that statement
  together with *any* `cfg : VeryNotSticky`.
* `Kakeya.VeryNotSticky.RepairedCoarseShadedFamilyStatement` and the `example` below it — the
  tripwire for the repaired form. It fails to typecheck the moment the fullness conjunct of
  `exists_coarseShadedFamilyAtGrid` changes.
* `Kakeya.VeryNotSticky.repaired_small_side_rescaleDensity_invariant` — the mechanical check
  that the repaired small side `(Cd · C)⁻¹ · lam` is `rescaleDensity`-invariant, i.e. that the
  refutation vector above really is closed.
* `Kakeya.VeryNotSticky.CoarseKatzTaoStatement` and
  `Kakeya.VeryNotSticky.coarseKatzTao_refutes` — the `ν`-uniformity defect of
  `Kakeya.VeryNotSticky.coarseKatzTaoBound`, which is stated without an upper accuracy budget: the `example` below
  `CoarseKatzTaoStatement` checks that the `Prop` refuted there is verbatim the one
  `AScaleResidues` still declares. The right-hand side is `q^ν · K` with `q < 1` and `ν`
  bounded only below, so it tends to `0` while the multiplicity does not move. The repair is
  the pair of thresholds of blueprint `genKKT`, which the proved
  `Kakeya.VeryNotSticky.coarseKatzTaoBound_of_scaleBudget` does carry.
* `Kakeya.VeryNotSticky.fullyShadedNodeFamily`,
  `Kakeya.VeryNotSticky.fullness_fullyShadedNodeFamily` and
  `Kakeya.VeryNotSticky.coarseKatzTao_refutes_config` — the same refutation with **no instance
  data left to supply**. `coarseKatzTao_refutes` asks its caller for a hierarchy, a grid index,
  a coarse family, a fullness hypothesis, a finite maximal density and a positive multiplicity;
  all six are built here out of `cfg` alone, so the refutation reads: *no
  `Kakeya.VeryNotSticky` configuration with `δ < 1` and `β < 1/2` can exist if
  `coarseKatzTaoBound` holds.* Since `Kakeya.VeryNotSticky.exists_setup_caseSideData` produces
  exactly such a configuration, at `cfg.β = β` and `cfg.δ = δ` for every `β ∈ (0, 1]` and every
  small `δ`, and `Kakeya.katzTaoEstimateDimensionThree` drives `β` down through `1/2`, the
  statement `AScaleResidues` declares is not merely `ν`-non-uniform: it contradicts the route
  it is a residue of.
* `Kakeya.VeryNotSticky.activeTubeNode_carrier_subset_closedBall_four` and
  `Kakeya.VeryNotSticky.node_carrier_not_subset_closedBall_one` — why the *proved* replacement
  `Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` requires additional hypotheses to be substituted into its consumer.
  That theorem asks for unit-ball containment of the outer bodies, i.e. of the node tubes of the
  hierarchy; the sharpest containment the hierarchy bundle supports is at radius `4`, and the
  second declaration exhibits a `Tube.UniformTubeSet` over a `δ`-tube in `B_1` whose node
  at *every* grid index `k < N` leaves `B_1`. So that hypothesis is unsuppliable at the consumer,
  and rewiring `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` onto the replacement needs a
  windowed Katz–Tao multiplicity bound that the development does not have.
* `Kakeya.VeryNotSticky.rScaleParentData_gain_mono` — the consumer of the refuted statement is
  *not* itself refutable by the `ν`-uniformity argument: `ν` enters its conclusion only through
  `δ^{-ν/90}` on the large side of one conjunct, so the conclusion only weakens as `ν` grows.
-/

@[expose] public section

universe u

open MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

/-! ## The density rescaling symmetry -/

/-- The rescaling `(lam, Cd) ↦ (t·lam, t·Cd)` of a `VeryNotSticky` configuration, `1 ≤ t`.
Every other field is untouched. The two shading clauses survive because `shading_lb` depends on
`(lam, Cd)` only through the scale-invariant combination `Cd⁻¹ · lam`, and `shading_ub` only
weakens; `lam_ge` survives because it too is `δ^{2η} ≤ Cd⁻¹ · lam` cleared of the inverse.

Consequence: no statement about a `VeryNotSticky` configuration may read the bare `lam`, since
`lam` alone is not a quantity of the data. -/
noncomputable def rescaleDensity (cfg : VeryNotSticky.{u}) (t : NNReal) (ht : 1 ≤ t) :
    VeryNotSticky.{u} :=
  { cfg with
    lam := t * cfg.lam
    Cd := t * cfg.Cd
    hCd := le_trans cfg.hCd (le_mul_of_one_le_left zero_le' ht)
    lam_ge := by
      rw [mul_assoc]
      exact mul_le_mul' le_rfl cfg.lam_ge
    shading_lb := by
      intro i hi
      have ht0 : ((t : ENNReal)) ≠ 0 := by
        simpa using (lt_of_lt_of_le zero_lt_one ht).ne'
      refine le_trans (le_of_eq ?_) (cfg.shading_lb i hi)
      have key : ∀ v : ENNReal,
          (t : ENNReal)⁻¹ * ((cfg.Cd : NNReal) : ENNReal)⁻¹ *
              ((t : ENNReal) * ((cfg.lam : NNReal) : ENNReal) * v)
            = (((cfg.Cd : NNReal) : ENNReal))⁻¹ * (((cfg.lam : NNReal) : ENNReal) * v) := by
        intro v
        rw [show (t : ENNReal)⁻¹ * ((cfg.Cd : NNReal) : ENNReal)⁻¹ *
              ((t : ENNReal) * ((cfg.lam : NNReal) : ENNReal) * v)
            = ((t : ENNReal)⁻¹ * (t : ENNReal)) *
              ((((cfg.Cd : NNReal) : ENNReal))⁻¹ * (((cfg.lam : NNReal) : ENNReal) * v)) from
          by ring, ENNReal.inv_mul_cancel ht0 ENNReal.coe_ne_top, one_mul]
      push_cast
      rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), key]
    shading_ub := by
      intro i hi
      have ht' : (1 : ENNReal) ≤ (t : ENNReal) := by exact_mod_cast ht
      refine le_trans (cfg.shading_ub i hi) ?_
      push_cast
      exact mul_le_mul' (le_mul_of_one_le_left zero_le' ht')
        (mul_le_mul' (le_mul_of_one_le_left zero_le' ht') le_rfl) }

@[simp] theorem rescaleDensity_lam (cfg : VeryNotSticky.{u}) (t : NNReal) (ht : 1 ≤ t) :
    (cfg.rescaleDensity t ht).lam = t * cfg.lam := rfl

@[simp] theorem rescaleDensity_Cd (cfg : VeryNotSticky.{u}) (t : NNReal) (ht : 1 ≤ t) :
    (cfg.rescaleDensity t ht).Cd = t * cfg.Cd := rfl

/-! ## The `rho_count` window

`Kakeya.VeryNotSticky.rho_count` is asserted over `Set.Icc (δ^(1-exscalb)) (δ^exscalb)`.
For `δ < 1` the map `t ↦ δ^t` is strictly antitone, so that interval is **empty** exactly when
`1/2 < exscalb`, and the field then says nothing at all.

Nothing in `Kakeya.VeryNotSticky` excludes that. The clause `exscal < 1/2` lives on
`Kakeya.VeryNotSticky.CaseParams.scale`, which is a separate bundle, and the configuration
carries only `hscale : exscal = exscalb` and the two positivity fields. So the tube-counting
hypothesis of blueprint `lemmain2vns` is carried by the configuration only in the presence of
`CaseParams`; every consumer that needs it must take `CaseParams` too, and every *producer* of
a configuration must supply `exscal < 1/2` for the field to have content.

`Kakeya.VeryNotSticky.exists_setup_caseSideData`, the sole producer, does take `params`, so it
is in the non-vacuous regime; `rho_count_nonvacuous_of_caseParams` below is the check. -/

/-- **`rho_count` is vacuous above `exscalb = 1/2`.** For `δ < 1` and `1/2 < exscalb` the
window of `Kakeya.VeryNotSticky.rho_count` is empty. -/
theorem rho_count_window_eq_empty (cfg : VeryNotSticky.{u}) (hδ : cfg.δ < 1)
    (h : 1 / 2 < cfg.exscalb) :
    Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) = ∅ := by
  refine Set.Icc_eq_empty (not_le.2 ?_)
  exact NNReal.rpow_lt_rpow_of_exponent_gt cfg.hδ hδ (by linarith)

/-- Consequently the field carries no information there: it follows from nothing. -/
theorem rho_count_of_half_lt_exscalb (cfg : VeryNotSticky.{u}) (hδ : cfg.δ < 1)
    (h : 1 / 2 < cfg.exscalb) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) →
      ∀ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ cfg.s, ∃ j ∈ tρ, (cfg.T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - cfg.ζ) ≤ (tρ.card : ℝ) := by
  intro ρ hρ
  rw [rho_count_window_eq_empty cfg hδ h] at hρ
  exact absurd hρ (Set.notMem_empty ρ)

/-- **In the presence of `CaseParams` the window is nonempty**, so the field does have content
for every configuration the sole producer
`Kakeya.VeryNotSticky.exists_setup_caseSideData` emits. -/
theorem rho_count_nonvacuous_of_caseParams (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') :
    (cfg.δ ^ cfg.exscalb) ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) := by
  refine ⟨?_, le_rfl⟩
  have hs : cfg.exscalb < 1 / 2 := cfg.hscale ▸ params.scale
  rcases eq_or_lt_of_le cfg.hδ1 with h1 | h1
  · simp [h1]
  · exact le_of_lt (NNReal.rpow_lt_rpow_of_exponent_gt cfg.hδ h1 (by linarith))

/-! ## The refuted form of the Section-5 residue -/

/-- The **earlier, refuted** statement of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`,
with all binders explicit: the fullness conjunct at the bare `cfg.lam`. -/
def CoarseShadedFamilyStatement : Prop :=
  ∀ (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ), k ≤ Tube.ssfGridLen cfg.δ →
    ∀ (ρ : NNReal), Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
    ρ ∈ Set.Icc cfg.δ 1 →
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))

/-- **Refutation.** The earlier statement of `exists_coarseShadedFamilyAtGrid` implies that
`Kakeya.VeryNotSticky` is uninhabited, so it may never be restored.

`rescaleDensity` sends `lam` past `1` while every hypothesis survives, and
`Kakeya.ShadedBody.fullness_le_one` is unconditional. -/
theorem coarseShadedFamilyStatement_uninhabits
    (H : CoarseShadedFamilyStatement.{u}) (cfg : VeryNotSticky.{u}) : False := by
  have hCd0 : (0 : NNReal) < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
  have hlam0 : cfg.lam ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (mul_pos hCd0 (NNReal.rpow_pos cfg.hδ)) cfg.lam_ge)
  set t : NNReal := max 1 (2 * cfg.lam⁻¹) with ht_def
  have ht : 1 ≤ t := le_max_left _ _
  have h2 : (2 : NNReal) ≤ t * cfg.lam := by
    calc (2 : NNReal) = 2 * cfg.lam⁻¹ * cfg.lam := by
          rw [mul_assoc, inv_mul_cancel₀ hlam0, mul_one]
      _ ≤ t * cfg.lam := by gcongr; exact le_max_right _ _
  obtain ⟨𝒱⟩ := (cfg.rescaleDensity t ht).uniform
  obtain ⟨G, -, -, -, -, hfull, -⟩ :=
    H (cfg.rescaleDensity t ht) 𝒱 0 (Nat.zero_le _) 1 (Tube.gridScale_zero _ _)
      ⟨(cfg.rescaleDensity t ht).hδ1, le_rfl⟩
  rw [rescaleDensity_lam] at hfull
  simp only [shadingMultiplicityEstimateForRhoTubes.C, inv_one, one_mul] at hfull
  have : (2 : NNReal) ≤ 1 :=
    le_trans h2 (le_trans hfull (ShadedBody.fullness_le_one _ _))
  norm_num at this

/-! ## The repaired form, and the tripwire -/

/-- The **current** statement of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`, with
all binders explicit. The only difference from `CoarseShadedFamilyStatement` is the `cfg.Cd` on
the small side of the fullness conjunct, which is exactly the constant carried by the proved
deliverer `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`. -/
def RepairedCoarseShadedFamilyStatement : Prop :=
  ∀ (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ), k ≤ Tube.ssfGridLen cfg.δ →
    ∀ (ρ : NNReal), Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
    ρ ∈ Set.Icc cfg.δ 1 →
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))

/-- The **current** statement of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`, at the
honest dimensional loss `ShadedBody.rhoTubesInducedFullnessLoss 3` in place of the placeholder
numeral `1`.

GWZ §9.3 writes the fullness conclusion of Lemma 5.11 as `λ(𝕋_a, Y_{𝕋_a}) ⪆ λ`, and §2.2 p. 3
defines `⪆` as permitting a sub-polynomial factor, so a loss is faithful and demanding none was
stricter than the source.  `RepairedCoarseShadedFamilyStatement` above records the placeholder
shape; `Kakeya.VeryNotSticky.honestCoarseShadedFamilyStatement_of_repaired` below shows this one
is the weaker of the two, so the swap discards no strength any consumer had.

The loss is *purely dimensional* — it depends on neither `δ` nor `|𝕋|` — which is what keeps
`Kakeya.aScaleDataConstant` a closed term fixable before `δ`, and hence keeps the quantifier
order that `Kakeya.VeryNotSticky.aScaleData_absorb` depends on.  A `δ`-dependent loss such as
`Kakeya.VeryNotSticky.coarseLoss` would not. -/
def HonestCoarseShadedFamilyStatement : Prop :=
  ∀ (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ), k ≤ Tube.ssfGridLen cfg.δ →
    ∀ (ρ : NNReal), Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
    ρ ∈ Set.Icc cfg.δ 1 →
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))

/-- **The placeholder shape implies the honest one.**  The two conjuncts that changed both carry
the constant on their *small* side, through its inverse, and `1 ≤ L`; so weakening the constant
weakens the statement and nothing that used the old strength is silently lost. -/
theorem honestCoarseShadedFamilyStatement_of_repaired
    (h : RepairedCoarseShadedFamilyStatement.{u}) : HonestCoarseShadedFamilyStatement.{u} := by
  intro cfg 𝒱 k hk ρ hgrid hρ
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := h cfg 𝒱 k hk ρ hgrid hρ
  have hL1 : (1 : NNReal) ≤ _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 :=
    _root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3
  have hCd0 : (0 : NNReal) < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
  refine ⟨G, h1, h2, h3, h4, ?_, ?_⟩
  · refine le_trans ?_ h5
    have hpos : (0 : NNReal) < cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C := by
      rw [shadingMultiplicityEstimateForRhoTubes.C, mul_one]
      exact hCd0
    have hle : cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C
        ≤ cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 := by
      rw [shadingMultiplicityEstimateForRhoTubes.C, mul_one]
      exact le_mul_of_one_le_right bot_le hL1
    exact mul_le_mul_right' (inv_anti₀ hpos hle) cfg.lam
  · intro x hx
    refine le_trans ?_ (h6 x hx)
    have hinv : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹
        ≤ ((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ := by
      refine ENNReal.inv_le_inv.2 ?_
      rw [shadingMultiplicityEstimateForRhoTubes.C]
      exact_mod_cast hL1
    gcongr

/-- **Tripwire.** `exists_coarseShadedFamilyAtGrid` still states the honest `Prop`.
Reverting the fullness conjunct to `CoarseShadedFamilyStatement`, which
`coarseShadedFamilyStatement_uninhabits` refutes, breaks this line; so does reverting the loss
constant to the placeholder numeral `1`, which is stricter than GWZ's `⪆` and which
`RepairedCoarseShadedFamilyStatement` above retains as a record. -/
example : HonestCoarseShadedFamilyStatement.{u} := @exists_coarseShadedFamilyAtGrid.{u}

/-- **The repair closes the refutation vector.** The repaired small side is invariant under
`rescaleDensity`, so the argument of `coarseShadedFamilyStatement_uninhabits` no longer
applies. -/
theorem repaired_small_side_rescaleDensity_invariant
    (cfg : VeryNotSticky.{u}) (t : NNReal) (ht : 1 ≤ t) :
    ((cfg.rescaleDensity t ht).Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ *
        (cfg.rescaleDensity t ht).lam
      = (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam := by
  have ht0 : t ≠ 0 := (lt_of_lt_of_le zero_lt_one ht).ne'
  show (t * cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * (t * cfg.lam)
      = (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam
  rw [show t * cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C
        = t * (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C) by ring, mul_inv]
  field_simp

/-! ## The `ν`-uniformity defect of the Section-3 residue

Unlike the Section-5 residue above this one is **not** repaired; the statement in
`AScaleResidues` is still the refuted one, and the `example` below is what keeps that visible.
-/

/-- The exact current statement of `Kakeya.VeryNotSticky.coarseKatzTaoBound`, all binders
explicit.

The fullness hypothesis is at `δ^{2η}`, matching the repaired
`Kakeya.VeryNotSticky.lam_ge`; see that field's docstring. The `ν`-uniformity defect refuted
below is untouched by that change — the refutation supplies `hfull`, and a weaker `hfull`
requirement only makes it easier. -/
def CoarseKatzTaoStatement : Prop :=
  ∀ (cfg : VeryNotSticky.{u}) (ν : ℝ), 0 < ν → 90 * cfg.η ≤ ν →
    ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
        (Tube.ssfGridLen cfg.δ) cfg.C₀)
      (k : ℕ), k ≤ Tube.ssfGridLen cfg.δ →
    ∀ (ρ : NNReal), Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
      ρ ∈ Set.Icc cfg.a 1 →
    ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
      G.outerSet = cfg.activeTubeNodes 𝒰 k →
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody) →
      (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody →
      ShadedBody.multiplicity G.outerSet G.outerBody ≤
        (cfg.a : ENNReal) ^ (-(ν / 90)) *
          ((cfg.δ : ENNReal) ^ (ν / 45) *
              ((cfg.δ : ENNReal) ^ cfg.η *
                maxDensity (cfg.activeTubeNodes 𝒰 k)
                  (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
            (1 - cfg.β) *
          (G.outerSet.card : ENNReal) ^ cfg.β

/-! **The tripwire is gone with the declaration it pinned.**  It read
`example : CoarseKatzTaoStatement := @coarseKatzTaoBound`, and it cannot survive the removal of
`Kakeya.VeryNotSticky.coarseKatzTaoBound`, which was **false**.  Its replacement is
`Kakeya.VeryNotSticky.statement_of_universal_coarseKatzTao_false`
(`Kakeya.DimensionThree.MainLemma2.CoarseKatzTaoRepair`), which says outright that the `Prop`
below is false — strictly more than the tripwire said.  `CoarseKatzTaoStatement` and
`Kakeya.VeryNotSticky.coarseKatzTao_refutes_config` are unchanged. -/

/-- The right-hand side of `coarseKatzTaoBound` is `q ^ ν * K` with `q` and `K` independent
of `ν`; this is the algebraic form of the `ν`-uniformity defect. -/
theorem coarseKatzTao_rhs_eq (cfg : VeryNotSticky.{u}) {ν : ℝ} (hν0 : 0 ≤ ν)
    (X card : ENNReal) :
    (cfg.a : ENNReal) ^ (-(ν / 90)) * ((cfg.δ : ENNReal) ^ (ν / 45) * X) ^ (1 - cfg.β) *
        card ^ cfg.β
      = ((cfg.a : ENNReal) ^ (-(1 / 90 : ℝ)) *
            ((cfg.δ : ENNReal) ^ (1 / 45 : ℝ)) ^ (1 - cfg.β)) ^ ν *
          (X ^ (1 - cfg.β) * card ^ cfg.β) := by
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hν0]
  have hA : (cfg.a : ENNReal) ^ (-(ν / 90))
      = ((cfg.a : ENNReal) ^ (-(1 / 90 : ℝ))) ^ ν := by
    rw [← ENNReal.rpow_mul]; ring_nf
  have hB : ((cfg.δ : ENNReal) ^ (ν / 45)) ^ (1 - cfg.β)
      = (((cfg.δ : ENNReal) ^ (1 / 45 : ℝ)) ^ (1 - cfg.β)) ^ ν := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]; ring_nf
  rw [hA, hB]
  ring

/-- `q < 1` in the regime `β < 1/2`, `δ < 1`: it follows from `cfg.hdims` alone
(`δ ≤ a`), so no extra data is needed. -/
theorem coarseKatzTao_q_lt_one (cfg : VeryNotSticky.{u}) (hδlt : cfg.δ < 1)
    (hβ : cfg.β < 1 / 2) :
    (cfg.a : ENNReal) ^ (-(1 / 90 : ℝ)) *
        ((cfg.δ : ENNReal) ^ (1 / 45 : ℝ)) ^ (1 - cfg.β) < 1 := by
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by simpa using cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδa : (cfg.δ : ENNReal) ≤ (cfg.a : ENNReal) := by
    exact_mod_cast cfg.hdims.1
  have hstep : (cfg.a : ENNReal) ^ (-(1 / 90 : ℝ)) ≤ (cfg.δ : ENNReal) ^ (-(1 / 90 : ℝ)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hδa (by norm_num))
  refine lt_of_le_of_lt (mul_le_mul_right' hstep _) ?_
  have hcollapse : (cfg.δ : ENNReal) ^ (-(1 / 90 : ℝ)) *
      ((cfg.δ : ENNReal) ^ (1 / 45 : ℝ)) ^ (1 - cfg.β)
      = (cfg.δ : ENNReal) ^ ((1 - 2 * cfg.β) / 90) := by
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ hδ0 hδtop]
    congr 1
    ring
  rw [hcollapse]
  exact ENNReal.rpow_lt_one (by exact_mod_cast hδlt) (by linarith)

/-- **The `ν`-uniformity defect of `coarseKatzTaoBound`, compiler-checked.**

In the regime `δ < 1`, `β < 1/2` the statement of `coarseKatzTaoBound` is inconsistent with the
existence of *any* instance of its own hypotheses carrying a positive multiplicity and a finite
maximal density. The reason is structural: `ν` is universally quantified subject only to
`0 < ν` and `90 η ≤ ν`, while the right-hand side is `q ^ ν * K` with `q < 1` — so it tends to
`0` along `ν → ∞` while the left-hand side does not move. The thresholds `ρ₀(ν)`, `ηKT(ν)`
and the budget of `Kakeya.VeryNotSticky.coarseKatzTaoBound_of_scaleBudget`, which are exactly
what makes the true statement *not* `ν`-uniform, are missing. -/
theorem coarseKatzTao_refutes
    (H : CoarseKatzTaoStatement.{u}) (cfg : VeryNotSticky.{u})
    (hδlt : cfg.δ < 1) (hβ : cfg.β < 1 / 2)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (ρ : NNReal) (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.a 1)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody)
    (hmd : maxDensity (cfg.activeTubeNodes 𝒰 k)
      (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) ≠ ⊤)
    (hmult : 0 < ShadedBody.multiplicity G.outerSet G.outerBody) :
    False := by
  classical
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  set X : ENNReal := (cfg.δ : ENNReal) ^ cfg.η * md with hX_def
  set K : ENNReal := X ^ (1 - cfg.β) * (G.outerSet.card : ENNReal) ^ cfg.β with hK_def
  set q : ENNReal := (cfg.a : ENNReal) ^ (-(1 / 90 : ℝ)) *
      ((cfg.δ : ENNReal) ^ (1 / 45 : ℝ)) ^ (1 - cfg.β) with hq_def
  have hq1 : q < 1 := coarseKatzTao_q_lt_one cfg hδlt hβ
  have hqtop : q ≠ ⊤ := (lt_of_lt_of_le hq1 le_top).ne
  have hXtop : X ≠ ⊤ := by
    rw [hX_def]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (le_of_lt cfg.hη) ENNReal.coe_ne_top
      |> fun h => h) hmd
  have hKtop : K ≠ ⊤ := by
    rw [hK_def]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hβ1m hXtop)
      (ENNReal.rpow_ne_top_of_nonneg (le_of_lt cfg.hβ) (by simp))
  have key : ∀ N : ℕ, 0 < (N : ℝ) → 90 * cfg.η ≤ (N : ℝ) →
      ShadedBody.multiplicity G.outerSet G.outerBody ≤ q ^ N * K := by
    intro N hN0 hNη
    have := H cfg (N : ℝ) hN0 hNη 𝒰 k hk ρ hgrid hρ G houterSet houterBody hfull
    rw [coarseKatzTao_rhs_eq cfg (le_of_lt hN0) X ((G.outerSet.card : ENNReal))] at this
    rw [← hq_def, ← hK_def, ENNReal.rpow_natCast q N] at this
    exact this
  obtain ⟨N₀, hN₀1, hN₀η⟩ : ∃ N : ℕ, 0 < (N : ℝ) ∧ 90 * cfg.η ≤ (N : ℝ) := by
    refine ⟨⌈90 * cfg.η⌉₊ + 1, ?_, ?_⟩
    · positivity
    · exact le_trans (Nat.le_ceil _) (by push_cast; linarith)
  have hmulttop : ShadedBody.multiplicity G.outerSet G.outerBody ≠ ⊤ := by
    intro h
    have := key N₀ hN₀1 hN₀η
    rw [h, top_le_iff] at this
    exact (ENNReal.mul_ne_top (ENNReal.pow_ne_top hqtop) hKtop) this
  set m : NNReal := (ShadedBody.multiplicity G.outerSet G.outerBody).toNNReal with hm_def
  set q' : NNReal := q.toNNReal with hq'_def
  set K' : NNReal := K.toNNReal with hK'_def
  have hmc : ((m : NNReal) : ENNReal) = ShadedBody.multiplicity G.outerSet G.outerBody :=
    ENNReal.coe_toNNReal hmulttop
  have hqc : ((q' : NNReal) : ENNReal) = q := ENNReal.coe_toNNReal hqtop
  have hKc : ((K' : NNReal) : ENNReal) = K := ENNReal.coe_toNNReal hKtop
  have hm0 : 0 < m := by
    have : (0 : ENNReal) < ((m : NNReal) : ENNReal) := by rw [hmc]; exact hmult
    exact_mod_cast this
  have hq'1 : q' < 1 := by
    have : ((q' : NNReal) : ENNReal) < 1 := by rw [hqc]; exact hq1
    exact_mod_cast this
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := m / (K' + 1))
    (by positivity) hq'1
  refine absurd (key (max n N₀) ?_ ?_) (not_le.2 ?_)
  · have : (N₀ : ℝ) ≤ (max n N₀ : ℕ) := by exact_mod_cast Nat.le_max_right n N₀
    linarith
  · have : (N₀ : ℝ) ≤ (max n N₀ : ℕ) := by exact_mod_cast Nat.le_max_right n N₀
    linarith
  · rw [← hmc, ← hqc, ← hKc, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_lt_coe]
    have hmono : q' ^ (max n N₀) ≤ q' ^ n :=
      pow_le_pow_of_le_one (zero_le') hq'1.le (Nat.le_max_left n N₀)
    have hK'1 : K' ≤ K' + 1 := le_self_add
    calc q' ^ (max n N₀) * K' ≤ q' ^ n * (K' + 1) := by
            exact mul_le_mul' hmono hK'1
      _ < (m / (K' + 1)) * (K' + 1) := by
            refine mul_lt_mul_of_pos_right hn ?_
            positivity
      _ = m := by
            field_simp

/-! ### The `ν`-uniformity defect with no instance data left to supply

`Kakeya.VeryNotSticky.coarseKatzTao_refutes` above leaves six things to its caller: a
hierarchy `𝒰`, a grid index `k`, the scale `ρ`, a coarse shaded family `G` matching the node
family at `k`, the fullness hypothesis, and the two nondegeneracy facts `maxDensity ≠ ⊤` and
`0 < multiplicity`. Each of the six is available from `cfg` itself, and the three declarations
below supply them, so that the refutation becomes a statement about the configuration alone.
-/

/-- **The node family of the hierarchy at grid level `k`, shaded by the whole of each node
tube.** The inner layer is empty, which is all the refutation needs: the three
`ShadedFactorFamily` clauses relating inner to outer are then vacuous, and every hypothesis of
`Kakeya.VeryNotSticky.CoarseKatzTaoStatement` reads only the outer layer.

This is *not* the family that a proof of blueprint `genKKT` would work with — it is the
cheapest family satisfying that statement's hypotheses, and its only role is to witness that
those hypotheses are satisfiable. -/
noncomputable def fullyShadedNodeFamily (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι where
  innerSet := ∅
  innerBody := fun i ↦ (cfg.T i).toShadedBody
  outerSet := cfg.activeTubeNodes 𝒰 k
  outerBody := fun j ↦
    { toConvexSpaceBody := (𝒰.cover.tube k j).toConvexSpaceBody
      shade := (𝒰.cover.tube k j).carrier
      measurableSet_shade :=
        ((𝒰.cover.tube k j).toConvexSpaceBody.isCompact).isClosed.measurableSet
      shade_subset := subset_rfl }
  parent := 𝒰.cover.assign k
  parent_mem := by simp
  inner_le_parent := by simp
  shade_subset_parent := by simp

/-- Every node tube of the hierarchy has positive volume, by the dimensional lower bound
`Tube.le_volume` at the grid scale `Tube.gridScale cfg.δ _ k`, which is positive
because `cfg.δ` is. -/
theorem volume_nodeTube_pos (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (j : cfg.ι) : 0 < volume ((𝒰.cover.tube k j).carrier) := by
  have h := _root_.Tube.le_volume (𝒰.cover.tube k j)
  refine lt_of_lt_of_le ?_ (by simpa using h)
  have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) :=
    ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)
  have hρ0 : 0 < Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k :=
    Tube.gridScale_pos cfg.hδ _ _
  have hρp : (0 : ENNReal) <
      ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2 :=
    ENNReal.pow_pos (ENNReal.coe_pos.mpr hρ0) _
  exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hρp)

/-- The fully shaded node family is exactly as full as a family can be. In particular it
satisfies the hypothesis `hfull` of `Kakeya.VeryNotSticky.coarseKatzTaoBound` — the hypothesis
whose *absence* was the earlier, and different, defect of that statement — with room to spare,
and it has positive multiplicity, so the refutation below is not testing the estimate at a null
shading. -/
theorem fullness_fullyShadedNodeFamily (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) :
    ShadedBody.fullness (cfg.fullyShadedNodeFamily 𝒰 k).outerSet
      (cfg.fullyShadedNodeFamily 𝒰 k).outerBody = 1 := by
  classical
  set G := cfg.fullyShadedNodeFamily 𝒰 k with hG
  have hshade : ∀ j, (G.outerBody j).shade = (G.outerBody j).carrier := fun _ ↦ rfl
  set X : ENNReal := ∑ j ∈ G.outerSet, volume (G.outerBody j).carrier with hX
  have hXtop : X ≠ ⊤ := by
    rw [hX]
    refine ENNReal.sum_ne_top.mpr fun j _ ↦ ?_
    exact (G.outerBody j).isCompact.measure_lt_top.ne
  have hXne : X ≠ 0 := by
    obtain ⟨j, hj⟩ := activeTubeNodes_nonempty cfg 𝒰 hk (s_nonempty cfg)
    have hjG : j ∈ G.outerSet := hj
    intro h0
    rw [hX, Finset.sum_eq_zero_iff] at h0
    exact absurd (h0 j hjG) (ne_of_gt (volume_nodeTube_pos cfg 𝒰 k j))
  have hone : (ShadedBody.fullness G.outerSet G.outerBody : ENNReal) = 1 := by
    rw [ShadedBody.coe_fullness]
    change (∑ j ∈ G.outerSet, volume (G.outerBody j).shade) /
      (∑ j ∈ G.outerSet, volume (G.outerBody j).carrier) = 1
    have hsum : (∑ j ∈ G.outerSet, volume (G.outerBody j).shade) = X := by
      rw [hX]; exact Finset.sum_congr rfl fun j _ ↦ by rw [hshade j]
    rw [hsum, ← hX]
    exact ENNReal.div_self hXne hXtop
  exact_mod_cast hone

/-- **`Kakeya.VeryNotSticky.coarseKatzTaoBound` is inconsistent with the existence of a
configuration in the regime the section works in.**

`Kakeya.VeryNotSticky.coarseKatzTao_refutes` derives `False` from the statement together with
one instance of its hypotheses. Here the instance is built from `cfg` alone: the hierarchy is
the one `Kakeya.VeryNotSticky.uniform` supplies, the grid index is `k = 0` (so the node scale
is `Tube.gridScale_zero`, `ρ = 1`, which lies in `Set.Icc cfg.a 1` because
`cfg.hdims` gives `cfg.a ≤ cfg.δ ^ cfg.exscal ≤ 1`), the coarse family is
`Kakeya.VeryNotSticky.fullyShadedNodeFamily`, the fullness hypothesis is
`Kakeya.VeryNotSticky.fullness_fullyShadedNodeFamily` against `δ ^ η ≤ 1`, the maximal density
is finite by `Kakeya.maxDensity_ne_top`, and the multiplicity is positive by
`ShadedBody.multiplicity_pos_of_fullness_pos`.

So the open statement of `AScaleResidues` asserts, in the presence of any configuration with
`cfg.δ < 1` and `cfg.β < 1/2`, a contradiction. The two side conditions are not restrictions in
practice: `Kakeya.VeryNotSticky.exists_setup_caseSideData` produces a configuration with
`cfg.β = β` and `cfg.δ = δ` for every `0 < β ≤ 1` and every sufficiently small `δ`, and
`Kakeya.katzTaoEstimateDimensionThree` invokes Main Lemma 2 at every `γ ∈ Set.Ioc 0 1`, hence
at `β < 1/2`.

**What the repair has to be, and what still blocks it.**
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` is the same statement with three
hypotheses added, and it *is* proved. They are `3 cfg.η (1 - cfg.β) ≤ cfg.exscal * (ν / 180)`,
a relation among `β`, `exscal`, `η` and the gain and so of the shape
`Kakeya.VeryNotSticky.CaseParams` carries; `cfg.η ≤ cfg.exscal * ηKT`, which compares `cfg.η`
with a quantity the Katz–Tao estimate *produces* at the loss exponent `ν/180`, so it can only be
carried by a bundle that sees `ν` — `Kakeya.VeryNotSticky.CaseScale`, which is indexed by the
gain, or a binder threaded from `Kakeya.VeryNotSticky.exists_goalMult`; and `ρ ≤ ρ₀` on the
*node* radius, which is not arrangeable by shrinking `cfg.δ`, since the grid scale at `k = 0`
is `1` whatever `δ` is. The last has to arrive as a smallness hypothesis on the nominal radius
`r` of `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` and
`Kakeya.VeryNotSticky.exists_aScaleInputs`, whose current binders allow `r = 1`; both call sites
can in fact supply one, the thick branch from `cfg.a ≤ cfg.δ^{exscal}` and the transverse branch
from the bound `max(3ρ, θb) ≤ 6 δ^{exscal}` that
`Kakeya.VeryNotSticky.transverseFillRadius_le_one` already establishes internally and throws
away.

**A fourth hypothesis used to block the rewiring outright, and it is now gone.** The earlier
form of `coarseKatzTaoBound_of_etaBudget` also asked for unit-ball containment of the outer
bodies, and that hypothesis is unsuppliable at every scale — see
`Kakeya.VeryNotSticky.node_carrier_not_subset_closedBall_one` below, which is retained as the
record of exactly that. What removed it is
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`, the Katz–Tao multiplicity bound
for families in `Metric.closedBall 0 R`; at `R = 4` the containment is *derived* inside
`coarseKatzTaoBound_of_etaBudget` from `Kakeya.MultiScaleFac.node_carrier_subset_ball`, so it is
no longer a binder at all.

**What is left is not plumbing.** `ν` is a *universally quantified* binder of
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`, while `cfg.η` and `cfg.δ` are fields of
`cfg`, fixed before it. So `cfg.η ≤ cfg.exscal * ηKT(ν)` and `ρ ≤ ρ₀(ν)` cannot be supplied by
new fields on `Kakeya.VeryNotSticky` quantified over all `ν > 0`: such fields would assert a
bound uniform in the gain, which is the very defect that makes `coarseKatzTaoBound` false. The
gain has to be bound *before* the configuration — that is what
`Kakeya.VeryNotSticky.CaseScale` is for — and doing so is a restructuring of the case split,
not an edit to this file. -/
theorem coarseKatzTao_refutes_config
    (H : CoarseKatzTaoStatement.{u}) (cfg : VeryNotSticky.{u})
    (hδlt : cfg.δ < 1) (hβ : cfg.β < 1 / 2) : False := by
  classical
  obtain ⟨𝒱⟩ := cfg.uniform
  set 𝒰 := 𝒱.tubeUniform with h𝒰
  set G := cfg.fullyShadedNodeFamily 𝒰 0 with hG
  have ha1 : cfg.a ≤ 1 :=
    le_trans cfg.hdims.2.1
      (le_trans cfg.hdims.2.2 (NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le))
  have hfull1 : ShadedBody.fullness G.outerSet G.outerBody = 1 :=
    fullness_fullyShadedNodeFamily cfg 𝒰 (Nat.zero_le _)
  refine coarseKatzTao_refutes H cfg hδlt hβ 𝒰 0 (Nat.zero_le _) 1
    (Tube.gridScale_zero _ _) ⟨ha1, le_rfl⟩ G rfl (fun j _ ↦ rfl) ?_
    (maxDensity_ne_top _ _) ?_
  · rw [hfull1]
    exact NNReal.rpow_le_one cfg.hδ1 (by linarith [cfg.hη] : (0:ℝ) ≤ 2 * cfg.η)
  · refine ShadedBody.multiplicity_pos_of_fullness_pos _ _ ?_
    rw [hfull1]
    exact zero_lt_one

/-! ### Why the proved replacement requires additional hypotheses to be substituted in

`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` is the refuted statement with four
hypotheses added, and it is proved. Three of the four are the thresholds discussed above. The
fourth is `hball`, unit-ball containment of the *outer* bodies,

`∀ j ∈ G.outerSet, (G.outerBody j).carrier ⊆ closedBall 0 1`,

and it is the one that stops the rewiring of the single consumer
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`, because **that consumer cannot supply
it**. `houterBody` pins each outer body to the node tube `𝒰.cover.tube k j` of the hierarchy,
`𝒰` is a universally quantified `Tube.UniformTubeSet` binder, and that bundle constrains
its nodes only through `Tube.GridCoverSystem.le_tube_assign`: a node must *contain* the
`δ`-tubes assigned to it. Containing a `δ`-tube that lies in `B_1` does not put a `ρ`-tube in
`B_1`; it puts it in `B_{1 + 4ρ}`, and the sharpest bound the development proves is
`Kakeya.MultiScaleFac.node_carrier_subset_ball`, at radius `4`. The two declarations below are
that positive bound and a compiler-checked witness that `1` is *not* available:

* `Kakeya.VeryNotSticky.activeTubeNode_carrier_subset_closedBall_four` — the best containment
  the hierarchy of a configuration gives for its own node tubes;
* `Kakeya.VeryNotSticky.node_carrier_not_subset_closedBall_one` — a `Tube.UniformTubeSet`
  over a single `δ`-tube whose carrier lies in `B_1`, whose node at *every* grid index `k < N`
  fails to lie in `B_1`. So `hball` is not a consequence of the data
  `rScaleParentData_of_gridScale` has, at any scale, and adding it as a binder there would be a
  hypothesis no call site can discharge.

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, and `Kakeya.KatzTaoEstimate` itself,
are stated for tube families in `closedBall 0 1`, and that `1` cannot be moved. Closing the
Section-3 residue therefore needed a *windowed* Katz–Tao multiplicity bound — the estimate at
tube families in `closedBall 0 R`, at the cost of a constant depending on `R` and the dimension.
That bound now exists: `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`
(`Kakeya/PartialEstimatesWindowed.lean`), proved by rescaling the family into the unit ball at
ratio `(4R)⁻¹` and re-tubing by `Tube.centredExtension`. Consequently
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` no longer carries a containment
hypothesis at all: it derives the radius-`4` containment internally. The two declarations below
are kept because they are the record of *why* the windowed bound was needed, and because
`node_carrier_not_subset_closedBall_one` still refutes any future attempt to reinstate the
unit-ball hypothesis.
-/

/-- **The containment the configuration's own hierarchy really gives its node tubes.**

`Kakeya.MultiScaleFac.node_carrier_subset_ball` at the configuration's data: a node tube
contains a `δ`-tube of `cfg.s`, that `δ`-tube lies in `B_1` by `Kakeya.VeryNotSticky.contained`,
and both have unit core length, so the node lies in `B_4`. This is the containment that
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` now uses internally, through
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` at `R = 4`; the next declaration
shows the radius cannot be improved to `1`, which is why the windowed bound was necessary. -/
theorem activeTubeNode_carrier_subset_closedBall_four (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (𝒰.cover.tube k j).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4 :=
  MultiScaleFac.node_carrier_subset_ball cfg.hδ cfg.hδ1 𝒰 (s_nonempty cfg)
    (fun i hi ↦ cfg.contained i hi) hk hj

/-- The direction of the witness tube of `node_carrier_not_subset_closedBall_one`. -/
noncomputable def boundaryDir : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ)

theorem norm_boundaryDir : ‖boundaryDir‖ = 1 := by simp [boundaryDir]

/-- The far endpoint of the witness tube: at distance `1 - δ` from the origin, so that the
`δ`-tube on it touches `∂B_1`. -/
noncomputable def boundaryFar (δ : NNReal) : EuclideanSpace ℝ (Fin 3) :=
  (1 - (δ : ℝ)) • boundaryDir

/-- The near endpoint of the witness tube. -/
noncomputable def boundaryNear (δ : NNReal) : EuclideanSpace ℝ (Fin 3) :=
  (-(δ : ℝ)) • boundaryDir

theorem dist_boundary_endpoints (δ : NNReal) : dist (boundaryFar δ) (boundaryNear δ) = 1 := by
  rw [dist_eq_norm]
  have h : boundaryFar δ - boundaryNear δ = (1 : ℝ) • boundaryDir := by
    simp only [boundaryFar, boundaryNear]
    module
  rw [h, norm_smul, norm_boundaryDir]
  norm_num

/-- **A `δ`-tube whose carrier touches the boundary of the unit ball.** Legitimate data for
Configuration `hyp:ml2setup`, whose only containment clause is
`Kakeya.VeryNotSticky.contained`, `⊆ closedBall 0 1`. -/
noncomputable def boundaryTube (δ : NNReal) : Tube δ (EuclideanSpace ℝ (Fin 3)) :=
  Tube.mk' δ (dist_boundary_endpoints δ)

theorem boundaryTube_subset_closedBall_one (δ : NNReal) (hδ : (δ : ℝ) ≤ 1 / 2) :
    (boundaryTube δ).carrier ⊆ Metric.closedBall 0 1 := by
  have hcar : (boundaryTube δ).carrier
      = ⋃ z ∈ segment ℝ (boundaryFar δ) (boundaryNear δ), Metric.closedBall z (δ : ℝ) := rfl
  have hseg : segment ℝ (boundaryFar δ) (boundaryNear δ)
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 - (δ : ℝ)) := by
    refine (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 - (δ : ℝ))).segment_subset ?_ ?_
    · simp only [Metric.mem_closedBall, dist_zero_right, boundaryFar, norm_smul,
        norm_boundaryDir, mul_one]
      have h0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    · simp only [Metric.mem_closedBall, dist_zero_right, boundaryNear, norm_smul,
        norm_boundaryDir, mul_one]
      have h0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
  rw [hcar]
  intro p hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  have hz' : ‖z‖ ≤ 1 - (δ : ℝ) := by
    have := hseg hz
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  have hpz' : dist p z ≤ (δ : ℝ) := by simpa [Metric.mem_closedBall] using hpz
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖p‖ ≤ ‖z‖ + dist p z := by
        rw [dist_eq_norm]
        simpa using norm_le_norm_add_norm_sub' p z
    _ ≤ (1 - (δ : ℝ)) + (δ : ℝ) := by gcongr
    _ = 1 := by ring

/-- Any strict rescale of the witness tube leaves the unit ball. -/
theorem boundaryTube_rescale_not_subset (δ ρ : NNReal) (hδρ : (δ : ℝ) < (ρ : ℝ)) :
    ¬ ((boundaryTube δ).rescale ρ).carrier ⊆ Metric.closedBall 0 1 := by
  intro hsub
  set q : EuclideanSpace ℝ (Fin 3) := (1 - (δ : ℝ) + (ρ : ℝ)) • boundaryDir with hq
  have hmem : q ∈ ((boundaryTube δ).rescale ρ).carrier := by
    have hcar : ((boundaryTube δ).rescale ρ).carrier
        = ⋃ z ∈ segment ℝ (boundaryFar δ) (boundaryNear δ), Metric.closedBall z (ρ : ℝ) := rfl
    rw [hcar]
    refine Set.mem_biUnion (left_mem_segment ℝ (boundaryFar δ) (boundaryNear δ)) ?_
    simp only [Metric.mem_closedBall, dist_eq_norm, hq, boundaryFar]
    have h : (1 - (δ : ℝ) + (ρ : ℝ)) • boundaryDir - (1 - (δ : ℝ)) • boundaryDir
        = (ρ : ℝ) • boundaryDir := by module
    rw [h, norm_smul, norm_boundaryDir, mul_one, Real.norm_eq_abs,
      abs_of_nonneg ρ.coe_nonneg]
  have hball := hsub hmem
  simp only [Metric.mem_closedBall, dist_zero_right, hq, norm_smul, norm_boundaryDir, mul_one,
    Real.norm_eq_abs] at hball
  have hpos : (0 : ℝ) ≤ 1 - (δ : ℝ) + (ρ : ℝ) := by
    have h0 := δ.coe_nonneg
    nlinarith [ρ.coe_nonneg]
  rw [abs_of_nonneg hpos] at hball
  linarith

private theorem boundary_rescale_body_mono (δ : NNReal) {ρ σ : NNReal} (hρσ : ρ ≤ σ) :
    ((boundaryTube δ).rescale ρ).toConvexSpaceBody
      ≤ ((boundaryTube δ).rescale σ).toConvexSpaceBody := by
  refine SetLike.coe_subset_coe.mp ?_
  intro p hp
  have hp0 : p ∈ ((boundaryTube δ).rescale ρ).carrier := hp
  change p ∈ ((boundaryTube δ).rescale σ).carrier
  have hcar1 : ((boundaryTube δ).rescale ρ).carrier
      = ⋃ z ∈ segment ℝ (boundaryFar δ) (boundaryNear δ), Metric.closedBall z ((ρ : NNReal) : ℝ) :=
    rfl
  have hcar2 : ((boundaryTube δ).rescale σ).carrier
      = ⋃ z ∈ segment ℝ (boundaryFar δ) (boundaryNear δ), Metric.closedBall z ((σ : NNReal) : ℝ) :=
    rfl
  rw [hcar1] at hp0
  rw [hcar2]
  simp only [Set.mem_iUnion, exists_prop] at hp0 ⊢
  obtain ⟨z, hz, hpz⟩ := hp0
  exact ⟨z, hz, Metric.closedBall_subset_closedBall (by exact_mod_cast hρσ) hpz⟩

private theorem boundaryTube_body_le (δ : NNReal) {ρ : NNReal} (hδρ : δ ≤ ρ) :
    (boundaryTube δ).toConvexSpaceBody ≤ ((boundaryTube δ).rescale ρ).toConvexSpaceBody := by
  have h := boundary_rescale_body_mono δ (ρ := δ) (σ := ρ) hδρ
  rwa [Tube.toConvexSpaceBody_rescale_self] at h

/-- **The one-node hierarchy over the witness tube.** Every clause of
`Tube.UniformTubeSet` is met with the constant `1`: the nodes are the rescales of the
single tube to the grid radii, so containment and nesting are the monotonicity of the tube
radius, the classes are singletons, and the overlap count never exceeds `1`. -/
noncomputable def boundaryHierarchy (δ : NNReal) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hN : 0 < N) :
    Tube.UniformTubeSet ({()} : Finset Unit) (fun _ ↦ boundaryTube δ) N 1 where
  cover :=
    { indexSet := fun _ ↦ {()}
      assign := fun _ _ ↦ ()
      tube := fun k _ ↦ (boundaryTube δ).rescale (Tube.gridScale δ N k)
      assign_mem := by intro k hk i hi; simp
      le_tube_assign := by
        intro k hk i hi
        refine boundaryTube_body_le δ ?_
        calc δ = Tube.gridScale δ N N := (Tube.gridScale_self δ hN).symm
          _ ≤ Tube.gridScale δ N k := Tube.gridScale_antitone hδ hδ1 N hk
      nested := by intro k hk i hi j hj h; rfl
      tube_nested := by
        intro k hk i hi
        exact boundary_rescale_body_mono δ (Tube.gridScale_antitone hδ hδ1 N (Nat.le_succ k)) }
  branchingN := fun _ ↦ 1
  tube_injOn := by
    intro k hk a ha b hb h
    exact Subsingleton.elim a b
  boundedOverlap := by
    intro k hk V
    classical
    calc (((({()} : Finset Unit).filter (fun j ↦ ∃ i ∈ ({()} : Finset Unit),
              (boundaryTube δ).toConvexSpaceBody ≤
                ((boundaryTube δ).rescale (Tube.gridScale δ N k)).toConvexSpaceBody ∧
              (boundaryTube δ).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal))
        ≤ ((({()} : Finset Unit).card : ℕ) : NNReal) := by
          exact_mod_cast Finset.card_filter_le _ _
      _ = 1 := by simp
  card_class_le := by
    intro k hk j hj
    classical
    have hcls : Tube.coverClass ({()} : Finset Unit) (fun _ : Unit ↦ ()) j
        = ({()} : Finset Unit) := by simp [Tube.coverClass]
    rw [hcls]
    simp
  le_card_class := by
    intro k hk j hj
    classical
    have hcls : Tube.coverClass ({()} : Finset Unit) (fun _ : Unit ↦ ()) j
        = ({()} : Finset Unit) := by simp [Tube.coverClass]
    rw [hcls]
    simp

/-- **Unit-ball containment of the node tubes is not a consequence of the hierarchy bundle.**

For every `0 < δ ≤ 1/2`, every positive grid length `N` and every grid index `k < N` there is a
`Tube.UniformTubeSet` over a family of `δ`-tubes contained in `closedBall 0 1` whose node
at index `k` is *not* contained in `closedBall 0 1`. The index `k` is unrestricted below `N`, so
this is not the `k = 0` degeneracy `ρ = 1`: it holds at every scale of the grid, in particular
below any threshold `ρ ≤ ρ₀` that
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` imposes.

Consequently the hypothesis `hball` of that theorem is not derivable from what
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` knows about its hierarchy binder, and
adding it there would be a binder no call site can supply. See the discussion above for what
would have to be built instead. -/
theorem node_carrier_not_subset_closedBall_one {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ12 : (δ : ℝ) ≤ 1 / 2) {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    (∀ i ∈ ({()} : Finset Unit), (boundaryTube δ).carrier ⊆ Metric.closedBall 0 1) ∧
      (() ∈ (boundaryHierarchy δ hδ hδ1 hN).cover.indexSet k) ∧
      ¬ ((boundaryHierarchy δ hδ hδ1 hN).cover.tube k ()).carrier
          ⊆ Metric.closedBall 0 1 := by
  have hδlt1 : δ < 1 := by
    have h : (δ : ℝ) < 1 := by linarith
    exact_mod_cast h
  refine ⟨fun i _ ↦ boundaryTube_subset_closedBall_one δ hδ12, by simp [boundaryHierarchy], ?_⟩
  have hgrid : δ < Tube.gridScale δ N k := by
    have h := Tube.gridScale_lt_gridScale hδ hδlt1 hN hk
    rwa [Tube.gridScale_self δ hN] at h
  exact boundaryTube_rescale_not_subset δ (Tube.gridScale δ N k) (by exact_mod_cast hgrid)

/-! ### The consumer of the refuted statement is not itself `ν`-refutable

The refutation of `Kakeya.VeryNotSticky.coarseKatzTaoBound` is a `ν`-uniformity refutation: its
right-hand side is `q^ν K` with `q < 1`. The single consumer,
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`, carries `ν` too — through the factor
`δ^{-ν/90}` of its mass conjunct and through the witness `Δ` — so the same question has to be
asked of it, and the answer is that the vector is closed. `ν` occurs in exactly one conjunct of
the conclusion, on the *large* side, as `δ^{-ν/90}` with `δ ≤ 1`; that factor is nondecreasing
in `ν`, so the conclusion at `ν` implies the conclusion at every larger gain, with the same five
witnesses. A statement that only weakens as `ν → ∞` cannot be refuted by letting `ν → ∞`.

The other four conjuncts do not mention `ν` at all, and `Δ` is existential, pinned from below by
the mass conjunct and from above by the two-scale conjunct
`Δ (Nf δ²) ≤ C ρ²`; raising `ν` loosens the lower pin and leaves the upper one alone.
-/

/-- **The conclusion of `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` is monotone in the
gain.** Compiler-checked form of the paragraph above: the same witnesses serve at every larger
`ν`. -/
theorem rScaleParentData_gain_mono (cfg : VeryNotSticky.{u}) {ν ν' : ℝ} (hν : ν ≤ ν')
    {r : NNReal} (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (H : ∃ volT volTa Δ Na Nf : ENNReal,
      Na ≠ 0 ∧ Na ≠ ⊤ ∧ Nf ≠ ⊤ ∧
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier = volT * (cfg.s.card : ENNReal) ∧
      (cfg.δ : ENNReal) ^ cfg.η * (Na * volTa) ≤
        (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ∧
      Δ * (Nf * (cfg.δ : ENNReal) ^ 2) ≤
        (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 ∧
      (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
        (cfg.δ : ENNReal) ^ 2 * volTa ∧
      (cfg.s.card : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 2 * (Na * Nf)) :
    ∃ volT volTa Δ Na Nf : ENNReal,
      Na ≠ 0 ∧ Na ≠ ⊤ ∧ Nf ≠ ⊤ ∧
      ∑ i ∈ cfg.s, volume (cfg.T i).toShadedBody.carrier = volT * (cfg.s.card : ENNReal) ∧
      (cfg.δ : ENNReal) ^ cfg.η * (Na * volTa) ≤
        (cfg.δ : ENNReal) ^ (-(ν' / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) ∧
      Δ * (Nf * (cfg.δ : ENNReal) ^ 2) ≤
        (deltamaxScaleAConstant cfg.C₀ cfg.D₀ : ENNReal) * (r : ENNReal) ^ 2 ∧
      (tubeVolumeRatioConstant 3 : ENNReal) * ((r : ENNReal) ^ 2 * volT) ≤
        (cfg.δ : ENNReal) ^ 2 * volTa ∧
      (cfg.s.card : ENNReal) ≤ (cfg.C₀ : ENNReal) ^ 2 * (Na * Nf) := by
  obtain ⟨volT, volTa, Δ, Na, Nf, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  refine ⟨volT, volTa, Δ, Na, Nf, h1, h2, h3, h4, ?_, h6, h7, h8⟩
  refine le_trans h5 ?_
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hstep : (cfg.δ : ENNReal) ^ (-(ν / 90)) ≤ (cfg.δ : ENNReal) ^ (-(ν' / 90)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith)
  gcongr


end Kakeya.VeryNotSticky
