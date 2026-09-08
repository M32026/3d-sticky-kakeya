/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupConfigOfFamily
public import Kakeya.DimensionThree.MainLemma2.BallCoreOfCover
public import Kakeya.DimensionThree.MainLemma2.SetupThresholdsDegenerate
public import Kakeya.DimensionThree.MainLemma2.SplitInputsProduce
public import Kakeya.DimensionThree.MainLemma2.SplitInputsLoosePlug
public import Kakeya.DimensionThree.MainLemma2.TangentialCase
public import Kakeya.DimensionThree.MainLemma2.Conjunct6LineED

/-!
# Assembly of the side data in the degenerate regime

`Kakeya.VeryNotSticky.SideDataResidue` supplies a refined configuration,
a `BallData`, and the corresponding `CaseSideData`. Together with
`LocalMassRefinementResidue`, it feeds
`exists_setup_caseSideData_of_sideDataResidue`.

`SideDataObligations` packages the five inputs used on the path `a = b = δ`:
the ball datum with its containment margin, the thin configuration and scale
thresholds, the slab package under that margin, the Katz--Tao estimate at
scale `ρ₂`, and the fibre-scale count for an admissible hierarchy.
`sideDataResidue_of_sideDataObligations` assembles these with the local
mass refinement, island cover, configuration of the retained family, thick
bundle, and splitting inputs.

The containment margin is required for the scale-thickening of each body
to remain in its ball. The slab construction consumes precisely that
margin. The hierarchy count allows `Ccnt ≤ δ^{-18η}` to account for
the parent comparison and scale rounding.

## Pointwise use of the Katz--Tao window

Inside `SideDataResidue`, the Katz--Tao and Frostman estimates and the
window are available through `cfg.ktEstimate`, `cfg.fEstimate`, and
`cfg.ckt` after `δ` is fixed. `exists_config_of_slackCut_at` is the
pointwise form of `eventually_exists_config_of_slackCut`: it takes the
seven window-independent thresholds as hypotheses and obtains
`6δ^{exscal-η} ≤ w.wρ` from `cfg.ckt.hδrad`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody
open scoped NNReal ENNReal
open Produce

universe u

/-! ### T2b — the pointwise form of `eventually_exists_config_of_slackCut` -/

/-- **Configuration `hyp:ml2setup` of the island-cut family, at one scale `δ`** — the body of
`Kakeya.VeryNotSticky.eventually_exists_config_of_slackCut` with its `∀ᶠ` thresholds as
hypotheses. `hgrid`, `habs`, `hcoarse`, `hthr`, `hindloss`, `hLcap`, `hhalf` are the seven
`w`-free thresholds that theorem filters on (`eventually_gridFine`,
`eventually_aScaleData_absorb_of_le 1`, `eventually_coarseLoss_absorb (K := 4)`,
`Kakeya.ML2Assembly.eventually_card_thresholds`, `eventually_ennreal_le_rpow_neg` twice,
`eventually_nnreal_mul_rpow_le_const 2 1`); `hwδ` is the window's radius clause, which inside
`Kakeya.VeryNotSticky.SideDataResidue` comes from the given configuration's
`Kakeya.CoarseKTData.hδrad`. Inputs and output are otherwise those of the `∀ᶠ` theorem: the
target's binders on `(s, T)`, the slack clauses of the refinement `(s', T')`, the island cut's
(ii)–(iv) for the cut family, and a configuration `cfg'` (`Kakeya.VeryNotSticky.ofFamily` of the
cut family) with the prescribed parameters, comparing to `(s, T)` at `c' = 2⁻¹ δ^{η/2} ≥ δ^η`,
index set `s'`, shades `Y'(i) \ Light`, working dimensions `a = b = δ`. -/
theorem exists_config_of_slackCut_at {β ζ exscal ϱ η η' τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hη' : 0 < η') (h8 : 8 * η' < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    {δ : NNReal}
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) (hwδ : 6 * δ ^ (exscal - η) ≤ w.wρ)
    (hgrid : 1 ≤ η * (Tube.ssfGridLen δ : ℝ))
    (habs : ∀ C₀ : NNReal, 1 ≤ C₀ → (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') →
      ((aScaleDataConstant C₀ 1 : NNReal) : ENNReal) ^ 2 ≤ (δ : ENNReal) ^ (-η))
    (hcoarse : ∀ N : ℕ, 0 < N → (N : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((_root_.ShadedBody.rhoTubesSection9Loss 3 N δ : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ (-η))
    (hthr : 0 < δ ∧ δ ≤ 1 ∧
      ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ (-1 : ℝ))
    (hindloss : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal) ≤
      (δ : ENNReal) ^ (-η))
    (hLcap : ((Tube.coverCountLoss 3 : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ (-η'))
    (hhalf : 2 * δ ^ (η / 2) ≤ 1) :
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (∀ i ∈ s, (T i).toTube.IsCentred) →
      (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
        Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
      maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
        ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
          (tρ : Set κ).Pairwise
            (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
          (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
          (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
      ∀ (s' : Finset ι) (T' : ι → ShadedTube δ E3) (Light : Set E3)
        (hL : MeasurableSet Light),
        s' ⊆ s →
        (∀ i, (T' i).toTube = (T i).toTube) →
        (∀ i, (T' i).shade ⊆ (T i).shade) →
        (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) →
        (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal) →
        (δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade ≤
          ∑ i ∈ s', volume (T' i).shade →
        (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤
            volume ((T' i).shade \ Light)) →
        (2 : ENNReal)⁻¹ * ∑ i ∈ s', volume (T' i).shade ≤
            ∑ i ∈ s', volume ((T' i).shade \ Light) →
        LocalMassAt δ η s' (fun i ↦ deleteShadeTube (T' i) Light hL) →
        ∃ (cfg' : VeryNotSticky.{u}) (e' : cfg'.ι ≃ ι) (c' : NNReal),
          (cfg'.β = β ∧ cfg'.ζ = ζ ∧ cfg'.δ = δ ∧ cfg'.exscal = exscal ∧ cfg'.ϱ = ϱ ∧
              cfg'.η = η) ∧
          ShadedBody.IsCRefinement (cfg'.s.map e'.toEmbedding)
            (fun i ↦ (cfg'.T (e'.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c' ∧
          (δ : ENNReal) ^ η ≤ (c' : ENNReal) ∧
          cfg'.s.map e'.toEmbedding = s' ∧
          (∀ i, (cfg'.T (e'.symm i)).shade = (T' i).shade \ Light) ∧
          cfg'.a = δ ∧ cfg'.b = δ ∧
          (∀ j ∈ cfg'.s, (cfg'.T j).toTube.IsCentred) := by
  classical
  have hη1 : η ≤ 1 := by
    have h1 := params.slabDensity
    have h2 := params.scale
    linarith
  have hexscal1 : exscal ≤ 1 := le_of_lt (lt_trans params.scale (by norm_num))
  set Lc : NNReal := Tube.coverCountLoss 3 with hLc_def
  obtain ⟨hδ, hδ1, hδC⟩ := hthr
  intro ι s T hball hcen huni hmax hfull hcount s' T' Light hL hs' htube hsh ⟨C₀, hC₀, hcap, ⟨𝒱⟩⟩
    htc hmass hfloor hmass2 hclm
  -- the enlarged uniformity constant, transported to the cut family
  set C₁ : NNReal := max C₀ Lc with hC₁_def
  have hC₁ : 1 ≤ C₁ := le_trans hC₀ (le_max_left _ _)
  have hcap₁ : (C₁ : ENNReal) ≤ (δ : ENNReal) ^ (-η') := by
    rw [hC₁_def, ENNReal.coe_max]
    exact max_le hcap hLcap
  have huni₁ : Nonempty (ShadedTube.ShadedUniformTubeSet s'
      (fun i ↦ deleteShadeTube (T' i) Light hL) (Tube.ssfGridLen δ) C₁) :=
    ⟨shadedUniform_deleteShadeTube (𝒱.mono (le_max_left _ _)) Light hL⟩
  -- carriers of the cut family are the original carriers
  have htube'' : ∀ i, (deleteShadeTube (T' i) Light hL).toTube = (T i).toTube := fun i => htube i
  have hsh'' : ∀ i, (deleteShadeTube (T' i) Light hL).shade ⊆ (T i).shade :=
    fun i => Set.sdiff_subset.trans (hsh i)
  have hbody'' : ∀ i, (deleteShadeTube (T' i) Light hL).toConvexSpaceBody =
      (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube'' i)
  have hcarset'' : ∀ i, (deleteShadeTube (T' i) Light hL).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody'' i)
  have hball'' : ∀ i ∈ s, (deleteShadeTube (T' i) Light hL).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcarset'' i]; exact hball i hi
  have hmax'' : maxDensity s (fun i ↦ (deleteShadeTube (T' i) Light hL).toConvexSpaceBody) ≤
      (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_congr (fun i _ => hbody'' i)]; exact hmax
  have hmaxs'' : maxDensity s' (fun i ↦ (deleteShadeTube (T' i) Light hL).toConvexSpaceBody) ≤
      (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax''
  -- the `ρ`-count datum: the count on the parent `s` itself, with the parent's hierarchy at
  -- Lemma 9.1's constant and the retention `δ^{2η}|s| ≤ |s'|`
  have hret : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal) :=
    card_retention_of_mass hδ hδ1 hs' htube hfull
      (ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.coe_le_one_iff.mpr hδ1) (by linarith)) hmass
  have hrho : RhoParentData δ ζ exscal η s' (fun i ↦ deleteShadeTube (T' i) Light hL) :=
    rhoParentData_of_binders hs' htube'' hball hmax huni hcount hret
  -- the cardinality budget, from the binders
  have hcardR : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) :=
    Kakeya.ML2Assembly.card_le_rpow_neg_four hδ hδ1 hδC s'
      (fun i ↦ deleteShadeTube (T' i) Light hL) (fun i hi => hball'' i (hs' hi)) hη1 hmaxs''
  have hcardN : ((s'.card : NNReal)) ≤ δ ^ (-(4 : ℝ)) := by
    have h : ((s'.card : NNReal) : ℝ) ≤ ((δ ^ (-(4 : ℝ)) : NNReal) : ℝ) := by
      rw [NNReal.coe_natCast, NNReal.coe_rpow]; exact hcardR
    exact_mod_cast h
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at htc; simp at htc
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  have hloss := hcoarse s'.card (Finset.card_pos.mpr ⟨i₀, hi₀⟩) hcardN
  -- the working dimensions, at `a = b = δ`
  have hdd : δ ≤ δ ^ exscal := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hexscal1
    simpa using h
  -- the per-tube floor of the cut family, in the record's form
  have hpt'' : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) *
      volume (deleteShadeTube (T' i) Light hL).toShadedBody.carrier ≤
      volume (deleteShadeTube (T' i) Light hL).toShadedBody.shade :=
    fun i hi => hfloor i hi
  -- the retention constant `c' = 2⁻¹ δ^{η/2}`
  have hδE0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ.ne'
  have hc'coe : (((2 : NNReal)⁻¹ * δ ^ (η / 2) : NNReal) : ENNReal) =
      (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) := by
    rw [ENNReal.coe_mul, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat,
      ENNReal.coe_rpow_of_ne_zero hδ.ne']
  have hmass'' : (((2 : NNReal)⁻¹ * δ ^ (η / 2) : NNReal) : ENNReal) *
      ∑ i ∈ s, volume (T i).shade ≤
      ∑ i ∈ s', volume (deleteShadeTube (T' i) Light hL).shade := by
    rw [hc'coe]
    calc (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade
        = (2 : ENNReal)⁻¹ * ((δ : ENNReal) ^ (η / 2) * ∑ i ∈ s, volume (T i).shade) := by ring
      _ ≤ (2 : ENNReal)⁻¹ * ∑ i ∈ s', volume (T' i).shade := by gcongr
      _ ≤ ∑ i ∈ s', volume ((T' i).shade \ Light) := hmass2
  have hgain : (δ : ENNReal) ^ η ≤ (((2 : NNReal)⁻¹ * δ ^ (η / 2) : NNReal) : ENNReal) := by
    rw [hc'coe]
    have hhalf' : (δ : ENNReal) ^ (η / 2) ≤ (2 : ENNReal)⁻¹ := by
      have h2 : ((2 * δ ^ (η / 2) : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hhalf
      rw [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_rpow_of_ne_zero hδ.ne'] at h2
      rw [ENNReal.le_inv_iff_mul_le, mul_comm]
      exact h2
    calc (δ : ENNReal) ^ η = (δ : ENNReal) ^ (η / 2) * (δ : ENNReal) ^ (η / 2) := by
          rw [← ENNReal.rpow_add _ _ hδE0 ENNReal.coe_ne_top]; congr 1; ring
      _ ≤ (2 : ENNReal)⁻¹ * (δ : ENNReal) ^ (η / 2) := by gcongr
  refine ⟨ofFamily hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₁ hgrid (habs C₁ hC₁ hcap₁)
      hball hmax hs' htube'' hrho huni₁ hpt'' htc hloss hindloss hclm (a := δ) (b := δ)
      ⟨le_rfl, le_rfl, hdd⟩,
    Equiv.refl ι, (2 : NNReal)⁻¹ * δ ^ (η / 2), ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ofFamily_isCRefinement hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₁ hgrid
      (habs C₁ hC₁ hcap₁) hball hmax hs' htube'' hrho huni₁ hpt'' htc hloss hindloss hclm
      ⟨le_rfl, le_rfl, hdd⟩ hsh'' hmass'',
    hgain, ?_, fun _ => rfl, rfl, rfl, ?_⟩
  -- the index equivalence is the identity; the implicit type arguments of `toEmbedding` are the
  -- configuration's `ι`, so re-state the goal over `ι` before simplifying
  · change Finset.map (Equiv.refl ι).toEmbedding s' = s'
    simp only [Equiv.refl_toEmbedding, Finset.map_refl]
  · intro j hj
    change (deleteShadeTube (T' j) Light hL).toTube.IsCentred
    rw [htube'' j]
    exact hcen j (hs' hj)

/-- **Pin (T2b is pure factoring):** the existing `∀ᶠ` theorem
`Kakeya.VeryNotSticky.eventually_exists_config_of_slackCut` — its type, not a restatement — is
recovered from the pointwise form by `filter_upwards` on its eight thresholds. If either statement
moves, this stops typechecking. -/
example {β ζ exscal ϱ η η' τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hη' : 0 < η') (h8 : 8 * η' < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    type_of% (eventually_exists_config_of_slackCut.{u} hβ hβ1 hζ hexscal hϱ hη hη' h8 params
      hKT hF w) := by
  filter_upwards [eventually_gridFine hη,
      eventually_aScaleData_absorb_of_le 1 h8,
      eventually_coarseLoss_absorb (η := η) (K := (4 : ℝ)) hη (by norm_num),
      Kakeya.ML2Assembly.eventually_card_thresholds,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
        (K := ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal))
        ENNReal.coe_ne_top hη,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
        (K := ((Tube.coverCountLoss 3 : NNReal) : ENNReal)) ENNReal.coe_ne_top hη',
      w.eventually_radius (by linarith [params.slabDensity, hη] : (0:ℝ) < exscal - η),
      eventually_nnreal_mul_rpow_le_const 2 1 one_pos (half_pos hη)] with
    δ hgrid habs hcoarse hthr hindloss hLcap hwδ hhalf
  exact exists_config_of_slackCut_at.{u} hβ hβ1 hζ hexscal hϱ hη hη' h8 params hKT hF
    w hwδ hgrid habs hcoarse hthr hindloss hLcap hhalf

/-! ### The boundary: the remaining obligations as one named `Prop` -/

/-- Sufficient inputs for constructing side data at `a = b = δ`.

The constants `C₀bd`, `Cbias`, `CF`, `Cdil`, `c₁`, `Cg`, and `D` are
fixed before the eventual scale quantifier. The five conjuncts provide:

1. A `BallData` from a disjoint measurable cover, with the specified constants,
   `m = Cm = 1`, `δ ≤ w₁ ≤ 1`, and containment of every body's
   scale-thickening in its radius-`r₁` ball. The cover pieces lie in
   radius-`r₁/16` balls with bounded overlap. Capsule localization at
   `11r₁/16` explains the available margin when the added thickness is small.
2. A `ThinConfig`, `SlabScale`, and `CaseScale`, together with the tangential
   density threshold at the produced thin constant. The latter can depend
   on `δ`, so its quantitative bound is part of this input.
3. A `SlabPackage` for every typical-angle datum, given the containment
   margin from the first conjunct. Containment of a body alone does not
   imply containment of its scale-thickening.
4. `KTRho2ScaleDataAt` at the lattice rescaling constant and exponents
   `4ϱ`, `9η`, and `3ϱ`. The fullness threshold uses the same `9η`.
5. The fibre-scale count at every admissible hierarchy and grid level:
   `ρ₂^{-2-ζ} ≤ Ccnt * #indexSet k`, with `Ccnt ≤ δ^{-18η}`. The
   level lies between `ρ₂*` and `δ^{-η}ρ₂*`; the constant accounts for
   both the comparison with the parent's hierarchy and scale rounding.

The parameter `ζ` enters through the configuration in the final count.
Angular control on the centered path is supplied separately by
`eventually_exists_pbSplitInputs_of_centred`. This definition is a
conjunction of sufficient hypotheses, not an assertion that arbitrary
cover data satisfy all of them. -/
def SideDataObligations (β exscal ϱ η τ τ' : ℝ) (C₀bd Cbias CF Cdil c₁ Cg : NNReal)
    (D : ℕ) : Prop :=
  (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.a = cfg.δ → cfg.b = cfg.δ →
      16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) →
      ∀ {bι : Type u} (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
        bs.Nonempty →
        (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg.r₁ : ℝ) / 16)) →
        (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg.r₁ : ℝ)) →
        (bs : Set bι).PairwiseDisjoint P →
        (∀ B, MeasurableSet (P B)) →
        (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) →
        (∀ (x : E3) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) →
        (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) →
        ∃ bd : BallData cfg, bd.C₀ = C₀bd ∧ bd.Cbias = Cbias ∧ bd.CF = CF ∧ bd.Cdil = Cdil ∧
          bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg = Cg ∧ bd.m = 1 ∧ bd.Cm = 1 ∧
          cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
              Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))) ∧
  (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd → bd.Cbias = Cbias → bd.CF = CF → bd.Cdil = Cdil → bd.c₁ = c₁ → bd.D = D →
      bd.Cg = Cg → bd.m = 1 → bd.Cm = 1 → cfg.δ ≤ bd.w₁ → bd.w₁ ≤ 1 →
      ∃ (tc : ThinConfig cfg bd) (thr₀ : ScaleThresholds),
        SlabScale cfg bd tc τ ∧
        CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr₀ ∧
        ((tangentialSlabDecompConstant tc.C : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η)) ∧
  (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
      (tc : ThinConfig cfg bd),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      cfg.a = cfg.δ → cfg.b = cfg.δ → bd.C₀ = C₀bd → bd.Cbias = Cbias →
      (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
        Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
          Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) →
      ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg tc hB τ'),
        Nonempty (SlabPackage cfg ta)) ∧
  (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.β = β → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      cfg.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
        (4 * cfg.ϱ) (9 * cfg.η) (3 * cfg.ϱ)) ∧
  (∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ → bd.C₀ = C₀bd →
      ∀ C : NNReal, 1 ≤ C → (C : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
      ∀ 𝒰s : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C,
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((𝒰s.cover.indexSet k).card : ℝ))

/-- **Residue 2 from its remaining obligations.** Given
`Kakeya.VeryNotSticky.SideDataObligations` (with T4's constants `4 ≤ C₀bd`,
`ballCoverConstant ≤ D`), `Kakeya.VeryNotSticky.SideDataResidue β ζ exscal ϱ η τ τ'` holds — the
existing producers line up around the six obligations. Inside the residue: the parameter facts come
from `params` (`η ≤ 1`, `3·exscal < 1`, `exscal ≤ 1/2`, `ϱ ≤ 1`, the count margin
`Kakeya.VeryNotSticky.card_margin_of_caseParams`); `filter_upwards` on the thirteen existing
thresholds and the six obligations; then, at a fixed `δ`, the Katz–Tao and Frostman estimates
and the K_KT window are read off the given `cfg`; step 1 the slack family (residue 1 at
`η' = η/16`, `Kakeya.VeryNotSticky.eventually_exists_localMassRefinement_slack`); step 2 the
island cut
(`Kakeya.VeryNotSticky.eventually_exists_lightPieceCut`, exporting the cover); step 3 `cfg'`
(`Kakeya.VeryNotSticky.exists_config_of_slackCut_at`); step 4 the cover transported to `cfg'`
along `e'` and the shade identity (the coarse core
`Kakeya.VeryNotSticky.exists_ballDataCore_of_cover`, T3, is recorded from it as `_hcore` and
not used — not load-bearing in the proof term); step 5 `bd` (T4, with the (A1') margin
`hmargin` of conjunct 1);
step 6 `tc` and the thresholds (T6); step 7 the thick bundle
(`Kakeya.VeryNotSticky.eventually_exists_thickDensityThresholds_degenerate_of_budget`, T11);
step 8 the splitting inputs (`Kakeya.VeryNotSticky.eventually_exists_splitInputs_degenerate`, T8,
with R17's `Ccnt` and R18 at its level `k`); step 9 the tangential inputs (T9 from `hmargin`, T10,
and
`Kakeya.VeryNotSticky.SlabMultKT` at `η₁ := 9·cfg'.η`); step 10
`Kakeya.VeryNotSticky.nonempty_caseSideData`. -/
theorem sideDataResidue_of_sideDataObligations {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    {C₀bd Cbias CF Cdil c₁ Cg : NNReal} (hC₀bd : 4 ≤ C₀bd) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataResidue.{u} β ζ exscal ϱ η τ τ' := by
  classical
  obtain ⟨hT4, hT6, hT9, hT10, hR17⟩ := h
  intro params hplankF
  -- parameter facts from `params`
  have hτ : 0 < τ := params.hτ
  have hslab := params.slab
  have hη1 : η ≤ 1 := by linarith
  have hexscal12 : exscal ≤ 1 / 2 := params.scale.le
  have hexscal1 : exscal < 1 := by linarith [params.scale]
  have hex3 : 3 * exscal < 1 := by linarith
  have hϱ1 : ϱ ≤ 1 := by
    have h := params.slabBias
    have hP : parameterSeparationConstant = 2 ^ 20 := rfl
    rw [hP] at h
    nlinarith
  have hm : 1 + 2 * η < (1 - exscal) * (2 + ζ) :=
    card_margin_of_caseParams hβ1 hζ.le hexscal.le hϱ hη.le params
  have hη' : 0 < η / 16 := by positivity
  have h8 : 8 * (η / 16) < η := by linarith
  have hC₀bd1 : 1 ≤ C₀bd := le_trans (by norm_num) hC₀bd
  filter_upwards [
    eventually_exists_localMassRefinement_slack.{u} hη' h8 hη1,
    eventually_exists_lightPieceCut.{u} hη hexscal hex3,
    eventually_card_of_count.{u} hexscal.le hexscal12 hm,
    eventually_sixteen_mul_le_rpow hexscal1,
    eventually_gridFine hη,
    eventually_aScaleData_absorb_of_le 1 h8,
    eventually_coarseLoss_absorb (η := η) (K := (4 : ℝ)) hη (by norm_num),
    Kakeya.ML2Assembly.eventually_card_thresholds,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal))
      ENNReal.coe_ne_top hη,
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ((Tube.coverCountLoss 3 : NNReal) : ENNReal)) ENNReal.coe_ne_top hη',
    eventually_nnreal_mul_rpow_le_const 2 1 one_pos (half_pos hη),
    eventually_exists_thickDensityThresholds_degenerate_of_budget.{u} Cbias C₀bd hτ hϱ hplankF,
    eventually_exists_pbSplitInputs_of_centred.{u} C₀bd hC₀bd1 hη hexscal hexscal12 hϱ1,
    hT4, hT6, hT9, hT10, hR17] with
    δ hslack hcut hcard h16 hgrid habs hcoarse hthr hindloss hLcap hhalf hthick hsplit
    hT4δ hT6δ hT9δ hT10δ hR17δ
  intro ι s T hball hcen _huni hmax hfull hcount cfg _e _c hparams _href _hc
  -- the Katz–Tao / Frostman estimates and the K_KT window come from `cfg`
  obtain ⟨hβc, -, hδc, hexc, hϱc, hηc⟩ := hparams
  have hKT : KatzTaoEstimate.{u} E3 β := hβc ▸ cfg.ktEstimate
  have hF : FrostmanEstimate.{u} E3 β := hβc ▸ cfg.fEstimate
  have hckt : Kakeya.CoarseKTData.{u} β ϱ η exscal δ := by
    have h := cfg.ckt
    rw [hβc, hϱc, hηc, hexc, hδc] at h
    exact h
  -- step 1: the slack family (residue 1 re-run at `η' = η/16`)
  have hcard' := hcard s T hcount
  obtain ⟨s', T', hs', htube, hsh, huniC, hfloor, htc, hmass, hlm⟩ :=
    hslack s T hball hmax hfull hcard'
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcar : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcar i]; exact hball i (hs' hi)
  -- step 2: the island cut (T1/T1b), exporting the eight cover clauses
  obtain ⟨Light, hL, bι, bs, ctr, P, hbsne, hcb, hdisj, -, hcov, hover, -, h16b, hmeas, hne,
    hii, hiii, hiv⟩ := hcut s' T' hball' hfloor htc hlm
  -- step 3: the configuration `cfg'` (T2b)
  obtain ⟨cfg', e', c', hparams', href', hc', hse', hshade, ha, hb, hcen'⟩ :=
    exists_config_of_slackCut_at.{u} hβ hβ1 hζ hexscal hϱ hη hη' h8 params hKT hF
      hckt.toCoarseKTWindow hckt.hδrad hgrid habs hcoarse hthr hindloss hLcap hhalf
      s T hball hcen _huni hmax hfull hcount s' T' Light hL hs' htube hsh huniC htc hmass hii hiii hiv
  obtain ⟨hβ', hζ', hδ', hex', hϱ', hη''⟩ := hparams'
  have ha' : cfg'.a = cfg'.δ := ha.trans hδ'.symm
  have hb' : cfg'.b = cfg'.δ := hb.trans hδ'.symm
  -- step 4: the cover, transported along `e'` and the shade identity to `cfg'`
  have hr₁' : cfg'.r₁ = δ ^ exscal := by simp only [VeryNotSticky.r₁, hδ', hex']
  have hδr : 16 * (cfg'.δ : ℝ) ≤ (cfg'.r₁ : ℝ) := by rw [hδ', hr₁']; exact h16
  have hPball16 : ∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg'.r₁ : ℝ) / 16) := by
    rw [hr₁']; exact h16b
  have hPball : ∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg'.r₁ : ℝ) := by
    rw [hr₁']; exact hcb
  have hoverlap : ∀ (x : E3) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg'.r₁ : ℝ)) → t.card ≤ ballCoverConstant := by
    rw [hr₁']; exact hover
  have hmem : ∀ j, j ∈ cfg'.s ↔ e' j ∈ s' := by
    intro j; rw [← hse', Finset.mem_map_equiv, Equiv.symm_apply_apply]
  have hPcov : ∀ j ∈ cfg'.s, (cfg'.T j).shade ⊆ ⋃ B ∈ bs, P B := by
    intro j hj
    have h1 : (cfg'.T j).shade = (T' (e' j)).shade \ Light := by
      have := hshade (e' j); rwa [Equiv.symm_apply_apply] at this
    rw [h1]; exact hcov (e' j) ((hmem j).1 hj)
  have hunion : (⋃ i ∈ s', ((T' i).shade \ Light)) ⊆ ⋃ j ∈ cfg'.s, (cfg'.T j).shade := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    refine ⟨e'.symm i, ?_, ?_⟩
    · rw [hmem, Equiv.apply_symm_apply]; exact hi
    · rw [hshade i]; exact hxi
  have hPne : ∀ B ∈ bs, (P B ∩ ⋃ j ∈ cfg'.s, (cfg'.T j).shade).Nonempty :=
    fun B hB => (hne B hB).mono (Set.inter_subset_inter_right _ hunion)
  -- T3 as existing: the coarse core exists from this cover (recorded; T4's interface quantifies
  -- over the cover itself, T12-PLAN F2)
  have _hcore : Nonempty (BallDataCore cfg') :=
    exists_ballDataCore_of_cover cfg' hC₀bd hD hδr hbsne hPball16 hPball hdisj hmeas hPcov
      hoverlap hPne
  -- step 5: the ball data (T4)
  obtain ⟨bd, hbdC₀, hbdCbias, hbdCF, hbdCdil, hbdc₁, hbdD, hbdCg, hbdm, hbdCm, hδw₁, hw₁one,
    hmargin⟩ :=
    hT4δ cfg' hδ' hη'' hex' hϱ' ha' hb' hδr bs ctr P hbsne hPball16 hPball hdisj hmeas hPcov
      hoverlap hPne
  -- step 6: the thin configuration and the thresholds (T6)
  obtain ⟨tc, thr₀, hslabScale, hcaseScale, hdens⟩ :=
    hT6δ cfg' bd hδ' hβ' hη'' hex' hϱ' ha' hb' hbdC₀ hbdCbias hbdCF hbdCdil hbdc₁ hbdD hbdCg
      hbdm hbdCm hδw₁ hw₁one
  -- step 7: the thick bundle (T11; vacuous at `a = δ`)
  obtain ⟨ηF, C_NC, -, -, -, thick⟩ :=
    hthick cfg' bd hδ' hϱ' hη'' hbdCbias hbdC₀ ha' (CP := 1) (Θ := 1) le_rfl le_rfl
  -- step 8: the splitting inputs (T8 + R17 + R18), over the loose datum conjunct 6 hands over
  --. The `𝒱` the exact chain took by
  -- `Classical.choice` from `cfg.splitHierarchy` now comes from conjunct 6's own `∃` — defect D2
  -- of  fixed — and conjunct 5 speaks about the same datum, which is why it moved in
  -- lockstep.
  obtain ⟨split⟩ :=
    hsplit cfg' bd hδ' hη'' hex' hϱ' hbdC₀ hb' hcen'
      (hR17δ cfg' bd hδ' hη'' hex' hϱ' hb' hbdC₀)
  -- step 9: the tangential inputs (T9, T10)
  have slab : ∀ {B : bd.bι} (hB : B ∈ bd.bs) (ta : TypicalAngleData cfg' tc hB τ'),
      SlabPackage cfg' ta :=
    fun hB ta => (hT9δ cfg' bd tc hδ' hβ' hη'' hex' hϱ' ha' hb' hbdC₀ hbdCbias hmargin hB ta).some
  have hest : cfg'.KTRho2ScaleDataAt bd (latticeRescaleConstant bd.C₀)
      (4 * cfg'.ϱ) (9 * cfg'.η) (3 * cfg'.ϱ) :=
    hT10δ cfg' bd hδ' hβ' hη'' hex' hϱ' hb' hbdC₀
  let slabMult : SlabMultKT cfg' tc :=
    { η₁ := 9 * cfg'.η
      fullness_threshold := le_rfl
      estimate := hest
      densityConstant := hdens }
  let tangential : TangentialInputs cfg' tc τ' :=
    { slab := fun hB ta => slab hB ta
      slabMult := slabMult
      split := split }
  -- step 10: assemble
  exact ⟨cfg', bd, e', c', ⟨hβ', hζ', hδ', hex', hϱ', hη''⟩, href', hc',
    nonempty_caseSideData thick tc hslabScale hcaseScale (fun _ _ => tangential)⟩

/-! ### Tripwires: the boundary composes with the frozen consumer and the frozen target -/

/-- **Tripwire 1**: if, for every admissible parameter set, some constants satisfy
`Kakeya.VeryNotSticky.SideDataObligations`, then
`Kakeya.VeryNotSticky.SetupCaseSideDataStatement` — the target's statement with every binder
explicit — holds, through the frozen consumer
`Kakeya.VeryNotSticky.exists_setup_caseSideData_of_sideDataResidue`. So `SideDataObligations` is
all that stands between the tree and the target on this path. -/
example
    (hob : ∀ {β ζ exscal ϱ η τ τ' : ℝ}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
      ∃ (C₀bd Cbias CF Cdil c₁ Cg : NNReal) (D : ℕ), 4 ≤ C₀bd ∧ ballCoverConstant ≤ D ∧
        SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SetupCaseSideDataStatement.{u} := by
  intro β ζ exscal ϱ η τ τ' hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
  obtain ⟨C₀bd, Cbias, CF, Cdil, c₁, Cg, D, hC₀bd, hD, h⟩ := hob hβ hβ1 hζ hexscal hϱ hη
  exact exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF w (sideDataResidue_of_sideDataObligations hβ hβ1 hζ hexscal hϱ hη hC₀bd hD h)

/-- **Tripwire 2**: the same, directly against the type of the frozen target
`Kakeya.VeryNotSticky.exists_setup_caseSideData`. If the target's binders or conclusion, the
consumer, or `Kakeya.VeryNotSticky.SideDataResidue` move, this stops typechecking. -/
example
    (hob : ∀ {β ζ exscal ϱ η τ τ' : ℝ}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
      ∃ (C₀bd Cbias CF Cdil c₁ Cg : NNReal) (D : ℕ), 4 ≤ C₀bd ∧ ballCoverConstant ≤ D ∧
        SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SetupCaseSideDataStatement.{u} := by
  intro β ζ exscal ϱ η τ τ' hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
  obtain ⟨C₀bd, Cbias, CF, Cdil, c₁, Cg, D, hC₀bd, hD, h⟩ := hob hβ hβ1 hζ hexscal hϱ hη
  exact exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF w (sideDataResidue_of_sideDataObligations hβ hβ1 hζ hexscal hϱ hη hC₀bd hD h)

/-- **Tripwire 3**: the producer of `Kakeya.VeryNotSticky.SideDataObligations` is entitled to
`Kakeya.VeryNotSticky.CaseParams` — it is a hypothesis of the frozen target — and it CHOOSES the
fullness constant `c₁`, which the boundary quantifies existentially.  So neither the admissibility
`4 c₁ ballCoverConstant ≤ 1` (satisfied here by `c₁ = 1/143748`) nor the bias bound `ϱ ≤ 1/21`
needs to appear in `SideDataObligations`: both are discharged on the producer's side. -/
example
    (hob : ∀ {β ζ exscal ϱ η τ τ' : ℝ}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
      CaseParams β ζ exscal ϱ η τ τ' →
      ∃ (C₀bd Cbias CF Cdil Cg : NNReal) (D : ℕ), 4 ≤ C₀bd ∧ ballCoverConstant ≤ D ∧
        SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil (1 / 143748) Cg D) :
    SetupCaseSideDataStatement.{u} := by
  intro β ζ exscal ϱ η τ τ' hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
  obtain ⟨C₀bd, Cbias, CF, Cdil, Cg, D, hC₀bd, hD, h⟩ := hob hβ hβ1 hζ hexscal hϱ hη params
  exact exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF w (sideDataResidue_of_sideDataObligations hβ hβ1 hζ hexscal hϱ hη hC₀bd hD h)

/-- **Tripwire 4**: the same, directly against the type of the frozen target. -/
example
    (hob : ∀ {β ζ exscal ϱ η τ τ' : ℝ}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
      CaseParams β ζ exscal ϱ η τ τ' →
      ∃ (C₀bd Cbias CF Cdil Cg : NNReal) (D : ℕ), 4 ≤ C₀bd ∧ ballCoverConstant ≤ D ∧
        SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil (1 / 143748) Cg D) :
    SetupCaseSideDataStatement.{u} := by
  intro β ζ exscal ϱ η τ τ' hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
  obtain ⟨C₀bd, Cbias, CF, Cdil, Cg, D, hC₀bd, hD, h⟩ := hob hβ hβ1 hζ hexscal hϱ hη params
  exact exists_setup_caseSideData_of_sideDataResidue hβ hβ1 hζ hexscal hϱ hη params hplankF
    hKT hF w (sideDataResidue_of_sideDataObligations hβ hβ1 hζ hexscal hϱ hη hC₀bd hD h)

end Kakeya.VeryNotSticky
