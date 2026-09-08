/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.WeightedPipeline

/-! # The refinement ledger for the carrier-weighted factoring pipeline -/

public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

set_option maxHeartbeats 800000 in
-- The proof expands the Step 2 level set and integrates two finite multiplicity decompositions.
/-- Carrier-weighted Steps 2--3 retain the named fraction of the shading mass selected by
Step 1.  This intermediate ledger is exposed separately because positivity of the Step 3 union
is needed before the internally chosen Step 5 cover is known to be nonempty. -/
theorem weightedPipelineStep2Step3_mass [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
    (r : ℝ) (hr : 0 < r)
    (hOmega : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr)) :
    ((factoringStep2Step3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D, volume (F.innerBody i).shade ≤
      ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D,
        volume (step3InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D r hr) hOmega
          (F.weightedPipelineExponent hδ hdisc D r hr) i).shade := by
  let u := F.step0.innerSet
  let t := (F.weightedPipelineStep1 hδ hdisc D).outerSet
  let Omega := F.weightedPipelineSet hδ hdisc D r hr
  let k := F.weightedPipelineExponent hδ hdisc D r hr
  let G := step3FactorFamily F F.innerSet_step0_subset t Omega hOmega k
  have hstep2 :
      ((factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D, volume (F.innerBody i).shade ≤
        ∫⁻ x in Omega,
          (pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
            F.innerBody x : ℝ≥0∞) := by
    have h := (F.weightedPipelineScaleTriple_spec hδ hdisc D r hr).2
    rw [F.weightedPipelineInnerSet_eq_filter hδ hdisc D] at h
    simp_rw [sum_fiberMultiplicity_eq_pointwiseMultiplicity F F.step0.innerSet
      (F.weightedPipelineStep1 hδ hdisc D).outerSet] at h
    have hout := F.outerSet_weightedStep1AtScale_subset_image hδ hdisc D.exponent
      D.volume_outer_le
    rw [← F.weightedPipelineStep1_eq hδ hdisc D] at hout
    have h' := ENNReal.inv_natCast_mul_le_of_le
      (scalePigeonholeConstant_le_factoringStep2PigeonholeConstant le_rfl
        (Finset.card_le_card_of_subset_image F.innerSet_step0_subset hout)) h
    rw [lintegral_pointwiseMultiplicity_eq_sum_volume_shade F F.step0.innerSet t] at h'
    simpa only [Omega, t, F.weightedPipelineSet_eq hδ hdisc D r hr,
      FactorFamily.weightedPipelineInnerSet_eq_filter] using h'
  have hC3zero : (factoringStep3Constant F.innerSet.card : ℝ≥0∞) ≠ 0 := by
    have hpos : 4 ≤ factoringStep3Constant F.innerSet.card :=
      (factoringStep2Constant_pos F.innerSet.card).2
    exact_mod_cast (by omega : factoringStep3Constant F.innerSet.card ≠ 0)
  have hC3top : (factoringStep3Constant F.innerSet.card : ℝ≥0∞) ≠ ⊤ := by simp
  have hpoint : ∀ x ∈ Omega,
      (pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
          F.innerBody x : ℝ≥0∞) ≤
        (factoringStep3Constant F.innerSet.card : ℝ≥0∞) *
          (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := by
    intro x hx
    have hb := F.bounds_of_mem_weightedPipelineSet hδ hdisc D r hr hx
    have hlower :
        2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
            2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr ≤
          pointwiseMultiplicity G.innerSet G.innerBody x := by
      calc
        2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
              2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr ≤
            2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
              (MultiplicityFamily.dyadicLevel t
                (fiberMultiplicity F (F.weightedPipelineInnerSet hδ hdisc D)) k x).card :=
          Nat.mul_le_mul_left _ hb.2.2.1
        _ ≤ pointwiseMultiplicity G.innerSet G.innerBody x := by
          simpa only [G, u, t, Omega, k,
            FactorFamily.weightedPipelineInnerSet_eq_filter] using
            mul_card_dyadicLevel_le_pointwiseMultiplicity_step3FactorFamily F
              F.innerSet_step0_subset t Omega hOmega k hx
    exact_mod_cast calc
      pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x ≤
          factoringStep2PointwiseConstant F.innerSet.card *
            (2 ^ F.weightedPipelineExponent hδ hdisc D r hr *
              2 ^ F.weightedPipelineOuterExponent hδ hdisc D r hr) := hb.2.1
      _ ≤ factoringStep2PointwiseConstant F.innerSet.card *
          pointwiseMultiplicity G.innerSet G.innerBody x := Nat.mul_le_mul_left _ hlower
      _ = factoringStep3Constant F.innerSet.card *
          pointwiseMultiplicity G.innerSet G.innerBody x := rfl
  have hstep3 :
      ((factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∫⁻ x in Omega, (pointwiseMultiplicity
            (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x : ℝ≥0∞) ≤
        ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    have hintegral :
        ∫⁻ x in Omega, (factoringStep3Constant F.innerSet.card : ℝ≥0∞)⁻¹ *
            (pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
              F.innerBody x : ℝ≥0∞) ≤
          ∫⁻ x in Omega,
            (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) := by
      refine lintegral_mono_ae ((ae_restrict_iff' hOmega).2 ?_)
      exact Filter.Eventually.of_forall fun x hx ↦
        (ENNReal.inv_mul_le_iff hC3zero hC3top).mpr (hpoint x hx)
    have hsupp : Function.support
        (fun x ↦ (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞)) ⊆ Omega := by
      intro x hx
      have hxnat : pointwiseMultiplicity G.innerSet G.innerBody x ≠ 0 := Nat.cast_ne_zero.mp hx
      obtain ⟨i, _, hxi⟩ := (pointwiseMultiplicity_pos_iff G.innerSet G.innerBody x).mp
        (Nat.pos_iff_ne_zero.mpr hxnat)
      change x ∈ (F.innerBody i).shade ∩ Omega ∩ step3DyadicSet F u t k (F.parent i) at hxi
      exact hxi.1.2
    calc
      ((factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
            ∫⁻ x in Omega, (pointwiseMultiplicity
              (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x : ℝ≥0∞) =
          ∫⁻ x in Omega, (factoringStep3Constant F.innerSet.card : ℝ≥0∞)⁻¹ *
            (pointwiseMultiplicity (F.weightedPipelineInnerSet hδ hdisc D)
              F.innerBody x : ℝ≥0∞) := by
        symm
        exact lintegral_const_mul' (μ := volume.restrict Omega)
          (factoringStep3Constant F.innerSet.card : ℝ≥0∞)⁻¹ _ (by simp [hC3zero])
      _ ≤ ∫⁻ x in Omega, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) :=
        hintegral
      _ = ∫⁻ x, (pointwiseMultiplicity G.innerSet G.innerBody x : ℝ≥0∞) :=
        setLIntegral_eq_of_support_subset hsupp
      _ = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade :=
        (sum_volume_shade_eq_lintegral_pointwiseMultiplicity G.innerSet G.innerBody).symm
  have hC2zero : (factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞) ≠ 0 := by
    have hpos := (factoringStep2Constant_pos F.innerSet.card).1
    exact_mod_cast (by omega : factoringStep2PigeonholeConstant F.innerSet.card ≠ 0)
  have hC2top : (factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞) ≠ ⊤ := by simp
  calc
    ((factoringStep2Step3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D, volume (F.innerBody i).shade =
        ((factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
          (((factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹ *
            ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D,
              volume (F.innerBody i).shade) := by
      simp only [factoringStep2Step3Constant, Nat.cast_mul]
      rw [ENNReal.mul_inv (Or.inl hC2zero) (Or.inl hC2top)]
      ac_rfl
    _ ≤ ((factoringStep3Constant F.innerSet.card : ℝ≥0∞))⁻¹ *
        ∫⁻ x in Omega, (pointwiseMultiplicity
          (F.weightedPipelineInnerSet hδ hdisc D) F.innerBody x : ℝ≥0∞) :=
      mul_le_mul_right hstep2 _
    _ ≤ ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := hstep3
    _ = ∑ i ∈ F.weightedPipelineInnerSet hδ hdisc D,
        volume (step3InnerBody F F.step0.innerSet
          (F.weightedPipelineStep1 hδ hdisc D).outerSet
          (F.weightedPipelineSet hδ hdisc D r hr) hOmega
          (F.weightedPipelineExponent hδ hdisc D r hr) i).shade := by
      simp only [G, t, Omega, k, step3FactorFamily_innerSet,
        step3FactorFamily_innerBody, FactorFamily.weightedPipelineInnerSet_eq_filter]

namespace Kakeya

/-- Retained mass fraction of the complete carrier-weighted pipeline. -/
@[expose] public noncomputable def factoringWeightedPipelineSelfRefinementConstant
    (n M₀ M N : ℕ) (coverCard : ℝ≥0) : ℝ≥0 :=
  (FactorFamily.weightedStep1AtScaleConstant n M₀ N)⁻¹ *
    ((factoringStep2Step3Constant M : ℕ) : ℝ≥0)⁻¹ *
      (factoringStep5SelfPigeonholeConstant n coverCard)⁻¹

/-- Expansion of the complete carrier-weighted retained-mass coefficient. -/
public theorem factoringWeightedPipelineSelfRefinementConstant_eq
    (n M₀ M N : ℕ) (coverCard : ℝ≥0) :
    factoringWeightedPipelineSelfRefinementConstant n M₀ M N coverCard =
      (FactorFamily.weightedStep1AtScaleConstant n M₀ N)⁻¹ *
        ((factoringStep2Step3Constant M : ℕ) : ℝ≥0)⁻¹ *
          (factoringStep5SelfPigeonholeConstant n coverCard)⁻¹ := rfl

/-- Increasing an upper bound for the Step 5 cover cardinality can only decrease the retained
mass coefficient of the complete carrier-weighted pipeline. -/
public theorem factoringWeightedPipelineSelfRefinementConstant_anti_coverCard
    {n M₀ M N : ℕ} {coverCard : ℕ} {coverBound : NNReal}
    (hcard : (coverCard : NNReal) ≤ coverBound) (hbound : 1 ≤ coverBound) :
    factoringWeightedPipelineSelfRefinementConstant n M₀ M N coverBound ≤
      factoringWeightedPipelineSelfRefinementConstant n M₀ M N coverCard := by
  have hmono := factoringStep5SelfPigeonholeConstant_mono (n := n) hcard hbound
  have hpos := factoringStep5SelfPigeonholeConstant_pos_natCast n coverCard
  unfold factoringWeightedPipelineSelfRefinementConstant
  gcongr

/-- The complete carrier-weighted pipeline retains a positive mass fraction when the Step 1 loss
is positive and the Step 5 cover is nonempty. -/
theorem factoringWeightedPipelineSelfRefinementConstant_pos
    {n M₀ M N : ℕ} {coverCard : ℝ≥0}
    (hstep1 : 0 < FactorFamily.weightedStep1AtScaleConstant n M₀ N)
    (hcover : 1 ≤ coverCard) :
    0 < factoringWeightedPipelineSelfRefinementConstant n M₀ M N coverCard := by
  have hstep23nat : 0 < factoringStep2Step3Constant M := by
    rw [factoringStep2Step3Constant_eq]
    positivity
  have hstep23 : 0 < ((factoringStep2Step3Constant M : ℕ) : NNReal) := by
    exact_mod_cast hstep23nat
  have hstep5 : 0 < factoringStep5SelfPigeonholeConstant n coverCard :=
    factoringStep5SelfPigeonholeConstant_pos hcover
  unfold factoringWeightedPipelineSelfRefinementConstant
  positivity

end Kakeya

namespace FactorFamily

variable [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
  (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (D : OuterInnerVolumeRatio F)
  (r : ℝ) (hr : 0 < r)
  (hOmega : MeasurableSet (F.weightedPipelineSet hδ hdisc D r hr))
  (T' : Finset E) (w₁ : ℝ≥0)

/-- Compose weighted Step 1, Steps 2--3, and the self-pigeonholed Step 5 ledger. -/
theorem weightedPipelineFamily_isCRefinementSelf {M : ℝ≥0}
    (href5 : IsCRefinement (F.weightedPipelineInnerSet hδ hdisc D)
      (step5InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr) T' w₁)
      (F.weightedPipelineInnerSet hδ hdisc D)
      (step3InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr))
      (Kakeya.factoringStep5SelfPigeonholeConstant (Module.finrank ℝ E) M)⁻¹) :
    IsCRefinement (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerSet
      (F.weightedPipelineFamily hδ hdisc D r hr hOmega T' w₁).innerBody
      F.innerSet F.innerBody
      (Kakeya.factoringWeightedPipelineSelfRefinementConstant
        (Module.finrank ℝ E) F.innerSet.card F.innerSet.card D.exponent M) := by
  have href23 : IsCRefinement (F.weightedPipelineInnerSet hδ hdisc D)
      (step3InnerBody F F.step0.innerSet
        (F.weightedPipelineStep1 hδ hdisc D).outerSet
        (F.weightedPipelineSet hδ hdisc D r hr) hOmega
        (F.weightedPipelineExponent hδ hdisc D r hr))
      (F.weightedPipelineStep1 hδ hdisc D).innerSet
      (F.weightedPipelineStep1 hδ hdisc D).innerBody
      ((factoringStep2Step3Constant F.innerSet.card : ℕ) : ℝ≥0)⁻¹ := by
    constructor
    · constructor
      · rw [weightedPipelineInnerSet_eq_step1]
      · intro i hi
        rw [weightedPipelineStep1_innerBody]
        refine ⟨rfl, ?_⟩
        intro x hx
        exact hx.1.1
    · have hCnat : factoringStep2Step3Constant F.innerSet.card ≠ 0 := by
        rw [factoringStep2Step3Constant_eq]
        positivity
      have hC : (factoringStep2Step3Constant F.innerSet.card : ℝ≥0) ≠ 0 := by
        exact_mod_cast hCnat
      have hmass := weightedPipelineStep2Step3_mass F hδ hdisc D r hr hOmega
      rw [ENNReal.coe_inv hC]
      simpa only [weightedPipelineInnerSet_eq_step1, weightedPipelineStep1_innerBody,
        ENNReal.coe_natCast] using hmass
  have href35 := href5.trans href23
  have href1 := F.isCRefinement_weightedStep1AtScale hδ hdisc D.exponent D.volume_outer_le
  rw [← F.weightedPipelineStep1_eq hδ hdisc D] at href1
  have href := href35.trans href1
  rw [weightedPipelineFamily_innerSet]
  rw [weightedPipelineFamily_innerBody]
  simpa only [Kakeya.factoringWeightedPipelineSelfRefinementConstant, mul_assoc] using href

end FactorFamily

end ShadedBody
