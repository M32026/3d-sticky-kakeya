/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.RhoTubes
public import Kakeya.Tube.Dilate
import all Kakeya.Factoring.RhoTubes

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

omit [Nontrivial E] in
open Classical in
/-- The pipeline inner indices over active outer blocks carry exactly the completed inner mass.
This is the product-only support: unlike the completed family, it does not reinsert discarded
zero-shaded indices from the original fibres. -/
private lemma sum_volume_completedActiveInnerBody (F : FactorFamily E ι κ)
    (G₅ : ShadedFactorFamily E ι κ) :
    ∑ i ∈ {i ∈ G₅.innerSet | G₅.parent i ∈ activeOuterSet G₅},
        volume (completedInnerBody F G₅ i).shade =
      ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
  let s₅ := {i ∈ G₅.innerSet | G₅.parent i ∈ activeOuterSet G₅}
  calc
    ∑ i ∈ s₅, volume (completedInnerBody F G₅ i).shade =
        ∑ i ∈ s₅, volume (G₅.innerBody i).shade := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [completedInnerBody, (Finset.mem_filter.mp hi).1]
    _ = ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hiA
      have hparentmem := G₅.parent_mem i hi
      have hnotactive : G₅.parent i ∉ activeOuterSet G₅ := by
        intro ha
        exact hiA (Finset.mem_filter.mpr ⟨hi, ha⟩)
      have hzero : volume (iUnionShade (G₅.fiber (G₅.parent i)) G₅.innerBody) = 0 := by
        by_contra hz
        exact hnotactive (Finset.mem_filter.mpr ⟨hparentmem, hz⟩)
      apply le_antisymm
      · calc
          volume (G₅.innerBody i).shade ≤
              volume (iUnionShade (G₅.fiber (G₅.parent i)) G₅.innerBody) := by
            apply measure_mono
            exact Set.subset_iUnion₂_of_subset i
              (Finset.mem_filter.mpr ⟨hi, rfl⟩) (Set.Subset.refl _)
          _ = 0 := hzero
      · exact bot_le

set_option maxHeartbeats 800000 in
-- The explicit Step 5 covering and multiplicity bookkeeping is a large elaboration steps.
open Classical in
/-- **GWZ Lemma 5.11, dilate form.** The two-scale tube factoring estimate for an outer family of
`c`-dilates of `ρ`-tubes.

Setup: `F` packages a family of shaded `δ`-tubes as its inner family, recorded by the witness `T`,
and the `c`-dilates of a family of `ρ`-tubes as its outer family, recorded by the witness `Tρ`
together with `houter`. The parent map of `F` carries the partition
`𝕋 = ⋃_{T_ρ ∈ 𝕋_ρ} 𝕋[T_ρ]`, and `hball` confines the inner tubes to the unit ball.

Neither essential distinctness of the outer bodies nor any per-tube density hypothesis on the
inner shading is assumed, and no Frostman condition appears: for dilated tubes the fullness
transfer is elementary capsule geometry
(`Kakeya.Tube.volume_dilate_inter_cthickening_ge`), and the pigeonholing of Steps 0-5 needs
nothing more.

Conclusion: there is a fully shaded factor family `G` whose outer family is the selected subfamily
`𝕋_ρ'` with induced shading and whose inner family is the refinement `(𝕋', Y')`. The five
structural conjuncts identify `G` as a restriction of `F` that leaves the convex bodies alone; the
four remaining ones give the aggregate outer fullness lower bound, the refinement, the
multiplicity factorization (`boundMuTTYAcrossTwoScales`), the pointwise shading containment
(`pointwiseContainmenttube`), and the `ρ`-ball volume estimate (`boundVolumeAcrossTwoScales`).
All losses use the single constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`.

The proof is the Step 0 - Step 5 pipeline of `Kakeya/Factoring/Step0.lean` through
`Kakeya/Factoring/Step5.lean`, with the fullness input supplied by
`Kakeya.Tube.volume_dilate_inter_cthickening_ge`. -/
theorem shadingMultiplicityEstimateForRhoTubesDilateRich
    {δ ρ c : ℝ≥0} (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1) (hc : 1 ≤ c)
    (F : FactorFamily E ι κ)
    (T : ι → ShadedTube δ E) (Tρ : κ → Tube ρ E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ j ∈ F.outerSet, F.outerBody j = Kakeya.Tube.dilate (Tρ j) (c : ℝ))
    (hball : ∀ i ∈ F.innerSet, (F.innerBody i).carrier ⊆ Metric.closedBall 0 1) :
    ∃ G : ShadedFactorFamily E ι κ,
      -- `G` restricts `F` to the selected outer family without changing convex bodies.
      G.outerSet ⊆ F.outerSet ∧
      G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet} ∧
      G.parent = F.parent ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = F.outerBody j) ∧
      (∀ i ∈ F.innerSet,
        (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody) ∧
      -- Every selected outer body has an active input fibre.  This is the small structural
      -- fact needed by product-only consumers which pigeonhole the actual fibre cardinalities.
      (∀ j ∈ G.outerSet, (G.fiber j).Nonempty) ∧
      -- The selected outer family is nonempty as soon as the inner shading carries mass; the
      -- hypothesis cannot be dropped, since a null shading selects nothing.
      (0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade → G.outerSet.Nonempty) ∧
      -- `λ (𝕋_ρ', Y_{𝕋_ρ}') ⪆ λ (𝕋, Y)`, in aggregate fullness.
      (shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ c)⁻¹ *
          fullness F.innerSet F.innerBody
        ≤ fullness G.outerSet G.outerBody ∧
      -- `(𝕋', Y')` is a `≈ 1` (here `⪆ 1`) refinement of `(𝕋, Y)`.
      IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C
          (Module.finrank ℝ E) F.innerSet.card δ c)⁻¹ ∧
      -- `boundMuTTYAcrossTwoScales`: `μ(𝕋, Y) ⪅ μ(𝕋_ρ', Y_{𝕋_ρ}') · μ(𝕋[T_ρ], Y')`.
      (∀ j ∈ G.outerSet,
        multiplicity F.innerSet F.innerBody
          ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C
                (Module.finrank ℝ E) F.innerSet.card δ c : ENNReal)
            * multiplicity G.outerSet G.outerBody
            * multiplicity (G.fiber j) G.innerBody) ∧
      -- `pointwiseContainmenttube`: since each `δ`-tube has a unique parent, the pointwise
      -- containment `𝕋_{Y'}(x) ⊂ ⋃_{T_ρ ∈ 𝕋_ρ', x ∈ Y_{𝕋_ρ'}(T_ρ)} (𝕋[T_ρ])_{Y'}(x)` is the
      -- shading inclusion below.
      (∀ i ∈ G.innerSet,
        (G.innerBody i).shade ⊆ (G.outerBody (F.parent i)).shade) ∧
      -- The uncompleted pipeline support retains all inner mass and has factor-two fibre
      -- cardinalities.  Product-only consumers use this support, so the zero-shaded indices
      -- inserted by completion never enter their cardinality product.
      (∃ u : Finset ι,
        u ⊆ G.innerSet ∧
        IsCRefinement u G.innerBody F.innerSet F.innerBody
          (shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank ℝ E) F.innerSet.card δ c)⁻¹ ∧
        (∀ j ∈ G.outerSet, ({i ∈ u | G.parent i = j} : Finset ι).Nonempty) ∧
        (∀ j ∈ G.outerSet, ∀ j' ∈ G.outerSet,
          (({i ∈ u | G.parent i = j} : Finset ι).card : ENNReal) ≤
            2 * (({i ∈ u | G.parent i = j'} : Finset ι).card : ENNReal)) ∧
        (∀ j ∈ G.outerSet,
          multiplicity (G.fiber j) G.innerBody =
            multiplicity {i ∈ u | G.parent i = j} G.innerBody)) ∧
      -- `boundVolumeAcrossTwoScales`: for `x ∈ U(𝕋_ρ', Y_{𝕋_ρ}')`,
      -- `|U(𝕋, Y')| ⪆ |U(𝕋_ρ', Y_{𝕋_ρ}')| · |U(𝕋, Y') ∩ B(x, ρ)| / |B(x, ρ)|`.
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank ℝ E) F.innerSet.card δ c : ENNReal)⁻¹
          * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
          * (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ Metric.ball x (ρ : ℝ))
              / volume (Metric.ball x (ρ : ℝ)))
          ≤ volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  let n := Module.finrank ℝ E
  let N := F.innerSet.card
  have hdisc : F.InnerIsDiscretizedAtScale δ :=
    { subset_unitBall := hball
      le_scale := by
        intro i hi
        rw [hinner i hi]
        exact Tube.le_ethickness_scale (T i).toTube }
  have hρpos : 0 < ρ := hδ.trans_le hρ.1
  have hρreal : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρpos
  let Ω := F.pipelineSet hδ hdisc (ρ : ℝ) hρreal
  have hΩ : MeasurableSet Ω := F.measurableSet_pipelineSet hδ hdisc (ρ : ℝ) hρreal
  obtain ⟨T₅, T₅', hT₅sub, hT₅sep, hT₅cover, hT₅overlap, hT₅'T₅, hT₅'pos, hT₅'sep,
      href₅, hballcomp⟩ :=
    exists_factoringPipelineSelf F hδ hdisc (ρ : ℝ) hρreal hΩ hρpos
  let G₅ := F.pipelineFamily hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
  have hT₅ball : (T₅ : Set E) ⊆ Metric.closedBall 0 1 := by
    refine hT₅sub.trans ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hiF : i ∈ F.innerSet := by
      rw [FactorFamily.pipelineInnerSet] at hi
      exact F.innerSet_step0_subset (Finset.mem_filter.mp hi).1
    apply hball i hiF
    have hxcarrier := (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
      (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
      (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) i).shade_subset hxi
    simpa using hxcarrier
  have hT₅card : (T₅.card : NNReal) ≤ step5PackingRatio n N δ := by
    exact card_le_step5PackingRatio hδ hρ hT₅ball hT₅sep
  have hratio1 : (1 : NNReal) ≤ step5PackingRatio n N δ := by
    rw [step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
    have hfact : (1 : NNReal) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hN : (1 : NNReal) ≤ max 1 N := by exact_mod_cast le_max_left 1 N
    have hδ1 : δ ≤ 1 := hρ.1.trans hρ.2
    have hinv : (1 : NNReal) ≤ (δ ^ n)⁻¹ := by
      rw [one_le_inv₀ (pow_pos hδ n)]
      exact pow_le_one₀ δ.coe_nonneg hδ1
    calc
      1 ≤ (2 : NNReal) ^ n := one_le_pow₀ (by norm_num)
      _ ≤ 2 ^ n * (2 ^ n * 1 * 1 * 1) := by
        simpa using le_mul_of_one_le_right (by positivity : (0 : NNReal) ≤ 2 ^ n)
          (one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2))
      _ ≤ 2 ^ n * (2 ^ n * n.factorial * max 1 N * (δ ^ n)⁻¹) := by gcongr
  have hselfpos : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n T₅.card := by
    unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
    have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1 T₅.card := by
      cases hcard : T₅.card with
      | zero =>
          have heq : Kakeya.factoringStep1FiberPigeonholeConstant 1 T₅.card = 1 := by
            rw [← ENNReal.coe_inj]
            rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant]
            simp [hcard]
          simpa [hcard] using congrArg (fun q : NNReal ↦ 0 < q) heq |>.mpr zero_lt_one
      | succ m =>
          exact lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant
              (show (1 : NNReal) ≤ (m + 1 : ℕ) by exact_mod_cast Nat.succ_pos m))
    have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
      unfold Kakeya.factoringStep5OverlapConstant
      positivity
    exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hFpos)
  have hcoef :
      (ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
        (step5PackingRatio n N δ))⁻¹ ≤
      (ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n T₅.card)⁻¹ :=
    inv_anti₀ hselfpos (step5SelfPigeonholeConstant_mono hT₅card hratio1)
  have href₅' := isCRefinement_mono hcoef href₅
  have hrefG₅ : IsCRefinement G₅.innerSet G₅.innerBody F.innerSet F.innerBody
      (ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
        (step5PackingRatio n N δ)) := by
    simpa [G₅, n, N] using
      F.pipelineFamily_isCRefinementSelf hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ href₅'
  let K : κ → ConvexSpaceBody E := fun j ↦ Kakeya.Tube.dilate (Tρ j) (c : ℝ)
  have hK : ∀ i ∈ F.innerSet, (F.innerBody i).toConvexSpaceBody ≤ K (F.parent i) := by
    intro i hi
    rw [show K (F.parent i) = F.outerBody (F.parent i) by
      exact (houter (F.parent i) (F.parent_mem i hi)).symm]
    exact F.inner_le_parent i hi
  let G := completedPipelineFamily F G₅ K ρ
    (F.pipelineFamily_outerSet_subset hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ)
    (F.pipelineFamily_parent hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ)
    (F.pipelineFamily_innerBody_toConvexSpaceBody hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ) hK
  refine ⟨G, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact F.pipelineFamily_outerSet_subset hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
      ((Finset.mem_filter.mp hj).1)
  · intro j hj
    change K j = F.outerBody j
    exact houter j (F.pipelineFamily_outerSet_subset hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
      ((Finset.mem_filter.mp hj).1)) |>.symm
  · intro i hi
    change (completedInnerBody F G₅ i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody
    by_cases hi₅ : i ∈ G₅.innerSet
    · rw [completedInnerBody, if_pos hi₅]
      exact F.pipelineFamily_innerBody_toConvexSpaceBody hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ i
    · simp [completedInnerBody, hi₅]
  · intro j hj
    have hjactive : j ∈ activeOuterSet G₅ := by
      simpa [G, completedPipelineFamily] using hj
    have hvol : volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0 :=
      (Finset.mem_filter.mp hjactive).2
    have hfibre₅ : (G₅.fiber j).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact hvol (by simp [iUnionShade, hne])
    obtain ⟨i, hi⟩ := hfibre₅
    have hi₅ : i ∈ G₅.innerSet := (Finset.mem_filter.mp hi).1
    have hip₅ : G₅.parent i = j := (Finset.mem_filter.mp hi).2
    have hiF : i ∈ F.innerSet := hrefG₅.1.1 hi₅
    have hparent₅ : G₅.parent = F.parent :=
      F.pipelineFamily_parent hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
    have hiG : i ∈ G.innerSet := by
      change i ∈ {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
      exact Finset.mem_filter.mpr ⟨hiF, by simpa [← hparent₅, hip₅] using hjactive⟩
    refine ⟨i, ?_⟩
    rw [ShadedFactorFamily.fiber]
    refine Finset.mem_filter.mpr ⟨hiG, ?_⟩
    simpa [G, completedPipelineFamily, ← hparent₅] using hip₅
  · have hsub₅ : G₅.innerSet ⊆ F.innerSet := hrefG₅.1.1
    have hparent₅ : G₅.parent = F.parent :=
      F.pipelineFamily_parent hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
    have hsum : ∑ i ∈ G.innerSet, volume (G.innerBody i).shade =
        ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
      simpa [G, completedPipelineFamily] using
        sum_volume_completedInnerBody F G₅ hsub₅ hparent₅
    have hδ1 : δ ≤ 1 := hρ.1.trans hρ.2
    have hnonempty : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade →
        G.outerSet.Nonempty := by
      intro hmass
      have hNpos : 0 < N := by
        by_contra hN0
        have he : F.innerSet = ∅ := Finset.card_eq_zero.mp (by simpa [N] using hN0)
        simp [he] at hmass
      have hA : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
        have hN1 := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
        have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
          n hN1 hδ hδ1
        rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
        rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
        apply mul_pos (by norm_num)
        rw [Real.toNNReal_pos]
        linarith
      have hB : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
        rw [Kakeya.factoringStep2Step3Constant_eq]
        positivity
      have hD : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
          (step5PackingRatio n N δ) := by
        unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
        have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
          unfold Kakeya.factoringStep5OverlapConstant
          positivity
        have hF : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
            (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
          (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
        exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hF)
      have hRpos : 0 < ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
          (step5PackingRatio n N δ) := by
        rw [pipelineRefinementConstant_eq_inv]
        positivity
      have hsum₅ : 0 < ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
        exact (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hRpos.ne') hmass.ne').trans_le hrefG₅.2
      obtain ⟨i, hi₅, hvi⟩ := Finset.sum_pos_iff.mp hsum₅
      refine ⟨G₅.parent i, ?_⟩
      change G₅.parent i ∈ activeOuterSet G₅
      apply Finset.mem_filter.mpr
      refine ⟨G₅.parent_mem i hi₅, ?_⟩
      have hmono : volume (G₅.innerBody i).shade ≤
          volume (iUnionShade (G₅.fiber (G₅.parent i)) G₅.innerBody) := by
        apply measure_mono
        exact Set.subset_iUnion₂_of_subset i
          (Finset.mem_filter.mpr ⟨hi₅, rfl⟩) (Set.Subset.refl _)
      exact ne_of_gt (hvi.trans_le hmono)
    refine ⟨hnonempty, ?_⟩
    have hrefG : IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
          (step5PackingRatio n N δ)) := by
      constructor
      · constructor
        · intro i hi
          exact (Finset.mem_filter.mp hi).1
        · intro i hi
          by_cases hi₅ : i ∈ G₅.innerSet
          · rw [show G.innerBody i = G₅.innerBody i by
                simp [G, completedPipelineFamily, completedInnerBody, hi₅]]
            exact hrefG₅.1.2 i hi₅
          · constructor
            · simp [G, completedPipelineFamily, completedInnerBody, hi₅]
            · simp [G, completedPipelineFamily, completedInnerBody, hi₅]
      · rw [hsum]
        exact hrefG₅.2
    have hrefFinal : IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
        (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ := by
      by_cases hN0 : N = 0
      · have he : F.innerSet = ∅ := Finset.card_eq_zero.mp (by simpa [N] using hN0)
        refine ⟨hrefG.1, ?_⟩
        simp [he]
      · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have hA : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
          have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
            n hN1 hδ hδ1
          rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
          rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
          apply mul_pos (by norm_num)
          rw [Real.toNNReal_pos]
          linarith
        have hB : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          positivity
        have hD : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
          have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
            unfold Kakeya.factoringStep5OverlapConstant
            positivity
          have hF : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
              (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
          exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hF)
        have hCinv : (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ ≤
            ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) := by
          rw [pipelineRefinementConstant_eq_inv]
          exact inv_anti₀ (by positivity) (pipelineLoss_le_C n N δ c hc)
        exact isCRefinement_mono hCinv hrefG
    refine ⟨?_, hrefFinal, ?_⟩
    · by_cases hmass0 : ∑ i ∈ F.innerSet, volume (F.innerBody i).shade = 0
      · have hfzero : fullness F.innerSet F.innerBody = 0 := by
          apply ENNReal.coe_injective
          calc
            (fullness F.innerSet F.innerBody : ENNReal) = fullness' F.innerSet F.innerBody :=
              coe_fullness F.innerSet F.innerBody
            _ = 0 := by simp [fullness', hmass0]
            _ = (0 : NNReal) := rfl
        rw [hfzero]
        simp
      · have ht : G.outerSet.Nonempty := hnonempty (pos_iff_ne_zero.mpr hmass0)
        let A : κ → ENNReal := fun j ↦ fiberVolume F (F.pipelineInnerSet hδ hdisc) j
        let KV : κ → ENNReal := fun j ↦ volume (K j).carrier
        let S : κ → ENNReal := fun j ↦
          ∑ i ∈ G₅.fiber j, volume (G₅.innerBody i).shade
        let O : κ → ENNReal := fun j ↦ volume (G.outerBody j).shade
        let Q : ENNReal :=
          (Tube.volume_le.C n / Tube.le_volume.c n : NNReal)
        let D : ENNReal := (Kakeya.Tube.dilateFullness.C n : ENNReal) *
          ENNReal.ofReal ((c : ℝ) ^ n)
        have hAcomp : ∀ j ∈ G.outerSet, ∀ j' ∈ G.outerSet, A j ≤ 2 * A j' := by
          intro j hj j' hj'
          exact F.pipelineFamily_fiberVolume_le_two_mul hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
            (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj').1
        have hKcomp : ∀ j ∈ G.outerSet, ∀ j' ∈ G.outerSet, KV j ≤ Q * KV j' := by
          intro j _ j' _
          exact volume_dilate_le_ratio_mul hρ.2 (by positivity) (Tρ j) (Tρ j')
        have hblock : ∀ j ∈ G.outerSet, S j * KV j ≤ D * O j * A j := by
          intro j hj
          have hjactive : j ∈ activeOuterSet G₅ := by simpa [G, completedPipelineFamily] using hj
          have hterm : ∀ i ∈ G₅.fiber j,
              (volume (G₅.innerBody i).shade / volume (T i).carrier) * KV j ≤
                D * O j := by
            intro i hi
            have hi₅ : i ∈ G₅.innerSet := (Finset.mem_filter.mp hi).1
            have hip : F.parent i = j := by
              simpa [hparent₅] using (Finset.mem_filter.mp hi).2
            have hiF : i ∈ F.innerSet := hsub₅ hi₅
            have hY : (G₅.innerBody i).shade ⊆ (T i).carrier := by
              have hcarr := hrefG₅.1.2 i hi₅
              calc
                (G₅.innerBody i).shade ⊆ (G₅.innerBody i).carrier :=
                  (G₅.innerBody i).shade_subset
                _ = (F.innerBody i).carrier := congrArg ConvexSpaceBody.carrier hcarr.1
                _ = (T i).carrier := congrArg (fun W : ShadedBody E ↦ W.carrier) (hinner i hiF)
            have hsubK : (T i).carrier ⊆ (K j).carrier := by
              have hb : (F.innerBody i).carrier = (T i).carrier :=
                congrArg (fun W : ShadedBody E ↦ W.carrier) (hinner i hiF)
              rw [← hb, ← hip]
              exact hK i hiF
            have hgeom := Kakeya.Tube.volume_dilate_inter_cthickening_ge hδ hρ.1 hρ.2 hc
              (T i).toTube (Tρ j) hsubK hY
            have hinter : (K j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
                (G₅.innerBody i).shade ⊆ (G.outerBody j).shade := by
              simpa only [G, completedPipelineFamily] using
                inter_cthickening_shade_subset_rhoCompletedOuterBody
                  F G₅ K ρ hjactive hi₅ hiF hip
            exact hgeom.trans (mul_le_mul_right (measure_mono hinter)
              ((Kakeya.Tube.dilateFullness.C n : ENNReal) *
                ENNReal.ofReal ((c : ℝ) ^ n)))
          have hV0 : ∀ i ∈ G₅.fiber j, volume (T i).carrier ≠ 0 := by
            intro i hi
            apply ne_of_gt
            apply (pos_iff_ne_zero.mpr ?_).trans_le (Tube.le_volume (T i).toTube)
            exact mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
              (pow_ne_zero _ (by exact_mod_cast hδ.ne'))
          have hVtop : ∀ i ∈ G₅.fiber j, volume (T i).carrier ≠ ⊤ := by
            intro i _
            exact (T i).toShadedBody.isCompact.measure_lt_top.ne
          have hs := sum_mul_le_of_div_mul_le (G₅.fiber j)
            (fun i ↦ volume (G₅.innerBody i).shade)
            (fun i ↦ volume (T i).carrier) (KV j) (D * O j) hV0 hVtop hterm
          have hfiber : G₅.fiber j =
              {i ∈ F.pipelineInnerSet hδ hdisc | F.parent i = j} := by
            ext q
            simp [G₅, ShadedFactorFamily.fiber]
          have hcar : ∑ i ∈ G₅.fiber j, volume (T i).carrier = A j := by
            rw [hfiber]
            rw [show A j = fiberVolume F (F.pipelineInnerSet hδ hdisc) j by rfl]
            rw [fiberVolume_eq_sum]
            apply Finset.sum_congr rfl
            intro i hi
            have hiP : i ∈ F.pipelineInnerSet hδ hdisc := (Finset.mem_filter.mp hi).1
            rw [FactorFamily.pipelineInnerSet] at hiP
            have hiF : i ∈ F.innerSet := F.innerSet_step0_subset (Finset.mem_filter.mp hiP).1
            exact congrArg volume (congrArg (fun W : ShadedBody E ↦ W.carrier)
              (hinner i hiF)).symm
          rw [hcar] at hs
          simpa only [S, KV, D, mul_assoc] using hs
        have hagg := sum_mul_sum_le_of_pairwise_comparable G.outerSet ht A KV S O Q D
          hAcomp hKcomp hblock
        have hSsum : ∑ j ∈ G.outerSet, S j =
            ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
          have hall : ∑ j ∈ G₅.outerSet, S j =
              ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := by
            simpa [S, ShadedFactorFamily.fiber] using
              (Finset.sum_fiberwise_of_maps_to G₅.parent_mem
                (fun i ↦ volume (G₅.innerBody i).shade))
          rw [← hall]
          apply Finset.sum_subset (by
            intro j hj
            exact (Finset.mem_filter.mp hj).1)
          intro j hj hja
          have hz : volume (iUnionShade (G₅.fiber j) G₅.innerBody) = 0 := by
            by_contra hnz
            exact hja (by
              change j ∈ activeOuterSet G₅
              exact Finset.mem_filter.mpr ⟨hj, hnz⟩)
          apply Finset.sum_eq_zero
          intro i hi
          exact measure_mono_null
            (Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)) hz
        have hAsum : ∑ j ∈ G.outerSet, A j ≤
            ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
          calc
            ∑ j ∈ G.outerSet, A j ≤ ∑ j ∈ G₅.outerSet, A j := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (fun j hj ↦ (Finset.mem_filter.mp hj).1) (fun _ _ _ ↦ bot_le)
            _ = ∑ i ∈ F.pipelineInnerSet hδ hdisc,
                volume (F.innerBody i).carrier := by
              simp_rw [A, fiberVolume_eq_sum]
              exact Finset.sum_fiberwise_of_maps_to
                (fun i hi ↦ by
                  rw [← FactorFamily.pipelineFamily_innerSet F hδ hdisc (ρ : ℝ)
                    hρreal hΩ T₅' ρ] at hi
                  exact G₅.parent_mem i hi)
                (fun i ↦ volume (F.innerBody i).carrier)
            _ ≤ ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hrefG₅.1.1 (fun _ _ _ ↦ bot_le)
        have hcross :
            (∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade) *
                (∑ j ∈ G.outerSet, volume (G.outerBody j).carrier) ≤
              4 * Q ^ 2 * D *
                (∑ j ∈ G.outerSet, volume (G.outerBody j).shade) *
                (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
          calc
            _ = (∑ j ∈ G.outerSet, S j) * (∑ j ∈ G.outerSet, KV j) := by
              rw [hSsum]
              rfl
            _ ≤ 4 * Q ^ 2 * D * (∑ j ∈ G.outerSet, O j) *
                (∑ j ∈ G.outerSet, A j) := hagg
            _ ≤ 4 * Q ^ 2 * D *
                (∑ j ∈ G.outerSet, volume (G.outerBody j).shade) *
                (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
              dsimp only [O]
              gcongr
        let P : NNReal := Kakeya.factoringStep1AtScaleConstant n N δ *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ)
        let H : ENNReal := 4 * Q ^ 2 * D
        let C₀ : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c
        let SF : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).shade
        let CF : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
        let ST : ENNReal := ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade
        let OT : ENNReal := ∑ j ∈ G.outerSet, volume (G.outerBody j).shade
        let KT : ENNReal := ∑ j ∈ G.outerSet, volume (G.outerBody j).carrier
        have hNpos : 0 < N := by
          by_contra hN0
          have he : F.innerSet = ∅ := Finset.card_eq_zero.mp (by simpa [N] using hN0)
          exact hmass0 (by simp [he])
        have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
        have hApos : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
          have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
            n hN1 hδ hδ1
          rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
          rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
          apply mul_pos (by norm_num)
          rw [Real.toNNReal_pos]
          linarith
        have hBpos : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          positivity
        have hDpos : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
          have hOpos : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
            unfold Kakeya.factoringStep5OverlapConstant
            positivity
          have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
              (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
          exact mul_pos (mul_pos (by norm_num) hOpos) (mul_pos (by norm_num) hFpos)
        have hPpos : 0 < P := mul_pos (mul_pos hApos hBpos) hDpos
        have hgeopos : 0 < c ^ n * rhoTubesGeometricLoss n := by
          have hgeo1 : (1 : NNReal) ≤ rhoTubesGeometricLoss n := by
            unfold rhoTubesGeometricLoss
            calc
              1 ≤ (4 : NNReal) := by norm_num
              _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) := by
                simpa only [mul_one] using
                  mul_le_mul_right (le_max_left (1 : NNReal) _) (4 : NNReal)
              _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                  max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 := by
                apply le_mul_of_one_le_right (by positivity)
                exact one_le_pow₀ (le_max_left (1 : NNReal) _)
              _ ≤ 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                  max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                    max 1 (rhoTubesOuterMultiplicityLoss n) := by
                apply le_mul_of_one_le_right (by positivity)
                exact le_max_left _ _
          exact mul_pos (pow_pos (zero_lt_one.trans_le hc) n) (zero_lt_one.trans_le hgeo1)
        have hPHC : P * (c ^ n * rhoTubesGeometricLoss n) ≤ C₀ := by
          exact pipelineGeometricLoss_le_C n N δ c
        have hcoefNN : C₀⁻¹ * (c ^ n * rhoTubesGeometricLoss n) ≤ P⁻¹ := by
          calc
            C₀⁻¹ * (c ^ n * rhoTubesGeometricLoss n) ≤
                (P * (c ^ n * rhoTubesGeometricLoss n))⁻¹ *
                  (c ^ n * rhoTubesGeometricLoss n) := by
              gcongr
            _ = P⁻¹ := by
              rw [mul_inv, mul_assoc, inv_mul_cancel₀ hgeopos.ne', mul_one]
        have hHgeo : H ≤ (c ^ n * rhoTubesGeometricLoss n : NNReal) := by
          dsimp only [H, Q, D]
          rw [show ENNReal.ofReal ((c : ℝ) ^ n) = (c ^ n : NNReal) by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_coe_nnreal,
              ENNReal.coe_pow]]
          have hNN : (4 : NNReal) *
              (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                (Kakeya.Tube.dilateFullness.C n * c ^ n) ≤
              c ^ n * rhoTubesGeometricLoss n := by
            unfold rhoTubesGeometricLoss
            calc
              (4 : NNReal) *
                  (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                    (Kakeya.Tube.dilateFullness.C n * c ^ n)
                  = c ^ n * (4 * Kakeya.Tube.dilateFullness.C n *
                      (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2) := by ring
              _ ≤ c ^ n * (4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                    max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2) := by
                gcongr
                · exact le_max_right _ _
                · exact le_max_right _ _
              _ ≤ c ^ n * (4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
                    max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2 *
                      max 1 (rhoTubesOuterMultiplicityLoss n)) := by
                apply mul_le_mul_right
                apply le_mul_of_one_le_right (by positivity)
                exact le_max_left _ _
          exact_mod_cast hNN
        have hC₀pos : 0 < C₀ := zero_lt_one.trans_le
          (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n N δ c)
        have hcoef : (C₀ : ENNReal)⁻¹ * H ≤ (P : ENNReal)⁻¹ := by
          calc
            (C₀ : ENNReal)⁻¹ * H ≤
                (C₀ : ENNReal)⁻¹ * (c ^ n * rhoTubesGeometricLoss n : NNReal) := by
              gcongr
            _ ≤ (P : ENNReal)⁻¹ := by
              rw [← ENNReal.coe_inv hC₀pos.ne',
                ← ENNReal.coe_mul, ← ENNReal.coe_inv hPpos.ne']
              exact ENNReal.coe_le_coe.mpr hcoefNN
        have hrefmass : (P : ENNReal)⁻¹ * SF ≤ ST := by
          have hR : ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) = P⁻¹ := by
            simpa only [P] using pipelineRefinementConstant_eq_inv n N δ
          rw [hR] at hrefG₅
          rw [← ENNReal.coe_inv hPpos.ne']
          exact hrefG₅.2
        have hCF0 : CF ≠ 0 := by
          intro hzero
          apply hmass0
          apply le_antisymm
          · calc
              SF ≤ CF := Finset.sum_le_sum fun i _ ↦ measure_mono (F.innerBody i).shade_subset
              _ = 0 := hzero
          · exact bot_le
        have hCFtop : CF ≠ ⊤ := by
          dsimp only [CF]
          exact ENNReal.sum_ne_top.mpr fun i _ ↦ (F.innerBody i).isCompact.measure_lt_top.ne
        have hKT0 : KT ≠ 0 := by
          obtain ⟨j, hj⟩ := ht
          apply ne_of_gt
          apply (Finset.single_le_sum (fun _ _ ↦ bot_le) hj).trans_lt'
          change 0 < volume (K j).carrier
          rw [rho_volume_dilate_eq (Tρ j) (by positivity)]
          apply ENNReal.mul_pos
          · exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)).ne'
          · exact (lt_of_lt_of_le (by
                exact_mod_cast mul_pos (Tube.le_volume.c_pos n) (pow_pos hρpos (n - 1)))
              (Tube.le_volume (Tρ j))).ne'
        have hKTtop : KT ≠ ⊤ := by
          dsimp only [KT]
          exact ENNReal.sum_ne_top.mpr fun j _ ↦ (G.outerBody j).isCompact.measure_lt_top.ne
        have hH0 : H ≠ 0 := by
          dsimp only [H, Q, D]
          apply mul_ne_zero
          · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by
              exact_mod_cast (div_pos (Tube.volume_le.C_pos n) (Tube.le_volume.c_pos n)).ne'))
          · exact mul_ne_zero (by exact_mod_cast (Kakeya.Tube.dilateFullness.C_pos n).ne')
              (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)).ne'
        have hHtop : H ≠ ⊤ := by
          dsimp only [H, Q, D]
          finiteness
        have hscaled : ((C₀ : ENNReal)⁻¹ * H * SF) * KT ≤ H * (OT * CF) := by
          calc
            ((C₀ : ENNReal)⁻¹ * H * SF) * KT ≤
                ((P : ENNReal)⁻¹ * SF) * KT := by gcongr
            _ ≤ ST * KT := by gcongr
            _ ≤ H * (OT * CF) := by
              simpa [H, ST, OT, KT, CF, mul_assoc] using hcross
        have hproduct : ((C₀ : ENNReal)⁻¹ * SF) * KT ≤ OT * CF := by
          apply (ENNReal.mul_le_mul_iff_right hH0 hHtop).1
          simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
        have hquot : ((C₀ : ENNReal)⁻¹ * SF) / CF ≤ OT / KT :=
          ennreal_div_le_div_of_mul_le_mul hCF0 hCFtop hKT0 hKTtop hproduct
        have hfinal : (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ *
            fullness F.innerSet F.innerBody ≤ fullness G.outerSet G.outerBody := by
          apply ENNReal.coe_le_coe.mp
          calc
            (((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ *
                  fullness F.innerSet F.innerBody : NNReal) : ENNReal) =
                (C₀ : ENNReal)⁻¹ * (SF / CF) := by
              calc
                _ = ((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ :
                      NNReal) * (fullness F.innerSet F.innerBody : ENNReal) :=
                    ENNReal.coe_mul _ _
                _ = (C₀ : ENNReal)⁻¹ * (SF / CF) := by
                  rw [ENNReal.coe_inv hC₀pos.ne', coe_fullness]
            _ ≤ OT / KT := by simpa only [mul_div_assoc] using hquot
            _ = (fullness G.outerSet G.outerBody : ENNReal) := by
              rw [coe_fullness]
        simpa only [n, N] using hfinal
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        let u := F.step0.innerSet
        let t' := (F.step1 hδ hdisc).outerSet
        let k := F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal
        let l := F.pipelineOuterExponent hδ hdisc (ρ : ℝ) hρreal
        let Z : Set E := ⋃ q ∈ G₅.outerSet.filter (fun q ↦ q ∉ activeOuterSet G₅),
          iUnionShade (G₅.fiber q) G₅.innerBody
        have hZzero : volume Z = 0 := by
          change volume (⋃ q ∈ ((G₅.outerSet.filter
            (fun q ↦ q ∉ activeOuterSet G₅)) : Set κ),
              iUnionShade (G₅.fiber q) G₅.innerBody) = 0
          apply (measure_biUnion_null_iff
            (Set.to_countable ((G₅.outerSet.filter
              (fun q ↦ q ∉ activeOuterSet G₅)) : Set κ))).2
          intro q hq
          obtain ⟨hqG, hqnot⟩ := Finset.mem_filter.mp hq
          by_contra hne
          exact hqnot (Finset.mem_filter.mpr ⟨hqG, hne⟩)
        have hcoverW : iUnionShade G.outerSet G.outerBody ⊆
            ⋃ z ∈ T₅', Metric.closedBall z (4 * (ρ : ℝ)) := by
          intro y hy
          obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp hy
          change y ∈ (K q).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
              (completedInnerBody F G₅)) at hyq
          have hthick := Metric.cthickening_subset_iUnion_closedBall_of_lt
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
              (completedInnerBody F G₅))
            (show (0 : ℝ) < 3 * (ρ : ℝ) by positivity)
            (show 2 * (ρ : ℝ) < 3 * (ρ : ℝ) by linarith) hyq.2
          obtain ⟨z, hzfib, hyz⟩ := Set.mem_iUnion₂.mp hthick
          have hqactive : q ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hq
          have hz₅ : z ∈ iUnionShade (G₅.fiber q) G₅.innerBody := by
            rw [← iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hqactive]
            exact hzfib
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz₅
          have hzi' : z ∈ (step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
              (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) T₅' ρ i).shade := by
            simpa [G₅, FactorFamily.pipelineFamily] using hzi
          rw [shade_step5InnerBody] at hzi'
          obtain ⟨z₀, hz₀, hzz₀⟩ := Set.mem_iUnion₂.mp hzi'.2
          refine Set.mem_iUnion₂.mpr ⟨z₀, hz₀, Metric.mem_closedBall.mpr ?_⟩
          calc
            dist y z₀ ≤ dist y z + dist z z₀ := dist_triangle _ _ _
            _ ≤ 3 * (ρ : ℝ) + (ρ : ℝ) := by
              gcongr
              · exact Metric.mem_closedBall.mp hyz
              · exact Metric.mem_closedBall.mp hzz₀
            _ = 4 * (ρ : ℝ) := by ring
        have hT₅'ne : T₅'.Nonempty := by
          have hjactive : j ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj
          have hvolj : volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0 :=
            (Finset.mem_filter.mp hjactive).2
          obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvolj
          obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          have hyi' : y ∈ (step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
              (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) T₅' ρ i).shade := by
            simpa [G₅, FactorFamily.pipelineFamily] using hyi
          rw [shade_step5InnerBody] at hyi'
          obtain ⟨z, hz, _⟩ := Set.mem_iUnion₂.mp hyi'.2
          exact ⟨z, hz⟩
        have hlocal : ∀ z ∈ T₅', ∃ J : Finset κ, J ⊆ G.outerSet ∧
            2 ^ l ≤ J.card ∧ ∀ q ∈ J, ∃ p : E,
              Metric.ball p ((ρ : ℝ) / 8) ⊆
                (G.outerBody q).shade ∩ Metric.ball z (2 * (ρ : ℝ)) := by
          intro z hz
          let A : Set E := iUnionShade G₅.innerSet G₅.innerBody ∩
            Metric.closedBall z (ρ : ℝ)
          have hA0 : volume A ≠ 0 := by
            simpa [A, G₅] using hT₅'pos z hz
          have hnotSub : ¬ A ⊆ Z := by
            intro hAZ
            exact hA0 (measure_mono_null hAZ hZzero)
          obtain ⟨y, hyA, hyZ⟩ := Set.not_subset.mp hnotSub
          have hyG₅ : y ∈ iUnionShade G₅.innerSet G₅.innerBody := hyA.1
          obtain ⟨i₀, hi₀, hyi₀⟩ := Set.mem_iUnion₂.mp hyG₅
          have hyi₀' : y ∈ (step5InnerBody F u t'
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ i₀).shade := by
            simpa [G₅, FactorFamily.pipelineFamily, u, t', k] using hyi₀
          rw [shade_step5InnerBody, shade_step3InnerBody] at hyi₀'
          have hyΩ : y ∈ F.pipelineSet hδ hdisc (ρ : ℝ) hρreal := hyi₀'.1.1.2
          have hySel : y ∈ step5Selection T₅' ρ := hyi₀'.2
          let J := MultiplicityFamily.dyadicLevel t'
            (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k y
          refine ⟨J, ?_, ?_, ?_⟩
          · intro q hq
            have hqt' : q ∈ t' := (Finset.mem_filter.mp hq).1
            have hqG₅ : q ∈ G₅.outerSet := by
              simpa [G₅, FactorFamily.pipelineFamily, t'] using hqt'
            have hqactive : q ∈ activeOuterSet G₅ := by
              apply Finset.mem_filter.mpr
              refine ⟨hqG₅, ?_⟩
              intro hzero
              have hyfiber : y ∈ iUnionShade (G₅.fiber q) G₅.innerBody := by
                have hpos : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q y :=
                  lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
                change 0 < ({i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = q} |
                  y ∈ (F.innerBody i).shade}).card at hpos
                obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
                have hi' := Finset.mem_filter.mp hi
                have hib := Finset.mem_filter.mp hi'.1
                have hip := hib.2
                refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
                · exact Finset.mem_filter.mpr ⟨by
                    simpa [G₅, FactorFamily.pipelineFamily, FactorFamily.pipelineInnerSet,
                      u, t'] using hib.1, by
                    simp [G₅, FactorFamily.pipelineFamily, hip]⟩
                · change y ∈ (step5InnerBody F u t'
                    (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ i).shade
                  rw [shade_step5InnerBody, shade_step3InnerBody]
                  refine ⟨⟨⟨hi'.2, hyΩ⟩, ?_⟩, hySel⟩
                  simpa [step3DyadicSet, hip] using (Finset.mem_filter.mp hq).2
              apply hyZ
              exact Set.mem_iUnion₂.mpr ⟨q,
                Finset.mem_filter.mpr ⟨hqG₅, fun ha ↦
                  (Finset.mem_filter.mp ha).2 hzero⟩, hyfiber⟩
            simpa [G, completedPipelineFamily] using hqactive
          · have hb := F.bounds_of_mem_pipelineSet hδ hdisc (ρ : ℝ) hρreal hyΩ
            simpa [J, l, k, t', u, FactorFamily.pipelineInnerSet] using hb.2.2.1
          · intro q hq
            have hqt' : q ∈ t' := (Finset.mem_filter.mp hq).1
            have hpos : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q y :=
              lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
            change 0 < ({i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = q} |
              y ∈ (F.innerBody i).shade}).card at hpos
            obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
            have hi' := Finset.mem_filter.mp hi
            have hib := Finset.mem_filter.mp hi'.1
            have hiu := (Finset.mem_filter.mp hib.1).1
            have hip := hib.2
            have hiF : i ∈ F.innerSet := F.innerSet_step0_subset hiu
            have hyK : y ∈ (K q).carrier := by
              change y ∈ K q
              simpa [hip] using hK i hiF ((F.innerBody i).shade_subset hi'.2)
            have hycapsule : y ∈ Metric.cthickening ((c : ℝ) * (ρ : ℝ))
                (segment ℝ (AffineMap.homothety (Tρ q).center (c : ℝ) (Tρ q).x)
                  (AffineMap.homothety (Tρ q).center (c : ℝ) (Tρ q).y)) := by
              rw [← Kakeya.Tube.dilate_carrier_eq_cthickening (Tρ q) (by positivity)]
              exact hyK
            obtain ⟨p, hp⟩ := Kakeya.exists_ball_subset_cthickening_inter_ball
              isCompact_segment hρreal (by
                have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
                nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hcR) hρreal]) hycapsule
            refine ⟨p, ?_⟩
            intro w hw
            have hwK : w ∈ (K q).carrier := by
              change w ∈ (Kakeya.Tube.dilate (Tρ q) (c : ℝ)).carrier
              rw [Kakeya.Tube.dilate_carrier_eq_cthickening (Tρ q) (by positivity)]
              exact (hp hw).1
            have hqactive : q ∈ activeOuterSet G₅ := by
              have hqG : q ∈ G.outerSet := by
                apply (show J ⊆ G.outerSet from ?_) hq
                intro q' hq'
                have hqt'' : q' ∈ t' := (Finset.mem_filter.mp hq').1
                have hqG₅ : q' ∈ G₅.outerSet := by
                  simpa [G₅, FactorFamily.pipelineFamily, t'] using hqt''
                apply Finset.mem_filter.mpr
                refine ⟨hqG₅, ?_⟩
                intro hzfiber
                have hyfiber : y ∈ iUnionShade (G₅.fiber q') G₅.innerBody := by
                  have hp' := (Finset.mem_filter.mp hq').2
                  have hpos' : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q' y :=
                    lt_of_lt_of_le (pow_pos (by omega) k) hp'.1
                  change 0 < ({a ∈ {a ∈ {a ∈ u | F.parent a ∈ t'} | F.parent a = q'} |
                    y ∈ (F.innerBody a).shade}).card at hpos'
                  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos'
                  have ha' := Finset.mem_filter.mp ha
                  have hab := Finset.mem_filter.mp ha'.1
                  have hap := hab.2
                  refine Set.mem_iUnion₂.mpr ⟨a, ?_, ?_⟩
                  · exact Finset.mem_filter.mpr ⟨by
                      simpa [G₅, FactorFamily.pipelineFamily,
                        FactorFamily.pipelineInnerSet, u, t'] using hab.1, by
                      simp [G₅, FactorFamily.pipelineFamily, hap]⟩
                  · change y ∈ (step5InnerBody F u t'
                      (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ a).shade
                    rw [shade_step5InnerBody, shade_step3InnerBody]
                    refine ⟨⟨⟨ha'.2, hyΩ⟩, ?_⟩, hySel⟩
                    simpa [step3DyadicSet, hap] using hp'
                exact hyZ (Set.mem_iUnion₂.mpr ⟨q',
                  Finset.mem_filter.mpr ⟨hqG₅, fun ha ↦
                    (Finset.mem_filter.mp ha).2 hzfiber⟩, hyfiber⟩)
              simpa [G, completedPipelineFamily] using hqG
            have hyfiber : y ∈ iUnionShade (G₅.fiber q) G₅.innerBody := by
              have hqG₅ : q ∈ G₅.outerSet := by
                simpa [G₅, FactorFamily.pipelineFamily, t'] using hqt'
              have hiG₅ : i ∈ G₅.innerSet := by
                simpa [G₅, FactorFamily.pipelineFamily, FactorFamily.pipelineInnerSet,
                  u, t'] using hib.1
              refine Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hiG₅, by
                simp [G₅, FactorFamily.pipelineFamily, hip]⟩, ?_⟩
              change y ∈ (step5InnerBody F u t'
                (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ k T₅' ρ i).shade
              rw [shade_step5InnerBody, shade_step3InnerBody]
              refine ⟨⟨⟨hi'.2, hyΩ⟩, ?_⟩, hySel⟩
              simpa [step3DyadicSet, hip] using (Finset.mem_filter.mp hq).2
            have hwthick : w ∈ Metric.cthickening (2 * (ρ : ℝ))
                (iUnionShade {i ∈ F.innerSet |
                  F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
                  (completedInnerBody F G₅)) := by
              apply Metric.mem_cthickening_of_dist_le w y _ _
              · rw [iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hqactive]
                exact hyfiber
              · exact le_trans (le_of_lt (Metric.mem_ball.mp (hp hw).2)) (by linarith)
            constructor
            · change w ∈ (K q).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
                (iUnionShade {i ∈ F.innerSet |
                  F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = q}
                  (completedInnerBody F G₅))
              exact ⟨hwK, hwthick⟩
            · apply Metric.mem_ball.mpr
              calc
                dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
                _ < (ρ : ℝ) + (ρ : ℝ) := add_lt_add_of_lt_of_le
                  (Metric.mem_ball.mp (hp hw).2) (Metric.mem_closedBall.mp hyA.2)
                _ = 2 * (ρ : ℝ) := by ring
        have hlpos : 0 < 2 ^ l := pow_pos (by omega) l
        have houterLower : (2 ^ l : ENNReal) ≤
            (rhoTubesOuterMultiplicityLoss n : ENNReal) *
              multiplicity G.outerSet G.outerBody := by
          simpa [n] using outerMultiplicity_lower_of_local_balls G.outerSet G.outerBody
            T₅' ρ (2 ^ l) hρpos hlpos hT₅'ne hT₅'sep hcoverW hlocal
        have hglobal : multiplicity G₅.innerSet G₅.innerBody ≤
            (4 * (2 ^ k * 2 ^ l) : ℕ) := by
          apply multiplicity_le_of_pointwiseMultiplicity_le
          intro x hx
          exact_mod_cast (F.pipelineFamily_multiplicity hδ hdisc (ρ : ℝ) hρreal
            hΩ T₅' ρ hx).2.le
        have hjactive : j ∈ activeOuterSet G₅ := by
          simpa [G, completedPipelineFamily] using hj
        have hfiberUnion0 : volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0 :=
          (Finset.mem_filter.mp hjactive).2
        have hfiberLower₅ : (2 ^ k : ENNReal) ≤
            multiplicity (G₅.fiber j) G₅.innerBody := by
          apply le_multiplicity_of_le_pointwiseMultiplicity _ _ hfiberUnion0
          intro x hx
          exact_mod_cast (F.pipelineFamily_fiber_multiplicity hδ hdisc (ρ : ℝ)
            hρreal hΩ T₅' ρ hx).1
        have hfiberEq : multiplicity (G₅.fiber j) G₅.innerBody =
            multiplicity (G.fiber j) G.innerBody := by
          rw [multiplicity_eq_div, multiplicity_eq_div]
          have hGfiber : G.fiber j =
              {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j} := by
            ext i
            simp [G, completedPipelineFamily, ShadedFactorFamily.fiber, and_assoc]
          rw [hGfiber]
          have hGinner : G.innerBody = completedInnerBody F G₅ := rfl
          rw [hGinner]
          rw [sum_volume_completed_fiber F G₅ hsub₅ hparent₅ hjactive]
          congr 1
          exact congrArg volume
            (iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hjactive).symm
        have hfiberLower : (2 ^ k : ENNReal) ≤ multiplicity (G.fiber j) G.innerBody :=
          hfiberEq ▸ hfiberLower₅
        have hNpos' : 0 < N := by
          have hfiberNe : (G₅.fiber j).Nonempty := by
            by_contra he
            have he' : G₅.fiber j = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
            exact hfiberUnion0 (by simp [he', iUnionShade])
          obtain ⟨i, hi⟩ := hfiberNe
          have hiF : i ∈ F.innerSet := hsub₅ (Finset.mem_filter.mp hi).1
          simpa [N] using F.innerSet.card_pos.mpr ⟨i, hiF⟩
        have hN1' : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos'.ne'
        have hApos' : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
          have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
            n hN1' hδ hδ1
          rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1' hδ] at hl
          rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1' hδ]
          apply mul_pos (by norm_num)
          rw [Real.toNNReal_pos]
          linarith
        have hBpos' : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
          rw [Kakeya.factoringStep2Step3Constant_eq]
          positivity
        have hDpos' : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
            (step5PackingRatio n N δ) := by
          unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
          have hOpos : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
            unfold Kakeya.factoringStep5OverlapConstant
            positivity
          have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
              (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
          exact mul_pos (mul_pos (by norm_num) hOpos) (mul_pos (by norm_num) hFpos)
        have hP0' : Kakeya.factoringStep1AtScaleConstant n N δ *
            (Kakeya.factoringStep2Step3Constant N : NNReal) *
            ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
              (step5PackingRatio n N δ) ≠ 0 :=
          (mul_pos (mul_pos hApos' hBpos') hDpos').ne'
        have hrefMu : multiplicity F.innerSet F.innerBody ≤
            ((Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) : NNReal) : ENNReal)⁻¹ *
              multiplicity G₅.innerSet G₅.innerBody := by
          apply multiplicity_le_of_isCRefinement
          · rw [pipelineRefinementConstant_eq_inv]
            exact inv_ne_zero hP0'
          · exact hrefG₅
        have hPinv : ((Kakeya.factoringPipelineSelfRefinementConstant n N δ
              (step5PackingRatio n N δ) : NNReal) : ENNReal)⁻¹ =
            (Kakeya.factoringStep1AtScaleConstant n N δ *
              (Kakeya.factoringStep2Step3Constant N : NNReal) *
              ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                (step5PackingRatio n N δ) : NNReal) := by
          rw [pipelineRefinementConstant_eq_inv]
          rw [ENNReal.coe_inv hP0']
          rw [inv_inv]
        rw [hPinv] at hrefMu
        calc
          multiplicity F.innerSet F.innerBody ≤
              (Kakeya.factoringStep1AtScaleConstant n N δ *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                  (step5PackingRatio n N δ) : NNReal) *
                multiplicity G₅.innerSet G₅.innerBody := hrefMu
          _ ≤ (Kakeya.factoringStep1AtScaleConstant n N δ *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                  (step5PackingRatio n N δ) : NNReal) *
              (4 * ((2 ^ k : ENNReal) * (2 ^ l : ENNReal))) := by
            gcongr
            simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hglobal
          _ ≤ (4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
                (Kakeya.factoringStep2Step3Constant N : NNReal) *
                ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                  (step5PackingRatio n N δ)) *
                rhoTubesOuterMultiplicityLoss n : NNReal) *
              multiplicity G.outerSet G.outerBody *
              multiplicity (G.fiber j) G.innerBody := by
            calc
              _ = (4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
                    (Kakeya.factoringStep2Step3Constant N : NNReal) *
                    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                      (step5PackingRatio n N δ)) : NNReal) *
                    (2 ^ l : ENNReal) * (2 ^ k : ENNReal) := by
                push_cast
                ring
              _ ≤ (4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
                    (Kakeya.factoringStep2Step3Constant N : NNReal) *
                    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
                      (step5PackingRatio n N δ)) : NNReal) *
                    ((rhoTubesOuterMultiplicityLoss n : ENNReal) *
                      multiplicity G.outerSet G.outerBody) *
                    multiplicity (G.fiber j) G.innerBody := by gcongr
              _ = _ := by
                push_cast
                ring
          _ ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : NNReal) *
              multiplicity G.outerSet G.outerBody *
              multiplicity (G.fiber j) G.innerBody := by
            gcongr
            exact_mod_cast four_mul_pipeline_outerLoss_le_C n N δ c hc
      · intro i hi
        exact G.shade_subset_parent i hi
      · have hsub₅ : G₅.innerSet ⊆ F.innerSet := hrefG₅.1.1
        have hparent₅ : G₅.parent = F.parent :=
          F.pipelineFamily_parent hδ hdisc (ρ : ℝ) hρreal hΩ T₅' ρ
        let ua : Finset ι :=
          {i ∈ G₅.innerSet | G₅.parent i ∈ activeOuterSet G₅}
        have huaFiber (j : κ) (hj : j ∈ G.outerSet) :
            {i ∈ ua | G.parent i = j} = G₅.fiber j := by
          have hjactive : j ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj
          ext i
          simp only [ua, ShadedFactorFamily.fiber, Finset.mem_filter]
          constructor
          · intro hi
            exact ⟨hi.1.1, by simpa [G, completedPipelineFamily, hparent₅] using hi.2⟩
          · intro hi
            refine ⟨⟨hi.1, ?_⟩, ?_⟩
            · simpa [hi.2] using hjactive
            · simpa [G, completedPipelineFamily, hparent₅] using hi.2
        have hfiber₅ne (j : κ) (hj : j ∈ G.outerSet) : (G₅.fiber j).Nonempty := by
          have hjactive : j ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj
          have hvol : volume (iUnionShade (G₅.fiber j) G₅.innerBody) ≠ 0 :=
            (Finset.mem_filter.mp hjactive).2
          by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          exact hvol (by simp [iUnionShade, hne])
        refine ⟨ua, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          have hi' := Finset.mem_filter.mp hi
          change i ∈ {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅}
          exact Finset.mem_filter.mpr ⟨hsub₅ hi'.1, by simpa [← hparent₅] using hi'.2⟩
        · constructor
          · constructor
            · intro i hi
              exact hsub₅ (Finset.mem_filter.mp hi).1
            · intro i hi
              have hi₅ : i ∈ G₅.innerSet := (Finset.mem_filter.mp hi).1
              rw [show G.innerBody i = G₅.innerBody i by
                simp [G, completedPipelineFamily, completedInnerBody, hi₅]]
              exact hrefG₅.1.2 i hi₅
          · calc
              (((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c)⁻¹ : NNReal) :
                    ENNReal) *
                    ∑ i ∈ F.innerSet, volume (F.innerBody i).shade
                  ≤ ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := hrefFinal.2
              _ = ∑ i ∈ G₅.innerSet, volume (G₅.innerBody i).shade := hsum
              _ = ∑ i ∈ ua, volume (G.innerBody i).shade := by
                symm
                simpa [ua, G, completedPipelineFamily] using
                  sum_volume_completedActiveInnerBody F G₅
        · intro j hj
          rw [huaFiber j hj]
          exact hfiber₅ne j hj
        · intro j hj j' hj'
          rw [huaFiber j hj, huaFiber j' hj']
          have hjactive : j ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj
          have hj'active : j' ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj'
          have hcmp := F.pipelineFamily_fiberVolume_le_two_mul hδ hdisc (ρ : ℝ)
            hρreal hΩ T₅' ρ (Finset.mem_filter.mp hjactive).1
              (Finset.mem_filter.mp hj'active).1
          rw [fiberVolume_eq_sum, fiberVolume_eq_sum] at hcmp
          have hfiberPipeline (q : κ) : G₅.fiber q =
              {i ∈ F.pipelineInnerSet hδ hdisc | F.parent i = q} := by
            simp [G₅, ShadedFactorFamily.fiber]
          rw [← hfiberPipeline j, ← hfiberPipeline j'] at hcmp
          have hsumT (q : κ) :
              ∑ i ∈ G₅.fiber q, volume (F.innerBody i).carrier =
                ∑ i ∈ G₅.fiber q, volume (T i).carrier := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hinner i (hsub₅ (Finset.mem_filter.mp hi).1)]
          rw [hsumT j, hsumT j'] at hcmp
          obtain ⟨i₀, hi₀⟩ := hfiber₅ne j' hj'
          have hsumCard (q : κ) :
              ∑ i ∈ G₅.fiber q, volume (T i).carrier =
                ((G₅.fiber q).card : ENNReal) * volume (T i₀).carrier := by
            rw [Finset.sum_eq_card_nsmul (fun i _ ↦
              Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube)]
            rw [nsmul_eq_mul]
          rw [hsumCard j, hsumCard j'] at hcmp
          have hv0 : volume (T i₀).carrier ≠ 0 := by
            exact (lt_of_lt_of_le (by
              exact_mod_cast mul_pos (Tube.le_volume.c_pos n) (pow_pos hδ (n - 1)))
                (Tube.le_volume (T i₀).toTube)).ne'
          have hvtop : volume (T i₀).carrier ≠ ⊤ := (T i₀).isCompact.measure_lt_top.ne
          apply (ENNReal.mul_le_mul_iff_left hv0 hvtop).mp
          simpa [mul_assoc] using hcmp
        · intro j hj
          rw [huaFiber j hj]
          have hjactive : j ∈ activeOuterSet G₅ := by
            simpa [G, completedPipelineFamily] using hj
          symm
          rw [multiplicity_eq_div, multiplicity_eq_div]
          have hGfiber : G.fiber j =
              {i ∈ F.innerSet | F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j} := by
            ext i
            simp [G, completedPipelineFamily, ShadedFactorFamily.fiber, and_assoc]
          have hGinner : G.innerBody = completedInnerBody F G₅ := rfl
          have hsumEq :
              ∑ i ∈ G.fiber j, volume (G.innerBody i).shade =
                ∑ i ∈ G₅.fiber j, volume (G₅.innerBody i).shade := by
            rw [hGfiber, hGinner]
            exact sum_volume_completed_fiber F G₅ hsub₅ hparent₅ hjactive
          have hunionEq :
              volume (iUnionShade (G.fiber j) G.innerBody) =
                volume (iUnionShade (G₅.fiber j) G₅.innerBody) := by
            rw [hGfiber, hGinner]
            exact congrArg volume
              (iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hjactive)
          have hbodyOn : ∀ i ∈ G₅.fiber j, G.innerBody i = G₅.innerBody i := by
            intro i hi
            have hi₅ : i ∈ G₅.innerSet := (Finset.mem_filter.mp hi).1
            simp [G, completedPipelineFamily, completedInnerBody, hi₅]
          have hsumBody :
              ∑ i ∈ G₅.fiber j, volume (G.innerBody i).shade =
                ∑ i ∈ G₅.fiber j, volume (G₅.innerBody i).shade := by
            exact Finset.sum_congr rfl fun i hi ↦ congrArg (fun V ↦ volume V.shade) (hbodyOn i hi)
          have hunionBody :
              volume (iUnionShade (G₅.fiber j) G.innerBody) =
                volume (iUnionShade (G₅.fiber j) G₅.innerBody) := by
            apply congrArg volume
            apply Set.iUnion₂_congr
            intro i hi
            exact congrArg ShadedBody.shade (hbodyOn i hi)
          rw [hsumBody, hunionBody, hsumEq, hunionEq]
      · intro x hx
        let U : Set E := iUnionShade G.innerSet G.innerBody
        let W : Set E := iUnionShade G.outerSet G.outerBody
        have hUmeas : MeasurableSet U := measurableSet_iUnion_shade G.innerSet G.innerBody
        have hcoverW : W ⊆ ⋃ z ∈ T₅', Metric.closedBall z (4 * (ρ : ℝ)) := by
          intro y hy
          obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
          change y ∈ (K j).carrier ∩ Metric.cthickening (2 * (ρ : ℝ))
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
              (completedInnerBody F G₅)) at hyj
          have hthick := Metric.cthickening_subset_iUnion_closedBall_of_lt
            (iUnionShade {i ∈ F.innerSet |
              F.parent i ∈ activeOuterSet G₅ ∧ F.parent i = j}
              (completedInnerBody F G₅))
            (show (0 : ℝ) < 3 * (ρ : ℝ) by positivity)
            (show 2 * (ρ : ℝ) < 3 * (ρ : ℝ) by linarith) hyj.2
          obtain ⟨z, hzfib, hyz⟩ := Set.mem_iUnion₂.mp hthick
          have hjactive : j ∈ activeOuterSet G₅ := by simpa [G, completedPipelineFamily] using hj
          have hz₅ : z ∈ iUnionShade (G₅.fiber j) G₅.innerBody := by
            rw [← iUnionShade_completed_fiber F G₅ hsub₅ hparent₅ hjactive]
            exact hzfib
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz₅
          have hzi' : z ∈ (step5InnerBody F F.step0.innerSet
              (F.step1 hδ hdisc).outerSet
              (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
              (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) T₅' ρ i).shade := by
            simpa [G₅, FactorFamily.pipelineFamily] using hzi
          rw [shade_step5InnerBody] at hzi'
          obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.mp hzi'.2
          refine Set.mem_iUnion₂.mpr ⟨q, hq, Metric.mem_closedBall.mpr ?_⟩
          have hyz' := Metric.mem_closedBall.mp hyz
          have hzq' := Metric.mem_closedBall.mp hzq
          calc
            dist y q ≤ dist y z + dist z q := dist_triangle y z q
            _ ≤ 3 * (ρ : ℝ) + (ρ : ℝ) := by
              gcongr
            _ = 4 * (ρ : ℝ) := by ring
        have hlocal : ∀ y, ∀ z ∈ T₅',
            volume (U ∩ Metric.ball y (ρ : ℝ)) ≤
              2 * Kakeya.factoringStep5OverlapConstant n *
                volume (U ∩ Metric.closedBall z (ρ : ℝ)) := by
          intro y z hz
          rw [show volume (U ∩ Metric.ball y (ρ : ℝ)) =
              volume (iUnionShade G₅.innerSet G₅.innerBody ∩ Metric.ball y (ρ : ℝ)) by
                simpa [U, G, completedPipelineFamily] using
                  volume_iUnionShade_completed_inter_eq F G₅ hsub₅ hparent₅
                    (Metric.ball y (ρ : ℝ)),
            show volume (U ∩ Metric.closedBall z (ρ : ℝ)) =
              volume (iUnionShade G₅.innerSet G₅.innerBody ∩ Metric.closedBall z (ρ : ℝ)) by
                simpa [U, G, completedPipelineFamily] using
                  volume_iUnionShade_completed_inter_eq F G₅ hsub₅ hparent₅
                    (Metric.closedBall z (ρ : ℝ))]
          simpa only [G₅, n, FactorFamily.pipelineInnerSet, FactorFamily.pipelineFamily,
            step5ShadedFactorFamily_innerSet, step5ShadedFactorFamily_innerBody] using
            volume_iUnionShade_step5_inter_ball_le F F.step0.innerSet
            (F.step1 hδ hdisc).outerSet (F.pipelineSet hδ hdisc (ρ : ℝ) hρreal) hΩ
            (F.pipelineExponent hδ hdisc (ρ : ℝ) hρreal) hρpos hT₅'sep hballcomp y hz
        have hb := ball_estimate_of_cover U W T₅' ρ x hρpos hUmeas hcoverW
          (fun y ↦ by
            rw [Finset.filter_congr_decidable]
            refine (Finset.card_le_card ?_).trans (hT₅overlap y)
            intro z hz
            exact Finset.mem_filter.mpr ⟨hT₅'T₅ (Finset.mem_filter.mp hz).1,
              (Finset.mem_filter.mp hz).2⟩) hlocal
        have hballC : rhoTubesBallLoss n ≤
            shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c := by
          rw [shadingMultiplicityEstimateForRhoTubesDilate.C]
          exact le_max_of_le_right (le_max_right _ _)
        have hC0 : (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal) ≠ 0 :=
          ENNReal.coe_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le
            (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n N δ c)))
        calc
          (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
                volume W * (volume (U ∩ Metric.ball x (ρ : ℝ)) /
                  volume (Metric.ball x (ρ : ℝ)))
              = (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
                (volume W * (volume (U ∩ Metric.ball x (ρ : ℝ)) /
                  volume (Metric.ball x (ρ : ℝ)))) := by ring
          _ ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
              ((rhoTubesBallLoss n : ENNReal) * volume U) := by gcongr
          _ ≤ (shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal)⁻¹ *
              ((shadingMultiplicityEstimateForRhoTubesDilate.C n N δ c : ENNReal) * volume U) := by
                gcongr
          _ = volume U := ENNReal.inv_mul_cancel_left hC0 ENNReal.coe_ne_top

end ShadedBody
