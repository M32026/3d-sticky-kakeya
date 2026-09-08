module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialEntryLemmasW94
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Factoring.Pipeline
public import Kakeya.Tube.IntersectionVolume
public import Kakeya.Tube.Dilate
public import Kakeya.Factoring.OuterPacking
import all Kakeya.Factoring.Step1

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

universe uE uI uP

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

def sourceRawCrossCostW97 (n : Nat) : NNReal := max 1 (Tube.dilateFullness.C n)

/-- Actual pipeline statistics on the SAME returned raw G. This record is
constructed by B1; it does not assume the subset-stable scalar conclusion. -/
structure ActualRawRhoStatisticsW97
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {delta rho : NNReal} (F : ShadedBody.FactorFamily E iota pi)
    (T : iota -> ShadedTube delta E) (Trho : pi -> Tube rho E)
    (G : ShadedBody.ShadedFactorFamily E iota pi) where
  outer_subset : G.outerSet ⊆ F.outerSet
  inner_eq : G.innerSet = F.innerSet.filter (fun i => F.parent i ∈ G.outerSet)
  parent_eq : G.parent = F.parent
  inner_body : ∀ i ∈ F.innerSet, (G.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody
  outer_body : ∀ Q ∈ G.outerSet, (G.outerBody Q).toConvexSpaceBody = (Trho Q).toConvexSpaceBody
  outer_nonempty : G.outerSet.Nonempty
  inner_image : G.innerSet.image G.parent = G.outerSet
  raw_refinement : IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody
    (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank Real E) F.innerSet.card delta 1)⁻¹
  outer_fullness :
    ((ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank Real E) F.innerSet.card delta 1 : NNReal) : ENNReal)⁻¹ *
      fullness' F.innerSet F.innerBody <= fullness' G.outerSet G.outerBody
  raw_scalar : ∀ Q ∈ G.outerSet, ShadedBody.multiplicity F.innerSet F.innerBody <=
    (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank Real E) F.innerSet.card delta 1 : ENNReal) *
      ShadedBody.multiplicity G.outerSet G.outerBody * ShadedBody.multiplicity (G.fiber Q) G.innerBody
  q : NNReal
  q_pos : 0 < q
  fibre_mass_pos : ∀ Q ∈ G.outerSet, 0 < ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade
  q_lower : ∀ Q ∈ G.outerSet, (q : ENNReal) <= ShadedBody.multiplicity (G.fiber Q) G.innerBody
  q_upper : ∀ Q ∈ G.outerSet, ShadedBody.multiplicity (G.fiber Q) G.innerBody <= 2 * (q : ENNReal)
  carrierSupport : Finset iota
  support_subset : carrierSupport ⊆ G.innerSet
  shade_off_support : ∀ i ∈ G.innerSet, i ∉ carrierSupport -> (G.innerBody i).shade = ∅
  support_fibre_pos : ∀ Q ∈ G.outerSet,
    0 < ∑ i ∈ completeFibreW94 carrierSupport F.parent Q, volume (T i).carrier
  support_fibre_comparable : ∀ Q ∈ G.outerSet, ∀ Q' ∈ G.outerSet,
    (∑ i ∈ completeFibreW94 carrierSupport F.parent Q, volume (T i).carrier) <=
      2 * ∑ i ∈ completeFibreW94 carrierSupport F.parent Q', volume (T i).carrier
  cross_density : ∀ Q ∈ G.outerSet,
    (∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) * volume (Trho Q).carrier <=
      (sourceRawCrossCostW97 (Module.finrank Real E) : ENNReal) * volume (G.outerBody Q).shade *
        ∑ i ∈ completeFibreW94 carrierSupport F.parent Q, volume (T i).carrier
  local_union : ∀ x ∈ iUnionShade G.outerSet G.outerBody,
    (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank Real E) F.innerSet.card delta 1 : ENNReal)⁻¹ *
      volume (iUnionShade G.outerSet G.outerBody) *
        (volume (iUnionShade G.innerSet G.innerBody ∩ Metric.ball x (rho : Real)) /
          volume (Metric.ball x (rho : Real))) <= volume (iUnionShade G.innerSet G.innerBody)
  neighbourhood : ∀ Q ∈ G.outerSet, ∀ i ∈ G.fiber Q,
    (G.outerBody Q).carrier ∩ Metric.cthickening (2 * (rho : Real)) (G.innerBody i).shade ⊆
      (G.outerBody Q).shade

/-- B1 reruns/exposes the real raw pipeline, including its common q and
comparable carrier support before zero completion. -/
theorem exists_raw_rho_factorization_with_fibre_statistics_w97
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {delta rho : NNReal} (hdelta : 0 < delta) (hdrho : delta <= rho) (hrho : rho <= 1)
    (F : ShadedBody.FactorFamily E iota pi)
    (T : iota -> ShadedTube delta E) (Trho : pi -> Tube rho E)
    (hinner : ∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody)
    (houter : ∀ Q ∈ F.outerSet, F.outerBody Q = (Trho Q).toConvexSpaceBody)
    (hball : ∀ i ∈ F.innerSet, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (T i).shade) :
    ∃ G : ShadedBody.ShadedFactorFamily E iota pi,
      Nonempty (ActualRawRhoStatisticsW97 F T Trho G) := by
  let n := Module.finrank Real E
  let N := F.innerSet.card
  have hdelta1 : delta <= 1 := hdrho.trans hrho
  have hrho0 : 0 < rho := hdelta.trans_le hdrho
  have hrhoR : (0 : Real) < rho := by exact_mod_cast hrho0
  have hmassF : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
    simpa only [Finset.sum_congr rfl (fun i hi => congrArg (fun W : ShadedBody E => volume W.shade)
      (hinner i hi))] using hmass
  have hNpos : 0 < N := by
    obtain ⟨i, hi, _⟩ := Finset.sum_pos_iff.mp hmassF
    exact Finset.card_pos.mpr ⟨i, hi⟩
  have hdisc : F.InnerIsDiscretizedAtScale delta :=
    { subset_unitBall := by
        intro i hi
        simpa only [hinner i hi] using hball i hi
      le_scale := by
        intro i hi
        rw [hinner i hi]
        exact Tube.le_ethickness_scale (T i).toTube }
  let Omega := F.pipelineSet hdelta hdisc (rho : Real) hrhoR
  have hOmega : MeasurableSet Omega := F.measurableSet_pipelineSet hdelta hdisc (rho : Real) hrhoR
  obtain ⟨net, selected, hnetSub, hnetSep, hnetCover, hnetOverlap, hselectedSub,
      hselectedPositive, hselectedSep, href5, hballComparable⟩ :=
    exists_factoringPipelineSelf F hdelta hdisc (rho : Real) hrhoR hOmega hrho0
  let G5 := F.pipelineFamily hdelta hdisc (rho : Real) hrhoR hOmega selected rho
  let R : NNReal := ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N delta net.card
  have hrefG5 : IsCRefinement G5.innerSet G5.innerBody F.innerSet F.innerBody R :=
    F.pipelineFamily_isCRefinementSelf hdelta hdisc (rho : Real) hrhoR hOmega selected rho href5
  have hG5sub : G5.innerSet ⊆ F.innerSet := hrefG5.1.1
  have hG5outer : G5.outerSet ⊆ F.outerSet :=
    F.pipelineFamily_outerSet_subset hdelta hdisc (rho : Real) hrhoR hOmega selected rho
  have hG5parent : G5.parent = F.parent :=
    F.pipelineFamily_parent hdelta hdisc (rho : Real) hrhoR hOmega selected rho
  have hG5body : ∀ i, (G5.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody :=
    F.pipelineFamily_innerBody_toConvexSpaceBody hdelta hdisc (rho : Real) hrhoR hOmega selected rho
  have hRpos : 0 < R := by
    have hA : 0 < Kakeya.factoringStep1AtScaleConstant n N delta := by
      have hN1 := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
      have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n hN1 hdelta hdelta1
      rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hdelta] at hl
      rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hdelta]
      apply mul_pos (by norm_num)
      rw [Real.toNNReal_pos]
      linarith
    have hB : (0 : NNReal) < Kakeya.factoringStep2Step3Constant N := by
      rw [Kakeya.factoringStep2Step3Constant_eq]
      positivity
    have hC := ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant_pos_natCast n net.card
    dsimp only [R, ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant]
    positivity
  have hmass5 : 0 < ∑ i ∈ G5.innerSet, volume (G5.innerBody i).shade :=
    (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hRpos.ne') hmassF.ne').trans_le hrefG5.2
  let active := G5.outerSet.filter (fun Q => volume (iUnionShade (G5.fiber Q) G5.innerBody) ≠ 0)
  let completed : iota -> ShadedBody E := fun i => if i ∈ G5.innerSet then G5.innerBody i
    else (F.innerBody i).restrictShade ∅ MeasurableSet.empty
  have hcompletedBody : ∀ i, (completed i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody := by
    intro i
    by_cases hi : i ∈ G5.innerSet
    · simpa only [completed, if_pos hi] using hG5body i
    · simp only [completed, if_neg hi, ShadedBody.restrictShade]
  let outer : pi -> ShadedBody E := fun Q =>
    { toConvexSpaceBody := (Trho Q).toConvexSpaceBody
      shade := (Trho Q).carrier ∩ Metric.cthickening (2 * (rho : Real))
        (iUnionShade (G5.fiber Q) G5.innerBody)
      measurableSet_shade := (Trho Q).isCompact.isClosed.measurableSet.inter
        Metric.isClosed_cthickening.measurableSet
      shade_subset := Set.inter_subset_left }
  have hparentTube : ∀ i ∈ F.innerSet,
      (F.innerBody i).toConvexSpaceBody <= (Trho (F.parent i)).toConvexSpaceBody := by
    intro i hi
    rw [← houter (F.parent i) (F.parent_mem i hi)]
    exact F.inner_le_parent i hi
  let G : ShadedFactorFamily E iota pi :=
    { innerSet := F.innerSet.filter (fun i => F.parent i ∈ active)
      innerBody := completed
      outerSet := active
      outerBody := outer
      parent := F.parent
      parent_mem := by intro i hi; exact (Finset.mem_filter.mp hi).2
      inner_le_parent := by
        intro i hi
        change (completed i).toConvexSpaceBody <= (Trho (F.parent i)).toConvexSpaceBody
        rw [hcompletedBody]
        exact hparentTube i (Finset.mem_filter.mp hi).1
      shade_subset_parent := by
        intro i hi x hxi
        have hxcar := (completed i).shade_subset hxi
        have hxF : x ∈ (F.innerBody i).carrier := by
          change x ∈ (F.innerBody i).toConvexSpaceBody.carrier
          rw [← hcompletedBody]
          exact hxcar
        refine ⟨hparentTube i (Finset.mem_filter.mp hi).1 hxF, ?_⟩
        apply Metric.self_subset_cthickening
        by_cases hi5 : i ∈ G5.innerSet
        · refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
          · simpa only [ShadedFactorFamily.fiber, Finset.mem_filter, hG5parent] using
              And.intro hi5 (rfl : F.parent i = F.parent i)
          · simpa only [completed, if_pos hi5] using hxi
        · simpa only [completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty, Set.mem_empty_iff_false] using hxi }
  have hactive : active.Nonempty := by
    obtain ⟨i, hi5, hvi⟩ := Finset.sum_pos_iff.mp hmass5
    refine ⟨G5.parent i, Finset.mem_filter.mpr ⟨G5.parent_mem i hi5, ?_⟩⟩
    apply (hvi.trans_le (measure_mono (Set.subset_iUnion₂_of_subset i ?_ (Set.Subset.refl _)))).ne'
    simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using And.intro hi5 (rfl : G5.parent i = G5.parent i)
  have hfibreMem : ∀ Q i, i ∈ G.fiber Q ↔ i ∈ F.innerSet ∧ F.parent i ∈ active ∧ F.parent i = Q := by
    intro Q i
    simp only [G, ShadedFactorFamily.fiber, Finset.mem_filter, and_assoc]
  have hfibre5Mem : ∀ Q i, i ∈ G5.fiber Q ↔ i ∈ G5.innerSet ∧ F.parent i = Q := by
    intro Q i
    simp only [ShadedFactorFamily.fiber, Finset.mem_filter, hG5parent]
  have hUnionFibre : ∀ Q ∈ active,
      iUnionShade (G.fiber Q) G.innerBody = iUnionShade (G5.fiber Q) G5.innerBody := by
    intro Q hQ
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hiF, _, hip⟩ := (hfibreMem Q i).mp hi
      by_cases hi5 : i ∈ G5.innerSet
      · exact Set.mem_iUnion₂.mpr ⟨i, (hfibre5Mem Q i).mpr ⟨hi5, hip⟩,
          by simpa only [G, completed, if_pos hi5] using hxi⟩
      · simpa only [G, completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty, Set.mem_empty_iff_false] using hxi
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hi5, hip⟩ := (hfibre5Mem Q i).mp hi
      exact Set.mem_iUnion₂.mpr ⟨i, (hfibreMem Q i).mpr ⟨hG5sub hi5, hip ▸ hQ, hip⟩,
        by simpa only [G, completed, if_pos hi5] using hxi⟩
  have hSumFibre : ∀ Q ∈ active,
      (∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) =
        ∑ i ∈ G5.fiber Q, volume (G5.innerBody i).shade := by
    intro Q hQ
    have hsub : G5.fiber Q ⊆ G.fiber Q := by
      intro i hi
      obtain ⟨hi5, hip⟩ := (hfibre5Mem Q i).mp hi
      exact (hfibreMem Q i).mpr ⟨hG5sub hi5, hip ▸ hQ, hip⟩
    calc
      _ = ∑ i ∈ G5.fiber Q, volume (G.innerBody i).shade := by
        symm
        apply Finset.sum_subset hsub
        intro i hi hinot
        have hi5 : i ∉ G5.innerSet := fun hi5 => hinot ((hfibre5Mem Q i).mpr
          ⟨hi5, ((hfibreMem Q i).mp hi).2.2⟩)
        simp only [G, completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty, measure_empty]
      _ = _ := Finset.sum_congr rfl (fun i hi => by
        simp only [G, completed, if_pos ((hfibre5Mem Q i).mp hi).1])
  let support := G5.innerSet.filter (fun i => F.parent i ∈ active)
  have hsupport : support ⊆ G.innerSet := by
    intro i hi
    obtain ⟨hi5, hip⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hG5sub hi5, hip⟩
  have hsupportFibre : ∀ Q ∈ active,
      completeFibreW94 support F.parent Q = G5.fiber Q := by
    intro Q hQ
    ext i
    rw [hfibre5Mem]
    simp only [completeFibreW94, support, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi5, _⟩, hip⟩
      exact ⟨hi5, hip⟩
    · rintro ⟨hi5, hip⟩
      exact ⟨⟨hi5, hip ▸ hQ⟩, hip⟩
  have hmassFibre : ∀ Q ∈ active, 0 < ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade := by
    intro Q hQ
    have hvol := (Finset.mem_filter.mp hQ).2
    rw [← hUnionFibre Q hQ] at hvol
    have hle : volume (iUnionShade (G.fiber Q) G.innerBody) <=
        ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade :=
      measure_biUnion_finset_le (G.fiber Q) (fun i => (G.innerBody i).shade)
    exact (pos_iff_ne_zero.mpr hvol).trans_le hle
  have himage : G.innerSet.image G.parent = G.outerSet := by
    apply Finset.Subset.antisymm
    · intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact G.parent_mem i hi
    · intro Q hQ
      obtain ⟨i, hi, _⟩ := Finset.sum_pos_iff.mp (hmassFibre Q hQ)
      have hi' : i ∈ G.innerSet ∧ G.parent i = Q := by
        simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
      exact Finset.mem_image.mpr ⟨i, hi'.1, hi'.2⟩
  let q : NNReal := (2 ^ F.pipelineExponent hdelta hdisc (rho : Real) hrhoR : Nat)
  have hq : 0 < q := by dsimp [q]; positivity
  have hmuFibre : ∀ Q ∈ active,
      ShadedBody.multiplicity (G.fiber Q) G.innerBody = ShadedBody.multiplicity (G5.fiber Q) G5.innerBody := by
    intro Q hQ
    simp only [ShadedBody.multiplicity, hSumFibre Q hQ, hUnionFibre Q hQ]
  have hqLower : ∀ Q ∈ active, (q : ENNReal) <= ShadedBody.multiplicity (G.fiber Q) G.innerBody := by
    intro Q hQ
    rw [hmuFibre Q hQ]
    apply ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity _ _ (Finset.mem_filter.mp hQ).2
    intro x hx
    dsimp only [q, G5]
    exact_mod_cast (F.pipelineFamily_fiber_multiplicity hdelta hdisc (rho : Real) hrhoR
      hOmega selected rho hx).1
  have hqUpper : ∀ Q ∈ active, ShadedBody.multiplicity (G.fiber Q) G.innerBody <= 2 * (q : ENNReal) := by
    intro Q hQ
    rw [hmuFibre Q hQ]
    apply ShadedBody.multiplicity_le_of_pointwiseMultiplicity_le
    intro x hx
    have hp := (F.pipelineFamily_fiber_multiplicity hdelta hdisc (rho : Real) hrhoR hOmega selected rho hx).2.le
    dsimp only [q, G5]
    exact_mod_cast (show pointwiseMultiplicity (G5.fiber Q) G5.innerBody x <=
      2 * 2 ^ F.pipelineExponent hdelta hdisc (rho : Real) hrhoR from by
        simpa only [pow_succ, mul_comm] using hp)
  have hsupportPositive : ∀ Q ∈ active,
      0 < ∑ i ∈ completeFibreW94 support F.parent Q, volume (T i).carrier := by
    intro Q hQ
    rw [hsupportFibre Q hQ]
    have hpos : 0 < ∑ i ∈ G5.fiber Q, volume (G5.innerBody i).shade :=
      hSumFibre Q hQ ▸ hmassFibre Q hQ
    apply hpos.trans_le
    apply Finset.sum_le_sum
    intro i hi
    have hiF := hG5sub ((hfibre5Mem Q i).mp hi).1
    have hbody := congrArg (fun K : ConvexSpaceBody E => K.carrier)
      ((hG5body i).trans (congrArg ShadedBody.toConvexSpaceBody (hinner i hiF)))
    exact measure_mono ((G5.innerBody i).shade_subset.trans hbody.subset)
  have hsupportComparable : ∀ Q ∈ active, ∀ Q' ∈ active,
      (∑ i ∈ completeFibreW94 support F.parent Q, volume (T i).carrier) <=
        2 * ∑ i ∈ completeFibreW94 support F.parent Q', volume (T i).carrier := by
    intro Q hQ Q' hQ'
    have hvalue : ∀ A ∈ active,
        (∑ i ∈ completeFibreW94 support F.parent A, volume (T i).carrier) =
          fiberVolume F (F.pipelineInnerSet hdelta hdisc) A := by
      intro A hA
      rw [hsupportFibre A hA]
      apply Finset.sum_congr
      · ext i
        simp only [ShadedFactorFamily.fiber, G5, FactorFamily.pipelineFamily_innerSet,
          FactorFamily.pipelineFamily_parent]
      · intro i hi
        have hiP := (Finset.mem_filter.mp hi).1
        rw [FactorFamily.pipelineInnerSet] at hiP
        have hiF := F.innerSet_step0_subset (Finset.mem_filter.mp hiP).1
        rw [hinner i hiF]
    rw [hvalue Q hQ, hvalue Q' hQ']
    exact F.pipelineFamily_fiberVolume_le_two_mul hdelta hdisc (rho : Real) hrhoR hOmega selected rho
      (Finset.mem_filter.mp hQ).1 (Finset.mem_filter.mp hQ').1
  have hneighbourhood : ∀ Q ∈ G.outerSet, ∀ i ∈ G.fiber Q,
      (G.outerBody Q).carrier ∩ Metric.cthickening (2 * (rho : Real)) (G.innerBody i).shade ⊆
        (G.outerBody Q).shade := by
    intro Q hQ i hi x hx
    refine ⟨hx.1, ?_⟩
    apply Metric.cthickening_subset_of_subset _ _ hx.2
    rw [← hUnionFibre Q hQ]
    exact Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)
  have hsumGlobal : (∑ i ∈ G.innerSet, volume (G.innerBody i).shade) =
      ∑ i ∈ G5.innerSet, volume (G5.innerBody i).shade := by
    calc
      _ = ∑ i ∈ support, volume (G.innerBody i).shade := by
        symm
        apply Finset.sum_subset hsupport
        intro i hi hinot
        have hi5 : i ∉ G5.innerSet := fun hi5 => hinot (Finset.mem_filter.mpr
          ⟨hi5, (Finset.mem_filter.mp hi).2⟩)
        simp only [G, completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty, measure_empty]
      _ = ∑ i ∈ support, volume (G5.innerBody i).shade := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [G, completed, if_pos (Finset.mem_filter.mp hi).1]
      _ = _ := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i hi hinot
        have hparentNot : G5.parent i ∉ active := by
          intro hp
          exact hinot (Finset.mem_filter.mpr ⟨hi, by simpa only [hG5parent] using hp⟩)
        have hz : volume (iUnionShade (G5.fiber (G5.parent i)) G5.innerBody) = 0 := by
          by_contra hz
          exact hparentNot (Finset.mem_filter.mpr ⟨G5.parent_mem i hi, hz⟩)
        apply le_antisymm _ bot_le
        calc
          _ <= volume (iUnionShade (G5.fiber (G5.parent i)) G5.innerBody) :=
            measure_mono (Set.subset_iUnion₂_of_subset i
              ((hfibre5Mem _ i).mpr ⟨hi, congrFun hG5parent i |>.symm⟩) (Set.Subset.refl _))
          _ = _ := hz
  let inactive := G5.outerSet.filter (fun Q => Q ∉ active)
  let nullUnion := ⋃ Q ∈ inactive, iUnionShade (G5.fiber Q) G5.innerBody
  have hnull : volume nullUnion = 0 := by
    change volume (⋃ Q ∈ (inactive : Set pi), iUnionShade (G5.fiber Q) G5.innerBody) = 0
    apply (measure_biUnion_null_iff (Set.to_countable (inactive : Set pi))).mpr
    intro Q hQ
    obtain ⟨hQ5, hQa⟩ := Finset.mem_filter.mp hQ
    by_contra hn
    exact hQa (Finset.mem_filter.mpr ⟨hQ5, hn⟩)
  have hglobalAE : iUnionShade G.innerSet G.innerBody =ᵐ[volume] iUnionShade G5.innerSet G5.innerBody := by
    have havoid : ∀ᵐ x ∂volume, x ∉ nullUnion := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using hnull
    filter_upwards [havoid] with x hxnull
    apply propext
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      by_cases hi5 : i ∈ G5.innerSet
      · exact Set.mem_iUnion₂.mpr ⟨i, hi5, by simpa only [G, completed, if_pos hi5] using hxi⟩
      · simpa only [G, completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty,
          Set.mem_empty_iff_false] using hxi
    · intro hx
      obtain ⟨i, hi5, hxi⟩ := Set.mem_iUnion₂.mp hx
      have hip : G5.parent i ∈ active := by
        by_contra hn
        apply hxnull
        exact Set.mem_iUnion₂.mpr ⟨G5.parent i,
          Finset.mem_filter.mpr ⟨G5.parent_mem i hi5, hn⟩,
          Set.mem_iUnion₂.mpr ⟨i, (hfibre5Mem _ i).mpr
            ⟨hi5, congrFun hG5parent i |>.symm⟩, hxi⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr
        ⟨hG5sub hi5, by simpa only [hG5parent] using hip⟩,
        by simpa only [G, completed, if_pos hi5] using hxi⟩
  have hrefG : IsCRefinement G.innerSet G.innerBody F.innerSet F.innerBody R := by
    refine ⟨⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
    · intro i hi
      refine ⟨hcompletedBody i, ?_⟩
      by_cases hi5 : i ∈ G5.innerSet
      · simpa only [G, completed, if_pos hi5] using (hrefG5.1.2 i hi5).2
      · simp only [G, completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty, Set.empty_subset]
    · rw [hsumGlobal]
      exact hrefG5.2
  have hnetBall : (net : Set E) ⊆ Metric.closedBall 0 1 := by
    refine hnetSub.trans ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hiF : i ∈ F.innerSet := by
      rw [FactorFamily.pipelineInnerSet] at hi
      exact F.innerSet_step0_subset (Finset.mem_filter.mp hi).1
    apply hball i hiF
    have hc := (step3InnerBody F F.step0.innerSet (F.step1 hdelta hdisc).outerSet
      (F.pipelineSet hdelta hdisc (rho : Real) hrhoR) hOmega
      (F.pipelineExponent hdelta hdisc (rho : Real) hrhoR) i).shade_subset hxi
    simpa only [step3InnerBody, hinner i hiF] using hc
  have hnetCard : (net.card : NNReal) <= step5PackingRatio n N delta := by
    have hpack := Metric.card_le_of_isSeparated_subset_closedBall (T := net) hrho0
      (x := (0 : E)) (R := 1) (by norm_num) hnetBall hnetSep
    have hdR : (0 : Real) < delta := by exact_mod_cast hdelta
    have hbase : 2 * (1 + (rho : Real)) / (rho : Real) <= 4 / (delta : Real) := by
      rw [div_le_div_iff₀ hrhoR hdR]
      have hdrr : (delta : Real) <= rho := by exact_mod_cast hdrho
      have hr1 : (rho : Real) <= 1 := by exact_mod_cast hrho
      nlinarith
    have hcard : (net.card : Real) <= (4 / (delta : Real)) ^ n :=
      hpack.trans (pow_le_pow_left₀ (by positivity) hbase n)
    rw [← NNReal.coe_le_coe]
    push_cast
    refine hcard.trans ?_
    rw [step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hdelta]
    push_cast
    rw [div_pow, div_eq_mul_inv]
    have hfact : (1 : Real) <= n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hN : (1 : Real) <= max 1 (N : Real) := le_max_left _ _
    calc
      _ = ((2 : Real) ^ n * 2 ^ n) * ((delta : Real) ^ n)⁻¹ := by rw [← mul_pow]; norm_num
      _ <= ((2 : Real) ^ n * 2 ^ n) *
          ((n.factorial : Real) * max 1 (N : Real) * ((delta : Real) ^ n)⁻¹) := by
        gcongr
        calc
          _ = 1 * 1 * ((delta : Real) ^ n)⁻¹ := by ring
          _ <= _ := by gcongr
      _ = _ := by ring
  have hratioOne : (1 : NNReal) <= step5PackingRatio n N delta := by
    rw [step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hdelta]
    have hf : (1 : NNReal) <= n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hN : (1 : NNReal) <= max 1 N := by exact_mod_cast le_max_left 1 N
    have hd : (1 : NNReal) <= (delta ^ n)⁻¹ := by
      rw [one_le_inv₀ (pow_pos hdelta n)]
      exact pow_le_one₀ zero_le hdelta1
    have hp : (1 : NNReal) <= 2 ^ n := one_le_pow₀ (by norm_num)
    calc
      (1 : NNReal) = 1 * (1 * 1 * 1 * 1) := by norm_num
      _ <= 2 ^ n * (2 ^ n * n.factorial * max 1 N * (delta ^ n)⁻¹) := by gcongr
  have hcost : R⁻¹ * rhoTubesGeometricLoss n <=
      shadingMultiplicityEstimateForRhoTubesDilate.C n N delta 1 := by
    have hself := ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant_mono (n := n) hnetCard hratioOne
    have hRinv : R⁻¹ = Kakeya.factoringStep1AtScaleConstant n N delta *
        (Kakeya.factoringStep2Step3Constant N : NNReal) *
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n net.card := by
      simp only [R, ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant, mul_inv_rev, inv_inv]
      ring
    rw [hRinv, shadingMultiplicityEstimateForRhoTubesDilate.C]
    apply le_max_of_le_right
    apply le_max_of_le_left
    calc
      _ <= (Kakeya.factoringStep1AtScaleConstant n N delta *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N delta)) *
            rhoTubesGeometricLoss n := by gcongr
      _ <= 2 * ((Kakeya.factoringStep1AtScaleConstant n N delta *
          (Kakeya.factoringStep2Step3Constant N : NNReal) *
          ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N delta)) *
            rhoTubesGeometricLoss n) := le_mul_of_one_le_left zero_le (by norm_num)
      _ = _ := by
        unfold Kakeya.factoringStep1Step2AtScaleConstant Kakeya.factoringStep2Step3Constant
        push_cast
        ring
  have hgeoOne : (1 : NNReal) <= rhoTubesGeometricLoss n := by
    dsimp only [rhoTubesGeometricLoss]
    calc
      _ <= (4 : NNReal) := by norm_num
      _ <= 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
          max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ (2 : Nat) *
            max 1 (rhoTubesOuterMultiplicityLoss n) := by
        have h1 := le_max_left (1 : NNReal) (Kakeya.Tube.dilateFullness.C n)
        have h2 := one_le_pow₀ (n := 2) (le_max_left (1 : NNReal) (Tube.volume_le.C n / Tube.le_volume.c n))
        have h3 := le_max_left (1 : NNReal) (rhoTubesOuterMultiplicityLoss n)
        calc
          (4 : NNReal) = 4 * 1 * 1 * 1 := by ring
          _ <= 4 * max 1 (Kakeya.Tube.dilateFullness.C n) *
              max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ (2 : Nat) *
                max 1 (rhoTubesOuterMultiplicityLoss n) := by gcongr
  have hcross : ∀ Q ∈ G.outerSet,
      (∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) * volume (Trho Q).carrier <=
        (sourceRawCrossCostW97 n : ENNReal) * volume (G.outerBody Q).shade *
          ∑ i ∈ completeFibreW94 support F.parent Q, volume (T i).carrier := by
    intro Q hQ
    rw [hSumFibre Q hQ, hsupportFibre Q hQ, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨hi5, hip⟩ := (hfibre5Mem Q i).mp hi
    have hiF := hG5sub hi5
    have hY : (G5.innerBody i).shade ⊆ (T i).carrier := by
      have hb := congrArg (fun K : ConvexSpaceBody E => K.carrier)
        ((hG5body i).trans (congrArg ShadedBody.toConvexSpaceBody (hinner i hiF)))
      exact (G5.innerBody i).shade_subset.trans hb.subset
    have hcontained : (T i).carrier ⊆ (Kakeya.Tube.dilate (Trho Q) (1 : Real)).carrier := by
      rw [Kakeya.Tube.dilate_one]
      have hh := hparentTube i hiF
      have hh' : (T i).toConvexSpaceBody <= (Trho Q).toConvexSpaceBody := by
        simpa only [hinner i hiF, hip] using hh
      exact hh'
    have hgeom := Kakeya.Tube.volume_dilate_inter_cthickening_ge hdelta hdrho hrho
      (le_rfl : (1 : Real) <= 1) (T i).toTube (Trho Q) hcontained hY
    have hlocal : (Trho Q).carrier ∩ Metric.cthickening (2 * (rho : Real)) (G5.innerBody i).shade ⊆
        (G.outerBody Q).shade := by
      intro x hx
      refine ⟨hx.1, Metric.cthickening_subset_of_subset _
        (Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)) hx.2⟩
    have hterm : (volume (G5.innerBody i).shade / volume (T i).carrier) * volume (Trho Q).carrier <=
        (sourceRawCrossCostW97 n : ENNReal) * volume (G.outerBody Q).shade := by
      have hg : (volume (G5.innerBody i).shade / volume (T i).carrier) * volume (Trho Q).carrier <=
          (Kakeya.Tube.dilateFullness.C n : ENNReal) *
            volume ((Trho Q).carrier ∩ Metric.cthickening (2 * (rho : Real)) (G5.innerBody i).shade) := by
        simpa only [Kakeya.Tube.dilate_one, NNReal.coe_one, one_pow, ENNReal.ofReal_one, mul_one, n] using hgeom
      exact hg.trans (mul_le_mul'
        (ENNReal.coe_le_coe.mpr (le_max_right 1 _)) (measure_mono hlocal))
    have hvpos := (Tube.volume_pos_and_lt_top hdelta hdelta1 (T i).toTube).1.ne'
    have hvtop : volume (T i).carrier ≠ ⊤ := (T i).isCompact.measure_ne_top
    calc
      _ = volume (T i).carrier *
          ((volume (G5.innerBody i).shade / volume (T i).carrier) * volume (Trho Q).carrier) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel hvpos hvtop]
      _ <= volume (T i).carrier * ((sourceRawCrossCostW97 n : ENNReal) * volume (G.outerBody Q).shade) :=
        mul_le_mul' le_rfl hterm
      _ = _ := by ring
  have hG5cover : iUnionShade G5.innerSet G5.innerBody ⊆
      ⋃ z ∈ selected, Metric.closedBall z (rho : Real) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hx5 : x ∈ (step5InnerBody F F.step0.innerSet (F.step1 hdelta hdisc).outerSet
        (F.pipelineSet hdelta hdisc (rho : Real) hrhoR) hOmega
        (F.pipelineExponent hdelta hdisc (rho : Real) hrhoR) selected rho i).shade := by
      simpa only [G5, FactorFamily.pipelineFamily, step5ShadedFactorFamily_innerBody] using hxi
    rw [shade_step5InnerBody] at hx5
    exact hx5.2
  have houterCover : iUnionShade G.outerSet G.outerBody ⊆
      ⋃ z ∈ selected, Metric.closedBall z (4 * (rho : Real)) := by
    intro y hy
    obtain ⟨Q, hQ, hyQ⟩ := Set.mem_iUnion₂.mp hy
    have hyThick : y ∈ Metric.cthickening (2 * (rho : Real))
        (iUnionShade (G5.fiber Q) G5.innerBody) := hyQ.2
    have hyNear := Metric.cthickening_subset_iUnion_closedBall_of_lt
      (iUnionShade (G5.fiber Q) G5.innerBody) (show 0 < 3 * (rho : Real) by positivity)
      (show 2 * (rho : Real) < 3 * (rho : Real) by linarith) hyThick
    obtain ⟨x, hxFibre, hyx⟩ := Set.mem_iUnion₂.mp hyNear
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxFibre
    have hxGlobal : x ∈ iUnionShade G5.innerSet G5.innerBody :=
      Set.mem_iUnion₂.mpr ⟨i, ((hfibre5Mem Q i).mp hi).1, hxi⟩
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hG5cover hxGlobal)
    refine Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall.mpr ?_⟩
    calc
      dist y z <= dist y x + dist x z := dist_triangle _ _ _
      _ <= 3 * (rho : Real) + rho := add_le_add (Metric.mem_closedBall.mp hyx) (Metric.mem_closedBall.mp hxz)
      _ = _ := by ring
  have hselectedOverlap : ∀ x : E, {z ∈ selected | x ∈ Metric.closedBall z (rho : Real)}.card <=
      Kakeya.factoringStep5OverlapConstant n := by
    intro x
    rw [Finset.filter_congr_decidable]
    refine (Finset.card_le_card ?_).trans (hnetOverlap x)
    intro z hz
    exact Finset.mem_filter.mpr ⟨hselectedSub (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
  refine ⟨G, ⟨{
    outer_subset := fun Q hQ => hG5outer (Finset.mem_filter.mp hQ).1
    inner_eq := rfl
    parent_eq := rfl
    inner_body := fun i hi => (hcompletedBody i).trans (congrArg ShadedBody.toConvexSpaceBody (hinner i hi))
    outer_body := fun Q hQ => rfl
    outer_nonempty := hactive
    inner_image := himage
    raw_refinement := ?_
    outer_fullness := ?_
    raw_scalar := ?_
    q := q
    q_pos := hq
    fibre_mass_pos := hmassFibre
    q_lower := hqLower
    q_upper := hqUpper
    carrierSupport := support
    support_subset := hsupport
    shade_off_support := ?_
    support_fibre_pos := hsupportPositive
    support_fibre_comparable := hsupportComparable
    cross_density := ?_
    local_union := ?_
    neighbourhood := hneighbourhood }⟩⟩
  · apply hrefG.mono
    rw [← inv_inv R]
    exact inv_anti₀ (inv_pos.mpr hRpos)
      ((le_mul_of_one_le_right zero_le hgeoOne).trans hcost)
  · let m : pi -> ENNReal := fun Q => ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade
    let A : pi -> ENNReal := fun Q => ∑ i ∈ completeFibreW94 support F.parent Q, volume (T i).carrier
    let K : pi -> ENNReal := fun Q => volume (Trho Q).carrier
    let z : pi -> ENNReal := fun Q => volume (G.outerBody Q).shade
    let D : NNReal := sourceRawCrossCostW97 n
    let L : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C n N delta 1
    have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
    have hL : 0 < L := zero_lt_one.trans_le (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _)
    have hsumM : (∑ Q ∈ active, m Q) = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
      calc
        _ = ∑ Q ∈ G.outerSet, ∑ i ∈ G.innerSet.filter (fun i => G.parent i = Q),
            volume (G.innerBody i).shade := by
          apply Finset.sum_congr rfl
          intro Q hQ
          dsimp only [m]
          apply Finset.sum_congr
          · ext i
            simp only [ShadedFactorFamily.fiber, Finset.mem_filter]
          · intro i hi; rfl
        _ = _ := Finset.sum_fiberwise_of_maps_to G.parent_mem (fun i => volume (G.innerBody i).shade)
    have hsumA : (∑ Q ∈ active, A Q) <= ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
      calc
        _ = ∑ i ∈ support, volume (T i).carrier :=
          Finset.sum_fiberwise_of_maps_to (fun i (hi : i ∈ support) => (Finset.mem_filter.mp hi).2)
            (fun i => volume (T i).carrier)
        _ = ∑ i ∈ support, volume (F.innerBody i).carrier := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hinner i (hG5sub (Finset.mem_filter.mp hi).1)]
        _ <= _ := Finset.sum_le_sum_of_subset (fun i hi => hG5sub (Finset.mem_filter.mp hi).1)
    have hpair : ∀ Q ∈ active, ∀ Q' ∈ active, m Q * K Q' <= (2 * D : NNReal) * z Q * A Q' := by
      intro Q hQ Q' hQ'
      calc
        _ = m Q * K Q := by rw [show K Q' = K Q from Tube.volume_carrier_eq_volume_carrier _ _]
        _ <= (D : ENNReal) * z Q * A Q := hcross Q hQ
        _ <= (D : ENNReal) * z Q * (2 * A Q') := mul_le_mul' le_rfl (hsupportComparable Q hQ Q' hQ')
        _ = _ := by push_cast; ring
    have hcrossAll : (∑ i ∈ G.innerSet, volume (G.innerBody i).shade) * (∑ Q ∈ active, K Q) <=
        (2 * D : NNReal) * (∑ Q ∈ active, z Q) * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
      calc
        _ = ∑ Q ∈ active, ∑ Q' ∈ active, m Q * K Q' := by
          rw [← hsumM, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun _ _ => Finset.mul_sum _ _ _)
        _ <= ∑ Q ∈ active, ∑ Q' ∈ active, (2 * D : NNReal) * z Q * A Q' :=
          Finset.sum_le_sum (fun Q hQ => Finset.sum_le_sum (hpair Q hQ))
        _ = (2 * D : NNReal) * (∑ Q ∈ active, z Q) * ∑ Q' ∈ active, A Q' := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
        _ <= _ := mul_le_mul' le_rfl hsumA
    have hVpos : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier :=
      hmassF.trans_le (Finset.sum_le_sum (fun i hi => measure_mono (F.innerBody i).shade_subset))
    have hVtop : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun i hi => (F.innerBody i).isCompact.measure_ne_top)
    have hKpos : 0 < ∑ Q ∈ active, K Q := by
      obtain ⟨Q, hQ⟩ := hactive
      exact (Tube.volume_pos_and_lt_top hrho0 hrho (Trho Q)).1.trans_le
        (Finset.single_le_sum (f := K) (fun _ _ => zero_le) hQ)
    have hKtop : (∑ Q ∈ active, K Q) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun Q hQ => (Trho Q).isCompact.measure_ne_top)
    have hrawFull : (R : ENNReal) * fullness' F.innerSet F.innerBody <=
        (2 * D : NNReal) * fullness' G.outerSet G.outerBody := by
      have hx : ((R : ENNReal) * ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) *
          (∑ Q ∈ active, K Q) <=
            (2 * D : NNReal) * (∑ Q ∈ active, z Q) * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier :=
        (mul_le_mul' hrefG.2 le_rfl).trans hcrossAll
      have hd := (ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKtop)).mpr hx
      have hd' : (R : ENNReal) * (∑ i ∈ F.innerSet, volume (F.innerBody i).shade) <=
          (((2 * D : NNReal) : ENNReal) * (∑ Q ∈ active, z Q) / (∑ Q ∈ active, K Q)) *
            (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by
        exact hd.trans_eq (mul_right_comm _ _ _)
      have hdivide := (ENNReal.div_le_iff hVpos.ne' hVtop).mpr hd'
      change (R : ENNReal) * ((∑ i ∈ F.innerSet, volume (F.innerBody i).shade) /
          (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier)) <=
        ((2 * D : NNReal) : ENNReal) * ((∑ Q ∈ active, z Q) / (∑ Q ∈ active, K Q))
      calc
        _ = ((R : ENNReal) * ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) /
            (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := (mul_div_assoc _ _ _).symm
        _ <= _ := hdivide
        _ = _ := mul_div_assoc _ _ _
    have hgeoD : 2 * D <= rhoTubesGeometricLoss n := by
      have h1 : (1 : NNReal) <= max 1 (Tube.volume_le.C n / Tube.le_volume.c n) ^ (2 : Nat) :=
        one_le_pow₀ (le_max_left _ _)
      have h2 := le_max_left (1 : NNReal) (rhoTubesOuterMultiplicityLoss n)
      calc
        _ <= 4 * D := mul_le_mul_of_nonneg_right (by norm_num) zero_le
        _ = 4 * D * 1 * 1 := by ring
        _ <= _ := by dsimp only [rhoTubesGeometricLoss, D, sourceRawCrossCostW97]; gcongr
    have hpaid : 2 * D <= R * L :=
      (inv_mul_le_iff₀ hRpos).mp ((mul_le_mul_of_nonneg_left hgeoD zero_le).trans hcost)
    have hcoef : ((2 * D : NNReal) : ENNReal) * (L : ENNReal)⁻¹ <= (R : ENNReal) := by
      rw [← ENNReal.coe_inv hL.ne', ← ENNReal.coe_mul]
      exact ENNReal.coe_le_coe.mpr ((mul_inv_le_iff₀ hL).mpr (by simpa only [mul_comm] using hpaid))
    have h2D : 0 < (2 * D : NNReal) := mul_pos (by norm_num) hD
    apply (ENNReal.mul_le_mul_iff_right (ENNReal.coe_ne_zero.mpr h2D.ne')
      ENNReal.coe_ne_top).mp
    calc
      _ = (((2 * D : NNReal) : ENNReal) * (L : ENNReal)⁻¹) * fullness' F.innerSet F.innerBody := by ring
      _ <= (R : ENNReal) * fullness' F.innerSet F.innerBody := mul_le_mul' hcoef le_rfl
      _ <= _ := hrawFull
  · intro Q hQ
    let u := F.step0.innerSet
    let t := (F.step1 hdelta hdisc).outerSet
    let k := F.pipelineExponent hdelta hdisc (rho : Real) hrhoR
    let ell := F.pipelineOuterExponent hdelta hdisc (rho : Real) hrhoR
    have hselected : selected.Nonempty := by
      obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp hmass5
      obtain ⟨x, hxi⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvi.ne'
      obtain ⟨z, hz, _⟩ := Set.mem_iUnion₂.mp (hG5cover (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩))
      exact ⟨z, hz⟩
    have hlocalBalls : ∀ z ∈ selected, ∃ J : Finset pi, J ⊆ G.outerSet ∧
        2 ^ ell <= J.card ∧ ∀ Q' ∈ J, ∃ p : E,
          Metric.ball p ((rho : Real) / 8) ⊆ (G.outerBody Q').shade ∩ Metric.ball z (2 * (rho : Real)) := by
      intro z hz
      let A := iUnionShade G5.innerSet G5.innerBody ∩ Metric.closedBall z (rho : Real)
      have hA : volume A ≠ 0 := by simpa only [A, G5, FactorFamily.pipelineFamily_innerSet] using hselectedPositive z hz
      have hnot : ¬A ⊆ nullUnion := fun hh => hA (measure_mono_null hh hnull)
      obtain ⟨y, hyA, hyNull⟩ := Set.not_subset.mp hnot
      obtain ⟨i0, hi0, hyi0⟩ := Set.mem_iUnion₂.mp hyA.1
      have hy0 : y ∈ (step5InnerBody F u t (F.pipelineSet hdelta hdisc (rho : Real) hrhoR)
          hOmega k selected rho i0).shade := by
        simpa only [G5, FactorFamily.pipelineFamily, step5ShadedFactorFamily_innerBody, u, t, k] using hyi0
      rw [shade_step5InnerBody, shade_step3InnerBody] at hy0
      have hyOmega : y ∈ F.pipelineSet hdelta hdisc (rho : Real) hrhoR := hy0.1.1.2
      have hySelected : y ∈ step5Selection selected rho := hy0.2
      let J := Kakeya.MultiplicityFamily.dyadicLevel t
        (fiberMultiplicity F (u.filter (fun i => F.parent i ∈ t))) k y
      have hyFibre : ∀ Q' ∈ J, y ∈ iUnionShade (G5.fiber Q') G5.innerBody := by
        intro Q' hQ'
        have hpos : 0 < fiberMultiplicity F (u.filter (fun i => F.parent i ∈ t)) Q' y :=
          (pow_pos (by norm_num : (0 : Nat) < 2) k).trans_le (Finset.mem_filter.mp hQ').2.1
        change 0 < {i ∈ {i ∈ {i ∈ u | F.parent i ∈ t} | F.parent i = Q'} |
          y ∈ (F.innerBody i).shade}.card at hpos
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        obtain ⟨hib, hYi⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiu, hip⟩ := Finset.mem_filter.mp hib
        have hi5 : i ∈ G5.innerSet := by
          simpa only [G5, FactorFamily.pipelineFamily_innerSet, FactorFamily.pipelineInnerSet, u, t] using hiu
        refine Set.mem_iUnion₂.mpr ⟨i, (hfibre5Mem Q' i).mpr ⟨hi5, hip⟩, ?_⟩
        change y ∈ (step5InnerBody F u t (F.pipelineSet hdelta hdisc (rho : Real) hrhoR)
          hOmega k selected rho i).shade
        rw [shade_step5InnerBody, shade_step3InnerBody]
        refine ⟨⟨⟨hYi, hyOmega⟩, ?_⟩, hySelected⟩
        simpa only [step3DyadicSet, Set.mem_setOf_eq, hip] using (Finset.mem_filter.mp hQ').2
      have hJactive : J ⊆ active := by
        intro Q' hQ'
        have hQt : Q' ∈ t := (Finset.mem_filter.mp hQ').1
        have hQ5 : Q' ∈ G5.outerSet := by
          simpa only [G5, FactorFamily.pipelineFamily, step5ShadedFactorFamily_outerSet, t] using hQt
        refine Finset.mem_filter.mpr ⟨hQ5, ?_⟩
        intro hzero
        apply hyNull
        exact Set.mem_iUnion₂.mpr ⟨Q', Finset.mem_filter.mpr
          ⟨hQ5, fun hqa => (Finset.mem_filter.mp hqa).2 hzero⟩, hyFibre Q' hQ'⟩
      refine ⟨J, hJactive, ?_, ?_⟩
      · have hb := F.bounds_of_mem_pipelineSet hdelta hdisc (rho : Real) hrhoR hyOmega
        simpa only [J, ell, k, t, u, FactorFamily.pipelineInnerSet] using hb.2.2.1
      · intro Q' hQ'
        have hyF := hyFibre Q' hQ'
        obtain ⟨i, hi, hYi⟩ := Set.mem_iUnion₂.mp hyF
        obtain ⟨hi5, hip⟩ := (hfibre5Mem Q' i).mp hi
        have hyCarrier : y ∈ (Trho Q').carrier := by
          have hbody := congrArg (fun K : ConvexSpaceBody E => K.carrier) (hG5body i)
          have hyFcar : y ∈ (F.innerBody i).carrier := hbody.subset ((G5.innerBody i).shade_subset hYi)
          have hh := hparentTube i (hG5sub hi5) hyFcar
          change y ∈ (Trho Q').toConvexSpaceBody
          simpa only [hip] using hh
        have hyCapsule : y ∈ Metric.cthickening (rho : Real) (segment Real (Trho Q').x (Trho Q').y) :=
          (Trho Q').carrier_eq_cthickening ▸ hyCarrier
        obtain ⟨p, hp⟩ := Kakeya.exists_ball_subset_cthickening_inter_ball
          (show IsCompact (segment Real (Trho Q').x (Trho Q').y) from isCompact_segment)
          hrhoR (show (rho : Real) <= 2 * (rho : Real) by linarith) hyCapsule
        refine ⟨p, ?_⟩
        intro w hw
        have hwCarrier : w ∈ (Trho Q').carrier := by
          rw [(Trho Q').carrier_eq_cthickening]
          exact (hp hw).1
        have hwThick : w ∈ Metric.cthickening (2 * (rho : Real)) (iUnionShade (G5.fiber Q') G5.innerBody) := by
          apply Metric.mem_cthickening_of_dist_le w y _ _
          · exact hyFibre Q' hQ'
          · exact (Metric.mem_ball.mp (hp hw).2).le.trans (by linarith)
        refine ⟨⟨hwCarrier, hwThick⟩, Metric.mem_ball.mpr ?_⟩
        calc
          dist w z <= dist w y + dist y z := dist_triangle _ _ _
          _ < (rho : Real) + rho := add_lt_add_of_lt_of_le
            (Metric.mem_ball.mp (hp hw).2) (Metric.mem_closedBall.mp hyA.2)
          _ = _ := by ring
    have houterLower : ((2 ^ ell : Nat) : ENNReal) <= (rhoTubesOuterMultiplicityLoss n : ENNReal) *
        ShadedBody.multiplicity G.outerSet G.outerBody := by
      have hp := ShadedBody.le_multiplicity_of_local_balls G.outerSet G.outerBody selected rho (2 ^ ell) 4
        hrho0 (by positivity) (by norm_num) hselected hselectedSep (by simpa using houterCover) hlocalBalls
      simpa only [ShadedBody.outerShadingPackingLoss, rhoTubesOuterMultiplicityLoss, n, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat, ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_pow,
        ENNReal.coe_ofNat, show (8 * 4 : Nat) = 32 by norm_num] using hp
    have hglobal : ShadedBody.multiplicity G5.innerSet G5.innerBody <=
        ((4 * (2 ^ k * 2 ^ ell) : Nat) : ENNReal) := by
      apply ShadedBody.multiplicity_le_of_pointwiseMultiplicity_le
      intro x hx
      exact_mod_cast (F.pipelineFamily_multiplicity hdelta hdisc (rho : Real) hrhoR hOmega selected rho hx).2.le
    have hrefMu : ShadedBody.multiplicity F.innerSet F.innerBody <=
        (R : ENNReal)⁻¹ * ShadedBody.multiplicity G5.innerSet G5.innerBody :=
      ShadedBody.multiplicity_le_of_isCRefinement F.innerSet F.innerBody hRpos.ne' hrefG5
    have hfourGeo : 4 * rhoTubesOuterMultiplicityLoss n <= rhoTubesGeometricLoss n := by
      have h1 := le_max_left (1 : NNReal) (Kakeya.Tube.dilateFullness.C n)
      have h2 := one_le_pow₀ (n := 2) (le_max_left (1 : NNReal) (Tube.volume_le.C n / Tube.le_volume.c n))
      have h3 := le_max_right 1 (rhoTubesOuterMultiplicityLoss n)
      calc
        _ = 4 * 1 * 1 * rhoTubesOuterMultiplicityLoss n := by ring
        _ <= _ := by dsimp only [rhoTubesGeometricLoss]; gcongr
    have hcostScalar : 4 * R⁻¹ * rhoTubesOuterMultiplicityLoss n <=
        shadingMultiplicityEstimateForRhoTubesDilate.C n N delta 1 := by
      calc
        _ = R⁻¹ * (4 * rhoTubesOuterMultiplicityLoss n) := by ring
        _ <= _ := (mul_le_mul_of_nonneg_left hfourGeo zero_le).trans hcost
    calc
      _ <= (R : ENNReal)⁻¹ * ((4 * (2 ^ k * 2 ^ ell) : Nat) : ENNReal) :=
        hrefMu.trans (mul_le_mul' le_rfl hglobal)
      _ = ((4 * R⁻¹ : NNReal) : ENNReal) * ((2 ^ ell : Nat) : ENNReal) * (q : ENNReal) := by
        rw [ENNReal.coe_mul, ENNReal.coe_inv hRpos.ne']
        simp only [q, k, Nat.cast_mul, ENNReal.coe_natCast, ENNReal.coe_ofNat]
        ring
      _ <= ((4 * R⁻¹ : NNReal) : ENNReal) *
          ((rhoTubesOuterMultiplicityLoss n : ENNReal) * ShadedBody.multiplicity G.outerSet G.outerBody) *
            ShadedBody.multiplicity (G.fiber Q) G.innerBody :=
        mul_le_mul' (mul_le_mul' le_rfl houterLower) (hqLower Q hQ)
      _ = ((4 * R⁻¹ * rhoTubesOuterMultiplicityLoss n : NNReal) : ENNReal) *
          ShadedBody.multiplicity G.outerSet G.outerBody * ShadedBody.multiplicity (G.fiber Q) G.innerBody := by
        push_cast
        ring
      _ <= _ := mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.mpr hcostScalar) le_rfl) le_rfl
  · intro i hi hinot
    have hi5 : i ∉ G5.innerSet := fun hi5 => hinot (Finset.mem_filter.mpr
      ⟨hi5, (Finset.mem_filter.mp hi).2⟩)
    simp only [G, completed, if_neg hi5, ShadedBody.restrictShade, Set.inter_empty]
  · exact hcross
  · intro x hx
    let U := iUnionShade G.innerSet G.innerBody
    let W := iUnionShade G.outerSet G.outerBody
    let O : ENNReal := Kakeya.factoringStep5OverlapConstant n
    let B : ENNReal := volume (Metric.ball x (rho : Real))
    let m : ENNReal := volume (U ∩ Metric.ball x (rho : Real))
    have hB0 : B ≠ 0 := by simp only [B, InnerProductSpace.volume_ball]; positivity
    have hBtop : B ≠ ⊤ := by simp only [B, InnerProductSpace.volume_ball]; finiteness
    have hlocal : ∀ y : E, ∀ z ∈ selected, volume (U ∩ Metric.ball y (rho : Real)) <=
        2 * O * volume (U ∩ Metric.closedBall z (rho : Real)) := by
      intro y z hz
      have hballEq := measure_congr (hglobalAE.inter
        (Filter.EventuallyEq.rfl : Metric.ball y (rho : Real) =ᵐ[volume] Metric.ball y (rho : Real)))
      have hclosedEq := measure_congr (hglobalAE.inter
        (Filter.EventuallyEq.rfl : Metric.closedBall z (rho : Real) =ᵐ[volume] Metric.closedBall z (rho : Real)))
      change volume (iUnionShade G.innerSet G.innerBody ∩ Metric.ball y (rho : Real)) <= _
      rw [hballEq, show volume (U ∩ Metric.closedBall z (rho : Real)) =
        volume (iUnionShade G5.innerSet G5.innerBody ∩ Metric.closedBall z (rho : Real)) from hclosedEq]
      simpa only [G5, O, n, FactorFamily.pipelineInnerSet, FactorFamily.pipelineFamily,
        step5ShadedFactorFamily_innerSet, step5ShadedFactorFamily_innerBody] using
        volume_iUnionShade_step5_inter_ball_le F F.step0.innerSet (F.step1 hdelta hdisc).outerSet
          (F.pipelineSet hdelta hdisc (rho : Real) hrhoR) hOmega
          (F.pipelineExponent hdelta hdisc (rho : Real) hrhoR) hrho0 hselectedSep hballComparable y hz
    have hball : ∀ z : E, volume (Metric.closedBall z (4 * (rho : Real))) = (4 : ENNReal) ^ n * B := by
      intro z
      rw [InnerProductSpace.volume_closedBall]
      simp only [B, InnerProductSpace.volume_ball]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 4)]
      norm_num [n, mul_pow]
      ring
    have hWvol : volume W <= (selected.card : ENNReal) * ((4 : ENNReal) ^ n * B) := by
      calc
        _ <= volume (⋃ z ∈ selected, Metric.closedBall z (4 * (rho : Real))) := measure_mono houterCover
        _ <= ∑ z ∈ selected, volume (Metric.closedBall z (4 * (rho : Real))) := measure_biUnion_finset_le _ _
        _ = _ := by simp_rw [hball]; rw [Finset.sum_const, nsmul_eq_mul]
    have hsum : (∑ z ∈ selected, volume (U ∩ Metric.closedBall z (rho : Real))) <= O * volume U := by
      calc
        _ <= O * volume (⋃ z ∈ selected, U ∩ Metric.closedBall z (rho : Real)) := by
          apply MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le
          · intro z hz
            exact (measurableSet_iUnion_shade G.innerSet G.innerBody).inter measurableSet_closedBall
          · intro y
            have hcard : {z ∈ selected | y ∈ U ∩ Metric.closedBall z (rho : Real)}.card <=
                {z ∈ selected | y ∈ Metric.closedBall z (rho : Real)}.card := by
              apply Finset.card_le_card
              intro z hz
              exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.2⟩
            rw [Finset.filter_congr_decidable]
            exact hcard.trans (hselectedOverlap y)
        _ <= _ := mul_le_mul' le_rfl (measure_mono (Set.iUnion₂_subset (fun z hz => Set.inter_subset_left)))
    have hcardm : (selected.card : ENNReal) * m <= 2 * O *
        ∑ z ∈ selected, volume (U ∩ Metric.closedBall z (rho : Real)) := by
      calc
        _ = ∑ z ∈ selected, m := by rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ z ∈ selected, 2 * O * volume (U ∩ Metric.closedBall z (rho : Real)) :=
          Finset.sum_le_sum (fun z hz => hlocal x z hz)
        _ = _ := by rw [Finset.mul_sum]
    have hcrossLocal : volume W * m <= (rhoTubesBallLoss n : ENNReal) * B * volume U := by
      calc
        _ <= ((selected.card : ENNReal) * ((4 : ENNReal) ^ n * B)) * m := mul_le_mul' hWvol le_rfl
        _ = ((4 : ENNReal) ^ n * B) * ((selected.card : ENNReal) * m) := by ring
        _ <= ((4 : ENNReal) ^ n * B) * (2 * O * (O * volume U)) :=
          mul_le_mul' le_rfl (hcardm.trans (mul_le_mul' le_rfl hsum))
        _ = _ := by simp only [rhoTubesBallLoss, O]; push_cast; ring
    have hb : volume W * (m / B) <= (rhoTubesBallLoss n : ENNReal) * volume U := by
      rw [← mul_div_assoc]
      apply (ENNReal.div_le_iff hB0 hBtop).mpr
      exact hcrossLocal.trans_eq (mul_right_comm _ _ _)
    let L : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C n N delta 1
    have hballCost : rhoTubesBallLoss n <= L := le_max_of_le_right (le_max_right _ _)
    have hL0 : (L : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr
      (zero_lt_one.trans_le (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _)).ne'
    calc
      _ = (L : ENNReal)⁻¹ * (volume W * (m / B)) := by ring
      _ <= (L : ENNReal)⁻¹ * ((rhoTubesBallLoss n : ENNReal) * volume U) := mul_le_mul' le_rfl hb
      _ <= (L : ENNReal)⁻¹ * ((L : ENNReal) * volume U) :=
        mul_le_mul' le_rfl (mul_le_mul' (ENNReal.coe_le_coe.mpr hballCost) le_rfl)
      _ = _ := ENNReal.inv_mul_cancel_left hL0 ENNReal.coe_ne_top

/-- B2: tube round caps, the raw local-union inequality and induced
neighbourhood inclusion control each whole fibre's true shade mass. -/
theorem rho_shadow_volume_controls_fibre_union_w97 :
    ∃ Cgeom : NNReal, 1 <= Cgeom ∧
      ∀ {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
        {delta rho : NNReal}, 0 < delta -> delta <= rho -> rho <= 1 ->
      ∀ (F : ShadedBody.FactorFamily E iota pi)
        (T : iota -> ShadedTube delta E) (Trho : pi -> Tube rho E)
        (G : ShadedBody.ShadedFactorFamily E iota pi)
        (raw : ActualRawRhoStatisticsW97 F T Trho G),
        0 < volume (iUnionShade G.innerSet G.innerBody) ->
        volume (iUnionShade G.innerSet G.innerBody) < ⊤ ->
        0 < volume (iUnionShade G.outerSet G.outerBody) ->
        volume (iUnionShade G.outerSet G.outerBody) < ⊤ ->
        ∀ Q ∈ G.outerSet,
          (∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) <=
            (Cgeom : ENNReal) * (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank Real E) F.innerSet.card delta 1 : ENNReal) * (raw.q : ENNReal) *
              (volume (iUnionShade G.innerSet G.innerBody) / volume (iUnionShade G.outerSet G.outerBody)) *
              volume (G.outerBody Q).shade := by
  let n := Module.finrank Real E
  refine ⟨(2 * 192 ^ n : NNReal), ?_, ?_⟩
  · have : (1 : NNReal) <= 192 ^ n := one_le_pow₀ (by norm_num)
    exact this.trans (le_mul_of_one_le_left zero_le (by norm_num))
  intro iota pi _ _ delta rho hdelta hdrho hrho F T Trho G raw hUpos hUtop hWpos hWtop Q hQ
  let U := iUnionShade G.innerSet G.innerBody
  let W := iUnionShade G.outerSet G.outerBody
  let V := iUnionShade (G.fiber Q) G.innerBody
  let L : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C n F.innerSet.card delta 1
  have hrNN : 0 < rho := hdelta.trans_le hdrho
  have hr : (0 : Real) < rho := by exact_mod_cast hrNN
  have hLpos : (0 : ENNReal) < L := by
    exact_mod_cast zero_lt_one.trans_le
      (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C n F.innerSet.card delta 1)
  have hVZ : V ⊆ (G.outerBody Q).shade := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hi' : i ∈ G.innerSet ∧ G.parent i = Q := by
      simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
    simpa only [hi'.2] using G.shade_subset_parent i hi'.1 hxi
  have hVU : V ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hi' : i ∈ G.innerSet ∧ G.parent i = Q := by
      simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
    exact Set.mem_iUnion₂.mpr ⟨i, hi'.1, hxi⟩
  have hVW : V ⊆ W := hVZ.trans
    (Set.subset_iUnion₂_of_subset Q hQ (Set.Subset.refl _))
  have hVK : V ⊆ (Trho Q).carrier := by
    have hc := congrArg (fun K : ConvexSpaceBody E => K.carrier) (raw.outer_body Q hQ)
    exact hVZ.trans ((G.outerBody Q).shade_subset.trans hc.subset)
  have hthickFinite : ∀ s : Finset iota,
      Metric.cthickening (2 * (rho : Real)) (iUnionShade s G.innerBody) =
        ⋃ i ∈ s, Metric.cthickening (2 * (rho : Real)) (G.innerBody i).shade := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [iUnionShade]
    | @insert i s hi ih =>
      simpa only [iUnionShade, Finset.set_biUnion_insert, Metric.cthickening_union] using
        congrArg (fun A => Metric.cthickening (2 * (rho : Real)) (G.innerBody i).shade ∪ A) ih
  have hshadow : (Trho Q).carrier ∩ Metric.cthickening (2 * (rho : Real)) V ⊆
      (G.outerBody Q).shade := by
    intro x hx
    have hxt : x ∈ ⋃ i ∈ G.fiber Q,
        Metric.cthickening (2 * (rho : Real)) (G.innerBody i).shade := by
      rw [← hthickFinite]
      exact hx.2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxt
    apply raw.neighbourhood Q hQ i hi
    refine ⟨?_, hxi⟩
    have hc := congrArg (fun K : ConvexSpaceBody E => K.carrier) (raw.outer_body Q hQ)
    exact hc.symm.subset hx.1
  have hcap : volume (Metric.cthickening (2 * (rho : Real)) V) <=
      (48 : ENNReal) ^ n * volume (G.outerBody Q).shade := by
    have hc := Kakeya.volume_cthickening_le_mul_volume_inter_cthickening
      (show IsCompact (segment Real (Trho Q).x (Trho Q).y) from isCompact_segment)
      (show 0 < 2 * (rho : Real) by positivity) le_rfl
      (show V ⊆ Metric.cthickening (rho : Real) (segment Real (Trho Q).x (Trho Q).y) from
        (Trho Q).carrier_eq_cthickening ▸ hVK)
    have hc' : volume (Metric.cthickening (2 * (rho : Real)) V) <=
        (48 : ENNReal) ^ n *
          volume ((Trho Q).carrier ∩ Metric.cthickening (2 * (rho : Real)) V) := by
      simpa only [Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C,
        Nat.cast_pow, Nat.cast_ofNat, (Trho Q).carrier_eq_cthickening, n] using hc
    exact hc'.trans (mul_le_mul' le_rfl (measure_mono hshadow))
  let w : NNReal := rho / 2
  have hw : 0 < w := by dsimp [w]; positivity
  obtain ⟨S, hSV, hsep, hcover, _⟩ :=
    ((Trho Q).isCompact.isBounded.subset hVK).exists_finset_isSeparated_isCover_closedBall hw
  have hdisj : (S : Set E).PairwiseDisjoint
      (fun x => Metric.closedBall x ((w : Real) / 2)) := by
    intro x hx y hy hxy
    have hdist : (w : ENNReal) < edist x y := hsep hx hy hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal (p := w)] at hdist
    have hreal := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg w.coe_nonneg).mp hdist
    exact Metric.closedBall_disjoint_closedBall (by linarith)
  have hsmall : (S.card : ENNReal) * volume (Metric.closedBall (0 : E) ((w : Real) / 2)) <=
      volume (Metric.cthickening (2 * (rho : Real)) V) := by
    calc
      _ = ∑ x ∈ S, volume (Metric.closedBall x ((w : Real) / 2)) := by
        simp only [InnerProductSpace.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ x ∈ S, Metric.closedBall x ((w : Real) / 2)) :=
        (measure_biUnion_finset hdisj (fun _ _ => measurableSet_closedBall)).symm
      _ <= _ := measure_mono (Set.iUnion₂_subset fun x hx =>
        (Metric.closedBall_subset_closedBall (show (w : Real) / 2 <= 2 * (rho : Real) by
          dsimp [w]
          push_cast
          linarith)).trans (Metric.closedBall_subset_cthickening (hSV hx) _))
  let v : ENNReal := volume (Metric.ball (0 : E) (rho : Real))
  have hvpos : v ≠ 0 := by dsimp [v]; simp only [InnerProductSpace.volume_ball]; positivity
  have hvtop : v ≠ ⊤ := by dsimp [v]; simp only [InnerProductSpace.volume_ball]; finiteness
  have hball : ∀ z : E, volume (Metric.ball z (rho : Real)) = v := by
    intro z
    simp only [v, InnerProductSpace.volume_ball]
  have hballRatio : v = (4 : ENNReal) ^ n *
      volume (Metric.closedBall (0 : E) ((w : Real) / 2)) := by
    dsimp only [v]
    rw [show (rho : Real) = 4 * ((w : Real) / 2) by dsimp [w]; push_cast; ring,
      InnerProductSpace.volume_ball, InnerProductSpace.volume_closedBall]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 4)]
    norm_num [mul_pow]
    ring
  have hcount : (S.card : ENNReal) * v <= (192 : ENNReal) ^ n * volume (G.outerBody Q).shade := by
    calc
      _ = (4 : ENNReal) ^ n * ((S.card : ENNReal) *
          volume (Metric.closedBall (0 : E) ((w : Real) / 2))) := by rw [hballRatio]; ring
      _ <= (4 : ENNReal) ^ n * ((48 : ENNReal) ^ n * volume (G.outerBody Q).shade) :=
        mul_le_mul' le_rfl (hsmall.trans hcap)
      _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num
  have hlocal : ∀ z ∈ S, volume (U ∩ Metric.ball z (rho : Real)) <=
      (L : ENNReal) * (volume U / volume W) * v := by
    intro z hz
    have hraw := raw.local_union z (hVW (hSV hz))
    have hp : (L : ENNReal)⁻¹ * volume W *
        (volume (U ∩ Metric.ball z (rho : Real)) / v) <= volume U := by
      simpa only [L, U, W, n, hball] using hraw
    have hp' : volume W * (volume (U ∩ Metric.ball z (rho : Real)) / v) <=
        (L : ENNReal) * volume U :=
      (ENNReal.inv_mul_le_iff hLpos.ne' ENNReal.coe_ne_top).mp (by simpa only [mul_assoc] using hp)
    have hdiv : volume (U ∩ Metric.ball z (rho : Real)) / v <=
        ((L : ENNReal) * volume U) / volume W :=
      (ENNReal.le_div_iff_mul_le (Or.inl hWpos.ne') (Or.inl hWtop.ne)).mpr (by
        simpa only [mul_comm] using hp')
    have hout := (ENNReal.div_le_iff hvpos hvtop).mp hdiv
    simpa only [div_eq_mul_inv, mul_assoc] using hout
  have hVcover : V ⊆ ⋃ z ∈ S, U ∩ Metric.ball z (rho : Real) := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact Set.mem_iUnion₂.mpr ⟨z, hz, hVU hx, Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hxz).trans_lt (show (w : Real) < rho by
        dsimp [w]
        push_cast
        linarith))⟩
  have hVbound : volume V <= (192 : ENNReal) ^ n * (L : ENNReal) *
      (volume U / volume W) * volume (G.outerBody Q).shade := by
    calc
      _ <= volume (⋃ z ∈ S, U ∩ Metric.ball z (rho : Real)) := measure_mono hVcover
      _ <= ∑ z ∈ S, volume (U ∩ Metric.ball z (rho : Real)) := measure_biUnion_finset_le _ _
      _ <= ∑ z ∈ S, (L : ENNReal) * (volume U / volume W) * v := Finset.sum_le_sum hlocal
      _ = (L : ENNReal) * (volume U / volume W) * ((S.card : ENNReal) * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ <= (L : ENNReal) * (volume U / volume W) *
          ((192 : ENNReal) ^ n * volume (G.outerBody Q).shade) := mul_le_mul' le_rfl hcount
      _ = _ := by ring
  have hmass := (ShadedBody.multiplicity_le_iff (G.fiber Q) G.innerBody).mp (raw.q_upper Q hQ)
  calc
    _ <= (2 * (raw.q : ENNReal)) * volume V := hmass
    _ <= (2 * (raw.q : ENNReal)) * ((192 : ENNReal) ^ n * (L : ENNReal) *
        (volume U / volume W) * volume (G.outerBody Q).shade) := mul_le_mul' le_rfl hVbound
    _ = _ := by simp only [L, U, W, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]; ring

/-- B3 proves subset stability on unchanged whole fibres from raw witnesses;
the requested scalar estimate is not a premise. -/
theorem raw_parent_subset_scalar_and_fullness_w97 :
    ∃ Cgeom : NNReal, 1 <= Cgeom ∧
      ∀ {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
        {delta rho : NNReal}, 0 < delta -> delta <= rho -> rho <= 1 ->
      ∀ (F : ShadedBody.FactorFamily E iota pi)
        (T : iota -> ShadedTube delta E) (Trho : pi -> Tube rho E)
        (G : ShadedBody.ShadedFactorFamily E iota pi)
        (raw : ActualRawRhoStatisticsW97 F T Trho G)
        (H : Finset pi) (r : ENNReal), H ⊆ G.outerSet -> 0 < r -> r <= 1 ->
        r * (∑ Q ∈ G.outerSet, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade) <=
          ∑ Q ∈ H, ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade ->
        let fineH := G.innerSet.filter (fun i => G.parent i ∈ H)
        H.Nonempty ∧ fineH.Nonempty ∧
        (∀ Q ∈ H, completeFibreW94 fineH G.parent Q = G.fiber Q) ∧
        (∀ Q ∈ H, ShadedBody.multiplicity F.innerSet F.innerBody <=
          (Cgeom : ENNReal) * (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank Real E) F.innerSet.card delta 1 : ENNReal) ^ (2 : Nat) / r *
            ShadedBody.multiplicity H G.outerBody * ShadedBody.multiplicity (G.fiber Q) G.innerBody) ∧
        (2 * (sourceRawCrossCostW97 (Module.finrank Real E) : ENNReal))⁻¹ *
          fullness' fineH G.innerBody <= fullness' H G.outerBody := by
  obtain ⟨Cgeom, hCgeom, hshadow⟩ := rho_shadow_volume_controls_fibre_union_w97 (E := E)
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro iota pi _ _ delta rho hdelta hdrho hrho F T Trho G raw H r hHG hr hr1 hretained
  let fineH := G.innerSet.filter (fun i => G.parent i ∈ H)
  let mass : pi -> ENNReal := fun Q => ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade
  let shade : pi -> ENNReal := fun Q => volume (G.outerBody Q).shade
  let A : pi -> ENNReal := fun Q =>
    ∑ i ∈ completeFibreW94 raw.carrierSupport F.parent Q, volume (T i).carrier
  let K : pi -> ENNReal := fun Q => volume (G.outerBody Q).carrier
  let Lloss : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C
    (Module.finrank Real E) F.innerSet.card delta 1
  let D : ENNReal := sourceRawCrossCostW97 (Module.finrank Real E)
  have hrfinite : r ≠ ⊤ := (hr1.trans_lt (by simp)).ne
  have hLpos : (0 : ENNReal) < Lloss := by
    exact_mod_cast zero_lt_one.trans_le
      (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C _ _ _ _)
  have hGF : G.innerSet ⊆ F.innerSet := by
    rw [raw.inner_eq]
    exact Finset.filter_subset _ _
  have hfibre : ∀ Q ∈ H, completeFibreW94 fineH G.parent Q = G.fiber Q := by
    intro Q hQ
    ext i
    simp only [completeFibreW94, fineH, ShadedFactorFamily.fiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, _⟩, hp⟩
      exact ⟨hi, hp⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨hi, hp.symm ▸ hQ⟩, hp⟩
  have sumH : ∀ w : iota -> ENNReal,
      (∑ Q ∈ H, ∑ i ∈ G.fiber Q, w i) = ∑ i ∈ fineH, w i := by
    intro w
    calc
      _ = ∑ Q ∈ H, ∑ i ∈ fineH.filter (fun i => G.parent i = Q), w i := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [show fineH.filter (fun i => G.parent i = Q) = G.fiber Q from hfibre Q hQ]
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun i (hi : i ∈ fineH) => (Finset.mem_filter.mp hi).2) w
  have sumG : (∑ Q ∈ G.outerSet, mass Q) = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    calc
      _ = ∑ Q ∈ G.outerSet, ∑ i ∈ G.innerSet.filter (fun i => G.parent i = Q),
          volume (G.innerBody i).shade := by
        apply Finset.sum_congr rfl
        intro Q hQ
        dsimp only [mass]
        apply Finset.sum_congr
        · ext i
          simp only [ShadedFactorFamily.fiber, Finset.mem_filter]
        · intro i hi
          rfl
      _ = _ := Finset.sum_fiberwise_of_maps_to G.parent_mem
        (fun i => volume (G.innerBody i).shade)
  obtain ⟨Q0, hQ0⟩ := raw.outer_nonempty
  have hmassG : 0 < ∑ Q ∈ G.outerSet, mass Q :=
    (raw.fibre_mass_pos Q0 hQ0).trans_le
      (Finset.single_le_sum (f := mass) (fun Q hQ => zero_le) hQ0)
  have hmassH : 0 < ∑ Q ∈ H, mass Q :=
    (ENNReal.mul_pos hr.ne' hmassG.ne').trans_le hretained
  have hH : H.Nonempty := by
    obtain ⟨Q, hQ, _⟩ := Finset.sum_pos_iff.mp hmassH
    exact ⟨Q, hQ⟩
  have hfineMass : 0 < ∑ i ∈ fineH, volume (G.innerBody i).shade := by
    rw [← sumH]
    exact hmassH
  have hfineH : fineH.Nonempty := by
    obtain ⟨i, hi, _⟩ := Finset.sum_pos_iff.mp hfineMass
    exact ⟨i, hi⟩
  have houterShade : ∀ Q ∈ G.outerSet, 0 < shade Q := by
    intro Q hQ
    have hv : 0 < volume (Trho Q).carrier :=
      (Tube.volume_pos_and_lt_top (hdelta.trans_le hdrho) hrho (Trho Q)).1
    have hpositive := ENNReal.mul_pos (raw.fibre_mass_pos Q hQ).ne' hv.ne'
    have hcross := raw.cross_density Q hQ
    by_contra hn
    have hz : volume (G.outerBody Q).shade = 0 := le_antisymm (not_lt.mp hn) bot_le
    rw [hz, mul_zero, zero_mul] at hcross
    exact (not_lt_of_ge hcross) hpositive
  have hUinner : 0 < volume (iUnionShade G.innerSet G.innerBody) := by
    obtain ⟨i, hi, hvi⟩ := Finset.sum_pos_iff.mp (sumG ▸ hmassG)
    exact hvi.trans_le (measure_mono (Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)))
  have hUouter : 0 < volume (iUnionShade G.outerSet G.outerBody) :=
    (houterShade Q0 hQ0).trans_le
      (measure_mono (Set.subset_iUnion₂_of_subset Q0 hQ0 (Set.Subset.refl _)))
  have hUinnerTop := ShadedBody.volume_iUnion_shade_ne_top G.innerSet G.innerBody
  have hUouterTop := ShadedBody.volume_iUnion_shade_ne_top G.outerSet G.outerBody
  have hshadowH : (∑ Q ∈ H, mass Q) <=
      (Cgeom : ENNReal) * (Lloss : ENNReal) * (raw.q : ENNReal) *
        (volume (iUnionShade G.innerSet G.innerBody) /
          volume (iUnionShade G.outerSet G.outerBody)) * ∑ Q ∈ H, shade Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun Q hQ => hshadow hdelta hdrho hrho F T Trho G raw
      hUinner hUinnerTop.lt_top hUouter hUouterTop.lt_top Q (hHG hQ))
  have hmuH : (∑ Q ∈ H, shade Q) / volume (iUnionShade G.outerSet G.outerBody) <=
      ShadedBody.multiplicity H G.outerBody := by
    apply ENNReal.div_le_div le_rfl
    exact measure_mono (Set.iUnion₂_subset fun Q hQ =>
      Set.subset_iUnion₂_of_subset Q (hHG hQ) (Set.Subset.refl _))
  have hmuG : ShadedBody.multiplicity G.innerSet G.innerBody <=
      ((Cgeom : ENNReal) * (Lloss : ENNReal) / r) *
        ShadedBody.multiplicity H G.outerBody * (raw.q : ENNReal) := by
    apply (ShadedBody.multiplicity_le_iff _ _).mpr
    apply (ENNReal.mul_le_mul_iff_right hr.ne' hrfinite).mp
    calc
      r * (∑ i ∈ G.innerSet, volume (G.innerBody i).shade) <= ∑ Q ∈ H, mass Q := by
        rw [← sumG]
        exact hretained
      _ <= _ := hshadowH
      _ = ((Cgeom : ENNReal) * (Lloss : ENNReal) * (raw.q : ENNReal) *
          volume (iUnionShade G.innerSet G.innerBody)) *
          ((∑ Q ∈ H, shade Q) / volume (iUnionShade G.outerSet G.outerBody)) := by
        simp only [div_eq_mul_inv]
        ring
      _ <= ((Cgeom : ENNReal) * (Lloss : ENNReal) * (raw.q : ENNReal) *
          volume (iUnionShade G.innerSet G.innerBody)) *
          ShadedBody.multiplicity H G.outerBody := mul_le_mul' le_rfl hmuH
      _ = _ := by
        calc
          _ = (((Cgeom : ENNReal) * (Lloss : ENNReal) / r) * r) *
              ShadedBody.multiplicity H G.outerBody * (raw.q : ENNReal) *
              volume (iUnionShade G.innerSet G.innerBody) := by
            rw [ENNReal.div_mul_cancel hr.ne' hrfinite]
            ring
          _ = _ := by ring
  have hmuF : ShadedBody.multiplicity F.innerSet F.innerBody <=
      (Lloss : ENNReal) * ShadedBody.multiplicity G.innerSet G.innerBody := by
    apply (ENNReal.inv_mul_le_iff hLpos.ne' ENNReal.coe_ne_top).mp
    have hLnz : Lloss ≠ 0 := ENNReal.coe_pos.mp hLpos |>.ne'
    rw [← ENNReal.coe_inv hLnz]
    exact raw.raw_refinement.mul_multiplicity_le
  have hscalar : ∀ Q ∈ H, ShadedBody.multiplicity F.innerSet F.innerBody <=
      (Cgeom : ENNReal) * (Lloss : ENNReal) ^ (2 : Nat) / r *
        ShadedBody.multiplicity H G.outerBody * ShadedBody.multiplicity (G.fiber Q) G.innerBody := by
    intro Q hQ
    calc
      _ <= (Lloss : ENNReal) *
          (((Cgeom : ENNReal) * (Lloss : ENNReal) / r) *
            ShadedBody.multiplicity H G.outerBody * (raw.q : ENNReal)) :=
        hmuF.trans (mul_le_mul' le_rfl hmuG)
      _ = (Cgeom : ENNReal) * (Lloss : ENNReal) ^ (2 : Nat) / r *
          ShadedBody.multiplicity H G.outerBody * (raw.q : ENNReal) := by
        simp only [div_eq_mul_inv, pow_two]
        ring
      _ <= _ := mul_le_mul' le_rfl (raw.q_lower Q (hHG hQ))
  have hAcarrier : ∀ Q ∈ H, A Q <= ∑ i ∈ G.fiber Q, volume (G.innerBody i).carrier := by
    intro Q hQ
    have hsub : completeFibreW94 raw.carrierSupport F.parent Q ⊆ G.fiber Q := by
      intro i hi
      obtain ⟨hiS, hp⟩ := Finset.mem_filter.mp hi
      have hiG := raw.support_subset hiS
      have hpG : G.parent i = Q := raw.parent_eq ▸ hp
      simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using And.intro hiG hpG
    calc
      A Q = ∑ i ∈ completeFibreW94 raw.carrierSupport F.parent Q,
          volume (G.innerBody i).carrier := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun W : ConvexSpaceBody E => volume W.carrier)
          (raw.inner_body i (hGF (raw.support_subset (Finset.mem_filter.mp hi).1))).symm
      _ <= _ := Finset.sum_le_sum_of_subset hsub
  have hKsame : ∀ Q ∈ H, ∀ R ∈ H, K Q = K R := by
    intro Q hQ R hR
    change volume (G.outerBody Q).toConvexSpaceBody.carrier =
      volume (G.outerBody R).toConvexSpaceBody.carrier
    rw [raw.outer_body Q (hHG hQ), raw.outer_body R (hHG hR)]
    exact Tube.volume_carrier_eq_volume_carrier (Trho Q) (Trho R)
  have hpair : ∀ Q ∈ H, ∀ R ∈ H, mass Q * K R <= 2 * D * shade Q * A R := by
    intro Q hQ R hR
    have hc := raw.cross_density Q (hHG hQ)
    have hbody := congrArg (fun W : ConvexSpaceBody E => volume W.carrier) (raw.outer_body Q (hHG hQ))
    calc
      mass Q * K R = mass Q * K Q := by rw [hKsame Q hQ R hR]
      _ <= D * shade Q * A Q := by simpa only [mass, K, D, shade, A, hbody] using hc
      _ <= D * shade Q * (2 * A R) := mul_le_mul' le_rfl
        (raw.support_fibre_comparable Q (hHG hQ) R (hHG hR))
      _ = _ := by ring
  have hcrossH : (∑ i ∈ fineH, volume (G.innerBody i).shade) * (∑ Q ∈ H, K Q) <=
      2 * D * (∑ Q ∈ H, shade Q) * ∑ i ∈ fineH, volume (G.innerBody i).carrier := by
    calc
      _ = ∑ Q ∈ H, ∑ R ∈ H, mass Q * K R := by
        rw [← sumH (fun i => volume (G.innerBody i).shade), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro Q hQ
        exact Finset.mul_sum _ _ _
      _ <= ∑ Q ∈ H, ∑ R ∈ H, 2 * D * shade Q * A R :=
        Finset.sum_le_sum (fun Q hQ => Finset.sum_le_sum (hpair Q hQ))
      _ = 2 * D * (∑ Q ∈ H, shade Q) * ∑ R ∈ H, A R := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ <= 2 * D * (∑ Q ∈ H, shade Q) * ∑ Q ∈ H,
          ∑ i ∈ G.fiber Q, volume (G.innerBody i).carrier :=
        mul_le_mul' le_rfl (Finset.sum_le_sum hAcarrier)
      _ = _ := by rw [sumH]
  refine ⟨hH, hfineH, hfibre, hscalar, ?_⟩
  have hcarrierPos : 0 < ∑ i ∈ fineH, volume (G.innerBody i).carrier := hfineMass.trans_le
    (Finset.sum_le_sum fun i hi => measure_mono (G.innerBody i).shade_subset)
  have hcarrierTop : (∑ i ∈ fineH, volume (G.innerBody i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i hi => (G.innerBody i).isCompact.measure_ne_top)
  have hKpos : 0 < ∑ Q ∈ H, K Q := by
    obtain ⟨Q, hQ⟩ := hH
    have hQpos : 0 < K Q := (houterShade Q (hHG hQ)).trans_le
      (measure_mono (G.outerBody Q).shade_subset)
    exact hQpos.trans_le (Finset.single_le_sum (f := K) (fun R hR => zero_le) hQ)
  have hKtop : (∑ Q ∈ H, K Q) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun Q hQ => (G.outerBody Q).isCompact.measure_ne_top)
  have hDpos : 0 < D := by
    dsimp [D, sourceRawCrossCostW97]
    exact_mod_cast zero_lt_one.trans_le (le_max_left 1 (Tube.dilateFullness.C (Module.finrank Real E)))
  have h2D : 2 * D ≠ 0 := by positivity
  have h2Dtop : 2 * D ≠ ⊤ := by dsimp [D]; finiteness
  apply (ENNReal.inv_mul_le_iff h2D h2Dtop).mpr
  apply (ENNReal.div_le_iff hcarrierPos.ne' hcarrierTop).mpr
  have hdiv := (ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKtop)).mpr hcrossH
  simpa only [fullness', K, shade, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- B4 discards actual tiny fine-mass fibres before the ratio band; the
realized range and bin count are paid uniformly before delta. -/
theorem exists_paid_common_ratio_bin_w97 (hdim : Module.finrank Real E = 3)
    (eReserve Ccard : Real) (heReserve : 0 < eReserve) (hCcard : 1 <= Ccard) :
    ∃ (Cratio Cbin : NNReal) (delta0 : NNReal),
      1 <= Cratio ∧ 1 <= Cbin ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
        {delta rho : NNReal}, 0 < delta -> delta < delta0 -> delta <= rho -> rho <= 1 ->
      ∀ (F : ShadedBody.FactorFamily E iota pi)
        (T : iota -> ShadedTube delta E) (Trho : pi -> Tube rho E)
        (G : ShadedBody.ShadedFactorFamily E iota pi)
        (raw : ActualRawRhoStatisticsW97 F T Trho G),
        (∀ i ∈ F.innerSet, F.innerBody i = (T i).toShadedBody) ->
        (delta : ENNReal) ^ eReserve <= fullness' F.innerSet F.innerBody ->
        (F.innerSet.card : Real) <= Ccard * (delta : Real) ^ (-6 : Real) ->
        let mass := fun Q => ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade
        let Sraw := ∑ Q ∈ G.outerSet, mass Q
        let heavy := G.outerSet.filter (fun Q => Sraw / (2 * (G.outerSet.card : ENNReal)) <= mass Q)
        ∃ (H : Finset pi) (c : NNReal) (J : Nat),
          H.Nonempty ∧ H ⊆ heavy ∧ 0 < c ∧ 1 <= J ∧
          (J : Real) <= (Cbin : Real) * (2 + Real.log (1 / (delta : Real))) ∧
          (1 / 2 : ENNReal) * Sraw <= ∑ Q ∈ heavy, mass Q ∧
          (∀ Q ∈ heavy, Sraw / (2 * (G.outerSet.card : ENNReal)) <= mass Q ∧
            (F.innerSet.card : ENNReal)⁻¹ <= volume (G.outerBody Q).shade / mass Q ∧
            volume (G.outerBody Q).shade / mass Q <=
              (Cratio : ENNReal) * (delta : ENNReal) ^ (-eReserve - 3)) ∧
          (∀ Q ∈ H, (c : ENNReal) * mass Q <= volume (G.outerBody Q).shade ∧
            volume (G.outerBody Q).shade < 2 * (c : ENNReal) * mass Q) ∧
          (2 * (J : ENNReal))⁻¹ * Sraw <= ∑ Q ∈ H, mass Q := by
  obtain ⟨Ce, hCe⟩ := shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox 3
    (1 / 7 : Real) (by norm_num)
  let CL : NNReal := max 1 Ce * Ccard.toNNReal ^ (1 / 7 : Real)
  let Cratio : NNReal := max 1 (2 * CL * Tube.volume_le.C 3 / Tube.le_volume.c 3)
  let Cbin : NNReal := max 1
    (2 + |Real.log ((Cratio : Real) * Ccard)| / Real.log 2 +
      (eReserve + 9) / Real.log 2).toNNReal
  refine ⟨Cratio, Cbin, 1 / 2, le_max_left _ _, le_max_left _ _, by norm_num, by norm_num, ?_⟩
  intro iota pi _ _ delta rho hdelta hdsmall hdrho hrho F T Trho G raw hinner hfull hcard
  let mass : pi -> ENNReal := fun Q => ∑ i ∈ G.fiber Q, volume (G.innerBody i).shade
  let Sraw : ENNReal := ∑ Q ∈ G.outerSet, mass Q
  let heavy := G.outerSet.filter (fun Q => Sraw / (2 * (G.outerSet.card : ENNReal)) <= mass Q)
  let L : NNReal := shadingMultiplicityEstimateForRhoTubesDilate.C 3 F.innerSet.card delta 1
  have hd1 : delta <= 1 := hdsmall.le.trans (by norm_num)
  have hdR : (0 : Real) < delta := by exact_mod_cast hdelta
  have hdR1 : (delta : Real) < 1 := by exact_mod_cast hdsmall.trans (by norm_num : (1 / 2 : NNReal) < 1)
  have hmassFinite : ∀ Q, mass Q ≠ ⊤ := by
    intro Q
    exact ENNReal.sum_ne_top.mpr (fun i hi =>
      ne_top_of_le_ne_top (G.innerBody i).isCompact.measure_ne_top
        (measure_mono (G.innerBody i).shade_subset))
  have hSfinite : Sraw ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun Q hQ => hmassFinite Q)
  obtain ⟨Q0, hQ0⟩ := raw.outer_nonempty
  have hSpos : 0 < Sraw := (raw.fibre_mass_pos Q0 hQ0).trans_le
    (Finset.single_le_sum (f := mass) (fun _ _ => zero_le) hQ0)
  have hGsub : G.innerSet ⊆ F.innerSet := by rw [raw.inner_eq]; exact Finset.filter_subset _ _
  have hGcard : G.outerSet.card <= F.innerSet.card := by
    rw [← raw.inner_image]
    exact (Finset.card_image_le).trans (Finset.card_le_card hGsub)
  have hNpos : 0 < F.innerSet.card := raw.outer_nonempty.card_pos.trans_le hGcard
  have hNnz : (F.innerSet.card : ENNReal) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hMpos : (0 : ENNReal) < G.outerSet.card := by exact_mod_cast raw.outer_nonempty.card_pos
  have hMfinite : (G.outerSet.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsumG : Sraw = ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    calc
      _ = ∑ Q ∈ G.outerSet, ∑ i ∈ G.innerSet.filter (fun i => G.parent i = Q),
          volume (G.innerBody i).shade := by
        apply Finset.sum_congr rfl
        intro Q hQ
        dsimp only [mass]
        apply Finset.sum_congr
        · ext i
          simp only [ShadedFactorFamily.fiber, Finset.mem_filter]
        · intro i hi
          rfl
      _ = _ := Finset.sum_fiberwise_of_maps_to G.parent_mem
        (fun i => volume (G.innerBody i).shade)
  have hhalf : (1 / 2 : ENNReal) * Sraw <= ∑ Q ∈ heavy, mass Q := by
    let light := G.outerSet.filter (fun Q => ¬Sraw / (2 * (G.outerSet.card : ENNReal)) <= mass Q)
    have hlight : (∑ Q ∈ light, mass Q) <= (1 / 2 : ENNReal) * Sraw := by
      calc
        _ <= ∑ Q ∈ light, Sraw / (2 * (G.outerSet.card : ENNReal)) :=
          Finset.sum_le_sum (fun Q hQ => (lt_of_not_ge (Finset.mem_filter.mp hQ).2).le)
        _ = (light.card : ENNReal) * (Sraw / (2 * (G.outerSet.card : ENNReal))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= (G.outerSet.card : ENNReal) * (Sraw / (2 * (G.outerSet.card : ENNReal))) := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = _ := by
          simp only [div_eq_mul_inv]
          rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          calc
            _ = (2 : ENNReal)⁻¹ * Sraw *
                ((G.outerSet.card : ENNReal) * (G.outerSet.card : ENNReal)⁻¹) := by ring
            _ = _ := by rw [ENNReal.mul_inv_cancel hMpos.ne' hMfinite]; simp
    have hsplit : Sraw = (∑ Q ∈ heavy, mass Q) + ∑ Q ∈ light, mass Q := by
      exact (Finset.sum_filter_add_sum_filter_not G.outerSet
        (fun Q => Sraw / (2 * (G.outerSet.card : ENNReal)) <= mass Q) mass).symm
    apply ENNReal.le_of_add_le_add_right
      (show (1 / 2 : ENNReal) * Sraw ≠ ⊤ from ENNReal.mul_ne_top (by norm_num) hSfinite)
    calc
      _ = Sraw := by rw [← add_mul]; simp only [one_div, ENNReal.inv_two_add_inv_two, one_mul]
      _ = _ := hsplit
      _ <= _ := add_le_add le_rfl hlight
  have hheavyPos : 0 < ∑ Q ∈ heavy, mass Q :=
    (ENNReal.mul_pos (by norm_num) hSpos.ne').trans_le hhalf
  have hheavy : heavy.Nonempty := by
    obtain ⟨Q, hQ, _⟩ := Finset.sum_pos_iff.mp hheavyPos
    exact ⟨Q, hQ⟩
  have hratioLow : ∀ Q ∈ G.outerSet,
      (F.innerSet.card : ENNReal)⁻¹ <= volume (G.outerBody Q).shade / mass Q := by
    intro Q hQ
    have hm : mass Q <= (F.innerSet.card : ENNReal) * volume (G.outerBody Q).shade := by
      calc
        _ <= ∑ i ∈ G.fiber Q, volume (G.outerBody Q).shade := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ∈ G.innerSet ∧ G.parent i = Q := by
            simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
          exact measure_mono (by simpa only [hi'.2] using G.shade_subset_parent i hi'.1)
        _ = ((G.fiber Q).card : ENNReal) * volume (G.outerBody Q).shade := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= _ := by
          apply mul_le_mul' _ le_rfl
          have hsub : G.fiber Q ⊆ F.innerSet := by
            intro i hi
            have hi' : i ∈ G.innerSet ∧ G.parent i = Q := by
              simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
            exact hGsub hi'.1
          exact_mod_cast Finset.card_le_card hsub
    apply (ENNReal.le_div_iff_mul_le (Or.inl (raw.fibre_mass_pos Q hQ).ne')
      (Or.inl (hmassFinite Q))).mpr
    exact (ENNReal.inv_mul_le_iff hNnz (ENNReal.natCast_ne_top _)).mpr hm
  have hLupper : (L : Real) <= (CL : Real) * (delta : Real) ^ (-1 : Real) := by
    have hc := hCe F.innerSet.card hNpos delta hdelta hd1 1 le_rfl
    have hcR : (L : Real) <= (Ce : Real) * (delta : Real) ^ (-(1 / 7 : Real)) *
        (F.innerSet.card : Real) ^ (1 / 7 : Real) := by
      simpa only [L, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_one, NNReal.coe_rpow,
        NNReal.coe_natCast, one_pow, mul_one] using NNReal.coe_le_coe.mpr hc
    calc
      _ <= (Ce : Real) * (delta : Real) ^ (-(1 / 7 : Real)) *
          (Ccard * (delta : Real) ^ (-6 : Real)) ^ (1 / 7 : Real) :=
        hcR.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by norm_num)) (by positivity))
      _ = (Ce : Real) * Ccard ^ (1 / 7 : Real) * (delta : Real) ^ (-1 : Real) := by
        rw [Real.mul_rpow (zero_lt_one.trans_le hCcard).le (Real.rpow_pos_of_pos hdR _).le,
          ← Real.rpow_mul hdR.le]
        calc
          _ = (Ce : Real) * Ccard ^ (1 / 7 : Real) *
              ((delta : Real) ^ (-(1 / 7 : Real)) * (delta : Real) ^ ((-6 : Real) * (1 / 7 : Real))) := by ring
          _ = _ := by rw [← Real.rpow_add hdR]; norm_num
      _ <= _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hdR _).le
        dsimp only [CL]
        rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal _ (zero_lt_one.trans_le hCcard).le]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right 1 Ce) (by positivity)
  have hratioUpper : ∀ Q ∈ heavy, volume (G.outerBody Q).shade / mass Q <=
      (Cratio : ENNReal) * (delta : ENNReal) ^ (-eReserve - 3) := by
    intro Q hQ
    have hQG := (Finset.mem_filter.mp hQ).1
    have hmq : 0 < (mass Q).toReal := ENNReal.toReal_pos (raw.fibre_mass_pos Q hQG).ne' (hmassFinite Q)
    have hL : (0 : Real) < L := by
      exact_mod_cast zero_lt_one.trans_le
        (shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 F.innerSet.card delta 1)
    have hN : (0 : Real) < F.innerSet.card := by exact_mod_cast hNpos
    have hM : (0 : Real) < G.outerSet.card := by exact_mod_cast raw.outer_nonempty.card_pos
    have hc0 : (0 : Real) < Tube.le_volume.c 3 := NNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)
    let MF : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).shade
    let VF : ENNReal := ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier
    have hMFtop : MF ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i hi =>
      ne_top_of_le_ne_top (F.innerBody i).isCompact.measure_ne_top
        (measure_mono (F.innerBody i).shade_subset))
    have hVFtop : VF ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i hi => (F.innerBody i).isCompact.measure_ne_top)
    have hvolLower : (F.innerSet.card : ENNReal) * (Tube.le_volume.c 3 : ENNReal) *
        (delta : ENNReal) ^ (2 : Nat) <= VF := by
      calc
        _ = ∑ i ∈ F.innerSet, (Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (2 : Nat) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
        _ <= _ := Finset.sum_le_sum (fun i hi => by
          simpa only [hinner i hi, hdim, Nat.reduceSub] using Tube.le_volume (T i).toTube)
    have hvolLowerR : (F.innerSet.card : Real) * (Tube.le_volume.c 3 : Real) *
        (delta : Real) ^ (2 : Nat) <= VF.toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal,
        ENNReal.toReal_pow] using ENNReal.toReal_mono hVFtop hvolLower
    have hVFpos : 0 < VF.toReal := (by positivity : (0 : Real) <
      (F.innerSet.card : Real) * (Tube.le_volume.c 3 : Real) * (delta : Real) ^ (2 : Nat)).trans_le hvolLowerR
    have hfullR : (delta : Real) ^ eReserve * VF.toReal <= MF.toReal := by
      have hh := ENNReal.toReal_mono
        (show fullness' F.innerSet F.innerBody ≠ ⊤ from ne_top_of_le_ne_top (by simp) (fullness'_le_one _ _)) hfull
      have hh' : (delta : Real) ^ eReserve <= MF.toReal / VF.toReal := by
        simpa only [fullness', ← ENNReal.toReal_rpow, ENNReal.coe_toReal, ENNReal.toReal_div, MF, VF] using hh
      exact (le_div_iff₀ hVFpos).mp hh'
    have hrefR : (L : Real)⁻¹ * MF.toReal <= Sraw.toReal := by
      have hh := ENNReal.toReal_mono
        (show (∑ i ∈ G.innerSet, volume (G.innerBody i).shade) ≠ ⊤ from hsumG ▸ hSfinite)
        raw.raw_refinement.2
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_inv, hdim, L, MF, ← hsumG] using hh
    have hmassLower : (delta : Real) ^ eReserve *
        ((F.innerSet.card : Real) * (Tube.le_volume.c 3 : Real) * (delta : Real) ^ (2 : Nat)) <=
        (L : Real) * Sraw.toReal :=
      ((mul_le_mul_of_nonneg_left hvolLowerR (Real.rpow_pos_of_pos hdR _).le).trans hfullR).trans
        ((inv_mul_le_iff₀ hL).mp hrefR)
    have hthreshold : Sraw.toReal <= 2 * (G.outerSet.card : Real) * (mass Q).toReal := by
      have hh := ENNReal.toReal_mono (hmassFinite Q) (Finset.mem_filter.mp hQ).2
      have hh' : Sraw.toReal / (2 * (G.outerSet.card : Real)) <= (mass Q).toReal := by
        simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
          ENNReal.toReal_natCast] using hh
      simpa only [mul_comm] using (div_le_iff₀ (by positivity)).mp hh'
    have hthreshold' : Sraw.toReal <= 2 * (F.innerSet.card : Real) * (mass Q).toReal :=
      hthreshold.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hGcard) (by norm_num)) hmq.le)
    have hcancel : (Tube.le_volume.c 3 : Real) *
        ((delta : Real) ^ eReserve * (delta : Real) ^ (2 : Nat)) <= 2 * (L : Real) * (mass Q).toReal := by
      apply (mul_le_mul_iff_right₀ hN).mp
      calc
        _ = (delta : Real) ^ eReserve * ((F.innerSet.card : Real) *
            (Tube.le_volume.c 3 : Real) * (delta : Real) ^ (2 : Nat)) := by ring
        _ <= _ := hmassLower
        _ <= (L : Real) * (2 * (F.innerSet.card : Real) * (mass Q).toReal) :=
          mul_le_mul_of_nonneg_left hthreshold' hL.le
        _ = _ := by ring
    have hfunded : (Tube.le_volume.c 3 : Real) * (delta : Real) ^ (eReserve + 3) <=
        2 * (CL : Real) * (mass Q).toReal := by
      calc
        _ = ((Tube.le_volume.c 3 : Real) *
            ((delta : Real) ^ eReserve * (delta : Real) ^ (2 : Nat))) * (delta : Real) := by
          rw [show eReserve + 3 = eReserve + (2 : Nat) + 1 by norm_num; ring,
            Real.rpow_add hdR, Real.rpow_add hdR, Real.rpow_one, Real.rpow_natCast]
          ring
        _ <= (2 * (L : Real) * (mass Q).toReal) * (delta : Real) :=
          mul_le_mul_of_nonneg_right hcancel hdR.le
        _ <= (2 * ((CL : Real) * (delta : Real) ^ (-1 : Real)) * (mass Q).toReal) * (delta : Real) := by
          gcongr
        _ = _ := by rw [Real.rpow_neg_one]; field_simp
    have hshadeTop : volume (G.outerBody Q).shade ≠ ⊤ :=
      ne_top_of_le_ne_top (G.outerBody Q).isCompact.measure_ne_top
        (measure_mono (G.outerBody Q).shade_subset)
    have hshadeUpper : (volume (G.outerBody Q).shade).toReal <= (Tube.volume_le.C 3 : Real) := by
      have hb := congrArg (fun K : ConvexSpaceBody E => volume K.carrier) (raw.outer_body Q hQG)
      have hv := Tube.volume_le hrho (Trho Q)
      have hv' : volume (G.outerBody Q).shade <= (Tube.volume_le.C 3 : ENNReal) := by
        calc
          _ <= volume (G.outerBody Q).carrier := measure_mono (G.outerBody Q).shade_subset
          _ = volume (Trho Q).carrier := hb
          _ <= (Tube.volume_le.C 3 : ENNReal) * (rho : ENNReal) ^ (2 : Nat) := by
            simpa only [hdim, Nat.reduceSub] using hv
          _ <= _ := by
            simpa using mul_le_mul' (le_refl (Tube.volume_le.C 3 : ENNReal))
              (pow_le_one₀ zero_le (show (rho : ENNReal) <= 1 by exact_mod_cast hrho))
      exact ENNReal.toReal_mono ENNReal.coe_ne_top hv'
    have hcoefficient : 2 * (CL : Real) * (Tube.volume_le.C 3 : Real) / (Tube.le_volume.c 3 : Real) <=
        (Cratio : Real) := by exact_mod_cast le_max_right 1 (2 * CL * Tube.volume_le.C 3 / Tube.le_volume.c 3)
    have hratioR : (volume (G.outerBody Q).shade).toReal / (mass Q).toReal <=
        (Cratio : Real) * (delta : Real) ^ (-eReserve - 3) := by
      apply (div_le_iff₀ hmq).mpr
      have hdp : 0 < (delta : Real) ^ (eReserve + 3) := Real.rpow_pos_of_pos hdR _
      have hbound : (Tube.volume_le.C 3 : Real) <=
          (2 * (CL : Real) * (Tube.volume_le.C 3 : Real) / (Tube.le_volume.c 3 : Real)) *
            ((delta : Real) ^ (eReserve + 3))⁻¹ * (mass Q).toReal := by
        have hh := mul_le_mul_of_nonneg_left hfunded
          (div_nonneg (Tube.volume_le.C 3).coe_nonneg (mul_pos hc0 hdp).le)
        field_simp [hc0.ne', hdp.ne'] at hh ⊢
        nlinarith
      calc
        _ <= _ := hshadeUpper.trans hbound
        _ <= (Cratio : Real) * ((delta : Real) ^ (eReserve + 3))⁻¹ * (mass Q).toReal := by
          gcongr
        _ = _ := by rw [← Real.rpow_neg hdR.le]; congr 2; ring
    apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hshadeTop (raw.fibre_mass_pos Q hQG).ne')
      (by finiteness)).mp
    simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.coe_toReal] using hratioR
  let a : Real := (F.innerSet.card : Real)⁻¹
  let b : Real := (Cratio : Real) * (delta : Real) ^ (-eReserve - 3)
  let ratio : pi -> Real := fun Q => (volume (G.outerBody Q).shade / mass Q).toReal
  have ha : 0 < a := by dsimp [a]; positivity
  have hbounds : ∀ Q ∈ heavy, a <= ratio Q ∧ ratio Q <= b := by
    intro Q hQ
    have htop : volume (G.outerBody Q).shade / mass Q ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · exact ne_top_of_le_ne_top (G.outerBody Q).isCompact.measure_ne_top
          (measure_mono (G.outerBody Q).shade_subset)
      · exact (raw.fibre_mass_pos Q (Finset.mem_filter.mp hQ).1).ne'
    constructor
    · have h := ENNReal.toReal_mono htop (hratioLow Q (Finset.mem_filter.mp hQ).1)
      simpa only [a, ratio, ENNReal.toReal_inv, ENNReal.toReal_natCast] using h
    · have h := ENNReal.toReal_mono
        (show (Cratio : ENNReal) * (delta : ENNReal) ^ (-eReserve - 3) ≠ ⊤ by finiteness)
        (hratioUpper Q hQ)
      simpa only [b, ratio, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal] using h
  have hab : a <= b := by obtain ⟨Q, hQ⟩ := hheavy; exact (hbounds Q hQ).1.trans (hbounds Q hQ).2
  let bin : pi -> Nat := fun Q => ⌊Real.logb 2 (ratio Q / a)⌋₊
  let J : Nat := ⌊Real.logb 2 (b / a)⌋₊ + 1
  have hJ : 1 <= J := Nat.le_add_left 1 _
  have hbin : ∀ Q ∈ heavy, bin Q ∈ Finset.range J := by
    intro Q hQ
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    exact (Real.logb_le_logb (by norm_num) (div_pos (ha.trans_le (hbounds Q hQ).1) ha)
      (div_pos (ha.trans_le hab) ha)).mpr (div_le_div_of_nonneg_right (hbounds Q hQ).2 ha.le)
  let weights : Nat -> ENNReal := fun k => ∑ Q ∈ heavy.filter (fun Q => bin Q = k), mass Q
  obtain ⟨k, hk, hkweight⟩ := ENNReal.exists_card_inv_mul_sum_le (T := Finset.range J)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt hJ))) weights
  let H := heavy.filter (fun Q => bin Q = k)
  have hsumBins : (∑ j ∈ Finset.range J, weights j) = ∑ Q ∈ heavy, mass Q :=
    Finset.sum_fiberwise_of_maps_to hbin mass
  have hretained : (2 * (J : ENNReal))⁻¹ * Sraw <= ∑ Q ∈ H, mass Q := by
    have hm : (J : ENNReal)⁻¹ * (∑ Q ∈ heavy, mass Q) <= ∑ Q ∈ H, mass Q := by
      simpa only [Finset.card_range, hsumBins, weights, H] using hkweight
    calc
      _ = (J : ENNReal)⁻¹ * ((1 / 2 : ENNReal) * Sraw) := by
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        simp only [one_div]
        ring
      _ <= _ := (mul_le_mul' le_rfl hhalf).trans hm
  have hH : H.Nonempty := by
    have hp : 0 < ∑ Q ∈ H, mass Q :=
      (ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (by finiteness)) hSpos.ne').trans_le hretained
    obtain ⟨Q, hQ, _⟩ := Finset.sum_pos_iff.mp hp
    exact ⟨Q, hQ⟩
  let c : NNReal := ⟨a * (2 : Real) ^ k, by positivity⟩
  have hc : 0 < c := by change (0 : Real) < a * (2 : Real) ^ k; positivity
  have hband : ∀ Q ∈ H, (c : ENNReal) * mass Q <= volume (G.outerBody Q).shade ∧
      volume (G.outerBody Q).shade < 2 * (c : ENNReal) * mass Q := by
    intro Q hQ
    obtain ⟨hQh, hQk⟩ := Finset.mem_filter.mp hQ
    have hratioPos : 0 < ratio Q / a := div_pos (ha.trans_le (hbounds Q hQh).1) ha
    have hlogPos : 0 <= Real.logb 2 (ratio Q / a) :=
      Real.logb_nonneg (by norm_num) ((one_le_div ha).mpr (hbounds Q hQh).1)
    have hkfloor : ⌊Real.logb 2 (ratio Q / a)⌋₊ = k := hQk
    have hlowReal : (c : Real) <= ratio Q := by
      change a * (2 : Real) ^ k <= ratio Q
      have hp : (2 : Real) ^ (k : Real) <= ratio Q / a :=
        (Real.le_logb_iff_rpow_le (by norm_num) hratioPos).mp (by
          rw [← hkfloor]
          exact Nat.floor_le hlogPos)
      have hp' := (le_div_iff₀ ha).mp hp
      simpa only [Real.rpow_natCast, mul_comm] using hp'
    have huppReal : ratio Q < 2 * (c : Real) := by
      change ratio Q < 2 * (a * (2 : Real) ^ k)
      have hp : ratio Q / a < (2 : Real) ^ ((k + 1 : Nat) : Real) :=
        (Real.logb_lt_iff_lt_rpow (by norm_num) hratioPos).mp (by
          rw [← hkfloor, Nat.cast_add, Nat.cast_one]
          exact Nat.lt_floor_add_one _)
      have hp' := (div_lt_iff₀ ha).mp hp
      simpa only [Real.rpow_natCast, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hp'
    have hmpos := (raw.fibre_mass_pos Q (Finset.mem_filter.mp hQh).1).ne'
    have hratioTop : volume (G.outerBody Q).shade / mass Q ≠ ⊤ :=
      ENNReal.div_ne_top
        (ne_top_of_le_ne_top (G.outerBody Q).isCompact.measure_ne_top
          (measure_mono (G.outerBody Q).shade_subset)) hmpos
    constructor
    · apply (ENNReal.le_div_iff_mul_le (Or.inl hmpos) (Or.inl (hmassFinite Q))).mp
      exact (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hratioTop).mp hlowReal
    · apply (ENNReal.div_lt_iff (Or.inl hmpos) (Or.inl (hmassFinite Q))).mp
      exact (ENNReal.toReal_lt_toReal hratioTop (by finiteness)).mp (by
        simpa only [ratio, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal] using huppReal)
  have hJpaid : (J : Real) <= (Cbin : Real) * (2 + Real.log (1 / (delta : Real))) := by
    let ell := Real.log (1 / (delta : Real))
    have hell : 0 <= ell := Real.log_nonneg ((one_le_div hdR).mpr hdR1.le)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCr : (0 : Real) < Cratio := by exact_mod_cast zero_lt_one.trans_le (le_max_left 1 _)
    have hCard : 0 < Ccard := zero_lt_one.trans_le hCcard
    have hratio : b / a <= ((Cratio : Real) * Ccard) * (delta : Real) ^ (-eReserve - 9) := by
      calc
        b / a = (Cratio : Real) * (delta : Real) ^ (-eReserve - 3) * (F.innerSet.card : Real) := by
          simp only [a, b, div_eq_mul_inv, inv_inv]
        _ <= (Cratio : Real) * (delta : Real) ^ (-eReserve - 3) *
            (Ccard * (delta : Real) ^ (-6 : Real)) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
        _ = _ := by
          rw [mul_mul_mul_comm, ← Real.rpow_add hdR]
          congr 2
          ring
    have hJlog : (J : Real) <= 1 + Real.logb 2 (b / a) := by
      dsimp only [J]
      rw [Nat.cast_add, Nat.cast_one, add_comm]
      exact add_le_add le_rfl (Nat.floor_le
        (Real.logb_nonneg (by norm_num : (1 : Real) < 2) ((one_le_div ha).mpr hab)))
    have hlog : Real.logb 2 (b / a) <=
        Real.log ((Cratio : Real) * Ccard) / Real.log 2 + (eReserve + 9) / Real.log 2 * ell := by
      have hmono := (Real.logb_le_logb (by norm_num : (1 : Real) < 2) (div_pos (ha.trans_le hab) ha)
        (by positivity : 0 < ((Cratio : Real) * Ccard) * (delta : Real) ^ (-eReserve - 9))).mpr hratio
      refine hmono.trans_eq ?_
      rw [Real.logb, Real.log_mul (mul_pos hCr hCard).ne' (Real.rpow_pos_of_pos hdR _).ne',
        Real.log_rpow hdR]
      dsimp [ell]
      rw [one_div, Real.log_inv]
      ring
    let A : Real := |Real.log ((Cratio : Real) * Ccard)| / Real.log 2
    let B : Real := (eReserve + 9) / Real.log 2
    have hA : 0 <= A := div_nonneg (abs_nonneg _) hlog2.le
    have hB : 0 <= B := div_nonneg (by linarith) hlog2.le
    have hcoeff : 2 + A + B <= (Cbin : Real) := by
      have hnonneg : 0 <= 2 + A + B := by positivity
      have hh := NNReal.coe_le_coe.mpr (le_max_right 1 (2 + A + B).toNNReal)
      simpa only [Real.coe_toNNReal _ hnonneg, A, B, Cbin] using hh
    have hpaid : (J : Real) <= 1 + A + B * ell := by
      have habs := div_le_div_of_nonneg_right
        (le_abs_self (Real.log ((Cratio : Real) * Ccard))) hlog2.le
      dsimp only [A, B]
      linarith
    change (J : Real) <= (Cbin : Real) * (2 + ell)
    nlinarith [mul_nonneg hA hell, mul_nonneg hB hell,
      mul_nonneg (sub_nonneg.mpr hcoeff) hell]
  refine ⟨H, c, J, hH, Finset.filter_subset _ _, hc, hJ, hJpaid, hhalf, ?_, hband, hretained⟩
  intro Q hQ
  exact ⟨(Finset.mem_filter.mp hQ).2, hratioLow Q (Finset.mem_filter.mp hQ).1, hratioUpper Q hQ⟩

/-- B5: exact Lebesgue measurable cuts, including target volume zero. -/
theorem exists_volume_cut_w97 (S : Set E) (hS : MeasurableSet S)
    (hfinite : volume S < ⊤) (t : ENNReal) (ht : t <= volume S) :
    ∃ R : Set E, R ⊆ S ∧ MeasurableSet R ∧ volume R = t := by
  by_cases ht0 : t = 0
  · exact ⟨∅, Set.empty_subset S, MeasurableSet.empty, by simp [ht0]⟩
  by_cases htS : t = volume S
  · exact ⟨S, Set.Subset.refl S, hS, htS.symm⟩
  have httop : t ≠ ⊤ := (ht.trans_lt hfinite).ne
  have htlt : t < volume S := lt_of_le_of_ne ht htS
  let mu : Measure E := volume.restrict S
  letI : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr hfinite.ne
  let nu : Measure Real := Measure.map (fun x : E => ‖x‖) mu
  letI : IsFiniteMeasure nu := inferInstance
  letI : NoAtoms nu := by
    constructor
    intro r
    change Measure.map (fun x : E => ‖x‖) mu {r} = 0
    rw [Measure.map_apply measurable_norm (measurableSet_singleton r)]
    have hpre : (fun x : E => ‖x‖) ⁻¹' {r} = Metric.sphere (0 : E) r := by
      ext x
      simp [Metric.mem_sphere, dist_zero_right]
    rw [hpre]
    apply le_antisymm _ bot_le
    exact (Measure.restrict_le_self (Metric.sphere (0 : E) r)).trans
      (Measure.addHaar_sphere volume (0 : E) r).le
  have hnu : nu Set.univ = volume S := by
    dsimp [nu, mu]
    rw [Measure.map_apply measurable_norm MeasurableSet.univ]
    simp
  let f : Real -> Real := fun r => (nu (Set.Iic r)).toReal
  have hf0 : f 0 = 0 := by
    have hpre : (fun x : E => ‖x‖) ⁻¹' Set.Iic 0 = {0} := by
      ext x
      simp
    dsimp [f, nu]
    rw [Measure.map_apply measurable_norm measurableSet_Iic, hpre, measure_singleton]
    rfl
  have hcont : ∀ b : Real, ContinuousOn f (Set.Iic b) := by
    intro b
    have h := ((integrable_const (1 : Real) : Integrable (fun _ : Real => (1 : Real)) nu).integrableOn
      (s := Set.Iic b)).continuousOn_Iic_primitive_Iic
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
      smul_eq_mul, mul_one] using h
  have htR : t.toReal < (volume S).toReal :=
    (ENNReal.toReal_lt_toReal httop hfinite.ne).mpr htlt
  have hlim : Filter.Tendsto f Filter.atTop (nhds (volume S).toReal) := by
    have h := (ENNReal.continuousAt_toReal (hnu ▸ hfinite.ne)).tendsto.comp
      (tendsto_measure_Iic_atTop nu)
    simpa only [hnu, Function.comp_def, f] using h
  have hevent : ∀ᶠ b : Real in Filter.atTop, t.toReal < f b :=
    hlim.eventually (eventually_gt_nhds htR)
  obtain ⟨b, hb0, hbt⟩ := (Filter.eventually_ge_atTop (0 : Real) |>.and hevent).exists
  have hbetween : t.toReal ∈ Set.Icc (f 0) (f b) :=
    ⟨by simpa only [hf0] using ENNReal.toReal_nonneg, hbt.le⟩
  obtain ⟨r, hr, hrt⟩ := intermediate_value_Icc hb0
    ((hcont b).mono Set.Icc_subset_Iic_self) hbetween
  refine ⟨((fun x : E => ‖x‖) ⁻¹' Set.Iic r) ∩ S, Set.inter_subset_right,
    (measurable_norm measurableSet_Iic).inter hS, ?_⟩
  have hmeasure : volume (((fun x : E => ‖x‖) ⁻¹' Set.Iic r) ∩ S) = nu (Set.Iic r) := by
    dsimp [nu, mu]
    rw [Measure.map_apply measurable_norm measurableSet_Iic,
      Measure.restrict_apply (measurable_norm measurableSet_Iic)]
  rw [hmeasure]
  exact (ENNReal.toReal_eq_toReal_iff _ _).mp hrt |>.resolve_right (by
    rintro (⟨_, htop⟩ | ⟨htop, _⟩)
    · exact httop htop
    · exact measure_ne_top nu _ htop)

/-- B6: one commonMass controls the SAME exact fine cut for every second
parent. Zero-shaded children remain as labels to preserve the full image. -/
theorem exists_same_proportional_fine_cut_w97
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {delta rho : NNReal} (F : Finset iota) (Y : iota -> ShadedTube delta E)
    (J F2 : Finset pi) (Z Z2 : pi -> ShadedTube rho E) (parent : iota -> pi)
    (hF2 : F2.Nonempty) (hF2J : F2 ⊆ J) (himage : F.image parent = J)
    (c : NNReal) (hc : 0 < c)
    (hinduced : ∀ Q ∈ J, volume (Z Q).shade = (c : ENNReal) *
      ∑ i ∈ completeFibreW94 F parent Q, volume (Y i).shade)
    (hsecond : ∀ Q ∈ F2, (Z2 Q).toTube = (Z Q).toTube ∧ (Z2 Q).shade ⊆ (Z Q).shade) :
    ∃ (Fdagger : Finset iota) (Ydagger : iota -> ShadedTube delta E),
      Fdagger = F.filter (fun i => parent i ∈ F2) ∧ Fdagger.Nonempty ∧ Fdagger ⊆ F ∧
      Fdagger.image parent = F2 ∧
      (∀ i ∈ Fdagger, (Ydagger i).toTube = (Y i).toTube ∧ (Ydagger i).shade ⊆ (Y i).shade) ∧
      (∀ Q ∈ F2, completeFibreW94 Fdagger parent Q = completeFibreW94 F parent Q) ∧
      (∀ Q ∈ F2, (∑ i ∈ completeFibreW94 Fdagger parent Q, volume (Ydagger i).shade) =
        (c : ENNReal)⁻¹ * volume (Z2 Q).shade) ∧
      (∀ Q ∈ F2, ∀ i ∈ completeFibreW94 Fdagger parent Q,
        volume (Ydagger i).shade =
          ((c : ENNReal)⁻¹ * volume (Z2 Q).shade /
            (∑ j ∈ completeFibreW94 F parent Q, volume (Y j).shade)) * volume (Y i).shade) := by
  let mass : pi -> ENNReal := fun Q =>
    ∑ i ∈ completeFibreW94 F parent Q, volume (Y i).shade
  let target : pi -> ENNReal := fun Q => (c : ENNReal)⁻¹ * volume (Z2 Q).shade
  have hcE : (0 : ENNReal) < c := by exact_mod_cast hc
  have hmassTop : ∀ Q, mass Q ≠ ⊤ := by
    intro Q
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    exact ne_top_of_le_ne_top (Y i).toConvexSpaceBody.isCompact.measure_ne_top
      (measure_mono (Y i).shade_subset)
  have htarget : ∀ Q ∈ F2, target Q <= mass Q := by
    intro Q hQ
    apply (ENNReal.inv_mul_le_iff hcE.ne' ENNReal.coe_ne_top).mpr
    exact (measure_mono (hsecond Q hQ).2).trans_eq (hinduced Q (hF2J hQ))
  let alpha : pi -> ENNReal := fun Q => if Q ∈ F2 then target Q / mass Q else 0
  have halpha : ∀ Q, alpha Q <= 1 := by
    intro Q
    by_cases hQ : Q ∈ F2
    · dsimp [alpha]
      rw [if_pos hQ]
      apply ENNReal.div_le_of_le_mul
      simpa only [one_mul] using htarget Q hQ
    · simp [alpha, hQ]
  have hcut : ∀ i : iota, ∃ R : Set E,
      R ⊆ (Y i).shade ∧ MeasurableSet R ∧ volume R = alpha (parent i) * volume (Y i).shade := by
    intro i
    apply exists_volume_cut_w97 (Y i).shade (Y i).measurableSet_shade
      ((measure_mono (Y i).shade_subset).trans_lt (Y i).toConvexSpaceBody.isCompact.measure_lt_top)
    simpa only [one_mul] using mul_le_mul' (halpha (parent i))
      (le_rfl : volume (Y i).shade <= volume (Y i).shade)
  choose R hR hRmeas hRvol using hcut
  let Ydagger : iota -> ShadedTube delta E := fun i =>
    { Y i with
      shade := R i
      measurableSet_shade := hRmeas i
      shade_subset := (hR i).trans (Y i).shade_subset }
  let Fdagger := F.filter (fun i => parent i ∈ F2)
  have hdagImage : Fdagger.image parent = F2 := by
    ext Q
    simp only [Fdagger, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨hiF, hiF2⟩, hiQ⟩
      exact hiQ ▸ hiF2
    · intro hQ
      have hQimage : Q ∈ F.image parent := himage.symm ▸ hF2J hQ
      obtain ⟨i, hiF, hiQ⟩ := Finset.mem_image.mp hQimage
      exact ⟨i, ⟨hiF, hiQ.symm ▸ hQ⟩, hiQ⟩
  have hdagNonempty : Fdagger.Nonempty :=
    Finset.image_nonempty.mp (hdagImage.symm ▸ hF2)
  have hfibre : ∀ Q ∈ F2, completeFibreW94 Fdagger parent Q = completeFibreW94 F parent Q := by
    intro Q hQ
    ext i
    simp only [completeFibreW94, Fdagger, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hiF, _⟩, hiQ⟩
      exact ⟨hiF, hiQ⟩
    · rintro ⟨hiF, hiQ⟩
      exact ⟨⟨hiF, hiQ.symm ▸ hQ⟩, hiQ⟩
  have hvol : ∀ Q ∈ F2, ∀ i ∈ completeFibreW94 Fdagger parent Q,
      volume (Ydagger i).shade = (target Q / mass Q) * volume (Y i).shade := by
    intro Q hQ i hi
    have hiQ : parent i = Q := (Finset.mem_filter.mp hi).2
    change volume (R i) = _
    rw [hRvol, hiQ]
    simp only [alpha, if_pos hQ]
  refine ⟨Fdagger, Ydagger, rfl, hdagNonempty, Finset.filter_subset _ _, hdagImage,
    (fun i hi => ⟨rfl, hR i⟩), hfibre, ?_, hvol⟩
  intro Q hQ
  calc
    _ = ∑ i ∈ completeFibreW94 Fdagger parent Q,
        (target Q / mass Q) * volume (Y i).shade := Finset.sum_congr rfl (hvol Q hQ)
    _ = (target Q / mass Q) * mass Q := by rw [hfibre Q hQ, ← Finset.mul_sum]
    _ = target Q := by
      by_cases hm : mass Q = 0
      · have ht : target Q = 0 := le_antisymm ((htarget Q hQ).trans_eq hm) bot_le
        simp [hm, ht]
      · exact ENNReal.div_mul_cancel hm (hmassTop Q)

/-- B7 chooses the same positive final-cut label for both funding thresholds. -/
theorem exists_joint_fullness_and_cut_label_w97
    {pi : Type uP} (Q : Finset pi) (h m t : pi -> ENNReal) (S r : ENNReal)
    (hS : 0 < S) (hSfinite : S < ⊤) (hr : 0 < r) (hrone : r <= 1)
    (hhfinite : ∀ q ∈ Q, h q < ⊤)
    (hmh : ∀ q ∈ Q, m q <= h q) (htm : ∀ q ∈ Q, t q <= m q)
    (hH : 0 < ∑ q ∈ Q, h q) (hSH : S <= ∑ q ∈ Q, h q)
    (hmS : (∑ q ∈ Q, m q) <= S) (hretained : r * S <= ∑ q ∈ Q, t q) :
    ∃ q ∈ Q, 0 < t q ∧
      (r / 4) * (S / ∑ j ∈ Q, h j) * h q <= m q ∧ (r / 4) * m q <= t q := by
  let rho := r / 4
  let H := ∑ q ∈ Q, h q
  have hHfinite : H < ⊤ := by
    exact (ENNReal.sum_ne_top.mpr (fun q hq => (hhfinite q hq).ne)).lt_top
  have hrfinite : r ≠ ⊤ := (hrone.trans_lt (by simp)).ne
  by_contra hn
  have hpoint : ∀ q ∈ Q, t q <= rho * (S / H) * h q + rho * m q := by
    intro q hq
    by_cases ht : 0 < t q
    · by_cases hm : rho * (S / H) * h q <= m q
      · have hbad : ¬rho * m q <= t q := fun hgood => hn ⟨q, hq, ht, hm, hgood⟩
        exact (not_le.mp hbad).le.trans (le_add_left le_rfl)
      · exact ((htm q hq).trans (not_le.mp hm).le).trans (le_add_right le_rfl)
    · exact (not_lt.mp ht).trans bot_le
  have hsum : (∑ q ∈ Q, t q) <= rho * S + rho * S := by
    calc
      (∑ q ∈ Q, t q) <= ∑ q ∈ Q, (rho * (S / H) * h q + rho * m q) := Finset.sum_le_sum hpoint
      _ = rho * (S / H) * H + rho * (∑ q ∈ Q, m q) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ <= rho * (S / H) * H + rho * S := add_le_add_right (mul_le_mul' le_rfl hmS) _
      _ = rho * S + rho * S := by rw [mul_assoc, ENNReal.div_mul_cancel hH.ne' hHfinite.ne]
  have hcoeff : rho + rho < r := by
    have hrho : rho ≠ ⊤ := by dsimp [rho]; finiteness
    apply (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.mpr ⟨hrho, hrho⟩) hrfinite).mp
    rw [ENNReal.toReal_add hrho hrho]
    simp only [rho, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    have hrR : 0 < r.toReal := ENNReal.toReal_pos hr.ne' hrfinite
    linarith
  have hstrict : rho * S + rho * S < r * S := by
    rw [← add_mul]
    simpa only [mul_comm] using ENNReal.mul_lt_mul_right hS.ne' hSfinite.ne hcoeff
  exact (not_lt_of_ge (hretained.trans hsum)) hstrict

/-- B8 uses a fixed midpoint patch and translation, preserving unit cores;
it constructs a genuine second raw factorization and its translated-back shades. -/
theorem exists_bounded_ball_patch_second_factor_w97 :
    ∃ Kpatch : Nat, 1 <= Kpatch ∧
      ∀ {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
        {rho theta : NNReal}, 0 < rho -> rho <= 1 / 16 -> rho <= theta -> theta <= 1 ->
      ∀ (F : Finset iota) (Z : iota -> ShadedTube rho E)
        (J : Finset pi) (Ttheta : pi -> Tube theta E) (parent : iota -> pi)
        (m : iota -> ENNReal) (c : NNReal),
        0 < c -> (0 < ∑ i ∈ F, volume (Z i).shade) ->
        (∀ i ∈ F, volume (Z i).shade = (c : ENNReal) * m i) ->
        (∀ i ∈ F, (Z i).carrier ⊆ Metric.closedBall 0 2) -> F.image parent ⊆ J ->
        (∀ i ∈ F, (Z i).toConvexSpaceBody <= (Ttheta (parent i)).toConvexSpaceBody) ->
        ∃ (patch : Finset iota) (z : E) (FF : ShadedBody.FactorFamily E iota pi)
          (G : ShadedBody.ShadedFactorFamily E iota pi)
          (Yi : iota -> ShadedTube rho E) (Yo : pi -> ShadedTube theta E),
          patch.Nonempty ∧ patch ⊆ F ∧
          (∑ i ∈ F, volume (Z i).shade) <= (Kpatch : ENNReal) * ∑ i ∈ patch, volume (Z i).shade ∧
          (∑ i ∈ F, m i) <= (Kpatch : ENNReal) * ∑ i ∈ patch, m i ∧
          (∀ i ∈ patch, ‖(Z i).toTube.center - z‖ <= 1 / 4) ∧
          (∀ i ∈ patch, ((Z i).translate (-z)).carrier ⊆ Metric.closedBall 0 1) ∧
          FF.innerSet = patch ∧ FF.outerSet = patch.image parent ∧ FF.parent = parent ∧
          FF.innerBody = (fun i => ((Z i).translate (-z)).toShadedBody) ∧
          FF.outerBody = (fun Q => ((Ttheta Q).translate (-z)).toConvexSpaceBody) ∧
          Nonempty (ActualRawRhoStatisticsW97 FF (fun i => (Z i).translate (-z))
            (fun Q => (Ttheta Q).translate (-z)) G) ∧
          (∀ i ∈ G.innerSet, (Yi i).toTube = (Z i).toTube ∧
            (Yi i).toShadedBody = (G.innerBody i).translate z ∧ (Yi i).shade ⊆ (Z i).shade) ∧
          (∀ Q ∈ G.outerSet, (Yo Q).toTube = Ttheta Q ∧
            (Yo Q).toShadedBody = (G.outerBody Q).translate z) ∧
          (∀ Q ∈ G.outerSet, ShadedBody.multiplicity patch (fun i => (Z i).toShadedBody) <=
            (ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
              (Module.finrank Real E) patch.card rho 1 : ENNReal) *
              ShadedBody.multiplicity G.outerSet (fun Q => (Yo Q).toShadedBody) *
              ShadedBody.multiplicity (G.fiber Q) (fun i => (Yi i).toShadedBody)) := by
  obtain ⟨centres, hcentres, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (0 : E) 2).totallyBounded (1 / 4 : Real) (by norm_num)
  let C : Finset E := insert 0 hcentres.toFinset
  have hC : C.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨C.card, hC.card_pos, ?_⟩
  intro iota pi _ _ rho theta hrho hrhosmall hrt ht F Z J Ttheta parent m c hc
    hmass hm hball himage hparent
  let patches : E -> Finset iota := fun z =>
    F.filter (fun i => ‖(Z i).toTube.center - z‖ <= 1 / 4)
  have hcovered : ∀ i ∈ F, ∃ z ∈ C, i ∈ patches z := by
    intro i hi
    have hcentre : (Z i).toTube.center ∈ (Z i).carrier := by
      simpa only [Tube.center, midpoint_eq_smul_add, Tube.midpoint, invOf_eq_inv, one_div]
        using Tube.midpoint_mem_carrier hrho (Z i).toTube
    obtain ⟨z, hz, hzball⟩ := Set.mem_iUnion₂.mp (hcover (hball i hi hcentre))
    refine ⟨z, Finset.mem_insert_of_mem (hcentres.mem_toFinset.mpr hz), Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
    exact (by simpa only [Metric.mem_ball, dist_eq_norm] using hzball :
      ‖(Z i).toTube.center - z‖ < 1 / 4).le
  let w : E -> ENNReal := fun z => ∑ i ∈ patches z, volume (Z i).shade
  obtain ⟨z, hz, hmax⟩ := C.exists_max_image w hC
  let patch := patches z
  have hpatchF : patch ⊆ F := Finset.filter_subset _ _
  have hpaid : (∑ i ∈ F, volume (Z i).shade) <=
      (C.card : ENNReal) * ∑ i ∈ patch, volume (Z i).shade := by
    calc
      _ <= ∑ i ∈ F, ∑ z ∈ C, if i ∈ patches z then volume (Z i).shade else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨z, hz, hiz⟩ := hcovered i hi
        have h := Finset.single_le_sum (f := fun z => if i ∈ patches z then volume (Z i).shade else 0)
          (fun z hz => zero_le) hz
        simpa only [if_pos hiz] using h
      _ = ∑ z ∈ C, w z := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        dsimp [w]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [patches, Finset.mem_filter, hi, true_and]
      _ <= ∑ _z ∈ C, w z := Finset.sum_le_sum hmax
      _ = _ := by simp [w, patch, nsmul_eq_mul]
  have hpatchmass : 0 < ∑ i ∈ patch, volume (Z i).shade := by
    by_contra h
    have hz0 := le_antisymm (not_lt.mp h) bot_le
    rw [hz0, mul_zero] at hpaid
    exact (not_lt_of_ge hpaid) hmass
  have hpatch : patch.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hpatchmass
  have hcE : (0 : ENNReal) < c := by exact_mod_cast hc
  have hpaidM : (∑ i ∈ F, m i) <= (C.card : ENNReal) * ∑ i ∈ patch, m i := by
    apply (ENNReal.mul_le_mul_iff_right hcE.ne' ENNReal.coe_ne_top).mp
    calc
      _ = ∑ i ∈ F, volume (Z i).shade := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i hi => (hm i hi).symm)
      _ <= _ := hpaid
      _ = _ := by
        rw [Finset.sum_congr rfl (fun i hi => hm i (hpatchF hi)), ← Finset.mul_sum]
        ring
  have hcentred : ∀ i ∈ patch, ‖(Z i).toTube.center - z‖ <= 1 / 4 :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have htranslatedBall : ∀ i ∈ patch, ((Z i).translate (-z)).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi x hx
    change x ∈ (fun y => -z + y) '' (Z i).carrier at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hymid := Kakeya.Tube.carrier_subset_closedBall_midpoint (E := E) (Z i).toTube hy
    have hdist : ‖y - (Z i).toTube.center‖ <= 1 / 2 + (rho : Real) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, Tube.center] using hymid
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      _ = ‖(y - (Z i).toTube.center) + ((Z i).toTube.center - z)‖ := by congr 1; abel
      _ <= ‖y - (Z i).toTube.center‖ + ‖(Z i).toTube.center - z‖ := norm_add_le _ _
      _ <= (1 / 2 + (rho : Real)) + 1 / 4 := add_le_add hdist (hcentred i hi)
      _ <= 1 := by
        have hrhoR : (rho : Real) <= 1 / 16 := by exact_mod_cast hrhosmall
        linarith
  let FF : ShadedBody.FactorFamily E iota pi :=
    { innerSet := patch
      innerBody := fun i => ((Z i).translate (-z)).toShadedBody
      outerSet := patch.image parent
      outerBody := fun Q => ((Ttheta Q).translate (-z)).toConvexSpaceBody
      parent := parent
      parent_mem := fun i hi => Finset.mem_image_of_mem _ hi
      inner_le_parent := by
        intro i hi
        exact translate_le_translate (-z) (hparent i (hpatchF hi)) }
  have htranslatedMass : 0 < ∑ i ∈ FF.innerSet, volume ((Z i).translate (-z)).shade := by
    simpa [FF] using hpatchmass
  obtain ⟨G, ⟨raw⟩⟩ := exists_raw_rho_factorization_with_fibre_statistics_w97 hrho hrt ht
    FF (fun i => (Z i).translate (-z)) (fun Q => (Ttheta Q).translate (-z))
    (fun i hi => rfl) (fun Q hQ => rfl) htranslatedBall htranslatedMass
  have hGpatch : G.innerSet ⊆ patch := by
    rw [raw.inner_eq]
    exact Finset.filter_subset _ _
  have body_ext : ∀ V W : ShadedBody E,
      V.toConvexSpaceBody = W.toConvexSpaceBody -> V.shade = W.shade -> V = W := by
    intro V W hbody hshade
    cases V
    cases W
    cases hbody
    cases hshade
    rfl
  have inner_lift : ∀ i : iota, ∃ Yi : ShadedTube rho E,
      i ∈ G.innerSet -> Yi.toTube = (Z i).toTube ∧
        Yi.toShadedBody = (G.innerBody i).translate z ∧ Yi.shade ⊆ (Z i).shade := by
    intro i
    by_cases hi : i ∈ G.innerSet
    · let W := (G.innerBody i).translate z
      have hW : W.toConvexSpaceBody = (Z i).toConvexSpaceBody := by
        change (G.innerBody i).toConvexSpaceBody.translate z = _
        rw [raw.inner_body i (hGpatch hi)]
        exact ConvexSpaceBody.translate_neg_cancel
      let Yi : ShadedTube rho E :=
        { toTube := (Z i).toTube
          shade := W.shade
          measurableSet_shade := W.measurableSet_shade
          shade_subset := by rw [← hW]; exact W.shade_subset }
      refine ⟨Yi, fun _ => ⟨rfl, body_ext _ _ hW.symm rfl, ?_⟩⟩
      rintro x ⟨y, hy, rfl⟩
      have hsub := raw.raw_refinement.1.2 i hi
      have hy' := hsub.2 hy
      change y ∈ (fun w => -z + w) '' (Z i).shade at hy'
      obtain ⟨v, hv, rfl⟩ := hy'
      simpa only [add_neg_cancel_left] using hv
    · exact ⟨Z i, fun hi' => (hi hi').elim⟩
  choose Yi hYi using inner_lift
  have outer_lift : ∀ Q : pi, ∃ Yo : ShadedTube theta E,
      Q ∈ G.outerSet -> Yo.toTube = Ttheta Q ∧
        Yo.toShadedBody = (G.outerBody Q).translate z := by
    intro Q
    by_cases hQ : Q ∈ G.outerSet
    · let W := (G.outerBody Q).translate z
      have hW : W.toConvexSpaceBody = (Ttheta Q).toConvexSpaceBody := by
        change (G.outerBody Q).toConvexSpaceBody.translate z = _
        rw [raw.outer_body Q hQ]
        exact ConvexSpaceBody.translate_neg_cancel
      let Yo : ShadedTube theta E :=
        { toTube := Ttheta Q
          shade := W.shade
          measurableSet_shade := W.measurableSet_shade
          shade_subset := by rw [← hW]; exact W.shade_subset }
      exact ⟨Yo, fun _ => ⟨rfl, body_ext _ _ hW.symm rfl⟩⟩
    · let Yo : ShadedTube theta E :=
        { toTube := Ttheta Q
          shade := ∅
          measurableSet_shade := MeasurableSet.empty
          shade_subset := Set.empty_subset _ }
      exact ⟨Yo, fun hQ' => (hQ hQ').elim⟩
  choose Yo hYo using outer_lift
  refine ⟨patch, z, FF, G, Yi, Yo, hpatch, hpatchF, hpaid, hpaidM, hcentred,
    htranslatedBall, rfl, rfl, rfl, rfl, rfl, ⟨raw⟩, hYi, hYo, ?_⟩
  intro Q hQ
  have hiEq : ShadedBody.multiplicity (G.fiber Q) (fun i => (Yi i).toShadedBody) =
      ShadedBody.multiplicity (G.fiber Q) G.innerBody := by
    rw [Kakeya.multiplicity_eq_of_eqOn E (G.fiber Q)
      (fun i hi => (hYi i (by
        have hi' : i ∈ G.innerSet ∧ G.parent i = Q := by
          simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
        exact hi'.1)).2.1)]
    exact ShadedBody.multiplicity_translate_const _ _ _
  have hoEq : ShadedBody.multiplicity G.outerSet (fun Q => (Yo Q).toShadedBody) =
      ShadedBody.multiplicity G.outerSet G.outerBody := by
    rw [Kakeya.multiplicity_eq_of_eqOn E G.outerSet (fun Q hQ => (hYo Q hQ).2)]
    exact ShadedBody.multiplicity_translate_const _ _ _
  rw [hiEq, hoEq]
  have hsource : ShadedBody.multiplicity patch (fun i => (Z i).toShadedBody) =
      ShadedBody.multiplicity FF.innerSet FF.innerBody := by
    exact (ShadedBody.multiplicity_translate_const patch (fun i => (Z i).toShadedBody) (-z)).symm
  rw [hsource]
  exact raw.raw_scalar Q hQ

end

end Kakeya.ml1Boot.TrialRestartW94
