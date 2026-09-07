import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalCleanupQuotientAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalNearbyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicFinalPreparation

/-!
# The synchronized affine-diagonal joint family

This file exposes the target, exact, and source shadings on precisely the
final index set selected by the affine nearby-CWA construction.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory
open PureWZ2ExternalWeightRegularizationData

namespace PureWZ2AffineDiagonalCleanupQuotientAssemblyData

private theorem center_norm_le_two
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (_assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    ‖cleanup.raw.center‖ ≤ 2 := by
  have hcenter0 : |cleanup.raw.center 0| ≤ 1 := by
    rw [cleanup.raw.center_eq]
    simpa [pureWZ2AffineDiagonalCommonCenter, point3] using
      popular.popular.center_mem (0 : Fin 3)
  have hcenter1 : |cleanup.raw.center 1| ≤ 1 := by
    rw [cleanup.raw.center_eq]
    simpa [pureWZ2AffineDiagonalCommonCenter, point3] using
      popular.popular.center_mem (1 : Fin 3)
  have hcenter2 : |cleanup.raw.center 2| ≤ 1 := by
    have hcenterHeight : cleanup.raw.center 2 =
        affineScale.slopeData.anchor := by
      rw [cleanup.raw.center_eq]
      simp [pureWZ2AffineDiagonalCommonCenter, point3]
    rw [hcenterHeight, abs_le]
    exact ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans <| subband.left_mem.trans
          affineScale.slope_anchor_mem.1),
      affineScale.slope_anchor_mem.2.trans <| subband.right_mem.trans <|
        band.right_mem.trans
        band.lemma31.data.scaleData.slabRight_mem⟩
  have h0sq : cleanup.raw.center 0 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (cleanup.raw.center 0)]
  have h1sq : cleanup.raw.center 1 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (cleanup.raw.center 1)]
  have h2sq : cleanup.raw.center 2 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (cleanup.raw.center 2)]
  have hnorm := point3_coord_norm_sq cleanup.raw.center
  nlinarith [norm_nonneg cleanup.raw.center]

/-- The finite scalar bound required to expose nearby CWA on the final
affine-diagonal joint family. -/
def nearbyConstantBudget
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant targetConstant :
      ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) : Prop :=
  ∀ coordinate, max
    (16 * ((assembly.sourceSchedule.scaleCount +
        assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
      (Nat.log 2
        (2 * (assembly.quotient.separatedFine
          (pureWZ2AffineDiagonalCleanupJointWeight data)
          assembly.selection).family.card) + 1 : ENNReal) ^
        (assembly.sourceSchedule.scaleCount +
          assembly.sourceSchedule.scaleCount))
    (ENNReal.ofReal
        (27 * (2 * (32 * affineScale.slopeData.heightScale) - 1) ^ 3) *
      ((432 : ENNReal) *
        Kakeya.realRpowENN (assembly.quotient.callerRho coordinate) 2 *
        ENNReal.ofReal (1 + 2 * assembly.quotient.callerRho coordinate) *
        ENNReal.ofReal (1 /
          (affineScale.slopeData.heightScale *
            affineScale.slopeData.transverseScale *
            assembly.representative.sourceRho coordinate ^ 2))) *
      ((data.selectedWeightLevel⁻¹ *
        (data.outputConstant * assembly.retentionConstant *
          (16 * ((assembly.sourceSchedule.scaleCount +
              assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (assembly.quotient.separatedFine
                (pureWZ2AffineDiagonalCleanupJointWeight data)
                assembly.selection).family.card) + 1 : ENNReal) ^
              (assembly.sourceSchedule.scaleCount +
                assembly.sourceSchedule.scaleCount)))) *
        data.outputConstant)) ≤ targetConstant

/-- The synchronized affine-diagonal assembly supplies nearby CWA on exactly
the final target family used by all downstream shading and local-grain data. -/
theorem toNearbyCWA
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant targetConstant :
      ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (hscaleBudget : affineDiagonalQuotientScaleWindowConstant
      sourceScheduleConstant ≤ targetConstant)
    (hconstantBudget : assembly.nearbyConstantBudget
      (targetConstant := targetConstant)) :
    WZ2PaperPureCWAAtNearbyScales
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2AffineDiagonalCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family targetConstant := by
  have hsourceLine : WZ1PaperIsLineClass data.selected.family :=
    ((band.lemma31.data.cfg.line_class.subfamily regularized.selected).subfamily
      data.selected)
  have hsourceBase : ∀ source,
      ‖(data.selected.family.tube source).base‖ ≤ 5 := by
    intro source
    rw [data.selected.tube_eq, regularized.selected.tube_eq]
    exact band.lemma31.data.cfg.bounded_base _ |>.trans (by norm_num)
  have htargetLine : WZ1PaperIsLineClass
      (cleanupTargetSubfamily (cleanup := cleanup) data).family :=
    cleanupTarget_line_class (cleanup := cleanup) data
  have htargetDirection : ∀ target,
      ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube
        target).direction =
        wz1PaperDirection
          ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube
            target) := by
    intro target
    have hzero := congrArg (fun tube => tube.direction)
      (cleanup.final_zeroBased
        (cleanupTargetEmbedding (cleanup := cleanup) data target))
    exact hzero.symm
  have htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint
        ((cleanupTargetSubfamily (cleanup := cleanup) data).family.tube
          target)‖ ≤ 3 := by
    intro target
    exact cleanup.final_midpoint_le_three
      (cleanupTargetEmbedding (cleanup := cleanup) data target)
  apply assembly.joint.toAffineDiagonalNearbyCWA assembly.sourceSchedule
    affineScale.slopeData.frameSlope cleanup.raw.center
    affineScale.slopeData.heightScale affineScale.slopeData.transverseScale
    ((show (1 : ℝ) ≤ 100 by norm_num).trans affineScale.height_lower)
    affineScale.transverse_pos
    (affineScale.transverse_le.trans (by norm_num))
    (center_norm_le_two assembly) band.lemma31.data.cfg.extremal.delta_pos
    affineScale.source_le_target hsourceBase htargetLine htargetDirection
    htargetMidpoint (cleanupTarget_axis_source (cleanup := cleanup) data)
    data.selectedWeightLevel assembly.retentionConstant
    data.selectedWeightLevel_pos.ne' data.selectedWeightLevel_ne_top
    assembly.source_cardinality_retention htargetFinite
    (cleanupTarget_distinct (cleanup := cleanup) data) assembly.sourceRho_eq
    assembly.callerRho_eq hscaleBudget hconstantBudget

def finalTargetSubfamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    Kakeya.Streamlined.TubeSubfamily
      (cleanupTargetSubfamily (cleanup := cleanup) data).family :=
  assembly.joint.finalTargetTubeSubfamily

def finalSourceSubfamily
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    Kakeya.Streamlined.TubeSubfamily data.selected.family :=
  assembly.joint.finalSourceTubeSubfamily

def finalTargetShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperTubeShading
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2AffineDiagonalCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family :=
  assembly.joint.finalTargetShading
    (cleanupTargetShading (cleanup := cleanup) data)

def finalExactShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperTubeShading
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2AffineDiagonalCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family :=
  assembly.joint.finalTargetShading
    (cleanupTargetExactShading (regularized := regularized)
      (cleanup := cleanup) data)

def finalSourceShading
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperTubeShading assembly.finalSourceSubfamily.family :=
  assembly.joint.finalSourceShading
    (cleanupTargetSourceShading (regularized := regularized)
      (cleanup := cleanup) data)

/-- On the synchronized cleanup family, the joint weight is exactly the
fixed cleanup factor times the retained target shaded mass. -/
theorem jointWeight_eq_target_volume
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant : ENNReal}
    {levelCount outputLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    (data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount)
    (target : Fin (cleanupTargetSubfamily (cleanup := cleanup) data).family.card) :
    pureWZ2AffineDiagonalCleanupJointWeight data target =
      (pureWZ2AffineDiagonalConflictDegreeBound affineScale + 1) *
        MeasureTheory.volume
          ((cleanupTargetShading (cleanup := cleanup) data).carrier target) := by
  unfold pureWZ2AffineDiagonalCleanupJointWeight
    pureWZ2AffineDiagonalCleanupIndicator
  let source := cleanupSourcePreimage (cleanup := cleanup) data target
  have hsource := cleanupSourcePreimage_ambient
    (cleanup := cleanup) data target
  have hunique : ∀ other : Fin cleanup.finalFamily.card,
      cleanup.finalTargetSourceIndex other = data.selected.embedding target ↔
        other = source := by
    intro other
    constructor
    · intro hother
      apply cleanup.finalTargetSourceIndex.injective
      exact hother.trans hsource.symm
    · rintro rfl
      exact hsource
  simp_rw [hunique]
  rw [Fintype.sum_ite_eq']
  change (pureWZ2AffineDiagonalConflictDegreeBound affineScale + 1) *
      MeasureTheory.volume (cleanup.finalShading.carrier source) =
    (pureWZ2AffineDiagonalConflictDegreeBound affineScale + 1) *
      MeasureTheory.volume
        (cleanup.finalShading.carrier
          (cleanupTargetEmbedding (cleanup := cleanup) data target))
  rw [cleanupTargetEmbedding_eq_preimage]

theorem finalTarget_line_class
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperIsLineClass assembly.finalTargetSubfamily.family :=
  assembly.joint.finalTarget_line_class
    (cleanupTarget_line_class (cleanup := cleanup) data)

theorem finalTarget_nonempty
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    assembly.finalTargetSubfamily.family.Nonempty := by
  have hsourceCard : 0 < data.selected.family.enncard := by
    change (0 : ENNReal) < (data.selected.family.card : ENNReal)
    exact_mod_cast data.selected_nonempty
  have hlhs : 0 <
      data.selectedWeightLevel * data.selected.family.enncard :=
    ENNReal.mul_pos data.selectedWeightLevel_pos.ne' hsourceCard.ne'
  have hretained := assembly.source_cardinality_retention
  by_contra hempty
  have hcardZero : assembly.finalTargetSubfamily.family.enncard = 0 := by
    change (assembly.finalTargetSubfamily.family.card : ENNReal) = 0
    exact_mod_cast Nat.eq_zero_of_not_pos hempty
  change data.selectedWeightLevel * data.selected.family.enncard ≤
      assembly.retentionConstant *
        assembly.finalTargetSubfamily.family.enncard at hretained
  rw [hcardZero, mul_zero] at hretained
  exact (not_le_of_gt hlhs) hretained

/-- The final joint target shading has positive mass.  This uses the positive
joint weight of any retained final index and its literal target-volume
interpretation. -/
theorem finalTargetShading_mass_pos
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    0 < assembly.finalTargetShading.mass := by
  let index : Fin assembly.finalTargetSubfamily.family.card :=
    ⟨0, assembly.finalTarget_nonempty⟩
  have hweight : 0 < pureWZ2AffineDiagonalCleanupJointWeight data
      (assembly.joint.finalTargetIndex index) := by
    exact assembly.joint.selected_weight_pos
      (assembly.joint.selected.orderEmbOfFin rfl index)
      (Finset.orderEmbOfFin_mem assembly.joint.selected rfl index)
  rw [jointWeight_eq_target_volume data] at hweight
  have hvolume : 0 < MeasureTheory.volume
      ((cleanupTargetShading (cleanup := cleanup) data).carrier
        (assembly.joint.finalTargetIndex index)) :=
    pos_of_mul_pos_right hweight bot_le
  have hle : MeasureTheory.volume
      (assembly.finalTargetShading.carrier index) ≤
        assembly.finalTargetShading.mass := by
    change MeasureTheory.volume
        ((cleanupTargetShading (cleanup := cleanup) data).carrier
          (assembly.joint.finalTargetIndex index)) ≤
      ∑ target, MeasureTheory.volume
        ((cleanupTargetShading (cleanup := cleanup) data).carrier
          (assembly.joint.finalTargetIndex target))
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun target : Fin assembly.finalTargetSubfamily.family.card =>
        MeasureTheory.volume
          ((cleanupTargetShading (cleanup := cleanup) data).carrier
            (assembly.joint.finalTargetIndex target)))
      (fun _ _ => by positivity) (Finset.mem_univ index)
  exact hvolume.trans_le hle

/-- The synchronized exact affine image also has positive mass.  Positivity
comes from the original source weight retained by the two source selections,
and the affine map has the positive Jacobian recorded by the slope scale. -/
theorem finalExactShading_mass_pos
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    0 < assembly.finalExactShading.mass := by
  let index : Fin assembly.finalTargetSubfamily.family.card :=
    ⟨0, assembly.finalTarget_nonempty⟩
  let sourceIndex : Fin data.selected.family.card :=
    assembly.joint.finalTargetIndex index
  let sourceCarrier : Set Point3 :=
    (cleanupTargetSourceShading (regularized := regularized)
      (cleanup := cleanup) data).carrier sourceIndex
  let imageCarrier : Set Point3 :=
    pureWZ2AffineDiagonalMapCentered affineScale.slopeData.frameSlope
      cleanup.raw.center affineScale.slopeData.heightScale
        affineScale.slopeData.transverseScale 1 '' sourceCarrier
  have hsourceVolume : 0 < MeasureTheory.volume sourceCarrier := by
    change 0 < MeasureTheory.volume
      (popular.popular.restricted.carrier
        (regularized.selected.embedding
          (data.selected.embedding sourceIndex)))
    exact regularized.selected_weight_pos (data.selected.embedding sourceIndex)
  have himageVolume : MeasureTheory.volume imageCarrier =
      ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
        MeasureTheory.volume sourceCarrier := by
    dsimp only [imageCarrier]
    rw [affineScale.slopeData.heightScale_eq,
      affineScale.slopeData.transverseScale_eq]
    exact pureWZ2AffineDiagonalMapCentered_volume_image_general
      affineScale.slopeData.frameSlope cleanup.raw.center
      affineScale.slopeData.rotatedSlopeScale_pos
      affineScale.slopeData.normalizationConstant_pos
      ((cleanupTargetSourceShading (regularized := regularized)
        (cleanup := cleanup) data).measurable_carrier sourceIndex)
  have himagePos : 0 < MeasureTheory.volume imageCarrier := by
    rw [himageVolume]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr
        affineScale.slopeData.rotatedSlopeScale_pos).ne' hsourceVolume.ne'
  have hsubset : imageCarrier ⊆
      assembly.finalExactShading.carrier index := by
    intro point hpoint
    change point ∈ (cleanupTargetExactShading (regularized := regularized)
      (cleanup := cleanup) data).carrier
        (assembly.joint.finalTargetIndex index)
    rw [cleanupTargetExactShading_carrier]
    refine ⟨hpoint, ?_⟩
    rw [cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data]
    exact ⟨point, hpoint, rfl⟩
  have hcarrierPos : 0 < MeasureTheory.volume
      (assembly.finalExactShading.carrier index) :=
    himagePos.trans_le (MeasureTheory.measure_mono hsubset)
  exact hcarrierPos.trans_le <| Finset.single_le_sum
    (s := Finset.univ)
    (f := fun other : Fin assembly.finalTargetSubfamily.family.card =>
      MeasureTheory.volume (assembly.finalExactShading.carrier other))
    (fun _ _ => by positivity) (Finset.mem_univ index)

/-- Every final exact affine carrier retains the first public
regularization's quantitative weight floor.  Summing over the final joint
index set gives a denominator-free exact-mass bound, independent of the two
later complete-fiber selection losses. -/
theorem rotatedSlopeScale_mul_selectedWeightLevel_mul_finalCard_le_exactMass
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    (ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
        regularized.selectedWeightLevel) *
      assembly.finalTargetSubfamily.family.enncard ≤
        assembly.finalExactShading.mass := by
  change (ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
        regularized.selectedWeightLevel) *
      (assembly.finalTargetSubfamily.family.card : ENNReal) ≤
    ∑ index : Fin assembly.finalTargetSubfamily.family.card,
      MeasureTheory.volume (assembly.finalExactShading.carrier index)
  calc
    (ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
          regularized.selectedWeightLevel) *
        (assembly.finalTargetSubfamily.family.card : ENNReal) =
      ∑ _index : Fin assembly.finalTargetSubfamily.family.card,
        ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
          regularized.selectedWeightLevel := by
        simp [Finset.sum_const]
        ring
    _ ≤ ∑ index : Fin assembly.finalTargetSubfamily.family.card,
        MeasureTheory.volume (assembly.finalExactShading.carrier index) := by
      apply Finset.sum_le_sum
      intro index _
      let sourceIndex : Fin data.selected.family.card :=
        assembly.joint.finalTargetIndex index
      let sourceCarrier : Set Point3 :=
        (cleanupTargetSourceShading (regularized := regularized)
          (cleanup := cleanup) data).carrier sourceIndex
      let imageCarrier : Set Point3 :=
        pureWZ2AffineDiagonalMapCentered affineScale.slopeData.frameSlope
          cleanup.raw.center affineScale.slopeData.heightScale
            affineScale.slopeData.transverseScale 1 '' sourceCarrier
      have hsourceFloor : regularized.selectedWeightLevel ≤
          MeasureTheory.volume sourceCarrier := by
        change regularized.selectedWeightLevel ≤
          MeasureTheory.volume
            (popular.popular.restricted.carrier
              (regularized.selected.embedding
                (data.selected.embedding sourceIndex)))
        exact (regularized.selected_weight_band
          (data.selected.embedding sourceIndex)).1
      have himageVolume : MeasureTheory.volume imageCarrier =
          ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
            MeasureTheory.volume sourceCarrier := by
        dsimp only [imageCarrier]
        rw [affineScale.slopeData.heightScale_eq,
          affineScale.slopeData.transverseScale_eq]
        exact pureWZ2AffineDiagonalMapCentered_volume_image_general
          affineScale.slopeData.frameSlope cleanup.raw.center
          affineScale.slopeData.rotatedSlopeScale_pos
          affineScale.slopeData.normalizationConstant_pos
          ((cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) data).measurable_carrier sourceIndex)
      have hsubset : imageCarrier ⊆
          assembly.finalExactShading.carrier index := by
        intro point hpoint
        change point ∈ (cleanupTargetExactShading
          (regularized := regularized) (cleanup := cleanup) data).carrier
            (assembly.joint.finalTargetIndex index)
        rw [cleanupTargetExactShading_carrier]
        refine ⟨hpoint, ?_⟩
        rw [cleanupTargetShading_carrier_eq_saturation
          (regularized := regularized) (cleanup := cleanup) data]
        exact ⟨point, hpoint, rfl⟩
      calc
        ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
              regularized.selectedWeightLevel ≤
            ENNReal.ofReal affineScale.slopeData.rotatedSlopeScale *
              MeasureTheory.volume sourceCarrier := by gcongr
        _ = MeasureTheory.volume imageCarrier := himageVolume.symm
        _ ≤ MeasureTheory.volume
              (assembly.finalExactShading.carrier index) :=
          MeasureTheory.measure_mono hsubset

theorem finalTarget_zeroBased
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin assembly.finalTargetSubfamily.family.card) :
    pureWZ2PaperZeroBasedTube
        (assembly.finalTargetSubfamily.family.tube index) =
      assembly.finalTargetSubfamily.family.tube index := by
  rw [assembly.finalTargetSubfamily.tube_eq]
  change pureWZ2PaperZeroBasedTube
      (cleanup.finalFamily.tube
        (cleanupTargetEmbedding (cleanup := cleanup) data
          (assembly.joint.finalTargetIndex index))) = _
  exact cleanup.final_zeroBased _

theorem finalTarget_direction
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin assembly.finalTargetSubfamily.family.card) :
    (assembly.finalTargetSubfamily.family.tube index).direction =
      wz1PaperDirection (assembly.finalTargetSubfamily.family.tube index) := by
  have hzero := congrArg (fun tube => tube.direction)
    (assembly.finalTarget_zeroBased index)
  exact hzero.symm

theorem finalTarget_base_le_five
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin assembly.finalTargetSubfamily.family.card) :
    ‖(assembly.finalTargetSubfamily.family.tube index).base‖ ≤ 5 := by
  let tube := assembly.finalTargetSubfamily.family.tube index
  have hline := assembly.finalTarget_line_class index
  have hzero := assembly.finalTarget_zeroBased index
  have hbase := congrArg (fun tube => tube.base) hzero
  change ‖tube.base‖ ≤ 5
  have hbaseEq : tube.base = wz1TubeAxisZeroPoint tube := by
    simpa only [pureWZ2PaperZeroBasedTube] using hbase.symm
  rw [hbaseEq]
  exact (pureWZ2_zeroPoint_norm_le_one hline).trans (by norm_num)

theorem finalTarget_packing_distinct
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperIsEssentiallyDistinct
      (pureWZ2CenteredPackingFamily assembly.finalTargetSubfamily.family) := by
  have hpaper : WZ1PaperIsEssentiallyDistinct
      assembly.finalTargetSubfamily.family :=
    (cleanupTarget_paper_essentially_distinct (cleanup := cleanup) data).subfamily
      assembly.finalTargetSubfamily
  intro first second hne
  change (2 / 3 : ℝ) * affineScale.targetDelta <
    wz1PaperLineDistance
      (wz2PaperRelabelTube
        (pureWZ2PaperCenteredTube
          (assembly.finalTargetSubfamily.family.tube first)))
      (wz2PaperRelabelTube
        (pureWZ2PaperCenteredTube
          (assembly.finalTargetSubfamily.family.tube second)))
  rw [wz2PaperRelabelTube_lineDistance_both,
    pureWZ2PaperCenteredTube_lineDistance _ _
      (assembly.finalTarget_line_class first)
      (assembly.finalTarget_line_class second)]
  have hraw := hpaper first second hne
  nlinarith [affineScale.targetDelta_pos]

theorem finalTarget_cubical
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperIsCubicalShading assembly.finalTargetShading :=
  assembly.joint.finalTargetShading_cubical
    (cleanupTargetShading_cubical (cleanup := cleanup) data)

theorem finalSource_line_class
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperIsLineClass assembly.finalSourceSubfamily.family :=
  ((band.lemma31.data.cfg.line_class.subfamily regularized.selected).subfamily
    data.selected).subfamily assembly.finalSourceSubfamily

theorem finalSource_base_le_five
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin assembly.finalSourceSubfamily.family.card) :
    ‖(assembly.finalSourceSubfamily.family.tube index).base‖ ≤ 5 := by
  rw [assembly.finalSourceSubfamily.tube_eq, data.selected.tube_eq,
    regularized.selected.tube_eq]
  exact band.lemma31.data.cfg.bounded_base _ |>.trans (by norm_num)

def finalSourceLocalGrains
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    PureWZ2LocalGrainData assembly.finalSourceShading sigma
      band.sourceConstant :=
  (cleanupTargetSourceLocalGrains (regularized := regularized)
    (cleanup := cleanup) data).subfamily assembly.finalSourceSubfamily

/-- Feed the final affine-diagonal joint family, its literal target shading,
and its nearby-CWA certificate into the generic final-isotropic preparation.
All geometric hypotheses are discharged by the synchronized joint package;
callers retain only the finite scalar schedule and radius budgets. -/
theorem toFinalIsotropicPreparation
    {sigma epsilon delta finalDelta isotropicScale : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant targetConstant
      boxScheduleConstant cleanupScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (hnearbyScale : affineDiagonalQuotientScaleWindowConstant
      sourceScheduleConstant ≤ targetConstant)
    (hnearbyConstant : assembly.nearbyConstantBudget
      (targetConstant := targetConstant))
    (hscale : 1 ≤ isotropicScale)
    (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaSmall : finalDelta ≤ 1 / 4)
    (hradius : isotropicScale * (6 * affineScale.targetDelta) +
      finalDelta * Real.sqrt 3 ≤ 6 * finalDelta)
    (hscaleSourceSmall :
      isotropicScale * affineScale.targetDelta ≤ 1 / 1000)
    (boxLevelCount : ℕ)
    (hsourceTwo : 2 < targetConstant)
    (hboxLevels : ENNReal.ofReal (1 / affineScale.targetDelta) ≤
      targetConstant ^ boxLevelCount)
    (hboxScheduleFinite :
      WZ2PaperFiniteErrorConstant boxScheduleConstant)
    (hboxSchedule :
      targetConstant * targetConstant ≤ boxScheduleConstant)
    (cleanupLevelCount : ℕ)
    (hboxTwo : 2 <
      (Classical.choice (pureWZ2_final_isotropic_box_preparation
        assembly.finalExactShading
        (assembly.toNearbyCWA htargetFinite hnearbyScale hnearbyConstant)
        assembly.finalTarget_nonempty affineScale.targetDelta_le_one
        assembly.finalExactShading_mass_pos isotropicScale hscale
        hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels hboxScheduleFinite
        hboxSchedule)).regularized.outputConstant)
    (hcleanupLevels : ENNReal.ofReal (1 / affineScale.targetDelta) ≤
      (Classical.choice (pureWZ2_final_isotropic_box_preparation
        assembly.finalExactShading
        (assembly.toNearbyCWA htargetFinite hnearbyScale hnearbyConstant)
        assembly.finalTarget_nonempty affineScale.targetDelta_le_one
        assembly.finalExactShading_mass_pos isotropicScale hscale
        hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels hboxScheduleFinite
        hboxSchedule)).regularized.outputConstant ^ cleanupLevelCount)
    (hcleanupScheduleFinite :
      WZ2PaperFiniteErrorConstant cleanupScheduleConstant)
    (hcleanupSchedule :
      (Classical.choice (pureWZ2_final_isotropic_box_preparation
        assembly.finalExactShading
        (assembly.toNearbyCWA htargetFinite hnearbyScale hnearbyConstant)
        assembly.finalTarget_nonempty affineScale.targetDelta_le_one
        assembly.finalExactShading_mass_pos isotropicScale hscale
        hscaleSourceSmall boxLevelCount hsourceTwo hboxLevels hboxScheduleFinite
        hboxSchedule)).regularized.outputConstant ^ 2 ≤
          cleanupScheduleConstant) :
    Nonempty (PureWZ2FinalIsotropicPreparationData
      (targetDelta := finalDelta) assembly.finalExactShading targetConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount isotropicScale) := by
  apply pureWZ2_final_isotropic_preparation assembly.finalExactShading
    (assembly.toNearbyCWA htargetFinite hnearbyScale hnearbyConstant)
    assembly.finalTarget_nonempty affineScale.targetDelta_le_one
    assembly.finalExactShading_mass_pos assembly.finalTarget_line_class
    assembly.finalTarget_direction assembly.finalTarget_base_le_five
    assembly.finalTarget_packing_distinct isotropicScale hscale hfinalDelta
    hfinalDeltaSmall hradius hscaleSourceSmall boxLevelCount hsourceTwo
    hboxLevels hboxScheduleFinite hboxSchedule cleanupLevelCount hboxTwo
    hcleanupLevels hcleanupScheduleFinite hcleanupSchedule

end PureWZ2AffineDiagonalCleanupQuotientAssemblyData

end Kakeya.Assouad

end
