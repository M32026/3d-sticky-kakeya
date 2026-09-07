import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicCleanupSourceRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicQuotientScheduleCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicJointShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalExtremalBudgets
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FiniteScheduleParameters

/-!
# Final-isotropic cleanup and quotient schedule assembly

This is the dependent assembly layer joining the cleanup-supported source
nearby-CWA regularization to the representative-parent quotient construction.
The source and target families use one literal index type, and the two later
selections keep complete quotient and source-parent fibers simultaneously.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The genuine retained target mass attached to the corresponding selected
source index. -/
def pureWZ2IsotropicCleanupJointWeight
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin data.isotropicCleanupFinalFamily.card) : ENNReal :=
  cleanup.sourceWeight (data.selected.embedding index)

/-- The finite source schedule, final-isotropic representative parents,
quotient parents, and both complete-fiber selections in one package. -/
structure PureWZ2IsotropicCleanupQuotientAssemblyData
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (sourceScheduleConstant : ENNReal) (parentLevelCount : ℕ) where
  sourceSchedule : PureWZ2FiniteNearbyScheduleData
    (family := data.selected.family) data.outputConstant
      sourceScheduleConstant parentLevelCount
  representative : PureWZ2FiniteRepresentativeParentScheduleData
    data.isotropicCleanupFinalFamily
    (Equiv.refl (Fin data.selected.family.card)) data.outputConstant
      sourceSchedule.scaleCount
  quotient : PureWZ2FiniteAnisotropicParentQuotientScheduleData representative
  selection : PureWZ2FiniteStrongParentSelectionData
    (pureWZ2IsotropicCleanupJointWeight data) sourceSchedule.scaleCount
    quotient.Parent
    (fun coordinate target =>
      (quotient.quotient coordinate).assignedParent target)
    quotient.conflict pureWZ2AnisotropicQuotientCenterConflictDegree
  joint : quotient.PureWZ2AnisotropicJointRegularizationData
    (pureWZ2IsotropicCleanupJointWeight data) selection
  sourceRho_eq : ∀ coordinate, representative.sourceRho coordinate =
    (sourceSchedule.witness coordinate).rho
  callerRho_eq : ∀ coordinate, quotient.callerRho coordinate =
    isotropicQuotientCallerScale targetDelta scale
      (representative.sourceRho coordinate)

/-- Assemble the final-isotropic quotient schedule from a source family whose
nearby CWA has already been restored inside the fixed target cleanup. -/
theorem pureWZ2_isotropic_cleanup_quotient_assembly
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    (data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount)
    (sourceScheduleConstant : ENNReal)
    (parentLevelCount : ℕ)
    (hsourceTwo : 2 < data.outputConstant)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (hlevels : ENNReal.ofReal (1 / sourceDelta) ≤
      data.outputConstant ^ parentLevelCount)
    (hsourceScheduleConstant : data.outputConstant * data.outputConstant ≤
      sourceScheduleConstant)
    (hscale : 1 ≤ scale) (hcenter : |center 2| ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (hsourceLine : WZ1PaperIsLineClass data.selected.family)
    (hsourceBase : ∀ source, ‖(data.selected.family.tube source).base‖ ≤ 5)
    (hzero : ∀ (index : Fin data.selected.family.card)
      (coordinate : Fin 2),
      |(pureWZ2IsotropicMap center scale
        (wz1PaperAxisPointAtHeight
          (data.selected.family.tube index) (center 2)))
          coordinate.castSucc| ≤ 1 / 3) :
    Nonempty (PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) := by
  rcases pureWZ2_finite_pure_nearby_schedule parentLevelCount
      data.cwa_nearby.1 hsourceDeltaOne hsourceTwo
      data.cwa_nearby.2.1.2 hlevels hsourceScheduleConstant data.cwa_nearby with
    ⟨sourceSchedule⟩
  let representative := isotropicRepresentativeParentSchedule sourceSchedule
    center hscale hcenter htargetDelta data.selected_nonempty hsourceLine
    hsourceBase hzero data.isotropicCleanupFinalFamily_distinct
  let quotient := isotropicParentQuotientSchedule representative
    (lt_of_lt_of_le (by norm_num) hscale) (fun _ => rfl)
  rcases quotient.simultaneouslySeparate
      (pureWZ2IsotropicCleanupJointWeight data) with ⟨selection⟩
  rcases quotient.simultaneouslyRegularizeQuotientAndSource
      (pureWZ2IsotropicCleanupJointWeight data) selection with ⟨joint⟩
  exact ⟨{
    sourceSchedule := sourceSchedule
    representative := representative
    quotient := quotient
    selection := selection
    joint := joint
    sourceRho_eq := fun _ => rfl
    callerRho_eq := fun _ => rfl
  }⟩

namespace PureWZ2IsotropicCleanupQuotientAssemblyData

/-- The family entering the second joint selection has polynomial cardinality
at the canonical centered packing radius.  This removes the last runtime
family cardinality from the final logarithmic CWA budget. -/
theorem separatedFine_card_le_packing_bound
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetDelta : 0 < targetDelta)
    (hpackingScaleOne : (2 / 3 : ℝ) * targetDelta ≤ 1) :
    (assembly.quotient.separatedFine
        (pureWZ2IsotropicCleanupJointWeight data)
        assembly.selection).family.card ≤
      (2 * Nat.ceil (80 / ((2 / 3 : ℝ) * targetDelta)) + 1) ^ 5 := by
  let targetFamily := data.isotropicCleanupFinalFamily
  let coordinate : Fin assembly.sourceSchedule.scaleCount :=
    ⟨0, assembly.sourceSchedule.scaleCount_pos⟩
  have htargetLine : WZ1PaperIsLineClass targetFamily :=
    (assembly.representative.parentData coordinate).target_line_class
  let packingFamily := wz2PaperRelabelFamily
    (sourceScale := targetDelta)
    (targetScale := (2 / 3 : ℝ) * targetDelta) targetFamily
  have hpackingDistinct : WZ1PaperIsEssentiallyDistinct packingFamily := by
    simpa [packingFamily, targetFamily] using
      (assembly.representative.parentData coordinate).target_packing_distinct
  have hpackingLine : WZ1PaperIsLineClass
      packingFamily := by
    intro index
    exact wz2PaperRelabelTube_lineClass
      (htargetLine index)
  have hpacking := paper_essentially_distinct_card_bound_nat
    hpackingDistinct hpackingLine
    (mul_pos (by norm_num) htargetDelta) hpackingScaleOne
  have hsubfamily :
      (assembly.quotient.separatedFine
        (pureWZ2IsotropicCleanupJointWeight data)
        assembly.selection).family.card ≤ targetFamily.card := by
    change assembly.selection.selected.card ≤ targetFamily.card
    simpa [targetFamily] using assembly.selection.selected.card_le_univ
  exact hsubfamily.trans (by
    simpa [packingFamily, targetFamily, wz2PaperRelabelFamily] using hpacking)

/-- Explicit logarithmic form of `separatedFine_card_le_packing_bound`. -/
theorem separatedFine_log_bound
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetDelta : 0 < targetDelta)
    (hpackingScaleOne : (2 / 3 : ℝ) * targetDelta ≤ 1) :
    (Nat.log 2
        (2 * (assembly.quotient.separatedFine
          (pureWZ2IsotropicCleanupJointWeight data)
          assembly.selection).family.card) + 1 : ℝ) ≤
      (5 / Real.log 2) *
          Real.log (1 / ((2 / 3 : ℝ) * targetDelta)) +
        (5 * Real.log 163 / Real.log 2 + 2) := by
  exact explicit_card_log_bound
    (mul_pos (by norm_num) htargetDelta) hpackingScaleOne
    (assembly.separatedFine_card_le_packing_bound
      htargetDelta hpackingScaleOne)

/-- The positive selected-weight level controls the total number of source
tubes entering the final quotient schedule. -/
theorem selectedWeightLevel_mul_sourceCard_le
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (_assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    data.selectedWeightLevel * data.selected.family.enncard ≤
      data.selectedWeight := by
  rw [data.selectedWeight_eq]
  change data.selectedWeightLevel *
      (data.selected.family.card : ENNReal) ≤
    ∑ index : Fin data.selected.family.card,
      cleanup.sourceWeight (data.selected.embedding index)
  calc
    data.selectedWeightLevel * (data.selected.family.card : ENNReal) =
        ∑ _index : Fin data.selected.family.card,
          data.selectedWeightLevel := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun index _ =>
      (data.selected_weight_band index).1

/-- Explicit total selection loss from the quotient-center pass and the
joint quotient/source-parent pass. -/
def retentionConstant
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) : ENNReal :=
  (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
      assembly.sourceSchedule.scaleCount *
    ((8 : ENNReal) *
      (Nat.log 2
        (2 * (assembly.quotient.separatedFine
          (pureWZ2IsotropicCleanupJointWeight data)
          assembly.selection).family.card) + 1 : ENNReal) ^
        (assembly.sourceSchedule.scaleCount +
          assembly.sourceSchedule.scaleCount + 1)) *
    (2 * data.selectedWeightLevel)

/-- The two complete-fiber selections retain enough indices for the
actual-John quotient CWA estimate. -/
theorem source_cardinality_retention
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    data.selectedWeightLevel * data.selected.family.enncard ≤
      assembly.retentionConstant *
        (assembly.quotient.jointlyRegularizedFine
          (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family.enncard := by
  let weight := pureWZ2IsotropicCleanupJointWeight data
  let separated := assembly.quotient.separatedFine weight assembly.selection
  let finalFine := assembly.quotient.jointlyRegularizedFine
    weight assembly.selection assembly.joint.selected
  have hselectedWeight : data.selectedWeight =
      ∑ target : Fin data.isotropicCleanupFinalFamily.card,
        weight target := by
    rw [data.selectedWeight_eq]
    rfl
  have hfinalWeight :
      (∑ index ∈ assembly.joint.selected,
        weight (separated.embedding index)) ≤
      (2 * data.selectedWeightLevel) * finalFine.family.enncard := by
    calc
      _ ≤ ∑ _index ∈ assembly.joint.selected,
          2 * data.selectedWeightLevel := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (data.selected_weight_band (separated.embedding index)).2
      _ = (2 * data.selectedWeightLevel) * finalFine.family.enncard := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Kakeya.Streamlined.TubeFamily.enncard]
        rw [show finalFine.family.card = assembly.joint.selected.card by rfl]
        exact mul_comm _ _
  calc
    data.selectedWeightLevel * data.selected.family.enncard ≤
        data.selectedWeight := assembly.selectedWeightLevel_mul_sourceCard_le
    _ = ∑ target : Fin data.isotropicCleanupFinalFamily.card,
          weight target := hselectedWeight
    _ ≤ (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          assembly.sourceSchedule.scaleCount *
        ∑ index ∈ assembly.selection.selected, weight index :=
      assembly.selection.retained_weight
    _ = (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          assembly.sourceSchedule.scaleCount *
        ∑ index : Fin separated.family.card,
          weight (separated.embedding index) := by
      have hsum :
          (∑ index : Fin separated.family.card,
            weight (separated.embedding index)) =
          ∑ index ∈ assembly.selection.selected, weight index := by
        have himageSum :
            (∑ index : Fin separated.family.card,
              weight (separated.embedding index)) =
            ∑ index ∈ Finset.image separated.embedding
                (Finset.univ : Finset (Fin separated.family.card)),
              weight index :=
          (Finset.sum_image
            (fun first _ second _ heq =>
              separated.embedding.injective heq)).symm
        have himage : Finset.image separated.embedding
            (Finset.univ : Finset (Fin separated.family.card)) =
          assembly.selection.selected := by
          change Finset.image
              (assembly.selection.selected.orderEmbOfFin rfl)
              (Finset.univ : Finset
                (Fin assembly.selection.selected.card)) =
            assembly.selection.selected
          exact Finset.image_orderEmbOfFin_univ
            assembly.selection.selected rfl
        exact himageSum.trans (congrArg
          (fun indices => ∑ index ∈ indices, weight index) himage)
      rw [hsum]
    _ ≤ (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          assembly.sourceSchedule.scaleCount *
        (((8 : ENNReal) *
          (Nat.log 2 (2 * separated.family.card) + 1 : ENNReal) ^
            (assembly.sourceSchedule.scaleCount +
              assembly.sourceSchedule.scaleCount + 1)) *
          ∑ index ∈ assembly.joint.selected,
            weight (separated.embedding index)) := by
      gcongr
      exact assembly.joint.retained_weight
    _ ≤ (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          assembly.sourceSchedule.scaleCount *
        (((8 : ENNReal) *
          (Nat.log 2 (2 * separated.family.card) + 1 : ENNReal) ^
            (assembly.sourceSchedule.scaleCount +
              assembly.sourceSchedule.scaleCount + 1)) *
          ((2 * data.selectedWeightLevel) * finalFine.family.enncard)) := by
      gcongr
    _ = assembly.retentionConstant * finalFine.family.enncard := by
      unfold retentionConstant
      ring

/-- The two weighted complete-fiber selections retain at least one final
isotropic tube.  Positivity comes from the source regularization's selected
weight level, while `source_cardinality_retention` rules out a zero final
cardinality. -/
theorem final_family_nonempty
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
        assembly.joint.selected).family.Nonempty := by
  have hsourceCard : 0 < data.selected.family.enncard := by
    change (0 : ENNReal) < (data.selected.family.card : ENNReal)
    exact_mod_cast data.selected_nonempty
  have hlhs : 0 <
      data.selectedWeightLevel * data.selected.family.enncard :=
    ENNReal.mul_pos data.selectedWeightLevel_pos.ne' hsourceCard.ne'
  have hretained := assembly.source_cardinality_retention
  by_contra hempty
  have hcardZero :
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family.enncard = 0 := by
    change ((assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
        assembly.joint.selected).family.card : ENNReal) = 0
    have hnat : (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
        assembly.joint.selected).family.card = 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hempty
    simp [hnat]
  rw [hcardZero, mul_zero] at hretained
  exact (not_le_of_gt hlhs) hretained

/-- Every final quotient index still lies in the dyadic weight band selected
by the cleanup-supported source regularization.  Since that weight is the
literal volume of the synchronized final target carrier, the final shading
has the sharp denominator-free density floor below. -/
theorem selectedWeightLevel_mul_finalCard_le_finalShading_mass
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    data.selectedWeightLevel *
        (assembly.quotient.jointlyRegularizedFine
          (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
            assembly.joint.selected).family.enncard ≤
      (assembly.joint.finalTargetShading
        data.isotropicCleanupFinalShading).mass := by
  let final := assembly.quotient.jointlyRegularizedFine
    (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
      assembly.joint.selected
  change data.selectedWeightLevel * (final.family.card : ENNReal) ≤
    ∑ index : Fin final.family.card,
      MeasureTheory.volume
        (data.isotropicCleanupFinalShading.carrier
          (assembly.joint.finalTargetIndex index))
  calc
    data.selectedWeightLevel * (final.family.card : ENNReal) =
        ∑ _index : Fin final.family.card, data.selectedWeightLevel := by
          simp [mul_comm]
    _ ≤ ∑ index : Fin final.family.card,
        cleanup.sourceWeight
          (data.selected.embedding
            (assembly.joint.finalTargetIndex index)) := by
      apply Finset.sum_le_sum
      intro index _
      exact (data.selected_weight_band
        (assembly.joint.finalTargetIndex index)).1
    _ = ∑ index : Fin final.family.card,
        MeasureTheory.volume
          (data.isotropicCleanupFinalShading.carrier
            (assembly.joint.finalTargetIndex index)) := by
      apply Finset.sum_congr rfl
      intro index _
      exact data.selected_sourceWeight_eq_finalShading_volume
        (assembly.joint.finalTargetIndex index)

/-- The exact per-coordinate constant consumed by the final isotropic
actual-John CWA transfer. -/
def nearbyCWACoordinateBudget
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (coordinate : Fin assembly.sourceSchedule.scaleCount) : ENNReal :=
  max
    (16 * ((assembly.sourceSchedule.scaleCount +
        assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
      (Nat.log 2
        (2 * (assembly.quotient.separatedFine
          (pureWZ2IsotropicCleanupJointWeight data)
          assembly.selection).family.card) + 1 : ENNReal) ^
        (assembly.sourceSchedule.scaleCount +
          assembly.sourceSchedule.scaleCount))
    (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
      ((432 : ENNReal) *
        Kakeya.realRpowENN (assembly.quotient.callerRho coordinate) 2 *
        ENNReal.ofReal (1 + 2 * assembly.quotient.callerRho coordinate) *
        ENNReal.ofReal (1 / (scale ^ 3 *
          assembly.representative.sourceRho coordinate ^ 2))) *
      ((data.selectedWeightLevel⁻¹ *
        (data.outputConstant * assembly.retentionConstant *
          (16 * ((assembly.sourceSchedule.scaleCount +
              assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (assembly.quotient.separatedFine
                (pureWZ2IsotropicCleanupJointWeight data)
                assembly.selection).family.card) + 1 : ENNReal) ^
              (assembly.sourceSchedule.scaleCount +
                assembly.sourceSchedule.scaleCount)))) *
        data.outputConstant))

/-- Replace the internal selected dyadic level in the named final-isotropic
coordinate budget by an explicit lower floor.  Downstream scalar arithmetic
can therefore depend only on a proved power floor, not on the existential
regularization witness. -/
theorem nearbyCWACoordinateBudget_le_of_level_floor
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant targetConstant levelFloor : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (hfloor : levelFloor ≤ data.selectedWeightLevel)
    (hbudget : ∀ coordinate,
      max
        (16 * ((assembly.sourceSchedule.scaleCount +
            assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * (assembly.quotient.separatedFine
              (pureWZ2IsotropicCleanupJointWeight data)
              assembly.selection).family.card) + 1 : ENNReal) ^
            (assembly.sourceSchedule.scaleCount +
              assembly.sourceSchedule.scaleCount))
        (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
          ((432 : ENNReal) *
            Kakeya.realRpowENN (assembly.quotient.callerRho coordinate) 2 *
            ENNReal.ofReal (1 + 2 * assembly.quotient.callerRho coordinate) *
            ENNReal.ofReal (1 / (scale ^ 3 *
              assembly.representative.sourceRho coordinate ^ 2))) *
          ((levelFloor⁻¹ *
            (data.outputConstant * assembly.retentionConstant *
              (16 * ((assembly.sourceSchedule.scaleCount +
                  assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
                (Nat.log 2
                  (2 * (assembly.quotient.separatedFine
                    (pureWZ2IsotropicCleanupJointWeight data)
                    assembly.selection).family.card) + 1 : ENNReal) ^
                  (assembly.sourceSchedule.scaleCount +
                    assembly.sourceSchedule.scaleCount)))) *
            data.outputConstant)) ≤ targetConstant) :
    ∀ coordinate,
      assembly.nearbyCWACoordinateBudget coordinate ≤ targetConstant := by
  intro coordinate
  have hinv : data.selectedWeightLevel⁻¹ ≤ levelFloor⁻¹ :=
    (ENNReal.inv_le_inv).2 hfloor
  unfold nearbyCWACoordinateBudget
  apply (max_le_max (le_refl _) ?_).trans (hbudget coordinate)
  gcongr

theorem nearbyCWACoordinateBudget_ne_top
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (coordinate : Fin assembly.sourceSchedule.scaleCount) :
    assembly.nearbyCWACoordinateBudget coordinate ≠ ⊤ := by
  have houtputTop : data.outputConstant ≠ ⊤ :=
    data.cwa_nearby.2.1.2
  have hweightInvTop : data.selectedWeightLevel⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr data.selectedWeightLevel_pos.ne'
  have hcoverTop :
      16 * ((assembly.sourceSchedule.scaleCount +
          assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
        (Nat.log 2
          (2 * (assembly.quotient.separatedFine
            (pureWZ2IsotropicCleanupJointWeight data)
            assembly.selection).family.card) + 1 : ENNReal) ^
          (assembly.sourceSchedule.scaleCount +
            assembly.sourceSchedule.scaleCount) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (by norm_num) (by simp)
    · exact ENNReal.pow_ne_top (by simp)
  have hretentionTop : assembly.retentionConstant ≠ ⊤ := by
    unfold retentionConstant
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (show
        (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ≠ ⊤ by
          simp))
        (ENNReal.mul_ne_top (show (8 : ENNReal) ≠ ⊤ by norm_num) <|
          ENNReal.pow_ne_top (show
            (Nat.log 2
              (2 * (assembly.quotient.separatedFine
                (pureWZ2IsotropicCleanupJointWeight data)
                assembly.selection).family.card) + 1 : ENNReal) ≠ ⊤ by simp)
        ))
      (ENNReal.mul_ne_top (show (2 : ENNReal) ≠ ⊤ by norm_num)
        data.selectedWeightLevel_ne_top)
  have hgeometricTop :
      ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  let scaleFactor : ENNReal :=
      (432 : ENNReal) *
          Kakeya.realRpowENN (assembly.quotient.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * assembly.quotient.callerRho coordinate) *
          ENNReal.ofReal (1 / (scale ^ 3 *
            assembly.representative.sourceRho coordinate ^ 2))
  have hscaleFactorTop : scaleFactor ≠ ⊤ := by
    dsimp only [scaleFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (show (432 : ENNReal) ≠ ⊤ by norm_num)
          (by simp [Kakeya.realRpowENN]))
        ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  let weightBudget : ENNReal :=
    (data.selectedWeightLevel⁻¹ *
        (data.outputConstant * assembly.retentionConstant *
          (16 * ((assembly.sourceSchedule.scaleCount +
              assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (assembly.quotient.separatedFine
                (pureWZ2IsotropicCleanupJointWeight data)
                assembly.selection).family.card) + 1 : ENNReal) ^
              (assembly.sourceSchedule.scaleCount +
                assembly.sourceSchedule.scaleCount)))) *
      data.outputConstant
  have hweightTop : weightBudget ≠ ⊤ := by
    dsimp only [weightBudget]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hweightInvTop
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top houtputTop hretentionTop) hcoverTop))
      houtputTop
  unfold nearbyCWACoordinateBudget
  change max _ (ENNReal.ofReal _ * scaleFactor * weightBudget) ≠ ⊤
  exact max_ne_top hcoverTop <|
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hgeometricTop hscaleFactorTop)
      hweightTop

/-- Choose one finite target constant that simultaneously pays the isotropic
scale-window loss and every coordinate's packet constant. -/
theorem exists_nearbyCWA_targetConstant
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (hsourceScheduleTop : sourceScheduleConstant ≠ ⊤) :
    Nonempty (PureWZ2FiniteBudgetEnvelope
      (isotropicQuotientScaleWindowConstant scale sourceScheduleConstant)
      assembly.nearbyCWACoordinateBudget) := by
  apply exists_finite_budget_envelope
  · unfold isotropicQuotientScaleWindowConstant
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsourceScheduleTop, by norm_num⟩
  · exact assembly.nearbyCWACoordinateBudget_ne_top

/-- The completed final-isotropic quotient assembly exposes public nearby CWA
on its ultimate joint complete-fiber subfamily. -/
theorem toNearbyCWA
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant targetConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (hscale : 1 ≤ scale) (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass data.selected.family)
    (hsourceBase : ∀ source, ‖(data.selected.family.tube source).base‖ ≤ 5)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (hscaleBudget : isotropicQuotientScaleWindowConstant
      scale sourceScheduleConstant ≤ targetConstant)
    (hconstantBudget : ∀ coordinate, max
      (16 * ((assembly.sourceSchedule.scaleCount +
          assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
        (Nat.log 2
          (2 * (assembly.quotient.separatedFine
            (pureWZ2IsotropicCleanupJointWeight data)
            assembly.selection).family.card) + 1 : ENNReal) ^
          (assembly.sourceSchedule.scaleCount +
            assembly.sourceSchedule.scaleCount))
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (assembly.quotient.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * assembly.quotient.callerRho coordinate) *
          ENNReal.ofReal (1 / (scale ^ 3 *
            assembly.representative.sourceRho coordinate ^ 2))) *
        ((data.selectedWeightLevel⁻¹ *
          (data.outputConstant * assembly.retentionConstant *
            (16 * ((assembly.sourceSchedule.scaleCount +
                assembly.sourceSchedule.scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (assembly.quotient.separatedFine
                  (pureWZ2IsotropicCleanupJointWeight data)
                  assembly.selection).family.card) + 1 : ENNReal) ^
                (assembly.sourceSchedule.scaleCount +
                  assembly.sourceSchedule.scaleCount)))) *
          data.outputConstant)) ≤ targetConstant) :
    WZ2PaperPureCWAAtNearbyScales
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family targetConstant := by
  apply assembly.joint.toIsotropicNearbyCWA assembly.sourceSchedule center
    hscale hcenter hsourceDelta hsourceTarget htargetDelta hsourceLine
    hsourceBase (htargetFamilyTube := by intro target; rfl)
    (normalizationWeight := data.selectedWeightLevel)
    (retentionConstant := assembly.retentionConstant)
    data.selectedWeightLevel_pos.ne' data.selectedWeightLevel_ne_top
    assembly.source_cardinality_retention htargetFinite
    data.isotropicCleanupFinalFamily_distinct assembly.sourceRho_eq
    assembly.callerRho_eq hscaleBudget hconstantBudget

/-- Final nearby-CWA together with the finite target constant chosen to cover
the scale-window loss and every scheduled coordinate. -/
structure PureWZ2AutoIsotropicNearbyCWAData
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) where
  envelope : PureWZ2FiniteBudgetEnvelope
    (isotropicQuotientScaleWindowConstant scale sourceScheduleConstant)
    assembly.nearbyCWACoordinateBudget
  nearby_cwa : WZ2PaperPureCWAAtNearbyScales
    (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
        assembly.joint.selected).family envelope.targetConstant

/-- Choose the finite target constant and produce final nearby CWA without
exposing the finite maximum calculation to the terminal caller. -/
theorem toNearbyCWAAuto
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (hscale : 1 ≤ scale) (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass data.selected.family)
    (hsourceBase : ∀ source, ‖(data.selected.family.tube source).base‖ ≤ 5)
    (hsourceScheduleTop : sourceScheduleConstant ≠ ⊤) :
    Nonempty (PureWZ2AutoIsotropicNearbyCWAData assembly) := by
  let envelope := Classical.choice <|
    assembly.exists_nearbyCWA_targetConstant hsourceScheduleTop
  have nearby := assembly.toNearbyCWA hscale hcenter hsourceDelta
    hsourceTarget htargetDelta hsourceLine hsourceBase
    envelope.target_finite envelope.scale_le (by
      intro coordinate
      simpa [nearbyCWACoordinateBudget] using envelope.coordinate_le coordinate)
  exact ⟨{ envelope := envelope, nearby_cwa := nearby }⟩

/-- The final joint CWA family as a genuine subfamily of the canonical
midpoint-centered isotropic family. -/
def finalTargetSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    Kakeya.Streamlined.TubeSubfamily data.isotropicCleanupFinalFamily :=
  assembly.joint.finalTargetTubeSubfamily

/-- The source tubes paired index-for-index with the final joint CWA family. -/
def finalSourceSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    Kakeya.Streamlined.TubeSubfamily data.selected.family :=
  assembly.joint.finalSourceTubeSubfamily

/-- Restrict the retained target shading to precisely the final family on
which `toNearbyCWA` is proved. -/
def finalShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperTubeShading
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family :=
  assembly.joint.finalTargetShading data.isotropicCleanupFinalShading

/-- The final quotient family inherits the line class recorded by every
representative-parent datum. -/
theorem final_line_class
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) :
    WZ1PaperIsLineClass
      (assembly.quotient.jointlyRegularizedFine
        (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family := by
  let coordinate : Fin assembly.sourceSchedule.scaleCount :=
    ⟨0, assembly.sourceSchedule.scaleCount_pos⟩
  exact assembly.joint.finalTarget_line_class
    (assembly.representative.parentData coordinate).target_line_class

/-- Cubicality survives both source-side regularization and the two final
complete-fiber selections. -/
theorem finalShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (hcubical : WZ1PaperIsCubicalShading targetShading) :
    WZ1PaperIsCubicalShading assembly.finalShading := by
  apply assembly.joint.finalTargetShading_cubical
  intro index point hpoint other hother
  change point ∈ targetShading.carrier
      (cleanup.sourceIndex
        (data.isotropicCleanupTargetPreimage index)) at hpoint
  change other ∈ targetShading.carrier
      (cleanup.sourceIndex
        (data.isotropicCleanupTargetPreimage index))
  exact hcubical _ point hpoint hother

/-- A scalar comparison with the second selected weight level is sufficient
for density on the final quotient family.  All family-selection losses have
already been paid before this boundary. -/
theorem finalShading_dense_of_selectedWeightLevel
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant density : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 24)
    (hbudget : density *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN targetDelta 2) ≤
      data.selectedWeightLevel) :
    assembly.finalShading.IsLambdaDense density := by
  apply pureWZ2_affineDiagonal_dense_of_mass_budget assembly.finalShading
    htargetDelta htargetDeltaSmall assembly.final_line_class
  calc
    density *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN targetDelta 2 *
              (assembly.quotient.jointlyRegularizedFine
                (pureWZ2IsotropicCleanupJointWeight data)
                  assembly.selection assembly.joint.selected).family.enncard) =
        (density *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN targetDelta 2)) *
              (assembly.quotient.jointlyRegularizedFine
                (pureWZ2IsotropicCleanupJointWeight data)
                  assembly.selection assembly.joint.selected).family.enncard := by
            ring
    _ ≤ data.selectedWeightLevel *
          (assembly.quotient.jointlyRegularizedFine
            (pureWZ2IsotropicCleanupJointWeight data)
              assembly.selection assembly.joint.selected).family.enncard := by
        gcongr
    _ ≤ assembly.finalShading.mass :=
      assembly.selectedWeightLevel_mul_finalCard_le_finalShading_mass

@[simp] theorem finalShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {center : Point3} {scale : ℝ}
    {targetShading : WZ1PaperTubeShading
      (pureWZ2IsotropicCenteredPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2IsotropicDistinctCleanupData
      sourceFamily center scale targetShading}
    {data : PureWZ2IsotropicCleanupSourceRegularizationData cleanup
      sourceConstant scheduleConstant normalizationWeight levelCount}
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin (assembly.quotient.jointlyRegularizedFine
      (pureWZ2IsotropicCleanupJointWeight data) assembly.selection
        assembly.joint.selected).family.card) :
    assembly.finalShading.carrier index =
      data.isotropicCleanupFinalShading.carrier
        (assembly.joint.finalTargetIndex index) := rfl

end PureWZ2IsotropicCleanupQuotientAssemblyData

end Kakeya.Assouad

end
