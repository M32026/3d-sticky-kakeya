import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalCleanupSourceReregularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalRepresentativeSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicJointShading

/-!
# Quotient schedule for the affine-diagonal cleanup

This joins the synchronized twice-regularized source and affine target
families to the map-independent representative, quotient, and simultaneous
complete-fiber selection machinery.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory
open PureWZ2ExternalWeightRegularizationData

attribute [local instance] Classical.propDecidable

/-- Retained affine target weight attached to its synchronized selected
source index. -/
def pureWZ2AffineDiagonalCleanupJointWeight
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
    (index : Fin (cleanupTargetSubfamily (cleanup := cleanup) data).family.card) :
    ENNReal :=
  pureWZ2AffineDiagonalCleanupIndicator cleanup (data.selected.embedding index)

/-- The finite source schedule, affine representative parents, quotient
parents, and both complete-fiber selections in one package. -/
structure PureWZ2AffineDiagonalCleanupQuotientAssemblyData
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
    (sourceScheduleConstant : ENNReal) (parentLevelCount : ℕ) where
  sourceSchedule : PureWZ2FiniteNearbyScheduleData
    (family := data.selected.family) data.outputConstant
      sourceScheduleConstant parentLevelCount
  representative : PureWZ2FiniteRepresentativeParentScheduleData
    (cleanupTargetSubfamily (cleanup := cleanup) data).family
    (Equiv.refl (Fin data.selected.family.card)) data.outputConstant
      sourceSchedule.scaleCount
  quotient : PureWZ2FiniteAnisotropicParentQuotientScheduleData representative
  selection : PureWZ2FiniteStrongParentSelectionData
    (pureWZ2AffineDiagonalCleanupJointWeight data) sourceSchedule.scaleCount
    quotient.Parent
    (fun coordinate target =>
      (quotient.quotient coordinate).assignedParent target)
    quotient.conflict pureWZ2AnisotropicQuotientCenterConflictDegree
  joint : quotient.PureWZ2AnisotropicJointRegularizationData
    (pureWZ2AffineDiagonalCleanupJointWeight data) selection
  sourceRho_eq : ∀ coordinate, representative.sourceRho coordinate =
    (sourceSchedule.witness coordinate).rho
  callerRho_eq : ∀ coordinate, quotient.callerRho coordinate =
    affineDiagonalQuotientCallerScale affineScale.targetDelta
      (representative.sourceRho coordinate)

/-- Assemble the affine quotient schedule from the synchronized source and
target families. -/
theorem pureWZ2_affineDiagonal_cleanup_quotient_assembly
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
    (sourceScheduleConstant : ENNReal)
    (parentLevelCount : ℕ)
    (hsourceTwo : 2 < data.outputConstant)
    (hsourceDeltaOne : delta ≤ 1)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      data.outputConstant ^ parentLevelCount)
    (hsourceScheduleConstant : data.outputConstant * data.outputConstant ≤
      sourceScheduleConstant) :
    Nonempty (PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount) := by
  rcases pureWZ2_finite_pure_nearby_schedule parentLevelCount
      data.cwa_nearby.1 hsourceDeltaOne hsourceTwo
      data.cwa_nearby.2.1.2 hlevels hsourceScheduleConstant data.cwa_nearby with
    ⟨sourceSchedule⟩
  let representative := affineDiagonalRepresentativeParentSchedule
    data sourceSchedule
  let quotient := affineDiagonalParentQuotientSchedule representative
    (fun _ => rfl)
  rcases quotient.simultaneouslySeparate
      (pureWZ2AffineDiagonalCleanupJointWeight data) with ⟨selection⟩
  rcases quotient.simultaneouslyRegularizeQuotientAndSource
      (pureWZ2AffineDiagonalCleanupJointWeight data) selection with ⟨joint⟩
  exact ⟨{
    sourceSchedule := sourceSchedule
    representative := representative
    quotient := quotient
    selection := selection
    joint := joint
    sourceRho_eq := fun _ => rfl
    callerRho_eq := fun _ => rfl
  }⟩

namespace PureWZ2AffineDiagonalCleanupQuotientAssemblyData

/-- The positive selected-weight level controls the source cardinality. -/
theorem selectedWeightLevel_mul_sourceCard_le
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
    data.selectedWeightLevel * data.selected.family.enncard ≤
      data.selectedWeight := by
  rw [data.selectedWeight_eq]
  change data.selectedWeightLevel *
      (data.selected.family.card : ENNReal) ≤
    ∑ index : Fin data.selected.family.card,
      pureWZ2AffineDiagonalCleanupIndicator cleanup
        (data.selected.embedding index)
  calc
    data.selectedWeightLevel * (data.selected.family.card : ENNReal) =
        ∑ _index : Fin data.selected.family.card,
          data.selectedWeightLevel := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun index _ =>
      (data.selected_weight_band index).1

/-- Total cardinality loss of the quotient-center and joint fiber
selections. -/
def retentionConstant
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
      sourceScheduleConstant parentLevelCount) : ENNReal :=
  (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
      assembly.sourceSchedule.scaleCount *
    ((8 : ENNReal) *
      (Nat.log 2
        (2 * (assembly.quotient.separatedFine
          (pureWZ2AffineDiagonalCleanupJointWeight data)
          assembly.selection).family.card) + 1 : ENNReal) ^
        (assembly.sourceSchedule.scaleCount +
          assembly.sourceSchedule.scaleCount + 1)) *
    (2 * data.selectedWeightLevel)

/-- Both complete-fiber selections retain enough source cardinality for the
packetwise actual-John estimate. -/
theorem source_cardinality_retention
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
    data.selectedWeightLevel * data.selected.family.enncard ≤
      assembly.retentionConstant *
        (assembly.quotient.jointlyRegularizedFine
          (pureWZ2AffineDiagonalCleanupJointWeight data) assembly.selection
          assembly.joint.selected).family.enncard := by
  let weight := pureWZ2AffineDiagonalCleanupJointWeight data
  let separated := assembly.quotient.separatedFine weight assembly.selection
  let finalFine := assembly.quotient.jointlyRegularizedFine
    weight assembly.selection assembly.joint.selected
  have hselectedWeight : data.selectedWeight =
      ∑ target : Fin
          (cleanupTargetSubfamily (cleanup := cleanup) data).family.card,
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
    _ = ∑ target : Fin
          (cleanupTargetSubfamily (cleanup := cleanup) data).family.card,
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
          exact Finset.image_orderEmbOfFin_univ assembly.selection.selected rfl
        exact himageSum.trans
          (congrArg (fun indices => ∑ index ∈ indices, weight index) himage)
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

end PureWZ2AffineDiagonalCleanupQuotientAssemblyData

end Kakeya.Assouad

end
