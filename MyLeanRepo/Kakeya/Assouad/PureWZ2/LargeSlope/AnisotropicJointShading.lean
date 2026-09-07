import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicQuotientScheduleCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction

/-!
# Shadings synchronized with the anisotropic joint regularization

The quotient/source-parent regularization produces one final target family,
but its CWA module deliberately does not mention shadings.  This file records
the two restrictions which have exactly the same final index type: the target
shading used by the public nearby-scale CWA and the corresponding source
shading used by affine local-grain transport.  In particular, no family is
reconstructed from an arbitrary union representation.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- The final joint family as an actual subfamily of the synchronized target
family. -/
def finalTargetTubeSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection) :
    Kakeya.Streamlined.TubeSubfamily targetFine :=
  (schedule.separatedFine weight selection).toTubeSubfamily.comp
    (schedule.jointlyRegularizedFine
      weight selection data.selected).toTubeSubfamily

/-- The source tubes paired with the final joint target family.  This uses the
same final index type and the injective source provenance already used by the
actual-John packet construction. -/
def finalSourceTubeSubfamily
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection) :
    Kakeya.Streamlined.TubeSubfamily sourceFine where
  family :=
    { card := (schedule.jointlyRegularizedFine
        weight selection data.selected).family.card
      tube := fun index => sourceFine.tube (data.finalSourceIndex index) }
  embedding := data.finalSourceIndex
  tube_eq _ := rfl

/-- Restrict a target shading to the exact family carrying the joint nearby
CWA conclusion. -/
def finalTargetShading
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (targetShading : WZ1PaperTubeShading targetFine) :
    WZ1PaperTubeShading
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family :=
  restrictPaperShading data.finalTargetTubeSubfamily targetShading

/-- Restrict the synchronized source shading with the same final indices. -/
def finalSourceShading
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (sourceShading : WZ1PaperTubeShading sourceFine) :
    WZ1PaperTubeShading data.finalSourceTubeSubfamily.family :=
  restrictPaperShading data.finalSourceTubeSubfamily sourceShading

@[simp] theorem finalTargetTubeSubfamily_embedding
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (index : Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card) :
    data.finalTargetTubeSubfamily.embedding index =
      data.finalTargetIndex index := rfl

@[simp] theorem finalTargetShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (targetShading : WZ1PaperTubeShading targetFine)
    (index : Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card) :
    (data.finalTargetShading targetShading).carrier index =
      targetShading.carrier (data.finalTargetIndex index) := rfl

@[simp] theorem finalSourceShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (sourceShading : WZ1PaperTubeShading sourceFine)
    (index : Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card) :
    (data.finalSourceShading sourceShading).carrier index =
      sourceShading.carrier (data.finalSourceIndex index) := rfl

theorem finalTargetShading_union_subset
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (targetShading : WZ1PaperTubeShading targetFine) :
    (data.finalTargetShading targetShading).union ⊆
      targetShading.union :=
  restrictPaperShading_union_subset data.finalTargetTubeSubfamily
    targetShading

/-- The same restriction identity in the other direction: every point in the
final union is carried by a unique retained ambient target index. -/
theorem finalTargetShading_union_iff
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (targetShading : WZ1PaperTubeShading targetFine)
    (point : Point3) :
    point ∈ (data.finalTargetShading targetShading).union ↔
      ∃ index : Fin (schedule.jointlyRegularizedFine
          weight selection data.selected).family.card,
        point ∈ targetShading.carrier (data.finalTargetIndex index) := by
  rfl

theorem finalSourceShading_union_subset
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (sourceShading : WZ1PaperTubeShading sourceFine) :
    (data.finalSourceShading sourceShading).union ⊆
      sourceShading.union :=
  restrictPaperShading_union_subset data.finalSourceTubeSubfamily
    sourceShading

theorem finalSourceShading_union_iff
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (sourceShading : WZ1PaperTubeShading sourceFine)
    (point : Point3) :
    point ∈ (data.finalSourceShading sourceShading).union ↔
      ∃ index : Fin (schedule.jointlyRegularizedFine
          weight selection data.selected).family.card,
        point ∈ sourceShading.carrier (data.finalSourceIndex index) := by
  rfl

theorem finalTargetShading_cubical
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    {targetShading : WZ1PaperTubeShading targetFine}
    (hcubical : WZ1PaperIsCubicalShading targetShading) :
    WZ1PaperIsCubicalShading (data.finalTargetShading targetShading) :=
  restrictPaperShading_cubical data.finalTargetTubeSubfamily hcubical

theorem finalTarget_line_class
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (hline : WZ1PaperIsLineClass targetFine) :
    WZ1PaperIsLineClass
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family :=
  hline.subfamily data.finalTargetTubeSubfamily

/-- The final joint target shading has exactly the weighted mass used by the
second simultaneous selection. -/
theorem selected_weight_eq_factor_mul_finalTargetShading_mass
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {targetShading : WZ1PaperTubeShading targetFine}
    {factor : ENNReal}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (hweight : ∀ target, weight target = factor *
      MeasureTheory.volume (targetShading.carrier target)) :
    (∑ index ∈ data.selected,
        weight ((schedule.separatedFine weight selection).embedding index)) =
      factor * (data.finalTargetShading targetShading).mass := by
  change _ = factor *
    (∑ index : Fin
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family.card,
      MeasureTheory.volume
        (targetShading.carrier (data.finalTargetIndex index)))
  let final := schedule.jointlyRegularizedFine
    weight selection data.selected
  have hsum :
      (∑ index : Fin final.family.card,
          MeasureTheory.volume
            (targetShading.carrier (data.finalTargetIndex index))) =
        ∑ index ∈ Finset.image final.embedding
            (Finset.univ : Finset (Fin final.family.card)),
          (MeasureTheory.volume
            (targetShading.carrier
              ((schedule.separatedFine weight selection).embedding index)) :
            ENNReal) := by
    have hinjective : Function.Injective final.embedding :=
      final.embedding.injective
    exact (Finset.sum_image
      (f := fun index =>
        (MeasureTheory.volume
          (targetShading.carrier
            ((schedule.separatedFine weight selection).embedding index)) :
          ENNReal))
      (fun first _ second _ heq => hinjective heq)).symm
  have himage : Finset.image final.embedding
      (Finset.univ : Finset (Fin final.family.card)) = data.selected := by
    change Finset.image (data.selected.orderEmbOfFin rfl)
        (Finset.univ : Finset (Fin data.selected.card)) = data.selected
    exact Finset.image_orderEmbOfFin_univ data.selected rfl
  rw [hsum, Finset.mul_sum, himage]
  apply Finset.sum_congr rfl
  intro index hindex
  exact hweight _

/-- The final target tube is exactly the triangular retubing of its final
source partner.  This is the family-level identity needed by both the exact
normal field and the quotient CWA proof. -/
theorem finalTarget_tube_eq_anisotropicPaperTargetTube
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (g : SlopeFunction) (c d m : ℝ) (center : Point3)
    (hcd : c < d) (hm : 0 < m)
    (htargetTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
    (index : Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card) :
    (schedule.jointlyRegularizedFine
        weight selection data.selected).family.tube index =
      anisotropicPaperTargetTube g c d m center targetDelta hcd hm
        (data.finalSourceTubeSubfamily.family.tube index) := by
  rw [(schedule.jointlyRegularizedFine
      weight selection data.selected).tube_eq]
  rw [(schedule.separatedFine weight selection).tube_eq]
  rw [htargetTube]
  rfl

/-- A synchronized source local-grain field restricts to exactly the source
family indexed by the final joint target family. -/
def finalSourceLocalGrains
    {sourceDelta targetDelta sigma : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {C : ENNReal}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C) :
    PureWZ2LocalGrainData
      (data.finalSourceShading sourceShading) sigma C :=
  sourceLocal.subfamily data.finalSourceTubeSubfamily

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
