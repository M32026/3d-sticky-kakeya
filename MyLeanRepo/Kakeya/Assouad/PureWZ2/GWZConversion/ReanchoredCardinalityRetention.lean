import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteAnchoredSelection
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Cardinality retention for reanchored families

The target family may have different carriers from the source family, so it
is not a tube subfamily in the geometric sense.  Since both are indexed
families of tubes at the same radius, density and shaded-mass retention still
give indexed-cardinality retention after cancelling the common tube volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
Dense shaded mass and finite mass loss imply cardinality retention between
arbitrary same-radius tube families.
-/
theorem pureWZ2_reanchored_cardinality_retention
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (source target : Kakeya.Streamlined.TubeFamily delta)
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (targetShading : Kakeya.Streamlined.TubeShading target)
    (density loss : ENNReal)
    (density_ne_zero : density ≠ 0)
    (density_ne_top : density ≠ ⊤)
    (source_dense : sourceShading.IsLambdaDense density)
    (mass_retained :
      sourceShading.mass ≤ loss * targetShading.mass) :
    source.enncard ≤
      (density⁻¹ * loss) * target.enncard := by
  let tubeVolume := Kakeya.deltaTubeVolume delta
  have htubeVolumePos :
      0 < tubeVolume :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).1
  have htubeVolumeTop :
      tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).2
  have htargetShading :
      targetShading.mass ≤ target.toBodyFamily.mass := by
    apply Finset.sum_le_sum
    intro index _
    exact measure_mono (targetShading.subset_body index)
  have hsourceMass :
      source.toBodyFamily.mass =
        source.enncard * tubeVolume := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have htargetMass :
      target.toBodyFamily.mass =
        target.enncard * tubeVolume := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have hwithVolume :
      (density * source.enncard) * tubeVolume ≤
        (loss * target.enncard) * tubeVolume := by
    calc
      (density * source.enncard) * tubeVolume =
          density * source.toBodyFamily.mass := by
        rw [hsourceMass]
        ring
      _ ≤ sourceShading.mass := source_dense
      _ ≤ loss * targetShading.mass := mass_retained
      _ ≤ loss * target.toBodyFamily.mass := by
        gcongr
      _ = (loss * target.enncard) * tubeVolume := by
        rw [htargetMass]
        ring
  have hweighted :
      density * source.enncard ≤
        loss * target.enncard :=
    (ENNReal.mul_le_mul_iff_left
      htubeVolumePos.ne' htubeVolumeTop).mp hwithVolume
  calc
    source.enncard =
        density⁻¹ * (density * source.enncard) := by
      rw [ENNReal.inv_mul_cancel_left
        density_ne_zero density_ne_top]
    _ ≤ density⁻¹ * (loss * target.enncard) := by
      gcongr
    _ = (density⁻¹ * loss) * target.enncard := by
      ring

/-- The selected shading associated to one final anchored selection. -/
def PureWZ2FiniteAnchoredSelectionData.selectedShading
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    {fine : PureWZ2LocalizedDistinctReanchoringData sourceShading}
    {coordinateCount : ℕ}
    {constant : ENNReal}
    {scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta}
    {scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) constant}
    {oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate)}
    {coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate)}
    {weight : Fin fine.family.card → ENNReal}
    (selection :
      PureWZ2FiniteAnchoredSelectionData
        fine coordinateCount scale scaleData oneScale coloring weight) :
    Kakeya.Streamlined.TubeShading selection.selected.family :=
  selection.selected.toTubeSubfamily.restrictShading fine.shading

/--
The weighted simultaneous selection retains the same shading weights when
the regularization weight is the indexed shaded volume.
-/
theorem PureWZ2FiniteAnchoredSelectionData.shading_mass_retained
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    {fine : PureWZ2LocalizedDistinctReanchoringData sourceShading}
    {coordinateCount : ℕ}
    {constant : ENNReal}
    {scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta}
    {scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) constant}
    {oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate)}
    {coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate)}
    (selection :
      PureWZ2FiniteAnchoredSelectionData
        fine coordinateCount scale scaleData oneScale coloring
          (fun index => volume (fine.shading.carrier index))) :
    fine.shading.mass ≤
      selection.retentionConstant *
        selection.selectedShading.mass := by
  change
    (∑ index : Fin fine.family.card,
      volume (fine.shading.carrier index)) ≤
        selection.retentionConstant *
          ∑ index : Fin selection.selected.family.card,
            volume
              (fine.shading.carrier
                (selection.selected.embedding index))
  exact selection.retained_weight

/--
The complete localization, fine distinctness selection, and finite anchored
selection give one explicit global source-to-final cardinality ratio.
-/
theorem PureWZ2FiniteAnchoredSelectionData.source_cardinality_retention
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    {coordinateCount : ℕ}
    {constant : ENNReal}
    {scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta}
    {scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) constant}
    {oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate)}
    {coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate)}
    (selection :
      PureWZ2FiniteAnchoredSelectionData
        fine coordinateCount scale scaleData oneScale coloring
          (fun index => volume (fine.shading.carrier index)))
    (density : ENNReal)
    (density_ne_zero : density ≠ 0)
    (density_ne_top : density ≠ ⊤)
    (source_dense : sourceShading.IsLambdaDense density) :
    source.enncard ≤
      (density⁻¹ *
        ((fine.cellCount : ENNReal) *
          (fine.distinctnessLoss : ENNReal) *
          selection.retentionConstant)) *
        selection.selected.family.enncard := by
  have hmass :
      sourceShading.mass ≤
        ((fine.cellCount : ENNReal) *
          (fine.distinctnessLoss : ENNReal) *
          selection.retentionConstant) *
            selection.selectedShading.mass := by
    calc
      sourceShading.mass ≤
          (fine.cellCount : ENNReal) *
            (fine.distinctnessLoss : ENNReal) *
            fine.shading.mass :=
        fine.mass_retained
      _ ≤
          (fine.cellCount : ENNReal) *
            (fine.distinctnessLoss : ENNReal) *
            (selection.retentionConstant *
              selection.selectedShading.mass) := by
        gcongr
        exact selection.shading_mass_retained
      _ =
          ((fine.cellCount : ENNReal) *
            (fine.distinctnessLoss : ENNReal) *
            selection.retentionConstant) *
              selection.selectedShading.mass := by
        ring
  exact
    pureWZ2_reanchored_cardinality_retention
      hdelta hdeltaOne source selection.selected.family
      sourceShading selection.selectedShading
      density
      ((fine.cellCount : ENNReal) *
        (fine.distinctnessLoss : ENNReal) *
        selection.retentionConstant)
      density_ne_zero density_ne_top source_dense hmass

end Kakeya.Assouad

end
