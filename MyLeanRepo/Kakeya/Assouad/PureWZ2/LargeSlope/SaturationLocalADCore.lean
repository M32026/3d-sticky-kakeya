import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationPlaneMapCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.NearbyProjectionADTransfer

/-!
# Local AD transfer across a nearby saturation

This is the local-AD half of the saturation argument, separated from every
Section-6 assembly record.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Local paper AD survives saturation when the exact-image estimate is
available on the ball enlarged by two witness radii. -/
theorem PureWZ2SaturationPlaneMapCoreData.local_ad_of_exact
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error rho alpha pointBound : ℝ} {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapCoreData exactImage target rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (point : {point : Point3 // point ∈ target})
    (hexactAD : PureWZ2PaperADSet1
      (scalarProjection (rawNormal (data.sourcePoint point))
        (exactImage ∩
          Metric.closedBall (data.sourcePoint point : Point3)
            (Real.sqrt rho + 2 * witnessRadius)))
      rho alpha C)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ rho) :
    PureWZ2PaperADSet1
      (scalarProjection (data.planeMap point)
        (target ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
      rho alpha (6 * C) := by
  apply hexactAD.of_subset_cthickening
      (D := witnessRadius + pointBound * error)
  · rintro value ⟨targetPoint, htargetPoint, rfl⟩
    let targetSubtype : {point : Point3 // point ∈ target} :=
      ⟨targetPoint, htargetPoint.1⟩
    let sourceSubtype : {point : Point3 // point ∈ exactImage} :=
      data.sourcePoint targetSubtype
    have hsourceDistance :
        dist targetPoint (sourceSubtype : Point3) ≤ witnessRadius :=
      data.sourcePoint_dist targetSubtype
    have hsourceBall : (sourceSubtype : Point3) ∈
        Metric.closedBall (data.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius) := by
      rw [Metric.mem_closedBall]
      calc
        dist (sourceSubtype : Point3) (data.sourcePoint point : Point3)
            ≤ dist (sourceSubtype : Point3) targetPoint +
                dist targetPoint (point : Point3) +
                  dist (point : Point3) (data.sourcePoint point : Point3) := by
              exact dist_triangle4 (sourceSubtype : Point3) targetPoint
                (point : Point3) (data.sourcePoint point : Point3)
        _ ≤ witnessRadius + Real.sqrt rho + witnessRadius := by
              gcongr
              · simpa [dist_comm] using hsourceDistance
              · exact htargetPoint.2
              · exact data.sourcePoint_dist point
        _ = Real.sqrt rho + 2 * witnessRadius := by ring
    let sourceValue := inner ℝ (sourceSubtype : Point3)
      (rawNormal (data.sourcePoint point))
    refine ⟨sourceValue, ?_, ?_⟩
    · exact ⟨sourceSubtype, ⟨sourceSubtype.property, hsourceBall⟩, rfl⟩
    rw [Real.dist_eq]
    have hsplit :
        inner ℝ targetPoint (data.planeMap point) - sourceValue =
          inner ℝ (targetPoint - (sourceSubtype : Point3))
              (data.planeMap point) +
            inner ℝ (sourceSubtype : Point3)
              (data.planeMap point - rawNormal (data.sourcePoint point)) := by
      dsimp only [sourceValue]
      rw [inner_sub_left, inner_sub_right]
      ring
    rw [hsplit]
    calc
      |inner ℝ (targetPoint - (sourceSubtype : Point3))
          (data.planeMap point) +
        inner ℝ (sourceSubtype : Point3)
          (data.planeMap point - rawNormal (data.sourcePoint point))|
          ≤ |inner ℝ (targetPoint - (sourceSubtype : Point3))
                (data.planeMap point)| +
              |inner ℝ (sourceSubtype : Point3)
                (data.planeMap point - rawNormal (data.sourcePoint point))| :=
            abs_add_le _ _
      _ ≤ ‖targetPoint - (sourceSubtype : Point3)‖ *
              ‖data.planeMap point‖ +
            ‖(sourceSubtype : Point3)‖ *
              ‖data.planeMap point - rawNormal (data.sourcePoint point)‖ := by
            gcongr <;> apply abs_real_inner_le_norm
      _ ≤ witnessRadius * 1 + pointBound * error := by
            gcongr
            · simpa [dist_eq_norm] using hsourceDistance
            · exact data.planeMap_unit point |>.le
            · exact hexactBound sourceSubtype
            · exact data.planeMap_close point
      _ = witnessRadius + pointBound * error := by ring
  · positivity
  · exact hprojectionBudget

/-- Fixed-constant variant allowing twice the target base-scale projection
error. -/
theorem PureWZ2SaturationPlaneMapCoreData.local_ad_of_exact_two
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {witnessRadius error rho alpha pointBound : ℝ} {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapCoreData exactImage target rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (point : {point : Point3 // point ∈ target})
    (hexactAD : PureWZ2PaperADSet1
      (scalarProjection (rawNormal (data.sourcePoint point))
        (exactImage ∩
          Metric.closedBall (data.sourcePoint point : Point3)
            (Real.sqrt rho + 2 * witnessRadius)))
      rho alpha C)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 2 * rho) :
    PureWZ2PaperADSet1
      (scalarProjection (data.planeMap point)
        (target ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
      rho alpha (15 * C) := by
  apply hexactAD.of_subset_cthickening_two
      (D := witnessRadius + pointBound * error)
  · rintro value ⟨targetPoint, htargetPoint, rfl⟩
    let targetSubtype : {point : Point3 // point ∈ target} :=
      ⟨targetPoint, htargetPoint.1⟩
    let sourceSubtype : {point : Point3 // point ∈ exactImage} :=
      data.sourcePoint targetSubtype
    have hsourceDistance :
        dist targetPoint (sourceSubtype : Point3) ≤ witnessRadius :=
      data.sourcePoint_dist targetSubtype
    have hsourceBall : (sourceSubtype : Point3) ∈
        Metric.closedBall (data.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius) := by
      rw [Metric.mem_closedBall]
      calc
        dist (sourceSubtype : Point3) (data.sourcePoint point : Point3)
            ≤ dist (sourceSubtype : Point3) targetPoint +
                dist targetPoint (point : Point3) +
                  dist (point : Point3) (data.sourcePoint point : Point3) := by
              exact dist_triangle4 (sourceSubtype : Point3) targetPoint
                (point : Point3) (data.sourcePoint point : Point3)
        _ ≤ witnessRadius + Real.sqrt rho + witnessRadius := by
              gcongr
              · simpa [dist_comm] using hsourceDistance
              · exact htargetPoint.2
              · exact data.sourcePoint_dist point
        _ = Real.sqrt rho + 2 * witnessRadius := by ring
    let sourceValue := inner ℝ (sourceSubtype : Point3)
      (rawNormal (data.sourcePoint point))
    refine ⟨sourceValue, ?_, ?_⟩
    · exact ⟨sourceSubtype, ⟨sourceSubtype.property, hsourceBall⟩, rfl⟩
    rw [Real.dist_eq]
    have hsplit :
        inner ℝ targetPoint (data.planeMap point) - sourceValue =
          inner ℝ (targetPoint - (sourceSubtype : Point3))
              (data.planeMap point) +
            inner ℝ (sourceSubtype : Point3)
              (data.planeMap point - rawNormal (data.sourcePoint point)) := by
      dsimp only [sourceValue]
      rw [inner_sub_left, inner_sub_right]
      ring
    rw [hsplit]
    calc
      |inner ℝ (targetPoint - (sourceSubtype : Point3))
          (data.planeMap point) +
        inner ℝ (sourceSubtype : Point3)
          (data.planeMap point - rawNormal (data.sourcePoint point))|
          ≤ |inner ℝ (targetPoint - (sourceSubtype : Point3))
                (data.planeMap point)| +
              |inner ℝ (sourceSubtype : Point3)
                (data.planeMap point - rawNormal (data.sourcePoint point))| :=
            abs_add_le _ _
      _ ≤ ‖targetPoint - (sourceSubtype : Point3)‖ *
              ‖data.planeMap point‖ +
            ‖(sourceSubtype : Point3)‖ *
              ‖data.planeMap point - rawNormal (data.sourcePoint point)‖ := by
            gcongr <;> apply abs_real_inner_le_norm
      _ ≤ witnessRadius * 1 + pointBound * error := by
            gcongr
            · simpa [dist_eq_norm] using hsourceDistance
            · exact data.planeMap_unit point |>.le
            · exact hexactBound sourceSubtype
            · exact data.planeMap_close point
      _ = witnessRadius + pointBound * error := by ring
  · positivity
  · exact hprojectionBudget

/-- Package incidence and exact-image local AD into the public local-grain
record after saturation. -/
def PureWZ2SaturationPlaneMapCoreData.toLocalGrainData
    {delta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapCoreData exactImage shading.union rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        |inner ℝ (family.tube index).direction
          (data.planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData shading sigma (6 * C) where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := hincidence
  local_ad := by
    intro rho hrhoLower hrhoOne point
    apply data.local_ad_of_exact hwitnessRadius herror hpointBound
      hexactBound point (hexactAD rho hrhoLower hrhoOne point)
    exact hprojectionBudget.trans hrhoLower

/-- Package the core saturation data using the twice-scale nearby-projection
transfer.  This is the core-data counterpart of the older extension record's
`toLocalGrainDataTwo`. -/
def PureWZ2SaturationPlaneMapCoreData.toLocalGrainDataTwo
    {delta sigma witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {C : ENNReal}
    (data : PureWZ2SaturationPlaneMapCoreData exactImage shading.union rawNormal
      witnessRadius error)
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 // point ∈ exactImage},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        |inner ℝ (family.tube index).direction
          (data.planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 2 * delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (rawNormal (data.sourcePoint point))
            (exactImage ∩
              Metric.closedBall (data.sourcePoint point : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    PureWZ2LocalGrainData shading sigma (15 * C) where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := hincidence
  local_ad := by
    intro rho hrhoLower hrhoOne point
    apply data.local_ad_of_exact_two hwitnessRadius herror hpointBound
      hexactBound point (hexactAD rho hrhoLower hrhoOne point)
    exact hprojectionBudget.trans <|
      mul_le_mul_of_nonneg_left hrhoLower (by norm_num)

end Kakeya.Assouad

end
