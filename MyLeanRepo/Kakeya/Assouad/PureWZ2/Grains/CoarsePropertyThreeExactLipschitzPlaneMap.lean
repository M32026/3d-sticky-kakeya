import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalCellwiseDirectionCapPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalCapFineLipschitz
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase

/-!
# Exact Lipschitz plane map on coarse Property Three

At the coarse family's own scale `L`, a global direction cap of diameter `L`
gives incidence exactly `L`.  A second common cap refinement of the resulting
cellwise stable-normal map makes it `1`-Lipschitz.  Both finite losses remain
explicit.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def coarsePropertyThreePlaneMapLoss (L : ℝ) : ENNReal :=
  (globalDirectionCapCount L : ENNReal) *
    (unitPlaneMapCapCount L : ENNReal) * 27

/-- A genuine multi-tube Property-Three refinement carrying an exact-scale,
unit, `1`-Lipschitz stable-normal plane map. -/
theorem coarse_property_three_exact_lipschitz_plane_map
    {sigma L tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading family}
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (L := L) (tau := tau)
      (coarseShading := coarseShading) epsilon₁ epsilon₃)
    (hL : 0 < L)
    (hfamily : family.Nonempty)
    (hline : WZ1PaperIsLineClass family) :
    ∃ (final : WZ1PaperTubeShading family)
      (planeMap : PaperWZ1WeakPlaneMapData final L),
      PaperIsSubshading final propP.propertyThree ∧
      WZ1PaperIsCubicalShading final ∧
      LipschitzWith 1
        (fun point : {point : Point3 // point ∈ final.union} =>
          planeMap.planeMap point) ∧
      propP.propertyThree.mass ≤
        coarsePropertyThreePlaneMapLoss L * final.mass := by
  rcases paper_global_cellwise_direction_cap_plane_map
      (S := propP.propertyThree) hfamily hL hL hline
      propP.propertyThree_cubical with
    ⟨directionSelected, center, directionPlaneMap, hdirectionSub,
      hdirectionCubical, _hcenterMeasurable, hcenterCell, _hcenterMem,
      hplaneMap, _hmultiplicity, hdirectionMass⟩
  have hplaneCell : ∀ first second,
      wz1PaperGridIndex L first = wz1PaperGridIndex L second →
      directionPlaneMap.planeMap first =
        directionPlaneMap.planeMap second := by
    intro first second hcell
    rw [hplaneMap first, hplaneMap second, hcenterCell first second hcell]
  rcases paper_global_cap_fine_lipschitz
      directionPlaneMap hL hL hdirectionCubical hplaneCell with
    ⟨final, finalPlaneMap, hfinalSubDirection, hfinalCubical,
      _hfinalMultiplicity, hfinalMass, hfinalLipschitz⟩
  have hfinalSub : PaperIsSubshading final propP.propertyThree :=
    fun index => (hfinalSubDirection index).trans (hdirectionSub index)
  have hratio : L / L = 1 := by field_simp [hL.ne']
  have htoNNReal : Real.toNNReal (L / L) = 1 := by
    rw [hratio]
    norm_num
  have hfinalLipschitzOne : LipschitzWith 1
      (fun point : {point : Point3 // point ∈ final.union} =>
        finalPlaneMap.planeMap point) := by
    simpa [htoNNReal] using hfinalLipschitz
  have hmass : propP.propertyThree.mass ≤
      coarsePropertyThreePlaneMapLoss L * final.mass := by
    calc
      propP.propertyThree.mass ≤
          (globalDirectionCapCount L : ENNReal) *
            directionSelected.mass := hdirectionMass
      _ ≤ (globalDirectionCapCount L : ENNReal) *
          ((unitPlaneMapCapCount L : ENNReal) * 27 * final.mass) := by
        gcongr
      _ = coarsePropertyThreePlaneMapLoss L * final.mass := by
        simp only [coarsePropertyThreePlaneMapLoss]
        ring
  exact ⟨final, finalPlaneMap, hfinalSub, hfinalCubical,
    hfinalLipschitzOne, hmass⟩

end Kakeya.Assouad.PureWZ2

end
