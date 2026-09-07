import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactImageLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScalePreparedSource

/-!
# Prepared-source adapter for Proposition 6.4 local grains

This file keeps the terminal-hierarchy convenience wrapper separate from the
core exact-image geometry.  In particular, importing the Proposition 6.4
geometry does not import the Node 5 sticky schedule.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The exact-image shading and plane field obtained from prepared
Proposition 6.4 data after the common-window source selection.  All source
incidence and local AD data are inherited from the selected short-slab
configuration. -/
theorem PureWZ2Proposition64PreparedData.exactImageLocalGrains
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss rawLoss
      extensionConstant targetDelta : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    {hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss}
    {raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN sourceDelta (-finalLoss)) rawLoss
        extensionConstant}
    (prepared : PureWZ2Proposition64PreparedData hierarchy raw)
    (common : PureWZ2Proposition64CommonWindowData
      prepared.restrictedRaw.slope prepared.slab.center
      prepared.slab.anchorHeight prepared.slab.halfHeight
      prepared.normalization source.family prepared.slab.shading)
    (hhalfHeightSmall : prepared.slab.halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ prepared.normalization)
    (hsourceDeltaTarget : sourceDelta ≤ targetDelta)
    (hradius : 180 * sourceDelta ≤ 6 * targetDelta)
    (hsourceDeltaSmall : 180 * sourceDelta ≤ 1 / 2) :
    let selectedSource :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset source.family common.selected
    let selectedShading : WZ1PaperTubeShading selectedSource.family :=
      restrictPaperShading selectedSource prepared.slab.shading
    let selectedSub : ∀ index, selectedShading.carrier index ⊆
        hierarchy.shading.carrier (selectedSource.embedding index) :=
      fun index point hpoint => prepared.slab.subshading
        (selectedSource.embedding index) hpoint
    let selectedLocal := hierarchy.localGrains.restrictSubfamilyWithShading
      selectedSource selectedShading selectedSub
    let imageBox : ∀ index, ∀ point ∈ selectedShading.carrier index,
        pureWZ2Proposition64TranslatedMap prepared.restrictedRaw.slope
            prepared.slab.center prepared.slab.anchorHeight
            prepared.slab.halfHeight prepared.normalization common.translation
            point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
      common.image_mem_axisBox source.extremal.delta_pos hsourceDeltaSmall
        prepared.slab.halfHeight_pos (by linarith) hnormalization
        prepared.normalized.anchor_value_bound source.line_class
        (by
          intro index point hpoint
          rw [prepared.slab.carrier_eq] at hpoint
          simpa [prepared.slab.slab_eq] using hpoint.2)
    Nonempty (PureWZ2Proposition64ExactPlaneMapData
      (targetDelta := targetDelta)
      (g := prepared.restrictedRaw.slope)
      (slabCenter := prepared.slab.center)
      (anchorHeight := prepared.slab.anchorHeight)
      (halfHeight := prepared.slab.halfHeight)
      (normalization := prepared.normalization)
      (translation := common.translation)
      (hhalfHeight := prepared.slab.halfHeight_pos)
      (hnormalization := hnormalization)
      (hsourceDelta := source.extremal.delta_pos)
      (hanchorSlope := prepared.normalized.anchor_value_bound)
      (hradius := hradius)
      (hsourceLine := source.line_class.subfamily selectedSource)
      (himageBox := imageBox) selectedLocal) := by
  let selectedSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset source.family common.selected
  let selectedShading : WZ1PaperTubeShading selectedSource.family :=
    restrictPaperShading selectedSource prepared.slab.shading
  have hselectedSub : ∀ index, selectedShading.carrier index ⊆
      hierarchy.shading.carrier (selectedSource.embedding index) := by
    intro index point hpoint
    exact prepared.slab.subshading (selectedSource.embedding index) hpoint
  let selectedLocal := hierarchy.localGrains.restrictSubfamilyWithShading
    selectedSource selectedShading hselectedSub
  let imageBox : ∀ index, ∀ point ∈ selectedShading.carrier index,
      pureWZ2Proposition64TranslatedMap prepared.restrictedRaw.slope
          prepared.slab.center prepared.slab.anchorHeight
          prepared.slab.halfHeight prepared.normalization common.translation
          point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    common.image_mem_axisBox source.extremal.delta_pos hsourceDeltaSmall
      prepared.slab.halfHeight_pos (by linarith) hnormalization
      prepared.normalized.anchor_value_bound source.line_class
      (by
        intro index point hpoint
        rw [prepared.slab.carrier_eq] at hpoint
        simpa [prepared.slab.slab_eq] using hpoint.2)
  exact ⟨pureWZ2Proposition64ExactPlaneMapData
    (hsourceLine := source.line_class.subfamily selectedSource)
    (himageBox := imageBox) selectedLocal
    (by
      intro point
      rcases point.property with ⟨index, hpoint⟩
      exact hierarchy.planeMap_vertical_bound
        ⟨point, ⟨selectedSource.embedding index, hselectedSub index hpoint⟩⟩)
    hsourceDeltaTarget hhalfHeightSmall⟩

end Kakeya.Assouad
