import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedMultiWindowCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection

/-!
# Nested ordinary one-scale assembly from the cropped critical floor

The selected nested residue already has all structural and geometric data
needed for the one-scale conclusion.  A quantifier-ordered cropped critical
floor supplies the remaining absolute volume lower bound on that same
shading, so no same-extremizer grain restoration is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2OrdinaryAllBinNestedRegionalData
namespace SelectedBlockResidueData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss structuralBudget : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers}
    {regional : PureWZ2OrdinaryAllBinNestedRegionalData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      carriers companions}

/-- One concrete locally-linear output together with the selected nested
residue from which its shading was assembled.  The equality is the
non-phantom provenance used by the hierarchy post-owner boundary. -/
structure OneScaleData
    (residueData : regional.SelectedBlockResidueData) where
  oneScale : PureWZ2LocallyLinearOneScaleData source finalLoss
    (pureWZ2SourceHorizontalFinalScale rho)
  shading_eq : oneScale.shading = residueData.shading

/-- Package the already selected nested residue once final extremality and its
absolute volume floor have been proved on that exact shading.  This isolates
the geometric output construction from the two legitimate ways of supplying
the lower bound: a global cropped floor, or a source-specific ordinary trace. -/
theorem toOneScaleDataOfExtremalAndVolumeLower
    (residueData : regional.SelectedBlockResidueData)
    (hinputFinal : inputLoss ≤ finalLoss)
    (hfamilyFinal : WZ2PaperCroppedIsExtremal
      sigma finalLoss source.family residueData.shading)
    (hvolume : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      volume residueData.shading.union) :
    Nonempty (OneScaleData residueData) := by
  have hconstantFinal : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputFinal
  have hconstantTop : Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    residueData.subshading hconstantFinal hconstantTop
  let globalGrains := source.globalGrains.restrict
    residueData.subshading hconstantFinal hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ residueData.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, residueData.subshading.union_subset point.property⟩
  let first : Fin residueData.retained.card :=
    ⟨0, Finset.card_pos.mpr residueData.retained_nonempty⟩
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    rw [← residueData.rich_scale_eq first]
    exact (regional.selectedRich
      (residueData.selectedIndex first)).richTrapezoid.scale_pos
  have hdeltaScale : delta ≤ pureWZ2SourceHorizontalFinalScale rho := by
    rw [← residueData.rich_scale_eq first]
    let block := residueData.selectedIndex first
    let bin := regional.selectedSourceBin block
    let nestedBin := regional.selectedNestedBin block bin
    let prep := ((regional.family block).nested bin).preparation nestedBin.1 |>.prep
    calc
      delta ≤ rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1
      _ ≤ prep.graphScale := prep.rho_le_graphScale
      _ ≤ 5 * prep.graphScale := by nlinarith [prep.graphScale_pos]
      _ = (regional.selectedRich block).richTrapezoid.scale :=
        (regional.selectedRich block).richTrapezoid.scale_eq.symm
  have hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1 := by
    rw [← residueData.rich_scale_eq first]
    exact (regional.selectedRich
      (residueData.selectedIndex first)).richTrapezoid.scale_le_one
  let oneScale : PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho) := {
    rho_pos := hscalePos
    delta_le_rho := hdeltaScale
    rho_le_one := hscaleOne
    shading := residueData.shading
    subshading := residueData.subshading
    whole_cells := residueData.cubical
    extremal := hfamilyFinal
    volume_lower := hvolume
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := residueData.trapezoids
    trapezoids_nonempty := residueData.trapezoids_nonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      unfold PureWZ2OrdinaryAllBinNestedRegionalData.selectedTrapezoid
      rw [(regional.selectedRich
        (residueData.selectedIndex index)).richTrapezoid.height_eq]
      exact residueData.rich_scale_eq index
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      exact (regional.selectedRich
        (residueData.selectedIndex index)).richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      unfold PureWZ2OrdinaryAllBinNestedRegionalData.selectedTrapezoid
      simpa [residueData.rich_scale_eq index] using
        (regional.selectedRich
          (residueData.selectedIndex index)).richTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with ⟨firstIndex, _, rfl⟩
      rcases Finset.mem_image.mp hother with ⟨secondIndex, _, rfl⟩
      have hindexNe : firstIndex ≠ secondIndex := by
        intro hindex
        subst secondIndex
        exact hne rfl
      exact residueData.separated_cores regional firstIndex secondIndex hindexNe
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨targetIndex, _, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (residueData.mem_shading_union_iff point).mp hpoint.1 with
        ⟨sourceIndex, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (regional.selectedShading
            (residueData.selectedIndex sourceIndex)).union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore := (regional.selectedRich
        (residueData.selectedIndex sourceIndex)).heightLift.active_height_coverage
          z hsourceSlice
      by_cases heq :
          regional.selectedTrapezoid
              (residueData.selectedIndex targetIndex) =
            regional.selectedTrapezoid
              (residueData.selectedIndex sourceIndex)
      · rw [heq]
        change |source.globalGrains.slope z -
            (regional.selectedTrapezoid
              (residueData.selectedIndex sourceIndex)).affine z| ≤
          pureWZ2SourceHorizontalFinalScale rho
        unfold PureWZ2OrdinaryAllBinNestedRegionalData.selectedTrapezoid
        simpa [residueData.rich_scale_eq sourceIndex] using
          (regional.selectedRich
            (residueData.selectedIndex sourceIndex)).heightLift.slope_approximation
              z hsourceSlice
      · have hsep := residueData.separated_cores regional targetIndex sourceIndex
          (by
            intro hindex
            subst sourceIndex
            exact heq rfl) z hz z hsourceCore
        exact False.elim ((not_le_of_gt
          (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep))
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (residueData.mem_shading_union_iff point).mp hpoint.1 with
        ⟨index, hindexPoint⟩
      have hindexSlice : horizontalSlice
          (regional.selectedShading
            (residueData.selectedIndex index)).union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hindexPoint, hpoint.2⟩
      exact ⟨regional.selectedTrapezoid
          (residueData.selectedIndex index),
        Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩,
        (regional.selectedRich
          (residueData.selectedIndex index)).heightLift.active_height_coverage
            z hindexSlice⟩
  }
  exact ⟨{ oneScale := oneScale, shading_eq := rfl }⟩

/-- Compatibility projection which forgets only the concrete selected-residue
provenance. -/
theorem toOneScaleOfExtremalAndVolumeLower
    (residueData : regional.SelectedBlockResidueData)
    (hinputFinal : inputLoss ≤ finalLoss)
    (hfamilyFinal : WZ2PaperCroppedIsExtremal
      sigma finalLoss source.family residueData.shading)
    (hvolume : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      volume residueData.shading.union) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases residueData.toOneScaleDataOfExtremalAndVolumeLower
      hinputFinal hfamilyFinal hvolume with ⟨data⟩
  exact ⟨data.oneScale⟩

/-- Assemble the nested selected residue directly on its original source
family.  The cropped critical-floor selection supplies the absolute volume
lower bound on the already constructed residue shading. -/
theorem toOneScaleOfCroppedCriticalFloor
    (residueData : regional.SelectedBlockResidueData)
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma finalLoss structuralBudget)
    (hinputStructural : inputLoss ≤ criticalFloor.structuralLoss)
    (hstructuralFinal : criticalFloor.structuralLoss ≤ finalLoss)
    (hdeltaCritical : delta ≤ criticalFloor.delta₀)
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta criticalFloor.structuralLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hsourceStructural : WZ2PaperCroppedIsExtremal
      sigma criticalFloor.structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hfamilyStructural : WZ2PaperCroppedIsExtremal
      sigma criticalFloor.structuralLoss source.family residueData.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := residueData.cubical
      dense := hdense
      volume_upper :=
        (measure_mono residueData.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  have hfamilyFinal : WZ2PaperCroppedIsExtremal
      sigma finalLoss source.family residueData.shading :=
    hfamilyStructural.mono_loss hstructuralFinal
  have hconstantStructural :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-criticalFloor.structuralLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputStructural
  have hvolume : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      volume residueData.shading.union :=
    criticalFloor.volume_floor delta source.extremal.delta_pos hdeltaCritical
      source.family source.extremal.nonempty residueData.shading
      (source.extremal.cwa_nearby_scales.mono hconstantStructural
        (by simp [Kakeya.realRpowENN]))
      residueData.cubical hdense
  exact residueData.toOneScaleOfExtremalAndVolumeLower
    (hinputStructural.trans hstructuralFinal) hfamilyFinal hvolume

/-- Source-specific critical-floor closure from the exact ordinary trace of a
re-entry normalization.  Unlike `PureWZ2CroppedFloorReductionStatement`, this
does not assert a model conversion for arbitrary cropped families: it reduces
only the selected residue on the literal runtime source carried by `reentry`. -/
theorem toOneScaleDataOfReentryTraceAndPureCriticalFloor
    {traceSourceLoss densityLoss : ℝ}
    {normalizationExponent : ℕ}
    (residueData : regional.SelectedBlockResidueData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma finalLoss structuralBudget)
    (lossConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (hinputDensity : inputLoss ≤ densityLoss)
    (hdensityFinal : densityLoss ≤ finalLoss)
    (hdeltaCritical : delta ≤ criticalFloor.delta₀)
    (hdeltaTrace : delta ≤ 1 / 12)
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta densityLoss))
    (htraceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta traceSourceLoss / 2))
    (hcwaAbsorption :
      lossConstant * Kakeya.realRpowENN delta (-densityLoss) ≤
        Kakeya.realRpowENN delta (-criticalFloor.structuralLoss))
    (hdensityAbsorption :
      Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN delta densityLoss) :
    Nonempty (OneScaleData residueData) := by
  have hsourceDensity : WZ2PaperCroppedIsExtremal
      sigma densityLoss source.family source.shading :=
    source.extremal.mono_loss hinputDensity
  have hfamilyDensity : WZ2PaperCroppedIsExtremal
      sigma densityLoss source.family residueData.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceDensity.cwa_nearby_scales
      cubical := residueData.cubical
      dense := hdense
      volume_upper :=
        (measure_mono residueData.subshading.union_subset).trans
          hsourceDensity.volume_upper }
  let normalized := reentry.toNormalizationData
  let selected : Kakeya.Streamlined.TubeSubfamily source.family :=
    { family := source.family
      embedding := Function.Embedding.refl _
      tube_eq := fun _ => rfl }
  have hfinalSubset : ∀ index, residueData.shading.carrier index ⊆
      normalized.croppedRefined.carrier (selected.embedding index) := by
    intro index
    exact residueData.subshading index
  have hordinaryPerTube : ∀ index : Fin selected.family.card,
      (Kakeya.realRpowENN delta traceSourceLoss / 2) *
          volume (normalized.croppedFamily.tube
            (selected.embedding index)).carrier ≤
        volume (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.ordinaryIndex selected index)) := by
    intro index
    exact normalized.framed_ordinary_per_tube selected
      index
  rcases normalized.croppedFloorReduction_of_trace selected
      residueData.shading source.extremal.nonempty residueData.cubical
      hfinalSubset (Kakeya.realRpowENN delta traceSourceLoss / 2)
      hordinaryPerTube lossConstant
      (Kakeya.realRpowENN delta (-densityLoss))
      (Kakeya.realRpowENN delta densityLoss)
      lossConstantOne lossConstantTop htraceAbsorption
      hfamilyDensity.cwa_nearby_scales hdense hdeltaTrace with
    ⟨reduced⟩
  have hordinaryCWA : WZ2PaperPureCWAAtNearbyScales
      reduced.ordinaryFamily
      (Kakeya.realRpowENN delta (-criticalFloor.structuralLoss)) :=
    reduced.ordinary_cwa.mono hcwaAbsorption
      (by simp [Kakeya.realRpowENN])
  have hordinaryDense : reduced.ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN delta criticalFloor.structuralLoss) := by
    exact
      (mul_le_mul_left hdensityAbsorption
        reduced.ordinaryFamily.toBodyFamily.mass).trans
        reduced.ordinary_dense
  have hvolume : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      volume residueData.shading.union :=
    (criticalFloor.volume_floor delta source.extremal.delta_pos
      hdeltaCritical reduced.ordinaryFamily reduced.ordinary_nonempty
      reduced.ordinaryShading hordinaryCWA hordinaryDense).trans
        reduced.ordinary_union_volume_le
  exact residueData.toOneScaleDataOfExtremalAndVolumeLower
    (hinputDensity.trans hdensityFinal)
    (hfamilyDensity.mono_loss hdensityFinal) hvolume

/-- Compatibility projection which forgets the selected-residue provenance. -/
theorem toOneScaleOfReentryTraceAndPureCriticalFloor
    {traceSourceLoss densityLoss : ℝ}
    {normalizationExponent : ℕ}
    (residueData : regional.SelectedBlockResidueData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma finalLoss structuralBudget)
    (lossConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (hinputDensity : inputLoss ≤ densityLoss)
    (hdensityFinal : densityLoss ≤ finalLoss)
    (hdeltaCritical : delta ≤ criticalFloor.delta₀)
    (hdeltaTrace : delta ≤ 1 / 12)
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta densityLoss))
    (htraceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta traceSourceLoss / 2))
    (hcwaAbsorption :
      lossConstant * Kakeya.realRpowENN delta (-densityLoss) ≤
        Kakeya.realRpowENN delta (-criticalFloor.structuralLoss))
    (hdensityAbsorption :
      Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN delta densityLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases residueData.toOneScaleDataOfReentryTraceAndPureCriticalFloor
      reentry criticalFloor lossConstant lossConstantOne lossConstantTop
      hinputDensity hdensityFinal hdeltaCritical hdeltaTrace hdense
      htraceAbsorption hcwaAbsorption hdensityAbsorption with ⟨data⟩
  exact ⟨data.oneScale⟩

end SelectedBlockResidueData
end PureWZ2OrdinaryAllBinNestedRegionalData

end Kakeya.Assouad

end
