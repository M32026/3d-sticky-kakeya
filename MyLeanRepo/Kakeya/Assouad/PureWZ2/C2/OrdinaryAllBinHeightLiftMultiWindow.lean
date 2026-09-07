import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinHeightLiftResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements

/-!
# Multi-window output of the all-bin height-only construction

The final shading is the finite union of the original-family height lifts
selected by one mod-64 block class.  The chosen global bin remains only in
the dependent provenance of each local rich-height and trapezoid witness.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
namespace SelectedHeightLiftResidueData

variable
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    {selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins}
    {rich : PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) selected}

/-- Finite union of the selected original-family height lifts. -/
def shading (residueData : rich.SelectedHeightLiftResidueData) :
    WZ1PaperTubeShading source.family where
  carrier sourceIndex := ⋃ index : Fin residueData.retained.card,
    (rich.rich (residueData.selectedIndex index)).heightLift.shading.carrier
      sourceIndex
  measurable_carrier sourceIndex := MeasurableSet.iUnion fun index =>
    (rich.rich (residueData.selectedIndex index)).heightLift.shading.measurable_carrier
      sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (rich.rich
      (residueData.selectedIndex index)).heightLift.shading.subset_body
        sourceIndex hindex

@[simp] theorem mem_shading_carrier_iff
    (residueData : rich.SelectedHeightLiftResidueData)
    (sourceIndex : Fin source.family.card) (point : Point3) :
    point ∈ residueData.shading.carrier sourceIndex ↔
      ∃ index : Fin residueData.retained.card,
        point ∈ (rich.rich
          (residueData.selectedIndex index)).heightLift.shading.carrier
            sourceIndex := by
  simp [shading]

theorem subshading (residueData : rich.SelectedHeightLiftResidueData) :
    PureWZ2PaperIsSubshading residueData.shading source.shading := by
  intro sourceIndex point hpoint
  rcases (residueData.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex⟩
  exact (rich.rich
    (residueData.selectedIndex index)).heightLift.subshading sourceIndex hindex

theorem cubical (residueData : rich.SelectedHeightLiftResidueData) :
    WZ1PaperIsCubicalShading residueData.shading := by
  intro sourceIndex point hpoint other hother
  rcases (residueData.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex⟩
  exact (residueData.mem_shading_carrier_iff sourceIndex other).mpr
    ⟨index, (rich.rich
      (residueData.selectedIndex index)).heightLift.whole_cells
        sourceIndex point hindex hother⟩

theorem mem_shading_union_iff
    (residueData : rich.SelectedHeightLiftResidueData) (point : Point3) :
    point ∈ residueData.shading.union ↔
      ∃ index : Fin residueData.retained.card,
        point ∈ (rich.rich
          (residueData.selectedIndex index)).heightLift.shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (residueData.mem_shading_carrier_iff
      sourceIndex point).mp hpoint with ⟨index, hindex⟩
    exact ⟨index, sourceIndex, hindex⟩
  · rintro ⟨index, sourceIndex, hpoint⟩
    exact ⟨sourceIndex,
      (residueData.mem_shading_carrier_iff sourceIndex point).mpr
        ⟨index, hpoint⟩⟩

theorem heightLift_union_pairwise_disjoint
    (residueData : rich.SelectedHeightLiftResidueData) :
    Pairwise fun first second : Fin residueData.retained.card =>
      Disjoint
        (rich.rich (residueData.selectedIndex first)).heightLift.shading.union
        (rich.rich (residueData.selectedIndex second)).heightLift.shading.union := by
  intro first second hne
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  let z := point (2 : Fin 3)
  have hfirstSlice : horizontalSlice
      (rich.rich
        (residueData.selectedIndex first)).heightLift.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hfirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (rich.rich
        (residueData.selectedIndex second)).heightLift.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hsecond, rfl⟩
  have hfirstCore := (rich.rich
    (residueData.selectedIndex first)).heightLift.active_height_coverage
      z hfirstSlice
  have hsecondCore := (rich.rich
    (residueData.selectedIndex second)).heightLift.active_height_coverage
      z hsecondSlice
  have hsep := residueData.separated_cores first second hne
    z hfirstCore z hsecondCore
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    have hrho : 0 < rho :=
      (carriers.carrier (residueData.selectedIndex first).1).line.rho_pos
    unfold pureWZ2SourceHorizontalFinalScale
    positivity
  exact (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep)

theorem heightLift_carrier_pairwise_disjoint
    (residueData : rich.SelectedHeightLiftResidueData)
    (sourceIndex : Fin source.family.card) :
    Pairwise fun first second : Fin residueData.retained.card =>
      Disjoint
        ((rich.rich
          (residueData.selectedIndex first)).heightLift.shading.carrier
            sourceIndex)
        ((rich.rich
          (residueData.selectedIndex second)).heightLift.shading.carrier
            sourceIndex) := by
  intro first second hne
  exact (residueData.heightLift_union_pairwise_disjoint hne).mono
    (fun point (hpoint : point ∈ (rich.rich
        (residueData.selectedIndex first)).heightLift.shading.carrier
          sourceIndex) =>
      show point ∈ (rich.rich
        (residueData.selectedIndex first)).heightLift.shading.union from
        ⟨sourceIndex, hpoint⟩)
    (fun point (hpoint : point ∈ (rich.rich
        (residueData.selectedIndex second)).heightLift.shading.carrier
          sourceIndex) =>
      show point ∈ (rich.rich
        (residueData.selectedIndex second)).heightLift.shading.union from
        ⟨sourceIndex, hpoint⟩)

theorem shading_mass_eq_sum
    (residueData : rich.SelectedHeightLiftResidueData) :
    residueData.shading.mass =
      ∑ index : Fin residueData.retained.card,
        (rich.rich
          (residueData.selectedIndex index)).heightLift.shading.mass := by
  calc
    residueData.shading.mass =
        ∑ sourceIndex : Fin source.family.card,
          volume (⋃ index : Fin residueData.retained.card,
            (rich.rich
              (residueData.selectedIndex index)).heightLift.shading.carrier
                sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin source.family.card,
          ∑ index : Fin residueData.retained.card,
            volume ((rich.rich
              (residueData.selectedIndex index)).heightLift.shading.carrier
                sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion
        (residueData.heightLift_carrier_pairwise_disjoint sourceIndex)
        (fun index => (rich.rich
          (residueData.selectedIndex index)).heightLift.shading.measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ index : Fin residueData.retained.card,
          ∑ sourceIndex : Fin source.family.card,
            volume ((rich.rich
              (residueData.selectedIndex index)).heightLift.shading.carrier
                sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ index : Fin residueData.retained.card,
        (rich.rich
          (residueData.selectedIndex index)).heightLift.shading.mass := rfl

theorem total_mass_le_shading_mass
    (residueData : rich.SelectedHeightLiftResidueData) :
    (∑ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      (rich.rich block).heightLift.shading.mass) ≤
      64 * residueData.shading.mass := by
  rw [residueData.shading_mass_eq_sum]
  exact residueData.total_mass_le

def trapezoids (residueData : rich.SelectedHeightLiftResidueData) :
    Finset WZ1VerticalTrapezoid :=
  Finset.univ.image fun index =>
    (rich.rich (residueData.selectedIndex index)).richTrapezoid.trapezoid

theorem trapezoids_nonempty
    (residueData : rich.SelectedHeightLiftResidueData) :
    residueData.trapezoids.Nonempty := by
  let first : Fin residueData.retained.card :=
    ⟨0, Finset.card_pos.mpr residueData.retained_nonempty⟩
  exact ⟨(rich.rich
      (residueData.selectedIndex first)).richTrapezoid.trapezoid,
    Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩⟩

theorem rich_scale_eq
    (residueData : rich.SelectedHeightLiftResidueData)
    (index : Fin residueData.retained.card) :
    (rich.rich (residueData.selectedIndex index)).richTrapezoid.scale =
      pureWZ2SourceHorizontalFinalScale rho := by
  rw [(rich.rich (residueData.selectedIndex index)).richTrapezoid.scale_eq]
  rw [((coarseBins.coarseFamily (residueData.selectedIndex index).1).prep
    (selected.chosenBin (residueData.selectedIndex index))).graphScale_eq]
  simp [pureWZ2SourceHorizontalFinalScale]
  ring

theorem dense_of_total_mass
    (residueData : rich.SelectedHeightLiftResidueData)
    {structuralLoss : ℝ}
    (hdense : 64 * (Kakeya.realRpowENN delta structuralLoss *
        (wz1PaperBodyFamily source.family).mass) ≤
      ∑ block :
        {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
        (rich.rich block).heightLift.shading.mass) :
    residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
  unfold Kakeya.Streamlined.Shading.IsLambdaDense
  apply (ENNReal.mul_le_mul_iff_left
    (show (64 : ENNReal) ≠ 0 by norm_num)
    (show (64 : ENNReal) ≠ ⊤ by norm_num)).mp
  simpa [mul_comm] using
    hdense.trans residueData.total_mass_le_shading_mass

theorem toOneScaleOfGrainProducer
    (residueData : rich.SelectedHeightLiftResidueData)
    {structuralLoss : ℝ}
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss))
    (hdense : residueData.shading.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  have hsourceStructural : WZ2PaperCroppedIsExtremal
      sigma structuralLoss source.family source.shading :=
    source.extremal.mono_loss hinputStructural
  have hfamilyStructural : WZ2PaperCroppedIsExtremal
      sigma structuralLoss source.family residueData.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceStructural.cwa_nearby_scales
      cubical := residueData.cubical
      dense := hdense
      volume_upper :=
        (measure_mono residueData.subshading.union_subset).trans
          hsourceStructural.volume_upper }
  rcases grainProducer source.family residueData.shading source.line_class
      hfamilyStructural with ⟨refined⟩
  have hsub : PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro sourceIndex point hpoint
    exact residueData.subshading sourceIndex
      (refined.subshading sourceIndex hpoint)
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one
      (hinputStructural.trans hstructuralFinal)
  have hconstantTop : Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant hsub hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict hsub hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let first : Fin residueData.retained.card :=
    ⟨0, Finset.card_pos.mpr residueData.retained_nonempty⟩
  have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
    rw [← residueData.rich_scale_eq first]
    exact (rich.rich
      (residueData.selectedIndex first)).richTrapezoid.scale_pos
  have hdeltaScale : delta ≤ pureWZ2SourceHorizontalFinalScale rho := by
    rw [← residueData.rich_scale_eq first]
    let block := residueData.selectedIndex first
    let prep := (coarseBins.coarseFamily block.1).prep
      (selected.chosenBin block)
    calc
      delta ≤ rho := by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.1
      _ ≤ prep.graphScale := prep.rho_le_graphScale
      _ ≤ 5 * prep.graphScale := by nlinarith [prep.graphScale_pos]
      _ = (rich.rich block).richTrapezoid.scale :=
        (rich.rich block).richTrapezoid.scale_eq.symm
  have hscaleOne : pureWZ2SourceHorizontalFinalScale rho ≤ 1 := by
    rw [← residueData.rich_scale_eq first]
    exact (rich.rich
      (residueData.selectedIndex first)).richTrapezoid.scale_le_one
  exact ⟨{
    rho_pos := hscalePos
    delta_le_rho := hdeltaScale
    rho_le_one := hscaleOne
    shading := refined.shading
    subshading := hsub
    whole_cells := refined.cubical
    extremal := refined.extremal
    volume_lower := refined.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := residueData.trapezoids
    trapezoids_nonempty := residueData.trapezoids_nonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      rw [(rich.rich
        (residueData.selectedIndex index)).richTrapezoid.height_eq]
      exact residueData.rich_scale_eq index
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      exact (rich.rich
        (residueData.selectedIndex index)).richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _, rfl⟩
      simpa [residueData.rich_scale_eq index] using
        (rich.rich
          (residueData.selectedIndex index)).richTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with ⟨firstIndex, _, rfl⟩
      rcases Finset.mem_image.mp hother with ⟨secondIndex, _, rfl⟩
      have hindexNe : firstIndex ≠ secondIndex := by
        intro hindex
        subst secondIndex
        exact hne rfl
      exact residueData.separated_cores firstIndex secondIndex hindexNe
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨targetIndex, _, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ residueData.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (residueData.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨sourceIndex, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (rich.rich
            (residueData.selectedIndex sourceIndex)).heightLift.shading.union
            z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore := (rich.rich
        (residueData.selectedIndex sourceIndex)).heightLift.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (rich.rich
            (residueData.selectedIndex targetIndex)).richTrapezoid.trapezoid =
          (rich.rich
            (residueData.selectedIndex sourceIndex)).richTrapezoid.trapezoid
      · rw [heq]
        change |source.globalGrains.slope z -
            (rich.rich
              (residueData.selectedIndex sourceIndex)).richTrapezoid.trapezoid.affine z| ≤
          pureWZ2SourceHorizontalFinalScale rho
        simpa [residueData.rich_scale_eq sourceIndex] using
          (rich.rich
            (residueData.selectedIndex sourceIndex)).heightLift.slope_approximation
              z hsourceSlice
      · have hsep := residueData.separated_cores targetIndex sourceIndex
          (by
            intro hindex
            subst sourceIndex
            exact heq rfl) z hz z hsourceCore
        exact False.elim ((not_le_of_gt
          (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep))
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ residueData.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (residueData.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨index, hindexPoint⟩
      have hindexSlice : horizontalSlice
          (rich.rich
            (residueData.selectedIndex index)).heightLift.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hindexPoint, hpoint.2⟩
      exact ⟨(rich.rich
          (residueData.selectedIndex index)).richTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩,
        (rich.rich
          (residueData.selectedIndex index)).heightLift.active_height_coverage
            z hindexSlice⟩
  }⟩

end SelectedHeightLiftResidueData
end PureWZ2OrdinaryPaperOrderRegularizedRichCoarseBinData

end Kakeya.Assouad

end
