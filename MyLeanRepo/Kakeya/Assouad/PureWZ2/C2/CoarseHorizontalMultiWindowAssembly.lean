import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseHorizontalGoodBlockFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineOneScaleAssembly

/-!
# Multi-window assembly on the genuine first-sticky coarse extremizer
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

def pureWZ2CoarseHorizontalFinalScale (rho : ℝ) : ℝ :=
  1280 * rho

structure PureWZ2CoarseHorizontalWindowFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) where
  windowCount : ℕ
  windowCount_pos : 0 < windowCount
  pipeline : Fin windowCount →
    PureWZ2CoarseHorizontalPipelineData (eta := eta) twoScale
  rich : ∀ index, PureWZ2CoarseHorizontalRichPipelineData
    (finalLoss := finalLoss) (theoremEta := theoremEta) (pipeline index)
  trapezoid_injective : Function.Injective fun index =>
    (rich index).richTrapezoid.trapezoid
  separated_cores :
    ∀ first second,
      (rich first).richTrapezoid.trapezoid ≠
          (rich second).richTrapezoid.trapezoid →
        ∀ z ∈ (rich first).richTrapezoid.trapezoid.core,
          ∀ w ∈ (rich second).richTrapezoid.trapezoid.core,
            Real.sqrt (pureWZ2CoarseHorizontalFinalScale rho) ≤ |z - w|

namespace PureWZ2CoarseHorizontalWindowFamilyData

def shading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :
    WZ1PaperTubeShading twoScale.coarse.coarse where
  carrier sourceIndex :=
    ⋃ window : Fin family.windowCount,
      (family.rich window).richShading.shading.carrier sourceIndex
  measurable_carrier sourceIndex :=
    MeasurableSet.iUnion fun window =>
      (family.rich window).richShading.shading.measurable_carrier sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨window, hwindow⟩
    exact (family.rich window).richShading.shading.subset_body
      sourceIndex hwindow

@[simp] theorem mem_shading_carrier_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale)
    (sourceIndex : Fin twoScale.coarse.coarse.card) (point : Point3) :
    point ∈ family.shading.carrier sourceIndex ↔
      ∃ window : Fin family.windowCount,
        point ∈ (family.rich window).richShading.shading.carrier
          sourceIndex := by
  simp [shading]

theorem subshading
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :
    PureWZ2PaperIsSubshading family.shading
      twoScale.coarseGrains.shading := by
  intro sourceIndex point hpoint
  rcases (family.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨window, hwindow⟩
  exact (family.rich window).richShading.subshading sourceIndex hwindow

theorem cubical
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :
    WZ1PaperIsCubicalShading family.shading := by
  intro sourceIndex point hpoint other hother
  rcases (family.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨window, hwindow⟩
  apply (family.mem_shading_carrier_iff sourceIndex other).mpr
  exact ⟨window, (family.rich window).richShading.whole_cells
    sourceIndex point hwindow hother⟩

theorem mem_shading_union_iff
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale)
    (point : Point3) :
    point ∈ family.shading.union ↔
      ∃ window : Fin family.windowCount,
        point ∈ (family.rich window).richShading.shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (family.mem_shading_carrier_iff sourceIndex point).mp hpoint with
      ⟨window, hwindow⟩
    exact ⟨window, sourceIndex, hwindow⟩
  · rintro ⟨window, sourceIndex, hpoint⟩
    exact ⟨sourceIndex,
      (family.mem_shading_carrier_iff sourceIndex point).mpr
        ⟨window, hpoint⟩⟩

theorem rich_union_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :
    Pairwise fun first second : Fin family.windowCount =>
      Disjoint
        (family.rich first).richShading.shading.union
        (family.rich second).richShading.shading.union := by
  intro first second hne
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  have htrapezoidNe :
      (family.rich first).richTrapezoid.trapezoid ≠
        (family.rich second).richTrapezoid.trapezoid := by
    intro heq
    exact hne (family.trapezoid_injective heq)
  let z := point (2 : Fin 3)
  have hfirstSlice : horizontalSlice
      (family.rich first).richShading.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hfirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (family.rich second).richShading.shading.union z ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hsecond, rfl⟩
  have hfirstCore :=
    (family.rich first).richTrapezoid.active_height_coverage z hfirstSlice
  have hsecondCore :=
    (family.rich second).richTrapezoid.active_height_coverage z hsecondSlice
  have hsep := family.separated_cores first second htrapezoidNe
    z hfirstCore z hsecondCore
  have hscalePos : 0 < pureWZ2CoarseHorizontalFinalScale rho := by
    unfold pureWZ2CoarseHorizontalFinalScale
    have hrho : 0 < rho := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos
    nlinarith
  exact (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep)

theorem rich_carrier_pairwise_disjoint
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale)
    (sourceIndex : Fin twoScale.coarse.coarse.card) :
    Pairwise fun first second : Fin family.windowCount =>
      Disjoint
        ((family.rich first).richShading.shading.carrier sourceIndex)
        ((family.rich second).richShading.shading.carrier sourceIndex) := by
  intro first second hne
  exact (family.rich_union_pairwise_disjoint hne).mono
    (fun point (hpoint : point ∈
        (family.rich first).richShading.shading.carrier sourceIndex) =>
      show point ∈ (family.rich first).richShading.shading.union from
        ⟨sourceIndex, hpoint⟩)
    (fun point (hpoint : point ∈
        (family.rich second).richShading.shading.carrier sourceIndex) =>
      show point ∈ (family.rich second).richShading.shading.union from
        ⟨sourceIndex, hpoint⟩)

theorem shading_mass_eq_sum
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) :
    family.shading.mass =
      ∑ window : Fin family.windowCount,
        (family.rich window).richShading.shading.mass := by
  calc
    family.shading.mass =
        ∑ sourceIndex : Fin twoScale.coarse.coarse.card,
          MeasureTheory.volume (⋃ window : Fin family.windowCount,
            (family.rich window).richShading.shading.carrier sourceIndex) := rfl
    _ = ∑ sourceIndex : Fin twoScale.coarse.coarse.card,
          ∑ window : Fin family.windowCount, MeasureTheory.volume
            ((family.rich window).richShading.shading.carrier sourceIndex) := by
      apply Finset.sum_congr rfl
      intro sourceIndex _
      rw [MeasureTheory.measure_iUnion
        (family.rich_carrier_pairwise_disjoint sourceIndex)
        (fun window =>
          (family.rich window).richShading.shading.measurable_carrier
            sourceIndex)]
      simp [tsum_fintype]
    _ = ∑ window : Fin family.windowCount,
          ∑ sourceIndex : Fin twoScale.coarse.coarse.card,
            MeasureTheory.volume
              ((family.rich window).richShading.shading.carrier
                sourceIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ window : Fin family.windowCount,
        (family.rich window).richShading.shading.mass := rfl

def trapezoids
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) : Finset WZ1VerticalTrapezoid :=
  Finset.univ.image fun window =>
    (family.rich window).richTrapezoid.trapezoid

theorem trapezoids_nonempty
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) : family.trapezoids.Nonempty := by
  let first : Fin family.windowCount := ⟨0, family.windowCount_pos⟩
  exact ⟨(family.rich first).richTrapezoid.trapezoid,
    Finset.mem_image.mpr ⟨first, Finset.mem_univ _, rfl⟩⟩

theorem rich_scale_eq
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale) (window : Fin family.windowCount) :
    (family.rich window).richTrapezoid.scale =
      pureWZ2CoarseHorizontalFinalScale rho := by
  rw [(family.rich window).richTrapezoid.scale_eq,
    (family.pipeline window).prep.graphScale_eq]
  simp [pureWZ2CoarseHorizontalFinalScale, twoScale.rhoRequested_eq]
  ring

/-- Convert a mass budget into density of the exact selected coarse union. -/
theorem dense_of_mass_budget
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale)
    (hbudget :
      Kakeya.realRpowENN twoScale.rhoRequested.1 structuralLoss *
          (wz1PaperBodyFamily twoScale.coarse.coarse).mass ≤
        family.shading.mass) :
    family.shading.IsLambdaDense
      (Kakeya.realRpowENN twoScale.rhoRequested.1 structuralLoss) := by
  exact hbudget

/--
Assemble the same-configuration Pure one-scale output on the actual
first-sticky coarse grain extremizer.
-/
theorem toOneScaleOfGrainProducer
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss eta theoremEta
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (family : PureWZ2CoarseHorizontalWindowFamilyData
      (finalLoss := finalLoss) (eta := eta) (theoremEta := theoremEta)
      twoScale)
    (hmiddleStructural : middleLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily :
          Kakeya.Streamlined.TubeFamily twoScale.rhoRequested.1,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma finalLoss))
    (hdense : family.shading.IsLambdaDense
      (Kakeya.realRpowENN twoScale.rhoRequested.1 structuralLoss)) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      (twoScale.coarseGrains.toQuantitativeGrainConfiguration
        twoScale.coarseGrains_slope_bound) finalLoss
      (pureWZ2CoarseHorizontalFinalScale rho)) := by
  let base := twoScale.coarseGrains.toQuantitativeGrainConfiguration
    twoScale.coarseGrains_slope_bound
  have hbaseStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss base.family base.shading :=
    base.extremal.mono_loss hmiddleStructural
  have hfamilyStructural :
      WZ2PaperCroppedIsExtremal
        sigma structuralLoss base.family family.shading :=
    { delta_pos := hbaseStructural.delta_pos
      delta_le_one := hbaseStructural.delta_le_one
      nonempty := hbaseStructural.nonempty
      cwa_nearby_scales := hbaseStructural.cwa_nearby_scales
      cubical := family.cubical
      dense := by
        simpa [base,
          PureWZ2GrainRefinementData.toQuantitativeGrainConfiguration]
          using hdense
      volume_upper :=
        (measure_mono family.subshading.union_subset).trans
          hbaseStructural.volume_upper }
  rcases grainProducer base.family family.shading base.line_class
      hfamilyStructural with ⟨refined⟩
  have hsub : PureWZ2PaperIsSubshading refined.shading base.shading := by
    intro sourceIndex point hpoint
    exact family.subshading sourceIndex
      (refined.subshading sourceIndex hpoint)
  have hconstant :
      Kakeya.realRpowENN twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1 (-finalLoss) :=
    pureWZ2_grain_constant_mono base.extremal.delta_pos
      base.extremal.delta_le_one
      (hmiddleStructural.trans hstructuralFinal)
  have hconstantTop :
      Kakeya.realRpowENN twoScale.rhoRequested.1 (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := base.localGrains.restrictWithConstant hsub hconstant hconstantTop
  let globalGrains := base.globalGrains.restrict hsub hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact base.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let first : Fin family.windowCount := ⟨0, family.windowCount_pos⟩
  have hscalePos : 0 < pureWZ2CoarseHorizontalFinalScale rho := by
    rw [← family.rich_scale_eq first]
    exact (family.rich first).richTrapezoid.scale_pos
  have hstoredScale : twoScale.rhoRequested.1 ≤
      pureWZ2CoarseHorizontalFinalScale rho := by
    rw [← family.rich_scale_eq first]
    calc
      twoScale.rhoRequested.1 ≤ (family.pipeline first).prep.graphScale := by
        rw [(family.pipeline first).prep.graphScale_eq]
        nlinarith [twoScale.coarseGrains.extremal.delta_pos]
      _ ≤ 5 * (family.pipeline first).prep.graphScale := by
        nlinarith [(family.pipeline first).prep.graphScale_pos]
      _ = (family.rich first).richTrapezoid.scale :=
        (family.rich first).richTrapezoid.scale_eq.symm
  have hscaleOne : pureWZ2CoarseHorizontalFinalScale rho ≤ 1 := by
    rw [← family.rich_scale_eq first]
    exact (family.rich first).richTrapezoid.scale_le_one
  exact ⟨{
    rho_pos := hscalePos
    delta_le_rho := hstoredScale
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
    trapezoids := family.trapezoids
    trapezoids_nonempty := family.trapezoids_nonempty
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      rw [(family.rich window).richTrapezoid.height_eq]
      exact family.rich_scale_eq window
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      exact (family.rich window).richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨window, _hwindow, rfl⟩
      simpa [family.rich_scale_eq window] using
        (family.rich window).richTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with
        ⟨firstWindow, _hfirstWindow, rfl⟩
      rcases Finset.mem_image.mp hother with
        ⟨secondWindow, _hsecondWindow, rfl⟩
      exact family.separated_cores firstWindow secondWindow hne
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨targetWindow, _htargetWindow, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ family.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (family.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨sourceWindow, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (family.rich sourceWindow).richShading.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore :=
        (family.rich sourceWindow).richTrapezoid.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (family.rich targetWindow).richTrapezoid.trapezoid =
            (family.rich sourceWindow).richTrapezoid.trapezoid
      · rw [heq]
        change
          |base.globalGrains.slope z -
              (family.rich sourceWindow).richTrapezoid.trapezoid.affine z| ≤
            pureWZ2CoarseHorizontalFinalScale rho
        simpa [base,
          PureWZ2GrainRefinementData.toQuantitativeGrainConfiguration,
          PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound,
          family.rich_scale_eq sourceWindow] using
          (family.rich sourceWindow).richTrapezoid.slope_approximation
            z hsourceCore hsourceSlice
      · have hsep := family.separated_cores targetWindow sourceWindow
          heq z hz z hsourceCore
        have hsqrtPos :
            0 < Real.sqrt (pureWZ2CoarseHorizontalFinalScale rho) :=
          Real.sqrt_pos.mpr hscalePos
        simp only [sub_self, abs_zero] at hsep
        exact False.elim ((not_le_of_gt hsqrtPos) hsep)
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      have hfamilyPoint : point ∈ family.shading.union :=
        refined.subshading.union_subset hpoint.1
      rcases (family.mem_shading_union_iff point).mp hfamilyPoint with
        ⟨window, hwindowPoint⟩
      have hwindowSlice : horizontalSlice
          (family.rich window).richShading.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hwindowPoint, hpoint.2⟩
      exact ⟨(family.rich window).richTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨window, Finset.mem_univ _, rfl⟩,
        (family.rich window).richTrapezoid.active_height_coverage
          z hwindowSlice⟩
  }⟩

end PureWZ2CoarseHorizontalWindowFamilyData

end Kakeya.Assouad
