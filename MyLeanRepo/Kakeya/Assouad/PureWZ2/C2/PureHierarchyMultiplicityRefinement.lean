import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyHighMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers

/-!
# Final constant-multiplicity refinement for the Pure WZ2 hierarchy

After iterating the one-scale construction, the proof of Corollary 5.6 passes
once to a dyadic constant-multiplicity refinement of the final shading.  This
module performs exactly that step.  It does not strengthen the one-scale or
Node-4 interfaces: multiplicity is selected only after the last scale has been
constructed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The iterated hierarchy after the paper's final dyadic multiplicity
pigeonhole, but before height-popularity thinning. -/
structure PureWZ2MultiplicityRefinedHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (finalLoss hierarchyLoss selectionLoss : ℝ) where
  iterated : PureWZ2IteratedHierarchyData source finalLoss hierarchyLoss
  bandLevel : ℕ
  shading : WZ1PaperTubeShading source.family :=
    wz1PaperDyadicBandSubshading iterated.shading bandLevel
  shading_eq : shading =
    wz1PaperDyadicBandSubshading iterated.shading bandLevel
  subshading_iterated :
    PureWZ2PaperIsSubshading shading iterated.shading
  subshading_source :
    PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  multiplicity : ℕ := 2 ^ bandLevel
  multiplicity_eq : multiplicity = 2 ^ bandLevel
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    shading.HasConstantMultiplicity multiplicity (2 * multiplicity)
  multiplicity_lower :
    Kakeya.realRpowENN delta (-sigma + selectionLoss) ≤
      (multiplicity : ENNReal)
  mass_retention :
    Kakeya.realRpowENN delta selectionLoss *
        (wz1PaperBodyFamily source.family).mass ≤
      shading.mass
  localGrains : PureWZ2LocalGrainData shading sigma
    (Kakeya.realRpowENN delta (-finalLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  sourceGlobalGrains : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
    (Kakeya.realRpowENN delta (-finalLoss))
  source_slope_eq : sourceGlobalGrains.slope = source.globalGrains.slope
  trapezoids : Fin iterated.levelCount → Finset WZ1VerticalTrapezoid :=
    iterated.trapezoids
  level_nonempty : ∀ level, (trapezoids level).Nonempty
  height_eq : ∀ level, ∀ trapezoid ∈ trapezoids level,
    trapezoid.height =
      wz1Corollary26Scale delta iterated.levelCount level
  slope_bound : ∀ level, ∀ trapezoid ∈ trapezoids level,
    |trapezoid.slope| ≤ 2
  length_bounds : ∀ level, ∀ trapezoid ∈ trapezoids level,
    Real.rpow (wz1Corollary26Scale delta iterated.levelCount level)
        (1 / 2 + hierarchyLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤
        Real.sqrt (wz1Corollary26Scale delta iterated.levelCount level)
  separated_cores : ∀ level, ∀ trapezoid ∈ trapezoids level,
    ∀ other ∈ trapezoids level, trapezoid ≠ other →
      ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
        Real.sqrt (wz1Corollary26Scale delta iterated.levelCount level) ≤
          |z - w|
  slope_approximation : ∀ level, ∀ trapezoid ∈ trapezoids level,
    ∀ z ∈ trapezoid.core,
      horizontalSlice shading.union z ≠ ∅ →
        |sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta iterated.levelCount level
  active_height_coverage : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    horizontalSlice shading.union z ≠ ∅ →
      ∃ trapezoid ∈ trapezoids level, z ∈ trapezoid.core

/-- Apply the paper's quantitative high/low dyadic multiplicity decomposition
before the popularity stage of Corollary 5.6.  The family-mass and smallness
premises are kept explicit so that the outer parameter schedule, rather than
this geometric step, chooses how they are discharged. -/
theorem PureWZ2IteratedHierarchyData.selectHighMultiplicityBand
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2IteratedHierarchyData
      source finalLoss hierarchyLoss)
    {selectionLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hselection : 0 < selectionLoss)
    (hfinal : 0 < finalLoss)
    (hthree : 3 * finalLoss < selectionLoss)
    (hfamilyMass : Kakeya.realRpowENN delta (2 * finalLoss) ≤
      (wz1PaperBodyFamily source.family).mass)
    (hfamilyMassTop : (wz1PaperBodyFamily source.family).mass ≠ ⊤)
    (hcard : 2 * (Nat.log 2 source.family.card + 1 : ENNReal) ≤
      Kakeya.realRpowENN delta (finalLoss - selectionLoss))
    (hmass : Kakeya.realRpowENN delta (3 * finalLoss) ≥
      4 * Kakeya.realRpowENN delta (selectionLoss - finalLoss)) :
    Nonempty
      (PureWZ2MultiplicityRefinedHierarchyData
        source finalLoss hierarchyLoss selectionLoss) := by
  rcases pureWZ2_paper_fine_multiplicity_refinement_with_band
      data.extremal.delta_pos data.extremal.delta_le_one
      hsigma hsigmaOne hselection hfinal hthree
      data.extremal.nonempty hfamilyMass hfamilyMassTop
      data.whole_cells data.extremal.dense data.extremal.volume_upper
      hcard hmass with
    ⟨shading, multiplicity, bandLevel, hsubIterated, hbandCubical,
      hmultiplicityPos, hmultiplicityEq, hconstant, hmultiplicityLower, hmassRetention,
      hshadingEq⟩
  have hsubSource : PureWZ2PaperIsSubshading shading source.shading :=
    fun index => (hsubIterated index).trans (data.subshading index)
  have hconstantTop :
      Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := data.localGrains.restrictWithConstant
    hsubIterated le_rfl hconstantTop
  let sourceGlobalGrains := data.sourceGlobalGrains.restrict
    hsubIterated le_rfl hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact data.planeMap_vertical_bound
      ⟨point, hsubIterated.union_subset point.property⟩
  have hslopeEq : sourceGlobalGrains.slope = source.globalGrains.slope := by
    exact data.source_slope_eq
  refine ⟨{
    iterated := data
    bandLevel := bandLevel
    shading := shading
    shading_eq := hshadingEq
    subshading_iterated := hsubIterated
    subshading_source := hsubSource
    whole_cells := hbandCubical
    multiplicity := multiplicity
    multiplicity_eq := hmultiplicityEq
    multiplicity_pos := hmultiplicityPos
    constant_multiplicity := hconstant
    multiplicity_lower := hmultiplicityLower
    mass_retention := hmassRetention
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    sourceGlobalGrains := sourceGlobalGrains
    source_slope_eq := hslopeEq
    trapezoids := data.trapezoids
    level_nonempty := data.level_nonempty
    height_eq := data.height_eq
    slope_bound := data.slope_bound
    length_bounds := data.length_bounds
    separated_cores := data.separated_cores
    slope_approximation := ?_
    active_height_coverage := ?_ }⟩
  · intro level trapezoid htrapezoid z hz hactive
    have hactiveIterated :
        horizontalSlice data.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hactive)
      intro point hpoint
      exact ⟨hsubIterated.union_subset hpoint.1, hpoint.2⟩
    change |data.sourceGlobalGrains.slope z - trapezoid.affine z| ≤
      wz1Corollary26Scale delta data.levelCount level
    exact data.slope_approximation level trapezoid htrapezoid z hz
      hactiveIterated
  · intro level z hz hactive
    have hactiveIterated :
        horizontalSlice data.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hactive)
      intro point hpoint
      exact ⟨hsubIterated.union_subset hpoint.1, hpoint.2⟩
    exact data.active_height_coverage level z hz hactiveIterated

end Kakeya.Assouad

end
