import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRichSetTrapezoid

/-!
# Append an exact terminal level to an ordinary Corollary-5.6 prefix

The first `N - 1` levels are produced by the ordinary one-scale construction
at the paper scales `delta^((j+1)/N)`.  The last level is the non-cubical exact
terminal carrier at scale `delta`.  This file records only the common raw
geometry needed by the carrier-generic popularity and reanchoring argument.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The ordinary part of Corollary 5.6 after the final whole-cell refinement
and same-extremizer grain restoration, but before the exact terminal level is
appended.  The scale denominator remains the final total `N`. -/
structure PureWZ2OrdinaryHierarchyPrefixData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (hierarchyLoss : ℝ) (N : ℕ) where
  levelCount_two : 2 ≤ N
  trapezoids : ∀ level : Fin N, (level : ℕ) + 1 < N →
    Finset WZ1VerticalTrapezoid
  level_nonempty : ∀ level hlevel, (trapezoids level hlevel).Nonempty
  height_eq : ∀ level hlevel, ∀ trapezoid ∈ trapezoids level hlevel,
    trapezoid.height = wz1Corollary26Scale delta N level
  slope_bound : ∀ level hlevel, ∀ trapezoid ∈ trapezoids level hlevel,
    |trapezoid.slope| ≤ 2
  length_bounds : ∀ level hlevel, ∀ trapezoid ∈ trapezoids level hlevel,
    Real.rpow (wz1Corollary26Scale delta N level)
          (1 / 2 + hierarchyLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt (wz1Corollary26Scale delta N level)
  separated_cores : ∀ level hlevel, ∀ trapezoid ∈ trapezoids level hlevel,
    ∀ other ∈ trapezoids level hlevel, trapezoid ≠ other →
      ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
        Real.sqrt (wz1Corollary26Scale delta N level) ≤ |z - w|
  slope_approximation :
    ∀ level hlevel, ∀ trapezoid ∈ trapezoids level hlevel,
      ∀ z ∈ trapezoid.core,
        horizontalSlice source.shading.union z ≠ ∅ →
          |source.globalGrains.slope z - trapezoid.affine z| ≤
            wz1Corollary26Scale delta N level
  active_height_coverage :
    ∀ level hlevel, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice source.shading.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids level hlevel, z ∈ trapezoid.core

/-- Raw heterogeneous hierarchy on its exact final carrier.  No cubicality or
extremality is asserted after the last height-only crop. -/
structure PureWZ2MixedRawHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (finalLoss hierarchyLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  shading : WZ1PaperTubeShading source.family
  subshading : PureWZ2PaperIsSubshading shading source.shading
  volume_lower : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
    volume shading.union
  localGrains : PureWZ2LocalGrainData shading sigma
    (Kakeya.realRpowENN delta (-finalLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  sourceGlobalGrains : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
    (Kakeya.realRpowENN delta (-finalLoss))
  source_slope_eq : sourceGlobalGrains.slope = source.globalGrains.slope
  trapezoids : Fin levelCount → Finset WZ1VerticalTrapezoid
  level_nonempty : ∀ level, (trapezoids level).Nonempty
  height_eq : ∀ level, ∀ trapezoid ∈ trapezoids level,
    trapezoid.height = wz1Corollary26Scale delta levelCount level
  slope_bound : ∀ level, ∀ trapezoid ∈ trapezoids level,
    |trapezoid.slope| ≤ 2
  length_bounds : ∀ level, ∀ trapezoid ∈ trapezoids level,
    Real.rpow (wz1Corollary26Scale delta levelCount level)
          (1 / 2 + hierarchyLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤
        Real.sqrt (wz1Corollary26Scale delta levelCount level)
  separated_cores : ∀ level, ∀ trapezoid ∈ trapezoids level,
    ∀ other ∈ trapezoids level, trapezoid ≠ other →
      ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
        Real.sqrt (wz1Corollary26Scale delta levelCount level) ≤ |z - w|
  slope_approximation : ∀ level, ∀ trapezoid ∈ trapezoids level,
    ∀ z ∈ trapezoid.core,
      horizontalSlice shading.union z ≠ ∅ →
        |sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta levelCount level
  active_height_coverage : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    horizontalSlice shading.union z ≠ ∅ →
      ∃ trapezoid ∈ trapezoids level, z ∈ trapezoid.core

/-- Source-parametric exact-terminal producer required after the ordinary
`N - 1` hierarchy prefix.  The source is universally quantified after the
scale threshold, so the producer cannot replace the recursively retained
prefix source by an unrelated critical configuration. -/
def PureWZ2ExactTerminalScaleAtStatement (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : PureWZ2QuantitativeGrainConfiguration
                sigma inputLoss delta,
              Nonempty (PureWZ2ExactTerminalLevelData source outputLoss)

/-- Uniform exact-terminal producer. -/
def PureWZ2ExactTerminalScaleStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2ExactTerminalScaleAtStatement sigma

/-- The thresholds and source-parametric constructor selected by one exact
terminal invocation, before the runtime source is known. -/
structure PureWZ2ExactTerminalScaleSchedule
    (sigma outputLoss : ℝ) where
  sourceLossCeiling : ℝ
  delta₀ : ℝ
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_le : sourceLossCeiling ≤ outputLoss / 100
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  produce :
    ∀ inputLoss : ℝ,
      0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
          Nonempty (PureWZ2ExactTerminalLevelData source outputLoss)

/-- Select the exact-terminal thresholds before the recursive prefix produces
its final runtime source. -/
theorem pureWZ2_select_exactTerminalScaleSchedule
    {sigma outputLoss : ℝ}
    (terminal : PureWZ2ExactTerminalScaleAtStatement sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtputLoss : 0 < outputLoss) :
    Nonempty (PureWZ2ExactTerminalScaleSchedule sigma outputLoss) := by
  rcases terminal outputLoss hsigma hsigmaOne houtputLoss with
    ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
      hsourceLossCeilingLe, hdelta₀, hdelta₀One, produce⟩
  exact ⟨{
    sourceLossCeiling := sourceLossCeiling
    delta₀ := delta₀
    sourceLossCeiling_pos := hsourceLossCeiling
    sourceLossCeiling_le := hsourceLossCeilingLe
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    produce := produce }⟩

namespace PureWZ2LocallyLinearOneScaleData

/-- Forget the extra cubical/extremal fields of an ordinary one-scale output
whose scale is definitionally the source scale. -/
noncomputable def toExactTerminalLevelAtSourceScale
    {sigma inputLoss delta outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source outputLoss delta) :
    PureWZ2ExactTerminalLevelData source outputLoss where
  shading := data.shading
  subshading := data.subshading
  volume_lower := data.volume_lower
  localGrains := data.localGrains
  planeMap_vertical_bound := data.planeMap_vertical_bound
  sourceGlobalGrains := data.globalGrains
  source_slope_eq := data.slope_eq
  trapezoids := data.trapezoids
  trapezoids_nonempty := data.trapezoids_nonempty
  height_eq := data.height_eq
  slope_bound := data.slope_bound
  length_bounds := data.length_bounds
  separated_cores := data.separated_cores
  slope_approximation := data.slope_approximation
  active_height_coverage := data.active_height_coverage

end PureWZ2LocallyLinearOneScaleData

/-- The historical terminal one-scale interface implies the weaker exact
terminal interface without changing the chosen runtime source. -/
theorem pureWZ2_exactTerminalScaleAt_of_locallyLinearTerminal
    {sigma : ℝ}
    (terminal : PureWZ2LocallyLinearTerminalScaleAtStatement sigma) :
    PureWZ2ExactTerminalScaleAtStatement sigma := by
  intro outputLoss hsigma hsigmaOne houtputLoss
  rcases terminal outputLoss hsigma hsigmaOne houtputLoss with
    ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
      hsourceLossCeilingLe, hdelta₀, hdelta₀One, produce⟩
  refine ⟨sourceLossCeiling, delta₀, hsourceLossCeiling,
    hsourceLossCeilingLe, hdelta₀, hdelta₀One, ?_⟩
  intro inputLoss hinputLoss hinputLossLe delta hdelta hdeltaLe source
  rcases produce inputLoss hinputLoss hinputLossLe delta hdelta hdeltaLe
      source with ⟨output⟩
  exact ⟨output.toExactTerminalLevelAtSourceScale⟩

/-- Append the exact `delta` endpoint while retaining the total hierarchy
depth as a dependent equality. -/
theorem PureWZ2OrdinaryHierarchyPrefixData.appendExactTerminalWithLevelCountAndShading
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {N : ℕ}
    (ordinary : PureWZ2OrdinaryHierarchyPrefixData source hierarchyLoss N)
    (terminal : PureWZ2ExactTerminalLevelData source finalLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss) :
    Nonempty { mixed : PureWZ2MixedRawHierarchyData
        source finalLoss hierarchyLoss //
      mixed.levelCount = N ∧ mixed.shading = terminal.shading } := by
  let trapezoids : Fin N → Finset WZ1VerticalTrapezoid := fun level =>
    if hlevel : (level : ℕ) + 1 < N then
      ordinary.trapezoids level hlevel
    else terminal.trapezoids
  have hlast : ∀ level : Fin N, ¬ (level : ℕ) + 1 < N →
      level = pureWZ2FinLast N ordinary.levelCount_two := by
    intro level hlevel
    apply Fin.ext
    simp only [pureWZ2FinLast]
    omega
  have hterminalScale : wz1Corollary26Scale delta N
      (pureWZ2FinLast N ordinary.levelCount_two) = delta :=
    pureWZ2HierarchyScale_last ordinary.levelCount_two source.extremal.delta_pos
  have hterminalLower : Real.rpow delta (1 / 2 + hierarchyLoss) ≤
      Real.rpow delta (1 / 2 + finalLoss) :=
    Real.rpow_le_rpow_of_exponent_ge source.extremal.delta_pos
      source.extremal.delta_le_one (by linarith)
  refine ⟨⟨{
      levelCount := N
      levelCount_two := ordinary.levelCount_two
      shading := terminal.shading
      subshading := terminal.subshading
      volume_lower := terminal.volume_lower
      localGrains := terminal.localGrains
      planeMap_vertical_bound := terminal.planeMap_vertical_bound
      sourceGlobalGrains := terminal.sourceGlobalGrains
      source_slope_eq := terminal.source_slope_eq
      trapezoids := trapezoids
      level_nonempty := ?_
      height_eq := ?_
      slope_bound := ?_
      length_bounds := ?_
      separated_cores := ?_
      slope_approximation := ?_
      active_height_coverage := ?_ }, ?_⟩⟩
  · intro level
    by_cases hlevel : (level : ℕ) + 1 < N
    · simpa [trapezoids, hlevel] using ordinary.level_nonempty level hlevel
    · simpa [trapezoids, hlevel] using terminal.trapezoids_nonempty
  · intro level trapezoid htrapezoid
    by_cases hlevel : (level : ℕ) + 1 < N
    · exact ordinary.height_eq level hlevel trapezoid (by
        simpa [trapezoids, hlevel] using htrapezoid)
    · have hlevelLast := hlast level hlevel
      have hheight := terminal.height_eq trapezoid (by
        simpa [trapezoids, hlevel] using htrapezoid)
      rw [hlevelLast, hterminalScale]
      exact hheight
  · intro level trapezoid htrapezoid
    by_cases hlevel : (level : ℕ) + 1 < N
    · exact ordinary.slope_bound level hlevel trapezoid (by
        simpa [trapezoids, hlevel] using htrapezoid)
    · exact terminal.slope_bound trapezoid (by
        simpa [trapezoids, hlevel] using htrapezoid)
  · intro level trapezoid htrapezoid
    by_cases hlevel : (level : ℕ) + 1 < N
    · exact ordinary.length_bounds level hlevel trapezoid (by
        simpa [trapezoids, hlevel] using htrapezoid)
    · have hlevelLast := hlast level hlevel
      have hbounds := terminal.length_bounds trapezoid (by
        simpa [trapezoids, hlevel] using htrapezoid)
      rw [hlevelLast, hterminalScale]
      exact ⟨hterminalLower.trans hbounds.1, hbounds.2⟩
  · intro level first hfirst second hsecond hne z hz w hw
    by_cases hlevel : (level : ℕ) + 1 < N
    · exact ordinary.separated_cores level hlevel first
        (by simpa [trapezoids, hlevel] using hfirst) second
        (by simpa [trapezoids, hlevel] using hsecond) hne z hz w hw
    · have hlevelLast := hlast level hlevel
      have hsep := terminal.separated_cores first
        (by simpa [trapezoids, hlevel] using hfirst) second
        (by simpa [trapezoids, hlevel] using hsecond) hne z hz w hw
      rw [hlevelLast, hterminalScale]
      exact hsep
  · intro level trapezoid htrapezoid z hz hslice
    by_cases hlevel : (level : ℕ) + 1 < N
    · have hsourceSlice : horizontalSlice source.shading.union z ≠ ∅ := by
        apply Set.Nonempty.ne_empty
        apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
        intro point hpoint
        exact ⟨terminal.subshading.union_subset hpoint.1, hpoint.2⟩
      rw [terminal.source_slope_eq]
      exact ordinary.slope_approximation level hlevel trapezoid
        (by simpa [trapezoids, hlevel] using htrapezoid) z hz hsourceSlice
    · have hlevelLast := hlast level hlevel
      have happ := terminal.slope_approximation trapezoid
        (by simpa [trapezoids, hlevel] using htrapezoid) z hz hslice
      rw [hlevelLast, hterminalScale]
      exact happ
  · intro level z hz hslice
    by_cases hlevel : (level : ℕ) + 1 < N
    · have hsourceSlice : horizontalSlice source.shading.union z ≠ ∅ := by
        apply Set.Nonempty.ne_empty
        apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
        intro point hpoint
        exact ⟨terminal.subshading.union_subset hpoint.1, hpoint.2⟩
      rcases ordinary.active_height_coverage level hlevel z hz hsourceSlice with
        ⟨trapezoid, htrapezoid, hcore⟩
      exact ⟨trapezoid, by simpa [trapezoids, hlevel] using htrapezoid, hcore⟩
    · rcases terminal.active_height_coverage z hz hslice with
        ⟨trapezoid, htrapezoid, hcore⟩
      exact ⟨trapezoid, by simpa [trapezoids, hlevel] using htrapezoid, hcore⟩
  · exact ⟨rfl, rfl⟩

/-- Compatibility projection which retains only the hierarchy depth. -/
theorem PureWZ2OrdinaryHierarchyPrefixData.appendExactTerminalWithLevelCount
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {N : ℕ}
    (ordinary : PureWZ2OrdinaryHierarchyPrefixData source hierarchyLoss N)
    (terminal : PureWZ2ExactTerminalLevelData source finalLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss) :
    Nonempty { mixed : PureWZ2MixedRawHierarchyData
        source finalLoss hierarchyLoss // mixed.levelCount = N } := by
  rcases ordinary.appendExactTerminalWithLevelCountAndShading terminal
      hfinalHierarchy with ⟨mixed⟩
  exact ⟨⟨mixed.1, mixed.2.1⟩⟩

/-- Compatibility projection which forgets the retained depth equality. -/
theorem PureWZ2OrdinaryHierarchyPrefixData.appendExactTerminal
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {N : ℕ}
    (ordinary : PureWZ2OrdinaryHierarchyPrefixData source hierarchyLoss N)
    (terminal : PureWZ2ExactTerminalLevelData source finalLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss) :
    Nonempty (PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss) := by
  rcases ordinary.appendExactTerminalWithLevelCount terminal hfinalHierarchy with
    ⟨mixed⟩
  exact ⟨mixed.1⟩

end Kakeya.Assouad

end
