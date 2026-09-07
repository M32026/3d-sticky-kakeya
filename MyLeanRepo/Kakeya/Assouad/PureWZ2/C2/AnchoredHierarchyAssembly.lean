import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyAnchoring

/-!
# Carrier-independent assembly of the pure anchored hierarchy

The finite popularity iteration must still produce one final shading and the
per-level trapezoids below.  Once those data include active endpoints, the
unique numerical parent is a purely one-dimensional consequence of scale
separation and slope approximation.  This module reuses that closed argument
without importing a `UniformTubeStructure` into the pure output.
-/

noncomputable section

namespace Kakeya.Assouad

/-- All anchored Corollary-26 data except the derived adjacent-level parent. -/
structure PureWZ2HierarchyWithoutParents
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sourceSlope : ℝ → ℝ)
    (hierarchyLoss : ℝ) where
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  hierarchyLoss_pos : 0 < hierarchyLoss
  vertical_bound :
    ∀ point ∈ shading.union, point 2 ∈ Set.Icc (-1 : ℝ) 1
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  trapezoids : Fin levelCount → Finset WZ1VerticalTrapezoid
  level_nonempty : ∀ level, (trapezoids level).Nonempty
  height_eq :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      trapezoid.height =
        wz1Corollary26Scale delta levelCount level
  slope_bound :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      |trapezoid.slope| ≤ 2
  length_bounds :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      Real.rpow
            (wz1Corollary26Scale delta levelCount level)
            (1 / 2 + hierarchyLoss) ≤
          trapezoid.length ∧
        trapezoid.length ≤
          Real.sqrt (wz1Corollary26Scale delta levelCount level)
  separated_cores :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      ∀ other ∈ trapezoids level, trapezoid ≠ other →
        ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
          Real.sqrt (wz1Corollary26Scale delta levelCount level) ≤
            |z - w|
  active_endpoints :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      horizontalSlice shading.union trapezoid.left ≠ ∅ ∧
        horizontalSlice shading.union trapezoid.right ≠ ∅
  slope_approximation :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      ∀ z ∈ trapezoid.core,
        horizontalSlice shading.union z ≠ ∅ →
          |sourceSlope z - trapezoid.affine z| ≤
            wz1Corollary26Scale delta levelCount level
  active_height_coverage :
    ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice shading.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids level, z ∈ trapezoid.core

namespace PureWZ2HierarchyWithoutParents

/-- Derive the unique adjacent-level parent and close the pure hierarchy. -/
noncomputable def toAnchoredHierarchy
    {delta hierarchyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {sourceSlope : ℝ → ℝ}
    (data :
      PureWZ2HierarchyWithoutParents
        shading sourceSlope hierarchyLoss) :
    PureWZ2AnchoredHierarchyData
      shading sourceSlope hierarchyLoss where
  levelCount := data.levelCount
  levelCount_two := data.levelCount_two
  trapezoids := data.trapezoids
  level_nonempty := data.level_nonempty
  height_eq := data.height_eq
  slope_bound := data.slope_bound
  length_bounds := data.length_bounds
  separated_cores := data.separated_cores
  active_endpoints := data.active_endpoints
  slope_approximation := data.slope_approximation
  active_height_coverage := data.active_height_coverage
  unique_parent := by
    apply
      prove_unique_parent_generic
        (N := data.levelCount)
        (delta := delta)
        (hierarchyLoss := hierarchyLoss)
        (BF := wz1PaperBodyFamily family)
        (Z := shading)
        (sourceSlope := sourceSlope)
        data.delta_pos data.delta_le_one data.hierarchyLoss_pos
    · exact data.vertical_bound
    · exact data.level_nonempty
    · exact data.height_eq
    · exact data.length_bounds
    · exact data.separated_cores
    · exact data.active_height_coverage
    · exact data.slope_approximation
    · exact data.active_endpoints

end PureWZ2HierarchyWithoutParents

end Kakeya.Assouad

end
