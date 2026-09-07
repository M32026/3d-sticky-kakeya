import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26Statements

/-!
# Repaired WZ1 Corollary 26 boundaries

The first Corollary 26 API omitted four quantitative inputs used by the paper:

* an absolute bound for the source slope;
* active witnesses at both endpoints of every trapezoid core;
* numerical parent-child center-line control rather than literal strip
  containment with unit constants;
* a relation between the number of levels, the hierarchy loss, the final
  power-loss budget, and the small source scale.

This module records those inputs without changing the still-useful one-scale
producer.
-/

namespace Kakeya.Assouad

/--
Paper-level nesting of adjacent Corollary 26 trapezoids.

The core is nested, and the two affine center lines differ by at most the sum
of their scale heights.  This is the literal quantitative content obtained
from approximating the same source slope at adjacent scales.
-/
def WZ1VerticalTrapezoid.IsNumericallyNestedIn
    (child parent : WZ1VerticalTrapezoid) : Prop :=
  child.core ⊆ parent.core ∧
    ∀ z ∈ child.core,
      |child.affine z - parent.affine z| ≤
        child.height + parent.height

/--
Anchored finite Corollary 26 hierarchy on one final retained shading.

Every trapezoid has active source heights at both endpoints.  This rules out
unused trapezoids with arbitrary intercepts and supplies the endpoint values
needed by the Proposition 27 extension costs.
-/
structure WZ1Corollary26AnchoredHierarchyData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sourceSlope : ℝ → ℝ)
    (hierarchyLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  trapezoids :
    Fin levelCount → Finset WZ1VerticalTrapezoid
  level_nonempty :
    ∀ level, (trapezoids level).Nonempty
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
          Real.sqrt
            (wz1Corollary26Scale delta levelCount level)
  separated_cores :
    ∀ level,
      ∀ trapezoid ∈ trapezoids level,
        ∀ other ∈ trapezoids level,
          trapezoid ≠ other →
            ∀ z ∈ trapezoid.core,
              ∀ w ∈ other.core,
                Real.sqrt
                    (wz1Corollary26Scale
                      delta levelCount level) ≤
                  |z - w|
  active_endpoints :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      horizontalSlice Y.union trapezoid.left ≠ ∅ ∧
        horizontalSlice Y.union trapezoid.right ≠ ∅
  slope_approximation :
    ∀ level,
      ∀ trapezoid ∈ trapezoids level,
        ∀ z ∈ trapezoid.core,
          horizontalSlice Y.union z ≠ ∅ →
            |sourceSlope z - trapezoid.affine z| ≤
              wz1Corollary26Scale delta levelCount level
  active_height_coverage :
    ∀ level,
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Y.union z ≠ ∅ →
          ∃ trapezoid ∈ trapezoids level,
            z ∈ trapezoid.core
  unique_parent :
    ∀ parentLevel childLevel : Fin levelCount,
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! parent,
            parent ∈ trapezoids parentLevel ∧
              child.IsNumericallyNestedIn parent

/--
Same-configuration anchored Corollary 26 output.

The AD and local-grain constants are weakened to the hierarchy-loss power.
This absorbs the fixed losses from repeated refinement while preserving the
source family, plane map, and global slope.
-/
structure WZ1Corollary26AnchoredHierarchyPackage
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (hierarchyLoss : ℝ) where
  shading :
    Kakeya.Streamlined.TubeShading source.family
  subshading : IsSubshading shading source.shading
  extremal :
    WZ1ExtremalPair sigma hierarchyLoss
      source.family source.uniform shading
  local_grains :
    WZ1LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-hierarchyLoss))
  planeMap_eq :
    local_grains.planeMap = source.local_grains.planeMap
  planeMap_lipschitz_bound :
    (local_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-hierarchyLoss)
  source_global_slab_ad :
    HasGlobalSlabAD shading
      source.global_grains.slope sigma
      (Kakeya.realRpowENN delta (-hierarchyLoss))
  source_slope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |source.global_grains.slope z| ≤ 3
  hierarchy :
    WZ1Corollary26AnchoredHierarchyData
      shading source.global_grains.slope hierarchyLoss

/--
Paper-faithful direct Corollary 26 conclusion.

The projection dichotomy is the substantial predecessor.  The source slope
bound is explicit because the abstract Proposition 9 package currently stores
only a Lipschitz seminorm, which is invariant under adding a large constant.
-/
def WZ1Corollary26AnchoredHierarchyConclusion : Prop :=
  ∀ sigma hierarchyLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < hierarchyLoss →
      HasWZ1CriticalVolumeFloor sigma →
      ∀ levelCount : ℕ, 2 ≤ levelCount →
        ∃ sourceLossCeiling delta₀ : ℝ,
          0 < sourceLossCeiling ∧
          sourceLossCeiling ≤ hierarchyLoss / 100 ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ inputLoss : ℝ,
            0 < inputLoss → inputLoss ≤ sourceLossCeiling →
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ source :
                  WZ1PlaninessGraininessPackage
                    sigma inputLoss delta,
                ∃ package :
                    WZ1Corollary26AnchoredHierarchyPackage
                      source hierarchyLoss,
                  package.hierarchy.levelCount = levelCount

/--
WZ1 Lemma 25 / Corollary 26 from the proved one-scale locally-linear
producers.

The hierarchy proof owns the finite loss schedule, descending popularity
refinements, active endpoints, and adjacent parent nesting.  It must not
reconstruct either the intermediate-window geometry isolated in
`WZ1LocallyLinearOneScaleStatement` or the exact-`delta` geometry isolated in
`WZ1LocallyLinearTerminalScaleStatement`.
-/
def WZ1Corollary26AnchoredHierarchyStatement : Prop :=
  WZ1LocallyLinearOneScaleConclusion →
    WZ1LocallyLinearTerminalScaleConclusion →
      WZ1Corollary26AnchoredHierarchyConclusion

/--
Certificate relating a correction segment to an anchored Corollary 26
trapezoid and its numerical parent.
-/
structure WZ1Corollary26SegmentSource
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {sourceSlope : ℝ → ℝ}
    {hierarchyLoss : ℝ}
    (hierarchy :
      WZ1Corollary26AnchoredHierarchyData
        Y sourceSlope hierarchyLoss)
    (level : Fin hierarchy.levelCount)
    (segment : WZ1SegmentCorrection) where
  trapezoid : WZ1VerticalTrapezoid
  trapezoid_mem :
    trapezoid ∈ hierarchy.trapezoids level
  parent :
    Option WZ1VerticalTrapezoid
  parent_at_first :
    (level : ℕ) = 0 → parent = none
  parent_after_first :
    ∀ parentLevel : Fin hierarchy.levelCount,
      (parentLevel : ℕ) + 1 = (level : ℕ) →
        ∃ parentTrapezoid,
          parent = some parentTrapezoid ∧
          parentTrapezoid ∈
            hierarchy.trapezoids parentLevel ∧
          trapezoid.IsNumericallyNestedIn parentTrapezoid
  core_eq :
    segment.core = trapezoid.core
  affine_eq :
    ∀ z ∈ segment.core,
      segment.affine z =
        match parent with
        | none => trapezoid.affine z
        | some parentTrapezoid =>
            trapezoid.affine z - parentTrapezoid.affine z

/--
Final-loss weakening of the retained Corollary 26 source on the original
family.

The fixed AD losses from replacing the source slope by the final
piecewise-affine slope are absorbed into `delta^(-finalLoss)` before the closed
Proposition 27 assembler is called.
-/
structure WZ1Corollary26FinalSourceData
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (finalLoss : ℝ) where
  finalLoss_pos : 0 < finalLoss
  shading :
    Kakeya.Streamlined.TubeShading source.family
  subshading : IsSubshading shading source.shading
  extremal :
    WZ1ExtremalPair sigma finalLoss
      source.family source.uniform shading
  local_grains :
    WZ1LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-finalLoss))
  planeMap_eq :
    local_grains.planeMap = source.local_grains.planeMap
  planeMap_lipschitz_bound :
    (local_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-finalLoss)
  global_grains :
    WZ1LipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-finalLoss))
  global_grains_slope_eq :
    global_grains.slope = source.global_grains.slope
  slope_lipschitz_bound :
    (global_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-finalLoss)
  slope_one_lipschitz :
    LipschitzOnWith 1 global_grains.slope (Set.Icc (-1 : ℝ) 1)
  slope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |global_grains.slope z| ≤ 3
  planeMap_vertical_bound :
    ∀ p ∈ shading.union,
      |local_grains.planeMap p (2 : Fin 3)| ≤ 1 / 2
  planeMap_one_lipschitz :
    LipschitzOnWith 1 local_grains.planeMap shading.union

namespace WZ1Corollary26FinalSourceData

/-- Expose the final-loss source in the legacy Proposition 27 input format. -/
noncomputable def toPlaninessGraininessPackage
    {sigma inputLoss delta finalLoss : ℝ}
    {source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta}
    (data : WZ1Corollary26FinalSourceData source finalLoss) :
    WZ1PlaninessGraininessPackage sigma finalLoss delta where
  family := source.family
  uniform := source.uniform
  shading := data.shading
  vertical_chart := source.vertical_chart
  constant := Kakeya.realRpowENN delta (-finalLoss)
  extremal := data.extremal
  constant_one := by
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        data.extremal.1 data.extremal.2.1 (by linarith [data.finalLoss_pos])
  constant_ne_top := by
    simp [Kakeya.realRpowENN]
  constant_bound := le_rfl
  global_grains := data.global_grains
  local_grains := data.local_grains
  slope_lipschitz_bound := data.slope_lipschitz_bound
  slope_one_lipschitz := data.slope_one_lipschitz
  slope_bound := data.slope_bound
  planeMap_vertical_bound := data.planeMap_vertical_bound
  planeMap_lipschitz_bound := data.planeMap_lipschitz_bound
  planeMap_one_lipschitz := data.planeMap_one_lipschitz

end WZ1Corollary26FinalSourceData

/-- Budgeted Proposition 27 input produced from an anchored hierarchy. -/
structure WZ1Corollary26BudgetedCorrectionPackage
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (finalLoss : ℝ) where
  finalSource :
    WZ1Corollary26FinalSourceData source finalLoss
  rawLoss : ℝ
  rawLoss_pos : 0 < rawLoss
  rawLoss_le : rawLoss ≤ finalLoss / 10
  corrections :
    WZ1MultiscaleSlopeCorrectionData
      finalSource.shading sigma
      (Kakeya.realRpowENN delta (-finalLoss)) rawLoss

namespace WZ1Corollary26BudgetedCorrectionPackage

/-- Forget the repaired Corollary 26 provenance and expose the closed
Proposition 27 input package. -/
def toMultiscaleSlopeCorrectionPackage
    {sigma inputLoss delta finalLoss : ℝ}
    {source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta}
    (package :
      WZ1Corollary26BudgetedCorrectionPackage source finalLoss) :
    WZ1MultiscaleSlopeCorrectionPackage
      package.finalSource.toPlaninessGraininessPackage finalLoss where
  rawLoss := package.rawLoss
  rawLoss_pos := package.rawLoss_pos
  rawLoss_le := package.rawLoss_le
  shading := package.finalSource.shading
  subshading := by
    intro i
    exact Set.Subset.rfl
  extremal := package.finalSource.extremal
  local_grains := package.finalSource.local_grains
  planeMap_eq := rfl
  planeMap_lipschitz_bound :=
    package.finalSource.planeMap_lipschitz_bound
  corrections := package.corrections

end WZ1Corollary26BudgetedCorrectionPackage

/--
Repaired Corollary 26 to Proposition 27 conversion.

The strict budget inequality is the paper's exponent
`1 / levelCount + 2 * hierarchyLoss`, with slack for fixed constants.  The
source threshold is selected before the hierarchy package.  The source loss
must be no larger than the hierarchy loss so that its slope Lipschitz bound
can be weakened to the final loss.
-/
def WZ1Corollary26BudgetedSegmentConversionStatement : Prop :=
  ∀ finalLoss hierarchyLoss : ℝ,
    0 < finalLoss → 0 < hierarchyLoss →
    hierarchyLoss ≤ finalLoss →
    ∀ levelCount : ℕ, 2 ≤ levelCount →
      1 / (levelCount : ℝ) + 2 * hierarchyLoss <
        finalLoss / 10 →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ {sigma inputLoss delta : ℝ},
          0 < delta → delta ≤ delta₀ →
          ∀ {source :
              WZ1PlaninessGraininessPackage
                sigma inputLoss delta},
            inputLoss ≤ hierarchyLoss →
            ∀ hierarchy :
                WZ1Corollary26AnchoredHierarchyPackage
                  source hierarchyLoss,
              hierarchy.hierarchy.levelCount = levelCount →
              ∃ package :
                  WZ1Corollary26BudgetedCorrectionPackage
                    source finalLoss,
                package.finalSource.shading = hierarchy.shading ∧
                  package.finalSource.global_grains.slope =
                    source.global_grains.slope ∧
                  ∃ levelCount_eq :
                      package.corrections.levelCount =
                        hierarchy.hierarchy.levelCount,
                    ∃ segmentFor :
                        ∀ level :
                            Fin hierarchy.hierarchy.levelCount,
                          ∀ trapezoid ∈
                              hierarchy.hierarchy.trapezoids level,
                            WZ1SegmentCorrection,
                      (∀ level trapezoid htrapezoid,
                        segmentFor level trapezoid htrapezoid ∈
                          package.corrections.segments
                            (Fin.cast levelCount_eq.symm level)) ∧
                      (∀ level trapezoid htrapezoid,
                        Nonempty
                          (WZ1Corollary26SegmentSource
                            hierarchy.hierarchy level
                            (segmentFor
                              level trapezoid htrapezoid))) ∧
                      (∀ level,
                        ∀ segment ∈
                            package.corrections.segments level,
                          ∃ trapezoid htrapezoid,
                            segment =
                              segmentFor
                                (Fin.cast levelCount_eq level)
                                trapezoid htrapezoid)

/--
Recover the legacy nested-correction producer from the two repaired
Corollary 26 leaves.

This adapter only chooses the number of levels, the hierarchy loss, and a
common source threshold.  All geometric work remains in the anchored
hierarchy and budgeted segment-conversion inputs.
-/
def WZ1NestedSlopeCorrectionsFromRepairedStatement : Prop :=
  WZ1CriticalFloorNormalizationStatement →
    WZ1LocallyLinearOneScaleStatement →
    WZ1LocallyLinearTerminalScaleStatement →
      WZ1Corollary26AnchoredHierarchyStatement →
        WZ1Corollary26BudgetedSegmentConversionStatement →
          WZ1NestedSlopeCorrectionsStatement

end Kakeya.Assouad
