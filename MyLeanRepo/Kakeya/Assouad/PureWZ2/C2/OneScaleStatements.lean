import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Refinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26RepairedStatements

/-!
# Pure paper-carrier locally-linear outputs

These are the carrier-faithful analogues of the old UTS-valued Corollary-26
interfaces.  They retain the cropped paper family and whole-cell shading and
therefore do not insert `UniformTubeStructure` into the canonical proof.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One retained pure configuration with locally affine slope data at `rho`. -/
structure PureWZ2LocallyLinearOneScaleData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (outputLoss rho : ℝ) where
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  shading : WZ1PaperTubeShading source.family
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss source.family shading
  volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      MeasureTheory.volume shading.union
  localGrains :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  globalGrains :
    PureWZ2BoundedLipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))
  slope_eq : globalGrains.slope = source.globalGrains.slope
  trapezoids : Finset WZ1VerticalTrapezoid
  trapezoids_nonempty : trapezoids.Nonempty
  height_eq :
    ∀ trapezoid ∈ trapezoids, trapezoid.height = rho
  slope_bound :
    ∀ trapezoid ∈ trapezoids, |trapezoid.slope| ≤ 2
  length_bounds :
    ∀ trapezoid ∈ trapezoids,
      Real.rpow rho (1 / 2 + outputLoss) ≤
          trapezoid.length ∧
        trapezoid.length ≤ Real.sqrt rho
  separated_cores :
    ∀ trapezoid ∈ trapezoids,
      ∀ other ∈ trapezoids, trapezoid ≠ other →
        ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
          Real.sqrt rho ≤ |z - w|
  slope_approximation :
    ∀ trapezoid ∈ trapezoids,
      ∀ z ∈ trapezoid.core,
        horizontalSlice shading.union z ≠ ∅ →
          |globalGrains.slope z - trapezoid.affine z| ≤ rho
  active_height_coverage :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice shading.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids, z ∈ trapezoid.core

/--
Carrier-independent anchored Corollary-26 hierarchy on a cropped paper
shading.  This is the exact numerical content consumed by Proposition 27.
-/
structure PureWZ2AnchoredHierarchyData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sourceSlope : ℝ → ℝ)
    (hierarchyLoss : ℝ) where
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
  unique_parent :
    ∀ parentLevel childLevel : Fin levelCount,
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! parent, parent ∈ trapezoids parentLevel ∧
            child.IsNumericallyNestedIn parent

/-- A finite retained hierarchy on one final cropped paper shading. -/
structure PureWZ2LocallyLinearHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (finalLoss hierarchyLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  shading : WZ1PaperTubeShading source.family
  subshading : PureWZ2PaperIsSubshading shading source.shading
  volume_lower :
    Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      MeasureTheory.volume shading.union
  localGrains :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-finalLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  sourceGlobalGrains :
    PureWZ2BoundedLipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-finalLoss))
  source_slope_eq :
    sourceGlobalGrains.slope = source.globalGrains.slope
  hierarchy :
    PureWZ2AnchoredHierarchyData
      shading sourceGlobalGrains.slope hierarchyLoss

/--
The genuine one-scale WZ Lemmas 23--24 producer in the cropped paper model.
The projection theorem is supplied by the closed local OSW development; no
new analytic hypothesis is exposed.
-/
def PureWZ2LocallyLinearOneScaleAtStatement (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
              ∀ rho : ℝ,
                delta ≤ rho → rho ≤ 1 →
                Real.rpow delta (1 - outputLoss) ≤ rho →
                rho ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2LocallyLinearOneScaleData
                      source outputLoss rho)

/-- Uniform ordinary one-scale producer, quantified over the ambient
critical exponent.  Hierarchy construction for one fixed critical package
uses `PureWZ2LocallyLinearOneScaleAtStatement` instead. -/
def PureWZ2LocallyLinearOneScaleStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2LocallyLinearOneScaleAtStatement sigma

/-- Exact-terminal-scale version used at the final Corollary-26 level. -/
def PureWZ2LocallyLinearTerminalScaleAtStatement (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
              Nonempty
                (PureWZ2LocallyLinearOneScaleData
                  source outputLoss delta)

/-- Uniform exact-terminal producer. -/
def PureWZ2LocallyLinearTerminalScaleStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2LocallyLinearTerminalScaleAtStatement sigma

end Kakeya.Assouad
