import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.TubeBaseAlignment
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import Mathlib.Tactic

/-!
# Bounded support for Proposition 6.2 metric parents

A radius-`delta` ordinary tube with base norm at most four lies in the fixed
box `axisBox 12 12 12` when `delta ≤ 1 / 100`.  The family and subfamily
forms below isolate the support input needed when the V4 metric-parent
pipeline is changed from `IsInUnitBall` to `HasBoundedBase _ 4`.

The line-class hypothesis is retained in the family-facing interface used by
the Proposition 6.2 pipeline, although the elementary norm estimate only
uses the unit direction stored by `DeltaTube`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A base bound by four supplies the existing pipeline's relaxed bound by
five. -/
theorem pureWZ2Prop62_base_norm_le_five_of_boundedBase_four
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (boundedBase : HasBoundedBase family 4) :
    ∀ index, ‖(family.tube index).base‖ ≤ 5 := by
  intro index
  exact (boundedBase index).trans (by norm_num)

/-- A small ordinary tube with bounded base lies in a fixed ambient box. -/
theorem pureWZ2Prop62_tube_carrier_subset_axisBox_twelve
    {delta : ℝ}
    (deltaNonnegative : 0 ≤ delta)
    (deltaLe : delta ≤ 1 / 100)
    (tube : Kakeya.DeltaTube delta)
    (_line : WZ1PaperTubeInLineClass tube)
    (baseBound : ‖tube.base‖ ≤ 4) :
    tube.carrier ⊆
      Kakeya.Streamlined.axisBox 12 12 12 := by
  intro point pointMem
  rcases
      tube_carrier_decomp deltaNonnegative tube point pointMem with
    ⟨parameter, parameterMem, error, errorNorm, pointEq⟩
  have parameterAbs : |parameter| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [parameterMem.1, parameterMem.2]
  have pointNorm : ‖point‖ ≤ 6 := by
    rw [pointEq]
    calc
      ‖tube.base + parameter • tube.direction + error‖ ≤
          ‖tube.base‖ + ‖parameter • tube.direction‖ + ‖error‖ := by
        exact (norm_add_le _ _).trans <| by
          gcongr
          exact norm_add_le _ _
      _ = ‖tube.base‖ + |parameter| + ‖error‖ := by
        rw [norm_smul, Real.norm_eq_abs, tube.direction_unit, mul_one]
      _ ≤ 4 + 1 + 1 / 100 := by
        exact
          add_le_add
            (add_le_add baseBound parameterAbs)
            (errorNorm.trans deltaLe)
      _ ≤ 6 := by norm_num
  have coordinateBound :
      ∀ coordinate : Fin 3, |point coordinate| ≤ 6 := by
    intro coordinate
    have coordinateNorm :
        ‖point coordinate‖ ≤ ‖point‖ :=
      PiLp.norm_apply_le point coordinate
    simpa [Real.norm_eq_abs] using coordinateNorm.trans pointNorm
  simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
  norm_num
  exact
    ⟨coordinateBound 0, coordinateBound 1, coordinateBound 2⟩

/-- Bounded base and the paper line class give fixed support for every source
carrier. -/
theorem pureWZ2Prop62_family_carrier_subset_axisBox_twelve
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (deltaNonnegative : 0 ≤ delta)
    (deltaLe : delta ≤ 1 / 100)
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 4) :
    ∀ index,
      (family.tube index).carrier ⊆
        Kakeya.Streamlined.axisBox 12 12 12 := by
  intro index
  exact
    pureWZ2Prop62_tube_carrier_subset_axisBox_twelve
      deltaNonnegative deltaLe (family.tube index)
      (line index) (boundedBase index)

/-- The same fixed support descends through any indexed tube subfamily. -/
theorem pureWZ2Prop62_subfamily_carrier_subset_axisBox_twelve
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (deltaNonnegative : 0 ≤ delta)
    (deltaLe : delta ≤ 1 / 100)
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 4)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    ∀ index,
      (selected.family.tube index).carrier ⊆
        Kakeya.Streamlined.axisBox 12 12 12 := by
  intro index
  rw [selected.tube_eq index]
  exact
    pureWZ2Prop62_family_carrier_subset_axisBox_twelve
      deltaNonnegative deltaLe line boundedBase
      (selected.embedding index)

end Kakeya.Assouad

end
