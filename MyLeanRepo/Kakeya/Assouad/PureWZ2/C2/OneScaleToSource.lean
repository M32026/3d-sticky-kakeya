import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements

/-!
# Advance a Pure one-scale output to the next hierarchy source

The family is unchanged.  The retained shading, extremality, local grains,
global grains, CWA, and volume lower bound all belong to one dependent
configuration.  No uniform tube structure is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperConvexWolffBound.mono_constant
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C C' : ENNReal}
    (data : WZ2PaperConvexWolffBound family C)
    (hconstant : C ≤ C') :
    WZ2PaperConvexWolffBound family C' := by
  intro convexSet hconvex
  calc
    (wz1PaperBodyFamily family).containedCount convexSet ≤
        C * MeasureTheory.volume convexSet * family.enncard :=
      data convexSet hconvex
    _ = C * (MeasureTheory.volume convexSet * family.enncard) := by ring
    _ ≤ C' * (MeasureTheory.volume convexSet * family.enncard) :=
      mul_le_mul_right' hconstant _
    _ = C' * MeasureTheory.volume convexSet * family.enncard := by ring

/-- Regard a same-family one-scale result as the source for the next level. -/
noncomputable def PureWZ2LocallyLinearOneScaleData.toGrainConfiguration
    {sigma inputLoss delta outputLoss rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source outputLoss rho)
    (hloss : inputLoss ≤ outputLoss) :
    PureWZ2QuantitativeGrainConfiguration sigma outputLoss delta := by
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hloss
  exact
    { family := source.family
      shading := data.shading
      line_class := source.line_class
      cubical := data.whole_cells
      extremal := data.extremal
      top_level_cwa := source.top_level_cwa.mono_constant hconstant
      volume_lower := data.volume_lower
      globalGrains := data.globalGrains
      localGrains := data.localGrains
      planeMap_vertical_bound := data.planeMap_vertical_bound
    }

@[simp] theorem PureWZ2LocallyLinearOneScaleData.toGrainConfiguration_family
    {sigma inputLoss delta outputLoss rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source outputLoss rho)
    (hloss : inputLoss ≤ outputLoss) :
    (data.toGrainConfiguration hloss).family = source.family := rfl

@[simp] theorem PureWZ2LocallyLinearOneScaleData.toGrainConfiguration_shading
    {sigma inputLoss delta outputLoss rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source outputLoss rho)
    (hloss : inputLoss ≤ outputLoss) :
    (data.toGrainConfiguration hloss).shading = data.shading := rfl

@[simp] theorem PureWZ2LocallyLinearOneScaleData.toGrainConfiguration_slope
    {sigma inputLoss delta outputLoss rho : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2LocallyLinearOneScaleData source outputLoss rho)
    (hloss : inputLoss ≤ outputLoss) :
    (data.toGrainConfiguration hloss).globalGrains.slope =
      source.globalGrains.slope := by
  exact data.slope_eq

end Kakeya.Assouad
