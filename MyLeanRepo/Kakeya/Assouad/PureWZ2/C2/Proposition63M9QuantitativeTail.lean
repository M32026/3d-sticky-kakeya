import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustTailAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.QuantitativeConfiguration

/-!
# Node-5-private quantitative projection of the Proposition 6.3 M9 tail

The public Proposition 6.3 result deliberately forgets the critical lower
volume bound and the two chart-normalization bounds.  The production M9
construction retains the exact transported maps, so Node 5 may attach those
certificates here without changing the public grain statement.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

namespace Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData

/-- Attach the separately proved critical volume floor to the exact grain
returned by the construction-aware mild-rescaling tail. -/
noncomputable def toQuantitativeGrainConfiguration
    {sourceDelta scale sigma sourceLoss outputLoss : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFine}
    {Lplane Lslope : NNReal}
    {preGrains : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
      Lplane Lslope 1}
    {targetFine : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    {targetShading : WZ1PaperTubeShading targetFine}
    (data : Proposition63MildRescalingFinalGrainData
      (outputLoss := outputLoss) sourceShading preGrains targetFine
      targetShading)
    (volume_lower : Kakeya.realRpowENN (scale * sourceDelta)
        (sigma + outputLoss) ≤ volume targetShading.union)
    (source_vertical :
      ∀ point : {point : Point3 // point ∈ sourceShading.union},
        |preGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2)
    (source_slope : ∀ height : ℝ, height ∈ Set.Icc (-1 : ℝ) 1 →
      |preGrains.slope height| ≤ 3) :
    PureWZ2QuantitativeGrainConfiguration sigma outputLoss
      (scale * sourceDelta) :=
  data.toGrainConfiguration.toQuantitativeGrainConfiguration volume_lower
    (data.slope_bound source_slope)
    (data.planeMap_vertical_bound source_vertical)

end Proposition63MildRescalingFiniteParentScheduleData.Proposition63MildRescalingFinalGrainData

end Kakeya.Assouad.PureWZ2

end
