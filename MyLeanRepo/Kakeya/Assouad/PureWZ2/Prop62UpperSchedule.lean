import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreInsertedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FinitePureNearbyAssembly

/-!
# Proposition 6.2 metric parents: finite upper schedule

Each old level above the inserted metric-parent level supplies a modified
factor-nineteen parent family, a monochromatic genuine partitioning cover,
uniform strict fibers, and canonical outer-John fiber CWA.  This module
packages those verified one-scale witnesses and performs only the final finite
rounding step.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62UpperScaleWitness
    {rho upper : ℝ}
    (children : Kakeya.Streamlined.TubeFamily rho)
    (outputConstant : ENNReal) where
  degree : ℕ
  parents : Kakeya.Streamlined.TubeFamily upper
  input :
    PureWZ2Prop62UpperScaleInput children parents degree
  coloring : input.ColoringData
  selectedColor : Fin (degree + 1)
  monochromatic :
    ∀ child,
      input.childColor coloring child = selectedColor
  coverData :
    input.MonochromaticCoverData coloring
      (pureWZ2Prop62IdentitySubfamily children)
  coverConstant : ENNReal
  bodyConstant : ENNReal
  fullFiberUniform :
    WZ2PaperPureFullFibersAreCUniform
      children coverData.selectedParents.family coverConstant
  normalization :
    ∀ parent : Fin coverData.selectedParents.family.card,
      WZ2PaperAssouadUnitRescalingData
        (coverData.selectedParents.family.tube parent)
  fiberCWA :
    ∀ parent : Fin coverData.selectedParents.family.card,
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := children)
          (coarse := coverData.selectedParents.family)
          parent (normalization parent))
        bodyConstant
  constant_le :
    max coverConstant bodyConstant ≤ outputConstant

namespace PureWZ2Prop62UpperScaleWitness

variable
    {rho upper : ℝ}
    {children : Kakeya.Streamlined.TubeFamily rho}
    {outputConstant : ENNReal}
    (witness :
      PureWZ2Prop62UpperScaleWitness
        (upper := upper) children outputConstant)

noncomputable def rawScaleData :
    WZ2PaperPureScaleCoverData children upper
      (max witness.coverConstant witness.bodyConstant) :=
  witness.coverData.toPureScaleData
    witness.coverConstant witness.bodyConstant
    witness.fullFiberUniform witness.normalization witness.fiberCWA

noncomputable def scaleData :
    WZ2PaperPureScaleCoverData children upper outputConstant :=
  witness.rawScaleData.mono witness.constant_le

theorem scaleData_coarse :
    (witness.scaleData (upper := upper)).coarse =
      witness.coverData.selectedParents.family := by
  rfl

end PureWZ2Prop62UpperScaleWitness

structure PureWZ2Prop62UpperSchedule
    {rho : ℝ}
    (parents : Kakeya.Streamlined.TubeFamily rho)
    (outputConstant : ENNReal) where
  output_finite : WZ2PaperFiniteErrorConstant outputConstant
  parent_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct parents
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  baseScale : Fin coordinateCount → ℝ
  baseScale_mem :
    ∀ coordinate,
      rho ≤ baseScale coordinate ∧
        baseScale coordinate ≤ 1
  witness :
    ∀ coordinate,
      PureWZ2Prop62UpperScaleWitness
        (upper := 19 * baseScale coordinate)
        parents outputConstant
  rounding :
    ∀ requested : WZ2PaperRequestedScale rho,
      ∃ coordinate : Fin coordinateCount,
        requested.1 ≤ 19 * baseScale coordinate ∧
          ENNReal.ofReal (19 * baseScale coordinate) <
            outputConstant * ENNReal.ofReal requested.1

theorem pureWZ2_prop62_upperSchedule_nearbyCWA
    {rho : ℝ}
    {parents : Kakeya.Streamlined.TubeFamily rho}
    {outputConstant : ENNReal}
    (schedule :
      PureWZ2Prop62UpperSchedule parents outputConstant) :
    WZ2PaperPureCWAAtNearbyScales parents outputConstant := by
  apply pureWZ2_nearby_from_finite_witnesses
    ((PureWZ2Prop62UpperSchedule.witness schedule
      ⟨0, PureWZ2Prop62UpperSchedule.coordinateCount_pos schedule⟩)
        |>.input.rho_pos)
    (PureWZ2Prop62UpperSchedule.output_finite schedule).1
    (PureWZ2Prop62UpperSchedule.output_finite schedule).2
    (PureWZ2Prop62UpperSchedule.parent_distinct schedule)
    (PureWZ2Prop62UpperSchedule.coordinateCount schedule)
    (PureWZ2Prop62UpperSchedule.coordinateCount_pos schedule)
    (fun coordinate =>
      ⟨19 * PureWZ2Prop62UpperSchedule.baseScale schedule coordinate,
        (PureWZ2Prop62UpperSchedule.witness schedule coordinate).scaleData⟩)
  exact PureWZ2Prop62UpperSchedule.rounding schedule

end Kakeya.Assouad

end
