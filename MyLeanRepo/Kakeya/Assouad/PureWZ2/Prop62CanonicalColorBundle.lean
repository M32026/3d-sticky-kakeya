import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ScheduledParentConflictColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryMetricMassRetention

/-!
# Proposition 6.2: canonical global color bundle

The single global dependent-color pigeonhole has exactly one slot for every
old schedule coordinate and one final slot for the fine source-conflict
color.  All slots use the same absolute finite color type.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)

abbrev CanonicalColorCoordinate :=
  Fin (schedule.levelCount + 1)

abbrev CanonicalColor
    (_coordinate : schedule.CanonicalColorCoordinate) :=
  Fin (pureWZ2OrdinaryLineConflictDegree + 1)

noncomputable def canonicalSourceConflict
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBoundedBase : HasBoundedBase fine 4) :
    PureWZ2Prop62SourceConflictColoringData fine :=
  Classical.choice <|
    pureWZ2_prop62_source_conflict_coloring
      (schedule.scaleData ⟨0, schedule.levelCount_pos⟩).delta_pos
      fineLine
      (fun source => (fineBoundedBase source).trans <| by norm_num)
      schedule.fine_distinct

def canonicalColor
    (sourceConflict :
      PureWZ2Prop62SourceConflictColoringData fine)
    (coordinate : schedule.CanonicalColorCoordinate)
    (source : Fin fine.card) :
    schedule.CanonicalColor coordinate :=
  if coordinateLt : coordinate.1 < schedule.levelCount then
    scheduled.leafColor
      ⟨coordinate.1, coordinateLt⟩ source
  else
    sourceConflict.color source

noncomputable def canonicalCoordinates
    (sourceConflict :
      PureWZ2Prop62SourceConflictColoringData fine) :
    PureWZ2Prop62ScheduledParentCoordinateData
      schedule scheduled (Function.Embedding.refl _)
      (schedule.levelCount + 1) schedule.CanonicalColor
      (schedule.canonicalColor scheduled sourceConflict) where
  slot := Fin.castSucc
  decode := fun _ color => color
  decode_color := by
    intro coordinate source
    simp [canonicalColor]

noncomputable def canonicalConflictCoordinate
    (sourceConflict :
      PureWZ2Prop62SourceConflictColoringData fine) :
    PureWZ2Prop62SourceConflictCoordinateData
      schedule.CanonicalColor
      (schedule.canonicalColor scheduled sourceConflict) where
  coloring := sourceConflict
  coordinate := Fin.last schedule.levelCount
  decode := fun color => color
  decode_color := by
    intro source
    simp [canonicalColor]

theorem canonicalColor_card :
    Fintype.card
        (∀ coordinate : schedule.CanonicalColorCoordinate,
          schedule.CanonicalColor coordinate) =
      (pureWZ2OrdinaryLineConflictDegree + 1) ^
        (schedule.levelCount + 1) := by
  simp [Fintype.card_pi]

end PureWZ2Prop62PureSchedule

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {sourceConflict :
      PureWZ2Prop62SourceConflictColoringData fine}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        weight preliminary M)

/-- The fixed structural part of the metric-parent mass loss. -/
def canonicalStructuralMassLoss : ENNReal :=
  let _output := output
  max
    ((Fintype.card
        (Fin 4 → ZMod (preliminary.residueStrideBase + 1)) : ENNReal) *
      (Fintype.card
        (schedule.UpperColorVector rho packetCoordinate) : ENNReal))
    (max
      (Fintype.card
        (∀ coordinate : schedule.CanonicalColorCoordinate,
          schedule.CanonicalColor coordinate) : ENNReal)
      (2 ^ (schedule.levelCount + 2) : ENNReal))

/--
The two numerical estimates still supplied by the outer small-scale
argument.  Every one of the five factors in the exact mass ledger follows
from these two bounds.
-/
structure CanonicalMetricMassRetentionBudget : Prop where
  logBase_pos :
    0 < ENNReal.ofReal (Real.log (1 / delta))
  structural :
    output.canonicalStructuralMassLoss ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2
  ambientDyadic :
    (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) ≤
      (ENNReal.ofReal (Real.log (1 / delta))) ^ 2

theorem metricSelectedFine_card_le_ambient :
    output.metric.selectedFine.card ≤ fine.card := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective
      output.metric.mesh.complete.selectedFine.embedding
      output.metric.mesh.complete.selectedFine.embedding.injective

theorem preliminary_leafBin_le_ambientDyadic :
    (2 * preliminary.preliminary.dyadicBinCount : ENNReal) ≤
      (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) := by
  have colorClassCardLe :
      preliminary.preliminary.colorClass.card ≤ fine.card :=
    by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card
          (Finset.subset_univ preliminary.preliminary.colorClass)
  have doubledCardLe :
      2 * preliminary.preliminary.colorClass.card ≤
        2 * fine.card := by
    omega
  have logLe :
      preliminary.preliminary.dyadicBinCount ≤
        Nat.log 2 (2 * fine.card) + 1 := by
    rw [preliminary.preliminary.dyadicBinCount_eq]
    exact
      Nat.add_le_add_right
        (Nat.log_mono_right doubledCardLe) 1
  exact_mod_cast Nat.mul_le_mul_left 2 logLe

theorem metricFiberBin_le_ambientDyadic :
    (output.metricFiberCardinalityBin.fiberBinCount : ENNReal) ≤
      (2 * (Nat.log 2 (2 * fine.card) + 1) : ENNReal) := by
  have selectedCardLe : output.metric.selectedFine.card ≤ fine.card :=
    output.metricSelectedFine_card_le_ambient
  have selectedCardLeDouble :
      output.metric.selectedFine.card ≤ 2 * fine.card := by
    omega
  have logLe :
      output.metricFiberCardinalityBin.fiberBinCount ≤
        Nat.log 2 (2 * fine.card) + 1 := by
    rw [output.metricFiberCardinalityBin.fiberBinCount_eq]
    exact
      Nat.add_le_add_right
        (Nat.log_mono_right selectedCardLeDouble) 1
  have doubled :
      output.metricFiberCardinalityBin.fiberBinCount ≤
        2 * (Nat.log 2 (2 * fine.card) + 1) := by
    omega
  exact_mod_cast doubled

theorem canonicalMetricMassRetentionBudget_to_logBudget
    (budget : output.CanonicalMetricMassRetentionBudget) :
    output.FinalMetricMassRetentionLogBudget where
  logBase_pos := budget.logBase_pos
  perCell :=
    (le_max_left _ _).trans budget.structural
  globalColor :=
    (le_max_left _
      (2 ^ (schedule.levelCount + 2) : ENNReal)
      |>.trans <| le_max_right _ _
      |>.trans budget.structural)
  leafBin :=
    preliminary_leafBin_le_ambientDyadic
      (preliminary := preliminary) |>.trans
      budget.ambientDyadic
  fiberBin :=
    output.metricFiberBin_le_ambientDyadic.trans
      budget.ambientDyadic
  tree :=
    (le_max_right
      (Fintype.card
        (∀ coordinate : schedule.CanonicalColorCoordinate,
          schedule.CanonicalColor coordinate) : ENNReal)
      (2 ^ (schedule.levelCount + 2) : ENNReal)
      |>.trans <| le_max_right _ _
      |>.trans budget.structural)

/--
The fixed-exponent metric-parent output for the canonical global color
bundle.  The caller supplies no arbitrary coordinate or source-conflict
certificate.
-/
theorem metricParentsOutput_canonical_logTen
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4)
    (budget : output.FinalMetricMassRetentionLogBudget) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight 10) := by
  exact
    output.metricParentsOutput_logTen
      (schedule.canonicalCoordinates scheduled sourceConflict)
      (schedule.canonicalConflictCoordinate scheduled sourceConflict)
      rhoPos rhoLeOne actualScaleLeOne widthPos
      packetScaleLtRho sixWidthLe
      allAncestryCoordinatesUpper scaleSeparation fineAxisBox
      fineBoundedBase budget

/--
Canonical output from the two outer scalar estimates.  This is equivalent to
the five-factor budget but exposes only the fixed structural and ambient
dyadic gates that remain to be discharged uniformly in `delta`.
-/
theorem metricParentsOutput_canonical
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4)
    (budget : output.CanonicalMetricMassRetentionBudget) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight 10) :=
  output.metricParentsOutput_canonical_logTen
    rhoPos rhoLeOne actualScaleLeOne widthPos
    packetScaleLtRho sixWidthLe
    allAncestryCoordinatesUpper scaleSeparation fineAxisBox
    fineBoundedBase
    (output.canonicalMetricMassRetentionBudget_to_logBudget budget)

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
