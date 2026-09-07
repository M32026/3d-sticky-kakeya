import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalMassBudget

/-!
# Proposition 6.2: canonical ancestry metric preliminary output

This module instantiates the abstract dependent-color interfaces with the
canonical `L + 1` color bundle:

* one scheduled-parent conflict color at every old level;
* one fine source-conflict color;
* one global mesh residue, followed by one upper-ancestry color per cell.

The only weight assumptions are positivity and finiteness of the original
total weight.  Positivity and finiteness after the combined geometric
selection are derived from its exact retention inequality.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62CanonicalMetricPreliminaryOutput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal)
    (M : ℝ)
    (residueStrideBase : ℕ) where
  scheduled :
    PureWZ2Prop62ScheduledParentColoringData schedule
  sourceConflict :
    PureWZ2Prop62SourceConflictColoringData fine
  preliminary :
    PureWZ2Prop62AncestryPreliminarySelectionData
      schedule scheduled rho width packetCoordinate
      schedule.CanonicalColor
      (schedule.canonicalColor scheduled sourceConflict)
      weight
  output :
    PureWZ2Prop62AncestryMetricPreliminaryOutput
      schedule scheduled width packetCoordinate
      schedule.CanonicalColor
      (schedule.canonicalColor scheduled sourceConflict)
      weight preliminary M
  preliminary_residueStrideBase :
    preliminary.residueStrideBase = residueStrideBase

theorem pureWZ2_prop62_canonical_metric_preliminary
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin fine.card → ENNReal)
    (M : ℝ)
    (residueStrideBase : ℕ)
    (totalFinite :
      (∑ source : Fin fine.card, weight source) ≠ ⊤)
    (totalPos :
      0 < ∑ source : Fin fine.card, weight source)
    (rhoPos : 0 < rho)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4)
    (fineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ M)
    (widthPos : 0 < width)
    (strongSeparation :
      360 * rho <
        (((residueStrideBase + 1 : ℕ) : ℝ) - 1) * width)
    (packetBound :
      (16 * M + 44) *
            schedule.actualScale packetCoordinate +
          6 * width ≤ rho / 2) :
    Nonempty
      (PureWZ2Prop62CanonicalMetricPreliminaryOutput
        (rho := rho) schedule width packetCoordinate weight M
          residueStrideBase) := by
  let scheduled :=
    Classical.choice <|
      pureWZ2_prop62_scheduled_parent_coloring
        schedule fineNonempty actualScaleLeOne fineBoundedBase
  let sourceConflict :=
    schedule.canonicalSourceConflict
      fineLine fineBoundedBase
  let perCell :=
    schedule.selectResidueUpperAncestryPerCell
      scheduled rho width packetCoordinate residueStrideBase weight
  let activeWeight : Fin fine.card → ENNReal :=
    fun source =>
      if source ∈ perCell.selected then weight source else 0
  have activeTotalLe :
      (∑ source : Fin fine.card, activeWeight source) ≤
        ∑ source : Fin fine.card, weight source := by
    apply Finset.sum_le_sum
    intro source _
    dsimp only [activeWeight]
    split_ifs
    · exact le_rfl
    · exact bot_le
  have activeTotalFinite :
      (∑ source : Fin fine.card, activeWeight source) ≠ ⊤ :=
    ne_top_of_le_ne_top totalFinite activeTotalLe
  have activeTotalEq :
      (∑ source : Fin fine.card, activeWeight source) =
        ∑ source ∈ perCell.selected, weight source := by
    unfold activeWeight
    calc
      (∑ source : Fin fine.card,
          if source ∈ perCell.selected then weight source else 0) =
          ∑ source ∈
              (Finset.univ.filter fun source =>
                source ∈ perCell.selected),
            weight source := by
        exact
          (Finset.sum_filter
            (s := (Finset.univ : Finset (Fin fine.card)))
            (p := fun source => source ∈ perCell.selected)
            (f := weight)).symm
      _ = ∑ source ∈ perCell.selected, weight source := by
        congr 1
        ext source
        simp
  have activeTotalPos : 0 < ∑ source : Fin fine.card, activeWeight source := by
    rw [activeTotalEq]
    by_contra selectedNotPos
    have selectedZero :
        (∑ source ∈ perCell.selected, weight source) = 0 := by
      simpa [not_lt] using selectedNotPos
    have totalZero :
        (∑ source : Fin fine.card, weight source) ≤ 0 := by
      have retention := perCell.weight_retention
      simpa [selectedZero] using retention
    exact (not_le_of_gt totalPos) totalZero
  let preliminaryCore :=
    Classical.choice <|
      pureWZ2_prop62_preliminary_selection
        (schedule.levelCount + 1)
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        activeWeight activeTotalFinite activeTotalPos
  have selectedSubset :
      preliminaryCore.selected ⊆ perCell.selected := by
    intro source sourceMem
    have weightLower :=
      (preliminaryCore.selected_weight_band source sourceMem).1
    have activePositive :
        0 < activeWeight source :=
      preliminaryCore.weightLevel_pos.trans_le weightLower
    by_contra sourceNotMem
    have activeZero : activeWeight source = 0 := by
      simp [activeWeight, sourceNotMem]
    rw [activeZero] at activePositive
    exact (lt_self_iff_false 0).mp activePositive
  let preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        weight :=
    {
      residueStrideBase := residueStrideBase
      perCell := perCell
      perCell_eq := rfl
      activeWeight := activeWeight
      activeWeight_eq := rfl
      preliminary := preliminaryCore
      selected_subset_perCell := selectedSubset
    }
  let output :=
    Classical.choice <|
      pureWZ2_prop62_ancestry_metric_preliminary_output
        schedule scheduled width packetCoordinate
        schedule.CanonicalColor
        (schedule.canonicalColor scheduled sourceConflict)
        weight preliminary M rhoPos fineNonempty fineLine fineLocal
        widthPos strongSeparation packetBound
  exact
    ⟨{
      scheduled := scheduled
      sourceConflict := sourceConflict
      preliminary := preliminary
      output := output
      preliminary_residueStrideBase := rfl
    }⟩

namespace PureWZ2Prop62CanonicalMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {weight : Fin fine.card → ENNReal}
    {M : ℝ}
    {residueStrideBase : ℕ}
    (canonical :
      PureWZ2Prop62CanonicalMetricPreliminaryOutput
        (rho := rho) schedule width packetCoordinate weight M
          residueStrideBase)

abbrev finalMetricRestriction :=
  PureWZ2Prop62AncestryMetricPreliminaryOutput.finalMetricRestriction
    (rho := rho) canonical.output

theorem metricParentsOutput_of_smallDelta
    (depthBound strideBaseBound : ℕ)
    (deltaPos : 0 < delta)
    (deltaLe :
      delta ≤
        PureWZ2Prop62AncestryMetricPreliminaryOutput.pureWZ2Prop62CanonicalMassThreshold
          depthBound strideBaseBound)
    (depthLe : schedule.levelCount ≤ depthBound)
    (strideLe :
      canonical.preliminary.residueStrideBase ≤ strideBaseBound)
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
        (canonical.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight 10) :=
  canonical.output.metricParentsOutput_canonical_of_smallDelta
    depthBound strideBaseBound deltaPos deltaLe depthLe strideLe
    rhoPos rhoLeOne actualScaleLeOne widthPos
    packetScaleLtRho sixWidthLe
    allAncestryCoordinatesUpper scaleSeparation fineAxisBox
    fineBoundedBase

end PureWZ2Prop62CanonicalMetricPreliminaryOutput

end Kakeya.Assouad

end
