import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Threshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerAnchoredLaminarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientBaseSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientAllScaleColorPreCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62RepresentativeParentScaledPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFiberCWABridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Certificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4ConstantAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperGeometryBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperGeometryConstruction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4BoundedBasePipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CleanupReceiptAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4LowerRoute
import MyLeanRepo.Kakeya.Assouad.PropStickyOrdinaryToCroppedShading
import MyLeanRepo.Kakeya.Assouad.ProjectionNormalization
import Mathlib.Tactic

/-!
# Proposition 6.2 metric-parent V4 pipeline

This module is independent of the paper-facing statement files.  It fixes the
order of the concrete construction through the caller-anchored schedule,
quotient, base selection, metric cover, source-colour pre-core, unique cleanup
receipt, metric core, ledger, density estimate, final refinement, lower-fibre
CWA, upper schedule, and terminal V4 certificate.

The lower requested-scale route and upper John/CWA witnesses are constructed
internally from the same schedule, pre-core, and cleanup receipt.  Neither a
completed CWA conclusion nor a completed V4 certificate is accepted as input.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The common final constant in the V4 conclusion. -/
def pureWZ2Prop62MetricParentsV4Target
    (delta : ℝ) (A : ℕ) (eta : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta
    (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)

/-- Transport the unique pre-core adapter along metric-core provenance. -/
def pureWZ2Prop62MetricParentsV4TransportPreCore
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → Color}
    (metric_eq : metricCore.metric = metric)
    (preCore :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric coloring Color sourceColor) :
    PureWZ2Prop62ProxyQuotientPreCoreAdapterData
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metricCore.metric coloring Color sourceColor := by
  rw [metric_eq]
  exact preCore

@[simp] theorem pureWZ2Prop62MetricParentsV4TransportPreCore_preliminary
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {Color : Type*}
    [Fintype Color] [DecidableEq Color] [Nonempty Color]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → Color}
    (metric_eq : metricCore.metric = metric)
    (preCore :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric coloring Color sourceColor) :
    (pureWZ2Prop62MetricParentsV4TransportPreCore
      metric_eq preCore).preCore.preliminary =
        preCore.preCore.preliminary := by
  subst metric
  rfl

/-- Transport the all-scale source-color pre-core along metric-core provenance. -/
def pureWZ2Prop62MetricParentsV4TransportAllScalePreCore
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (metric_eq : metricCore.metric = metric)
    (preCore :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric coloring conflictScale conflictDegree) :
    PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metricCore.metric coloring conflictScale
        conflictDegree := by
  rw [metric_eq]
  exact preCore

@[simp] theorem
    pureWZ2Prop62MetricParentsV4TransportAllScalePreCore_preliminary
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (metric_eq : metricCore.metric = metric)
    (preCore :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric coloring conflictScale conflictDegree) :
    (pureWZ2Prop62MetricParentsV4TransportAllScalePreCore
      metric_eq preCore).adapter.preCore.preliminary =
        preCore.adapter.preCore.preliminary := by
  subst metric
  rfl

/--
Closed V4 metric-parent pipeline.

Every selection through the unique metric core is constructed here.  The
lower and upper routes are constructed from the same schedule and the same
cleanup receipt; no completed CWA conclusion is accepted as an input.
-/
theorem pureWZ2_prop62_metric_parents_v4_pipeline_of_bounded_base
    (A : ℕ) (epsilon eta c0 delta : ℝ)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos)
    (sourceNonempty : source.Nonempty)
    (sourceBoundedBase : HasBoundedBase source 4)
    (sourceLine : WZ1PaperIsLineClass source)
    (sourceCubical : WZ1PaperIsCubicalShading shading)
    (sourceCWA :
      WZ2PaperPureCWAAtNearbyScales source
        (pureWZ2Prop62CallerCstar delta A eta))
    (sourceDense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta ((A : ℝ) * eta)))
    (rho_lower : Real.rpow delta (1 - epsilon) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta epsilon)
    (cleanupOracle : PureWZ2Prop62CleanupOracle) :
    Nonempty
      (PureWZ2Prop62MetricParentsV4Certificate
        shading rho c0
          (pureWZ2Prop62MetricParentsV4Target delta A eta)
          (pureWZ2Prop62MetricParentsV4Target delta A eta)) := by
  let thresholdInput :=
    pureWZ2Prop62MetricParentsV4CanonicalInput
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
  have rho_pos : 0 < rho.1 := lt_of_lt_of_le delta_pos rho.2.1
  have rho_le_one : rho.1 ≤ 1 := rho.2.2
  let caller :=
    Classical.choice <|
      thresholdInput.caller_certificate delta_pos delta_le
        rho_pos rho_le_one rho_lower
  let anchored :=
    Classical.choice <| caller.callerAnchoredSchedule sourceCWA
  let schedule := anchored.laminar
  let packetCoordinate : Fin schedule.levelCount :=
    Fin.cast anchored.laminar_levelCount_eq.symm anchored.anchorCoordinate
  have packetScaleLt :
      schedule.actualScale packetCoordinate <
        rho.1 / caller.parameters.K :=
    anchored.anchor_actual_upper
  have fineBaseFour : HasBoundedBase source 4 :=
    sourceBoundedBase
  have fineBaseFive : ∀ sourceIndex, ‖(source.tube sourceIndex).base‖ ≤ 5 := by
    intro sourceIndex
    exact (fineBaseFour sourceIndex).trans (by norm_num)
  let quotient :=
    Classical.choice <|
      exists_pureWZ2Prop62ProxyQuotientScheduleData
        schedule sourceNonempty sourceLine
  let weight : Fin source.card → ENNReal :=
    fun sourceIndex => volume (shading.carrier sourceIndex)
  have sourceMassFinite : shading.mass ≠ ⊤ :=
    wz1PaperTubeShading_mass_ne_top shading
  have density_pos :
      0 < Kakeya.realRpowENN delta ((A : ℝ) * eta) := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos delta_pos _
  have sourceEnncardPos : 0 < source.enncard := by
    change (0 : ENNReal) < (source.card : ENNReal)
    exact_mod_cast sourceNonempty
  have sourceBodyMassPos :
      0 < (wz1PaperBodyFamily source).mass := by
    exact lt_of_lt_of_le
      (ENNReal.mul_pos sourceEnncardPos.ne' <|
        (ENNReal.ofReal_pos.mpr <| Real.rpow_pos_of_pos delta_pos 2).ne')
      (pureWZ2_prop62_paper_body_mass_lower
        delta_pos
        (delta_le.trans thresholdInput.threshold_le_one_hundred |>.trans
          (by norm_num))
        sourceLine)
  have sourceMassPos : 0 < shading.mass := by
    exact lt_of_lt_of_le
      (ENNReal.mul_pos density_pos.ne' sourceBodyMassPos.ne')
      sourceDense
  have totalWeightPos : 0 < ∑ index : Fin source.card, weight index := by
    change 0 < ∑ index : Fin source.card, volume (shading.carrier index)
    exact sourceMassPos
  have selectionNonempty :=
    pureWZ2_prop62_proxy_quotient_selection_nonempty
      (rho := rho.1)
      schedule sourceNonempty quotient caller.parameters.width
      packetCoordinate caller.parameters.strideBase weight totalWeightPos
  let metric :=
    Classical.choice <|
      pureWZ2_prop62_proxy_ancestry_metric_output
        (rho := rho.1)
        schedule sourceNonempty sourceLine fineBaseFive quotient
        rho.1 caller.parameters.width packetCoordinate
        caller.parameters.strideBase weight rho_pos
        caller.parameters.width_pos selectionNonempty
        caller.parameters.strict_separation
        (caller.packet_metric_bound packetScaleLt)
  let baseSelection :=
    pureWZ2_prop62_proxy_quotient_base_selection_of_shading
      schedule sourceNonempty quotient caller.parameters.width
      packetCoordinate caller.parameters.strideBase shading weight metric
      (fun _ => rfl) sourceMassPos sourceMassFinite
  let coloring :=
    Classical.choice <|
      pureWZ2_prop62_upperEnvelope_center_coloring
        (rho := rho.1)
        schedule sourceNonempty sourceLine quotient packetCoordinate
  have packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho.1 := by
    have KOne : 1 ≤ caller.parameters.K := by
      rw [caller.parameters.K_eq, pureWZ2Prop62CallerK,
        ← caller.parameters.theta_eq]
      rw [le_div_iff₀ caller.parameters.theta_pos]
      nlinarith [caller.parameters.theta_le_one]
    exact packetScaleLt.le.trans <|
      div_le_self rho_pos.le KOne
  let sourceColor :=
    Classical.choice <|
      pureWZ2_prop62_proxy_quotient_allScaleColor_preCore
        schedule sourceNonempty quotient caller.parameters.width
        packetCoordinate caller.parameters.strideBase weight metric coloring
        (pureWZ2Prop62RepresentativeParentScaledConflictScale schedule)
        (fun _ =>
          pureWZ2Prop62RepresentativeParentScaledConflictDegree)
        (by
          intro coordinate fixed
          simpa [pureWZ2Prop62RepresentativeParentScaledConflict] using
            pureWZ2_prop62_representative_parent_scaled_degree
              schedule sourceNonempty sourceLine fineBaseFive quotient
                coordinate fixed)
        baseSelection.selectionWeightPos baseSelection.weight_finite
        delta_pos sourceLine fineBaseFive rho_pos caller.parameters.width_pos
        packetScaleLeRho caller.parameters.six_width_le
  have preliminarySubsetSelection :
      sourceColor.adapter.preCore.preliminary ⊆
        (quotient.selectProxyResidueUpperAncestryPerCell
          rho.1 caller.parameters.width packetCoordinate
          caller.parameters.strideBase weight).selected := by
    intro leaf leafMem
    have leafWhole :
        leaf ∈ sourceColor.adapter.preCore.wholeLeaves :=
      sourceColor.adapter.preCore.preliminary_subset_whole_fibers leafMem
    rw [sourceColor.adapter.preCore.wholeLeaves_eq] at leafWhole
    rcases Finset.mem_biUnion.mp leafWhole with
      ⟨parent, _parentMem, leafFiber⟩
    have leafHull :=
      (metric.mem_ambientCompleteMetricFiber_iff parent leaf).mp
        leafFiber |>.1
    rw [metric.packet_hull_eq_selection, metric.selection_eq] at leafHull
    exact leafHull
  let receipt :=
    Classical.choice <|
      cleanupOracle
        (Fin source.card)
        (Finset (Fin source.card))
        (schedule.levelCount + 1)
        (pureWZ2Prop62ProxyQuotientAuxiliaryLevel
          schedule sourceNonempty quotient rho.1 caller.parameters.width
            packetCoordinate).tree
        sourceColor.adapter.preCore.preliminary
        sourceColor.adapter.preCore.preliminary_nonempty
  rcases
      pureWZ2_prop62_proxy_quotient_metric_core_with_provenance
        schedule sourceNonempty quotient rho.1 caller.parameters.width
        packetCoordinate caller.parameters.strideBase weight metric
        sourceColor.adapter.preCore.preliminary
        sourceColor.adapter.preCore.preliminary_nonempty
        preliminarySubsetSelection receipt
    with ⟨metricCore, metricEq, cleanupEq⟩
  have preliminaryEq :
      metricCore.cleanup.preliminary =
        sourceColor.adapter.preCore.preliminary := by
    rw [cleanupEq]
    rfl
  let ledger :=
    pureWZ2_prop62_proxy_quotient_mass_ledger
      schedule sourceNonempty quotient caller.parameters.width
      packetCoordinate caller.parameters.strideBase weight
      metric Finset.univ
      sourceColor.adapter.global.selectedParents
      metric.ambientCompleteMetricFiber
      (fun parent =>
        (metric.ambientCompleteMetricFiber parent).card)
      metric.metricParentWeight
      metric.ambientMetricParentOf
      (pureWZ2Prop62ProxyQuotientAllScaleSourceColor
        sourceColor.parentColoring sourceColor.sourceConflict)
      metric.selectedFine.card
      sourceColor.adapter.preCore receipt metricCore metricEq
      preliminarySubsetSelection cleanupEq
      baseSelection.baseSelectionLoss
      baseSelection.base_selection_retention
      sourceColor.adapter.global.upperColorLoss
      sourceColor.adapter.global.weighted_retention
  let bounds :=
    pureWZ2Prop62MetricParentsV4MassBounds A eta c0
  have depthLe :
      schedule.levelCount ≤
        pureWZ2Prop62MetricParentsV4DepthBound A eta := by
    simpa only [schedule, pureWZ2Prop62MetricParentsV4DepthBound,
      pureWZ2Prop62CallerAnchoredDepthBound,
      pureWZ2Prop62CallerStep_eq] using
      pureWZ2Prop62CallerAnchoredScheduleData_geometric_levelCount_le
        sourceCWA caller.delta_lt_one caller.step_pos
        caller.requested_separation anchored
  have baseLossBound :
      ledger.baseSelectionLoss ≤ bounds.baseStructural := by
    change baseSelection.baseSelectionLoss ≤ _
    exact
      baseSelection.baseSelectionLoss_le_fixedBound
        depthLe
        (by rw [caller.parameters.strideBase_eq])
  have upperLossBound :
      ledger.upperColorLoss ≤ bounds.strongUpperVector := by
    change sourceColor.adapter.global.upperColorLoss ≤ _
    exact
      sourceColor.adapter.global.upperColorLoss_le_depthBound depthLe
  have delta_le_one : delta ≤ 1 :=
    (delta_le.trans
      (pureWZ2Prop62MetricParentsV4Threshold_le_one_hundred
        A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos)
      ).trans (by norm_num)
  have selectedFineCardLe :
      metric.selectedFine.card ≤ source.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        metric.mesh.complete.selectedFine.embedding
        metric.mesh.complete.selectedFine.embedding.injective
  have selectedFineCardLeDouble :
      metric.selectedFine.card ≤ 2 * source.card := by
    omega
  have sourceCardBound :
      source.card ≤
        (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
    have localBound :=
      wz2PaperOrdinary_local_six_grid_card_bound
        delta_pos (show (0 : ℝ) ≤ 5 by norm_num)
        schedule.fine_distinct Finset.univ (0 : Point3) <| by
          intro index _
          simpa [dist_zero_right] using
            PureWZ2Prop62AncestryMetricPreliminaryOutput.fine_midpoint_norm_le_five
              fineBaseFour index
    have firstArgument :
        5 / (delta / 64) = 320 / delta := by
      field_simp [delta_pos.ne']
      norm_num
    have secondArgument :
        1 / (delta / 64) ≤ 320 / delta := by
      have identity :
          1 / (delta / 64) = 64 / delta := by
        field_simp [delta_pos.ne']
      rw [identity]
      exact div_le_div_of_nonneg_right (by norm_num) delta_pos.le
    have firstCeil :
        Nat.ceil (5 / (delta / 64)) =
          Nat.ceil (320 / delta) := by
      rw [firstArgument]
    have secondCeil :
        Nat.ceil (1 / (delta / 64)) ≤
          Nat.ceil (320 / delta) :=
      Nat.ceil_mono secondArgument
    simpa only [Finset.card_univ, Fintype.card_fin] using
      localBound.trans <| by
        rw [firstCeil]
        calc
          (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
                (2 * Nat.ceil (1 / (delta / 64)) + 1) ^ 3 ≤
              (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
                (2 * Nat.ceil (320 / delta) + 1) ^ 3 := by
            gcongr
          _ = (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by ring
  have ambientLogReal :=
    pureWZ2Prop62_ordinary_card_log_bound
      delta_pos delta_le_one sourceNonempty sourceCardBound
  have ambientLogENN :
      (Nat.log 2 (2 * source.card) + 1 : ENNReal) ≤
        ENNReal.ofReal
          (pureWZ2Prop62OrdinaryCardLogConstant *
            (1 + Real.log delta⁻¹)) := by
    have converted := ENNReal.ofReal_mono ambientLogReal
    have castEq :
        ENNReal.ofReal
            (Nat.log 2 (2 * source.card) + 1 : ℝ) =
          (Nat.log 2 (2 * source.card) + 1 : ENNReal) := by
      rw [ENNReal.ofReal_add (by positivity)]
      norm_num
      positivity
    rwa [castEq] at converted
  have fiberLogLe :
      Nat.log 2 metric.selectedFine.card + 1 ≤
        Nat.log 2 (2 * source.card) + 1 :=
    Nat.add_le_add_right
      (Nat.log_mono_right selectedFineCardLeDouble) 1
  have fiberLossBound :
      ledger.fiberBinLoss ≤
        ENNReal.ofReal
          (bounds.fiberBinCoefficient *
            (1 + Real.log delta⁻¹)) := by
    rw [ledger.fiberBinLoss_eq,
      sourceColor.adapter.preCore.retention.fiberBinLoss_eq]
    calc
      (Nat.log 2 metric.selectedFine.card + 1 : ENNReal) ≤
          (Nat.log 2 (2 * source.card) + 1 : ENNReal) := by
        exact_mod_cast fiberLogLe
      _ ≤
          ENNReal.ofReal
            (pureWZ2Prop62OrdinaryCardLogConstant *
              (1 + Real.log delta⁻¹)) :=
        ambientLogENN
      _ =
          ENNReal.ofReal
            (bounds.fiberBinCoefficient *
              (1 + Real.log delta⁻¹)) := by
        rfl
  have sourceColorLossBound :
      ledger.sourceColorLoss ≤ bounds.sourceColor := by
    rw [ledger.sourceColorLoss_eq]
    exact
      sourceColor.sourceColorLoss_le_metricParentsV4MassBounds depthLe
  have colorSelectedCardLe :
      sourceColor.adapter.preCore.leafBin.colorSelected.card ≤
        source.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card
        (Finset.subset_univ
          sourceColor.adapter.preCore.leafBin.colorSelected)
  have leafLogLe :
      sourceColor.adapter.preCore.leafBin.dyadicBinCount ≤
        Nat.log 2 (2 * source.card) + 1 := by
    rw [sourceColor.adapter.preCore.leafBin.dyadicBinCount_eq]
    exact
      Nat.add_le_add_right
        (Nat.log_mono_right <| Nat.mul_le_mul_left 2 colorSelectedCardLe) 1
  have leafLossBound :
      ledger.leafBinLoss ≤
        ENNReal.ofReal
          (bounds.leafBinCoefficient *
            (1 + Real.log delta⁻¹)) := by
    rw [ledger.leafBinLoss_eq,
      sourceColor.adapter.preCore.retention.leafBinLoss_eq]
    calc
      (2 * sourceColor.adapter.preCore.leafBin.dyadicBinCount : ENNReal) ≤
          (2 * (Nat.log 2 (2 * source.card) + 1) : ENNReal) := by
        exact_mod_cast Nat.mul_le_mul_left 2 leafLogLe
      _ ≤
          2 *
            ENNReal.ofReal
              (pureWZ2Prop62OrdinaryCardLogConstant *
                (1 + Real.log delta⁻¹)) := by
        gcongr
      _ =
          ENNReal.ofReal
            ((2 * pureWZ2Prop62OrdinaryCardLogConstant) *
              (1 + Real.log delta⁻¹)) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ =
          ENNReal.ofReal
            (bounds.leafBinCoefficient *
              (1 + Real.log delta⁻¹)) := by
        rfl
  have cleanupLossBound :
      ledger.cleanupLoss ≤ bounds.weightedCleanup := by
    rw [ledger.cleanupLoss_eq]
    exact pow_le_pow_right₀ (by norm_num) <| by omega
  have massAbsorption :
      wz1PaperRefinementFraction delta 10 * ledger.totalLoss ≤ 1 := by
    have deltaMass :
        delta ≤
          pureWZ2Prop62ProxyQuotientMassThreshold
            A eta c0 bounds :=
      pureWZ2Prop62MetricParentsV4_deltaMassSmall
        A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
        delta_le
    exact
      ledger.final_refinement_absorption_of_le_threshold
        bounds delta_pos deltaMass baseLossBound upperLossBound
        fiberLossBound sourceColorLossBound leafLossBound cleanupLossBound
  let finalRefinement :=
    pureWZ2_prop62_proxy_quotient_final_refinement_of_ledger
      schedule sourceNonempty quotient caller.parameters.width
      packetCoordinate caller.parameters.strideBase weight
      metric Finset.univ
      sourceColor.adapter.global.selectedParents
      metric.ambientCompleteMetricFiber
      (fun parent =>
        (metric.ambientCompleteMetricFiber parent).card)
      metric.metricParentWeight
      metric.ambientMetricParentOf
      (pureWZ2Prop62ProxyQuotientAllScaleSourceColor
        sourceColor.parentColoring sourceColor.sourceConflict)
      metric.selectedFine.card
      sourceColor.adapter.preCore preliminarySubsetSelection receipt
      metricCore ledger shading sourceCubical (fun _ => rfl)
      massAbsorption
  have upperColorLossNeTop :
      ledger.upperColorLoss ≠ ⊤ := by
    change sourceColor.adapter.global.upperColorLoss ≠ ⊤
    rw [sourceColor.adapter.global.upperColorLoss_eq_power]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  let densityData :=
    ledger.densityLossOfPaperGeometry
      shading
      (Kakeya.realRpowENN delta ((A : ℝ) * eta))
      delta_pos
      ((delta_le.trans
        (pureWZ2Prop62MetricParentsV4Threshold_le_one_hundred
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos)
        ).trans (by norm_num))
      sourceLine
      (by
        exact
          (ENNReal.ofReal_pos.mpr <|
            Real.rpow_pos_of_pos delta_pos _).ne')
      (by simp [Kakeya.realRpowENN])
      sourceDense (fun _ => rfl)
      baseSelection.baseSelectionLoss_ne_top upperColorLossNeTop
  let densityEnvelope :=
    pureWZ2Prop62MetricParentsV4DensityFixedLoss A eta c0 *
      (pureWZ2Prop62CallerCstar delta A eta) ^ 2
  have densityLossLe :
      metricCore.quotientDensityLoss ≤ densityEnvelope := by
    have densityProvenance :
        metricCore.quotientDensityLoss =
          ledger.cleanupDensityRatio := by
      simpa only [
        PureWZ2Prop62ProxyQuotientMetricCoreOutput.quotientDensityLoss,
        PureWZ2Prop62ProxyQuotientMassLedger.cleanupDensityRatio,
        pureWZ2Prop62CleanupDensityRatio,
        Kakeya.Streamlined.TubeFamily.enncard,
        preliminaryEq
      ]
    rw [densityProvenance]
    apply
      ledger.cleanupDensityRatio_le_fixedLoss_mul_Cstar_sq
        bounds
        thresholdInput.densityPowerCertificate
        densityData
        delta_pos
        (delta_le.trans thresholdInput.threshold_le_densityPower)
        depthLe baseLossBound upperLossBound fiberLossBound
        sourceColorLossBound leafLossBound
  let powerBudget :=
    pureWZ2Prop62MetricParentsV4_power_certificate
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
      delta_pos delta_le
  have uniformityAbsorption :
      2 * densityEnvelope ≤
        pureWZ2Prop62MetricParentsV4Target delta A eta := by
    have coefficientTwo :
        (2 : ENNReal) ≤
          pureWZ2Prop62MetricParentsV4UniformityCoefficient := by
      unfold pureWZ2Prop62MetricParentsV4UniformityCoefficient
      have copyOne :
          (1 : ENNReal) ≤
            (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal) := by
        have largePos :
            0 < pureWZ2Prop62ProxyCenterCopyLargeScaleBound := by
          unfold pureWZ2Prop62ProxyCenterCopyLargeScaleBound
          positivity
        exact_mod_cast
          (show 1 ≤ pureWZ2Prop62ProxyCenterCopyPackingBound by
            unfold pureWZ2Prop62ProxyCenterCopyPackingBound
            omega)
      simpa only [mul_one] using
        mul_le_mul_left' copyOne (2 : ENNReal)
    have densityEnvelope_le :
        densityEnvelope ≤
          pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
      calc
        densityEnvelope = 1 * densityEnvelope := by simp
        _ ≤
            pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
          exact
            mul_le_mul_right'
              powerBudget.Cstar_one densityEnvelope
    have scaled :
        2 * densityEnvelope ≤
          pureWZ2Prop62MetricParentsV4UniformityCoefficient *
            pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
      calc
        2 * densityEnvelope ≤
            pureWZ2Prop62MetricParentsV4UniformityCoefficient *
              densityEnvelope := by
          gcongr
        _ ≤
            pureWZ2Prop62MetricParentsV4UniformityCoefficient *
              pureWZ2Prop62CallerCstar delta A eta * densityEnvelope := by
          rw [mul_assoc]
          exact
            mul_le_mul_left'
              densityEnvelope_le
              pureWZ2Prop62MetricParentsV4UniformityCoefficient
    exact scaled.trans <| by
      change
        pureWZ2Prop62MetricParentsV4UniformityCoefficient *
              Kakeya.realRpowENN delta (-((A : ℝ) * eta)) *
              densityEnvelope ≤
          Kakeya.realRpowENN delta
            (-(pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta)
      exact
        thresholdInput.upper_uniformity_to_target
          delta_pos delta_le (Λ := densityEnvelope) (by rfl)
  let constants :=
    pureWZ2_prop62_metric_parents_v4_constant_assembly
      A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos
      delta_pos delta_le
  let sourceConstant :=
    pureWZ2Prop62MetricParentsV4SourceConstant A eta delta
  have anchorScalePos :
      0 < schedule.actualScale packetCoordinate :=
    (schedule.scaleData packetCoordinate).rho_pos
  have CstarToRealPos :
      0 < (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    have CstarPos :
        0 < pureWZ2Prop62CallerCstar delta A eta :=
      lt_of_lt_of_le (by norm_num) caller.Cstar_four
    exact ENNReal.toReal_pos CstarPos.ne' caller.Cstar_finite
  have anchorDenominatorPos :
      0 <
        caller.parameters.K *
          (pureWZ2Prop62CallerCstar delta A eta).toReal :=
    mul_pos caller.parameters.K_pos CstarToRealPos
  have anchorRatioNonneg :
      0 ≤ rho.1 / schedule.actualScale packetCoordinate :=
    div_nonneg rho_pos.le anchorScalePos.le
  have anchorRatioLe :
      rho.1 / schedule.actualScale packetCoordinate ≤
        pureWZ2Prop62CallerK c0 *
          (pureWZ2Prop62CallerCstar delta A eta).toReal := by
    have anchorLower := anchored.anchor_actual_lower
    change
      rho.1 /
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) ≤
        schedule.actualScale packetCoordinate at anchorLower
    have rhoLe :
        rho.1 ≤
          schedule.actualScale packetCoordinate *
            (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) :=
      (div_le_iff₀ anchorDenominatorPos).mp anchorLower
    rw [← caller.parameters.K_eq]
    apply (div_le_iff₀ anchorScalePos).mpr
    calc
      rho.1 ≤
          schedule.actualScale packetCoordinate *
            (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) :=
        rhoLe
      _ =
          (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) *
            schedule.actualScale packetCoordinate := by
        apply mul_comm
  have insertedConstantLe :
      pureWZ2Prop62InsertedCWALoss
          rho.1 (schedule.actualScale packetCoordinate)
            (pureWZ2Prop62CallerCstar delta A eta) *
        metricCore.quotientDensityLoss ≤ sourceConstant := by
    calc
      pureWZ2Prop62InsertedCWALoss
            rho.1 (schedule.actualScale packetCoordinate)
              (pureWZ2Prop62CallerCstar delta A eta) *
          metricCore.quotientDensityLoss ≤
        pureWZ2Prop62InsertedCWALoss
            rho.1 (schedule.actualScale packetCoordinate)
              (pureWZ2Prop62CallerCstar delta A eta) *
          densityEnvelope := by
            gcongr
      _ ≤ constants.sourceConstant :=
        constants.insertedConstant_le anchorRatioNonneg anchorRatioLe
      _ = sourceConstant := by
        exact constants.sourceConstant_eq
  have fiberTarget :
      (81000000 : ENNReal) * sourceConstant =
        pureWZ2Prop62MetricParentsV4Target delta A eta := by
    calc
      (81000000 : ENNReal) * sourceConstant =
          (81000000 : ENNReal) * constants.sourceConstant := by
        rw [constants.sourceConstant_eq]
      _ = pureWZ2Prop62MetricParentsV4TargetConstant A eta delta :=
        constants.fiber_target
      _ = pureWZ2Prop62MetricParentsV4Target delta A eta := by
        simp [pureWZ2Prop62MetricParentsV4Target,
          pureWZ2Prop62MetricParentsV4TargetConstant,
          pureWZ2Prop62MetricParentsV4CWAPower]
  let corePreCore :=
    pureWZ2Prop62MetricParentsV4TransportPreCore
      metricEq sourceColor.adapter
  have corePreliminaryEq :
      metricCore.cleanup.preliminary =
        corePreCore.preCore.preliminary := by
    rw [pureWZ2Prop62MetricParentsV4TransportPreCore_preliminary]
    exact preliminaryEq
  have parentDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        metricCore.restriction.coarseSelected.family :=
    metricCore.finalMetricParents_ordinary_distinct
      sourceLine caller.parameters.width_pos
        caller.parameters.upper_strong_separation
  let Bcopy : ENNReal :=
    pureWZ2Prop62ProxyCenterCopyPackingBound
  let Cold : ENNReal :=
    pureWZ2Prop62CallerCstar delta A eta
  have centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho.1 packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy := by
    intro coordinate center
    change
      ((quotient.centerActualParents
        coordinate.1 center).card : ENNReal) ≤
        (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal)
    exact_mod_cast
      pureWZ2_prop62_proxy_center_actualParents_card_le
        schedule sourceNonempty sourceLine fineBaseFive quotient
        coordinate.1 center
  have ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho.1 packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          source (schedule.scaleData coordinate.1).coarse Cold := by
    intro coordinate
    exact (schedule.scaleData coordinate.1).full_fiber_uniform
  have targetEq :
      pureWZ2Prop62MetricParentsV4Target delta A eta =
        pureWZ2Prop62MetricParentsV4TargetConstant A eta delta := by
    simp [pureWZ2Prop62MetricParentsV4Target,
      pureWZ2Prop62MetricParentsV4TargetConstant,
      pureWZ2Prop62MetricParentsV4CWAPower]
  have coverAbsorption :
      2 * Bcopy * Cold * densityEnvelope ≤
        pureWZ2Prop62MetricParentsV4Target delta A eta := by
    rw [targetEq]
    change
      2 * (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal) *
            pureWZ2Prop62CallerCstar delta A eta *
            pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta ≤
        pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
    exact
      (le_max_left
        (2 * (pureWZ2Prop62ProxyCenterCopyPackingBound : ENNReal) *
          pureWZ2Prop62CallerCstar delta A eta *
          pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta)
        (PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant
          (pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta)
          (pureWZ2Prop62CallerCstar delta A eta))).trans
        constants.upper_final_scale_constant_le
  have bodyAbsorption :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant
          densityEnvelope Cold ≤
        pureWZ2Prop62MetricParentsV4Target delta A eta := by
    rw [targetEq]
    change
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant
          (pureWZ2Prop62MetricParentsV4DensityEnvelope A eta c0 delta)
          (pureWZ2Prop62CallerCstar delta A eta) ≤
        pureWZ2Prop62MetricParentsV4TargetConstant A eta delta
    calc
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant
            densityEnvelope Cold =
          (densityEnvelope * Cold) *
            (pureWZ2Prop62UpperEnvelopeGeometricLoss * 2) := by
        unfold
          PureWZ2Prop62ProxyQuotientMetricCoreOutput.finalUpperBodyConstant
        ring
      _ ≤
          (densityEnvelope * Cold) *
            pureWZ2Prop62MetricParentsV4UpperCoefficient := by
        gcongr
        exact le_max_left _ _
      _ ≤
          pureWZ2Prop62MetricParentsV4TargetConstant A eta delta := by
        simpa only [densityEnvelope, Cold,
          pureWZ2Prop62MetricParentsV4DensityEnvelope] using
          constants.upper_parent_absorption
  have scheduleWindowEq :
      pureWZ2Prop62CallerCstar delta A eta *
          ENNReal.ofReal
            ((Real.rpow delta
              (-pureWZ2Prop62CallerStep A eta)) ^ 2) =
        (pureWZ2Prop62CallerCstar delta A eta) ^ 5 := by
    apply
      pureWZ2Prop62_geometric_anchored_finalWindow_eq_fifth
        delta_pos
        (pureWZ2Prop62CallerStep_eq A eta)
    simp [pureWZ2Prop62CallerCstar, pureWZ2Prop62CallerLoss,
      Kakeya.realRpowENN]
  have representativeFactorLeK :
      (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor : ℝ) ≤
        caller.parameters.K := by
    rw [pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
      pureWZ2Prop62RepresentativeParentScaledFactor_eq,
      caller.parameters.K_eq, pureWZ2Prop62CallerK,
      ← caller.parameters.theta_eq]
    apply (le_div_iff₀ caller.parameters.theta_pos).2
    calc
      (1200000 : ℝ) * caller.parameters.theta ≤
          1200000 * 1 := by
        exact mul_le_mul_of_nonneg_left
          caller.parameters.theta_le_one (by norm_num)
      _ ≤ 2400000 := by norm_num
  have descendantActualSmall :
      ∀ coordinate : Fin schedule.levelCount,
        packetCoordinate.val < coordinate.val →
          schedule.actualScale coordinate ≤ 1 / 10000 := by
    intro coordinate coordinateAfter
    have actualLePacket :
        schedule.actualScale coordinate ≤
          schedule.actualScale packetCoordinate :=
      schedule.actualScale_antitone
        packetCoordinate coordinate coordinateAfter.le
    have KLarge : (10000 : ℝ) ≤ caller.parameters.K := by
      rw [caller.parameters.K_eq, pureWZ2Prop62CallerK,
        ← caller.parameters.theta_eq]
      apply (le_div_iff₀ caller.parameters.theta_pos).2
      nlinarith [caller.parameters.theta_le_one]
    have rhoDivKLe :
        rho.1 / caller.parameters.K ≤ 1 / 10000 := by
      apply (div_le_iff₀ caller.parameters.K_pos).2
      nlinarith [rho_le_one]
    exact actualLePacket.trans packetScaleLt.le |>.trans rhoDivKLe
  have routeScaleSeparation :
      100 * delta ≤ rho.1 := by
    have CstarRealOne :
        1 ≤ (pureWZ2Prop62CallerCstar delta A eta).toReal := by
      have converted :=
        ENNReal.toReal_mono caller.Cstar_finite caller.Cstar_four
      exact (show (1 : ℝ) ≤ 4 by norm_num).trans converted
    have hundredLeK : (100 : ℝ) ≤ caller.parameters.K := by
      rw [caller.parameters.K_eq, pureWZ2Prop62CallerK,
        ← caller.parameters.theta_eq]
      apply (le_div_iff₀ caller.parameters.theta_pos).2
      nlinarith [caller.parameters.theta_le_one]
    have denominatorPos :
        0 <
          caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal :=
      mul_pos caller.parameters.K_pos (lt_of_lt_of_le zero_lt_one CstarRealOne)
    have hundredLeDenominator :
        (100 : ℝ) ≤
          caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal := by
      calc
        (100 : ℝ) ≤ caller.parameters.K := hundredLeK
        _ = caller.parameters.K * 1 := by ring
        _ ≤
            caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal := by
          gcongr
    have q0Lower := caller.q0_lower
    unfold pureWZ2Prop62CallerQ0 at q0Lower
    rw [← caller.parameters.K_eq] at q0Lower
    have scaled :
        delta *
            (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) ≤
          rho.1 :=
      (le_div_iff₀ denominatorPos).mp q0Lower
    calc
      100 * delta ≤
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) * delta :=
        mul_le_mul_of_nonneg_right hundredLeDenominator delta_pos.le
      _ = delta *
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) := by ring
      _ ≤ rho.1 := scaled
  have routeFloorGate :
      _ * ENNReal.ofReal delta <
        ENNReal.ofReal (schedule.actualScale packetCoordinate) :=
    thresholdInput.routeFloorGate_of_scaleWindow_eq caller delta_le
      scheduleWindowEq rho_lower anchorScalePos anchored.anchor_actual_lower
  have routeScaledWindowAbsorption :
      (100 : ENNReal) *
          ENNReal.ofReal pureWZ2Prop62RepresentativeParentScaledFactor *
          _ ≤
        (81000000 : ENNReal) * sourceConstant :=
    thresholdInput.routeScaledWindowAbsorption
      delta_pos delta_le scheduleWindowEq fiberTarget
  have routeDensityAbsorption :
      pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
          (pureWZ2Prop62CallerCstar delta A eta *
            metricCore.quotientDensityLoss) ≤
        sourceConstant := by
    calc
      pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
            (pureWZ2Prop62CallerCstar delta A eta *
              metricCore.quotientDensityLoss) ≤
          pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
            (pureWZ2Prop62CallerCstar delta A eta * densityEnvelope) := by
        gcongr
      _ ≤ sourceConstant := by
        change
          pureWZ2Prop62MetricParentsV4RepresentativeMiddleJohnLoss *
                (pureWZ2Prop62CallerCstar delta A eta * densityEnvelope) ≤
            sourceConstant
        apply
          thresholdInput.representativeMiddleJohnLoss_mul_le_sourceConstant
            delta_pos delta_le
        · rfl
        · exact fiberTarget
  have routeTopGate :
      (4 : ENNReal) *
          ((100 : ENNReal) * _ * ENNReal.ofReal rho.1) ≤
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal (schedule.actualScale packetCoordinate) :=
    thresholdInput.routeTopGate caller delta_le scheduleWindowEq
      anchored.anchor_actual_lower fiberTarget
  let coreSourceColor :=
    pureWZ2Prop62MetricParentsV4TransportAllScalePreCore
      metricEq sourceColor
  have coreSourcePreliminaryEq :
      metricCore.cleanup.preliminary =
        coreSourceColor.adapter.preCore.preliminary := by
    rw [
      pureWZ2Prop62MetricParentsV4TransportAllScalePreCore_preliminary]
    exact preliminaryEq
  let routeInput :
      PureWZ2Prop62ProxyQuotientFiberRouteInput
        schedule sourceNonempty quotient caller.parameters.width
          packetCoordinate caller.parameters.strideBase weight metricCore
          sourceConstant :=
    pureWZ2_prop62_metricParentsV4_lowerRoute
      schedule sourceNonempty quotient caller.parameters.width
      packetCoordinate caller.parameters.strideBase weight metricCore
      coreSourceColor coreSourcePreliminaryEq
      sourceLine fineBaseFour rho_le_one
      routeScaleSeparation constants.sourceConstant_finite
      caller.parameters.K representativeFactorLeK descendantActualSmall
      routeDensityAbsorption packetScaleLt routeFloorGate
      routeScaledWindowAbsorption routeTopGate
  let fiberCWA :=
    pureWZ2_prop62_proxy_quotient_fiber_cwa_bridge_of_adapter
      schedule sourceNonempty quotient caller.parameters.width
      packetCoordinate caller.parameters.strideBase weight metric
      coloring
      (pureWZ2Prop62ProxyQuotientAllScaleSourceColor
        sourceColor.parentColoring sourceColor.sourceConflict)
      sourceColor.adapter metricCore metricEq preliminaryEq
      sourceConstant routeInput sourceLine
      caller.parameters.width_pos caller.parameters.six_width_le
      insertedConstantLe
      (sourceColor.finalMetricFibers_sourceStronglySeparated
        metricCore metricEq preliminaryEq)
  have roundingAbsorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) *
          (pureWZ2Prop62CallerCstar delta A eta *
            ENNReal.ofReal
              ((Real.rpow delta
                (-pureWZ2Prop62CallerStep A eta)) ^ 2)) ≤
        pureWZ2Prop62MetricParentsV4Target delta A eta := by
    rw [scheduleWindowEq]
    simpa [pureWZ2Prop62MetricParentsV4Target,
      pureWZ2Prop62MetricParentsV4TargetConstant] using
        constants.envelope_absorption
  have packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho.1 := by
    have KOne : 1 ≤ caller.parameters.K := by
      rw [caller.parameters.K_eq, pureWZ2Prop62CallerK,
        ← caller.parameters.theta_eq]
      rw [le_div_iff₀ caller.parameters.theta_pos]
      nlinarith [caller.parameters.theta_le_one]
    exact packetScaleLt.trans_le <| div_le_self rho_pos.le KOne
  have fourDeltaLeRho : 4 * delta ≤ rho.1 := by
    have fourLeK : 4 ≤ caller.parameters.K := by
      rw [caller.parameters.K_eq, pureWZ2Prop62CallerK,
        ← caller.parameters.theta_eq]
      apply (le_div_iff₀ caller.parameters.theta_pos).2
      nlinarith [caller.parameters.theta_le_one]
    have CstarRealFour :
        4 ≤
          (pureWZ2Prop62CallerCstar delta A eta).toReal := by
      have converted :=
        ENNReal.toReal_mono caller.Cstar_finite caller.Cstar_four
      norm_num at converted ⊢
      exact converted
    have denominatorPos :
        0 <
          caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal :=
      mul_pos caller.parameters.K_pos <|
        lt_of_lt_of_le (by norm_num) CstarRealFour
    have fourLeDenominator :
        4 ≤
          caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal := by
      calc
        (4 : ℝ) ≤ caller.parameters.K := fourLeK
        _ = caller.parameters.K * 1 := by ring
        _ ≤
            caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal := by
          exact mul_le_mul_of_nonneg_left
            ((show (1 : ℝ) ≤ 4 by norm_num).trans CstarRealFour)
            caller.parameters.K_pos.le
    have q0Lower := caller.q0_lower
    unfold pureWZ2Prop62CallerQ0 at q0Lower
    rw [← caller.parameters.K_eq] at q0Lower
    have scaled :
        delta *
            (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) ≤
          rho.1 :=
      (le_div_iff₀ denominatorPos).mp q0Lower
    calc
      4 * delta ≤
          (caller.parameters.K *
            (pureWZ2Prop62CallerCstar delta A eta).toReal) * delta :=
        mul_le_mul_of_nonneg_right fourLeDenominator delta_pos.le
      _ =
          delta *
            (caller.parameters.K *
              (pureWZ2Prop62CallerCstar delta A eta).toReal) := by
        ring
      _ ≤ rho.1 := scaled
  let upperGeometry :
      PureWZ2Prop62ProxyQuotientUpperGeometryData
        (sourceConstant := pureWZ2Prop62CallerCstar delta A eta)
        metricCore corePreCore corePreliminaryEq
          sourceLine fineBaseFive rho_pos :=
    metricCore.upperGeometryDataOfBoundedBaseFour
      corePreCore corePreliminaryEq sourceLine fineBaseFive rho_pos
      (delta_le.trans <|
        pureWZ2Prop62MetricParentsV4Threshold_le_one_hundred
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos
            loss_small c0_pos)
      fineBaseFour
      fourDeltaLeRho caller.parameters.width_pos
      packetScaleLeRho caller.parameters.six_width_le
  let coarseCWA :
      WZ2PaperPureCWAAtNearbyScales
        metricCore.restriction.coarseSelected.family
        (pureWZ2Prop62MetricParentsV4Target delta A eta) :=
    metricCore.finalMetricParents_publicPureCWA_of_upperGeometryComponents
      corePreCore corePreliminaryEq sourceLine fineBaseFive rho_pos
      caller.parameters.width_pos packetScaleLtRho rho_le_one
      caller.parameters.six_width_le
      caller.parameters.upper_strong_separation
      Bcopy Cold densityEnvelope
      (pureWZ2Prop62CallerCstar delta A eta)
      (pureWZ2Prop62MetricParentsV4Target delta A eta)
      centerCopyBound ambientUniform densityLossLe
      (by
        simpa [pureWZ2Prop62MetricParentsV4Target,
          pureWZ2Prop62MetricParentsV4TargetConstant] using
            constants.target_finite)
      coverAbsorption bodyAbsorption roundingAbsorption
      upperGeometry
  exact
    pureWZ2_prop62_metric_parents_v4_certificate
      shading rho c0 schedule sourceNonempty quotient packetCoordinate
      weight caller.parameters metricCore corePreCore corePreliminaryEq
      finalRefinement
      (pureWZ2Prop62MetricParentsV4Target delta A eta)
      sourceConstant
      (pureWZ2Prop62MetricParentsV4Target delta A eta)
      densityEnvelope coarseCWA fiberCWA fiberTarget.symm
      sourceLine fineBaseFive packetScaleLt
      densityLossLe uniformityAbsorption

/--
Compatibility wrapper for the original unit-ball boundary.

The geometric pipeline itself only needs the weaker bounded-base certificate;
unit-ball containment is used here solely to derive that certificate.
-/
theorem pureWZ2_prop62_metric_parents_v4_pipeline
    (A : ℕ) (epsilon eta c0 delta : ℝ)
    (source : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (A_ge_one : 1 ≤ A)
    (epsilon_pos : 0 < epsilon)
    (eta_pos : 0 < eta)
    (loss_small :
      (pureWZ2Prop62MetricParentsV4CWAPower A : ℝ) * eta ≤
        epsilon / 100)
    (c0_pos : 0 < c0)
    (delta_pos : 0 < delta)
    (delta_le :
      delta ≤
        pureWZ2Prop62MetricParentsV4Threshold
          A epsilon eta c0 A_ge_one epsilon_pos eta_pos loss_small c0_pos)
    (sourceNonempty : source.Nonempty)
    (sourceUnitBall : source.IsInUnitBall)
    (sourceLine : WZ1PaperIsLineClass source)
    (sourceCubical : WZ1PaperIsCubicalShading shading)
    (sourceCWA :
      WZ2PaperPureCWAAtNearbyScales source
        (pureWZ2Prop62CallerCstar delta A eta))
    (sourceDense :
      shading.IsLambdaDense
        (Kakeya.realRpowENN delta ((A : ℝ) * eta)))
    (rho_lower : Real.rpow delta (1 - epsilon) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta epsilon)
    (cleanupOracle : PureWZ2Prop62CleanupOracle) :
    Nonempty
      (PureWZ2Prop62MetricParentsV4Certificate
        shading rho c0
          (pureWZ2Prop62MetricParentsV4Target delta A eta)
          (pureWZ2Prop62MetricParentsV4Target delta A eta)) := by
  have sourceBoundedBaseOne : HasBoundedBase source 1 :=
    hasBoundedBase_of_isInUnitBall delta_pos.le sourceUnitBall
  have sourceBoundedBaseFour : HasBoundedBase source 4 := by
    intro sourceIndex
    exact (sourceBoundedBaseOne sourceIndex).trans (by norm_num)
  exact
    pureWZ2_prop62_metric_parents_v4_pipeline_of_bounded_base
      A epsilon eta c0 delta source shading rho A_ge_one epsilon_pos
      eta_pos loss_small c0_pos delta_pos delta_le sourceNonempty
      sourceBoundedBaseFour sourceLine sourceCubical sourceCWA sourceDense
      rho_lower rho_upper cleanupOracle

end Kakeya.Assouad

end
