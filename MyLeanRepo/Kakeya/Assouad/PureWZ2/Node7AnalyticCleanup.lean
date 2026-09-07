import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7bQuantitative
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperCWAToDeltaMax
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DeltaMaxToNormalizedNonconcentration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TwistedProjection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperConvexWolffCardinalityCore
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperConvexWolffCardinality
import MyLeanRepo.Kakeya.Assouad.Targets.ProbabilisticKatzTaoSubfamily
import MyLeanRepo.Kakeya.Assouad.Subunit.ExpDomination
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExplicitDensityTestNet
import MyLeanRepo.Kakeya.Assouad.Subunit.ExpDomination

/-!
# Scale-generic Node 7 analytic cleanup

This module isolates the analytic-cleanup part of Node 7 from the critical
configuration and normalization records.  All geometric and analytic inputs
live directly at the runtime scale `r`.
-/

noncomputable section

open MeasureTheory Set Metric
open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Assouad.Subunit

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Bounded basepoints pass to the cleanup subfamily without any coordinate
normalization or shear. -/
private theorem node7_cleanup_hasBoundedBase
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (hbase : HasBoundedBase ambient 4) :
    HasBoundedBase data.family 4 := by
  intro index
  rw [data.tube_eq_source index]
  exact hbase (data.sourceIndex index)

/-- The vertical-chart condition passes to the cleanup subfamily. -/
private theorem node7_cleanup_vertical
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (hvertical : IsInVerticalChart ambient) :
    IsInVerticalChart data.family := by
  intro index
  rw [data.tube_eq_source index]
  exact hvertical (data.sourceIndex index)

/-- The slope window passes through the literal cleanup subshading. -/
private theorem node7_cleanup_slope_window
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (hwindow : IsInSlopeWindow ambientShading) :
    IsInSlopeWindow data.shading := by
  intro point hpoint
  rcases hpoint with ⟨index, hindex⟩
  exact hwindow ⟨data.sourceIndex index,
    data.shading_subset_source index hindex⟩

/-- Cleanup only deletes shaded points.  Centering is definitionally harmless
for a slope already normalized to vanish at zero; no geometric shear is used. -/
private theorem node7_cleanup_projection_upper
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : Kakeya.Streamlined.TubeShading ambient}
    {target D : ENNReal} {net : TubeDensityTestNet delta}
    (data : PureWZ2AnalyticCleanupData ambient ambientShading target D net)
    (slope : SlopeFunction) (hzero : slope 0 = 0) :
    volume (twistedUnion data.shading slope.centered) ≤
      volume (twistedProjection slope '' ambientShading.union) := by
  have hslope : slope.centered = slope := by
    cases slope with
    | mk toFun contDiff =>
      simp only [SlopeFunction.centered]
      congr
      funext z
      rw [show toFun 0 = 0 from hzero, sub_zero]
  rw [hslope]
  exact measure_mono (Set.image_mono (by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨data.sourceIndex index,
      data.shading_subset_source index hindex⟩))

/-- The numerical receipts needed by the scale-generic analytic cleanup.
They are separated from the geometric hypotheses because a fixed upper bound
`r ≤ 1 / 10000` alone cannot absorb these constants uniformly as the positive
loss tends to zero. -/
structure PureWZ2Node7AnalyticCleanupScaleBudget
    (sigma analyticLoss r : ℝ)
    (family : Kakeya.Streamlined.TubeFamily r)
    (shading : Kakeya.Streamlined.TubeShading family) where
  net : TubeDensityTestNet r
  net_loss : net.lossFactor ≤ (10^7 : ENNReal)
  cleanup_input :
    let target := Kakeya.realRpowENN r (-(analyticLoss / 20))
    let D := 9261000 * Kakeya.realRpowENN r (-(analyticLoss / 100)) *
      family.enncard * Kakeya.deltaTubeVolume r
    family.toBodyFamily.deltaMax ≤ target ∨
      target ≤ D ∧
        Kakeya.deltaTubeVolume r ≤ (target / D) * shading.mass ∧
        (net.testSets.card : ℝ) *
              Real.exp (-(11 - Real.exp 1) * target.toReal) +
            Real.exp (-(3 - Real.exp 1) *
              (target.toReal / D.toReal) * (family.card : ℝ)) < 1 / 8
  paper_card_absorb :
    55296 * Kakeya.deltaTubeVolume 1 ≤
      Kakeya.realRpowENN r (-(analyticLoss / 100))
  final_card_absorb :
    (2400 : ENNReal) ≤
      Kakeya.realRpowENN r
        (-(analyticLoss / 10 - analyticLoss / 20))
  density_absorb :
    4 * (2700000000000000001 : ENNReal) ≤
      Kakeya.realRpowENN r
        (-(analyticLoss - analyticLoss / 100 - analyticLoss / 20))
  tube_wolff_absorb :
    ((2 * (2700000000000000001 : ENNReal) * pureWZ2SamplingConstant) *
        (24 * Kakeya.deltaTubeVolume 1 * (10^8 : ENNReal))) ≤
      Kakeya.realRpowENN r
        (-(analyticLoss - 3 * (analyticLoss / 100) -
          2 * (analyticLoss / 20)))
  parameter_frostman_absorb :
    ((2 * (2700000000000000001 : ENNReal) * pureWZ2SamplingConstant) *
        (4800 * (10^8 : ENNReal))) ≤
      Kakeya.realRpowENN r
        (-(analyticLoss - 3 * (analyticLoss / 100) -
          2 * (analyticLoss / 20)))

/-- Run one analytic cleanup directly on an arbitrary runtime-scale ordinary
shading and package all of the data needed by the parameter-Frostman step. -/
theorem pure_wz2_node7_analytic_cleanup
    {sigma analyticLoss r : ℝ}
    (family : Kakeya.Streamlined.TubeFamily r)
    (shading : Kakeya.Streamlined.TubeShading family)
    (hloss : 0 < analyticLoss)
    (hr : 0 < r) (hr_small : r ≤ 1 / 10000)
    (hfamily : family.Nonempty)
    (hbase : HasBoundedBase family 4)
    (hvertical : IsInVerticalChart family)
    (hwindow : IsInSlopeWindow shading)
    (hline : WZ1PaperIsLineClass family)
    (hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN r (-(analyticLoss / 100))))
    (hdense : shading.IsLambdaDense
      (Kakeya.realRpowENN r (analyticLoss / 100)))
    (slope : SlopeFunction)
    (hslope_zero : slope 0 = 0)
    (hslope_nonsingular : slope.IsNonsingular)
    (hprojection : volume (twistedUnion shading slope) ≤
      Kakeya.realRpowENN r (sigma - analyticLoss))
    (budget : PureWZ2Node7AnalyticCleanupScaleBudget
      sigma analyticLoss r family shading) :
    Nonempty (PureWZ2ParameterFrostmanPreparationData
      sigma analyticLoss r) := by
  let coreLoss : ℝ := analyticLoss / 100
  let thinEta : ℝ := analyticLoss / 20
  let target : ENNReal := Kakeya.realRpowENN r (-thinEta)
  let D : ENNReal := 9261000 * Kakeya.realRpowENN r (-coreLoss) *
    family.enncard * Kakeya.deltaTubeVolume r
  have hcore_pos : 0 < coreLoss := by positivity
  have hthin_pos : 0 < thinEta := by positivity
  have hr_one : r ≤ 1 := hr_small.trans (by norm_num)
  have hr_cleanup : r ≤ 1 / 1000 := hr_small.trans (by norm_num)
  have hdeltaMaxD : family.toBodyFamily.deltaMax ≤ D := by
    exact paper_cwa_to_ordinary_deltaMax hr hr_one family hline hbase
      (Kakeya.realRpowENN r (-coreLoss)) hcwa
  have hDtop : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.coe_ne_top)
      (tube_volume_scaling.2.1 r hr hr_one).2
  have htargetZero : target ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _)).ne'
  have htargetTop : target ≠ ⊤ := ENNReal.ofReal_ne_top
  have hambientSupport : ∀ i, (family.tube i).carrier ⊆
      Metric.closedBall (0 : Point3) 10 := by
    intro i
    exact (tube_carrier_subset_closedBall_six hr.le hr_one
      (family.tube i) (hbase i)).trans
        (Metric.closedBall_subset_closedBall (by norm_num))
  have hambientSupportSix : ∀ i, (family.tube i).carrier ⊆
      Metric.closedBall (0 : Point3) 6 := by
    intro i
    exact tube_carrier_subset_closedBall_six hr.le hr_one
      (family.tube i) (hbase i)
  have hpaperCard : Kakeya.realRpowENN r (-2 + 2 * coreLoss) ≤
      family.enncard := by
    exact wz2PaperConvexWolff_cardinality_lower
      wz2_paper_tube_carrier_geometry
      wz2_paper_convex_wolff_cardinality_core
      hr (by linarith [hr_cleanup]) hfamily hline hcwa (by
        simpa only [coreLoss] using budget.paper_card_absorb)
  let cardinalityFloor : ENNReal :=
    ((2 : ENNReal) * 2700000000000000001 *
      pureWZ2SamplingConstant)⁻¹ *
      Kakeya.realRpowENN r (-2 + 3 * coreLoss + thinEta)
  have hcleanupExists : ∃ Dcleanup : ENNReal,
      Dcleanup ≠ ⊤ ∧ target ≤ Dcleanup ∧
      family.toBodyFamily.deltaMax ≤ Dcleanup ∧
      ∃ cleanup : PureWZ2AnalyticCleanupData
          family shading target Dcleanup budget.net,
        cardinalityFloor ≤ cleanup.family.enncard := by
    rcases (by simpa only [target, D, coreLoss, thinEta] using
      budget.cleanup_input) with hlow | hhigh
    · rcases pure_wz2_analytic_cleanup_low hr hr_one hr_cleanup family shading
          thinEta hthin_pos budget.net hlow with ⟨cleanup⟩
      have hretention : cleanup.loss⁻¹ *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN r coreLoss *
            family.enncard) ≤ cleanup.family.enncard := by
        have h := cleanup.cardinality_retention hr hr_one htargetTop hdense
        rw [cleanup.samplingRate_eq,
          ENNReal.div_self htargetZero htargetTop] at h
        simpa [mul_assoc] using h
      have hfloor := pure_wz2_cleanup_cardinality_floor_low
        (coreLoss := coreLoss) (thinEta := thinEta) hr hr_one budget.net
        cleanup.loss family.enncard cleanup.family.enncard
        (pure_wz2_cleanup_loss_ne_zero_top budget.net).1
        (pure_wz2_cleanup_loss_ne_zero_top budget.net).2
        (pure_wz2_cleanup_loss_le hr hr_one hthin_pos budget.net budget.net_loss)
        hpaperCard hretention
      exact ⟨target, htargetTop, le_rfl, hlow, cleanup, by
        simpa only [cardinalityFloor] using hfloor⟩
    · rcases hhigh with ⟨htargetD, hmass, hunion⟩
      rcases pure_wz2_analytic_cleanup hr hr_one hr_cleanup family hfamily
          hambientSupport shading thinEta hthin_pos D hdeltaMaxD hDtop htargetD
          budget.net hmass hunion with ⟨cleanup⟩
      have hsampleFloor := pure_wz2_high_sampling_card_power_lower
        hr hr_one family.enncard D ENNReal.coe_ne_top hDtop le_rfl htargetD
      have hretention : cleanup.loss⁻¹ *
          ((1 / 2 : ENNReal) * Kakeya.realRpowENN r coreLoss *
            (cleanup.samplingRate * family.enncard)) ≤
          cleanup.family.enncard := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          cleanup.cardinality_retention hr hr_one htargetTop hdense
      have hfloorStrong := pure_wz2_cleanup_cardinality_floor hr budget.net
        (coreLoss := coreLoss) (thinEta := thinEta) cleanup.loss
        (cleanup.samplingRate * family.enncard) cleanup.family.enncard
        (pure_wz2_cleanup_loss_ne_zero_top budget.net).1
        (pure_wz2_cleanup_loss_ne_zero_top budget.net).2
        (pure_wz2_cleanup_loss_le hr hr_one hthin_pos budget.net budget.net_loss)
        (by simpa [cleanup.samplingRate_eq] using hsampleFloor) hretention
      have hpower : Kakeya.realRpowENN r
          (-2 + 3 * coreLoss + thinEta) ≤
          Kakeya.realRpowENN r (-2 + 2 * coreLoss) :=
        realRpowENN_mono_constant hr hr_one (by
          dsimp only [coreLoss, thinEta]
          linarith)
      have hfloor := (mul_le_mul_right hpower
        ((2 : ENNReal) * 2700000000000000001 *
          pureWZ2SamplingConstant)⁻¹).trans hfloorStrong
      exact ⟨D, hDtop, htargetD, hdeltaMaxD, cleanup, by
        simpa only [cardinalityFloor] using hfloor⟩
  rcases hcleanupExists with
    ⟨Dcleanup, hDcleanupTop, htargetCleanup, hdeltaMaxCleanup,
      cleanup, hcleanupFloor⟩
  have hDcleanupZero : Dcleanup ≠ 0 := by
    intro hzero
    rw [hzero] at htargetCleanup
    exact htargetZero (bot_unique htargetCleanup)
  have hcleanupUpper : cleanup.family.enncard ≤
      2400 * target * (Kakeya.deltaTubeVolume r)⁻¹ :=
    pure_wz2_cleanup_family_card_le hr hr_one family shading target Dcleanup
      budget.net cleanup hambientSupportSix hdeltaMaxCleanup htargetCleanup
      htargetZero hDcleanupTop
  have hcardinalityUpper : HasExtremalCardinalityUpper
      cleanup.family (analyticLoss / 10) := by
    have hpowerUpper := pure_wz2_cleanup_family_card_power_le hr hcleanupUpper
    calc
      cleanup.family.enncard ≤
          2400 * Kakeya.realRpowENN r (-2 - thinEta) := by
            simpa only [target] using hpowerUpper
      _ ≤ Kakeya.realRpowENN r (-2 - analyticLoss / 10) := by
        rw [show -2 - analyticLoss / 10 =
            (-(analyticLoss / 10 - thinEta)) + (-2 - thinEta) by ring,
          realRpowENN_add hr]
        gcongr
        simpa only [thinEta] using budget.final_card_absorb
  have hcleanupNonempty : cleanup.family.Nonempty := by
    have hpositive : 0 < cardinalityFloor := by
      exact ENNReal.mul_pos pureWZ2FinalFloorConstant_ne_zero
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _)).ne'
    have hcardPositive : 0 < cleanup.family.enncard :=
      hpositive.trans_le hcleanupFloor
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty,
      Kakeya.Streamlined.TubeFamily.enncard] using hcardPositive
  have hcleanupDense : cleanup.shading.IsLambdaDense
      (Kakeya.realRpowENN r analyticLoss) := by
    apply cleanup.isLambdaDense_of_absorption hr htargetZero htargetTop
      hDcleanupZero hDcleanupTop hdense
    exact pure_wz2_cleanup_density_absorption hr target cleanup.loss rfl
      (pure_wz2_cleanup_loss_le hr hr_one hthin_pos budget.net budget.net_loss)
      (by simpa only [coreLoss, thinEta] using budget.density_absorb)
  let densityBound : ENNReal := budget.net.lossFactor * 10 * target
  let normalizedConstant : ENNReal := Kakeya.realRpowENN r (-analyticLoss)
  have hnetBound : budget.net.lossFactor * 10 ≤ (10^8 : ENNReal) := by
    calc
      budget.net.lossFactor * 10 ≤ (10^7 : ENNReal) * 10 :=
        by simpa [mul_comm] using mul_le_mul_right budget.net_loss 10
      _ = 10^8 := by norm_num
  have htubeAbsorb :
      24 * Kakeya.deltaTubeVolume 1 * densityBound *
          (Kakeya.realRpowENN r 2)⁻¹ ≤
        normalizedConstant * cardinalityFloor := by
    calc
      24 * Kakeya.deltaTubeVolume 1 * densityBound *
          (Kakeya.realRpowENN r 2)⁻¹ ≤
        (24 * Kakeya.deltaTubeVolume 1 * (10^8 : ENNReal)) *
          Kakeya.realRpowENN r (-thinEta) * Kakeya.realRpowENN r (-2) := by
            rw [pure_wz2_realRpowENN_inv hr]
            dsimp only [densityBound, target]
            have h := mul_le_mul_left hnetBound
              (24 * Kakeya.deltaTubeVolume 1 *
                Kakeya.realRpowENN r (-thinEta) *
                Kakeya.realRpowENN r (-2))
            simpa [mul_assoc, mul_comm, mul_left_comm] using h
      _ ≤ normalizedConstant * cardinalityFloor := by
        dsimp only [normalizedConstant, cardinalityFloor]
        exact pure_wz2_normalized_nonconcentration_absorption hr
          (24 * Kakeya.deltaTubeVolume 1 * (10^8 : ENNReal))
          (by simpa only [coreLoss, thinEta] using budget.tube_wolff_absorb)
  have hparamAbsorb :
      4800 * densityBound * (Kakeya.deltaTubeVolume r)⁻¹ ≤
        normalizedConstant * cardinalityFloor := by
    have hVinv : (Kakeya.deltaTubeVolume r)⁻¹ ≤
        Kakeya.realRpowENN r (-2) := by
      have h := ENNReal.inv_le_inv.mpr (canonical_volume_lower hr)
      have hpow : ENNReal.ofReal (r ^ 2) = Kakeya.realRpowENN r 2 := by
        simp [Kakeya.realRpowENN]
      rw [hpow, pure_wz2_realRpowENN_inv hr] at h
      exact h
    calc
      4800 * densityBound * (Kakeya.deltaTubeVolume r)⁻¹ ≤
          (4800 * (10^8 : ENNReal)) *
            Kakeya.realRpowENN r (-thinEta) *
              Kakeya.realRpowENN r (-2) := by
        dsimp only [densityBound, target]
        have h := mul_le_mul_left hnetBound
          (4800 * Kakeya.realRpowENN r (-thinEta) *
            Kakeya.realRpowENN r (-2))
        exact (mul_le_mul_of_nonneg_left hVinv (by positivity)).trans (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using h)
      _ ≤ normalizedConstant * cardinalityFloor := by
        dsimp only [normalizedConstant, cardinalityFloor]
        exact pure_wz2_normalized_nonconcentration_absorption hr
          (4800 * (10^8 : ENNReal))
          (by simpa only [coreLoss, thinEta] using
            budget.parameter_frostman_absorb)
  have hcleanupTubeWolff : TubeWolffBound cleanup.family normalizedConstant :=
    deltaMax_to_normalized_tubeWolff hr hr_one cleanup.family densityBound
      cardinalityFloor normalizedConstant cleanup.deltaMax_le hcleanupFloor
      htubeAbsorb
  have hcleanupPF :
      TubeParameterFrostmanBound cleanup.family normalizedConstant :=
    deltaMax_to_normalized_parameterFrostman hr cleanup.family
      (node7_cleanup_hasBoundedBase cleanup hbase)
      (node7_cleanup_vertical cleanup hvertical) densityBound cardinalityFloor
      normalizedConstant cleanup.deltaMax_le hcleanupFloor hparamAbsorb
  refine ⟨{
    family := cleanup.family
    family_nonempty := hcleanupNonempty
    shading := cleanup.shading
    dense := hcleanupDense
    bounded_base := node7_cleanup_hasBoundedBase cleanup hbase
    analytic_distinct := cleanup.analytic_distinct
    vertical_chart := node7_cleanup_vertical cleanup hvertical
    tube_wolff := by simpa [normalizedConstant] using hcleanupTubeWolff
    parameter_frostman := by simpa [normalizedConstant] using hcleanupPF
    cardinality_upper := hcardinalityUpper
    slope_window := node7_cleanup_slope_window cleanup hwindow
    analysisSlope := slope.centered
    analysisSlope_zero := by simp [SlopeFunction.centered]
    analysisSlope_nonsingular :=
      SlopeFunction.centered_isNonsingular hslope_nonsingular
    projection_upper :=
      (node7_cleanup_projection_upper cleanup slope hslope_zero).trans
      (by simpa only [twistedUnion] using hprojection) }⟩

/-- A family-independent cutoff below which the scale-generic cleanup budget
is available for every later runtime family and shading satisfying the stated
ordinary geometric and analytic hypotheses. -/
structure PureWZ2Node7AnalyticCleanupCutoffData
    (sigma analyticLoss : ℝ) where
  r₀ : ℝ
  r₀_pos : 0 < r₀
  r₀_le_small : r₀ ≤ 1 / 10000
  budget : ∀ {r : ℝ}, 0 < r → r ≤ r₀ →
    ∀ (family : Kakeya.Streamlined.TubeFamily r)
      (shading : Kakeya.Streamlined.TubeShading family),
      family.Nonempty → HasBoundedBase family 4 →
      IsInVerticalChart family → WZ1PaperIsLineClass family →
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN r (-(analyticLoss / 100))) →
      shading.IsLambdaDense
        (Kakeya.realRpowENN r (analyticLoss / 100)) →
      Nonempty (PureWZ2Node7AnalyticCleanupScaleBudget
        sigma analyticLoss r family shading)

/-- Choose every numerical threshold before the runtime scale, family, and
shading.  Runtime data are used only after specialization below `r₀`. -/
theorem pure_wz2_node7_analytic_cleanup_cutoff
    (sigma analyticLoss : ℝ)
    (_hσ : 0 < sigma) (hσ_one : sigma < 1)
    (hloss : 0 < analyticLoss) (hloss_sigma : analyticLoss < sigma) :
    Nonempty (PureWZ2Node7AnalyticCleanupCutoffData
      sigma analyticLoss) := by
  let coreLoss : ℝ := analyticLoss / 100
  let thinEta : ℝ := analyticLoss / 20
  have hcore_pos : 0 < coreLoss := by positivity
  have hthin_pos : 0 < thinEta := by positivity
  rcases union_bound_small_delta
      (A := 200) (c := 11 - Real.exp 1)
      (η' := thinEta) (by norm_num)
      (by linarith [Real.exp_one_lt_three]) hthin_pos with
    ⟨dUnion, hdUnion_pos, hUnionSmall⟩
  let secondExponent : ℝ := -2 + coreLoss - thinEta
  have hsecond_neg : secondExponent < 0 := by
    dsimp only [secondExponent, coreLoss, thinEta]
    linarith [hloss_sigma, hσ_one]
  rcases rpow_negative_tends_to_inf
      (c := (3 - Real.exp 1) / pureWZ2SamplingConstant.toReal)
      (e := secondExponent)
      (by
        have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
        exact div_pos (by linarith) pureWZ2SamplingConstant_toReal_pos)
      hsecond_neg with
    ⟨dSecond, hdSecond_pos, hSecondSmall⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one
      (3000 : ℝ) (by norm_num) 1 (by norm_num) with
    ⟨dGeometry, hdGeometry_pos, _hdGeometry_one, _hGeometrySmall⟩
  rcases exists_delta_mul_rpow_le_rpow
      (24 : ℝ) (by norm_num)
      (show sigma - analyticLoss < sigma - coreLoss by
        dsimp only [coreLoss]
        linarith) with
    ⟨dProjection, hdProjection_pos, _hdProjection_one, _hProjectionSmall⟩
  rcases exists_delta_realRpowENN_bound
      (2 * (2700000000000000001 : ENNReal) *
        pureWZ2SamplingConstant)
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (by norm_num))
        pureWZ2SamplingConstant_ne_top)
      (show 0 < analyticLoss / 10 - (3 * coreLoss + thinEta) by
        dsimp only [coreLoss, thinEta]
        linarith) with
    ⟨dCardUpper, hdCardUpper_pos, _hdCardUpper_one, _hCardUpperSmall⟩
  rcases exists_delta_realRpowENN_bound
      (2400 : ENNReal) (by norm_num)
      (show 0 < analyticLoss / 10 - thinEta by
        dsimp only [thinEta]
        linarith) with
    ⟨dFinalUpper, hdFinalUpper_pos, _hdFinalUpper_one, hFinalUpperSmall⟩
  rcases exists_delta_realRpowENN_bound
      (55296 * Kakeya.deltaTubeVolume 1)
      (ENNReal.mul_ne_top (by norm_num)
        (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).2)
      hcore_pos with
    ⟨dPaperCard, hdPaperCard_pos, _hdPaperCard_one, hPaperCardSmall⟩
  rcases exists_delta_realRpowENN_bound
      pureWZ2SamplingConstant pureWZ2SamplingConstant_ne_top
      (show 0 < 2 - 2 * coreLoss + thinEta by
        dsimp only [coreLoss, thinEta]
        linarith [hloss_sigma, hσ_one]) with
    ⟨dSamplingMass, hdSamplingMass_pos, _hdSamplingMass_one,
      hSamplingMassSmall⟩
  rcases exists_delta_realRpowENN_bound
      (4 * (2700000000000000001 : ENNReal)) (by norm_num)
      (show 0 < analyticLoss - coreLoss - thinEta by
        dsimp only [coreLoss, thinEta]
        linarith) with
    ⟨dDensity, hdDensity_pos, _hdDensity_one, hDensitySmall⟩
  rcases exists_delta_realRpowENN_bound
      ((2 * (2700000000000000001 : ENNReal) * pureWZ2SamplingConstant) *
        (24 * Kakeya.deltaTubeVolume 1 * (10^8 : ENNReal)))
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (by norm_num))
          pureWZ2SamplingConstant_ne_top)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num)
            (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).2)
          (by norm_num)))
      (show 0 < analyticLoss - 3 * coreLoss - 2 * thinEta by
        dsimp only [coreLoss, thinEta]
        linarith) with
    ⟨dTubeWolff, hdTubeWolff_pos, _hdTubeWolff_one, hTubeWolffSmall⟩
  rcases exists_delta_realRpowENN_bound
      ((2 * (2700000000000000001 : ENNReal) * pureWZ2SamplingConstant) *
        (4800 * (10^8 : ENNReal)))
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (by norm_num))
          pureWZ2SamplingConstant_ne_top)
        (by norm_num))
      (show 0 < analyticLoss - 3 * coreLoss - 2 * thinEta by
        dsimp only [coreLoss, thinEta]
        linarith) with
    ⟨dParamFrostman, hdParamFrostman_pos, _hdParamFrostman_one,
      hParamFrostmanSmall⟩
  let r₀ := min dUnion (min dSecond (min dGeometry (min dProjection
    (min dCardUpper (min dFinalUpper (min dPaperCard
      (min dSamplingMass (min dDensity
        (min dTubeWolff (min dParamFrostman (1 / 10000)))))))))))
  refine ⟨{
    r₀ := r₀
    r₀_pos := by dsimp only [r₀]; positivity
    r₀_le_small := by
      dsimp only [r₀]
      simp only [min_le_iff]
      right; right; right; right; right; right; right; right; right; right
      right; exact le_rfl
    budget := ?_ }⟩
  intro r hr hr₀ family shading hfamily hbase _hvertical hline hcwa hdense
  have hrUnion : r ≤ dUnion := hr₀.trans (by
    dsimp only [r₀]
    exact min_le_left _ _)
  have hrSecond : r ≤ dSecond := hr₀.trans (by
    dsimp only [r₀]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hrFinalUpper : r ≤ dFinalUpper := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; left; exact le_rfl)
  have hrPaperCard : r ≤ dPaperCard := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; right; left; exact le_rfl)
  have hrSamplingMass : r ≤ dSamplingMass := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; right; right; left; exact le_rfl)
  have hrDensity : r ≤ dDensity := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; right; right; right; left; exact le_rfl)
  have hrTubeWolff : r ≤ dTubeWolff := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; right; right; right; right; left
    exact le_rfl)
  have hrParamFrostman : r ≤ dParamFrostman := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; right; right; right; right; right; left
    exact le_rfl)
  have hrSmall : r ≤ 1 / 10000 := hr₀.trans (by
    dsimp only [r₀]
    simp only [min_le_iff]
    right; right; right; right; right; right; right; right; right; right
    right; exact le_rfl)
  have hrOne : r ≤ 1 := hrSmall.trans (by norm_num)
  rcases pure_wz2_tube_density_test_net_explicit hr hrOne with
    ⟨net, hnetLoss, hnetCard⟩
  let target := Kakeya.realRpowENN r (-thinEta)
  let D := 9261000 * Kakeya.realRpowENN r (-coreLoss) *
    family.enncard * Kakeya.deltaTubeVolume r
  have hdeltaMaxD : family.toBodyFamily.deltaMax ≤ D :=
    paper_cwa_to_ordinary_deltaMax hr hrOne family hline hbase
      (Kakeya.realRpowENN r (-coreLoss)) hcwa
  have hDtop : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.coe_ne_top)
      (tube_volume_scaling.2.1 r hr hrOne).2
  have htargetZero : target ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hr _)).ne'
  have htargetTop : target ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpaperCard : Kakeya.realRpowENN r (-2 + 2 * coreLoss) ≤
      family.enncard :=
    wz2PaperConvexWolff_cardinality_lower
      wz2_paper_tube_carrier_geometry
      wz2_paper_convex_wolff_cardinality_core hr
      (by linarith [hrSmall]) hfamily hline hcwa
      (hPaperCardSmall r hr hrPaperCard)
  have hunionFirst : (net.testSets.card : ℝ) *
      Real.exp (-(11 - Real.exp 1) * target.toReal) < 1 / 16 := by
    have htargetReal : target.toReal = Real.rpow r (-thinEta) :=
      Subunit.realRpowENN_toReal hr
    exact density_net_failure_bound htargetReal hnetCard
      (hUnionSmall r hr hrUnion)
  have hcleanupInput : family.toBodyFamily.deltaMax ≤ target ∨
      target ≤ D ∧ Kakeya.deltaTubeVolume r ≤ (target / D) * shading.mass ∧
        (net.testSets.card : ℝ) *
              Real.exp (-(11 - Real.exp 1) * target.toReal) +
            Real.exp (-(3 - Real.exp 1) *
              (target.toReal / D.toReal) * (family.card : ℝ)) < 1 / 8 := by
    by_cases hlow : family.toBodyFamily.deltaMax ≤ target
    · exact Or.inl hlow
    · right
      have htargetD : target ≤ D := (le_of_not_ge hlow).trans hdeltaMaxD
      have hsample := pure_wz2_high_sampling_card_power_lower hr hrOne
        family.enncard D ENNReal.coe_ne_top hDtop le_rfl htargetD
      have hDzero : D ≠ 0 := by
        intro hzero
        rw [hzero] at htargetD
        exact htargetZero (bot_unique htargetD)
      have hsampleReal : pureWZ2SamplingConstant.toReal⁻¹ *
          Real.rpow r secondExponent ≤
          (target.toReal / D.toReal) * (family.card : ℝ) := by
        have hleftTop : pureWZ2SamplingConstant⁻¹ *
            Kakeya.realRpowENN r secondExponent ≠ ⊤ :=
          ENNReal.mul_ne_top
            (ENNReal.inv_ne_top.mpr pureWZ2SamplingConstant_pos.ne')
            ENNReal.ofReal_ne_top
        have hrightTop : (target / D) * family.enncard ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.div_ne_top htargetTop hDzero)
            ENNReal.coe_ne_top
        have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).mpr hsample
        simpa [ENNReal.toReal_mul, ENNReal.toReal_div,
          pureWZ2SamplingConstant_ne_top, hDtop,
          Kakeya.Streamlined.TubeFamily.enncard,
          Subunit.realRpowENN_toReal hr] using hreal
      have hsecond : Real.exp (-(3 - Real.exp 1) *
          ((target.toReal / D.toReal) * (family.card : ℝ))) < 1 / 16 :=
        pure_wz2_thinning_failure_bound
          (by linarith [Real.exp_one_lt_three])
          pureWZ2SamplingConstant_toReal_pos hsampleReal
          (hSecondSmall r hr hrSecond)
      have hunion : (net.testSets.card : ℝ) *
              Real.exp (-(11 - Real.exp 1) * target.toReal) +
            Real.exp (-(3 - Real.exp 1) *
              (target.toReal / D.toReal) * (family.card : ℝ)) < 1 / 8 := by
        have hsecond' : Real.exp (-(3 - Real.exp 1) *
            (target.toReal / D.toReal) * (family.card : ℝ)) < 1 / 16 := by
          simpa [mul_assoc] using hsecond
        linarith
      have hmass : Kakeya.deltaTubeVolume r ≤
          (target / D) * shading.mass := by
        have hdenseMass : Kakeya.realRpowENN r coreLoss *
            family.toBodyFamily.mass ≤ shading.mass := hdense
        rw [tubeFamily_mass_eq_nominal family] at hdenseMass
        change Kakeya.realRpowENN r coreLoss *
          (family.enncard * Kakeya.deltaTubeVolume r) ≤ shading.mass
          at hdenseMass
        have hraw : pureWZ2SamplingConstant⁻¹ *
            Kakeya.realRpowENN r secondExponent *
              (Kakeya.realRpowENN r coreLoss * Kakeya.deltaTubeVolume r) ≤
            (target / D) * shading.mass := by
          calc
            _ ≤ ((target / D) * family.enncard) *
                (Kakeya.realRpowENN r coreLoss *
                  Kakeya.deltaTubeVolume r) := by gcongr
            _ = (target / D) * (Kakeya.realRpowENN r coreLoss *
                (family.enncard * Kakeya.deltaTubeVolume r)) := by ring
            _ ≤ (target / D) * shading.mass := by gcongr
        have hconst : pureWZ2SamplingConstant ≤
            Kakeya.realRpowENN r (-(2 - 2 * coreLoss + thinEta)) :=
          hSamplingMassSmall r hr hrSamplingMass
        have hfactor : (1 : ENNReal) ≤ pureWZ2SamplingConstant⁻¹ *
            Kakeya.realRpowENN r secondExponent *
              Kakeya.realRpowENN r coreLoss := by
          have hpower : pureWZ2SamplingConstant ≤
              Kakeya.realRpowENN r secondExponent *
                Kakeya.realRpowENN r coreLoss := by
            rw [← realRpowENN_add hr]
            have hexp : secondExponent + coreLoss =
                -(2 - 2 * coreLoss + thinEta) := by
              dsimp only [secondExponent]
              ring
            rw [hexp]
            exact hconst
          have hinv := mul_le_mul_right hpower pureWZ2SamplingConstant⁻¹
          have hcancel : pureWZ2SamplingConstant⁻¹ *
              pureWZ2SamplingConstant = 1 :=
            ENNReal.inv_mul_cancel pureWZ2SamplingConstant_pos.ne'
              pureWZ2SamplingConstant_ne_top
          simpa [hcancel, mul_assoc, mul_comm, mul_left_comm] using hinv
        have hleft : Kakeya.deltaTubeVolume r ≤
            pureWZ2SamplingConstant⁻¹ *
              Kakeya.realRpowENN r secondExponent *
                (Kakeya.realRpowENN r coreLoss *
                  Kakeya.deltaTubeVolume r) := by
          simpa [mul_assoc] using mul_le_mul_left hfactor
            (Kakeya.deltaTubeVolume r)
        exact hleft.trans hraw
      exact ⟨htargetD, hmass, hunion⟩
  exact ⟨{
    net := net
    net_loss := hnetLoss
    cleanup_input := by
      simpa only [target, D, coreLoss, thinEta] using hcleanupInput
    paper_card_absorb := by
      simpa only [coreLoss] using hPaperCardSmall r hr hrPaperCard
    final_card_absorb := hFinalUpperSmall r hr hrFinalUpper
    density_absorb := by
      simpa only [coreLoss, thinEta] using hDensitySmall r hr hrDensity
    tube_wolff_absorb := by
      simpa only [coreLoss, thinEta] using hTubeWolffSmall r hr hrTubeWolff
    parameter_frostman_absorb := by
      simpa only [coreLoss, thinEta] using
        hParamFrostmanSmall r hr hrParamFrostman }⟩

/-- The automatic scale-generic wrapper: specialize the pre-runtime cutoff,
construct its numerical budget, and run the analytic cleanup. -/
theorem PureWZ2Node7AnalyticCleanupCutoffData.run
    {sigma analyticLoss r : ℝ}
    (cutoff : PureWZ2Node7AnalyticCleanupCutoffData sigma analyticLoss)
    (family : Kakeya.Streamlined.TubeFamily r)
    (shading : Kakeya.Streamlined.TubeShading family)
    (hloss : 0 < analyticLoss)
    (hr : 0 < r) (hr_cutoff : r ≤ cutoff.r₀)
    (hfamily : family.Nonempty) (hbase : HasBoundedBase family 4)
    (hvertical : IsInVerticalChart family)
    (hwindow : IsInSlopeWindow shading)
    (hline : WZ1PaperIsLineClass family)
    (hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN r (-(analyticLoss / 100))))
    (hdense : shading.IsLambdaDense
      (Kakeya.realRpowENN r (analyticLoss / 100)))
    (slope : SlopeFunction) (hslope_zero : slope 0 = 0)
    (hslope_nonsingular : slope.IsNonsingular)
    (hprojection : volume (twistedUnion shading slope) ≤
      Kakeya.realRpowENN r (sigma - analyticLoss)) :
    Nonempty (PureWZ2ParameterFrostmanPreparationData
      sigma analyticLoss r) := by
  rcases cutoff.budget hr hr_cutoff family shading hfamily hbase hvertical
      hline hcwa hdense with ⟨budget⟩
  exact pure_wz2_node7_analytic_cleanup family shading hloss hr
    (hr_cutoff.trans cutoff.r₀_le_small) hfamily hbase hvertical hwindow
    hline hcwa hdense slope hslope_zero hslope_nonsingular hprojection budget

end Kakeya.Assouad

end
