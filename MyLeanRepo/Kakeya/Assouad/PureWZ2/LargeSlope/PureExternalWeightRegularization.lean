import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureFiniteNearbyRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization

/-!
# Public pure nearby-scale regularization with external tube weights

The weight retained by Lemma 8 is the literal source mass inside the selected
spatial and derivative window.  It need not itself be a cubical shading.
This module regularizes the actual public pure parent maps using that external
weight and recovers public pure nearby-scale CWA on the selected subfamily.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2ExternalWeightRegularizationData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal)
    (levelCount : ℕ)
    (externalWeight : Fin family.card → ENNReal) where
  schedule : PureWZ2FiniteNearbyScheduleData
    (family := family) ambientConstant scheduleConstant levelCount
  selected : Kakeya.Streamlined.TubeSubfamily family
  selected_nonempty : selected.family.Nonempty
  selectedWeight : ENNReal
  selectedWeight_eq : selectedWeight =
    ∑ index : Fin selected.family.card,
      externalWeight (selected.embedding index)
  selectedWeightLevel : ENNReal
  selectedWeightLevel_pos : 0 < selectedWeightLevel
  selectedWeightLevel_ne_top : selectedWeightLevel ≠ ⊤
  selected_weight_band : ∀ index : Fin selected.family.card,
    selectedWeightLevel ≤ externalWeight (selected.embedding index) ∧
      externalWeight (selected.embedding index) ≤
        2 * selectedWeightLevel
  selected_weight_pos : ∀ index : Fin selected.family.card,
    0 < externalWeight (selected.embedding index)
  selected_weight_average_floor : ∀ index : Fin selected.family.card,
    (∑ source : Fin family.card, externalWeight source) /
        (2 * family.enncard) ≤
      externalWeight (selected.embedding index)
  regularizationLoss : ENNReal
  regularizationLoss_eq : regularizationLoss =
    (8 : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
  retained_weight :
    (∑ index : Fin family.card, externalWeight index) ≤
      regularizationLoss * selectedWeight
  degreeConstant : ENNReal
  degreeConstant_eq : degreeConstant =
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        schedule.scaleCount
  degree_uniform :
    ∀ coordinate,
      ∀ first second :
          Fin (schedule.witness coordinate).scaleData.coarse.card,
        0 <
            ((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) = first).card →
        0 <
            ((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) = second).card →
        ((((Finset.univ : Finset (Fin selected.family.card)).filter
          fun source =>
            (schedule.witness coordinate).scaleData.cover.parent
                (selected.embedding source) = first).card : ℕ) : ENNReal) ≤
          degreeConstant *
            ((((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) = second).card : ℕ) :
              ENNReal)
  retentionConstant : ENNReal
  retentionConstant_eq : retentionConstant =
    regularizationLoss * weightUpper
  cardinality_retention :
    normalizationWeight * family.enncard ≤
      retentionConstant * selected.family.enncard
  outputConstant : ENNReal
  outputConstant_eq : outputConstant =
    max scheduleConstant
      (wz2PaperPureNearbyRestrictionConstant
        ambientConstant normalizationWeight degreeConstant
          retentionConstant)
  cwa_nearby : WZ2PaperPureCWAAtNearbyScales
    selected.family outputConstant

namespace PureWZ2ExternalWeightRegularizationData

/-- Summing the lower endpoint of the selected dyadic weight band gives a
denominator-free lower bound for the retained total weight. -/
theorem selectedWeightLevel_mul_selectedCard_le_selectedWeight
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight) :
    data.selectedWeightLevel * data.selected.family.enncard ≤
      data.selectedWeight := by
  rw [data.selectedWeight_eq]
  change data.selectedWeightLevel *
      (data.selected.family.card : ENNReal) ≤
    ∑ index : Fin data.selected.family.card,
      externalWeight (data.selected.embedding index)
  calc
    data.selectedWeightLevel *
          (data.selected.family.card : ENNReal) =
        ∑ _index : Fin data.selected.family.card,
          data.selectedWeightLevel := by simp [mul_comm]
    _ ≤ ∑ index : Fin data.selected.family.card,
        externalWeight (data.selected.embedding index) :=
      Finset.sum_le_sum fun index _ => (data.selected_weight_band index).1

/-- A caller-facing upper envelope for the nearby-CWA constant produced by
external-weight regularization.  The four hypotheses isolate the schedule,
ambient, degree, and inverse-normalization losses, so later small-scale
arguments can absorb them independently. -/
theorem outputConstant_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper
      targetConstant : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hschedule : scheduleConstant ≤ targetConstant)
    (hambient : ambientConstant ≤ targetConstant)
    (hdegree : data.degreeConstant ≤ targetConstant)
    (hratio : (normalizationWeight⁻¹ *
        (ambientConstant * data.retentionConstant * data.degreeConstant)) *
      ambientConstant ≤ targetConstant) :
    data.outputConstant ≤ targetConstant := by
  rw [data.outputConstant_eq]
  apply max_le hschedule
  unfold wz2PaperPureNearbyRestrictionConstant
  exact max_le hambient (max_le hdegree hratio)

/-- Fixed-depth upper bound for the regularization loss after replacing the
runtime family logarithm by a caller-supplied envelope. -/
theorem regularizationLoss_le_logEnvelope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper
      logEnvelope : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hlog : (Nat.log 2 (2 * family.card) + 1 : ENNReal) ≤ logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.regularizationLoss ≤
      8 * logEnvelope ^ (levelCount + 2) := by
  rw [data.regularizationLoss_eq]
  have hexponent : data.schedule.scaleCount + 1 ≤ levelCount + 2 := by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_right data.schedule.scaleCount_le 1
  calc
    (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (data.schedule.scaleCount + 1) ≤
        8 * logEnvelope ^ (data.schedule.scaleCount + 1) := by gcongr
    _ ≤ 8 * logEnvelope ^ (levelCount + 2) := by
      exact mul_le_mul_left'
        (pow_le_pow_right' hlogOne hexponent) _

/-- Fixed-depth upper bound for the per-scale degree constant. -/
theorem degreeConstant_le_logEnvelope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper
      logEnvelope : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hlog : (Nat.log 2 (2 * family.card) + 1 : ENNReal) ≤ logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.degreeConstant ≤
      16 * ((levelCount + 1 : ℕ) : ENNReal) *
        logEnvelope ^ (levelCount + 1) := by
  rw [data.degreeConstant_eq]
  have hcount : (data.schedule.scaleCount : ENNReal) ≤
      ((levelCount + 1 : ℕ) : ENNReal) := by
    exact_mod_cast data.schedule.scaleCount_le
  calc
    16 * (data.schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            data.schedule.scaleCount ≤
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          logEnvelope ^ data.schedule.scaleCount := by gcongr
    _ ≤ 16 * ((levelCount + 1 : ℕ) : ENNReal) *
          logEnvelope ^ (levelCount + 1) := by
      exact mul_le_mul_left'
        (pow_le_pow_right' hlogOne data.schedule.scaleCount_le) _

/-- The fixed-depth retention loss is controlled by the same logarithmic
envelope and the uniform per-tube weight bound. -/
theorem retentionConstant_le_logEnvelope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper
      logEnvelope : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hlog : (Nat.log 2 (2 * family.card) + 1 : ENNReal) ≤ logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.retentionConstant ≤
      (8 * logEnvelope ^ (levelCount + 2)) * weightUpper := by
  rw [data.retentionConstant_eq]
  exact mul_le_mul_right'
    (data.regularizationLoss_le_logEnvelope hlog hlogOne) _

/-- Explicit fixed-depth envelope for one external-weight regularization. -/
def pureWZ2ExternalWeightOutputEnvelope
    (ambientBound scheduleBound normalizationInverseBound weightUpperBound
      logEnvelope : ENNReal) (levelCount : ℕ) : ENNReal :=
  max scheduleBound <| max ambientBound <|
    max
      (16 * ((levelCount + 1 : ℕ) : ENNReal) *
        logEnvelope ^ (levelCount + 1))
      ((normalizationInverseBound *
          (ambientBound *
            ((8 * logEnvelope ^ (levelCount + 2)) * weightUpperBound) *
            (16 * ((levelCount + 1 : ℕ) : ENNReal) *
              logEnvelope ^ (levelCount + 1)))) *
        ambientBound)

/-- Every regularization output is bounded by the explicit envelope once the
ambient, schedule, normalization, weight, and logarithmic inputs are bounded. -/
theorem outputConstant_le_externalWeightOutputEnvelope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper
      ambientBound scheduleBound normalizationInverseBound weightUpperBound
      logEnvelope : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hambient : ambientConstant ≤ ambientBound)
    (hschedule : scheduleConstant ≤ scheduleBound)
    (hnormalization : normalizationWeight⁻¹ ≤ normalizationInverseBound)
    (hweight : weightUpper ≤ weightUpperBound)
    (hlog : (Nat.log 2 (2 * family.card) + 1 : ENNReal) ≤ logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.outputConstant ≤ pureWZ2ExternalWeightOutputEnvelope
      ambientBound scheduleBound normalizationInverseBound weightUpperBound
      logEnvelope levelCount := by
  let degreeEnvelope : ENNReal :=
    16 * ((levelCount + 1 : ℕ) : ENNReal) *
      logEnvelope ^ (levelCount + 1)
  let retentionEnvelope : ENNReal :=
    (8 * logEnvelope ^ (levelCount + 2)) * weightUpperBound
  have hdegree : data.degreeConstant ≤ degreeEnvelope := by
    exact data.degreeConstant_le_logEnvelope hlog hlogOne
  have hretention : data.retentionConstant ≤ retentionEnvelope := by
    calc
      data.retentionConstant ≤
          (8 * logEnvelope ^ (levelCount + 2)) * weightUpper :=
        data.retentionConstant_le_logEnvelope hlog hlogOne
      _ ≤ retentionEnvelope := by
        exact mul_le_mul_left' hweight _
  apply data.outputConstant_le
  · exact hschedule.trans <| by
      unfold pureWZ2ExternalWeightOutputEnvelope
      exact le_max_left _ _
  · exact hambient.trans <| by
      unfold pureWZ2ExternalWeightOutputEnvelope
      exact (le_max_left ambientBound _).trans (le_max_right _ _)
  · exact hdegree.trans <| by
      unfold pureWZ2ExternalWeightOutputEnvelope degreeEnvelope
      exact (le_max_left _ _).trans <|
        (le_max_right ambientBound _).trans (le_max_right _ _)
  · have hratio :
        (normalizationWeight⁻¹ *
            (ambientConstant * data.retentionConstant * data.degreeConstant)) *
          ambientConstant ≤
        (normalizationInverseBound *
            (ambientBound * retentionEnvelope * degreeEnvelope)) *
          ambientBound := by gcongr
    exact hratio.trans <| by
      unfold pureWZ2ExternalWeightOutputEnvelope
      exact (le_max_right _ _).trans <|
        (le_max_right ambientBound _).trans (le_max_right _ _)

/-- Fixed-depth envelope which keeps the inverse normalization and the
per-source weight upper bound paired.  In geometric applications these two
quantities carry reciprocal width or Jacobian factors, so separating them
would create a spurious scale loss. -/
def pureWZ2ExternalWeightRatioOutputEnvelope
    (ambientBound scheduleBound normalizationWeightRatioBound logEnvelope :
      ENNReal) (levelCount : ℕ) : ENNReal :=
  max scheduleBound <| max ambientBound <|
    max
      (16 * ((levelCount + 1 : ℕ) : ENNReal) *
        logEnvelope ^ (levelCount + 1))
      ((normalizationWeightRatioBound *
          (ambientBound * (8 * logEnvelope ^ (levelCount + 2)) *
            (16 * ((levelCount + 1 : ℕ) : ENNReal) *
              logEnvelope ^ (levelCount + 1)))) *
        ambientBound)

/-- Ratio-aware version of
`outputConstant_le_externalWeightOutputEnvelope`.  The hypothesis controls
`normalizationWeight⁻¹ * weightUpper` as one expression, retaining any exact
geometric cancellation between the two factors. -/
theorem outputConstant_le_externalWeightRatioOutputEnvelope
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper
      ambientBound scheduleBound normalizationWeightRatioBound logEnvelope :
      ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hambient : ambientConstant ≤ ambientBound)
    (hschedule : scheduleConstant ≤ scheduleBound)
    (hratio : normalizationWeight⁻¹ * weightUpper ≤
      normalizationWeightRatioBound)
    (hlog : (Nat.log 2 (2 * family.card) + 1 : ENNReal) ≤ logEnvelope)
    (hlogOne : 1 ≤ logEnvelope) :
    data.outputConstant ≤ pureWZ2ExternalWeightRatioOutputEnvelope
      ambientBound scheduleBound normalizationWeightRatioBound logEnvelope
        levelCount := by
  let degreeEnvelope : ENNReal :=
    16 * ((levelCount + 1 : ℕ) : ENNReal) *
      logEnvelope ^ (levelCount + 1)
  let lossEnvelope : ENNReal :=
    8 * logEnvelope ^ (levelCount + 2)
  have hdegree : data.degreeConstant ≤ degreeEnvelope := by
    exact data.degreeConstant_le_logEnvelope hlog hlogOne
  have hloss : data.regularizationLoss ≤ lossEnvelope := by
    exact data.regularizationLoss_le_logEnvelope hlog hlogOne
  apply data.outputConstant_le
  · exact hschedule.trans <| by
      unfold pureWZ2ExternalWeightRatioOutputEnvelope
      exact le_max_left _ _
  · exact hambient.trans <| by
      unfold pureWZ2ExternalWeightRatioOutputEnvelope
      exact (le_max_left ambientBound _).trans (le_max_right _ _)
  · exact hdegree.trans <| by
      unfold pureWZ2ExternalWeightRatioOutputEnvelope degreeEnvelope
      exact (le_max_left _ _).trans <|
        (le_max_right ambientBound _).trans (le_max_right _ _)
  · have hrewritten :
        (normalizationWeight⁻¹ *
            (ambientConstant * data.retentionConstant * data.degreeConstant)) *
          ambientConstant =
        ((normalizationWeight⁻¹ * weightUpper) *
            (ambientConstant * data.regularizationLoss * data.degreeConstant)) *
          ambientConstant := by
        rw [data.retentionConstant_eq]
        ring
    rw [hrewritten]
    have hratioBound :
        ((normalizationWeight⁻¹ * weightUpper) *
            (ambientConstant * data.regularizationLoss *
              data.degreeConstant)) * ambientConstant ≤
          (normalizationWeightRatioBound *
            (ambientBound * lossEnvelope * degreeEnvelope)) *
              ambientBound := by
      gcongr
    exact hratioBound.trans <| by
      unfold pureWZ2ExternalWeightRatioOutputEnvelope lossEnvelope
        degreeEnvelope
      exact (le_max_right _ _).trans <|
        (le_max_right ambientBound _).trans (le_max_right _ _)

/-- The output nearby-CWA constant dominates the ambient constant whenever the
chosen schedule constant pays for its square. -/
theorem ambientConstant_le_outputConstant
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hambientOne : 1 ≤ ambientConstant)
    (hschedule : ambientConstant * ambientConstant ≤ scheduleConstant) :
    ambientConstant ≤ data.outputConstant := by
  have hambientLeSquare :
      ambientConstant ≤ ambientConstant * ambientConstant := by
    simpa using mul_le_mul_left' hambientOne ambientConstant
  have hscheduleLeOutput : scheduleConstant ≤ data.outputConstant := by
    rw [data.outputConstant_eq]
    exact le_max_left _ _
  exact hambientLeSquare.trans <| hschedule.trans hscheduleLeOutput

/-- A schedule constant dominating the square of an ambient constant larger
than two forces the regularized nearby-CWA output constant to remain larger
than two. -/
theorem outputConstant_gt_two
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hambientTwo : 2 < ambientConstant)
    (hschedule : ambientConstant * ambientConstant ≤ scheduleConstant) :
    2 < data.outputConstant := by
  exact hambientTwo.trans_le <| data.ambientConstant_le_outputConstant
    ((by norm_num : (1 : ENNReal) ≤ 2).trans hambientTwo.le) hschedule

/-- The dyadic level selected by external-weight regularization is bounded
below by one quarter of any per-source normalization whose total mass is
available.  This denominator-free form is the input needed when a later
regularization contains `selectedWeightLevel⁻¹` in its CWA constant. -/
theorem normalization_div_four_le_selectedWeightLevel
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    (hmass : normalizationWeight * family.enncard ≤
      ∑ index : Fin family.card, externalWeight index) :
    normalizationWeight / 4 ≤ data.selectedWeightLevel := by
  let selectedIndex : Fin data.selected.family.card :=
    ⟨0, data.selected_nonempty⟩
  let weight := externalWeight (data.selected.embedding selectedIndex)
  have haverage := data.selected_weight_average_floor selectedIndex
  have hfamilyNonempty : family.Nonempty := by
    change 0 < family.card
    exact data.selected_nonempty.trans_le
      (by
        simpa using Fintype.card_le_of_injective
          data.selected.embedding data.selected.embedding.injective)
  have hcardZero : family.enncard ≠ 0 := by
    change (family.card : ENNReal) ≠ 0
    exact_mod_cast hfamilyNonempty.ne'
  have hcardTop : family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have htwoCardZero : 2 * family.enncard ≠ 0 :=
    mul_ne_zero (by norm_num) hcardZero
  have htwoCardTop : 2 * family.enncard ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hcardTop
  have htotal : (∑ index : Fin family.card, externalWeight index) ≤
      weight * (2 * family.enncard) := by
    apply (ENNReal.div_le_iff htwoCardZero htwoCardTop).mp
    exact haverage
  have hnormalizationFour : normalizationWeight ≤
      4 * data.selectedWeightLevel := by
    have hscaled : normalizationWeight * family.enncard ≤
        (4 * data.selectedWeightLevel) * family.enncard := by
      calc
        normalizationWeight * family.enncard ≤
            ∑ index : Fin family.card, externalWeight index := hmass
        _ ≤ weight * (2 * family.enncard) := htotal
        _ ≤ (2 * data.selectedWeightLevel) *
            (2 * family.enncard) := by
          gcongr
          exact (data.selected_weight_band selectedIndex).2
        _ = (4 * data.selectedWeightLevel) * family.enncard := by ring
    exact (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp <| by
      simpa [mul_comm] using hscaled
  exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).2 <| by
    simpa [mul_comm] using hnormalizationFour

/-- The same weighted cardinality retention transfers the cropped top-level
Convex--Wolff bound to the selected source family. -/
theorem top_level_cwa
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (data : PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight)
    {topConstant : ENNReal}
    (htop : WZ2PaperConvexWolffBound family topConstant)
    (hnormalizationZero : normalizationWeight ≠ 0)
    (hnormalizationTop : normalizationWeight ≠ ⊤) :
    WZ2PaperConvexWolffBound data.selected.family
      ((normalizationWeight⁻¹ * data.retentionConstant) * topConstant) :=
  htop.subfamily_of_weighted_cardinality data.selected
    hnormalizationZero hnormalizationTop data.cardinality_retention

end PureWZ2ExternalWeightRegularizationData

theorem pureWZ2_external_weight_regularization
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scheduleConstant normalizationWeight weightUpper :
      ENNReal}
    (ambientCWA : WZ2PaperPureCWAAtNearbyScales family ambientConstant)
    (hfamily : family.Nonempty)
    (hdeltaOne : delta ≤ 1)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant scheduleConstant)
    (hnormalizationZero : normalizationWeight ≠ 0)
    (hnormalizationTop : normalizationWeight ≠ ⊤)
    (hweightUpperTop : weightUpper ≠ ⊤)
    (externalWeight : Fin family.card → ENNReal)
    (hmass : normalizationWeight * family.enncard ≤
      ∑ index : Fin family.card, externalWeight index)
    (hweight : ∀ index, externalWeight index ≤ weightUpper)
    (levelCount : ℕ)
    (hambientTwo : 2 < ambientConstant)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      ambientConstant ^ levelCount)
    (hscheduleConstant :
      ambientConstant * ambientConstant ≤ scheduleConstant) :
    Nonempty (PureWZ2ExternalWeightRegularizationData
      ambientConstant scheduleConstant normalizationWeight weightUpper
        levelCount externalWeight) := by
  classical
  have hdelta := ambientCWA.1
  rcases pureWZ2_finite_pure_nearby_schedule levelCount
      hdelta hdeltaOne hambientTwo ambientCWA.2.1.2
      hlevels hscheduleConstant ambientCWA with
    ⟨schedule⟩
  let Parent : Fin schedule.scaleCount → Type := fun coordinate =>
    Fin (schedule.witness coordinate).scaleData.coarse.card
  let parent : ∀ coordinate, Fin family.card → Parent coordinate :=
    fun coordinate =>
      (schedule.witness coordinate).scaleData.cover.parent
  rcases simultaneous_degree_regularization_with_support_and_weight_band
      schedule.scaleCount Parent parent externalWeight with
    ⟨selectedIndices, huniform, hretained, hpositive, hfloor,
      hweightBand⟩
  rcases hweightBand schedule.scaleCount_pos with
    ⟨weightLevel, hweightLevelPos, hweightBand⟩
  let selected := Kakeya.Streamlined.TubeSubfamily.fromFinset
    family selectedIndices
  let selectedWeight := ∑ index : Fin selected.family.card,
    externalWeight (selected.embedding index)
  have hembeddingMem : ∀ index : Fin selected.family.card,
      selected.embedding index ∈ selectedIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem selectedIndices rfl index
  have himage : Finset.image selected.embedding
      (Finset.univ : Finset (Fin selected.family.card)) =
        selectedIndices := by
    ext index
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨source, rfl⟩
      exact hembeddingMem source
    · intro hindex
      let source : Fin selected.family.card :=
        (selectedIndices.orderIsoOfFin rfl).symm ⟨index, hindex⟩
      refine ⟨source, ?_⟩
      exact congrArg Subtype.val
        ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
          ⟨index, hindex⟩)
  have hselectedWeight : selectedWeight =
      ∑ index ∈ selectedIndices, externalWeight index := by
    dsimp only [selectedWeight]
    have hsum :
        (∑ index : Fin selected.family.card,
            externalWeight (selected.embedding index)) =
          ∑ index ∈ Finset.image selected.embedding
              (Finset.univ : Finset (Fin selected.family.card)),
            externalWeight index := by
      exact (Finset.sum_image
        (fun first _ second _ heq =>
          selected.embedding.injective heq)).symm
    rw [hsum, himage]
  let regularizationLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (schedule.scaleCount + 1)
  let degreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        schedule.scaleCount
  let retentionConstant := regularizationLoss * weightUpper
  let restrictionConstant := wz2PaperPureNearbyRestrictionConstant
    ambientConstant normalizationWeight degreeConstant retentionConstant
  let outputConstant := max scheduleConstant restrictionConstant
  have hretained' :
      (∑ index : Fin family.card, externalWeight index) ≤
        regularizationLoss * selectedWeight := by
    rw [hselectedWeight]
    simpa [regularizationLoss] using hretained
  have htotalPos : 0 < ∑ index : Fin family.card, externalWeight index := by
    have hfamilyPos : 0 < family.enncard := by
      change (0 : ENNReal) < (family.card : ENNReal)
      exact_mod_cast hfamily
    exact (ENNReal.mul_pos hnormalizationZero hfamilyPos.ne').trans_le hmass
  have hselectedNonempty : selected.family.Nonempty := by
    have hselectedIndicesNonempty : selectedIndices.Nonempty := by
      by_contra hempty
      have hselectedEmpty : selectedIndices = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hsum :
          ∑ index ∈ selectedIndices, externalWeight index = 0 := by
        rw [hselectedEmpty]
        simp
      have hzero :
          (∑ index : Fin family.card, externalWeight index) ≤ 0 := by
        rw [hselectedWeight, hsum, mul_zero] at hretained'
        exact hretained'
      exact (not_le_of_gt htotalPos) hzero
    dsimp only [selected, Kakeya.Streamlined.TubeFamily.Nonempty]
    exact hselectedIndicesNonempty.card_pos
  have hselectedWeightPos : ∀ index : Fin selected.family.card,
      0 < externalWeight (selected.embedding index) := by
    intro index
    exact hpositive _ (hembeddingMem index)
  have hselectedWeightBand : ∀ index : Fin selected.family.card,
      weightLevel ≤ externalWeight (selected.embedding index) ∧
        externalWeight (selected.embedding index) ≤ 2 * weightLevel := by
    intro index
    exact hweightBand _ (hembeddingMem index)
  have hweightLevelTop : weightLevel ≠ ⊤ := by
    let index : Fin selected.family.card :=
      ⟨0, by simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using
        hselectedNonempty⟩
    exact ne_top_of_le_ne_top
      (ne_top_of_le_ne_top hweightUpperTop
        (hweight (selected.embedding index)))
      (hselectedWeightBand index).1
  have hdegreeUniform :
      ∀ coordinate,
        ∀ first second : Parent coordinate,
          0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source => parent coordinate (selected.embedding source) =
                first).card →
          0 < ((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source => parent coordinate (selected.embedding source) =
                second).card →
          ((((Finset.univ : Finset (Fin selected.family.card)).filter
            fun source => parent coordinate (selected.embedding source) =
              first).card : ℕ) : ENNReal) ≤
            degreeConstant *
              ((((Finset.univ : Finset (Fin selected.family.card)).filter
                fun source => parent coordinate (selected.embedding source) =
                  second).card : ℕ) : ENNReal) := by
    intro coordinate first second hfirst hsecond
    have hfirstCard := fromFinset_filter_card selectedIndices
      (parent coordinate) first
    have hsecondCard := fromFinset_filter_card selectedIndices
      (parent coordinate) second
    have hfirst' : 0 < (selectedIndices.filter fun index =>
        parent coordinate index = first).card := by
      rw [← hfirstCard]
      exact hfirst
    have hsecond' : 0 < (selectedIndices.filter fun index =>
        parent coordinate index = second).card := by
      rw [← hsecondCard]
      exact hsecond
    have hraw := huniform coordinate first second hfirst' hsecond'
    have hfirstCast :
        (((Finset.univ : Finset (Fin selected.family.card)).filter
          fun source => parent coordinate (selected.embedding source) =
            first).card : ENNReal) =
          ((selectedIndices.filter fun index =>
            parent coordinate index = first).card : ENNReal) := by
      exact_mod_cast hfirstCard
    have hsecondCast :
        (((Finset.univ : Finset (Fin selected.family.card)).filter
          fun source => parent coordinate (selected.embedding source) =
            second).card : ENNReal) =
          ((selectedIndices.filter fun index =>
            parent coordinate index = second).card : ENNReal) := by
      exact_mod_cast hsecondCard
    rw [hfirstCast, hsecondCast]
    simpa [degreeConstant] using hraw
  have hselectedWeightUpper : selectedWeight ≤
      weightUpper * selected.family.enncard := by
    change (∑ index : Fin selected.family.card,
      externalWeight (selected.embedding index)) ≤
        weightUpper * (selected.family.card : ENNReal)
    calc
      (∑ index : Fin selected.family.card,
          externalWeight (selected.embedding index)) ≤
          ∑ _index : Fin selected.family.card, weightUpper := by
        exact Finset.sum_le_sum fun index _ =>
          hweight (selected.embedding index)
      _ = weightUpper * (selected.family.card : ENNReal) := by
        simp [Finset.sum_const, mul_comm]
  have hcardinality : normalizationWeight * family.enncard ≤
      retentionConstant * selected.family.enncard := by
    calc
      normalizationWeight * family.enncard ≤
          ∑ index : Fin family.card, externalWeight index := hmass
      _ ≤ regularizationLoss * selectedWeight := hretained'
      _ ≤ regularizationLoss *
          (weightUpper * selected.family.enncard) := by gcongr
      _ = retentionConstant * selected.family.enncard := by
        simp [retentionConstant]
        ring
  have hregularizationTop : regularizationLoss ≠ ⊤ := by
    dsimp only [regularizationLoss]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (by simp))
  have hdegreeTop : degreeConstant ≠ ⊤ := by
    dsimp only [degreeConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.pow_ne_top (by simp))
  have hretentionTop : retentionConstant ≠ ⊤ :=
    ENNReal.mul_ne_top hregularizationTop hweightUpperTop
  let pureSelected : WZ2PaperPureTubeSubfamily family :=
    { family := selected.family
      embedding := selected.embedding
      tube_eq := selected.tube_eq }
  have hcwa := schedule.restrictOfWeightedRetention ambientCWA
    hscheduleFinite pureSelected
    (by simpa [pureSelected] using hselectedNonempty)
    normalizationWeight degreeConstant retentionConstant
    hnormalizationZero hnormalizationTop hretentionTop hdegreeTop
    (by simpa [pureSelected] using hcardinality)
    (by
      intro coordinate first second hfirst hsecond
      simpa [pureSelected, parent, Parent] using
        hdegreeUniform coordinate first second hfirst hsecond)
  exact ⟨{
    schedule := schedule
    selected := selected
    selected_nonempty := hselectedNonempty
    selectedWeight := selectedWeight
    selectedWeight_eq := rfl
    selectedWeightLevel := weightLevel
    selectedWeightLevel_pos := hweightLevelPos
    selectedWeightLevel_ne_top := hweightLevelTop
    selected_weight_band := hselectedWeightBand
    selected_weight_pos := hselectedWeightPos
    selected_weight_average_floor := by
      intro index
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        hfloor schedule.scaleCount_pos (selected.embedding index)
          (hembeddingMem index)
    regularizationLoss := regularizationLoss
    regularizationLoss_eq := rfl
    retained_weight := hretained'
    degreeConstant := degreeConstant
    degreeConstant_eq := rfl
    degree_uniform := by
      simpa [parent, Parent] using hdegreeUniform
    retentionConstant := retentionConstant
    retentionConstant_eq := rfl
    cardinality_retention := hcardinality
    outputConstant := outputConstant
    outputConstant_eq := rfl
    cwa_nearby := by
      simpa [outputConstant, restrictionConstant] using hcwa
  }⟩

end Kakeya.Assouad

end
