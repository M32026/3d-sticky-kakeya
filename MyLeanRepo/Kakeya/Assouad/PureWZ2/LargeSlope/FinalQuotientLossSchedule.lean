import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6CommonYFixedLossDerivativeBand

/-!
# Pre-runtime loss schedule for the final quotient

Every exponent in this file is chosen before the source scale.  The common
unit is deliberately much smaller than the source-to-final power window
`delta ^ (2 * epsilon) / 2500 <= finalDelta`; later scalar modules may spend
fixed multiples of the unit without changing the quantifier order.
-/

noncomputable section
namespace Kakeya.Assouad

def pureWZ2FinalNearbyLoss (outputLoss : ℝ) : ℝ :=
  min (outputLoss / 16) (1 / 4)

def pureWZ2FinalEpsilon (outputLoss : ℝ) : ℝ :=
  pureWZ2FinalNearbyLoss outputLoss / 1000

def pureWZ2FinalUnitLoss (outputLoss : ℝ) : ℝ :=
  pureWZ2FinalEpsilon outputLoss * pureWZ2FinalNearbyLoss outputLoss / 1000000

/-- All loss parameters needed before asking the Node-3/4/5 chain for a
runtime scale. -/
structure PureWZ2FinalQuotientLossSchedule
    (sigma outputLoss : ℝ) where
  nearbyLoss : ℝ
  epsilon : ℝ
  eta : ℝ
  fixedLoss : ℝ
  cardinalityLoss : ℝ
  scheduleLoss : ℝ
  nearbyLoss_eq : nearbyLoss = pureWZ2FinalNearbyLoss outputLoss
  epsilon_eq : epsilon = pureWZ2FinalEpsilon outputLoss
  eta_eq : eta = pureWZ2FinalUnitLoss outputLoss * sigma ^ 2
  fixedLoss_eq : fixedLoss = eta / 16
  cardinalityLoss_eq : cardinalityLoss = eta / 8192
  scheduleLoss_eq : scheduleLoss = eta / 16
  nearby_loss_pos : 0 < nearbyLoss
  nearby_loss_le_one : nearbyLoss ≤ 1
  nearby_loss_le_output : nearbyLoss ≤ outputLoss
  top_level_gap : 0 < outputLoss - 3 * nearbyLoss
  epsilon_pos : 0 < epsilon
  epsilon_le_sixty_fourth : epsilon ≤ 1 / 64
  eta_pos : 0 < eta
  eta_budget : 1000 * eta ≤ epsilon * sigma ^ 2
  fixed_loss_pos : 0 < fixedLoss
  fixed_loss_le_epsilon : fixedLoss ≤ epsilon
  cardinality_loss_pos : 0 < cardinalityLoss
  schedule_loss_pos : 0 < scheduleLoss
  band_loss_budget :
    eta / 8 + 4 * (eta / 2) + fixedLoss ≤
      3 * pureWZ2FinalUnitLoss outputLoss
  aggregate_loss_budget :
    256 *
        (3 * pureWZ2FinalUnitLoss outputLoss +
          cardinalityLoss + scheduleLoss) <
      2 * epsilon * nearbyLoss

theorem exists_pureWZ2FinalQuotientLossSchedule
    {sigma outputLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (PureWZ2FinalQuotientLossSchedule sigma outputLoss) := by
  let nearbyLoss := pureWZ2FinalNearbyLoss outputLoss
  let epsilon := pureWZ2FinalEpsilon outputLoss
  let unitLoss := pureWZ2FinalUnitLoss outputLoss
  have hnearby : 0 < nearbyLoss := by
    dsimp only [nearbyLoss, pureWZ2FinalNearbyLoss]
    exact lt_min (div_pos houtput (by norm_num)) (by norm_num)
  have hnearbyQuarter : nearbyLoss ≤ 1 / 4 := by
    exact min_le_right _ _
  have hnearbyOutput : nearbyLoss ≤ outputLoss := by
    exact (min_le_left _ _).trans (by linarith)
  have htop : 0 < outputLoss - 3 * nearbyLoss := by
    have hnearbySixteenth : nearbyLoss ≤ outputLoss / 16 :=
      min_le_left _ _
    linarith
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon, pureWZ2FinalEpsilon]
    positivity
  have hepsilonSixtyFourth : epsilon ≤ 1 / 64 := by
    dsimp only [epsilon, pureWZ2FinalEpsilon]
    linarith
  have hunit : 0 < unitLoss := by
    dsimp only [unitLoss, pureWZ2FinalUnitLoss]
    positivity
  have hsigmaSq : sigma ^ 2 < 1 := by
    nlinarith [mul_pos hsigma (sub_pos.mpr hsigmaOne)]
  refine ⟨{
    nearbyLoss := nearbyLoss
    epsilon := epsilon
    eta := unitLoss * sigma ^ 2
    fixedLoss := unitLoss * sigma ^ 2 / 16
    cardinalityLoss := unitLoss * sigma ^ 2 / 8192
    scheduleLoss := unitLoss * sigma ^ 2 / 16
    nearbyLoss_eq := rfl
    epsilon_eq := rfl
    eta_eq := rfl
    fixedLoss_eq := by rfl
    cardinalityLoss_eq := by rfl
    scheduleLoss_eq := by rfl
    nearby_loss_pos := hnearby
    nearby_loss_le_one := hnearbyQuarter.trans (by norm_num)
    nearby_loss_le_output := hnearbyOutput
    top_level_gap := htop
    epsilon_pos := hepsilon
    epsilon_le_sixty_fourth := hepsilonSixtyFourth
    eta_pos := mul_pos hunit (sq_pos_of_pos hsigma)
    eta_budget := ?_
    fixed_loss_pos := by positivity
    fixed_loss_le_epsilon := ?_
    cardinality_loss_pos := by positivity
    schedule_loss_pos := by positivity
    band_loss_budget := ?_
    aggregate_loss_budget := ?_ }⟩
  · dsimp only [unitLoss, pureWZ2FinalUnitLoss]
    have hnearbyNonnegative : 0 ≤ nearbyLoss := hnearby.le
    have hsigmaSqNonnegative : 0 ≤ sigma ^ 2 := sq_nonneg sigma
    dsimp only [epsilon]
    nlinarith [mul_nonneg hepsilon.le hnearbyNonnegative,
      mul_nonneg (mul_nonneg hepsilon.le hnearbyNonnegative)
        hsigmaSqNonnegative]
  · dsimp only [unitLoss, pureWZ2FinalUnitLoss]
    have hnearbyOne : nearbyLoss ≤ 1 :=
      hnearbyQuarter.trans (by norm_num)
    dsimp only [epsilon]
    nlinarith [mul_pos hepsilon hnearby, sq_pos_of_pos hsigma,
      mul_le_mul_of_nonneg_left hnearbyOne hepsilon.le]
  · have hetaLe : unitLoss * sigma ^ 2 ≤ unitLoss := by
      nlinarith [mul_nonneg hunit.le (sq_nonneg sigma)]
    nlinarith
  · dsimp only [unitLoss, pureWZ2FinalUnitLoss]
    have hproduct : 0 < epsilon * nearbyLoss := mul_pos hepsilon hnearby
    have hsigmaSqNonnegative : 0 ≤ sigma ^ 2 := sq_nonneg sigma
    have hsmall : epsilon * nearbyLoss * sigma ^ 2 ≤
        epsilon * nearbyLoss := by
      nlinarith [mul_nonneg hepsilon.le hnearby.le]
    nlinarith

namespace PureWZ2FinalQuotientLossSchedule

theorem scheduleLoss_le_eta_div_eight
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    schedule.scheduleLoss ≤ schedule.eta / 8 := by
  rw [schedule.scheduleLoss_eq]
  exact div_le_div_of_nonneg_left schedule.eta_pos.le (by norm_num)
    (by norm_num)

theorem scheduleLoss_le_nearbyLoss
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    schedule.scheduleLoss ≤ schedule.nearbyLoss := by
  have hsigmaSq : sigma ^ 2 < 1 := by
    nlinarith [mul_pos hsigma (sub_pos.mpr hsigmaOne)]
  have hepsilonNearby : schedule.epsilon ≤ schedule.nearbyLoss := by
    rw [schedule.epsilon_eq, schedule.nearbyLoss_eq]
    unfold pureWZ2FinalEpsilon
    have hnearbyPos : 0 < pureWZ2FinalNearbyLoss outputLoss := by
      simpa [schedule.nearbyLoss_eq] using schedule.nearby_loss_pos
    linarith
  have hproduct : schedule.epsilon * sigma ^ 2 ≤ schedule.epsilon := by
    nlinarith [schedule.epsilon_pos, sq_nonneg sigma]
  rw [schedule.scheduleLoss_eq]
  nlinarith [schedule.eta_budget]

theorem cardinalityLoss_le_scheduleLoss
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    schedule.cardinalityLoss ≤ schedule.scheduleLoss := by
  rw [schedule.cardinalityLoss_eq, schedule.scheduleLoss_eq]
  exact div_le_div_of_nonneg_left schedule.eta_pos.le (by norm_num)
    (by norm_num)

theorem fixedLoss_eq_scheduleLoss
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    schedule.fixedLoss = schedule.scheduleLoss := by
  rw [schedule.fixedLoss_eq, schedule.scheduleLoss_eq]

/-- The fixed common-y derivative band spends at most the loss reserved for
all pre-terminal source refinements. -/
theorem commonY_band_massLoss_le
    {sigma outputLoss delta : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss)
    {lemma31 : PureWZ2Lemma31DerivativeAssembly
      sigma schedule.epsilon delta}
    (heta : lemma31.eta = schedule.eta)
    (commonBand : PureWZ2CoupledCommonYFixedLossDerivativeBandData
      lemma31 schedule.fixedLoss) :
    commonBand.band.massLoss ≤
      3 * pureWZ2FinalUnitLoss outputLoss := by
  rw [commonBand.band_massLoss, commonBand.commonData.common_loss,
    lemma31.data.targetLoss_eq, ← lemma31.eta_eq, heta]
  exact schedule.band_loss_budget

end PureWZ2FinalQuotientLossSchedule

end Kakeya.Assouad
end
