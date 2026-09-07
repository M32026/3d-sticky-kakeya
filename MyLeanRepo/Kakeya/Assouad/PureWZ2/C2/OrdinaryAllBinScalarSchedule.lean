import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderAllGlobalBins
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Scalar schedule for ordinary all-bin coarse selection

The all-bin geometry leaves one uniform scalar inequality.  Its positive
`rho`-power gap pays the original-scale losses and all fixed constants.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A source-scale threshold which pays the complete per-block all-bin cost. -/
structure PureWZ2OrdinaryAllBinScalarThreshold
    (sigma sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss
      outerLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  scalar_budget :
    ∀ {inputLoss coarseLoss delta rho : ℝ},
      0 ≤ inputLoss → inputLoss ≤ sourceLossCeiling →
      0 ≤ coarseLoss → coarseLoss ≤ coarseLossCeiling →
      0 < delta → delta ≤ delta₀ →
      0 < rho → rho ≤ 1 → rho ≤ Real.rpow delta stickyLoss →
      Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
            Kakeya.realRpowENN delta (sigma - inputLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) ≤
        (32 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta (sigma + coarseLoss) *
            Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ) *
            Kakeya.realRpowENN rho
              (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))

/-- Construct the all-bin scalar threshold from the exact exponent gap. -/
theorem pureWZ2_ordinaryAllBin_scalar_threshold
    {sigma sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss
      outerLoss : ℝ}
    (hsourceNonneg : 0 ≤ sourceLossCeiling)
    (hcoarseNonneg : 0 ≤ coarseLossCeiling)
    (hsticky : 0 < stickyLoss)
    (hgap : sourceLossCeiling + coarseLossCeiling <
      stickyLoss *
        (volumeLoss - outerLoss - coarseLossCeiling -
          5 * stickyLoss / 2)) :
    Nonempty (PureWZ2OrdinaryAllBinScalarThreshold sigma
      sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss outerLoss) := by
  let gain := volumeLoss - outerLoss - coarseLossCeiling -
    5 * stickyLoss / 2
  let sourceCost := sourceLossCeiling + coarseLossCeiling
  have hgain : 0 < gain := by
    dsimp only [gain]
    have hsourceCost : 0 ≤ sourceLossCeiling + coarseLossCeiling :=
      add_nonneg hsourceNonneg hcoarseNonneg
    nlinarith
  have hsourceCost : 0 ≤ sourceCost := by
    dsimp only [sourceCost]
    positivity
  let intermediate := (sourceCost + stickyLoss * gain) / 2
  have hsourceIntermediate : sourceCost < intermediate := by
    dsimp only [sourceCost, gain, intermediate] at *
    linarith
  have hintermediateNonneg : 0 ≤ intermediate := by
    dsimp only [intermediate]
    positivity
  have hintermediateGap : intermediate < stickyLoss * gain := by
    dsimp only [sourceCost, gain, intermediate] at *
    linarith
  let exponent := 1 + sigma / 2 + volumeLoss - outerLoss
  let constant : ENNReal :=
    64 * pureWZ2OrdinaryAllBinCoarseVolumeConstant *
      Kakeya.realRpowENN 256 exponent
  have hvolumeConstantTop :
      pureWZ2OrdinaryAllBinCoarseVolumeConstant ≠ ⊤ := by
    norm_num [pureWZ2OrdinaryAllBinCoarseVolumeConstant]
  have hconstantTop : constant ≠ ⊤ := by
    dsimp only [constant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hvolumeConstantTop)
      (by simp [Kakeya.realRpowENN])
  rcases exists_scale_absorb_constant constant hconstantTop
      hsourceCost hsourceIntermediate with
    ⟨constantDelta₀, hconstantDelta₀, hconstantDelta₀One, habsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := stickyLoss) (a := intermediate) (b := gain)
      (by norm_num) hsticky hintermediateNonneg hintermediateGap with
    ⟨transportDelta₀, htransportDelta₀, htransportDelta₀One, htransport⟩
  let delta₀ := min constantDelta₀ transportDelta₀
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hconstantDelta₀ htransportDelta₀
    delta₀_le_one := (min_le_left _ _).trans hconstantDelta₀One
    scalar_budget := ?_
  }⟩
  intro inputLoss coarseLoss delta rho hinputNonneg hinputCeiling
    hcoarseLossNonneg hcoarseLossCeiling hdelta hdeltaSmall hrho hrhoOne
    hrhoPower
  have hdeltaConstant : delta ≤ constantDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaTransport : delta ≤ transportDelta₀ :=
    hdeltaSmall.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaConstant.trans hconstantDelta₀One
  have hactualCost : inputLoss + coarseLoss ≤ sourceCost := by
    dsimp only [sourceCost]
    linarith
  have hactualPower :
      Kakeya.realRpowENN delta (-(inputLoss + coarseLoss)) ≤
        Kakeya.realRpowENN delta (-sourceCost) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
  have hconstantAbsorb :
      constant * Kakeya.realRpowENN delta
          (-(inputLoss + coarseLoss)) ≤
        Kakeya.realRpowENN delta (-intermediate) :=
    (mul_le_mul_left' hactualPower constant).trans
      (habsorb delta hdelta hdeltaConstant)
  have htransported :
      Kakeya.realRpowENN delta (-intermediate) ≤
        Kakeya.realRpowENN rho (-gain) :=
    htransport delta rho hdelta hdeltaTransport hrho hrhoOne
      (by simpa using hrhoPower)
  have hfactor : constant * Kakeya.realRpowENN delta
      (-(inputLoss + coarseLoss)) ≤
        Kakeya.realRpowENN rho
          (-(volumeLoss - outerLoss - coarseLoss -
            5 * stickyLoss / 2)) := by
    apply hconstantAbsorb.trans
    apply htransported.trans
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by
      dsimp only [gain]
      linarith)
  let rhoBase := 2 + sigma / 2 + coarseLoss + 5 * stickyLoss / 2
  have hconstant256 :
      Kakeya.realRpowENN 256 (-outerLoss) *
          Kakeya.realRpowENN 256 (1 + sigma / 2 + volumeLoss) =
        Kakeya.realRpowENN 256 exponent := by
    rw [← realRpowENN_add (by norm_num : (0 : ℝ) < 256)]
    congr 1
    dsimp only [exponent]
    ring
  have hrhoCombine :
      (Kakeya.realRpowENN rho (-outerLoss) *
          Kakeya.realRpowENN rho 1) *
          Kakeya.realRpowENN rho (1 + sigma / 2 + volumeLoss) =
        Kakeya.realRpowENN rho
          (rhoBase +
            (volumeLoss - outerLoss - coarseLoss -
              5 * stickyLoss / 2)) := by
    rw [← realRpowENN_add hrho, ← realRpowENN_add hrho]
    congr 1
    dsimp only [rhoBase]
    ring
  have hleftRho :
      Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) =
        Kakeya.realRpowENN 256 exponent *
          Kakeya.realRpowENN rho
            (rhoBase +
              (volumeLoss - outerLoss - coarseLoss -
                5 * stickyLoss / 2)) := by
    rw [realRpowENN_mul (by norm_num) hrho (-outerLoss),
      realRpowENN_mul (by norm_num) hrho
        (1 + sigma / 2 + volumeLoss)]
    calc
      _ = (Kakeya.realRpowENN 256 (-outerLoss) *
            Kakeya.realRpowENN 256
              (1 + sigma / 2 + volumeLoss)) *
          ((Kakeya.realRpowENN rho (-outerLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN rho
              (1 + sigma / 2 + volumeLoss)) := by ring
      _ = Kakeya.realRpowENN 256 exponent *
          Kakeya.realRpowENN rho
            (rhoBase +
              (volumeLoss - outerLoss - coarseLoss -
                5 * stickyLoss / 2)) := by
        rw [hconstant256, hrhoCombine]
  have hdeltaSplit :
      Kakeya.realRpowENN delta (-(inputLoss + coarseLoss)) *
          Kakeya.realRpowENN delta (sigma + coarseLoss) =
        Kakeya.realRpowENN delta (sigma - inputLoss) := by
    rw [← realRpowENN_add hdelta]
    congr 1
    ring
  have hrhoSplit :
      Kakeya.realRpowENN rho
          (-(volumeLoss - outerLoss - coarseLoss -
            5 * stickyLoss / 2)) *
          Kakeya.realRpowENN rho
            (rhoBase +
              (volumeLoss - outerLoss - coarseLoss -
                5 * stickyLoss / 2)) =
        Kakeya.realRpowENN rho rhoBase := by
    rw [← realRpowENN_add hrho]
    congr 1
    ring
  have hscaled :
      (64 * pureWZ2OrdinaryAllBinCoarseVolumeConstant *
          Kakeya.realRpowENN 256 exponent) *
          Kakeya.realRpowENN delta (sigma - inputLoss) *
          Kakeya.realRpowENN rho
            (rhoBase +
              (volumeLoss - outerLoss - coarseLoss -
                5 * stickyLoss / 2)) ≤
        Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho rhoBase := by
    calc
      _ = constant *
            (Kakeya.realRpowENN delta (sigma - inputLoss) *
              Kakeya.realRpowENN rho
                (rhoBase +
                  (volumeLoss - outerLoss - coarseLoss -
                    5 * stickyLoss / 2))) := by
        dsimp only [constant]
        ring
      _ = constant *
            ((Kakeya.realRpowENN delta (-(inputLoss + coarseLoss)) *
                Kakeya.realRpowENN delta (sigma + coarseLoss)) *
              Kakeya.realRpowENN rho
                (rhoBase +
                  (volumeLoss - outerLoss - coarseLoss -
                    5 * stickyLoss / 2))) := by
        rw [hdeltaSplit]
      _ = (constant * Kakeya.realRpowENN delta
              (-(inputLoss + coarseLoss))) *
            (Kakeya.realRpowENN delta (sigma + coarseLoss) *
              Kakeya.realRpowENN rho
                (rhoBase +
                  (volumeLoss - outerLoss - coarseLoss -
                    5 * stickyLoss / 2))) := by ring
      _ ≤ Kakeya.realRpowENN rho
              (-(volumeLoss - outerLoss - coarseLoss -
                5 * stickyLoss / 2)) *
            (Kakeya.realRpowENN delta (sigma + coarseLoss) *
              Kakeya.realRpowENN rho
                (rhoBase +
                  (volumeLoss - outerLoss - coarseLoss -
                    5 * stickyLoss / 2))) := by
        gcongr
      _ = Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho rhoBase := by
        calc
          _ = Kakeya.realRpowENN delta (sigma + coarseLoss) *
              (Kakeya.realRpowENN rho
                (-(volumeLoss - outerLoss - coarseLoss -
                  5 * stickyLoss / 2)) *
                Kakeya.realRpowENN rho
                  (rhoBase +
                    (volumeLoss - outerLoss - coarseLoss -
                      5 * stickyLoss / 2))) := by ring
          _ = _ := by rw [hrhoSplit]
  have hmul32 :
      32 *
        (Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
            Kakeya.realRpowENN delta (sigma - inputLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss))) ≤
        Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho rhoBase := by
    rw [show 32 *
        (Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
            Kakeya.realRpowENN delta (sigma - inputLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss))) =
      (64 * pureWZ2OrdinaryAllBinCoarseVolumeConstant *
          Kakeya.realRpowENN delta (sigma - inputLoss)) *
        (Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          Kakeya.realRpowENN rho 1 *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) by ring, hleftRho]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hright :
      Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho rhoBase =
        Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
          Kakeya.realRpowENN rho (1 / 2 : ℝ) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
    have hfirst :
        Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ) =
          Kakeya.realRpowENN rho
            (stickyLoss + coarseLoss + 1 / 2) :=
      (realRpowENN_add hrho _ _).symm
    have hsecond :
        Kakeya.realRpowENN rho
              (stickyLoss + coarseLoss + 1 / 2) *
            Kakeya.realRpowENN rho
              (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) =
          Kakeya.realRpowENN rho rhoBase := by
      rw [← realRpowENN_add hrho]
      congr 1
      dsimp only [rhoBase]
      ring
    rw [← hsecond, ← hfirst]
    ring
  rw [hright] at hmul32
  calc
    Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
            Kakeya.realRpowENN delta (sigma - inputLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) =
        (32 : ENNReal)⁻¹ *
          (32 *
            (Kakeya.realRpowENN (256 * rho) (-outerLoss) *
              (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
                Kakeya.realRpowENN delta (sigma - inputLoss) *
                Kakeya.realRpowENN rho 1) *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss)))) := by
      calc
        _ = ((32 : ENNReal)⁻¹ * 32) *
            (Kakeya.realRpowENN (256 * rho) (-outerLoss) *
              (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
                Kakeya.realRpowENN delta (sigma - inputLoss) *
                Kakeya.realRpowENN rho 1) *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss))) := by
          rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ = _ := by ring
    _ ≤ (32 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
          Kakeya.realRpowENN rho (1 / 2 : ℝ) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) := by
      exact mul_le_mul_left' hmul32 _

/-- Apply the uniform scalar threshold to the exact all-bin family selected
over every regularized source block. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData.selectGoodCoarseBinsOfThreshold
    {sigma sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss
      outerLoss inputLoss delta rho middleLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    (coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins)
    (threshold : PureWZ2OrdinaryAllBinScalarThreshold sigma
      sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss outerLoss)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hcoarseLossNonneg : 0 ≤ twoScale.coarseLoss)
    (hcoarseLossCeiling : twoScale.coarseLoss ≤ coarseLossCeiling)
    (hdeltaSmall : delta ≤ threshold.delta₀)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hrhoPower : rho ≤ Real.rpow delta stickyLoss)
    (houter : ∀ block : {block // block ∈ safe.blocks},
      (2 * (carriers.carrier block).outerPopular.popular.bins : ENNReal) ≤
        Kakeya.realRpowENN (256 * rho) (-outerLoss)) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
        (volumeLoss := volumeLoss) coarseBins) := by
  apply coarseBins.selectGoodCoarseBinsOfScalarBudget houter
  simpa only [twoScale.rhoRequested_eq] using
    threshold.scalar_budget hinputNonneg hinputCeiling
      hcoarseLossNonneg hcoarseLossCeiling source.extremal.delta_pos
      hdeltaSmall hrho hrhoOne hrhoPower

end Kakeya.Assouad

end
