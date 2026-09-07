import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinUniformScalarSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRelativeMassBudget

/-!
# Production scalar choice for the source-heavy common-bin family

Choose the real common-bin cell count from the midpoint quotient
`popularFloor / (4 * B₀ * cellCap)`.  The two hypotheses below are
multiplication-only budgets and are the exact interface for the pre-runtime
power calculation.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Absorb a fixed logarithmic cost at the source scale and then transport the
remaining negative power to a larger hierarchy scale. -/
private theorem commonBin_log_power_transfer
    (D : ENNReal) (hDTop : D ≠ ⊤) (n : ℕ) (hn : 0 < n)
    {sourceCost scaleLoss gain : ℝ}
    (hsourceCost : 0 ≤ sourceCost) (hscaleLoss : 0 < scaleLoss)
    (hgap : sourceCost < scaleLoss * gain) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {actualCost delta rho : ℝ},
        0 ≤ actualCost → actualCost ≤ sourceCost →
        0 < delta → delta ≤ delta₀ → delta ≤ rho → rho ≤ 1 →
        rho ≤ Real.rpow delta scaleLoss →
          D * ENNReal.ofReal (1 + Real.log rho⁻¹) ^ n *
              Kakeya.realRpowENN delta (-actualCost) ≤
            Kakeya.realRpowENN rho (-gain) := by
  let logLoss := (scaleLoss * gain - sourceCost) / 2
  let intermediate := sourceCost + logLoss
  have hlogLoss : 0 < logLoss := by
    dsimp only [logLoss]
    linarith
  have hintermediateNonneg : 0 ≤ intermediate := by
    dsimp only [intermediate]
    positivity
  have hintermediateGap : intermediate < scaleLoss * gain := by
    dsimp only [intermediate, logLoss]
    linarith
  rcases exists_delta_log_absorbed_ennreal D hDTop hlogLoss hn with
    ⟨logDelta₀, hlogDelta₀, hlogDelta₀One, hlogAbsorb⟩
  rcases exists_scale_power_conversion
      (C := 1) (p := scaleLoss) (a := intermediate) (b := gain)
      (by norm_num) hscaleLoss hintermediateNonneg hintermediateGap with
    ⟨transportDelta₀, htransportDelta₀, htransportDelta₀One, htransport⟩
  let delta₀ := min logDelta₀ transportDelta₀
  refine ⟨delta₀, lt_min hlogDelta₀ htransportDelta₀,
    (min_le_left _ _).trans hlogDelta₀One, ?_⟩
  intro actualCost delta rho hactualNonneg hactualCost hdelta hdeltaSmall
    hdeltaRho hrhoOne hrhoPower
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans ((min_le_left _ _).trans hlogDelta₀One)
  have hlogMono : ENNReal.ofReal (1 + Real.log rho⁻¹) ≤
      ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    apply ENNReal.ofReal_mono
    have hinverse : rho⁻¹ ≤ delta⁻¹ :=
      (inv_le_inv₀ (hdelta.trans_le hdeltaRho) hdelta).mpr hdeltaRho
    exact add_le_add_right
      (Real.log_le_log (inv_pos.mpr (hdelta.trans_le hdeltaRho)) hinverse) 1
  have hlogPower :
      D * ENNReal.ofReal (1 + Real.log rho⁻¹) ^ n ≤
        Kakeya.realRpowENN delta (-logLoss) := by
    calc
      D * ENNReal.ofReal (1 + Real.log rho⁻¹) ^ n ≤
          D * ENNReal.ofReal (1 + Real.log delta⁻¹) ^ n := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-logLoss) :=
        hlogAbsorb delta hdelta
          (hdeltaSmall.trans (min_le_left _ _))
  have hactualPower :
      Kakeya.realRpowENN delta (-actualCost) ≤
        Kakeya.realRpowENN delta (-sourceCost) :=
    realRpowENN_antitone hdelta hdeltaOne (by linarith)
  have htransported :
      Kakeya.realRpowENN delta (-intermediate) ≤
        Kakeya.realRpowENN rho (-gain) :=
    htransport delta rho hdelta
      (hdeltaSmall.trans (min_le_right _ _))
      (hdelta.trans_le hdeltaRho) hrhoOne (by simpa using hrhoPower)
  calc
    D * ENNReal.ofReal (1 + Real.log rho⁻¹) ^ n *
          Kakeya.realRpowENN delta (-actualCost) ≤
        Kakeya.realRpowENN delta (-logLoss) *
          Kakeya.realRpowENN delta (-sourceCost) := by gcongr
    _ = Kakeya.realRpowENN delta (-intermediate) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      dsimp only [intermediate, logLoss]
      ring
    _ ≤ Kakeya.realRpowENN rho (-gain) := htransported

private theorem commonBin_inverseSqrt_mul_spatialPower
    {rho sigma : ℝ} (hrho : 0 < rho) :
    Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) *
        Kakeya.realRpowENN rho (1 - sigma / 2) =
      Kakeya.realRpowENN rho (1 / 2 : ℝ) := by
  have hbase : 1 / Real.sqrt rho = Real.rpow rho (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    simpa [one_div] using
      (Real.rpow_neg hrho.le (1 / 2 : ℝ)).symm
  have hnested :
      Real.rpow (Real.rpow rho (-(1 / 2 : ℝ))) (1 - sigma) =
        Real.rpow rho ((-(1 / 2 : ℝ)) * (1 - sigma)) :=
    (Real.rpow_mul hrho.le (-(1 / 2 : ℝ)) (1 - sigma)).symm
  simp only [Kakeya.realRpowENN, hbase]
  rw [hnested]
  calc
    ENNReal.ofReal (Real.rpow rho (-(1 / 2) * (1 - sigma))) *
          ENNReal.ofReal (Real.rpow rho (1 - sigma / 2)) =
        ENNReal.ofReal
          (Real.rpow rho (-(1 / 2) * (1 - sigma)) *
            Real.rpow rho (1 - sigma / 2)) :=
      (ENNReal.ofReal_mul (Real.rpow_nonneg hrho.le _)).symm
    _ = ENNReal.ofReal (Real.rpow rho
          ((-(1 / 2 : ℝ)) * (1 - sigma) + (1 - sigma / 2))) := by
      congr 1
      exact (Real.rpow_add hrho _ _).symm
    _ = ENNReal.ofReal (Real.rpow rho (1 / 2)) := by
      congr 2
      ring

def pureWZ2SourceHeavyCommonBinPopularConstant : ENNReal :=
  20 * 4 * 264 * 32 * 42

def pureWZ2SourceHeavyCommonBinGraphConstant
    (sigma volumeLoss : ℝ) : ENNReal :=
  20 * 8 * 264 * 32 * 40 * 5 * 512 *
    42 ^ 2 *
    Kakeya.realRpowENN 256 (1 + sigma / 2 + volumeLoss)

def pureWZ2SourceHeavyCommonBinBound
    (sigma inputLoss delta rho : ℝ) : ENNReal :=
  264 * Kakeya.realRpowENN delta (-inputLoss) *
    Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma)

/-- Family-free scalar cutoff for the pre-bin common-bin construction.  The
first field pays the existence of a positive uniform rich-cell count; the
second pays the graph threshold after the separated-parent selection. -/
structure PureWZ2SourceHeavyCommonBinScalarThreshold
    (sigma sourceCostCeiling coarseLossCeiling stickyLoss volumeLoss
      scaleLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  popular_budget :
    ∀ {inputLoss coarseLoss delta rho : ℝ},
      0 ≤ inputLoss → 2 * inputLoss + coarseLoss ≤ sourceCostCeiling →
      0 ≤ coarseLoss → coarseLoss ≤ coarseLossCeiling →
      0 < delta → delta ≤ delta₀ → delta ≤ rho → rho ≤ 1 →
      rho ≤ Real.rpow delta scaleLoss →
        (20 * pureWZ2CommonBinPreBinHeightCost rho) *
            (4 * pureWZ2SourceHeavyCommonBinBound
              sigma inputLoss delta rho *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho) ≤
          Kakeya.realRpowENN delta (sigma + coarseLoss) *
            Kakeya.realRpowENN rho (stickyLoss + coarseLoss)
  graph_budget :
    ∀ {inputLoss coarseLoss delta rho : ℝ},
      0 ≤ inputLoss → 2 * inputLoss + coarseLoss ≤ sourceCostCeiling →
      0 ≤ coarseLoss → coarseLoss ≤ coarseLossCeiling →
      0 < delta → delta ≤ delta₀ → delta ≤ rho → rho ≤ 1 →
      rho ≤ Real.rpow delta scaleLoss →
        (20 * pureWZ2CommonBinPreBinHeightCost rho) *
            ((8 * pureWZ2SourceHeavyCommonBinBound
              sigma inputLoss delta rho *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho) *
              (40 * pureWZ2CommonBinPreBinHeightCost rho *
                (5 : ENNReal) * 512 *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss))) ≤
          Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
            Kakeya.realRpowENN delta (sigma + coarseLoss) *
            Kakeya.realRpowENN rho
              (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)

theorem pureWZ2_sourceHeavyCommonBin_scalar_threshold
    {sigma sourceCostCeiling coarseLossCeiling stickyLoss volumeLoss
      scaleLoss : ℝ}
    (hsourceCost : 0 ≤ sourceCostCeiling)
    (hcoarseLoss : 0 ≤ coarseLossCeiling)
    (hscaleLoss : 0 < scaleLoss)
    (hpopularGap : sourceCostCeiling <
      scaleLoss * (1 / 2 - stickyLoss - coarseLossCeiling))
    (hgraphGap : sourceCostCeiling <
      scaleLoss *
        (volumeLoss - coarseLossCeiling - 5 * stickyLoss / 2)) :
    Nonempty (PureWZ2SourceHeavyCommonBinScalarThreshold sigma
      sourceCostCeiling coarseLossCeiling stickyLoss volumeLoss scaleLoss) := by
  have hpopularConstantTop :
      pureWZ2SourceHeavyCommonBinPopularConstant ≠ ⊤ := by
    unfold pureWZ2SourceHeavyCommonBinPopularConstant
    repeat' apply ENNReal.mul_ne_top
    all_goals simp
  have hgraphConstantTop :
      pureWZ2SourceHeavyCommonBinGraphConstant sigma volumeLoss ≠ ⊤ := by
    unfold pureWZ2SourceHeavyCommonBinGraphConstant
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  rcases commonBin_log_power_transfer
      pureWZ2SourceHeavyCommonBinPopularConstant hpopularConstantTop 1
      (by norm_num) hsourceCost hscaleLoss hpopularGap with
    ⟨popularDelta₀, hpopularDelta₀, hpopularDelta₀One, hpopular⟩
  rcases commonBin_log_power_transfer
      (pureWZ2SourceHeavyCommonBinGraphConstant sigma volumeLoss)
      hgraphConstantTop 2 (by norm_num) hsourceCost hscaleLoss hgraphGap with
    ⟨graphDelta₀, hgraphDelta₀, hgraphDelta₀One, hgraph⟩
  let delta₀ := min popularDelta₀ graphDelta₀
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min hpopularDelta₀ hgraphDelta₀
    delta₀_le_one := (min_le_left _ _).trans hpopularDelta₀One
    popular_budget := ?_
    graph_budget := ?_ }⟩
  · intro inputLoss coarseLoss delta rho hinputNonneg hactualCeiling
      hcoarseNonneg hcoarseCeiling hdelta hdeltaSmall hdeltaRho hrhoOne
      hrhoPower
    have hbase := hpopular
      (show 0 ≤ 2 * inputLoss + coarseLoss by positivity) hactualCeiling hdelta
      (hdeltaSmall.trans (min_le_left _ _)) hdeltaRho hrhoOne hrhoPower
    have htransfer :
        pureWZ2SourceHeavyCommonBinPopularConstant *
            ENNReal.ofReal (1 + Real.log rho⁻¹) *
            Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss)) ≤
          Kakeya.realRpowENN rho
            (-(1 / 2 - stickyLoss - coarseLoss)) := by
        have hbase' :
            pureWZ2SourceHeavyCommonBinPopularConstant *
                ENNReal.ofReal (1 + Real.log rho⁻¹) *
                Kakeya.realRpowENN delta
                  (-(2 * inputLoss + coarseLoss)) ≤
              Kakeya.realRpowENN rho
                (-(1 / 2 - stickyLoss - coarseLossCeiling)) := by
          simpa only [pow_one] using hbase
        exact hbase'.trans <| realRpowENN_antitone
          (hdelta.trans_le hdeltaRho) hrhoOne (by linarith)
    have hheight := pureWZ2CommonBinPreBinHeightCost_le_boundaryFactor rho
    have hdeltaPowers :
        Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma =
          Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss)) *
            Kakeya.realRpowENN delta (sigma + coarseLoss) := by
      have hleft :
          Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma =
            Kakeya.realRpowENN delta
              ((-inputLoss + -inputLoss) + sigma) := by
        calc
          _ = Kakeya.realRpowENN delta (-inputLoss + -inputLoss) *
              Kakeya.realRpowENN delta sigma := by
            rw [(realRpowENN_add hdelta (-inputLoss) (-inputLoss)).symm]
          _ = _ := (realRpowENN_add hdelta _ _).symm
      have hright :
          Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss)) *
              Kakeya.realRpowENN delta (sigma + coarseLoss) =
            Kakeya.realRpowENN delta
              (-(2 * inputLoss + coarseLoss) + (sigma + coarseLoss)) :=
        (realRpowENN_add hdelta _ _).symm
      rw [hleft, hright]
      congr 1
      ring
    have hrhoPowers := commonBin_inverseSqrt_mul_spatialPower
      (sigma := sigma) (hdelta.trans_le hdeltaRho)
    calc
      (20 * pureWZ2CommonBinPreBinHeightCost rho) *
            (4 * pureWZ2SourceHeavyCommonBinBound
              sigma inputLoss delta rho *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho) ≤
          (20 * (42 * ENNReal.ofReal (1 + Real.log rho⁻¹))) *
            (4 * pureWZ2SourceHeavyCommonBinBound
              sigma inputLoss delta rho *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho) := by gcongr
      _ = pureWZ2SourceHeavyCommonBinPopularConstant *
            ENNReal.ofReal (1 + Real.log rho⁻¹) *
          ((Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma) *
            (Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) *
              Kakeya.realRpowENN rho (1 - sigma / 2))) := by
        simp only [pureWZ2SourceHeavyCommonBinBound,
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap]
        norm_num [pureWZ2SourceHeavyCommonBinPopularConstant]
        ring
      _ = (pureWZ2SourceHeavyCommonBinPopularConstant *
            ENNReal.ofReal (1 + Real.log rho⁻¹) *
            Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss))) *
          (Kakeya.realRpowENN delta (sigma + coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ)) := by
        rw [hdeltaPowers, hrhoPowers]
        ring
      _ ≤ Kakeya.realRpowENN rho
            (-(1 / 2 - stickyLoss - coarseLoss)) *
          (Kakeya.realRpowENN delta (sigma + coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ)) := by gcongr
      _ = Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho (stickyLoss + coarseLoss) := by
        calc
          _ = Kakeya.realRpowENN delta (sigma + coarseLoss) *
              (Kakeya.realRpowENN rho
                  (-(1 / 2 - stickyLoss - coarseLoss)) *
                Kakeya.realRpowENN rho (1 / 2 : ℝ)) := by ring
          _ = Kakeya.realRpowENN delta (sigma + coarseLoss) *
              Kakeya.realRpowENN rho
                (-(1 / 2 - stickyLoss - coarseLoss) + 1 / 2) := by
            rw [← realRpowENN_add (hdelta.trans_le hdeltaRho)]
          _ = _ := by congr 2 <;> ring
  · intro inputLoss coarseLoss delta rho hinputNonneg hactualCeiling
      hcoarseNonneg hcoarseCeiling hdelta hdeltaSmall hdeltaRho hrhoOne
      hrhoPower
    have hbase := hgraph
      (show 0 ≤ 2 * inputLoss + coarseLoss by positivity) hactualCeiling hdelta
      (hdeltaSmall.trans (min_le_right _ _)) hdeltaRho hrhoOne hrhoPower
    have htransfer :
        pureWZ2SourceHeavyCommonBinGraphConstant sigma volumeLoss *
            ENNReal.ofReal (1 + Real.log rho⁻¹) ^ 2 *
            Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss)) ≤
          Kakeya.realRpowENN rho
            (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2)) :=
      hbase.trans <| realRpowENN_antitone
        (hdelta.trans_le hdeltaRho) hrhoOne (by linarith)
    have hheight := pureWZ2CommonBinPreBinHeightCost_le_boundaryFactor rho
    have hdeltaPowers :
        Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma =
          Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss)) *
            Kakeya.realRpowENN delta (sigma + coarseLoss) := by
      have hleft :
          Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma =
            Kakeya.realRpowENN delta
              ((-inputLoss + -inputLoss) + sigma) := by
        calc
          _ = Kakeya.realRpowENN delta (-inputLoss + -inputLoss) *
              Kakeya.realRpowENN delta sigma := by
            rw [(realRpowENN_add hdelta (-inputLoss) (-inputLoss)).symm]
          _ = _ := (realRpowENN_add hdelta _ _).symm
      have hright :
          Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss)) *
              Kakeya.realRpowENN delta (sigma + coarseLoss) =
            Kakeya.realRpowENN delta
              (-(2 * inputLoss + coarseLoss) + (sigma + coarseLoss)) :=
        (realRpowENN_add hdelta _ _).symm
      rw [hleft, hright]
      congr 1
      ring
    have hrhoPowers := commonBin_inverseSqrt_mul_spatialPower
      (sigma := sigma) (hdelta.trans_le hdeltaRho)
    have hgraphSplit :
        Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) =
          Kakeya.realRpowENN 256 (1 + sigma / 2 + volumeLoss) *
            Kakeya.realRpowENN rho (1 + sigma / 2 + volumeLoss) :=
      realRpowENN_mul (by norm_num) (hdelta.trans_le hdeltaRho) _
    calc
      (20 * pureWZ2CommonBinPreBinHeightCost rho) *
            ((8 * pureWZ2SourceHeavyCommonBinBound
              sigma inputLoss delta rho *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho) *
              (40 * pureWZ2CommonBinPreBinHeightCost rho *
                (5 : ENNReal) * 512 *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss))) ≤
          (20 * (42 * ENNReal.ofReal (1 + Real.log rho⁻¹))) *
            ((8 * pureWZ2SourceHeavyCommonBinBound
              sigma inputLoss delta rho *
              PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
                sigma inputLoss delta rho) *
              (40 * (42 * ENNReal.ofReal (1 + Real.log rho⁻¹)) *
                (5 : ENNReal) * 512 *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss))) := by gcongr
      _ = pureWZ2SourceHeavyCommonBinGraphConstant sigma volumeLoss *
            ENNReal.ofReal (1 + Real.log rho⁻¹) ^ 2 *
          ((Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma) *
            ((Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) *
                Kakeya.realRpowENN rho (1 - sigma / 2)) *
              Kakeya.realRpowENN rho
                (1 + sigma / 2 + volumeLoss))) := by
        simp only [pureWZ2SourceHeavyCommonBinBound,
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap]
        rw [hgraphSplit]
        norm_num [pureWZ2SourceHeavyCommonBinGraphConstant]
        ring
      _ = (pureWZ2SourceHeavyCommonBinGraphConstant sigma volumeLoss *
            ENNReal.ofReal (1 + Real.log rho⁻¹) ^ 2 *
            Kakeya.realRpowENN delta (-(2 * inputLoss + coarseLoss))) *
          (Kakeya.realRpowENN delta (sigma + coarseLoss) *
            (Kakeya.realRpowENN rho (1 / 2 : ℝ) *
              Kakeya.realRpowENN rho
                (1 + sigma / 2 + volumeLoss))) := by
        rw [hdeltaPowers, hrhoPowers]
        ring
      _ ≤ Kakeya.realRpowENN rho
            (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2)) *
          (Kakeya.realRpowENN delta (sigma + coarseLoss) *
            (Kakeya.realRpowENN rho (1 / 2 : ℝ) *
              Kakeya.realRpowENN rho
                (1 + sigma / 2 + volumeLoss))) := by gcongr
      _ = Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
          Kakeya.realRpowENN delta (sigma + coarseLoss) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
        have hrhoCombine :
            Kakeya.realRpowENN rho (-(volumeLoss - coarseLoss -
                5 * stickyLoss / 2)) *
              (Kakeya.realRpowENN rho (1 / 2 : ℝ) *
                Kakeya.realRpowENN rho
                  (1 + sigma / 2 + volumeLoss)) =
            Kakeya.realRpowENN rho (stickyLoss + coarseLoss) *
              Kakeya.realRpowENN rho
                (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
          have hfirst :
              Kakeya.realRpowENN rho (1 / 2 : ℝ) *
                  Kakeya.realRpowENN rho
                    (1 + sigma / 2 + volumeLoss) =
                Kakeya.realRpowENN rho
                  (1 / 2 + (1 + sigma / 2 + volumeLoss)) :=
            (realRpowENN_add (hdelta.trans_le hdeltaRho) _ _).symm
          have hsecond :
              Kakeya.realRpowENN rho
                  (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2)) *
                Kakeya.realRpowENN rho
                  (1 / 2 + (1 + sigma / 2 + volumeLoss)) =
              Kakeya.realRpowENN rho
                (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2) +
                  (1 / 2 + (1 + sigma / 2 + volumeLoss))) :=
            (realRpowENN_add (hdelta.trans_le hdeltaRho) _ _).symm
          calc
            _ = Kakeya.realRpowENN rho
                (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2) +
                  (1 / 2 + (1 + sigma / 2 + volumeLoss))) := by
              rw [hfirst, hsecond]
            _ = Kakeya.realRpowENN rho
                ((stickyLoss + coarseLoss) +
                  (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) := by
              congr 1
              ring
            _ = _ := realRpowENN_add (hdelta.trans_le hdeltaRho) _ _
        rw [show Kakeya.realRpowENN rho
              (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2)) *
                (Kakeya.realRpowENN delta (sigma + coarseLoss) *
                  (Kakeya.realRpowENN rho (1 / 2 : ℝ) *
                    Kakeya.realRpowENN rho
                      (1 + sigma / 2 + volumeLoss))) =
            Kakeya.realRpowENN delta (sigma + coarseLoss) *
              (Kakeya.realRpowENN rho
                  (-(volumeLoss - coarseLoss - 5 * stickyLoss / 2)) *
                (Kakeya.realRpowENN rho (1 / 2 : ℝ) *
                  Kakeya.realRpowENN rho
                    (1 + sigma / 2 + volumeLoss))) by ring, hrhoCombine]
        ring

theorem PureWZ2TwoScaleCellPullbackData.sourceHeavyCommonBinScalarData_of_mulBudgets
    {sigma inputLoss delta rho middleLoss outputLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (B₀ : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hB₀Pos : 0 < B₀)
    (hB₀Top : B₀ ≠ ⊤)
    (hpopular :
      4 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        volume pullback.shading.union /
          (20 * pureWZ2CommonBinPreBinHeightCost rho))
    (hgraph :
      (8 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho) *
          (40 * pureWZ2CommonBinPreBinHeightCost rho *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) ≤
        (volume pullback.shading.union /
          (20 * pureWZ2CommonBinPreBinHeightCost rho)) *
          twoScale.fine.balanced.cellMass) :
    Nonempty
      (PureWZ2SourceHeavyCommonBinScalarData pullback B₀ volumeLoss) := by
  rcases pullback.sourceHeavyPreBinRhoHeightFamily with ⟨preBinFamily⟩
  let cellCap :=
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho
  let denom : ENNReal := 4 * B₀ * cellCap
  let popular := preBinFamily.popularFloor
  let X := popular / denom
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcellCapPos : 0 < cellCap := by
    unfold cellCap
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num)
          (ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos hdelta _)).ne').ne'
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hdelta _)).ne').ne'
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hrho _)).ne'
  have hcellCapTop : cellCap ≠ ⊤ := by
    unfold cellCap
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      Kakeya.realRpowENN
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hdenomPos : 0 < denom :=
    ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) hB₀Pos.ne').ne'
      hcellCapPos.ne'
  have hdenomTop : denom ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hB₀Top)
      hcellCapTop
  have hpullbackVolumeTop : volume pullback.shading.union ≠ ⊤ := by
    rw [pullback.volume_eq]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      twoScale.coarse.balanced.cellMass_ne_top
  have hpopularTop : popular ≠ ⊤ := by
    unfold popular PureWZ2SourceHeavyPreBinRhoHeightFamilyData.popularFloor
    exact ENNReal.div_ne_top hpullbackVolumeTop (by
      exact (ENNReal.mul_pos (by norm_num)
        (pureWZ2CommonBinPreBinHeightCost_pos hrho <| by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.2).ne').ne')
  have hXOne : 1 ≤ X := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hdenomPos.ne') (Or.inl hdenomTop)).2
    simpa [denom, popular,
      PureWZ2SourceHeavyPreBinRhoHeightFamilyData.popularFloor] using hpopular
  have hXTop : X ≠ ⊤ := by
    exact ENNReal.div_ne_top hpopularTop hdenomPos.ne'
  have hXDenom : X * denom = popular := by
    exact ENNReal.div_mul_cancel hdenomPos.ne' hdenomTop
  have hcapacity :
      2 * B₀ * (X * cellCap) ≤ popular := by
    calc
      2 * B₀ * (X * cellCap) =
          X * (2 * B₀ * cellCap) := by ring
      _ ≤ X * (4 * B₀ * cellCap) := by
        gcongr
        norm_num
      _ = X * denom := by rfl
      _ = popular := hXDenom
  have htwiceDenomPos : 0 < 2 * denom :=
    ENNReal.mul_pos (by norm_num) hdenomPos.ne'
  have htwiceDenomTop : 2 * denom ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hdenomTop
  have hseparated :
      40 * pureWZ2CommonBinPreBinHeightCost rho * (5 : ENNReal) * 512 *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) ≤
        (X / 2) * twoScale.fine.balanced.cellMass := by
    apply (ENNReal.mul_le_mul_iff_right
      htwiceDenomPos.ne' htwiceDenomTop).mp
    calc
      (2 * denom) *
          (40 * pureWZ2CommonBinPreBinHeightCost rho *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) =
        (8 * B₀ * cellCap) *
          (40 * pureWZ2CommonBinPreBinHeightCost rho *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) := by
          dsimp only [denom]
          ring
      _ ≤ popular * twoScale.fine.balanced.cellMass := by
        simpa [popular,
          PureWZ2SourceHeavyPreBinRhoHeightFamilyData.popularFloor] using
          hgraph
      _ = (2 * denom) *
          ((X / 2) * twoScale.fine.balanced.cellMass) := by
        have htwo : (2 : ENNReal) ≠ 0 := by norm_num
        have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
        calc
          popular * twoScale.fine.balanced.cellMass =
              (X * denom) * twoScale.fine.balanced.cellMass := by
            rw [hXDenom]
          _ = (2 * denom) *
              ((X / 2) * twoScale.fine.balanced.cellMass) := by
            rw [show (2 * denom) *
                  ((X / 2) * twoScale.fine.balanced.cellMass) =
                (X / 2 * 2) * denom *
                  twoScale.fine.balanced.cellMass by ring,
              ENNReal.div_mul_cancel htwo htwoTop]
  exact pullback.sourceHeavyCommonBinScalarData preBinFamily B₀ X hB₀
    hXOne hXTop (by rfl) hcapacity hseparated

/-- Reduce the two common-bin construction budgets to explicit power lower
bounds for the literal pullback volume and the second balanced cell mass. -/
theorem PureWZ2TwoScaleCellPullbackData.sourceHeavyCommonBinScalarData_of_powerBudgets
    {sigma inputLoss delta rho middleLoss outputLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (B₀ : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hB₀Pos : 0 < B₀)
    (hB₀Top : B₀ ≠ ⊤)
    (hpopularPower :
      (20 * pureWZ2CommonBinPreBinHeightCost rho) *
          (4 * B₀ *
            PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
              sigma inputLoss delta rho) ≤
        Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN rho
            (outputLoss + twoScale.coarseLoss))
    (hgraphPower :
      (20 * pureWZ2CommonBinPreBinHeightCost rho) *
          ((8 * B₀ *
            PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
              sigma inputLoss delta rho) *
            (40 * pureWZ2CommonBinPreBinHeightCost rho *
              (5 : ENNReal) * 512 *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss))) ≤
        Kakeya.realRpowENN rho
            (outputLoss + twoScale.coarseLoss) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * outputLoss / 2)) :
    Nonempty
      (PureWZ2SourceHeavyCommonBinScalarData pullback B₀ volumeLoss) := by
  let denom := 20 * pureWZ2CommonBinPreBinHeightCost rho
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hdenomPos : 0 < denom :=
    ENNReal.mul_pos (by norm_num)
      (pureWZ2CommonBinPreBinHeightCost_pos hrho hrhoOne).ne'
  have hdenomTop : denom ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (pureWZ2CommonBinPreBinHeightCost_ne_top rho)
  have hvolume :
      Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN rho (outputLoss + twoScale.coarseLoss) ≤
        volume pullback.shading.union := by
    simpa [prepared.shadow_union] using prepared.pullback_volume_relative_lower
  have hpopular :
      4 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        volume pullback.shading.union / denom := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hdenomPos.ne') (Or.inl hdenomTop)).2
    calc
      (4 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho) * denom ≤
        Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN rho (outputLoss + twoScale.coarseLoss) := by
        simpa [denom, mul_comm, mul_left_comm, mul_assoc] using hpopularPower
      _ ≤ volume pullback.shading.union := hvolume
  have hvolumeFine :
      Kakeya.realRpowENN rho
            (outputLoss + twoScale.coarseLoss) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * outputLoss / 2) ≤
        volume pullback.shading.union * twoScale.fine.balanced.cellMass := by
    calc
      _ = (Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho
              (outputLoss + twoScale.coarseLoss)) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * outputLoss / 2) := by ring
      _ ≤ volume pullback.shading.union *
          twoScale.fine.balanced.cellMass := by
        gcongr
        exact twoScale.second_source_floor_power
  have hgraph :
      (8 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho) *
          (40 * pureWZ2CommonBinPreBinHeightCost rho *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) ≤
        (volume pullback.shading.union / denom) *
          twoScale.fine.balanced.cellMass := by
    apply (ENNReal.mul_le_mul_iff_left hdenomPos.ne' hdenomTop).mp
    calc
      ((8 * B₀ *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho) *
          (40 * pureWZ2CommonBinPreBinHeightCost rho *
            (5 : ENNReal) * 512 *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss))) * denom ≤
        volume pullback.shading.union *
          twoScale.fine.balanced.cellMass := by
        simpa [denom, mul_comm, mul_left_comm, mul_assoc] using
          hgraphPower.trans hvolumeFine
      _ = ((volume pullback.shading.union / denom) *
            twoScale.fine.balanced.cellMass) * denom := by
        rw [show ((volume pullback.shading.union / denom) *
                twoScale.fine.balanced.cellMass) * denom =
            ((volume pullback.shading.union / denom) * denom) *
              twoScale.fine.balanced.cellMass by ring,
          ENNReal.div_mul_cancel hdenomPos.ne' hdenomTop]
  simpa [denom] using pullback.sourceHeavyCommonBinScalarData_of_mulBudgets
    B₀ hB₀ hB₀Pos hB₀Top hpopular hgraph

end Kakeya.Assouad

end
