import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CommonSliceRescaled

/-!
# The paper-literal common-slice cost

This file records the scale-independent estimate for the number of literal
height slices times the contribution of one tube to one slice.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- At the literal width `Delta / 100`, the number of height intervals and
the one-tube slab volume have a scale-independent product after the expected
factor `delta ^ 2` is removed. -/
theorem proposition63_literal_interval_cost_le
    {delta Delta : ℝ}
    (hdelta : 0 < delta)
    (hDelta : 0 < Delta)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hDeltaSmall : Delta ≤ 1 / 200) :
    (Fintype.card (commonSliceIntervalType
          (proposition63LiteralSliceWidth Delta)) : ENNReal) *
        commonSliceSingleTubeBound delta Delta ≤
      100000000 * Kakeya.realRpowENN delta 2 := by
  let width : ℝ := proposition63LiteralSliceWidth Delta
  let lower : ℤ := Int.floor (-1 / width)
  let upper : ℤ := Int.floor (1 / width)
  have hwidth : 0 < width := by
    dsimp only [width, proposition63LiteralSliceWidth]
    positivity
  have hlowerUpper : lower ≤ upper + 1 := by
    have hneg : -1 / width ≤ 1 / width := by
      apply (div_le_div_iff_of_pos_right hwidth).2
      norm_num
    have hfloor : lower ≤ upper := Int.floor_mono hneg
    omega
  have hcardInt :
      ((Fintype.card (commonSliceIntervalType width) : ℕ) : ℤ) =
        upper + 1 - lower := by
    simpa only [commonSliceIntervalType, commonSliceHeightIndices, lower, upper,
      Fintype.card_coe] using
        Int.card_Icc_of_le (a := lower) (b := upper) hlowerUpper
  have hupper : (upper : ℝ) ≤ 1 / width := by
    exact Int.floor_le _
  have hlower : -1 / width - 1 < (lower : ℝ) := by
    exact Int.sub_one_lt_floor _
  have hcardReal :
      (Fintype.card (commonSliceIntervalType width) : ℝ) ≤
        2 / width + 2 := by
    have hcardRealEq :
        (Fintype.card (commonSliceIntervalType width) : ℝ) =
          (upper : ℝ) + 1 - (lower : ℝ) := by
      exact_mod_cast hcardInt
    rw [hcardRealEq]
    have hrecip : (-1 : ℝ) / width = -(1 / width) := by ring
    have htwoRecip : (2 : ℝ) / width = 2 * (1 / width) := by ring
    rw [hrecip] at hlower
    rw [htwoRecip]
    linarith
  have hDeltaOne : Delta ≤ 1 := hDeltaSmall.trans (by norm_num)
  have hcardReal' :
      (Fintype.card (commonSliceIntervalType width) : ℝ) ≤
        202 / Delta := by
    calc
      (Fintype.card (commonSliceIntervalType width) : ℝ) ≤
          2 / width + 2 := hcardReal
      _ = 200 / Delta + 2 := by
        dsimp only [width, proposition63LiteralSliceWidth]
        field_simp
        ring
      _ ≤ 202 / Delta := by
        rw [show (200 : ℝ) / Delta + 2 = (200 + 2 * Delta) / Delta by
          field_simp]
        exact (div_le_div_iff_of_pos_right hDelta).2 (by linarith)
  have hcard :
      (Fintype.card (commonSliceIntervalType width) : ENNReal) ≤
        ENNReal.ofReal (202 / Delta) := by
    calc
      (Fintype.card (commonSliceIntervalType width) : ENNReal) =
          ENNReal.ofReal
            (Fintype.card (commonSliceIntervalType width) : ℝ) := by simp
      _ ≤ ENNReal.ofReal (202 / Delta) :=
        ENNReal.ofReal_le_ofReal hcardReal'
  have hdeltaLinear : delta ≤ Delta / 200 := by
    have hfactor : 0 ≤ Delta * (1 / 200 - Delta) :=
      mul_nonneg hDelta.le (sub_nonneg.mpr hDeltaSmall)
    calc
      delta ≤ Delta ^ 2 := hdeltaDelta
      _ ≤ Delta / 200 := by
        nlinarith
  have hsingleReal :
      4 * (Real.pi * (24 * delta) ^ 2 *
          ((Delta + 2 * (24 * delta)) / (1 / 2 : ℝ) +
            2 * (24 * delta))) ≤
        27648 * Delta * delta ^ 2 := by
    have hbracket :
        (Delta + 2 * (24 * delta)) / (1 / 2 : ℝ) +
            2 * (24 * delta) ≤ 3 * Delta := by
      norm_num
      nlinarith
    have hpi := Real.pi_le_four
    have hdeltaSq : 0 ≤ delta ^ 2 := sq_nonneg delta
    have hDeltaNonneg : 0 ≤ Delta := hDelta.le
    calc
      4 * (Real.pi * (24 * delta) ^ 2 *
          ((Delta + 2 * (24 * delta)) / (1 / 2 : ℝ) +
            2 * (24 * delta)))
          ≤ 4 * (4 * (24 * delta) ^ 2 * (3 * Delta)) := by gcongr
      _ = 27648 * Delta * delta ^ 2 := by ring
  have hsingle : commonSliceSingleTubeBound delta Delta ≤
      ENNReal.ofReal (27648 * Delta * delta ^ 2) := by
    rw [commonSliceSingleTubeBound]
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hsingleReal
  have hproductReal :
      (202 / Delta) * (27648 * Delta * delta ^ 2) ≤
        100000000 * delta ^ 2 := by
    have hdeltaSq : 0 ≤ delta ^ 2 := sq_nonneg delta
    field_simp
    nlinarith
  calc
    (Fintype.card (commonSliceIntervalType
          (proposition63LiteralSliceWidth Delta)) : ENNReal) *
        commonSliceSingleTubeBound delta Delta =
        (Fintype.card (commonSliceIntervalType width) : ENNReal) *
          commonSliceSingleTubeBound delta Delta := by rfl
    _ ≤ ENNReal.ofReal (202 / Delta) *
        ENNReal.ofReal (27648 * Delta * delta ^ 2) := by gcongr
    _ = ENNReal.ofReal
        ((202 / Delta) * (27648 * Delta * delta ^ 2)) := by
      exact (ENNReal.ofReal_mul (div_nonneg (by norm_num) hDelta.le)).symm
    _ ≤ ENNReal.ofReal (100000000 * delta ^ 2) :=
      ENNReal.ofReal_le_ofReal hproductReal
    _ = 100000000 * Kakeya.realRpowENN delta 2 := by
      rw [show Kakeya.realRpowENN delta 2 = ENNReal.ofReal (delta ^ 2) by
        simp [Kakeya.realRpowENN]]
      rw [← ENNReal.ofReal_ofNat, ENNReal.ofReal_mul (by norm_num)]

/-- Family-free scale cutoff paying both density transfers in the first
chart.  The exponent `sigma * stickyLoss` is forced by the exact identity
`Delta = h^(sigma/2)` after squaring the terminal fibre mass floor. -/
structure Proposition63M9FirstChartDensityCutoffData
    (sigma stickyLoss localLoss chartLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  common_density : ∀ {q : ℝ}, 0 < q → q ≤ delta₀ →
    Kakeya.realRpowENN q localLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ((400000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN q (sigma * stickyLoss))
  chart_density : ∀ {q : ℝ}, 0 < q → q ≤ delta₀ →
    Kakeya.realRpowENN q chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        (((400000000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN q (sigma * stickyLoss)) / 2)

/-- Choose the two first-chart density absorptions before runtime. -/
theorem proposition63_m9_firstChart_density_cutoff
    {sigma stickyLoss localLoss chartLoss : ℝ}
    (hcommonGap : sigma * stickyLoss < localLoss)
    (hchartGap : sigma * stickyLoss < chartLoss) :
    Nonempty (Proposition63M9FirstChartDensityCutoffData
      sigma stickyLoss localLoss chartLoss) := by
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let commonTarget : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      (400000000 : ENNReal)⁻¹
  let chartTarget : ENNReal := commonTarget / 2
  have commonTargetZero : commonTarget ≠ 0 := by
    dsimp only [commonTarget]
    exact mul_ne_zero (by norm_num) (ENNReal.inv_ne_zero.mpr (by norm_num))
  have commonTargetTop : commonTarget ≠ ⊤ := by
    dsimp only [commonTarget]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.mpr (by norm_num))
  have chartTargetZero : chartTarget ≠ 0 := by
    dsimp only [chartTarget]
    exact ENNReal.div_ne_zero.mpr ⟨commonTargetZero, by norm_num⟩
  have chartTargetTop : chartTarget ≠ ⊤ := by
    dsimp only [chartTarget]
    exact ENNReal.div_ne_top commonTargetTop (by norm_num)
  let fixed : ENNReal := chartTarget⁻¹ * geometry
  have fixedTop : fixed ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr chartTargetZero)
      (by
        dsimp only [geometry]
        exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
  let commonGap : ℝ := localLoss - sigma * stickyLoss
  let chartGap : ℝ := chartLoss - sigma * stickyLoss
  have commonGapPos : 0 < commonGap := by dsimp only [commonGap]; linarith
  have chartGapPos : 0 < chartGap := by dsimp only [chartGap]; linarith
  rcases exists_delta_realRpowENN_bound fixed fixedTop commonGapPos with
    ⟨commonScale, commonScalePos, commonScaleOne, commonBound⟩
  rcases exists_delta_realRpowENN_bound fixed fixedTop chartGapPos with
    ⟨chartScale, chartScalePos, chartScaleOne, chartBound⟩
  let delta₀ := min commonScale chartScale
  have geometric_bound : ∀ {q gap : ℝ}, 0 < q →
      fixed ≤ Kakeya.realRpowENN q (-gap) →
      geometry * Kakeya.realRpowENN q gap ≤ chartTarget := by
    intro q gap hq hbound
    have hsmall : fixed * Kakeya.realRpowENN q gap ≤ 1 := by
      calc
        fixed * Kakeya.realRpowENN q gap ≤
            Kakeya.realRpowENN q (-gap) *
              Kakeya.realRpowENN q gap := by
                exact mul_le_mul_right' hbound _
        _ = 1 := by
          rw [← realRpowENN_add hq]
          simp [Kakeya.realRpowENN]
    have hquotient :
        (geometry * Kakeya.realRpowENN q gap) / chartTarget ≤ 1 := by
      rw [ENNReal.div_eq_inv_mul]
      simpa [fixed, mul_comm, mul_left_comm, mul_assoc] using hsmall
    simpa using (ENNReal.div_le_iff chartTargetZero chartTargetTop).mp hquotient
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min commonScalePos chartScalePos
    delta₀_le_one := (min_le_left _ _).trans commonScaleOne
    common_density := ?_
    chart_density := ?_
  }⟩
  · intro q hq hqCutoff
    have hgap := geometric_bound hq <|
      commonBound q hq (hqCutoff.trans (min_le_left _ _))
    have htarget : chartTarget ≤ commonTarget := by
      dsimp only [chartTarget]
      rw [ENNReal.div_eq_inv_mul]
      calc
        (2 : ENNReal)⁻¹ * commonTarget ≤ 1 * commonTarget := by
          gcongr <;> norm_num
        _ = commonTarget := one_mul _
    have hgeom : geometry * Kakeya.realRpowENN q commonGap ≤
        commonTarget := hgap.trans htarget
    have qPower : Kakeya.realRpowENN q localLoss =
        Kakeya.realRpowENN q (sigma * stickyLoss) *
          Kakeya.realRpowENN q commonGap := by
      rw [← realRpowENN_add hq]
      congr 1
      dsimp only [commonGap]
      ring
    rw [qPower]
    dsimp only [geometry, commonTarget] at hgeom ⊢
    calc
      Kakeya.realRpowENN q (sigma * stickyLoss) *
            Kakeya.realRpowENN q commonGap *
            (55296 * Kakeya.deltaTubeVolume 1) =
          Kakeya.realRpowENN q (sigma * stickyLoss) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN q commonGap) := by ring
      _ ≤ Kakeya.realRpowENN q (sigma * stickyLoss) *
            (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
              (400000000 : ENNReal)⁻¹) :=
        mul_le_mul_left' hgeom _
      _ = _ := by ring
  · intro q hq hqCutoff
    have hgeom := geometric_bound hq <|
      chartBound q hq (hqCutoff.trans (min_le_right _ _))
    have qPower : Kakeya.realRpowENN q chartLoss =
        Kakeya.realRpowENN q (sigma * stickyLoss) *
          Kakeya.realRpowENN q chartGap := by
      rw [← realRpowENN_add hq]
      congr 1
      dsimp only [chartGap]
      ring
    rw [qPower]
    dsimp only [geometry, chartTarget, commonTarget] at hgeom ⊢
    have hgeom' :
        (55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN q chartGap ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ((400000000 : ENNReal)⁻¹ / 2) := by
      simpa [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc]
        using hgeom
    calc
      Kakeya.realRpowENN q (sigma * stickyLoss) *
            Kakeya.realRpowENN q chartGap *
            (55296 * Kakeya.deltaTubeVolume 1) =
          Kakeya.realRpowENN q (sigma * stickyLoss) *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN q chartGap) := by ring
      _ ≤ Kakeya.realRpowENN q (sigma * stickyLoss) *
            (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
              ((400000000 : ENNReal)⁻¹ / 2)) :=
        mul_le_mul_left' hgeom' _
      _ = _ := by
        simp only [ENNReal.div_eq_inv_mul]
        ac_rfl

/-- A family-free density extracted from the terminal complete-fibre mass
floor.  The factor `4` pays for the square of the factor-two terminal
cardinality band, while `100000000` is the literal interval cost above. -/
def proposition63FirstChartTerminalDensity
    (rho outputLoss : ℝ) : ENNReal :=
  (400000000 : ENNReal)⁻¹ *
    Kakeya.realRpowENN rho outputLoss ^ 2

/-- The terminal fibre mass floor and its matching cardinality band imply
the exact aggregate inequality needed by common-slice selection.  All three
hypotheses refer to the same selected complete fibre. -/
theorem proposition63_firstChart_terminal_density_aggregate
    {delta Delta sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily Delta}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hDelta : 0 < Delta}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hDelta)
    (outputLoss : ℝ) (fiberFloor : ℕ)
    (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hmass :
      Kakeya.realRpowENN Delta outputLoss *
            (fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 ≤
        input.selectedFiber.mass)
    (hcard : input.fiberFamily.family.enncard ≤
      2 * (fiberFloor : ENNReal)) :
    (input.fiberFamily.family.card : ENNReal) *
          (proposition63FirstChartTerminalDensity Delta outputLoss *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) ≤
        input.selectedFiber.mass ^ 2 := by
  let A := Kakeya.realRpowENN Delta outputLoss
  let F : ENNReal := fiberFloor
  let d2 := Kakeya.realRpowENN delta 2
  let intervalCost :=
    (Fintype.card (commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) : ENNReal) *
        commonSliceSingleTubeBound delta Delta
  let fixed : ENNReal := 400000000
  have hcost : intervalCost ≤ 100000000 * d2 := by
    exact proposition63_literal_interval_cost_le hdelta hDelta
      hdeltaDelta hDeltaSmall
  have hmassSq : (A * F * d2) ^ 2 ≤ input.selectedFiber.mass ^ 2 :=
    pow_le_pow_left' hmass 2
  have hfixedZero : fixed ≠ 0 := by norm_num [fixed]
  have hfixedTop : fixed ≠ ⊤ := by norm_num [fixed]
  calc
    (input.fiberFamily.family.card : ENNReal) *
          (proposition63FirstChartTerminalDensity Delta outputLoss *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) =
        input.fiberFamily.family.enncard *
          ((fixed⁻¹ * A ^ 2) * input.fiberFamily.family.enncard * d2) *
            intervalCost := by
      simp only [Kakeya.Streamlined.TubeFamily.enncard]
      rfl
    _ ≤ (2 * F) * ((fixed⁻¹ * A ^ 2) * (2 * F) * d2) *
          (100000000 * d2) := by gcongr
    _ = (A * F * d2) ^ 2 := by
      have hcancel : fixed⁻¹ * fixed = (1 : ENNReal) :=
        ENNReal.inv_mul_cancel hfixedZero hfixedTop
      calc
        (2 * F) * ((fixed⁻¹ * A ^ 2) * (2 * F) * d2) *
              (100000000 * d2) =
            (F ^ 2 * A ^ 2 * d2 ^ 2) * (fixed⁻¹ * fixed) := by
          norm_num [fixed]
          ring
        _ = F ^ 2 * A ^ 2 * d2 ^ 2 := by rw [hcancel, mul_one]
        _ = (A * F * d2) ^ 2 := by ring
    _ ≤ input.selectedFiber.mass ^ 2 := hmassSq

/-- Quotient form of the terminal-density estimate. -/
theorem proposition63FirstChartTerminalDensity_le_canonical
    {delta Delta sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily Delta}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hDelta : 0 < Delta}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hDelta)
    (outputLoss : ℝ) (fiberFloor : ℕ)
    (fiberFloor_pos : 0 < fiberFloor)
    (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hmass :
      Kakeya.realRpowENN Delta outputLoss *
            (fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 ≤
        input.selectedFiber.mass)
    (hcard : input.fiberFamily.family.enncard ≤
      2 * (fiberFloor : ENNReal)) :
    proposition63FirstChartTerminalDensity Delta outputLoss ≤
      proposition63CanonicalSliceDensity (Delta := Delta) input := by
  let denominator : ENNReal :=
    (input.fiberFamily.family.card : ENNReal) *
      input.fiberFamily.family.enncard *
      Kakeya.realRpowENN delta 2 *
      ((Fintype.card (commonSliceIntervalType
          (proposition63LiteralSliceWidth Delta)) : ENNReal) *
        commonSliceSingleTubeBound delta Delta)
  have hmassPos : 0 < input.selectedFiber.mass := by
    have hAPos : 0 < Kakeya.realRpowENN Delta outputLoss := by
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hDelta _)
    have hFPos : 0 < (fiberFloor : ENNReal) := by
      exact_mod_cast fiberFloor_pos
    have hd2Pos : 0 < Kakeya.realRpowENN delta 2 := by
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have hleftPos : 0 <
        Kakeya.realRpowENN Delta outputLoss *
          (fiberFloor : ENNReal) * Kakeya.realRpowENN delta 2 := by
      exact ENNReal.mul_pos
        (ENNReal.mul_pos hAPos.ne' hFPos.ne').ne' hd2Pos.ne'
    exact hleftPos.trans_le hmass
  have hdenominatorTop : denominator ≠ ⊤ := by
    dsimp only [denominator]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top (by simp) (by
          simp [Kakeya.Streamlined.TubeFamily.enncard])
      · simp [Kakeya.realRpowENN]
    · exact ENNReal.mul_ne_top (by simp) <|
        ENNReal.mul_ne_top (by norm_num) (by simp)
  unfold proposition63CanonicalSliceDensity
  apply (ENNReal.le_div_iff_mul_le
      (Or.inr (pow_ne_zero 2 hmassPos.ne'))
      (Or.inl hdenominatorTop)).2
  have haggregate := proposition63_firstChart_terminal_density_aggregate
    input outputLoss fiberFloor hDeltaSmall hdeltaDelta hmass hcard
  dsimp only [denominator]
  calc
    proposition63FirstChartTerminalDensity Delta outputLoss *
          ((input.fiberFamily.family.card : ENNReal) *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2 *
            ((Fintype.card (commonSliceIntervalType
                (proposition63LiteralSliceWidth Delta)) : ENNReal) *
              commonSliceSingleTubeBound delta Delta)) =
        (input.fiberFamily.family.card : ENNReal) *
          (proposition63FirstChartTerminalDensity Delta outputLoss *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) := by ring
    _ ≤ input.selectedFiber.mass ^ 2 := haggregate

end Kakeya.Assouad.PureWZ2
