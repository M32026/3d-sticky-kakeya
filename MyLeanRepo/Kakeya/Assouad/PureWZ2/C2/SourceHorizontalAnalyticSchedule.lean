import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalOuterScale
import MyLeanRepo.Kakeya.Assouad.WZ1.AsymptoticHelpers

/-!
# Uniform analytic costs for the source-horizontal pipeline

Every dependent local pipeline uses a subset of the same radius-two spatial
grid.  This file bounds that grid polynomially and absorbs the resulting
height-popularity logarithm into an arbitrary positive graph-scale loss.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Any fixed paper polylogarithmic refinement loss dominates an arbitrarily
small positive power at sufficiently small scale. -/
theorem pureWZ2_refinementFraction_power_schedule
    (logExponent : ℕ) {powerLoss : ℝ} (hpowerLoss : 0 < powerLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        Kakeya.realRpowENN rho powerLoss ≤
          wz2PaperPureRefinementFraction rho logExponent := by
  by_cases hzero : logExponent = 0
  · subst logExponent
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro rho hrho hrhoOne
    simp only [wz2PaperPureRefinementFraction, pow_zero]
    exact ENNReal.ofReal_le_one.mpr
      (Real.rpow_le_one hrho.le hrhoOne hpowerLoss.le)
  · have hexponent : 0 < logExponent := Nat.pos_of_ne_zero hzero
    rcases exists_delta_log_absorbed_ennreal
        1 (by norm_num) hpowerLoss hexponent with
      ⟨rho₀, hrho₀, hrho₀One, habsorb⟩
    refine ⟨rho₀, hrho₀, hrho₀One, ?_⟩
    intro rho hrho hrhoSmall
    have hrhoOne : rho ≤ 1 := hrhoSmall.trans hrho₀One
    let power : ENNReal := Kakeya.realRpowENN rho powerLoss
    let logarithm : ENNReal := ENNReal.ofReal (Real.log (1 / rho))
    have hlogNonneg : 0 ≤ Real.log (1 / rho) := by
      apply Real.log_nonneg
      exact one_le_one_div hrho hrhoOne
    have hlogLe : logarithm ≤
        ENNReal.ofReal (1 + Real.log rho⁻¹) := by
      apply ENNReal.ofReal_mono
      simpa [one_div] using (show Real.log (1 / rho) ≤
        1 + Real.log (1 / rho) by linarith)
    have hlogPow : logarithm ^ logExponent ≤ power⁻¹ := by
      calc
        logarithm ^ logExponent ≤
            (ENNReal.ofReal (1 + Real.log rho⁻¹)) ^ logExponent := by
          gcongr
        _ ≤ Kakeya.realRpowENN rho (-powerLoss) := by
          simpa using habsorb rho hrho hrhoSmall
        _ = power⁻¹ := by
          dsimp only [power, Kakeya.realRpowENN]
          have hneg : Real.rpow rho (-powerLoss) =
              (Real.rpow rho powerLoss)⁻¹ :=
            Real.rpow_neg hrho.le powerLoss
          rw [hneg]
          exact ENNReal.ofReal_inv_of_pos
            (Real.rpow_pos_of_pos hrho powerLoss)
    have hpowerZero : power ≠ 0 := by
      dsimp only [power, Kakeya.realRpowENN]
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (Real.rpow_pos_of_pos hrho powerLoss)
    have hpowerTop : power ≠ ⊤ := by
      dsimp only [power, Kakeya.realRpowENN]
      exact ENNReal.ofReal_ne_top
    have hinv := ENNReal.inv_le_inv.mpr hlogPow
    have hdouble : power⁻¹⁻¹ = power := by
      rw [inv_inv]
    rw [hdouble] at hinv
    simpa [wz2PaperPureRefinementFraction, logarithm, one_div,
      ENNReal.inv_pow] using hinv

private lemma sourceHorizontal_natLog_le_realLog
    {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have h := Real.natLog_le_logb n 2
  simpa [Real.logb] using h

/-- The radius-two Lemma-23 grid has the expected cubic cardinality.  The
large absolute constant keeps the statement independent of floor/ceiling
endpoint conventions. -/
theorem wz1Lemma23BoundedCells_card_real_le
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    ((wz1Lemma23BoundedCells rho hrho).card : ℝ) ≤
      (16 / rho) ^ 3 := by
  let s : ℝ := gridSide (rho / 2)
  let b : ℤ := ⌈(2 : ℝ) / s⌉ + 1
  let interval : Finset ℤ := Finset.Icc (-b) b
  have hs : s = rho / Real.sqrt 3 := by
    simp [s, gridSide]
    ring
  have hsPos : 0 < s := by
    rw [hs]
    positivity
  have hquotientPos : 0 < (2 : ℝ) / s := by positivity
  have hbPos : 0 < b := by
    dsimp only [b]
    have hceil : 0 ≤ ⌈(2 : ℝ) / s⌉ := Int.ceil_nonneg hquotientPos.le
    omega
  have hintervalCardInt : (interval.card : ℤ) = 2 * b + 1 := by
    dsimp only [interval]
    rw [Int.card_Icc_of_le (-b) b (by omega)]
    ring
  have hceilUpper : (⌈(2 : ℝ) / s⌉ : ℝ) < 2 / s + 1 :=
    Int.ceil_lt_add_one _
  have hsqrtThree : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hbUpper : (b : ℝ) < 6 / rho := by
    have htwo : 2 ≤ 2 / rho := by
      exact (le_div_iff₀ hrho).2 (by nlinarith)
    have hquotient : 2 / (rho / Real.sqrt 3) =
        2 * Real.sqrt 3 / rho := by
      field_simp [hrho.ne', (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne']
    have hquotientUpper : 2 / s < 4 / rho := by
      rw [hs, hquotient]
      exact div_lt_div_of_pos_right (by nlinarith) hrho
    have hbCast : (b : ℝ) = (⌈(2 : ℝ) / s⌉ : ℝ) + 1 := by
      simp [b]
    have hconstant : 4 / rho + 2 ≤ 6 / rho := by
      rw [le_div_iff₀ hrho]
      field_simp [hrho.ne']
      nlinarith
    calc
      (b : ℝ) = (⌈(2 : ℝ) / s⌉ : ℝ) + 1 := hbCast
      _ < 2 / s + 2 := by linarith
      _ < 4 / rho + 2 := by linarith
      _ ≤ 6 / rho := hconstant
  have hintervalCard : (interval.card : ℝ) ≤ 16 / rho := by
    have hcast : (interval.card : ℝ) = 2 * (b : ℝ) + 1 := by
      exact_mod_cast hintervalCardInt
    rw [hcast]
    have hone : 1 ≤ 4 / rho := (le_div_iff₀ hrho).2 (by nlinarith)
    apply le_of_lt
    calc
      2 * (b : ℝ) + 1 < 2 * (6 / rho) + 1 := by linarith
      _ ≤ 2 * (6 / rho) + 4 / rho := by linarith
      _ = 16 / rho := by ring
  have hcardEq :
      (wz1Lemma23BoundedCells rho hrho).card = interval.card ^ 3 := by
    change (interval.product (interval.product interval)).card = interval.card ^ 3
    calc
      (interval.product (interval.product interval)).card =
          interval.card * (interval.product interval).card :=
        Finset.card_product interval (interval.product interval)
      _ = interval.card * (interval.card * interval.card) := by
        have hinner := Finset.card_product interval interval
        exact congrArg (fun value : ℕ => interval.card * value) hinner
      _ = interval.card ^ 3 := by ring
  rw [hcardEq]
  rw [Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity) hintervalCard 3

/-- The grid popularity logarithm is at most a fixed multiple of
`1 + log(1/rho)`. -/
theorem wz1Lemma23BoundedCells_log_bound
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    (Nat.log 2 (wz1Lemma23BoundedCells rho hrho).card + 1 : ℝ) ≤
      20 * (Real.log (1 / rho) + 1) := by
  let cells := wz1Lemma23BoundedCells rho hrho
  have hcellsNonempty : 0 < cells.card := by
    unfold cells wz1Lemma23BoundedCells gridIndicesInRadius
    apply Finset.card_pos.mpr
    let zero : ℤ := 0
    refine ⟨(zero, zero, zero), ?_⟩
    have hscale : 0 < gridSide (rho / 2) := by
      simp [gridSide]
      positivity
    have hceil : 0 ≤ ⌈(2 : ℝ) / gridSide (rho / 2)⌉ := by
      apply Int.ceil_nonneg
      exact div_nonneg (by norm_num) hscale.le
    apply Finset.mem_product.mpr
    constructor
    · change zero ∈ Finset.Icc _ _
      exact Finset.mem_Icc.mpr ⟨by dsimp only [zero]; omega, by dsimp only [zero]; omega⟩
    · apply Finset.mem_product.mpr
      constructor <;> change zero ∈ Finset.Icc _ _
      · exact Finset.mem_Icc.mpr ⟨by dsimp only [zero]; omega, by dsimp only [zero]; omega⟩
      · exact Finset.mem_Icc.mpr ⟨by dsimp only [zero]; omega, by dsimp only [zero]; omega⟩
  have hcard := wz1Lemma23BoundedCells_card_real_le hrho hrhoOne
  have hrightPos : 0 < (16 / rho) ^ 3 := by positivity
  have hlogCard :
      Real.log (cells.card : ℝ) ≤ Real.log ((16 / rho) ^ 3) :=
    Real.log_le_log (by exact_mod_cast hcellsNonempty) hcard
  have hlogFormula :
      Real.log ((16 / rho) ^ 3) =
        3 * (Real.log 16 + Real.log (1 / rho)) := by
    rw [Real.log_pow]
    have hdiv : Real.log (16 / rho) = Real.log 16 + Real.log (1 / rho) := by
      rw [Real.log_div (by norm_num) hrho.ne',
        Real.log_div (by norm_num) hrho.ne', Real.log_one]
      ring
    rw [hdiv]
    ring
  rw [hlogFormula] at hlogCard
  have hlogRho : 0 ≤ Real.log (1 / rho) := by
    apply Real.log_nonneg
    exact one_le_one_div hrho hrhoOne
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogSixteen : Real.log 16 = 4 * Real.log 2 := by
    have : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_num
  have hnatLog := sourceHorizontal_natLog_le_realLog hcellsNonempty
  dsimp only [cells] at hnatLog hlogCard ⊢
  rw [hlogSixteen] at hlogCard
  have hlogTwoLower : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hdivision :
      Real.log ((wz1Lemma23BoundedCells rho hrho).card : ℝ) / Real.log 2 ≤
        12 + 6 * Real.log (1 / rho) := by
    apply (div_le_iff₀ hlogTwo).2
    calc
      Real.log ((wz1Lemma23BoundedCells rho hrho).card : ℝ) ≤
          3 * (4 * Real.log 2 + Real.log (1 / rho)) := hlogCard
      _ ≤ (12 + 6 * Real.log (1 / rho)) * Real.log 2 := by
        nlinarith
  calc
    (Nat.log 2 (wz1Lemma23BoundedCells rho hrho).card + 1 : ℝ) ≤
        Real.log ((wz1Lemma23BoundedCells rho hrho).card : ℝ) /
            Real.log 2 + 1 := by linarith
    _ ≤ 13 + 6 * Real.log (1 / rho) := by linarith
    _ ≤ 20 * (Real.log (1 / rho) + 1) := by nlinarith

/-- The scalar quadratic-log cost at graph scale `256 * rho` is absorbed by
any prescribed positive graph-scale loss.  This statement is independent of
the family or graph data to which the estimate will later be applied. -/
theorem pureWZ2_sourceHorizontal_extraCost_scalar_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho graphScale : ℝ, 0 < rho → rho ≤ rho₀ →
        graphScale = 256 * rho →
        920 * (Real.log (1 / graphScale) + 1) ^ 2 ≤
          Real.rpow graphScale (-extraLoss) := by
  rcases log_poly_decay_general 2000 (extraLoss / 2) (by norm_num)
      (by positivity) with
    ⟨constantScale₀, hconstantScale₀, hconstantScale₀One, hgraphLog⟩
  rcases log_poly_decay_general 1 (extraLoss / 4) (by norm_num)
      (by positivity) with
    ⟨logScale₀, hlogScale₀, hlogScale₀One, hlogPower⟩
  let graphScale₀ := min constantScale₀ logScale₀
  let rho₀ := graphScale₀ / 256
  refine ⟨rho₀, by positivity, ?_, ?_⟩
  · exact (div_le_self (by positivity) (by norm_num)).trans
      ((min_le_left _ _).trans hconstantScale₀One)
  intro rho graphScale hrho hrhoSmall hgraphScale
  have hgraphPos : 0 < graphScale := by
    rw [hgraphScale]
    positivity
  have hgraphOne : graphScale ≤ 1 := by
    rw [hgraphScale]
    calc
      256 * rho ≤ 256 * rho₀ := by gcongr
      _ = graphScale₀ := by unfold rho₀; ring
      _ ≤ 1 := (min_le_left _ _).trans hconstantScale₀One
  have hgraphSmall : graphScale ≤ graphScale₀ := by
    rw [hgraphScale]
    calc
      256 * rho ≤ 256 * rho₀ := by gcongr
      _ = graphScale₀ := by unfold rho₀; ring
  let L : ℝ := Real.log (1 / graphScale) + 1
  have hLNonneg : 0 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / graphScale) := by
      apply Real.log_nonneg
      exact one_le_one_div hgraphPos hgraphOne
    linarith
  have hLsmall : L ≤ Real.rpow graphScale
      (-(extraLoss / 4)) := by
    have h := hlogPower graphScale hgraphPos
      (hgraphSmall.trans (min_le_right _ _))
    simpa [L, one_div, Real.rpow_neg hgraphPos.le] using h
  have hquadratic :
      920 * L ^ 2 ≤
        920 * Real.rpow graphScale (-(extraLoss / 2)) := by
    calc
      920 * L ^ 2 ≤
          920 * (Real.rpow graphScale (-(extraLoss / 4))) ^ 2 := by
        gcongr
      _ = 920 * Real.rpow graphScale (-(extraLoss / 2)) := by
        rw [pow_two]
        congr 1
        calc
          Real.rpow graphScale (-(extraLoss / 4)) *
              Real.rpow graphScale (-(extraLoss / 4)) =
            Real.rpow graphScale
              (-(extraLoss / 4) + -(extraLoss / 4)) :=
            (Real.rpow_add hgraphPos _ _).symm
          _ = Real.rpow graphScale (-(extraLoss / 2)) := by
            congr 1
            ring
  have habsorb := hgraphLog graphScale hgraphPos
    (hgraphSmall.trans (min_le_left _ _))
  have hconstant : 920 ≤ Real.rpow graphScale
      (-(extraLoss / 2)) := by
    have hLone : 1 ≤ Real.log (1 / graphScale) + 1 := by
      have hlogNonneg : 0 ≤ Real.log (1 / graphScale) := by
        apply Real.log_nonneg
        exact one_le_one_div hgraphPos hgraphOne
      linarith
    have : 2000 ≤ 2000 * (Real.log (1 / graphScale) + 1) := by
      nlinarith
    have h920 : (920 : ℝ) ≤ 2000 := by norm_num
    have hpower :
        2000 * (Real.log (1 / graphScale) + 1) ≤
          Real.rpow graphScale (-(extraLoss / 2)) := by
      simpa [one_div, Real.rpow_neg hgraphPos.le] using habsorb
    exact h920.trans (this.trans hpower)
  change 920 * L ^ 2 ≤ Real.rpow graphScale (-extraLoss)
  calc
    920 * L ^ 2 ≤
        920 * Real.rpow graphScale (-(extraLoss / 2)) := hquadratic
    _ ≤ Real.rpow graphScale (-(extraLoss / 2)) *
        Real.rpow graphScale (-(extraLoss / 2)) := by gcongr
    _ = Real.rpow graphScale (-extraLoss) := by
      calc
        Real.rpow graphScale (-(extraLoss / 2)) *
            Real.rpow graphScale (-(extraLoss / 2)) =
          Real.rpow graphScale
            (-(extraLoss / 2) + -(extraLoss / 2)) :=
          (Real.rpow_add hgraphPos _ _).symm
        _ = Real.rpow graphScale (-extraLoss) := by
          congr 1
          ring

/-- Uniformly absorb the popularity log of every source-horizontal pipeline
into a prescribed positive graph-scale loss. -/
theorem pureWZ2_sourceHorizontal_extraCost_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        ∀ sigma inputLoss delta middleLoss stickyLoss normalEta theoremEta : ℝ,
        ∀ logExponent : ℕ,
        ∀ source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta,
        ∀ twoScale : PureWZ2OneScaleTwoScaleStickyData
            source rho middleLoss stickyLoss logExponent,
        ∀ pipeline : PureWZ2SourceHorizontalPipelineData
            (normalEta := normalEta) twoScale,
          (pipeline.graph.residue.extraCost : ℝ) ≤
            Real.rpow pipeline.prep.graphScale (-extraLoss) := by
  rcases pureWZ2_sourceHorizontal_extraCost_scalar_schedule hextraLoss with
    ⟨scalarRho₀, hscalarRho₀, hscalarRho₀One, hscalar⟩
  let rho₀ := min scalarRho₀ (1 / 256 : ℝ)
  refine ⟨rho₀, by positivity, ?_, ?_⟩
  · exact (min_le_left _ _).trans hscalarRho₀One
  intro rho hrho hrhoSmall sigma inputLoss delta middleLoss stickyLoss
    normalEta theoremEta logExponent source twoScale pipeline
  have hgraphPos : 0 < pipeline.prep.graphScale :=
    pipeline.prep.graphScale_pos
  have hgraphOne : pipeline.prep.graphScale ≤ 1 := by
    rw [pipeline.prep.graphScale_eq]
    have hsmall : rho ≤ 1 / 256 :=
      hrhoSmall.trans (min_le_right _ _)
    nlinarith
  have hlog := wz1Lemma23BoundedCells_log_bound hgraphPos hgraphOne
  have hcellsSubset : pipeline.prep.windowed.global.cells ⊆
      wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos := by
    classical
    exact pipeline.prep.windowed.global.cells_active.trans
      (Finset.filter_subset _ _)
  have hcard : pipeline.prep.windowed.global.cells.card ≤
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card :=
    Finset.card_le_card hcellsSubset
  have hrawCard : pipeline.rawResidue.cells.card ≤
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card :=
    (Finset.card_le_card pipeline.rawResidue.cells_subset).trans hcard
  have hrawNonempty : pipeline.rawResidue.cells.Nonempty := by
    rw [pipeline.rawResidue_eq]
    exact pipeline.popularSource.cells_nonempty
  have hboundedNonempty :
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).Nonempty :=
    hrawNonempty.mono
      (pipeline.rawResidue.cells_subset.trans hcellsSubset)
  have hrawLogNat : Nat.log 2 pipeline.rawResidue.cells.card + 1 ≤
      Nat.log 2
        (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hrawCard) 1
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices
        pipeline.prep.graphScale hgraphPos).card ≤
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card :=
    Finset.card_image_le
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices
          pipeline.prep.graphScale hgraphPos).card ≤
        4 * (wz1Lemma23BoundedCells
          pipeline.prep.graphScale hgraphPos).card := by
    have hcellsPos : 0 <
        (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card := by
      exact hboundedNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2 (2 * (wz1Lemma23BoundedHeightIndices
          pipeline.prep.graphScale hgraphPos).card) ≤
        Nat.log 2 (4 * (wz1Lemma23BoundedCells
          pipeline.prep.graphScale hgraphPos).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe :
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card ≠ 0 := by
    exact hboundedNonempty.card_ne_zero
  have hfourEq : 4 *
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card =
      (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card *
        2 * 2 := by ring
  have hbinsNat : pipeline.heightPopular.bins ≤
      Nat.log 2
        (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card + 3 := by
    rw [pipeline.heightPopular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices
            pipeline.prep.graphScale hgraphPos).card) + 1 ≤
          Nat.log 2
            (4 * (wz1Lemma23BoundedCells
              pipeline.prep.graphScale hgraphPos).card) + 1 := by omega
      _ = Nat.log 2
            (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card +
          3 := by
        rw [hfourEq]
        calc
          Nat.log 2
              ((wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card *
                2 * 2) + 1 =
              Nat.log 2
                ((wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card *
                  2) + 1 + 1 := by
            rw [Nat.log_mul_base (by omega)
              (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2
                (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card +
              1 + 1 + 1 := by
            rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / pipeline.prep.graphScale) + 1
  have hLNonneg : 0 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / pipeline.prep.graphScale) := by
      apply Real.log_nonneg
      exact one_le_one_div hgraphPos hgraphOne
    linarith
  have hrawLogReal :
      (Nat.log 2 pipeline.rawResidue.cells.card + 1 : ℝ) ≤ 20 * L := by
    have hcast :
        (Nat.log 2 pipeline.rawResidue.cells.card + 1 : ℝ) ≤
          (Nat.log 2
            (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card +
            1 : ℕ) := by
      exact_mod_cast hrawLogNat
    exact hcast.trans (by simpa [L] using hlog)
  have hbinsReal : (pipeline.heightPopular.bins : ℝ) ≤ 23 * L := by
    have hnat : (pipeline.heightPopular.bins : ℝ) ≤
        (Nat.log 2
          (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card +
          3 : ℕ) := by exact_mod_cast hbinsNat
    have hone : 1 ≤ L := by
      dsimp only [L]
      have hlogNonneg : 0 ≤ Real.log (1 / pipeline.prep.graphScale) := by
        apply Real.log_nonneg
        exact one_le_one_div hgraphPos hgraphOne
      linarith
    calc
      (pipeline.heightPopular.bins : ℝ) ≤
          (Nat.log 2
            (wz1Lemma23BoundedCells pipeline.prep.graphScale hgraphPos).card +
            3 : ℕ) := hnat
      _ ≤ 20 * L + 2 := by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith [hlog]
      _ ≤ 23 * L := by nlinarith
  have hcostQuadratic :
      (pipeline.graph.residue.extraCost : ℝ) ≤ 920 * L ^ 2 := by
    rw [pipeline.extraCost_eq]
    push_cast
    nlinarith [mul_le_mul hbinsReal hrawLogReal (by positivity) (by positivity)]
  exact hcostQuadratic.trans
    (hscalar rho pipeline.prep.graphScale hrho
      (hrhoSmall.trans (min_le_left _ _)) pipeline.prep.graphScale_eq)

end Kakeya.Assouad
