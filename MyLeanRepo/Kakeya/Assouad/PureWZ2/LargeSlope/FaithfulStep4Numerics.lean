import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulPrismRawCover
import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Numerical absorption for the faithful Step-4 route
-/

noncomputable section

namespace Kakeya.Assouad

private lemma pureWZ2_realRpowENN_mul
    {delta first second : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta first * Kakeya.realRpowENN delta second =
      Kakeya.realRpowENN delta (first + second) := by
  simp only [Kakeya.realRpowENN]
  calc
    ENNReal.ofReal (Real.rpow delta first) *
        ENNReal.ofReal (Real.rpow delta second) =
      ENNReal.ofReal
        (Real.rpow delta first * Real.rpow delta second) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hdelta.le first)).symm
    _ = ENNReal.ofReal (Real.rpow delta (first + second)) :=
      congrArg ENNReal.ofReal (Real.rpow_add hdelta first second).symm

private lemma pureWZ2_realRpowENN_sqrt
    {delta : ℝ} (hdelta : 0 < delta) :
    ENNReal.ofReal (Real.sqrt delta) =
      Kakeya.realRpowENN delta (1 / 2 : ℝ) := by
  simp [Kakeya.realRpowENN, Real.sqrt_eq_rpow]

/-- The single small positive power used by the faithful card, AD, and mass
budgets. -/
theorem pureWZ2_faithfulStep4_delta_exists
    {eta loss : ℝ} (hgap : 5 * loss < 12 * eta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        Real.rpow delta (12 * eta - 5 * loss) ≤ 1 / 100000 := by
  exact exists_delta_rpow_le_single (12 * eta - 5 * loss)
    (1 / 100000) (by linarith) (by norm_num) (by norm_num)

/-- A very small `delta^(12 eta - 5 loss)` pays for the projected-normal
thickening constant. -/
theorem pureWZ2_faithful_whole_ad_constant
    {delta eta loss : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : 0 ≤ loss)
    (hsmall : Real.rpow delta (12 * eta - 5 * loss) ≤ 1 / 100000) :
    (4356 : ENNReal) * (20 * Kakeya.realRpowENN delta (-loss)) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) := by
  have hexp : 12 * eta - 5 * loss ≤ 12 * eta - loss := by linarith
  have hpower : Real.rpow delta (12 * eta - loss) ≤ 1 / 100000 :=
    (Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexp).trans hsmall
  have hreal : 87120 * Real.rpow delta (12 * eta - loss) ≤ 1 := by
    linarith
  simp only [Kakeya.realRpowENN]
  have hleft :
      (4356 : ENNReal) * (20 * ENNReal.ofReal (Real.rpow delta (-loss))) =
        ENNReal.ofReal (87120 * Real.rpow delta (-loss)) := by
    calc
      (4356 : ENNReal) * (20 * ENNReal.ofReal
          (Real.rpow delta (-loss))) =
          87120 * ENNReal.ofReal (Real.rpow delta (-loss)) := by ring
      _ = ENNReal.ofReal (87120 * Real.rpow delta (-loss)) := by
        rw [show (87120 : ENNReal) = ENNReal.ofReal (87120 : ℝ) by
          norm_num]
        exact (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 87120)).symm
  rw [hleft]
  apply ENNReal.ofReal_mono
  have hpowPos : 0 < Real.rpow delta (12 * eta) :=
    Real.rpow_pos_of_pos hdelta _
  have hneg : Real.rpow delta (-(12 * eta)) =
      (Real.rpow delta (12 * eta))⁻¹ := Real.rpow_neg hdelta.le _
  rw [hneg]
  have hmul :
    87120 * Real.rpow delta (-loss) * Real.rpow delta (12 * eta) =
        87120 * Real.rpow delta (12 * eta - loss) := by
    calc
      87120 * Real.rpow delta (-loss) * Real.rpow delta (12 * eta) =
          87120 * (Real.rpow delta (-loss) *
            Real.rpow delta (12 * eta)) := by ring
      _ = 87120 * Real.rpow delta ((-loss) + 12 * eta) := by
        exact congrArg (fun value : ℝ => 87120 * value)
          (Real.rpow_add hdelta (-loss) (12 * eta)).symm
      _ = 87120 * Real.rpow delta (12 * eta - loss) := by
        congr 2 <;> ring
  have hmulLe :
      87120 * Real.rpow delta (-loss) * Real.rpow delta (12 * eta) ≤ 1 := by
    rw [hmul]
    exact hreal
  calc
    87120 * Real.rpow delta (-loss) =
        (87120 * Real.rpow delta (-loss) *
          Real.rpow delta (12 * eta)) /
            Real.rpow delta (12 * eta) := by
      field_simp [hpowPos.ne']
    _ ≤ 1 / Real.rpow delta (12 * eta) := by gcongr
    _ = (Real.rpow delta (12 * eta))⁻¹ := by ring

/-- Four copies of the heavy-piece threshold fit below the card-proportional
mass retained by the weighted common-y refinement. -/
theorem pureWZ2_faithful_pruning_budget
    {delta eta badYLoss slabLoss scale rho : ℝ}
    (hdelta : 0 < delta) (hscalePos : 0 < scale)
    (hsqrtRho : Real.sqrt rho = 8 * scale)
    (hsmall : Real.rpow delta
      (12 * eta - 4 * badYLoss - slabLoss) ≤ 1 / 100000) :
    (4 : ENNReal) * ENNReal.ofReal
        (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) ≤
      (1 / 4 : ENNReal) * Kakeya.realRpowENN delta (4 * badYLoss) *
        (ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (slabLoss + 2) * ENNReal.ofReal scale) := by
  have hgapPos : 0 < Real.rpow delta
      (12 * eta - 4 * badYLoss - slabLoss) :=
    Real.rpow_pos_of_pos hdelta _
  have hcoeff :
      1152 * Real.rpow delta
        (12 * eta - 4 * badYLoss - slabLoss) ≤ Real.pi / 16 := by
    have hleft :
        1152 * Real.rpow delta
          (12 * eta - 4 * badYLoss - slabLoss) ≤
          1152 / 100000 := by nlinarith
    have hconstant : (1152 / 100000 : ℝ) < 3 / 16 := by norm_num
    nlinarith [Real.pi_gt_three]
  have hpowLeft : Real.rpow delta (12 * eta) * delta ^ 2 =
      Real.rpow delta (12 * eta + 2) := by
    rw [show delta ^ 2 = Real.rpow delta 2 by
      exact (Real.rpow_two delta).symm]
    exact (Real.rpow_add hdelta _ _).symm
  have hpowRight : Real.rpow delta (4 * badYLoss) *
      Real.rpow delta (slabLoss + 2) =
        Real.rpow delta (4 * badYLoss + slabLoss + 2) := by
    calc
      Real.rpow delta (4 * badYLoss) *
          Real.rpow delta (slabLoss + 2) =
          Real.rpow delta ((4 * badYLoss) + (slabLoss + 2)) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (4 * badYLoss + slabLoss + 2) := by
        congr 1 <;> ring
  have hfactor : Real.rpow delta (12 * eta + 2) =
      Real.rpow delta (12 * eta - 4 * badYLoss - slabLoss) *
        Real.rpow delta (4 * badYLoss + slabLoss + 2) := by
    calc
      Real.rpow delta (12 * eta + 2) =
          Real.rpow delta ((12 * eta - 4 * badYLoss - slabLoss) +
            (4 * badYLoss + slabLoss + 2)) := by congr 1 <;> ring
      _ = Real.rpow delta (12 * eta - 4 * badYLoss - slabLoss) *
          Real.rpow delta (4 * badYLoss + slabLoss + 2) :=
        Real.rpow_add hdelta _ _
  have hreal :
      4 * (36 * Real.rpow delta (12 * eta) * delta ^ 2 *
        Real.sqrt rho) ≤
      (1 / 4 : ℝ) * Real.rpow delta (4 * badYLoss) *
        ((Real.pi / 4) * Real.rpow delta (slabLoss + 2) * scale) := by
    rw [hsqrtRho]
    have hfactorNonneg :
        0 ≤ Real.rpow delta (4 * badYLoss + slabLoss + 2) * scale :=
      mul_nonneg (Real.rpow_nonneg hdelta.le _) hscalePos.le
    calc
      4 * (36 * Real.rpow delta (12 * eta) * delta ^ 2 *
          (8 * scale)) =
        1152 * (Real.rpow delta (12 * eta) * delta ^ 2) * scale := by
          ring
      _ = 1152 * Real.rpow delta (12 * eta + 2) * scale := by
        rw [hpowLeft]
      _ = 1152 *
          (Real.rpow delta (12 * eta - 4 * badYLoss - slabLoss) *
            Real.rpow delta (4 * badYLoss + slabLoss + 2)) * scale := by
        rw [hfactor]
      _ =
        (1152 * Real.rpow delta
          (12 * eta - 4 * badYLoss - slabLoss)) *
          (Real.rpow delta (4 * badYLoss + slabLoss + 2) * scale) := by ring
      _ ≤ (Real.pi / 16) *
          (Real.rpow delta (4 * badYLoss + slabLoss + 2) * scale) :=
        mul_le_mul_of_nonneg_right hcoeff hfactorNonneg
      _ = (1 / 4 : ℝ) *
          ((Real.pi / 4) *
            (Real.rpow delta (4 * badYLoss + slabLoss + 2) * scale)) := by ring
      _ = (1 / 4 : ℝ) * Real.rpow delta (4 * badYLoss) *
          ((Real.pi / 4) * Real.rpow delta (slabLoss + 2) * scale) := by
        rw [← hpowRight]
        ring
  let leftReal :=
    4 * (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho)
  let rightReal :=
    (1 / 4 : ℝ) * Real.rpow delta (4 * badYLoss) *
      ((Real.pi / 4) * Real.rpow delta (slabLoss + 2) * scale)
  have hleft :
      (4 : ENNReal) * ENNReal.ofReal
        (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) =
      ENNReal.ofReal leftReal := by
    calc
      (4 : ENNReal) * ENNReal.ofReal
          (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) =
        ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal
          (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) := by
            norm_num
      _ = ENNReal.ofReal leftReal := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hright :
      (1 / 4 : ENNReal) * Kakeya.realRpowENN delta (4 * badYLoss) *
        (ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (slabLoss + 2) * ENNReal.ofReal scale) =
      ENNReal.ofReal rightReal := by
    simp only [Kakeya.realRpowENN]
    have hquarter : (1 / 4 : ENNReal) =
        ENNReal.ofReal (1 / 4 : ℝ) := by
      have hfour : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by norm_num
      calc
        (1 / 4 : ENNReal) = (4 : ENNReal)⁻¹ := by rw [one_div]
        _ = (ENNReal.ofReal (4 : ℝ))⁻¹ := by rw [hfour]
        _ = ENNReal.ofReal ((4 : ℝ)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)).symm
        _ = ENNReal.ofReal (1 / 4 : ℝ) := by congr 1 <;> norm_num
    rw [hquarter]
    have hq : 0 ≤ (1 / 4 : ℝ) := by norm_num
    have hA : 0 ≤ Real.rpow delta (4 * badYLoss) :=
      Real.rpow_nonneg hdelta.le _
    have hB : 0 ≤ Real.pi / 4 := by positivity
    have hC : 0 ≤ Real.rpow delta (slabLoss + 2) :=
      Real.rpow_nonneg hdelta.le _
    have hD : 0 ≤ scale := hscalePos.le
    calc
      ENNReal.ofReal (1 / 4 : ℝ) *
          ENNReal.ofReal (Real.rpow delta (4 * badYLoss)) *
          (ENNReal.ofReal (Real.pi / 4) *
            ENNReal.ofReal (Real.rpow delta (slabLoss + 2)) *
              ENNReal.ofReal scale) =
        (ENNReal.ofReal (1 / 4 : ℝ) *
          ENNReal.ofReal (Real.rpow delta (4 * badYLoss))) *
          ((ENNReal.ofReal (Real.pi / 4) *
            ENNReal.ofReal (Real.rpow delta (slabLoss + 2))) *
              ENNReal.ofReal scale) := by ring
      _ = ENNReal.ofReal
          ((1 / 4 : ℝ) * Real.rpow delta (4 * badYLoss)) *
        (ENNReal.ofReal
          ((Real.pi / 4) * Real.rpow delta (slabLoss + 2)) *
            ENNReal.ofReal scale) := by
        rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_mul hB]
      _ = ENNReal.ofReal
          ((1 / 4 : ℝ) * Real.rpow delta (4 * badYLoss)) *
        ENNReal.ofReal
          (((Real.pi / 4) * Real.rpow delta (slabLoss + 2)) * scale) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hB hC)]
      _ = ENNReal.ofReal
          (((1 / 4 : ℝ) * Real.rpow delta (4 * badYLoss)) *
            (((Real.pi / 4) * Real.rpow delta (slabLoss + 2)) * scale)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hq hA)]
      _ = ENNReal.ofReal rightReal := by
        congr 1
  rw [hleft, hright]
  exact ENNReal.ofReal_mono hreal

/-- The fixed-frame `x'` projection of each raw prism piece has a trivial AD
constant `10/rho`; at the power scale this is absorbed directly into the
Step-4 target constant. -/
theorem pureWZ2_faithful_fixed_frame_ad_constant
    {delta rho eta : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hbound : 10 / rho ≤ Real.rpow delta (-(12 * eta))) :
    ENNReal.ofReal (10 / rho) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) := by
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono hbound

/-- Raw faithful prism count, after the common-y Markov estimate and the
spatial-cover bound. -/
theorem PureWZ2FaithfulRawPrismCover.prism_card_upper
    {sigma grainLoss slabLoss delta rho eta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta}
    {scale : WZ2PaperRequestedScale delta}
    {scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale}
    {popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData}
    {frameSlope : ℝ}
    {common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope}
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hrho : rho = 64 * scale.1 ^ 2)
    (hsmall : Real.rpow delta
      (12 * eta - 4 * common.badYLoss - slabLoss) ≤ 1 / 100000) :
    (raw.prismCount : ENNReal) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2) := by
  have hdelta := cfg.extremal.delta_pos
  have hdeltaOne := cfg.extremal.delta_le_one
  have hactive := common.cover_count common.y0 common.y0_mem
  have hcover := common.cover_card
  have hraw : (raw.prismCount : ENNReal) ≤
      4 * (Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
        ENNReal.ofReal scale.1 *
        (Kakeya.realRpowENN delta (-slabLoss) *
          Kakeya.realRpowENN scale.1 (-2 + sigma))) := by
    calc
      (raw.prismCount : ENNReal) ≤
          4 * (common.rotatedCoverCenters.filter fun center =>
            |center 1 - common.y0| ≤ scale.1).card := raw.prism_card_raw
      _ ≤ 4 * (Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
          ENNReal.ofReal scale.1 *
          (common.rotatedCoverCenters.card : ENNReal)) := by gcongr
      _ ≤ 4 * (Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
          ENNReal.ofReal scale.1 *
          (Kakeya.realRpowENN delta (-slabLoss) *
            Kakeya.realRpowENN scale.1 (-2 + sigma))) := by gcongr
  have hrawSimplified : (raw.prismCount : ENNReal) ≤
      4 * Kakeya.realRpowENN delta
          (-(4 * common.badYLoss + slabLoss)) *
        Kakeya.realRpowENN scale.1 (-1 + sigma) := by
    calc
      (raw.prismCount : ENNReal) ≤
          4 * (Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
            ENNReal.ofReal scale.1 *
            (Kakeya.realRpowENN delta (-slabLoss) *
              Kakeya.realRpowENN scale.1 (-2 + sigma))) := hraw
      _ = 4 * Kakeya.realRpowENN delta
          (-(4 * common.badYLoss + slabLoss)) *
          Kakeya.realRpowENN scale.1 (-1 + sigma) := by
        have hscalePos : 0 < scale.1 :=
          cfg.extremal.delta_pos.trans_le scale.2.1
        have hscaleENN : ENNReal.ofReal scale.1 =
            Kakeya.realRpowENN scale.1 1 := by
          simp [Kakeya.realRpowENN, Real.rpow_one]
        have hlossMul :
            Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
              Kakeya.realRpowENN delta (-slabLoss) =
            Kakeya.realRpowENN delta
              (-(4 * common.badYLoss + slabLoss)) := by
          rw [pureWZ2_realRpowENN_mul hdelta]
          congr 1 <;> ring
        have hscaleMul : Kakeya.realRpowENN scale.1 1 *
            Kakeya.realRpowENN scale.1 (-2 + sigma) =
              Kakeya.realRpowENN scale.1 (-1 + sigma) := by
          rw [pureWZ2_realRpowENN_mul hscalePos]
          congr 1 <;> ring
        calc
          4 * (Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
              ENNReal.ofReal scale.1 *
              (Kakeya.realRpowENN delta (-slabLoss) *
                Kakeya.realRpowENN scale.1 (-2 + sigma))) =
            4 * ((Kakeya.realRpowENN delta (-(4 * common.badYLoss)) *
                Kakeya.realRpowENN delta (-slabLoss)) *
              (Kakeya.realRpowENN scale.1 1 *
                Kakeya.realRpowENN scale.1 (-2 + sigma))) := by
                  rw [hscaleENN]
                  ring
          _ = 4 * (Kakeya.realRpowENN delta
                (-(4 * common.badYLoss + slabLoss)) *
              Kakeya.realRpowENN scale.1 (-1 + sigma)) := by
            rw [hlossMul, hscaleMul]
          _ = 4 * Kakeya.realRpowENN delta
              (-(4 * common.badYLoss + slabLoss)) *
              Kakeya.realRpowENN scale.1 (-1 + sigma) := by ring
  have hconstantReal :
      4 * Real.rpow delta
        (12 * eta - 4 * common.badYLoss - slabLoss) ≤
        Real.rpow 64 ((-1 + sigma) / 2) := by
    have hleft : 4 * Real.rpow delta
        (12 * eta - 4 * common.badYLoss - slabLoss) ≤
        4 / 100000 := by linarith
    have h64 : (1 / 8 : ℝ) ≤ Real.rpow 64 ((-1 + sigma) / 2) := by
      have hexp : (-1 / 2 : ℝ) ≤ (-1 + sigma) / 2 := by linarith
      calc
        (1 / 8 : ℝ) = Real.rpow 64 (-1 / 2 : ℝ) := by norm_num
        _ ≤ Real.rpow 64 ((-1 + sigma) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    linarith
  have hconstantENN :
      (4 : ENNReal) * Kakeya.realRpowENN delta
          (-(4 * common.badYLoss + slabLoss)) ≤
        Kakeya.realRpowENN delta (-(12 * eta)) *
          Kakeya.realRpowENN 64 ((-1 + sigma) / 2) := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        4 * Real.rpow delta (-(4 * common.badYLoss + slabLoss)) ≤
          Real.rpow delta (-(12 * eta)) *
            Real.rpow 64 ((-1 + sigma) / 2) := by
      have hp : 0 < Real.rpow delta (12 * eta) :=
        Real.rpow_pos_of_pos hdelta _
      have hfivePos : 0 < Real.rpow delta
          (4 * common.badYLoss + slabLoss) :=
        Real.rpow_pos_of_pos hdelta _
      have hnegFive : Real.rpow delta
          (-(4 * common.badYLoss + slabLoss)) =
          (Real.rpow delta (4 * common.badYLoss + slabLoss))⁻¹ :=
        Real.rpow_neg hdelta.le (4 * common.badYLoss + slabLoss)
      have hnegTwelve : Real.rpow delta (-(12 * eta)) =
          (Real.rpow delta (12 * eta))⁻¹ :=
        Real.rpow_neg hdelta.le (12 * eta)
      rw [hnegFive, hnegTwelve]
      have hmul : 4 * (Real.rpow delta
          (4 * common.badYLoss + slabLoss))⁻¹ *
          Real.rpow delta (12 * eta) =
          4 * Real.rpow delta
            (12 * eta - 4 * common.badYLoss - slabLoss) := by
        have hsub := Real.rpow_sub hdelta (12 * eta)
          (4 * common.badYLoss + slabLoss)
        calc
          4 * (Real.rpow delta (4 * common.badYLoss + slabLoss))⁻¹ *
              Real.rpow delta (12 * eta) =
            4 * (Real.rpow delta (12 * eta) /
              Real.rpow delta (4 * common.badYLoss + slabLoss)) := by
                field_simp [hfivePos.ne']
          _ = 4 * Real.rpow delta
              (12 * eta - 4 * common.badYLoss - slabLoss) := by
            rw [show 12 * eta - 4 * common.badYLoss - slabLoss =
              12 * eta - (4 * common.badYLoss + slabLoss) by ring]
            exact congrArg (fun value : ℝ => 4 * value) hsub.symm
      calc
        4 * (Real.rpow delta (4 * common.badYLoss + slabLoss))⁻¹ =
            (4 * (Real.rpow delta
              (4 * common.badYLoss + slabLoss))⁻¹ *
              Real.rpow delta (12 * eta)) /
                Real.rpow delta (12 * eta) := by
          field_simp [hp.ne']
        _ ≤ Real.rpow 64 ((-1 + sigma) / 2) /
              Real.rpow delta (12 * eta) := by
          gcongr
          rw [hmul]
          exact hconstantReal
        _ = (Real.rpow delta (12 * eta))⁻¹ *
              Real.rpow 64 ((-1 + sigma) / 2) := by ring
    have hleft : (4 : ENNReal) *
        ENNReal.ofReal (Real.rpow delta
          (-(4 * common.badYLoss + slabLoss))) =
        ENNReal.ofReal (4 * Real.rpow delta
          (-(4 * common.badYLoss + slabLoss))) := by
      rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num]
      exact (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)).symm
    have hright : ENNReal.ofReal (Real.rpow delta (-(12 * eta))) *
        ENNReal.ofReal (Real.rpow 64 ((-1 + sigma) / 2)) =
        ENNReal.ofReal (Real.rpow delta (-(12 * eta)) *
          Real.rpow 64 ((-1 + sigma) / 2)) :=
      (ENNReal.ofReal_mul
        (Real.rpow_nonneg hdelta.le (-(12 * eta)))).symm
    rw [hleft, hright]
    exact ENNReal.ofReal_mono hreal
  have hrhoPower : Kakeya.realRpowENN rho ((-1 + sigma) / 2) =
      Kakeya.realRpowENN 64 ((-1 + sigma) / 2) *
        Kakeya.realRpowENN scale.1 (-1 + sigma) := by
    have hscalePos : 0 < scale.1 :=
      cfg.extremal.delta_pos.trans_le scale.2.1
    simp only [Kakeya.realRpowENN]
    have hreal : Real.rpow rho ((-1 + sigma) / 2) =
        Real.rpow 64 ((-1 + sigma) / 2) *
          Real.rpow scale.1 (-1 + sigma) := by
      rw [hrho]
      calc
        Real.rpow (64 * scale.1 ^ 2) ((-1 + sigma) / 2) =
            Real.rpow 64 ((-1 + sigma) / 2) *
              Real.rpow (scale.1 ^ 2) ((-1 + sigma) / 2) :=
          Real.mul_rpow (by norm_num) (sq_nonneg scale.1)
        _ = Real.rpow 64 ((-1 + sigma) / 2) *
              Real.rpow scale.1 (2 * ((-1 + sigma) / 2)) := by
          congr 1
          rw [show scale.1 ^ 2 = Real.rpow scale.1 2 by
            exact (Real.rpow_two scale.1).symm]
          exact (Real.rpow_mul hscalePos.le 2 ((-1 + sigma) / 2)).symm
        _ = Real.rpow 64 ((-1 + sigma) / 2) *
              Real.rpow scale.1 (-1 + sigma) := by congr 1 <;> ring
    rw [hreal]
    exact ENNReal.ofReal_mul
      (Real.rpow_nonneg (by norm_num) ((-1 + sigma) / 2))
  calc
    (raw.prismCount : ENNReal) ≤
        4 * Kakeya.realRpowENN delta
            (-(4 * common.badYLoss + slabLoss)) *
          Kakeya.realRpowENN scale.1 (-1 + sigma) := hrawSimplified
    _ ≤ (Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN 64 ((-1 + sigma) / 2)) *
          Kakeya.realRpowENN scale.1 (-1 + sigma) := by gcongr
    _ = Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2) := by rw [hrhoPower]; ring

end Kakeya.Assouad

end
