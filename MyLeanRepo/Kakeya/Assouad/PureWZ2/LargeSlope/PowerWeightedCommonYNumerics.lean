import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6PowerArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedWeightedCommonYRefinement

/-!
# Power-scale weighted common-y numerics
-/

noncomputable section
namespace Kakeya.Assouad
open MeasureTheory Set Finset
attribute [local instance] Classical.propDecidable

private lemma power_weighted_threshold_budget_of_bounds
    {A C N B L M threshold : ENNReal}
    (hNZero : N ≠ 0) (hNTop : N ≠ ⊤)
    (hCZero : C ≠ 0) (hCTop : C ≠ ⊤)
    (hNB : N ≤ B)
    (hidentity : 2 * (N * threshold) = M)
    (hLM : L ≤ M)
    (hnumeric : 4 * A * C * B ≤ L) :
    A ≤ (1 / 2 : ENNReal) * (threshold / C) := by
  have hfour : 4 * A * C * N ≤ M := by
    calc
      4 * A * C * N ≤ 4 * A * C * B := by gcongr
      _ ≤ L := hnumeric
      _ ≤ M := hLM
  have hfactor : (2 * N) * (2 * (A * C)) ≤ (2 * N) * threshold := by
    rw [show (2 * N) * (2 * (A * C)) = 4 * A * C * N by ring]
    rw [show (2 * N) * threshold = 2 * (N * threshold) by ring, hidentity]
    exact hfour
  have htwoNZero : (2 * N) ≠ 0 := mul_ne_zero (by norm_num) hNZero
  have htwoNTop : (2 * N) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hNTop
  have htwoAC : 2 * (A * C) ≤ threshold :=
    (ENNReal.mul_le_mul_iff_right htwoNZero htwoNTop).mp hfactor
  have hAC : A * C ≤ (1 / 2 : ENNReal) * threshold := by
    apply (ENNReal.mul_le_mul_iff_right
      (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp
    calc
      2 * (A * C) ≤ threshold := htwoAC
      _ = 2 * ((1 / 2 : ENNReal) * threshold) := by
        have hhalf : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        rw [show 2 * ((1 / 2 : ENNReal) * threshold) =
          (2 * (1 / 2 : ENNReal)) * threshold by ring, hhalf, one_mul]
  have hdiv : A ≤ ((1 / 2 : ENNReal) * threshold) / C :=
    (ENNReal.le_div_iff_mul_le (Or.inl hCZero) (Or.inl hCTop)).mpr hAC
  rw [div_eq_mul_inv, div_eq_mul_inv] at hdiv ⊢
  simpa [mul_assoc] using hdiv

theorem weighted_commonY_numeric_base_at_power
    {sigma grainLoss slabLoss badYLoss delta W power : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hW : 0 < W) (hdeltaW : delta ≤ W)
    (hrho : W = Real.rpow delta power)
    (hsmall : Kakeya.realRpowENN delta
      (4 * badYLoss - grainLoss - 2 * slabLoss -
        power * (2 - sigma - slabLoss)) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    4 * (ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss))) *
        Kakeya.realRpowENN (delta / W) (2 - sigma - slabLoss) *
        (ENNReal.ofReal (W / delta + 2) *
          (24 * Kakeya.realRpowENN delta (-grainLoss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma))) ≤
      ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        ENNReal.ofReal (W) := by
  rw [section6_power_relative_rpow hdelta hrho]
  have hinv : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hleftTop : 4 * (ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss))) *
        Kakeya.realRpowENN delta ((1 - power) * (2 - sigma - slabLoss)) *
        (ENNReal.ofReal (W / delta + 2) *
          (24 * Kakeya.realRpowENN delta (-grainLoss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma))) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · norm_num
        · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          apply ENNReal.mul_ne_top
          · norm_num
          · simp [Kakeya.realRpowENN]
      · simp [Kakeya.realRpowENN]
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · norm_num
        · simp [Kakeya.realRpowENN]
      · simp [Kakeya.realRpowENN]
  have hrightTop : ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        ENNReal.ofReal (W) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      simp [Kakeya.realRpowENN]
    · exact ENNReal.ofReal_ne_top
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  have hrpowToReal : ∀ e : ℝ,
      (Kakeya.realRpowENN delta e).toReal = Real.rpow delta e := by
    intro e
    change (ENNReal.ofReal (Real.rpow delta e)).toReal = Real.rpow delta e
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hdelta.le e)
  have hinvRpowToReal : ∀ e : ℝ,
      (Kakeya.realRpowENN (1 / delta) e).toReal =
        Real.rpow (1 / delta) e := by
    intro e
    change (ENNReal.ofReal (Real.rpow (1 / delta) e)).toReal =
      Real.rpow (1 / delta) e
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hinv.le e)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, hrpowToReal,
    hinvRpowToReal]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 128 * delta ^ 2)]
  rw [ENNReal.toReal_ofReal
    (by positivity : 0 ≤ W / delta + 2)]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 4)]
  rw [ENNReal.toReal_ofReal (hW.le)]
  have hsmallReal : Real.rpow delta
      (4 * badYLoss - grainLoss - 2 * slabLoss -
        power * (2 - sigma - slabLoss)) ≤ (1 / 400000 : ℝ) := by
    have h := (ENNReal.toReal_le_toReal
      (by simp [Kakeya.realRpowENN] :
        Kakeya.realRpowENN delta
          (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss)) ≠ ⊤)
      ENNReal.ofReal_ne_top).2 hsmall
    change (ENNReal.ofReal (Real.rpow delta
      (4 * badYLoss - grainLoss - 2 * slabLoss -
        power * (2 - sigma - slabLoss)))).toReal ≤
      (ENNReal.ofReal (1 / 400000 : ℝ)).toReal at h
    have hleft := ENNReal.toReal_ofReal
      (Real.rpow_nonneg hdelta.le
        (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss)))
    have hright := ENNReal.toReal_ofReal
      (by norm_num : 0 ≤ (1 / 400000 : ℝ))
    change (ENNReal.ofReal
      (Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
        power * (2 - sigma - slabLoss)))).toReal =
      Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
        power * (2 - sigma - slabLoss)) at hleft
    change (ENNReal.ofReal (1 / 400000 : ℝ)).toReal =
      (1 / 400000 : ℝ) at hright
    rw [hleft, hright] at h
    exact h
  have hsqrtRatio : W / delta + 2 ≤
      3 * (W / delta) := by
    have hratio : 1 ≤ W / delta :=
      (le_div_iff₀ hdelta).2 (by simpa using hdeltaW)
    linarith
  have hone : Real.rpow (1 / delta) (1 - sigma) =
      Real.rpow delta (-(1 - sigma)) := by
    rw [one_div]
    exact (Real.inv_rpow hdelta.le (1 - sigma)).trans
      (Real.rpow_neg hdelta.le (1 - sigma)).symm
  have hpowers : Real.rpow delta (4 * badYLoss) *
        Real.rpow delta ((1 - power) * (2 - sigma - slabLoss)) *
          Real.rpow delta (-grainLoss) *
        Real.rpow (1 / delta) (1 - sigma) =
      Real.rpow delta
        (1 + slabLoss + (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss))) := by
    rw [hone]
    calc
      Real.rpow delta (4 * badYLoss) *
          Real.rpow delta ((1 - power) * (2 - sigma - slabLoss)) *
          Real.rpow delta (-grainLoss) * Real.rpow delta (-(1 - sigma)) =
        Real.rpow delta ((4 * badYLoss) +
          ((1 - power) * (2 - sigma - slabLoss)) + (-grainLoss) +
          (-(1 - sigma))) := by
          rw [show Real.rpow delta (4 * badYLoss) *
              Real.rpow delta ((1 - power) * (2 - sigma - slabLoss)) =
            Real.rpow delta
              ((4 * badYLoss) +
                ((1 - power) * (2 - sigma - slabLoss))) from
              (Real.rpow_add hdelta _ _).symm]
          rw [show Real.rpow delta
                ((4 * badYLoss) +
                  ((1 - power) * (2 - sigma - slabLoss))) *
              Real.rpow delta (-grainLoss) =
            Real.rpow delta ((4 * badYLoss) +
              ((1 - power) * (2 - sigma - slabLoss)) + (-grainLoss)) from
              (Real.rpow_add hdelta _ _).symm]
          exact (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta
          (1 + slabLoss + (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss))) := by
        congr 1
        ring
  have hpowSplit : Real.rpow delta
        (1 + slabLoss + (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss))) =
      delta * Real.rpow delta slabLoss *
        Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss)) := by
    calc
      Real.rpow delta
          (1 + slabLoss + (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss))) =
        Real.rpow delta (1 + slabLoss) *
          Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss)) :=
        Real.rpow_add hdelta _ _
      _ = (Real.rpow delta 1 * Real.rpow delta slabLoss) *
          Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss)) := by
        congr 1
        exact Real.rpow_add hdelta 1 slabLoss
      _ = _ := by simp [Real.rpow_one]
  have hpowL2 : Real.rpow delta (slabLoss + 2) =
      Real.rpow delta slabLoss * delta ^ 2 := by
    calc
      Real.rpow delta (slabLoss + 2) =
          Real.rpow delta slabLoss * Real.rpow delta 2 :=
        Real.rpow_add hdelta slabLoss 2
      _ = Real.rpow delta slabLoss * delta ^ 2 := by
        rw [show Real.rpow delta (2 : ℝ) = delta ^ 2 by
          exact Real.rpow_ofNat delta 2]
  have hpi : (294912 : ℝ) * Real.rpow delta
      (4 * badYLoss - grainLoss - 2 * slabLoss -
        power * (2 - sigma - slabLoss)) ≤ Real.pi := by
    apply le_of_lt
    calc
      (294912 : ℝ) * Real.rpow delta
          (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss)) ≤
          294912 * (1 / 400000 : ℝ) := by gcongr
      _ < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  rw [show 4 * (128 * delta ^ 2 *
      (2 * Real.rpow delta (4 * badYLoss))) *
      Real.rpow delta ((1 - power) * (2 - sigma - slabLoss)) *
      ((W / delta + 2) *
        (24 * Real.rpow delta (-grainLoss) *
          Real.rpow (1 / delta) (1 - sigma))) =
      24576 * delta ^ 2 * (W / delta + 2) *
        (Real.rpow delta (4 * badYLoss) *
          Real.rpow delta ((1 - power) * (2 - sigma - slabLoss)) *
          Real.rpow delta (-grainLoss) *
          Real.rpow (1 / delta) (1 - sigma)) by ring]
  rw [hpowers, hpowSplit, hpowL2]
  calc
    24576 * delta ^ 2 * (W / delta + 2) *
        (delta * Real.rpow delta slabLoss *
          Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss)))
      ≤ 24576 * delta ^ 2 * (3 * (W / delta)) *
        (delta * Real.rpow delta slabLoss *
          Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss))) := by
          have hfactorNonneg :
              0 ≤ delta * Real.rpow delta slabLoss *
                  Real.rpow delta
                    (4 * badYLoss - grainLoss - 2 * slabLoss -
                      power * (2 - sigma - slabLoss)) := by
            exact mul_nonneg
              (mul_nonneg hdelta.le (Real.rpow_nonneg hdelta.le slabLoss))
              (Real.rpow_nonneg hdelta.le
                (4 * badYLoss - grainLoss - 2 * slabLoss -
                  power * (2 - sigma - slabLoss)))
          have hmiddle := mul_le_mul_of_nonneg_right hsqrtRatio hfactorNonneg
          have hprefix : 0 ≤ (24576 : ℝ) * delta ^ 2 := by positivity
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hmiddle hprefix
    _ = 73728 * delta ^ 2 * W * Real.rpow delta slabLoss *
        Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss)) := by
      field_simp [hdelta.ne']
      ring
    _ ≤ (Real.pi / 4) * delta ^ 2 * W *
        Real.rpow delta slabLoss := by
      have hconstant : (73728 : ℝ) * Real.rpow delta
          (4 * badYLoss - grainLoss - 2 * slabLoss -
            power * (2 - sigma - slabLoss)) ≤
          Real.pi / 4 := by linarith
      calc
        73728 * delta ^ 2 * W * Real.rpow delta slabLoss *
            Real.rpow delta (4 * badYLoss - grainLoss - 2 * slabLoss -
              power * (2 - sigma - slabLoss)) =
          (73728 * Real.rpow delta
            (4 * badYLoss - grainLoss - 2 * slabLoss -
              power * (2 - sigma - slabLoss))) *
            (delta ^ 2 * W * Real.rpow delta slabLoss) := by ring
        _ ≤ (Real.pi / 4) *
            (delta ^ 2 * W * Real.rpow delta slabLoss) := by
              have hfactorNonneg :
                  0 ≤ delta ^ 2 * W * Real.rpow delta slabLoss :=
                mul_nonneg
                  (mul_nonneg (sq_nonneg delta) (hW.le))
                  (Real.rpow_nonneg hdelta.le slabLoss)
              exact mul_le_mul_of_nonneg_right hconstant hfactorNonneg
        _ = _ := by ring
    _ = Real.pi / 4 * (Real.rpow delta slabLoss * delta ^ 2) *
        W := by ring

/-- Common-y scalar budget using the sharp Proposition-5 fine-scale
multiplicity cap.  Full-fiber uniformity removes the old
`power * (2 - sigma)` loss; only `power * stickyLoss` remains. -/
theorem weighted_commonY_numeric_base_at_fine_power
    {sigma grainLoss slabLoss stickyLoss badYLoss delta W power : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hW : 0 < W) (hdeltaW : delta ≤ W)
    (hrho : W = Real.rpow delta power)
    (hsmall : Kakeya.realRpowENN delta
      (4 * badYLoss - grainLoss - slabLoss -
        (1 + power) * stickyLoss) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    4 * (ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss))) *
        (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN W (-stickyLoss)) *
        (ENNReal.ofReal (W / delta + 2) *
          (24 * Kakeya.realRpowENN delta (-grainLoss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma))) ≤
      ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        ENNReal.ofReal W := by
  have hinv : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hleftTop : 4 * (ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss))) *
        (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN W (-stickyLoss)) *
        (ENNReal.ofReal (W / delta + 2) *
          (24 * Kakeya.realRpowENN delta (-grainLoss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma))) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · norm_num
        · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          exact ENNReal.mul_ne_top (by norm_num)
            (by simp [Kakeya.realRpowENN])
      · exact ENNReal.mul_ne_top
          (by simp [Kakeya.realRpowENN])
          (by simp [Kakeya.realRpowENN])
    · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.realRpowENN])
  have hrightTop : ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        ENNReal.ofReal W ≠ ⊤ := by
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  rw [← ENNReal.toReal_le_toReal hleftTop hrightTop]
  have hdeltaRpow : ∀ exponent : ℝ,
      (Kakeya.realRpowENN delta exponent).toReal =
        Real.rpow delta exponent := by
    intro exponent
    exact ENNReal.toReal_ofReal
      (Real.rpow_nonneg hdelta.le exponent)
  have hWRpow : ∀ exponent : ℝ,
      (Kakeya.realRpowENN W exponent).toReal =
        Real.rpow W exponent := by
    intro exponent
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hW.le exponent)
  have hinvRpow : ∀ exponent : ℝ,
      (Kakeya.realRpowENN (1 / delta) exponent).toReal =
        Real.rpow (1 / delta) exponent := by
    intro exponent
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hinv.le exponent)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, hdeltaRpow,
    hWRpow, hinvRpow]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 128 * delta ^ 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ W / delta + 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 4),
    ENNReal.toReal_ofReal hW.le]
  let gap := 4 * badYLoss - grainLoss - slabLoss -
    (1 + power) * stickyLoss
  have hsmallReal : Real.rpow delta gap ≤ (1 / 400000 : ℝ) := by
    have h := (ENNReal.toReal_le_toReal
      (by simp [Kakeya.realRpowENN] :
        Kakeya.realRpowENN delta gap ≠ ⊤) ENNReal.ofReal_ne_top).2 hsmall
    rw [hdeltaRpow, ENNReal.toReal_ofReal (by norm_num :
      0 ≤ (1 / 400000 : ℝ))] at h
    exact h
  have hratio : W / delta + 2 ≤ 3 * (W / delta) := by
    have hone : 1 ≤ W / delta :=
      (le_div_iff₀ hdelta).2 (by simpa using hdeltaW)
    linarith
  have hinvPower : Real.rpow (1 / delta) (1 - sigma) =
      Real.rpow delta (-(1 - sigma)) := by
    rw [one_div]
    exact (Real.inv_rpow hdelta.le (1 - sigma)).trans
      (Real.rpow_neg hdelta.le (1 - sigma)).symm
  have hdeltaProduct :
      Real.rpow delta (4 * badYLoss) *
        Real.rpow delta (2 - sigma - stickyLoss) *
        Real.rpow delta (-grainLoss) *
        Real.rpow (1 / delta) (1 - sigma) =
      Real.rpow delta (1 + 4 * badYLoss - stickyLoss - grainLoss) := by
    rw [hinvPower]
    calc
      Real.rpow delta (4 * badYLoss) *
          Real.rpow delta (2 - sigma - stickyLoss) *
          Real.rpow delta (-grainLoss) *
          Real.rpow delta (-(1 - sigma)) =
        Real.rpow delta ((4 * badYLoss) +
          (2 - sigma - stickyLoss) + (-grainLoss) +
          (-(1 - sigma))) := by
            rw [show Real.rpow delta (4 * badYLoss) *
                Real.rpow delta (2 - sigma - stickyLoss) =
              Real.rpow delta ((4 * badYLoss) +
                (2 - sigma - stickyLoss)) from
              (Real.rpow_add hdelta _ _).symm]
            rw [show Real.rpow delta ((4 * badYLoss) +
                  (2 - sigma - stickyLoss)) *
                Real.rpow delta (-grainLoss) =
              Real.rpow delta ((4 * badYLoss) +
                (2 - sigma - stickyLoss) + (-grainLoss)) from
              (Real.rpow_add hdelta _ _).symm]
            exact (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta
          (1 + 4 * badYLoss - stickyLoss - grainLoss) := by
        congr 1
        ring
  have hWPower : Real.rpow W (-stickyLoss) =
      Real.rpow delta (-(power * stickyLoss)) := by
    rw [hrho]
    calc
      Real.rpow (Real.rpow delta power) (-stickyLoss) =
          Real.rpow delta (power * (-stickyLoss)) :=
        (Real.rpow_mul hdelta.le power (-stickyLoss)).symm
      _ = Real.rpow delta (-(power * stickyLoss)) := by congr 1 <;> ring
  have hcombined : Real.rpow delta
        (4 * badYLoss - stickyLoss - grainLoss) *
      Real.rpow W (-stickyLoss) =
      Real.rpow delta (slabLoss + gap) := by
    rw [hWPower]
    calc
      Real.rpow delta (4 * badYLoss - stickyLoss - grainLoss) *
          Real.rpow delta (-(power * stickyLoss)) =
        Real.rpow delta ((4 * badYLoss - stickyLoss - grainLoss) +
          (-(power * stickyLoss))) := (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (slabLoss + gap) := by
        congr 1
        dsimp only [gap]
        ring
  have hpi : (294912 : ℝ) * Real.rpow delta gap ≤ Real.pi := by
    apply le_of_lt
    calc
      (294912 : ℝ) * Real.rpow delta gap ≤
          294912 * (1 / 400000 : ℝ) := by gcongr
      _ < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  rw [show
    4 * (128 * delta ^ 2 * (2 * Real.rpow delta (4 * badYLoss))) *
        (Real.rpow delta (2 - sigma - stickyLoss) *
          Real.rpow W (-stickyLoss)) *
        ((W / delta + 2) *
          (24 * Real.rpow delta (-grainLoss) *
            Real.rpow (1 / delta) (1 - sigma))) =
      24576 * delta ^ 2 * (W / delta + 2) *
        ((Real.rpow delta (4 * badYLoss) *
          Real.rpow delta (2 - sigma - stickyLoss) *
          Real.rpow delta (-grainLoss) *
          Real.rpow (1 / delta) (1 - sigma)) *
          Real.rpow W (-stickyLoss)) by ring, hdeltaProduct]
  calc
    24576 * delta ^ 2 * (W / delta + 2) *
        (Real.rpow delta (1 + 4 * badYLoss - stickyLoss - grainLoss) *
          Real.rpow W (-stickyLoss)) ≤
      24576 * delta ^ 2 * (3 * (W / delta)) *
        (Real.rpow delta (1 + 4 * badYLoss - stickyLoss - grainLoss) *
          Real.rpow W (-stickyLoss)) := by
        have hfactor : 0 ≤ Real.rpow delta
            (1 + 4 * badYLoss - stickyLoss - grainLoss) *
              Real.rpow W (-stickyLoss) :=
          mul_nonneg (Real.rpow_nonneg hdelta.le _)
            (Real.rpow_nonneg hW.le _)
        have hmiddle := mul_le_mul_of_nonneg_right hratio hfactor
        have hprefix : 0 ≤ (24576 : ℝ) * delta ^ 2 := by positivity
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hmiddle hprefix
    _ = 73728 * delta ^ 2 * W *
        (Real.rpow delta (4 * badYLoss - stickyLoss - grainLoss) *
          Real.rpow W (-stickyLoss)) := by
      field_simp [hdelta.ne']
      have hsplit : Real.rpow delta
        (1 + 4 * badYLoss - stickyLoss - grainLoss) =
          delta * Real.rpow delta
            (4 * badYLoss - stickyLoss - grainLoss) := by
        calc
          Real.rpow delta
              (1 + 4 * badYLoss - stickyLoss - grainLoss) =
            Real.rpow delta
              (1 + (4 * badYLoss - stickyLoss - grainLoss)) := by
                congr 1
                ring
          _ = Real.rpow delta 1 * Real.rpow delta
              (4 * badYLoss - stickyLoss - grainLoss) :=
            Real.rpow_add hdelta _ _
          _ = _ := by simp [Real.rpow_one]
      rw [hsplit]
      ring
    _ = 73728 * delta ^ 2 * W * Real.rpow delta (slabLoss + gap) := by
      rw [hcombined]
    _ = (73728 * Real.rpow delta gap) *
        (Real.rpow delta slabLoss * delta ^ 2 * W) := by
      rw [show Real.rpow delta (slabLoss + gap) =
        Real.rpow delta slabLoss * Real.rpow delta gap from
          Real.rpow_add hdelta _ _]
      ring
    _ ≤ (Real.pi / 4) *
        (Real.rpow delta slabLoss * delta ^ 2 * W) := by
      have hconstant : (73728 : ℝ) * Real.rpow delta gap ≤
          Real.pi / 4 := by linarith
      exact mul_le_mul_of_nonneg_right hconstant
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hdelta.le slabLoss)
            (sq_nonneg delta)) hW.le)
    _ = (Real.pi / 4) * Real.rpow delta (slabLoss + 2) * W := by
      rw [show Real.rpow delta (slabLoss + 2) =
        Real.rpow delta slabLoss * Real.rpow delta 2 from
          Real.rpow_add hdelta _ _,
        show Real.rpow delta 2 = delta ^ 2 by
          exact Real.rpow_ofNat delta 2]
      ring

theorem pureWZ2_weightedCommonY_badBudget_at_power
    {sigma grainLoss slabLoss badYLoss delta power : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hrho : scale.1 = Real.rpow delta power)
    (hsmall : Kakeya.realRpowENN delta
        (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss)) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    ENNReal.ofReal (128 * delta ^ 2) *
        (2 * Kakeya.realRpowENN delta (4 * badYLoss)) ≤
      (1 / 2 : ENNReal) *
        (popular.labelThreshold /
          (Kakeya.realRpowENN (delta / scale.1) (2 - sigma - slabLoss) *
            cfg.family.enncard)) := by
  let A := ENNReal.ofReal (128 * delta ^ 2) *
    (2 * Kakeya.realRpowENN delta (4 * badYLoss))
  let C := Kakeya.realRpowENN (delta / scale.1)
    (2 - sigma - slabLoss) * cfg.family.enncard
  let N : ENNReal := popular.labels.card
  let B := ENNReal.ofReal (scale.1 / delta + 2) *
    (24 * Kakeya.realRpowENN delta (-grainLoss) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma))
  let L := ENNReal.ofReal (Real.pi / 4) *
    Kakeya.realRpowENN delta (slabLoss + 2) * cfg.family.enncard *
      ENNReal.ofReal scale.1
  let M := scaleData.slabShading.mass
  have hlabelsNonempty : popular.labels.Nonempty := by
    rcases popular.keptLabels_nonempty with ⟨label, hlabel⟩
    refine ⟨label, ?_⟩
    rw [popular.keptLabels_eq] at hlabel
    exact (Finset.mem_filter.mp hlabel).1
  have hNZero : N ≠ 0 := by
    dsimp only [N]
    exact_mod_cast hlabelsNonempty.card_pos.ne'
  have hNTop : N ≠ ⊤ := by simp [N]
  have hratio : 0 < delta / scale.1 :=
    div_pos cfg.extremal.delta_pos
      (cfg.extremal.delta_pos.trans_le scale.2.1)
  have hCZero : C ≠ 0 := by
    apply mul_ne_zero
    · simp [C, Kakeya.realRpowENN, Real.rpow_pos_of_pos hratio]
    · change (cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast cfg.extremal.nonempty.ne'
  have hCTop : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [C, Kakeya.realRpowENN])
      (by simp [C, Kakeya.Streamlined.TubeFamily.enncard])
  have hNB : N ≤ B := popular.total_label_bound
  have hidentity : 2 * (N * popular.labelThreshold) = M :=
    popular.labelThreshold_identity
  have hLM : L ≤ M := scaleData.slab_mass
  have hbase := weighted_commonY_numeric_base_at_power (sigma := sigma)
    cfg.extremal.delta_pos cfg.extremal.delta_le_one
      (cfg.extremal.delta_pos.trans_le scale.2.1) scale.2.1 hrho hsmall
  have hnumeric : 4 * A * C * B ≤ L := by
    dsimp only [A, C, B, L]
    calc
      _ = (4 * (ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss))) *
          Kakeya.realRpowENN (delta / scale.1) (2 - sigma - slabLoss) *
          (ENNReal.ofReal (scale.1 / delta + 2) *
            (24 * Kakeya.realRpowENN delta (-grainLoss) *
              Kakeya.realRpowENN (1 / delta) (1 - sigma)))) *
            cfg.family.enncard := by ring
      _ ≤ (ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (slabLoss + 2) *
          ENNReal.ofReal scale.1) * cfg.family.enncard := by gcongr
      _ = L := by dsimp only [L]; ring
  simpa only [A, C] using
    power_weighted_threshold_budget_of_bounds hNZero hNTop hCZero hCTop
      hNB hidentity hLM hnumeric

theorem pureWZ2_weightedCommonY_badBudget_at_fine_power
    {sigma grainLoss slabLoss stickyLoss badYLoss delta power : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hrho : scale.1 = Real.rpow delta power)
    (hsmall : Kakeya.realRpowENN delta
        (4 * badYLoss - grainLoss - slabLoss -
          (1 + power) * stickyLoss) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    ENNReal.ofReal (128 * delta ^ 2) *
        (2 * Kakeya.realRpowENN delta (4 * badYLoss)) ≤
      (1 / 2 : ENNReal) *
        (popular.labelThreshold /
          ((Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
            Kakeya.realRpowENN scale.1 (-stickyLoss)) *
              cfg.family.enncard)) := by
  let A := ENNReal.ofReal (128 * delta ^ 2) *
    (2 * Kakeya.realRpowENN delta (4 * badYLoss))
  let C := (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
    Kakeya.realRpowENN scale.1 (-stickyLoss)) * cfg.family.enncard
  let N : ENNReal := popular.labels.card
  let B := ENNReal.ofReal (scale.1 / delta + 2) *
    (24 * Kakeya.realRpowENN delta (-grainLoss) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma))
  let L := ENNReal.ofReal (Real.pi / 4) *
    Kakeya.realRpowENN delta (slabLoss + 2) * cfg.family.enncard *
      ENNReal.ofReal scale.1
  let M := scaleData.slabShading.mass
  have hlabelsNonempty : popular.labels.Nonempty := by
    rcases popular.keptLabels_nonempty with ⟨label, hlabel⟩
    refine ⟨label, ?_⟩
    rw [popular.keptLabels_eq] at hlabel
    exact (Finset.mem_filter.mp hlabel).1
  have hNZero : N ≠ 0 := by
    dsimp only [N]
    exact_mod_cast hlabelsNonempty.card_pos.ne'
  have hNTop : N ≠ ⊤ := by simp [N]
  have hCZero : C ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero
        (by simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos cfg.extremal.delta_pos])
        (by simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos
            (cfg.extremal.delta_pos.trans_le scale.2.1)])
    · change (cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast cfg.extremal.nonempty.ne'
  have hCTop : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp [C, Kakeya.realRpowENN])
        (by simp [C, Kakeya.realRpowENN]))
      (by simp [C, Kakeya.Streamlined.TubeFamily.enncard])
  have hbase := weighted_commonY_numeric_base_at_fine_power
    (sigma := sigma) (grainLoss := grainLoss)
    (slabLoss := slabLoss) (stickyLoss := stickyLoss)
    (badYLoss := badYLoss) cfg.extremal.delta_pos
    cfg.extremal.delta_le_one
    (cfg.extremal.delta_pos.trans_le scale.2.1) scale.2.1 hrho hsmall
  have hnumeric : 4 * A * C * B ≤ L := by
    dsimp only [A, C, B, L]
    calc
      _ = (4 * (ENNReal.ofReal (128 * delta ^ 2) *
          (2 * Kakeya.realRpowENN delta (4 * badYLoss))) *
          (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
            Kakeya.realRpowENN scale.1 (-stickyLoss)) *
          (ENNReal.ofReal (scale.1 / delta + 2) *
            (24 * Kakeya.realRpowENN delta (-grainLoss) *
              Kakeya.realRpowENN (1 / delta) (1 - sigma)))) *
            cfg.family.enncard := by ring
      _ ≤ (ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (slabLoss + 2) *
          ENNReal.ofReal scale.1) * cfg.family.enncard := by gcongr
      _ = L := by dsimp only [L]; ring
  simpa only [A, C] using
    power_weighted_threshold_budget_of_bounds hNZero hNTop hCZero hCTop
      popular.total_label_bound popular.labelThreshold_identity
      scaleData.slab_mass hnumeric

theorem pureWZ2_rotatedWeightedCommonYRefinement_at_fine_power
    {sigma grainLoss slabLoss stickyLoss badYLoss delta power : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hbadYLoss : 0 < badYLoss) (hdeltaLtOne : delta < 1)
    (frameSlope : ℝ)
    (hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        2 * scale.1 ^ 2)
    (hframeSmall : 2 * scale.1 ^ 2 ≤ 1 / 100)
    (hrho : scale.1 = Real.rpow delta power)
    (hpointCap : ∀ point,
      (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
        (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN scale.1 (-stickyLoss)) *
            cfg.family.enncard)
    (hsmall : Kakeya.realRpowENN delta
        (4 * badYLoss - grainLoss - slabLoss -
          (1 + power) * stickyLoss) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    ∃ common : PureWZ2RotatedWeightedCommonYData
        cfg scale scaleData popular frameSlope,
      common.badYLoss = badYLoss := by
  let cap := (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
    Kakeya.realRpowENN scale.1 (-stickyLoss)) * cfg.family.enncard
  have hcapZero : cap ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero
        (by simp [cap, Kakeya.realRpowENN,
          Real.rpow_pos_of_pos cfg.extremal.delta_pos])
        (by simp [cap, Kakeya.realRpowENN,
          Real.rpow_pos_of_pos
            (cfg.extremal.delta_pos.trans_le scale.2.1)])
    · change (cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast cfg.extremal.nonempty.ne'
  have hcapTop : cap ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp [cap, Kakeya.realRpowENN])
        (by simp [cap, Kakeya.realRpowENN]))
      (by simp [cap, Kakeya.Streamlined.TubeFamily.enncard])
  apply pureWZ2_rotatedWeightedCommonYRefinement cfg scale scaleData popular
    hbadYLoss hdeltaLtOne frameSlope hlabelClose hframeSmall cap
    hcapZero hcapTop (by simpa [cap] using hpointCap)
  simpa [cap] using pureWZ2_weightedCommonY_badBudget_at_fine_power
    cfg scale scaleData popular hrho hsmall

/-- Positive-path version of the preceding numerical wrapper.  It records
only the common-slice geometry and mass; the caller supplies any frame error
small enough for the rotated slice estimate. -/
theorem pureWZ2_rotatedWeightedCommonYRefinementCore_at_fine_power
    {sigma grainLoss slabLoss stickyLoss badYLoss delta power frameGap : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hbadYLoss : 0 < badYLoss) (hdeltaLtOne : delta < 1)
    (frameSlope : ℝ)
    (hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        frameGap)
    (hframeSmall : frameGap ≤ 1 / 100)
    (hrho : scale.1 = Real.rpow delta power)
    (hpointCap : ∀ point,
      (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
        (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
          Kakeya.realRpowENN scale.1 (-stickyLoss)) *
            cfg.family.enncard)
    (hsmall : Kakeya.realRpowENN delta
        (4 * badYLoss - grainLoss - slabLoss -
          (1 + power) * stickyLoss) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    ∃ common : PureWZ2RotatedWeightedCommonYCore
        cfg scale scaleData popular frameSlope,
      common.badYLoss = badYLoss := by
  let cap := (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
    Kakeya.realRpowENN scale.1 (-stickyLoss)) * cfg.family.enncard
  have hcapZero : cap ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero
        (by simp [cap, Kakeya.realRpowENN,
          Real.rpow_pos_of_pos cfg.extremal.delta_pos])
        (by simp [cap, Kakeya.realRpowENN,
          Real.rpow_pos_of_pos
            (cfg.extremal.delta_pos.trans_le scale.2.1)])
    · change (cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast cfg.extremal.nonempty.ne'
  have hcapTop : cap ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp [cap, Kakeya.realRpowENN])
        (by simp [cap, Kakeya.realRpowENN]))
      (by simp [cap, Kakeya.Streamlined.TubeFamily.enncard])
  apply pureWZ2_rotatedWeightedCommonYRefinementCore cfg scale scaleData popular
    hbadYLoss hdeltaLtOne frameSlope hlabelClose hframeSmall cap
    hcapZero hcapTop (by simpa [cap] using hpointCap)
  simpa [cap] using pureWZ2_weightedCommonY_badBudget_at_fine_power
    cfg scale scaleData popular hrho hsmall

theorem pureWZ2_rotatedWeightedCommonYRefinement_at_power
    {sigma grainLoss slabLoss badYLoss delta power : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma grainLoss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma slabLoss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (hbadYLoss : 0 < badYLoss) (hdeltaLtOne : delta < 1)
    (frameSlope : ℝ)
    (hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        2 * scale.1 ^ 2)
    (hframeSmall : 2 * scale.1 ^ 2 ≤ 1 / 100)
    (hrho : scale.1 = Real.rpow delta power)
    (hsmall : Kakeya.realRpowENN delta
        (4 * badYLoss - grainLoss - 2 * slabLoss -
          power * (2 - sigma - slabLoss)) ≤
      ENNReal.ofReal (1 / 400000 : ℝ)) :
    ∃ common : PureWZ2RotatedWeightedCommonYData
        cfg scale scaleData popular frameSlope,
      common.badYLoss = badYLoss := by
  let cap := Kakeya.realRpowENN (delta / scale.1)
    (2 - sigma - slabLoss) * cfg.family.enncard
  have hratio : 0 < delta / scale.1 :=
    div_pos cfg.extremal.delta_pos
      (cfg.extremal.delta_pos.trans_le scale.2.1)
  have hcapZero : cap ≠ 0 := by
    apply mul_ne_zero
    · simp [cap, Kakeya.realRpowENN, Real.rpow_pos_of_pos hratio]
    · change (cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast cfg.extremal.nonempty.ne'
  have hcapTop : cap ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [cap, Kakeya.realRpowENN])
      (by simp [cap, Kakeya.Streamlined.TubeFamily.enncard])
  apply pureWZ2_rotatedWeightedCommonYRefinement cfg scale scaleData popular
    hbadYLoss hdeltaLtOne frameSlope hlabelClose hframeSmall cap
    hcapZero hcapTop scaleData.slab_pointMultiplicity_upper
  simpa [cap] using
    pureWZ2_weightedCommonY_badBudget_at_power cfg scale scaleData
      popular hrho hsmall

end Kakeya.Assouad
end
