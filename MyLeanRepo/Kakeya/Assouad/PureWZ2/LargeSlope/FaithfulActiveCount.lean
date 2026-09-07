import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Producer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedConvexOverload

/-!
# Active-count algebra for the faithful Step-4 witness
-/

noncomputable section

namespace Kakeya.Assouad

/-- Card-proportional active count after faithful prism pigeonholing. -/
lemma pureWZ2_faithful_active_count_from_pigeonhole
    {delta eta sigma rho prismCount card active : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcard : 0 ≤ card) (hactive : 0 ≤ active)
    (hpigeonhole :
      36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho * card ≤
        prismCount * (4000 * Real.sqrt rho * delta ^ 2) * active)
    (hprism : prismCount ≤
      Real.rpow delta (-(12 * eta)) *
        Real.rpow rho ((-1 + sigma) / 2)) :
    (9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
        Real.rpow rho ((1 - sigma) / 2) * card ≤ active := by
  let D : ℝ := 4000 * Real.rpow delta (2 - 12 * eta) *
    Real.rpow rho (sigma / 2)
  have hDpos : 0 < D := by
    dsimp only [D]
    exact mul_pos (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos hdelta _))
      (Real.rpow_pos_of_pos hrho _)
  have hsqrtRho : Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow rho
  have hdeltaLeft : Real.rpow delta (12 * eta) * delta ^ 2 =
      Real.rpow delta (12 * eta + 2) := by
    rw [show delta ^ 2 = Real.rpow delta 2 by
      exact (Real.rpow_two delta).symm]
    exact (Real.rpow_add hdelta _ _).symm
  have hdeltaUpper : Real.rpow delta (-(12 * eta)) * delta ^ 2 =
      Real.rpow delta (2 - 12 * eta) := by
    rw [show delta ^ 2 = Real.rpow delta 2 by
      exact (Real.rpow_two delta).symm]
    calc
      Real.rpow delta (-(12 * eta)) * Real.rpow delta 2 =
          Real.rpow delta (-(12 * eta) + 2) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (2 - 12 * eta) := by congr 1 <;> ring
  have hrhoUpper : Real.rpow rho ((-1 + sigma) / 2) *
      Real.sqrt rho = Real.rpow rho (sigma / 2) := by
    rw [hsqrtRho]
    calc
      Real.rpow rho ((-1 + sigma) / 2) *
          Real.rpow rho (1 / 2 : ℝ) =
        Real.rpow rho (((-1 + sigma) / 2) + (1 / 2 : ℝ)) :=
          (Real.rpow_add hrho _ _).symm
      _ = Real.rpow rho (sigma / 2) := by congr 1 <;> ring
  have hupperScaled :
      prismCount * (4000 * Real.sqrt rho * delta ^ 2) * active ≤
        D * active := by
    have hfactorNonneg :
        0 ≤ 4000 * Real.sqrt rho * delta ^ 2 := by positivity
    have hfirst := mul_le_mul_of_nonneg_right hprism hfactorNonneg
    have hsecond := mul_le_mul_of_nonneg_right hfirst hactive
    calc
      prismCount * (4000 * Real.sqrt rho * delta ^ 2) * active ≤
          (Real.rpow delta (-(12 * eta)) *
            Real.rpow rho ((-1 + sigma) / 2)) *
              (4000 * Real.sqrt rho * delta ^ 2) * active := hsecond
      _ = D * active := by
        dsimp only [D]
        calc
          (Real.rpow delta (-(12 * eta)) *
              Real.rpow rho ((-1 + sigma) / 2)) *
                (4000 * Real.sqrt rho * delta ^ 2) * active =
            4000 * (Real.rpow delta (-(12 * eta)) * delta ^ 2) *
              (Real.rpow rho ((-1 + sigma) / 2) * Real.sqrt rho) *
                active := by ring
          _ = 4000 * Real.rpow delta (2 - 12 * eta) *
              Real.rpow rho (sigma / 2) * active := by
            rw [hdeltaUpper, hrhoUpper]
  have hDdesired :
      D * ((9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
        Real.rpow rho ((1 - sigma) / 2) * card) =
      36 * Real.rpow delta (12 * eta) * delta ^ 2 *
        Real.sqrt rho * card := by
    have hdeltaProduct : Real.rpow delta (2 - 12 * eta) *
        Real.rpow delta (24 * eta) =
          Real.rpow delta (12 * eta + 2) := by
      calc
        Real.rpow delta (2 - 12 * eta) *
            Real.rpow delta (24 * eta) =
          Real.rpow delta ((2 - 12 * eta) + 24 * eta) :=
            (Real.rpow_add hdelta _ _).symm
        _ = Real.rpow delta (12 * eta + 2) := by congr 1 <;> ring
    have hrhoProduct : Real.rpow rho (sigma / 2) *
        Real.rpow rho ((1 - sigma) / 2) = Real.sqrt rho := by
      rw [hsqrtRho]
      calc
        Real.rpow rho (sigma / 2) *
            Real.rpow rho ((1 - sigma) / 2) =
          Real.rpow rho ((sigma / 2) + ((1 - sigma) / 2)) :=
            (Real.rpow_add hrho _ _).symm
        _ = Real.rpow rho (1 / 2 : ℝ) := by congr 1 <;> ring
    dsimp only [D]
    calc
      4000 * Real.rpow delta (2 - 12 * eta) *
          Real.rpow rho (sigma / 2) *
          ((9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
            Real.rpow rho ((1 - sigma) / 2) * card) =
        36 * (Real.rpow delta (2 - 12 * eta) *
          Real.rpow delta (24 * eta)) *
          (Real.rpow rho (sigma / 2) *
            Real.rpow rho ((1 - sigma) / 2)) * card := by ring
      _ = 36 * Real.rpow delta (12 * eta + 2) *
          Real.sqrt rho * card := by rw [hdeltaProduct, hrhoProduct]
      _ = 36 * Real.rpow delta (12 * eta) * delta ^ 2 *
          Real.sqrt rho * card := by
        rw [← hdeltaLeft]
        ring
  have hscaled :
      D * ((9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
        Real.rpow rho ((1 - sigma) / 2) * card) ≤ D * active := by
    rw [hDdesired]
    exact hpigeonhole.trans hupperScaled
  exact (mul_le_mul_iff_left₀ hDpos).mp (by
    simpa [mul_comm] using hscaled)

/-- Convert the ENNReal prism upper bound to its real form. -/
lemma pureWZ2_faithful_prism_upper_toReal
    {delta eta sigma rho : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho)
    {prismCount : ℕ}
    (h : (prismCount : ENNReal) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2)) :
    (prismCount : ℝ) ≤ Real.rpow delta (-(12 * eta)) *
      Real.rpow rho ((-1 + sigma) / 2) := by
  have hfinite : Kakeya.realRpowENN delta (-(12 * eta)) *
      Kakeya.realRpowENN rho ((-1 + sigma) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.realRpowENN])
  have hreal := ENNReal.toReal_mono hfinite h
  have hdeltaToReal :
      (Kakeya.realRpowENN delta (-(12 * eta))).toReal =
        Real.rpow delta (-(12 * eta)) := by
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hdelta.le _)
  have hrhoToReal :
      (Kakeya.realRpowENN rho ((-1 + sigma) / 2)).toReal =
        Real.rpow rho ((-1 + sigma) / 2) := by
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hdeltaToReal,
    hrhoToReal] at hreal
  exact hreal

/-- Convert the faithful ENNReal pigeonhole inequality to real arithmetic. -/
lemma pureWZ2_faithful_pigeonhole_toReal
    {delta eta rho : ℝ} (hdelta : 0 < delta) (hrho : 0 < rho)
    {familyCard prismCount activeCount : ℕ}
    (h : ENNReal.ofReal
          (36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho) *
          (familyCard : ENNReal) ≤
        (prismCount : ENNReal) *
          ENNReal.ofReal (4000 * Real.sqrt rho * delta ^ 2) *
            (activeCount : ENNReal)) :
    36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho *
        (familyCard : ℝ) ≤
      (prismCount : ℝ) * (4000 * Real.sqrt rho * delta ^ 2) *
        (activeCount : ℝ) := by
  have hfinite : (prismCount : ENNReal) *
      ENNReal.ofReal (4000 * Real.sqrt rho * delta ^ 2) *
        (activeCount : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) (by simp)
  have hreal := ENNReal.toReal_mono hfinite h
  have hleftNonneg :
      0 ≤ 36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hdelta.le _))
        (sq_nonneg delta))
      (Real.sqrt_nonneg rho)
  have hrightNonneg : 0 ≤ 4000 * Real.sqrt rho * delta ^ 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg rho))
      (sq_nonneg delta)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hleftNonneg,
    ENNReal.toReal_ofReal hrightNonneg] using hreal

/-- Replace `rho = 64 * width^2` in the faithful active factor. -/
lemma pureWZ2_faithful_rho_power
    {rho width sigma : ℝ} (hwidth : 0 < width)
    (hrho : rho = 64 * width ^ 2) :
    Real.rpow rho ((1 - sigma) / 2) =
      Real.rpow 64 ((1 - sigma) / 2) *
        Real.rpow width (1 - sigma) := by
  rw [hrho]
  have hmul := Real.mul_rpow
    (x := (64 : ℝ)) (y := width ^ 2) (z := (1 - sigma) / 2)
    (by norm_num) (sq_nonneg width)
  have htower : Real.rpow (width ^ 2) ((1 - sigma) / 2) =
      Real.rpow width (1 - sigma) := by
    rw [show width ^ 2 = Real.rpow width 2 by
      exact (Real.rpow_two width).symm]
    calc
      Real.rpow (Real.rpow width 2) ((1 - sigma) / 2) =
          Real.rpow width (2 * ((1 - sigma) / 2)) :=
        (Real.rpow_mul hwidth.le 2 ((1 - sigma) / 2)).symm
      _ = Real.rpow width (1 - sigma) := by congr 1 <;> ring
  calc
    Real.rpow (64 * width ^ 2) ((1 - sigma) / 2) =
        Real.rpow 64 ((1 - sigma) / 2) *
          Real.rpow (width ^ 2) ((1 - sigma) / 2) := hmul
    _ = Real.rpow 64 ((1 - sigma) / 2) *
        Real.rpow width (1 - sigma) := by rw [htower]

/-- Finish the faithful convex-overload inequality once geometry and
pigeonholing have supplied the volume and active-count bounds. -/
lemma pureWZ2_faithful_overload_finish
    {delta epsilon sigma eta rho width vol card count : ℝ}
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hwidth : 0 < width) (hcard : 0 < card)
    (K : ℝ) (hK : 0 < K)
    (hrho : rho = 64 * width ^ 2)
    (hvolume : vol ≤ K * Real.sqrt rho *
      Real.rpow delta (-(36 * eta / sigma)))
    (hactive : (9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
        Real.rpow rho ((1 - sigma) / 2) * card ≤ count)
    (hwidthDelta : width ≤ Real.rpow delta epsilon)
    (habsorb : 4608 * K * Real.rpow 64 (sigma / 2) / Real.pi <
      Real.rpow delta
        (12 * eta + 13 * eta + 36 * eta / sigma - epsilon * sigma)) :
    Real.rpow delta (-eta) * vol * card < count := by
  have hrhoPower := pureWZ2_faithful_rho_power
    (sigma := sigma) hwidth hrho
  have h64sigma : 0 < Real.rpow 64 (sigma / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hproduct : Real.rpow 64 ((1 - sigma) / 2) *
      Real.rpow 64 (sigma / 2) = 8 := by
    calc
      Real.rpow 64 ((1 - sigma) / 2) *
          Real.rpow 64 (sigma / 2) =
        Real.rpow 64 (((1 - sigma) / 2) + sigma / 2) :=
          (Real.rpow_add (by norm_num) _ _).symm
      _ = Real.rpow 64 (1 / 2 : ℝ) := by congr 1 <;> ring
      _ = 8 := by norm_num
  have hcoefficient :
      Real.pi / (576 * Real.rpow 64 (sigma / 2)) ≤
        (9 / 1000 : ℝ) * Real.rpow 64 ((1 - sigma) / 2) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) h64sigma)).2
    rw [show (9 / 1000 : ℝ) * Real.rpow 64 ((1 - sigma) / 2) *
        (576 * Real.rpow 64 (sigma / 2)) =
      (9 / 1000 : ℝ) * 576 *
        (Real.rpow 64 ((1 - sigma) / 2) *
          Real.rpow 64 (sigma / 2)) by ring, hproduct]
    nlinarith [Real.pi_lt_four]
  have hactiveExpected :
      (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
          Real.rpow delta (12 * eta + 12 * eta) * card *
            Real.rpow width (1 - sigma) ≤ count := by
    rw [show 12 * eta + 12 * eta = 24 * eta by ring]
    calc
      (Real.pi / (576 * Real.rpow 64 (sigma / 2))) *
          Real.rpow delta (24 * eta) * card *
            Real.rpow width (1 - sigma) ≤
        ((9 / 1000 : ℝ) * Real.rpow 64 ((1 - sigma) / 2)) *
          Real.rpow delta (24 * eta) * card *
            Real.rpow width (1 - sigma) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoefficient
              (Real.rpow_nonneg hdelta.le _)) hcard.le)
          (Real.rpow_nonneg hwidth.le _)
      _ = (9 / 1000 : ℝ) * Real.rpow delta (24 * eta) *
          Real.rpow rho ((1 - sigma) / 2) * card := by
        rw [hrhoPower]
        ring
      _ ≤ count := hactive
  exact cropped_convex_overload_final_ineq_card hdelta hsigma heta hepsilon
    hcard hwidth K hK hrho hvolume hactiveExpected hwidthDelta habsorb

end Kakeya.Assouad

end
