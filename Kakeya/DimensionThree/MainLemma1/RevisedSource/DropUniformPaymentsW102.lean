module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceDropPreparationW101

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem exists_drop_log_lower_w102 (epsilon A : Real) (heps : 0 < epsilon) :
    ∃ cutoff : NNReal, 0 < cutoff ∧ cutoff < 1 ∧
      ∀ {delta d : NNReal}, 0 < delta -> delta < cutoff -> 0 < d -> d <= delta ^ epsilon ->
        A <= 1 + Real.log (1 / (d : Real)) := by
  let cutoff : NNReal := min ⟨Real.exp (-(A + 1) / epsilon), (Real.exp_pos _).le⟩ (1 / 2)
  refine ⟨cutoff, lt_min (Real.exp_pos _) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro delta d hd hcut hdp hscale
  have hcutR : (delta : Real) < Real.exp (-(A + 1) / epsilon) :=
    hcut.trans_le (min_le_left _ _)
  have hlogDelta := Real.log_lt_log (show (0 : Real) < delta from hd) hcutR
  rw [Real.log_exp] at hlogDelta
  have hlogD := Real.log_le_log (show (0 : Real) < d from hdp)
    (show (d : Real) <= (delta : Real) ^ epsilon by exact_mod_cast hscale)
  rw [Real.log_rpow (show (0 : Real) < delta from hd)] at hlogD
  have hpaid := (lt_div_iff₀ heps).mp hlogDelta
  rw [one_div, Real.log_inv]
  nlinarith

/-- All fixed geometric and original-scale preparation losses are paid by
one uniformly chosen integer trial exponent. -/
theorem exists_drop_uniform_polylog_payment_w102
    (epsilon : Real) (heps : 0 < epsilon)
    (Cgeom Cprep Cselect : NNReal) (Kmax Kprep Kselect : Nat) :
    ∃ (Kout : Nat) (cutoff : NNReal), Kmax <= Kout ∧ 1 <= Kout ∧
      0 < cutoff ∧ cutoff < 1 ∧
      ∀ {delta d : NNReal}, 0 < delta -> delta < cutoff ->
        0 < d -> d <= 1 -> d <= delta ^ epsilon ->
      ∀ k : Nat, k <= Kmax ->
        trialRetainedFractionW94 d Kout <= (Cgeom : ENNReal)⁻¹ * trialRetainedFractionW94 d k *
          towerPreparationRetainedW95 delta Cprep Kprep *
            (towerPreparationRetainedW95 delta Cselect Kselect) ^ (3 : Nat) := by
  let C : Real := 2 + (epsilon * Real.log 2)⁻¹
  let A : Real := (Cgeom : Real) * Cprep * (Cselect : Real) ^ (3 : Nat) * C ^ (Kprep + Kselect * 3)
  obtain ⟨cutoff, hcutoff, hcutoff1, hlogLarge⟩ := exists_drop_log_lower_w102 epsilon A heps
  let Kout := Kmax + Kprep + Kselect * 3 + 1
  refine ⟨Kout, cutoff, by omega, by omega, hcutoff, hcutoff1, ?_⟩
  intro delta d hd hcut hdp hd1 hscale k hk
  have hdlt : delta < 1 := hcut.trans hcutoff1
  let t := Real.log (1 / (delta : Real))
  let s := Real.log (1 / (d : Real))
  have ht : 0 <= t := Real.log_nonneg ((le_div_iff₀ (show (0 : Real) < delta from hd)).mpr
    (by simpa only [one_mul] using (show (delta : Real) <= 1 from hdlt.le)))
  have hs : 0 <= s := Real.log_nonneg ((le_div_iff₀ (show (0 : Real) < d from hdp)).mpr
    (by simpa only [one_mul] using (show (d : Real) <= 1 from hd1)))
  have hL : 0 < 1 + s := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 <= C := by dsimp [C]; positivity
  have hlogs : epsilon * t <= s := by
    have h := Real.log_le_log (show (0 : Real) < d from hdp)
      (show (d : Real) <= (delta : Real) ^ epsilon by exact_mod_cast hscale)
    rw [Real.log_rpow (show (0 : Real) < delta from hd)] at h
    dsimp only [s, t]
    simp only [one_div, Real.log_inv]
    linarith
  have hT : 0 <= 2 + t / Real.log 2 := by positivity
  have hcompare : 2 + t / Real.log 2 <= C * (1 + s) := by
    have hts : t <= s / epsilon := (le_div_iff₀ heps).mpr (by simpa [mul_comm] using hlogs)
    calc
      _ <= 2 + (s / epsilon) / Real.log 2 := add_le_add_right (div_le_div_of_nonneg_right hts hlog2.le) _
      _ = 2 + (epsilon * Real.log 2)⁻¹ * s := by rw [div_div, div_eq_mul_inv, mul_comm s]
      _ <= 2 * (1 + s) + (epsilon * Real.log 2)⁻¹ * (1 + s) := by
        apply add_le_add
        · nlinarith
        · gcongr
          linarith
      _ = C * (1 + s) := by dsimp [C]; ring
  have hden : (Cgeom : Real) * (1 + s) ^ k * ((Cprep : Real) * (2 + t / Real.log 2) ^ Kprep) *
      ((Cselect : Real) * (2 + t / Real.log 2) ^ Kselect) ^ (3 : Nat) <= (1 + s) ^ Kout := by
    calc
      _ <= (Cgeom : Real) * (1 + s) ^ Kmax * ((Cprep : Real) * (C * (1 + s)) ^ Kprep) *
          ((Cselect : Real) * (C * (1 + s)) ^ Kselect) ^ (3 : Nat) := by
        gcongr
        linarith
      _ = A * (1 + s) ^ (Kmax + Kprep + Kselect * 3) := by
        dsimp only [A]
        simp only [pow_add, pow_mul, mul_pow]
        ring
      _ <= (1 + s) * (1 + s) ^ (Kmax + Kprep + Kselect * 3) := by
        exact mul_le_mul_of_nonneg_right (hlogLarge hd hcut hdp hscale) (pow_nonneg hL.le _)
      _ = (1 + s) ^ Kout := by rw [show Kout = Kmax + Kprep + Kselect * 3 + 1 from rfl, pow_succ]; ring
  let L : NNReal := ⟨1 + s, hL.le⟩
  let T : NNReal := ⟨2 + t / Real.log 2, hT⟩
  have hdenNN : Cgeom * L ^ k * (Cprep * T ^ Kprep) * (Cselect * T ^ Kselect) ^ (3 : Nat) <= L ^ Kout := by
    exact_mod_cast hden
  have hdenE : (Cgeom : ENNReal) * (L : ENNReal) ^ k * ((Cprep : ENNReal) * (T : ENNReal) ^ Kprep) *
      ((Cselect : ENNReal) * (T : ENNReal) ^ Kselect) ^ (3 : Nat) <= (L : ENNReal) ^ Kout := by
    exact_mod_cast hdenNN
  have htrial : ∀ n, trialRetainedFractionW94 d n = ((L : ENNReal) ^ n)⁻¹ := by
    intro n
    unfold trialRetainedFractionW94
    rw [Real.rpow_neg hL.le, Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (pow_pos hL n),
      ENNReal.ofReal_pow hL.le]
    change (ENNReal.ofReal (L : Real) ^ n)⁻¹ = _
    rw [ENNReal.ofReal_coe_nnreal]
  have hprep : ∀ (C0 : NNReal) n, towerPreparationRetainedW95 delta C0 n =
      ((C0 : ENNReal) * (T : ENNReal) ^ n)⁻¹ := by
    intro C0 n
    unfold towerPreparationRetainedW95
    rw [ENNReal.ofReal_pow hT]
    change ((C0 : ENNReal) * ENNReal.ofReal (T : Real) ^ n)⁻¹ = _
    rw [ENNReal.ofReal_coe_nnreal]
  rw [htrial, htrial, hprep, hprep]
  have hinv := ENNReal.inv_le_inv.mpr hdenE
  rw [ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl ENNReal.coe_ne_top), ENNReal.inv_pow] at hinv
  simpa only [ENNReal.inv_pow] using hinv

/-- The actual Window lower endpoint supplies the sixteen-fold scale gap
required by the corrected exact-unit-tube comparison. -/
theorem exists_drop_window_scale_separation_w102 (epsilon : Real) (heps : 0 < epsilon) :
    ∃ cutoff : NNReal, 0 < cutoff ∧ cutoff < 1 ∧
      ∀ {delta d r : NNReal}, 0 < delta -> delta < cutoff -> 0 < d -> d <= delta ^ epsilon ->
        (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= (r : ENNReal) -> 16 * d <= r := by
  let e : Real := 3 * epsilon ^ 2 / 2
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      (16 : ENNReal) <= (delta : ENNReal) ^ (-e) :=
    eventually_finite_const_le_rpow_neg (by finiteness) he
  obtain ⟨c, hc, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  refine ⟨min c (1 / 2), lt_min hc (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro delta d r hd hdelta hdp hscale hwindow
  have hpayE := hcut ⟨hd, hdelta.trans_le (min_le_left _ _)⟩
  have hpay : (16 : NNReal) <= delta ^ (-e) := by
    change (16 : ENNReal) <= (delta : ENNReal) ^ (-e) at hpayE
    rw [← ENNReal.coe_rpow_of_ne_zero hd.ne'] at hpayE
    exact_mod_cast hpayE
  have hpower : (16 : NNReal) <= d ^ (-(3 * epsilon / 2)) := by
    calc
      _ <= delta ^ (-e) := hpay
      _ = (delta ^ epsilon) ^ (-(3 * epsilon / 2)) := by
        rw [← NNReal.rpow_mul]
        congr 1
        dsimp [e]
        ring
      _ <= d ^ (-(3 * epsilon / 2)) :=
        NNReal.rpow_le_rpow_of_nonpos hdp hscale (by linarith)
  apply ENNReal.coe_le_coe.mp
  calc
    ((16 * d : NNReal) : ENNReal) <= ((d ^ (-(3 * epsilon / 2)) * d : NNReal) : ENNReal) := by
      exact_mod_cast mul_le_mul_left hpower d
    _ = (d : ENNReal) ^ (1 - 3 * epsilon / 2) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hdp.ne']
      calc
        _ = (d : ENNReal) ^ (-(3 * epsilon / 2)) * (d : ENNReal) ^ (1 : Real) := by
          rw [ENNReal.rpow_one]
        _ = (d : ENNReal) ^ (-(3 * epsilon / 2) + 1) :=
          (ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hdp.ne') ENNReal.coe_ne_top).symm
        _ = _ := by congr 1; ring
    _ <= (r : ENNReal) := hwindow

end

end Kakeya.ml1Boot.TrialRestartW94
