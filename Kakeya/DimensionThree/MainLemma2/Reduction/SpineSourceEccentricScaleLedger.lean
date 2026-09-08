/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceRetainedTerminalBridges
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedPlankCaller

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

noncomputable def sourceEccentricLogLoss (K : Nat) (delta : NNReal) : NNReal :=
  Real.toNNReal ((2 + Real.logb 2 (1 / (delta : Real))) ^ K)

noncomputable def sourceEccentricFineScale (delta : NNReal) (M a : Nat) : NNReal :=
  delta / (4 * sourceTowerRadius delta M a)

noncomputable def sourceEccentricParentScale (delta : NNReal) (M a m : Nat)
    (cParent : NNReal) : NNReal :=
  cParent * sourceTowerRadius delta M m / sourceTowerRadius delta M a

/-- A fixed polynomial payment; p and K precede delta and the later bias. -/
noncomputable def sourceEccentricSelectionCost (A : NNReal) (p K : Nat)
    (delta : NNReal) (etaPlank zeta : Real) : NNReal :=
  A * sourceEccentricLogLoss K delta * delta ^ (-(p : Real) * (etaPlank + zeta))

noncomputable def sourceEccentricTransportCost (A L : NNReal) (p : Nat)
    (delta : NNReal) (bias : Real) : NNReal :=
  A * L ^ p * sourceZeroPlankConstant delta bias ^ p

/-- The actual fixed-tower scale window, including the exceptional bottom
radius. The named sigma and rho are functions of the same a-cell. -/
structure SourceEccentricScaleBounds (delta : NNReal) (M : Nat) (e : Real)
    (a b m : Nat) (cParent : NNReal) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta <= 1
  exponent_pos : 0 < e
  exponent_half : e < 1 / 2
  outer_lt_middle : a < m
  middle_lt_inner : m < b
  inner_bound : b <= M
  original_to_middle : delta <= sourceTowerRadius delta M m
  middle_to_outer : sourceTowerRadius delta M m <= sourceTowerRadius delta M a
  outer_root : sourceTowerRadius delta M a <= 1 / 40
  fine_to_inner : delta / sourceTowerRadius delta M a <=
    sourceTowerRadius delta M b / sourceTowerRadius delta M a
  inner_separation : sourceTowerRadius delta M b / sourceTowerRadius delta M a <= delta ^ e
  window_lower : (sourceTowerRadius delta M b / sourceTowerRadius delta M a) ^ (1 - e) <=
    sourceTowerRadius delta M m / sourceTowerRadius delta M a
  window_upper : sourceTowerRadius delta M m / sourceTowerRadius delta M a <=
    (sourceTowerRadius delta M b / sourceTowerRadius delta M a) ^ e
  fine_window_lower : (delta / sourceTowerRadius delta M a) ^ (1 - e) <=
    sourceTowerRadius delta M m / sourceTowerRadius delta M a
  global_middle_upper : sourceTowerRadius delta M m / sourceTowerRadius delta M a <= delta ^ (e ^ 2)
  fine_positive : 0 < sourceEccentricFineScale delta M a
  fine_global_lower : 10 * delta <= sourceEccentricFineScale delta M a
  fine_global_upper : sourceEccentricFineScale delta M a <= delta ^ e / 4
  fine_small : sourceEccentricFineScale delta M a <= 1 / 16
  parent_positive : 0 < sourceEccentricParentScale delta M a m cParent
  coarse_scale_lower : sourceEccentricFineScale delta M a ^ (1 - e / 2) <=
    sourceEccentricParentScale delta M a m cParent
  parent_small : sourceEccentricParentScale delta M a m cParent <= 1 / 64
  ball_room : (13 / 16 : NNReal) + 4 * sourceEccentricParentScale delta M a m cParent <= 1

theorem source_eccentric_normalized_scale_bounds (M : Nat) (hM : 2 <= M)
    (e : Real) (he : 0 < e) (hehalf : e < 1 / 2)
    (cParent : NNReal) (hcParent : 0 < cParent) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0, forall a b m : Nat,
      b <= M ->
      (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
        (delta : Real) ^ e ->
      SourceTowerWindow delta M e a b m ->
      SourceEccentricScaleBounds delta M e a b m cParent := by
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  have he2half : 0 < e ^ 2 / 2 := by positivity
  have hcut1 : (0 : NNReal) < (1 / (64 * cParent)) ^ (1 / e ^ 2) := by positivity
  have hcut2 : (0 : NNReal) < cParent ^ (1 / (e ^ 2 / 2)) := by positivity
  filter_upwards [source_eventually_fixed_tower_radius_conditions M hM he,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num),
    Ioo_mem_nhdsGT hcut1, Ioo_mem_nhdsGT hcut2] with delta hd hd1 hd2 hd3
  have hd0 := hd.2.2.1
  have hdle : delta <= 1 := hd1.2.le
  have hparent : delta ^ (e ^ 2) <= 1 / (64 * cParent) := by
    have h := NNReal.rpow_le_rpow hd2.2.le he2.le
    rwa [← NNReal.rpow_mul, one_div_mul_cancel he2.ne', NNReal.rpow_one] at h
  have hsmall : delta ^ (e ^ 2 / 2) <= cParent := by
    have h := NNReal.rpow_le_rpow hd3.2.le he2half.le
    rwa [← NNReal.rpow_mul, one_div_mul_cancel he2half.ne', NNReal.rpow_one] at h
  have hrpos : forall k, 0 < sourceTowerRadius delta M k := by
    intro k
    unfold sourceTowerRadius
    split_ifs <;> positivity
  have hbottom : forall k, k <= M -> delta <= sourceTowerRadius delta M k := by
    intro k hk
    by_cases hkm : k < M
    · have h := hd.2.2.2.2.1 k hkm
      nlinarith
    · simp only [sourceTowerRadius, if_neg hkm, le_refl]
  have hmono : forall j k, j <= k -> k <= M ->
      sourceTowerRadius delta M k <= sourceTowerRadius delta M j := by
    intro j k hjk hk
    by_cases hkm : k < M
    · have hjm : j < M := lt_of_le_of_lt hjk hkm
      simp only [sourceTowerRadius, if_pos hkm, if_pos hjm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply NNReal.rpow_le_rpow_of_exponent_ge hd0 hdle
      exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)
    · simpa only [sourceTowerRadius, if_neg hkm] using hbottom j (hjk.trans hk)
  have hroot : forall k, k < M -> sourceTowerRadius delta M k <= 1 / 40 := by
    intro k hk
    simp only [sourceTowerRadius, if_pos hk]
    calc (1 / 40 : NNReal) * delta ^ ((k : Real) / M) <= (1 / 40) * 1 := by
          gcongr
          exact NNReal.rpow_le_one hdle (by positivity)
      _ = 1 / 40 := mul_one _
  intro a b m hb hsep hw
  rcases hw with ⟨ham, hmb, hwlo, hwhi⟩
  have hamM : a < M := lt_of_lt_of_le (ham.trans hmb) hb
  have hmm : m < M := lt_of_lt_of_le hmb hb
  let x := delta / sourceTowerRadius delta M a
  let t := sourceTowerRadius delta M b / sourceTowerRadius delta M a
  let y := sourceTowerRadius delta M m / sourceTowerRadius delta M a
  let z := sourceTowerRadius delta M b / sourceTowerRadius delta M m
  have hx : 0 < x := div_pos hd0 (hrpos a)
  have ht : 0 < t := div_pos (hrpos b) (hrpos a)
  have hz : 0 < z := div_pos (hrpos b) (hrpos m)
  have hxt : x <= t := div_le_div_of_nonneg_right (hbottom b hb) (by positivity)
  have htd : t <= delta ^ e := by exact_mod_cast hsep
  have hwlo' : t ^ (1 - e) <= z := by exact_mod_cast hwlo
  have hwhi' : z <= t ^ e := by exact_mod_cast hwhi
  have htz : t / z = y := by
    dsimp [t, z, y]
    field_simp [(hrpos a).ne', (hrpos b).ne', (hrpos m).ne']
  have hylo : t ^ (1 - e) <= y := by
    calc t ^ (1 - e) = t / t ^ e := by
          rw [NNReal.rpow_sub ht.ne', NNReal.rpow_one]
      _ <= t / z := div_le_div_of_nonneg_left ht.le hz hwhi'
      _ = y := htz
  have hyhi : y <= t ^ e := by
    calc y = t / z := htz.symm
      _ <= t / t ^ (1 - e) :=
        div_le_div_of_nonneg_left ht.le (by positivity) hwlo'
      _ = t ^ e := by
        have h := NNReal.rpow_sub ht.ne' 1 (1 - e)
        rw [NNReal.rpow_one] at h
        convert h.symm using 1 <;> congr 1 <;> ring
  have hxy : x ^ (1 - e) <= y :=
    (NNReal.rpow_le_rpow hxt (by linarith)).trans hylo
  have hyd : y <= delta ^ (e ^ 2) := by
    calc y <= t ^ e := hyhi
      _ <= (delta ^ e) ^ e := NNReal.rpow_le_rpow htd he.le
      _ = delta ^ (e ^ 2) := by rw [← NNReal.rpow_mul, ← pow_two]
  have hxd : x <= delta ^ e := hxt.trans htd
  have hsig : sourceEccentricFineScale delta M a = x / 4 := by
    dsimp [sourceEccentricFineScale, x]
    ring
  have hpar : sourceEccentricParentScale delta M a m cParent = cParent * y := by
    dsimp [sourceEccentricParentScale, y]
    ring
  have hsigma : sourceEccentricFineScale delta M a <= x := by
    rw [hsig]
    exact div_le_self (by positivity) (by norm_num)
  have hcoarse : sourceEccentricFineScale delta M a ^ (1 - e / 2) <=
      sourceEccentricParentScale delta M a m cParent := by
    have hxsmall : x ^ (e / 2) <= cParent := by
      calc x ^ (e / 2) <= (delta ^ e) ^ (e / 2) :=
            NNReal.rpow_le_rpow hxd (by positivity)
        _ = delta ^ (e ^ 2 / 2) := by rw [← NNReal.rpow_mul]; congr 1 <;> ring
        _ <= cParent := hsmall
    calc sourceEccentricFineScale delta M a ^ (1 - e / 2) <= x ^ (1 - e / 2) :=
          NNReal.rpow_le_rpow hsigma (by linarith)
      _ = x ^ (1 - e) * x ^ (e / 2) := by
        rw [← NNReal.rpow_add hx.ne']; congr 1 <;> ring
      _ <= y * cParent := mul_le_mul hxy hxsmall (by positivity) (by positivity)
      _ = sourceEccentricParentScale delta M a m cParent := by rw [hpar, mul_comm]
  have hparsmall : sourceEccentricParentScale delta M a m cParent <= 1 / 64 := by
    rw [hpar]
    calc cParent * y <= cParent * (1 / (64 * cParent)) := by gcongr; exact hyd.trans hparent
      _ = 1 / 64 := by field_simp [hcParent.ne']
  refine ⟨hd0, hdle, he, hehalf, ham, hmb, hb, hbottom m hmm.le,
    hmono a m ham.le hmm.le, hroot a hamM, hxt, htd, hylo, hyhi, hxy, hyd,
    ?_, ?_, ?_, ?_, ?_, hcoarse, hparsmall, ?_⟩
  · rw [hsig]; positivity
  · unfold sourceEccentricFineScale
    rw [le_div_iff₀ (mul_pos (by norm_num) (hrpos a))]
    have h := hroot a hamM
    nlinarith only [h, delta.2, mul_le_mul_of_nonneg_left h delta.2]
  · rw [hsig]
    exact div_le_div_of_nonneg_right hxd (by positivity)
  · rw [hsig]
    have h := hxd.trans hd.2.1
    rw [div_le_iff₀ (show (0 : NNReal) < 4 by norm_num)]
    norm_num at h ⊢
    linarith only [h]
  · rw [hpar]
    exact mul_pos hcParent (div_pos (hrpos m) (hrpos a))
  · norm_num at hparsmall ⊢
    linarith only [hparsmall]

/-- The common logarithm is exactly the existing preparation ledger, with no
runtime-dependent exponent hidden in its NNReal presentation. -/
theorem source_eccentric_logloss_eq (K : Nat) (delta : NNReal) :
    (sourceEccentricLogLoss K delta : ENNReal) = sourceFixedPreparationLoss K delta := by
  rfl

/-- The complete fixed scalar payment at one delta and one later bias. -/
noncomputable def SourceEccentricLossBounds (beta G eta66 etaOuter : Real)
    (A : NNReal) (p K : Nat) (delta : NNReal) (etaPlank zeta bias : Real)
    (sigma : NNReal) : Prop :=
  let L := sourceEccentricSelectionCost A p K delta etaPlank zeta
  let H := sourceEccentricTransportCost A L p delta bias
  1 <= L /\ 1 <= H /\
  H <= sigma ^ (-eta66) /\
  A * delta ^ (-(p : Real) * zeta) <= sigma ^ (-eta66) /\
  11664 * H ^ 12 <= sigma ^ (-eta66) /\
  9 * H ^ 4 <= sigma ^ (-eta66) /\
  sigma ^ eta66 <= delta ^ etaPlank / (A * sourceEccentricLogLoss K delta * L) /\
  delta ^ etaOuter <= delta ^ etaPlank / sourceEccentricLogLoss K delta /\
  (sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
    (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
    ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
    (3 * (H : ENNReal) ^ 3) ^ beta * (2 : ENNReal) ^ beta <=
      (delta : ENNReal) ^ (-(G / 2))

/-- Scalar budgeting uses the actual Part-B powers: CF has degree twelve,
Kdim degree four, and re-reading the aspect has degree three. All choices
precede delta and every later bias. -/
theorem source_exists_eccentric_fixed_loss_ledger
    {beta G e eta66 etaOuter : Real}
    (hbeta : 0 < beta) (hbeta1 : beta <= 1) (hG : 0 < G)
    (he : 0 < e) (hehalf : e < 1 / 2)
    (h66 : 0 < eta66) (hOuter : 0 < etaOuter)
    (A : NNReal) (hA : 1 <= A) (p K : Nat) (hp : 1 <= p) (hK : 1 <= K) :
    exists etaPlank zeta : Real, 0 < etaPlank /\ etaPlank <= 1 /\ 0 < zeta /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias -> bias <= etaPlank / 8 ->
        forall sigma : NNReal, 10 * delta <= sigma -> sigma <= delta ^ e / 4 ->
        SourceEccentricLossBounds beta G eta66 etaOuter A p K delta etaPlank zeta bias sigma := by
  let P : Real := p
  let B : Real := (P + 1) ^ 2
  have hP : 1 <= P := by dsimp [P]; exact_mod_cast hp
  have hB : 0 < B := by dsimp [B]; positivity
  have h1B : 1 <= B := by dsimp [B]; nlinarith only [hP]
  have hPB : P <= B := by dsimp [B]; nlinarith only [hP]
  have hP2B : P ^ 2 <= B := by dsimp [B]; nlinarith only [hP]
  let q := min 1 (min (etaOuter / 4)
    (min (e * eta66 / (1000 * B)) (G / (1000 * B))))
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q <= 1 := min_le_left _ _
  have hqo : q <= etaOuter / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hqe : 1000 * B * q <= e * eta66 := by
    have h : q <= e * eta66 / (1000 * B) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have := (le_div_iff₀ (by positivity : 0 < 1000 * B)).mp h
    nlinarith only [this]
  have hqG : 1000 * B * q <= G := by
    have h : q <= G / (1000 * B) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have := (le_div_iff₀ (by positivity : 0 < 1000 * B)).mp h
    nlinarith only [this]
  have hqB : q <= B * q := by nlinarith only [mul_le_mul_of_nonneg_right h1B hq.le]
  have hPq : P * q <= B * q := mul_le_mul_of_nonneg_right hPB hq.le
  have hP2q : P ^ 2 * q <= B * q := mul_le_mul_of_nonneg_right hP2B hq.le
  let C0 : NNReal := Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6)
  have hC0 : 1 <= C0 := by
    apply NNReal.coe_le_coe.mp
    change (1 : Real) <= (Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6) : Real)
    rw [Real.coe_toNNReal _ (by positivity)]
    have h := Real.one_le_rpow (by norm_num : (1 : Real) <= 3)
      (by norm_num : (0 : Real) <= 9 / 2)
    norm_num at ⊢
    nlinarith only [h]
  have hlogEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceEccentricLogLoss K delta <= delta ^ (-q) := by
    have h := Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog_pow
      (f := sourceEccentricLogLoss K) (A := 2) (B := 1) (k := K)
      (by norm_num) (by norm_num) (fun d hd hd1 => by
        change (Real.toNNReal ((2 + Real.logb 2 (1 / (d : Real))) ^ K) : Real) <= _
        rw [Real.coe_toNNReal _ (by
          apply pow_nonneg
          have h := Real.logb_nonneg (by norm_num : (1 : Real) < 2)
            (show 1 <= 1 / (d : Real) by
              rw [le_div_iff₀ (by exact_mod_cast hd)]
              simpa using (show (d : Real) <= 1 by exact_mod_cast hd1))
          linarith)]
        simp [one_div]) hq
    filter_upwards [h, self_mem_nhdsWithin] with d hd hd0
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hd0)] at hd
    exact ENNReal.coe_le_coe.mp hd
  have hconst : forall C : NNReal, ∀ᶠ delta : NNReal in 𝓝[>] 0, C <= delta ^ (-q) := by
    intro C
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (C : ENNReal)) ENNReal.coe_ne_top hq, self_mem_nhdsWithin] with d hd hd0
    rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hd0)] at hd
    exact ENNReal.coe_le_coe.mp hd
  refine ⟨q, q, hq, hq1, hq, ?_⟩
  filter_upwards [hlogEvent, hconst A, hconst C0, hconst 11664, hconst 9,
    hconst 6, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with
      delta hlog hAc hC0c h11664 h9 h6 hd
  have hd0 := hd.1
  have hd1 := hd.2.le
  have hpow : forall r s : Real, r <= s -> delta ^ (-r) <= delta ^ (-s) := by
    intro r s hrs
    exact NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1 (by linarith only [hrs])
  have hlog1 : 1 <= sourceEccentricLogLoss K delta := by
    have hl := Real.logb_nonneg (by norm_num : (1 : Real) < 2)
      (show 1 <= 1 / (delta : Real) by
        rw [le_div_iff₀ (by exact_mod_cast hd0)]
        simpa using (show (delta : Real) <= 1 by exact_mod_cast hd1))
    have h : (1 : Real) <= (2 + Real.logb 2 (1 / (delta : Real))) ^ K :=
      one_le_pow₀ (by linarith only [hl])
    exact_mod_cast h.trans (Real.le_coe_toNNReal _)
  intro bias hbias hbiasq sigma hslo hshi
  have hs0 : 0 < sigma := lt_of_lt_of_le (by positivity) hslo
  have hds : delta <= sigma := (show delta <= 10 * delta by nlinarith only [delta.2]).trans hslo
  have hsd : sigma <= delta ^ e := hshi.trans (div_le_self (by positivity) (by norm_num))
  let L := sourceEccentricSelectionCost A p K delta q q
  let H := sourceEccentricTransportCost A L p delta bias
  have hL1 : 1 <= L := by
    dsimp [L, sourceEccentricSelectionCost]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hlog1)
      (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg p)) (by linarith only [hq])))
  have hCbias : 1 <= sourceZeroPlankConstant delta bias := by
    exact one_le_mul_of_one_le_of_one_le hC0
      (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1 (by linarith only [hbias]))
  have hH1 : 1 <= H := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hL1)) (one_le_pow₀ hCbias)
  have hL : L <= delta ^ (-(4 * P * q)) := by
    calc L <= delta ^ (-q) * delta ^ (-q) * delta ^ (-(P * (q + q))) := by
          dsimp [L, sourceEccentricSelectionCost, P]
          rw [neg_mul]
          exact mul_le_mul_of_nonneg_right (mul_le_mul hAc hlog (by positivity) (by positivity)) (by positivity)
      _ = delta ^ (-((2 + 2 * P) * q)) := by
          rw [← NNReal.rpow_add hd0.ne', ← NNReal.rpow_add hd0.ne']
          congr 1 <;> ring
      _ <= delta ^ (-(4 * P * q)) := hpow _ _ (by nlinarith only [mul_le_mul_of_nonneg_right hP hq.le])
  have hCbiasUp : sourceZeroPlankConstant delta bias <= delta ^ (-(11 * q / 8)) := by
    calc sourceZeroPlankConstant delta bias <= delta ^ (-q) * delta ^ (-(3 * q / 8)) := by
          apply mul_le_mul hC0c _ (by positivity) (by positivity)
          exact NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1 (by linarith only [hbiasq])
      _ = delta ^ (-(11 * q / 8)) := by rw [← NNReal.rpow_add hd0.ne']; congr 1 <;> ring
  have hH : H <= delta ^ (-(8 * B * q)) := by
    calc H <= delta ^ (-q) * (delta ^ (-(4 * P * q))) ^ p *
          (delta ^ (-(11 * q / 8))) ^ p := by
          exact mul_le_mul (mul_le_mul hAc (pow_le_pow_left₀ (by positivity) hL p)
            (by positivity) (by positivity))
            (pow_le_pow_left₀ (by positivity) hCbiasUp p) (by positivity) (by positivity)
      _ = delta ^ (-((1 + 4 * P ^ 2 + 11 * P / 8) * q)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_natCast, ← NNReal.rpow_mul,
            ← NNReal.rpow_mul, ← NNReal.rpow_add hd0.ne', ← NNReal.rpow_add hd0.ne']
          dsimp [P]
          congr 1 <;> ring
      _ <= delta ^ (-(8 * B * q)) := hpow _ _ (by nlinarith only [hqB, hPq, hP2q])
  have hsbudget : delta ^ (-(e * eta66)) <= sigma ^ (-eta66) := by
    calc delta ^ (-(e * eta66)) = (delta ^ e) ^ (-eta66) := by
          rw [← NNReal.rpow_mul]; congr 1 <;> ring
      _ <= sigma ^ (-eta66) := NNReal.rpow_le_rpow_of_nonpos hs0 hsd (by linarith only [h66])
  have hHbudget : H <= sigma ^ (-eta66) :=
    hH.trans ((hpow _ _ (by nlinarith only [hqe, mul_pos hB hq])).trans hsbudget)
  have hcount : A * delta ^ (-(P * q)) <= sigma ^ (-eta66) := by
    calc A * delta ^ (-(P * q)) <= delta ^ (-q) * delta ^ (-(P * q)) := by gcongr
      _ = delta ^ (-((1 + P) * q)) := by rw [← NNReal.rpow_add hd0.ne']; congr 1 <;> ring
      _ <= delta ^ (-(e * eta66)) := hpow _ _ (by nlinarith only [hqe, hqB, hPq])
      _ <= sigma ^ (-eta66) := hsbudget
  have hCF : 11664 * H ^ 12 <= sigma ^ (-eta66) := by
    calc 11664 * H ^ 12 <= delta ^ (-q) * (delta ^ (-(8 * B * q))) ^ 12 := by gcongr
      _ = delta ^ (-((1 + 96 * B) * q)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, ← NNReal.rpow_add hd0.ne']
          congr 1 <;> norm_num <;> ring
      _ <= delta ^ (-(e * eta66)) := hpow _ _ (by nlinarith only [hqe, hqB, hq])
      _ <= sigma ^ (-eta66) := hsbudget
  have hKdim : 9 * H ^ 4 <= sigma ^ (-eta66) := by
    calc 9 * H ^ 4 <= delta ^ (-q) * (delta ^ (-(8 * B * q))) ^ 4 := by gcongr
      _ = delta ^ (-((1 + 32 * B) * q)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, ← NNReal.rpow_add hd0.ne']
          congr 1 <;> norm_num <;> ring
      _ <= delta ^ (-(e * eta66)) := hpow _ _ (by nlinarith only [hqe, hqB, hq])
      _ <= sigma ^ (-eta66) := hsbudget
  have hfull : sigma ^ eta66 <= delta ^ q / (A * sourceEccentricLogLoss K delta * L) := by
    rw [le_div_iff₀ (by positivity)]
    calc sigma ^ eta66 * (A * sourceEccentricLogLoss K delta * L) <=
          (delta ^ e) ^ eta66 * (delta ^ (-q) * delta ^ (-q) * delta ^ (-(4 * P * q))) := by gcongr
      _ = delta ^ (e * eta66 - (2 + 4 * P) * q) := by
          rw [← NNReal.rpow_mul, ← NNReal.rpow_add hd0.ne',
            ← NNReal.rpow_add hd0.ne', ← NNReal.rpow_add hd0.ne']
          congr 1 <;> ring
      _ <= delta ^ q := NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
          (by nlinarith only [hqe, hqB, hPq])
  have houter : delta ^ etaOuter <= delta ^ q / sourceEccentricLogLoss K delta := by
    rw [le_div_iff₀ (lt_of_lt_of_le zero_lt_one hlog1)]
    calc delta ^ etaOuter * sourceEccentricLogLoss K delta <= delta ^ etaOuter * delta ^ (-q) := by gcongr
      _ = delta ^ (etaOuter - q) := by rw [← NNReal.rpow_add hd0.ne']; congr 1 <;> ring
      _ <= delta ^ q := NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1 (by linarith only [hqo, hq])
  refine ⟨hL1, hH1, hHbudget, by simpa only [P, neg_mul] using hcount,
    hCF, hKdim, hfull, houter, ?_⟩
  have hsigInv : sigma ^ (-(G / 64)) <= delta ^ (-(G / 64)) :=
    NNReal.rpow_le_rpow_of_nonpos hd0 hds (by linarith only [hG])
  have hden : (A * delta ^ (-q)) ^ (1 - beta) <= delta ^ (-(2 * q)) := by
    calc (A * delta ^ (-q)) ^ (1 - beta) <=
          (delta ^ (-q) * delta ^ (-q)) ^ (1 - beta) := by gcongr
      _ = delta ^ (-(2 * q * (1 - beta))) := by
          rw [← NNReal.rpow_add hd0.ne', ← NNReal.rpow_mul]
          congr 1 <;> ring
      _ <= delta ^ (-(2 * q)) := hpow _ _ (by nlinarith only [mul_pos hq hbeta])
  have haspect : (3 * H ^ 3) ^ beta <= delta ^ (-(25 * B * q)) := by
    have h3 : (3 : NNReal) <= delta ^ (-q) := (by norm_num : (3 : NNReal) <= 6).trans h6
    calc (3 * H ^ 3) ^ beta <= (delta ^ (-q) * (delta ^ (-(8 * B * q))) ^ 3) ^ beta := by gcongr
      _ = delta ^ (-((1 + 24 * B) * q * beta)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul,
            ← NNReal.rpow_add hd0.ne', ← NNReal.rpow_mul]
          congr 1 <;> norm_num <;> ring
      _ <= delta ^ (-(25 * B * q)) := hpow _ _ (by
          have h := mul_le_mul_of_nonneg_left hbeta1
            (show 0 <= (1 + 24 * B) * q by positivity)
          nlinarith only [h, hqB])
  have htwo : (2 : NNReal) ^ beta <= delta ^ (-q) := by
    have h2 : (2 : NNReal) <= delta ^ (-q) := (by norm_num : (2 : NNReal) <= 6).trans h6
    calc (2 : NNReal) ^ beta <= (delta ^ (-q)) ^ beta := NNReal.rpow_le_rpow h2 hbeta.le
      _ = delta ^ (-(q * beta)) := by rw [← NNReal.rpow_mul]; congr 1 <;> ring
      _ <= delta ^ (-q) := hpow _ _ (by nlinarith only [mul_le_mul_of_nonneg_left hbeta1 hq.le])
  have hfinal : sourceEccentricLogLoss K delta * L * delta ^ (-(G / 64)) *
      sigma ^ (-(G / 64)) * (A * delta ^ (-q)) ^ (1 - beta) *
      (3 * H ^ 3) ^ beta * (2 : NNReal) ^ beta <= delta ^ (-(G / 2)) := by
    calc sourceEccentricLogLoss K delta * L * delta ^ (-(G / 64)) *
          sigma ^ (-(G / 64)) * (A * delta ^ (-q)) ^ (1 - beta) *
          (3 * H ^ 3) ^ beta * (2 : NNReal) ^ beta <=
          delta ^ (-q) * delta ^ (-(4 * P * q)) * delta ^ (-(G / 64)) *
          delta ^ (-(G / 64)) * delta ^ (-(2 * q)) * delta ^ (-(25 * B * q)) * delta ^ (-q) := by
            gcongr
      _ = delta ^ (-((4 + 4 * P + 25 * B) * q + G / 32)) := by
          repeat rw [← NNReal.rpow_add hd0.ne']
          congr 1 <;> ring
      _ <= delta ^ (-(G / 2)) := hpow _ _ (by nlinarith only [hqG, hqB, hPq, hG])
  have hfinalE := ENNReal.coe_le_coe.mpr hfinal
  simpa only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat,
    ENNReal.coe_rpow_of_ne_zero hd0.ne', ENNReal.coe_rpow_of_ne_zero hs0.ne',
    ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.mpr hbeta1),
    ENNReal.coe_rpow_of_nonneg _ hbeta.le] using hfinalE

end Kakeya.ML2Core
