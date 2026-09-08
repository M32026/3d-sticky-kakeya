/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceZeroDefectData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

open ML2Assembly

universe u

/-- The source's shifted J-indexed scalar window context comes from the
actual canonical ladder and fixed mesh, before any runtime tower is chosen. -/
theorem source_zeroDefect_window_schedule
    {beta varpi eps1 : Real} {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens)
    (M M1 Mc : Nat)
    (hmesh : SourceTowerMesh (ML2Spine.spineCount varpi eps1) M1 Mc M
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      (sourceTerminalParent beta varpi eps1 rawGain rawDens)) :
    ∀ m, m < ML2Spine.spineCount varpi eps1 ->
      SourceZeroWindowSchedule (ML2Spine.spineCount varpi eps1) M (m + 1)
        (ML2Spine.spineDiv varpi eps1) (sourceZeroLadder beta varpi eps1 rawGain rawDens)
        (sourceTerminalParent beta varpi eps1 rawGain rawDens m) := by
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hsp := ML2Spine.spineRung_isSpine hbeta0 hbeta1 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  intro m hm
  have hb := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
  refine {
    count_bound := by have := hsp.four_thousand_le_stepCount; omega
    level_bound := hmesh.levels_ge_two
    source_index_lower := by omega
    source_index_upper := by omega
    window_exponent := ?_
    rung_positive := ?_
    rung_mono := ?_
    rung_upper := ?_
    rung_step := ?_
    parent_positive := hb.parent_pos
    parent_upper := ?_
    global_mesh := hmesh.global_mesh
    parent_mesh := hmesh.all_parent_meshes m hm }
  · rw [ML2Spine.spineDiv, Real.sqrt_eq_rpow, one_div,
      show (-(1 : Real) / 2) = -(1 / 2 : Real) by ring,
      Real.rpow_neg (Nat.cast_nonneg _)]
  · intro j _ _
    exact hsp.rung_pos (j - 1)
  · intro j k _ hjk _
    exact hsp.rung_mono (Nat.sub_le_sub_right hjk 1)
  · exact hsp.rung_le_div _
  · intro j hj hjN
    have hsmall := sourceSpine_six_smallness hbeta0 hbeta1 heps1 hp (j - 1)
      (show j - 1 < ML2Spine.spineCount varpi eps1 by omega)
    simpa only [sourceZeroLadder, Nat.add_sub_cancel,
      Nat.sub_add_cancel hj] using hsmall.geometric
  · simpa only [sourceTerminalParent, sourceZeroLadder,
      show m + 1 + 1 - 1 = m + 1 by omega] using
      (show sourceTerminalParent beta varpi eps1 rawGain rawDens m <=
        ML2Spine.spineDiv varpi eps1 ^ 2 *
          ML2Spine.spineRung beta varpi eps1
            (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 64
        from min_le_left _ _)

/-- The elementary comparison reads the exact canonical first rung and raw
outputs. It is separate from the geometric producer and does not call it. -/
theorem source_zeroDefect_terminal_gain_margin
    {beta varpi eps1 : Real} {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    ∀ m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      6 * ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) <=
        sourceZeroNonstickyGain beta (ML2Spine.spineDiv varpi eps1)
          (rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16))
          (sourceTerminalParent beta varpi eps1 rawGain rawDens m) /\
      2 * sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 1) * (1 - beta) <=
        (beta * sourceTerminalParent beta varpi eps1 rawGain rawDens m / 8) / 4 := by
  intro m hm
  have hb := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
  let c := ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  let e := ML2Spine.spineDiv varpi eps1
  let q := ML2Spine.spineRung beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m
  let v := rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16)
  let P := sourceTerminalParent beta varpi eps1 rawGain rawDens m
  have hcq : c <= q := hb.margin_le_rung
  have hqP : q <= beta * P / 100 := hb.rung_le_beta_parent
  have hqv : q <= e * v / 100000 := by
    simpa only [v, sourceZeroLadder, show m + 2 - 1 = m + 1 by omega]
      using hb.rung_le_scaled_gain
  have hc0 : 0 < c := hb.margin_pos
  have hq0 : 0 < q := hc0.trans_le hcq
  have hP0 : 0 < P := hb.parent_pos
  have hv0 : 0 < e * v := by
    simpa only [v, sourceZeroLadder, show m + 2 - 1 = m + 1 by omega]
      using hb.scaled_gain_pos
  change 6 * c <= min (e * v / 8) (beta * P / 16) ∧
    2 * q * (1 - beta) <= (beta * P / 8) / 4
  constructor
  · exact le_min (by linarith only [hcq, hqv, hv0])
      (by nlinarith only [hcq, hqP, mul_pos hbeta0 hP0])
  · have hqbeta : 0 <= q * beta := mul_nonneg hq0.le hbeta0.le
    nlinarith only [hqP, hqbeta, mul_pos hbeta0 hP0]

/-- Exact algebraic consumer of a produced four-factor witness. The fixed
cardinality factor 16 is retained, and all three analytic charges are visible. -/
theorem source_zeroDefect_fourFactor_ledger
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {a p b : Nat} {beta fineCharge parentCharge outerCharge middleGain : Real}
    {loss : ENNReal} (hdelta0 : 0 < delta) (hbeta : 0 <= beta)
    (F : SourceZeroFourFactors Q Z a p b beta fineCharge parentCharge outerCharge middleGain loss) :
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      loss * (16 : ENNReal) ^ beta *
        (delta : ENNReal) ^ (middleGain - fineCharge - parentCharge - outerCharge) *
        (S.card : ENNReal) ^ beta := by
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta0.ne'
  have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        loss * ShadedBody.multiplicity (Q.cell b F.jb) (fun i => (F.fineShade i).toShadedBody) *
          ShadedBody.multiplicity F.middle (fun i => (F.middleShade i).toShadedBody) *
          ShadedBody.multiplicity F.parents (fun i => (F.parentShade i).toShadedBody) *
          ShadedBody.multiplicity F.coarse (fun i => (F.outerShade i).toShadedBody) := F.split
    _ <= loss * ((delta : ENNReal) ^ (-fineCharge) * ((Q.cell b F.jb).card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ middleGain * (F.middle.card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (-parentCharge) * (F.parents.card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (-outerCharge) * (F.coarse.card : ENNReal) ^ beta) := by
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl F.fine)
        F.middle_bound) F.parent) F.outer
    _ = loss * (delta : ENNReal) ^ (middleGain - fineCharge - parentCharge - outerCharge) *
          (((Q.cell b F.jb).card : ENNReal) * F.middle.card * F.parents.card * F.coarse.card) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta, ENNReal.mul_rpow_of_nonneg _ _ hbeta,
        ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      rw [show middleGain - fineCharge - parentCharge - outerCharge =
        ((-fineCharge + middleGain) + -parentCharge) + -outerCharge by ring]
      rw [ENNReal.rpow_add _ _ hd0 hdt, ENNReal.rpow_add _ _ hd0 hdt,
        ENNReal.rpow_add _ _ hd0 hdt]
      ring
    _ <= loss * (delta : ENNReal) ^ (middleGain - fineCharge - parentCharge - outerCharge) *
          (16 * (S.card : ENNReal)) ^ beta :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow F.card_product hbeta)
    _ = loss * (16 : ENNReal) ^ beta *
          (delta : ENNReal) ^ (middleGain - fineCharge - parentCharge - outerCharge) *
          (S.card : ENNReal) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      ring

/-- A paid child terminal transfers the actual mass to the original shading.
The strict gain margin pays its only displayed retention cost. -/
theorem source_zeroDefect_retained_terminal_payment
    {iota : Type u} {delta : NNReal} {S R : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) (Q' : SourceThreadedTower R T M C)
    (Z Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {selectionLoss terminalLoss : ENNReal} {beta gain target : Real}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1) (hbeta : 0 <= beta)
    (hretained : SourceZeroRetainedState Q Z R Z' Q' selectionLoss)
    (hterminal : ShadedBody.multiplicity R (fun i => (Z' i).toShadedBody) <=
      terminalLoss * (delta : ENNReal) ^ gain * (R.card : ENNReal) ^ beta)
    (hpayment : selectionLoss * terminalLoss * (delta : ENNReal) ^ (gain - target) <= 1) :
    (∑ i ∈ S, volume (Z i).shade) <=
      (delta : ENNReal) ^ target * (S.card : ENNReal) ^ beta *
        volume (⋃ i ∈ S, (Z i).shade) := by
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta0.ne'
  have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcard : (R.card : ENNReal) ^ beta <= (S.card : ENNReal) ^ beta :=
    ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card hretained.restriction.subset) hbeta
  have hunion : volume (⋃ i ∈ R, (Z' i).shade) <= volume (⋃ i ∈ S, (Z i).shade) := by
    apply measure_mono
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hretained.restriction.subset hi, hretained.subshade i hxi⟩
  have hmass := (ShadedBody.multiplicity_le_iff R (fun i => (Z' i).toShadedBody)).mp hterminal
  calc
    (∑ i ∈ S, volume (Z i).shade) <= selectionLoss * ∑ i ∈ R, volume (Z' i).shade :=
      hretained.mass
    _ <= selectionLoss * (terminalLoss * (delta : ENNReal) ^ gain * (R.card : ENNReal) ^ beta *
          volume (⋃ i ∈ R, (Z' i).shade)) := mul_le_mul' le_rfl hmass
    _ <= selectionLoss * (terminalLoss * (delta : ENNReal) ^ gain * (S.card : ENNReal) ^ beta *
          volume (⋃ i ∈ S, (Z i).shade)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hcard) hunion)
    _ = (selectionLoss * terminalLoss * (delta : ENNReal) ^ (gain - target)) *
          ((delta : ENNReal) ^ target * (S.card : ENNReal) ^ beta *
          volume (⋃ i ∈ S, (Z i).shade)) := by
      rw [show gain = (gain - target) + target by ring,
        ENNReal.rpow_add _ _ hd0 hdt]
      ring
    _ <= 1 * ((delta : ENNReal) ^ target * (S.card : ENNReal) ^ beta *
          volume (⋃ i ∈ S, (Z i).shade)) := mul_le_mul' hpayment le_rfl
    _ = _ := one_mul _

/-- S:4110-4125. The actual failed density test creates the natural-number
drop on this same Q, including the nontruncation condition. -/
theorem source_zeroDefect_failed_concentration_drop
    {iota : Type u} {delta : NNReal} {S R : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) {a m : Nat} {c e tau : Real}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hc : 0 < c) (he : 0 < e) (hctau : c <= tau)
    (hfailure : SourceZeroFailedConcentration Q R a m e tau) :
    Q.assignedPotential (c * e ^ 2 / 8) R + 1 <=
      Q.assignedPotential (c * e ^ 2 / 8) S := by
  have htau : 0 < tau := hc.trans_le hctau
  have hradius : ∀ k, 0 < (sourceTowerRadius delta M k : Real) := by
    intro k
    have : 0 < sourceTowerRadius delta M k := by
      unfold sourceTowerRadius
      split <;> positivity
    exact_mod_cast this
  let x : Real := (sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)
  have hx : 0 < x := div_pos (hradius a) (hradius m)
  have hlog : 0 < Real.log (1 / (delta : Real)) := by
    apply Real.log_pos
    exact (lt_div_iff₀ (show (0 : Real) < delta by exact_mod_cast hdelta0)).mpr
      (by simpa using (show (delta : Real) < 1 by exact_mod_cast hdelta1))
  have hnew := ENNReal.toReal_mono
    (show (1 / 2 : ENNReal) * ENNReal.ofReal (x ^ (tau / 2)) ≠ ⊤ by finiteness)
    hfailure.new_density
  have hold := ENNReal.toReal_mono (source_assignedProfile_ne_top Q S a m)
    hfailure.old_density
  have hxp : 0 <= x ^ (tau / 2) := Real.rpow_nonneg hx.le _
  have hxpp : 0 <= x ^ tau := Real.rpow_nonneg hx.le _
  change (Q.assignedProfile R a m).toReal <=
    ((1 / 2 : ENNReal) * ENNReal.ofReal (x ^ (tau / 2))).toReal at hnew
  change ((1 / 2 : ENNReal) * ENNReal.ofReal (x ^ tau)).toReal <=
    (Q.assignedProfile S a m).toReal at hold
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hxp, ENNReal.toReal_ofReal hxpp] at hnew hold
  have hntr : 2 <= x ^ (tau / 2) := hfailure.nontruncated
  have hmaxnew : max 1 (Q.assignedProfile R a m).toReal <= (1 / 2 : Real) * x ^ (tau / 2) :=
    max_le (by linarith only [hntr]) hnew
  have hmaxold : (1 / 2 : Real) * x ^ tau <= max 1 (Q.assignedProfile S a m).toReal :=
    hold.trans (le_max_right _ _)
  have hlnnew : Real.log (max 1 (Q.assignedProfile R a m).toReal) <=
      Real.log ((1 / 2 : Real) * x ^ (tau / 2)) :=
    Real.log_le_log (by positivity) hmaxnew
  have hlnold : Real.log ((1 / 2 : Real) * x ^ tau) <=
      Real.log (max 1 (Q.assignedProfile S a m).toReal) :=
    Real.log_le_log (by positivity) hmaxold
  rw [Real.log_mul (by norm_num : (1 / 2 : Real) ≠ 0)
      (Real.rpow_pos_of_pos hx _).ne', Real.log_rpow hx] at hlnnew hlnold
  have hgap : e ^ 2 / 2 <= Real.log x / Real.log (1 / (delta : Real)) := hfailure.logarithmic_gap
  have hgap' := (le_div_iff₀ hlog).mp hgap
  have hscaled := mul_le_mul_of_nonneg_left hgap' (show 0 <= tau / 2 by positivity)
  have hctau' := mul_le_mul_of_nonneg_right hctau
    (show 0 <= e ^ 2 / 4 * Real.log (1 / (delta : Real)) by positivity)
  have hexp : Q.assignedProfileExp R a m + 2 * (c * e ^ 2 / 8) <=
      Q.assignedProfileExp S a m := by
    unfold SourceThreadedTower.assignedProfileExp
    apply (le_div_iff₀ hlog).mpr
    rw [add_mul, div_mul_cancel₀ _ hlog.ne']
    nlinarith only [hlnnew, hlnold, hscaled, hctau']
  exact source_assignedPotential_drop Q hfailure.subset (by positivity)
    hdelta0 hdelta1 hfailure.coarse_lt_middle hfailure.middle_bound hexp

end Kakeya.ML2Core
