/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalWindowTrial
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedArrayTrial
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedStickyTerminal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceGridChoice

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

set_option maxHeartbeats 8000000 in
theorem source_exists_direct_paid_trial
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3)))
    {beta : Real} (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta) :
    exists c : Real, 0 < c /\ 2 * c <= beta /\
    exists P : SourcePaidDescentParameters beta c,
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T P.M sourceThreadConstant)
          (Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED P.eta0 ->
        SourceDirectPaidTrialLaw Y Q P.h P.eta0
          (P.stickyAccuracy + P.stickyPayment) P.gain beta (P.loss delta) := by
  classical
  have hC : 1 <= sourceThreadConstant := by norm_num [sourceThreadConstant]
  have hA0 : 1 <= sourceBottomED := by norm_num [sourceBottomED]
  have hA1 : 1 <= sourceLevelED := by norm_num [sourceLevelED]
  have hbounded : exists (varpi : Real) (rawGain rawDens : Real -> Real),
      0 < varpi /\ varpi < 1 / 2 /\ Lemma91ParamsAt.{u} beta varpi rawGain rawDens := by
    obtain ⟨varpi, gain, dens, hp⟩ := exists_lemma91ParamsAt.{u} hbeta0 hbeta1
    refine ⟨min varpi (1 / 4), gain, dens, lt_min hp.window_pos (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    exact ⟨lt_min hp.window_pos (by norm_num), hp.gain_pos, hp.dens_pos,
      hp.gain_le_dens, fun z hz =>
        VNSUniform.VNSBody.mono_window (min_le_left _ _) (hp.body z hz)⟩
  obtain ⟨varpi, rawGain, rawDens, hvarpi0, hvarpi, hp⟩ := hbounded
  obtain ⟨M1, etaB, hM1, hetaB, hsticky⟩ := source_exists_assigned_good_sticky_exit
    sourceThreadConstant sourceBottomED sourceLevelED hSFE hC hA0 hA1
    (show 0 < beta / 8 by positivity) (show beta / 8 < 1 by linarith)
  obtain ⟨eps1, heps1, hgrid⟩ := ML2Spine.sourceSpine_exists_grid_choice
    hbeta0 hbeta1 hvarpi0 (show (0 : Real) < 1 by norm_num) hetaB
  obtain ⟨s, acc, hbudget⟩ := sourceSpine_exists_local_budget hbeta0 hbeta1 heps1 hp
  let N := ML2Spine.spineCount varpi eps1
  let e := ML2Spine.spineDiv varpi eps1
  let cSpine := ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  let ladder := sourceZeroLadder beta varpi eps1 rawGain rawDens
  let parent := sourceTerminalParent beta varpi eps1 rawGain rawDens
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hsp := ML2Spine.spineRung_isSpine hbeta0 hbeta1 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hcSpine : 0 < cSpine := ML2Spine.spineNu_pos hbeta0 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hN : 5 <= N := by have := hgrid.count_ge_4096; omega
  have he : 0 < e := hgrid.div_pos
  have he1 : e <= 1 := by
    have := hgrid.div_le_eps
    have := hgrid.eps_le_beta
    dsimp only [e]
    linarith
  have heSticky : 5 * e < etaB := by
    have := hgrid.div_le_eps
    have := hgrid.eps_le_sticky
    dsimp only [e]
    linarith
  have hparent (m : Nat) (hm : m < N) : 0 < parent m :=
    (sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm).parent_pos
  obtain ⟨M, hmesh⟩ := source_exists_fixed_tower_mesh (show 1 <= N by omega)
    (show 0 < M1 by omega) (show 0 < N by omega) hcSpine hparent
  have hMdiv : M1 ∣ M := (dvd_mul_right M1 N).trans hmesh.divisible
  have hNdiv : N ∣ M := (dvd_mul_left N M1).trans hmesh.divisible
  obtain ⟨etaA, epsBias, etaF, Kselect, D, hetaA, hetaAs, hparameters, hnonsticky⟩ :=
    source_exists_actual_terminal_nonsticky_trial hbeta0 hbeta1 heps1 hp hvarpi hKT hF
      hbudget M M1 N hmesh
  let cap := min 1 (min etaA (min etaB cSpine))
  have hcap : 0 < cap := lt_min (by norm_num) (lt_min hetaA (lt_min hetaB hcSpine))
  let eta0 := cap / 8
  have heta0 : 0 < eta0 := by positivity
  have hcap1 : cap <= 1 := min_le_left _ _
  have hcapA : cap <= etaA := (min_le_right _ _).trans (min_le_left _ _)
  have hcapB : cap <= etaB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcapC : cap <= cSpine := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hetaA3 : 3 * eta0 <= etaA := by dsimp only [eta0]; linarith
  have hetaB3 : 3 * eta0 <= etaB := by dsimp only [eta0]; linarith
  have hentry : 2 * eta0 <= ladder 1 := by
    change 2 * eta0 <= cSpine
    dsimp only [eta0]
    linarith
  have hthin : 2 * eta0 < 10 := by dsimp only [eta0]; linarith
  let h := cSpine * e ^ 2 / 8
  have hh : 0 < h := by positivity
  obtain ⟨K0, Kprep, Bprep, dprep, hK0, hKprep, hBprep, hdprep, hdprep1, hdprepM, hprepare⟩ :=
    source_exists_fixedTower_preparation M sourceBottomED sourceLevelED sourceThreadConstant
      hmesh.levels_ge_two hC hA0 hA1 heta0 hthin hh
  let Kmax := (Finset.range N).sup Kselect
  let K := Kprep + Kmax
  have hK : 1 <= K := hKprep.trans (Nat.le_add_right _ _)
  let c := min cSpine (beta / 8)
  have hc : 0 < c := lt_min hcSpine (by positivity)
  have hcc : c <= cSpine := min_le_left _ _
  have hcb : c <= beta / 8 := min_le_right _ _
  obtain ⟨q, a0, hq, ha0, ha0eta, hqeta, hgain⟩ := source_exists_paid_descent_scalar_budget heta0 hc
  let P : SourcePaidDescentParameters beta c := {
    M := M, K := K, h := h, eta0 := eta0, q := q, a0 := a0, eta := min 1 q
    stickyAccuracy := beta / 8, stickyPayment := 0, gain := 5 * cSpine
    levels_ge_two := hmesh.levels_ge_two
    loss_power_pos := hK
    potential_step_pos := hh
    input_ceiling_pos := heta0
    entrance_payment_pos := hq
    descent_payment_pos := ha0
    descent_payment_le := ha0eta
    entrance_fullness_budget := hqeta
    gain_budget := hgain
    dichotomy_exponent_pos := lt_min (by norm_num) hq
    dichotomy_exponent_le_one := min_le_left _ _
    dichotomy_exponent_le_entrance := min_le_right _ _
    sticky_accuracy_pos := by positivity
    sticky_payment_nonneg := le_rfl
    sticky_margin := by linarith
    actual_gain_margin := by linarith }
  have hladder : SourceAssignedArrayLadder N ladder e := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j _ _; exact hsp.rung_pos (j - 1)
    · intro j k _ hjk _; exact hsp.rung_mono (Nat.sub_le_sub_right hjk 1)
    · exact hsp.rung_le_div _
    · intro j hj hjN
      have hsmall := sourceSpine_six_smallness hbeta0 hbeta1 heps1 hp (j - 1)
        (show j - 1 < ML2Spine.spineCount varpi eps1 by omega)
      have hs : ladder j <= e ^ 2 * ladder (j + 1) / 100 := by
        simpa only [ladder, sourceZeroLadder, Nat.add_sub_cancel,
          Nat.sub_add_cancel hj] using hsmall.geometric
      apply hs.trans
      calc
        _ = (e ^ 2 / 100) * ladder (j + 1) := by ring
        _ <= (e / 2) * ladder (j + 1) := by
          apply mul_le_mul_of_nonneg_right _ (hsp.rung_pos j).le
          nlinarith only [he, mul_nonneg he.le (sub_nonneg.mpr he1)]
  have heq : e ^ 2 = 1 / (N : Real) := by
    simp [e, ML2Spine.spineDiv, one_div, inv_pow, Real.sq_sqrt, N]
  have harr := source_exists_actual_assigned_array_trial hN hmesh.levels_ge_two hNdiv
    he heq hladder heta0 hentry
  let B : NNReal := sourceTowerWindowConstant sourceThreadConstant sourceBottomED sourceLevelED
  have hB : 1 <= B := by norm_num [B, sourceTowerWindowConstant, sourceThreadConstant, sourceBottomED, sourceLevelED]
  obtain ⟨dsticky, hdsticky, hdsticky1, hdstickyM, hstickyApply⟩ := hsticky
    M hmesh.levels_ge_two hMdiv N B e eta0 hB he heSticky heta0 hetaB3
  refine ⟨c, hc, by linarith, P, ?_⟩
  filter_upwards [harr, hnonsticky, Ioo_mem_nhdsGT hdprep, Ioo_mem_nhdsGT hdsticky,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)]
    with delta harray hnonsticky hdprep' hdsticky' hd
  intro iota S T Q Y hinput x hxfull
  change (delta : ENNReal) ^ (2 * eta0) <=
    ShadedBody.fullness' x.family (fun i => (x.shaded i).toShadedBody) at hxfull
  have hpow (z : Real) : ENNReal.ofReal ((delta : Real) ^ z) = (delta : ENNReal) ^ z := by
    rw [← ENNReal.ofReal_rpow_of_pos (show (0 : Real) < delta by exact_mod_cast hd.1)]
    simp only [ENNReal.ofReal_coe_nnreal]
  obtain ⟨R, Qp, hrest, hinputp, hstatsp, Hprep, hprepLoss⟩ := hprepare delta hd.1 hdprep'.2
    S T Q hinput x.family x.subset x.nonempty x.shaded x.same_tubes (by
      simpa only [hpow] using hxfull)
  have hlog : (1 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)) := by
    have hone : (1 : Real) <= 1 / (delta : Real) :=
      (le_div_iff₀ (show (0 : Real) < delta by exact_mod_cast hd.1)).mpr
        (by simpa only [one_mul] using (show (delta : Real) <= 1 by exact_mod_cast hd.2.le))
    have hnonneg := Real.logb_nonneg (by norm_num : (1 : Real) < 2) hone
    linarith only [hnonneg]
  have hLossMono {k l : Nat} (hkl : k <= l) :
      sourceFixedPreparationLoss k delta <= sourceFixedPreparationLoss l delta :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hlog hkl)
  have hLossMul (k l : Nat) : sourceFixedPreparationLoss k delta * sourceFixedPreparationLoss l delta =
      sourceFixedPreparationLoss (k + l) delta := by
    unfold sourceFixedPreparationLoss
    rw [pow_add, ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans hlog) k)]
  have hprepP : 2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-Bprep)) <= P.loss delta :=
    hprepLoss.trans (hLossMono (Nat.le_add_right Kprep Kmax))
  rcases harray R T Qp x.shaded hinputp hstatsp with hgood | ⟨a, b, J, hwindow⟩
  · left
    left
    have hterminal := (hstickyApply hd.1 hdsticky'.2 Qp x.shaded hinputp hstatsp Hprep.fullness_floor hgood).1
    have hterminal' : ShadedBody.multiplicity R (fun i => (x.shaded i).toShadedBody) <=
        (delta : ENNReal) ^ (-(beta / 8)) := by simpa only [hpow] using hterminal
    exact Hprep.multiplicity.trans (mul_le_mul' hprepP (by simpa only [P, add_zero] using hterminal'))
  · let m := J - 1
    have hm : m < N := by
      have := hwindow.source_index_lower
      have := hwindow.source_index_upper
      omega
    have hJ : m + 1 = J := Nat.sub_add_cancel hwindow.source_index_lower
    have hwindow' : SourceTowerDividingWindow Qp sourceBottomED sourceLevelED N ladder e a b (m + 1) := by
      simpa only [hJ] using hwindow
    have hinputA : SourceFixedTowerInput Qp sourceBottomED sourceLevelED etaA := by
      refine ⟨hinputp.geometry, hinputp.neighbour_sharing, hinputp.maximal_density.trans ?_⟩
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_ge
        (show (0 : Real) < delta by exact_mod_cast hd.1)
        (show (delta : Real) <= 1 by exact_mod_cast hd.2.le)
        (neg_le_neg (by linarith only [heta0, hetaA3]))
    have hfullA : delta ^ etaA <= ShadedBody.fullness R (fun i => (x.shaded i).toShadedBody) := by
      have hfull' : (delta : ENNReal) ^ etaA <=
          ShadedBody.fullness' R (fun i => (x.shaded i).toShadedBody) :=
        (ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd.2.le) hetaA3).trans
          (by simpa only [hpow] using Hprep.fullness_floor)
      rw [← ShadedBody.coe_fullness] at hfull'
      exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hfull')
    obtain ⟨R', Q', Z', H, hexit⟩ := hnonsticky R T Qp x.shaded hinputA hstatsp hfullA
      m a b hm hwindow'
    have hpayment : (2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-Bprep))) *
        sourceFixedPreparationLoss (Kselect m) delta <= P.loss delta := by
      calc
        _ <= sourceFixedPreparationLoss Kprep delta * sourceFixedPreparationLoss (Kselect m) delta :=
          mul_le_mul' hprepLoss le_rfl
        _ = sourceFixedPreparationLoss (Kprep + Kselect m) delta := hLossMul _ _
        _ <= P.loss delta := hLossMono (Nat.add_le_add_left
          (Finset.le_sup (f := Kselect) (Finset.mem_range.mpr hm)) Kprep)
    rcases hexit with hgood | hdrop
    · left
      right
      have hmult : ShadedBody.multiplicity R (fun i => (x.shaded i).toShadedBody) <=
          (delta : ENNReal) ^ (5 * cSpine) * (R.card : ENNReal) ^ beta :=
        (ShadedBody.multiplicity_le_iff R (fun i => (x.shaded i).toShadedBody)).mpr hgood
      have hcard : (R.card : ENNReal) ^ beta <= (x.family.card : ENNReal) ^ beta :=
        ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card Hprep.subset) hbeta0.le
      calc
        _ <= (2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-Bprep))) *
            ((delta : ENNReal) ^ (5 * cSpine) * (R.card : ENNReal) ^ beta) :=
          Hprep.multiplicity.trans (mul_le_mul' le_rfl hmult)
        _ <= P.loss delta * ((delta : ENNReal) ^ (5 * cSpine) * (x.family.card : ENNReal) ^ beta) :=
          mul_le_mul' hprepP (mul_le_mul' le_rfl hcard)
        _ = _ := by rw [mul_assoc]
    · right
      have hsubset : R' <= x.family := H.retained.restriction.subset.trans Hprep.subset
      have hmass : x.mass <= P.loss delta * ∑ i ∈ R', volume (Z' i).shade := by
        calc
          _ <= (2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-Bprep))) *
              ∑ i ∈ R, volume (x.shaded i).shade := Hprep.mass
          _ <= (2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-Bprep))) *
              (sourceFixedPreparationLoss (Kselect m) delta * ∑ i ∈ R', volume (Z' i).shade) :=
            mul_le_mul' le_rfl H.retained.mass
          _ <= P.loss delta * ∑ i ∈ R', volume (Z' i).shade := by
            rw [← mul_assoc]
            exact mul_le_mul' hpayment le_rfl
      have hmassPos : 0 < ∑ i ∈ R', volume (Z' i).shade := by
        by_contra hn
        have hz := le_antisymm (not_lt.mp hn) (show 0 <= ∑ i ∈ R', volume (Z' i).shade from zero_le)
        rw [hz, mul_zero] at hmass
        exact (not_le_of_gt x.mass_pos) hmass
      let y : SourcePaidState S T Y := {
        family := R'
        shaded := Z'
        subset := hsubset.trans x.subset
        nonempty := H.retained.nonempty
        same_tubes := H.retained.same_tubes
        shade_subset := fun i hi => (H.retained.subshade i).trans (x.shade_subset i (hsubset hi))
        mass_pos := hmassPos }
      refine ⟨y, hsubset, (fun i _ => H.retained.subshade i), hmass, ?_⟩
      have hpoteq (R0 : Finset iota) : Qp.assignedPotential h R0 = Q.assignedPotential h R0 := by
        simp only [SourceThreadedTower.assignedPotential, SourceThreadedTower.assignedProfileExp,
          SourceThreadedTower.assignedProfile, SourceThreadedTower.assignedFootprint,
          SourceThreadedTower.retainedAssignedFibre]
        simp_rw [hrest.assignment, hrest.tubes]
        rfl
      change Q.assignedPotential h R' + 1 <= Q.assignedPotential h x.family
      have hdrop' : Qp.assignedPotential h R' + 1 <= Qp.assignedPotential h R := hdrop
      rw [hpoteq R', hpoteq R] at hdrop'
      exact hdrop'.trans Hprep.source_potential

end Kakeya.ML2Core
