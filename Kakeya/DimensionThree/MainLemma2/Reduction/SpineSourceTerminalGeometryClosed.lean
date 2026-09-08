/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankSelection
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankAnalytic
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectFloorExit

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

/-- Analytic consumption of the source-ordered outcome. P exits on its
two count levels; F consumes its actual full statistical state. -/
theorem source_exists_terminal_geometry_nonsticky_exit
    {beta varpi eps1 s : Real} {rawGain rawDens : Real -> Real}
    {acc : SourceLocalAccuracyData}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens)
    (hvarpi : varpi < 1 / 2)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hbudget : SourceLocalBudget beta varpi eps1 rawGain rawDens s acc)
    (M M1 Mc : Nat)
    (hmesh : SourceTowerMesh (ML2Spine.spineCount varpi eps1) M1 Mc M
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      (sourceTerminalParent beta varpi eps1 rawGain rawDens))
    (D : Nat -> NNReal) (hD : forall m, 1 <= D m) :
    exists (etaAnalytic : Real) (epsBias : Nat -> Real),
      0 < etaAnalytic /\ etaAnalytic <= s /\
      (forall m, m < ML2Spine.spineCount varpi eps1 -> 0 < epsBias m /\
        epsBias m <= sourceTerminalParent beta varpi eps1 rawGain rawDens m / 16) /\
      forall Kselect : Nat,
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
          (R : Finset iota) (Q' : SourceThreadedTower R T M sourceThreadConstant)
          (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q' sourceBottomED sourceLevelED etaAnalytic ->
        delta ^ etaAnalytic <= ShadedBody.fullness R (fun i => (Z' i).toShadedBody) ->
        forall (m a b : Nat) (etaF : Real), m < ML2Spine.spineCount varpi eps1 ->
        SourceTerminalWindowOutcome Q Z R Q' Z'
          (ML2Spine.spineCount varpi eps1) (m + 1) sourceBottomED sourceLevelED
          (ML2Spine.spineDiv varpi eps1) (sourceZeroLadder beta varpi eps1 rawGain rawDens)
          (sourceTerminalParent beta varpi eps1 rawGain rawDens m) (epsBias m)
          etaF Kselect (D m) a b ->
        SourceDirectGoodMass S Z beta (5 * ML2Spine.spineNu beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)) \/
        SourceDirectPotentialDrop Q R
          (ML2Spine.spineNu beta varpi eps1
            (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) *
            (ML2Spine.spineDiv varpi eps1) ^ 2 / 8) := by
  set_option maxHeartbeats 4000000 in
  classical
  let N := ML2Spine.spineCount varpi eps1
  let e := ML2Spine.spineDiv varpi eps1
  let c := ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  let ladder := sourceZeroLadder beta varpi eps1 rawGain rawDens
  let P := sourceTerminalParent beta varpi eps1 rawGain rawDens
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hsp := ML2Spine.spineRung_isSpine hbeta0 hbeta1 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hc : 0 < c := ML2Spine.spineNu_pos hbeta0 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hschedule (m : Nat) (hm : m < N) :
      SourceZeroWindowSchedule N M (m + 1) e ladder (P m) := by
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
    · dsimp only [e, N]
      rw [ML2Spine.spineDiv, Real.sqrt_eq_rpow, one_div,
        show (-(1 : Real) / 2) = -(1 / 2 : Real) by ring,
        Real.rpow_neg (Nat.cast_nonneg _)]
    · intro j _ _; exact hsp.rung_pos (j - 1)
    · intro j k _ hjk _; exact hsp.rung_mono (Nat.sub_le_sub_right hjk 1)
    · exact hsp.rung_le_div _
    · intro j hj hjN
      have hsmall := sourceSpine_six_smallness hbeta0 hbeta1 heps1 hp (j - 1)
        (show j - 1 < ML2Spine.spineCount varpi eps1 by omega)
      simpa only [ladder, sourceZeroLadder, Nat.add_sub_cancel,
        Nat.sub_add_cancel hj] using hsmall.geometric
    · simpa only [P, ladder, sourceTerminalParent, sourceZeroLadder,
        show m + 1 + 1 - 1 = m + 1 by omega] using
        (show P m <= e ^ 2 *
          ML2Spine.spineRung beta varpi eps1
            (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 64
          from min_le_left _ _)
  have hparent (m : Nat) (hm : m < N) : 0 < P m :=
    (sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm).parent_pos
  have hrung (m : Nat) : 0 < ladder (m + 1) := hsp.rung_pos _
  have hmargin (m : Nat) (hm : m < N) :
      6 * c <= min (sourceZeroFloorGain e (rawGain (ladder (m + 2) / 16)))
        (beta * P m / 16) /\
      2 * ladder (m + 1) * (1 - beta) <= (beta * P m / 8) / 4 := by
    have hb := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
    let q := ML2Spine.spineRung beta varpi eps1
      (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m
    let v := rawGain (ladder (m + 2) / 16)
    have hcq : c <= q := hb.margin_le_rung
    have hqP : q <= beta * P m / 100 := hb.rung_le_beta_parent
    have hqv : q <= e * v / 100000 := by
      simpa only [v, ladder, sourceZeroLadder, show m + 2 - 1 = m + 1 by omega]
        using hb.rung_le_scaled_gain
    have hq0 : 0 < q := hc.trans_le hcq
    have hP0 : 0 < P m := hb.parent_pos
    have hv0 : 0 < e * v := by
      simpa only [v, ladder, sourceZeroLadder, show m + 2 - 1 = m + 1 by omega]
        using hb.scaled_gain_pos
    change 6 * c <= min (e * v / 8) (beta * P m / 16) /\
      2 * q * (1 - beta) <= (beta * P m / 8) / 4
    constructor
    · exact le_min (by linarith only [hcq, hqv, hv0])
        (by nlinarith only [hcq, hqP, mul_pos hbeta0 hP0])
    · have hqbeta : 0 <= q * beta := mul_nonneg hq0.le hbeta0.le
      nlinarith only [hqP, hqbeta, mul_pos hbeta0 hP0]
  have hexists (j : Fin N) := source_exists_terminal_plank_exit
    hbeta0 hbeta1 hKT hF (hparent j j.isLt)
    (show 0 < beta * P j / 8 by have := hparent j j.isLt; positivity)
    (show beta * P j / 8 <= P j * beta / 4 by nlinarith [mul_pos hbeta0 (hparent j j.isLt)])
    (show 0 <= 2 * ladder (j + 1) by have := hrung j; positivity)
    (hmargin j j.isLt).2 N M (j + 1) e ladder (hschedule j j.isLt) (D j) (hD j)
  choose etaP KP hetaP hKP hevP using hexists
  obtain ⟨etaF, KF, hetaF, hetaFs, hKF, hevF⟩ :=
    source_exists_direct_floor_exit hbeta0 hbeta1 heps1 hp hvarpi hKT hF hbudget M M1 Mc hmesh
  have heventOuter (j : Fin N) := source_exists_retained_outer_density
    N M (j + 1) sourceBottomED sourceLevelED sourceThreadConstant hmesh.levels_ge_two
    (by norm_num [sourceThreadConstant]) (by norm_num [sourceBottomED])
    (by norm_num [sourceLevelED]) ladder e (hrung j)
  let caps : Finset Real := insert etaF ((Finset.univ : Finset (Fin N)).image etaP)
  have hcaps : caps.Nonempty := ⟨etaF, by simp [caps]⟩
  let eta := caps.min' hcaps
  have heta : 0 < eta := by
    have hmem := caps.min'_mem hcaps
    simp only [caps, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    rcases hmem with h | ⟨j, h⟩
    · change 0 < caps.min' hcaps
      change caps.min' hcaps = etaF at h
      rw [h]
      exact hetaF
    · change 0 < caps.min' hcaps
      change etaP j = caps.min' hcaps at h
      rw [← h]
      exact hetaP j
  have hetaFle : eta <= etaF := caps.min'_le _ (by simp [caps])
  have hetaPle (j : Fin N) : eta <= etaP j := caps.min'_le _ (by simp [caps])
  let epsBias : Nat -> Real := fun m => if hm : m < N then
    min (P m / 16) (etaP ⟨m, hm⟩ / 8) / 2 else 1
  have hbias (m : Nat) (hm : m < N) : 0 < epsBias m /\
      epsBias m <= min (P m / 16) (etaP ⟨m, hm⟩ / 8) := by
    have hmin : 0 < min (P m / 16) (etaP ⟨m, hm⟩ / 8) :=
      lt_min (by have := hparent m hm; positivity) (by have := hetaP ⟨m, hm⟩; positivity)
    simp only [epsBias, dif_pos hm]
    exact ⟨by positivity, by linarith only [hmin]⟩
  have hloss (K : Nat) : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceFixedPreparationLoss K delta <= (delta : ENNReal) ^ (-c) := by
    simpa only [sourceFixedPreparationLoss, one_div, one_mul] using
      VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
        (A := (2 : Real)) (B := (1 : Real)) (by norm_num) (by norm_num) K hc
  refine ⟨eta, epsBias, heta, hetaFle.trans hetaFs, ?_, ?_⟩
  · intro m hm
    exact ⟨(hbias m hm).1, (hbias m hm).2.trans (min_le_left _ _)⟩
  · intro Kselect
    filter_upwards [hevF, Filter.eventually_all.mpr hevP,
      Filter.eventually_all.mpr heventOuter,
      hloss (Kselect + KF), Filter.eventually_all.mpr (fun j : Fin N => hloss (Kselect + KP j)),
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hFdelta hPdelta hOuter hLF hLP hd
    intro iota S T Q Z R Q' Z' hinput hfull m a b etaInput hm H
    have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
    have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hd1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd.2.le
    have hinput_mono {z : Real} (hz : eta <= z) :
        SourceFixedTowerInput Q' sourceBottomED sourceLevelED z := by
      refine ⟨hinput.geometry, hinput.neighbour_sharing, hinput.maximal_density.trans ?_⟩
      apply ENNReal.ofReal_le_ofReal
      exact Real.rpow_le_rpow_of_exponent_ge (show (0 : Real) < delta by exact_mod_cast hd.1)
        (show (delta : Real) <= 1 by exact_mod_cast hd.2.le) (neg_le_neg hz)
    have hfull_mono {z : Real} (hz : eta <= z) :
        delta ^ z <= ShadedBody.fullness R (fun i => (Z' i).toShadedBody) :=
      (NNReal.rpow_le_rpow_of_exponent_ge hd.1 hd.2.le hz).trans hfull
    have hpayment {K : Nat} {gain : Real}
        (hl : sourceFixedPreparationLoss (Kselect + K) delta <= (delta : ENNReal) ^ (-c))
        (hg : 6 * c <= gain)
        (ht : ShadedBody.multiplicity R (fun i => (Z' i).toShadedBody) <=
          sourceFixedPreparationLoss K delta * (delta : ENNReal) ^ gain *
            (R.card : ENNReal) ^ beta) : SourceDirectGoodMass S Z beta (5 * c) := by
      have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
        Real.logb_nonneg (by norm_num)
          ((le_div_iff₀ (show (0 : Real) < delta by exact_mod_cast hd.1)).mpr
            (by simpa using (show (delta : Real) <= 1 by exact_mod_cast hd.2.le)))
      have hbase : 0 <= 2 + Real.logb 2 (1 / (delta : Real)) := by linarith only [hlog]
      have hmul : sourceFixedPreparationLoss Kselect delta * sourceFixedPreparationLoss K delta =
          sourceFixedPreparationLoss (Kselect + K) delta := by
        unfold sourceFixedPreparationLoss
        rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hbase Kselect)]
      have hcard : (R.card : ENNReal) ^ beta <= (S.card : ENNReal) ^ beta :=
        ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card H.retained.restriction.subset)
          hbeta0.le
      apply (ShadedBody.multiplicity_le_iff S (fun i => (Z i).toShadedBody)).mp
      calc _ <= sourceFixedPreparationLoss Kselect delta *
            (sourceFixedPreparationLoss K delta * (delta : ENNReal) ^ gain *
              (R.card : ENNReal) ^ beta) := H.retained.multiplicity.trans (mul_le_mul' le_rfl ht)
        _ = sourceFixedPreparationLoss (Kselect + K) delta * (delta : ENNReal) ^ gain *
            (R.card : ENNReal) ^ beta := by rw [← hmul]; ring
        _ <= (delta : ENNReal) ^ (-c) * (delta : ENNReal) ^ (6 * c) *
            (S.card : ENNReal) ^ beta :=
          mul_le_mul' (mul_le_mul' hl (ENNReal.rpow_le_rpow_of_exponent_ge hd1 hg)) hcard
        _ = _ := by rw [← ENNReal.rpow_add _ _ hd0 hdt]; congr 2 <;> ring
    rcases H.alternative with hplank | ⟨hstats, hfloor | hdrop⟩
    · left
      let j : Fin N := ⟨m, hm⟩
      obtain ⟨F, hstatsP⟩ := hplank
      have houter : Kakeya.maxDensity (Q'.indexSet a) (fun i => (Q'.tube a i).toConvexSpaceBody) <=
          (delta : ENNReal) ^ (-(2 * ladder (m + 1))) := by
        simpa only [neg_mul] using hOuter j R T Q' hinput.geometry a b H.upper
      have hterminal := (hPdelta j (epsBias m) (hbias m hm).1 (hbias m hm).2
        R T Q' Z' (hinput_mono (hetaPle j)) (hfull_mono (hetaPle j))
        a b F.level F.short F.middle F.long hstatsP H.upper F.in_window F.factors houter).2
      have hgain : 6 * c <= beta * P m / 8 := by
        have hsmall : 6 * c <= beta * P m / 16 := (hmargin m hm).1.trans (min_le_right _ _)
        nlinarith only [hsmall, mul_pos hbeta0 (hparent m hm)]
      exact hpayment (hLP j) hgain hterminal
    · left
      obtain ⟨F⟩ := hfloor
      have hterminal := hFdelta R T Q' Z' (hinput_mono hetaFle) hstats
        (hfull_mono hetaFle) m a b hm H.upper F
      have hg : 6 * c <= sourceZeroFloorGain e (rawGain (ladder (m + 2) / 16)) :=
        (hmargin m hm).1.trans (min_le_left _ _)
      exact hpayment hLF hg hterminal
    · right
      simpa only [SourceDirectPotentialDrop, sourceZeroLadder, show 1 - 1 = 0 from rfl,
        ML2Spine.spineNu] using hdrop

end Kakeya.ML2Core
