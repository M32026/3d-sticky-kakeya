/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowConstruction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQPaidMiddleSelection

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly ML2Reduction VeryNotSticky

universe u

set_option maxHeartbeats 8000000 in
/-- S:4482-4500,4672-4685, with the direct F input and explicit seed-transfer
payment. The actual same-Q construction includes all VNS antecedents. Eta
and its uniform local gain margin are chosen before delta and every family;
the analytic power payment does not change the trial's restart mass ledger. -/
theorem source_exists_direct_paid_floor_geometry
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
      (sourceTerminalParent beta varpi eps1 rawGain rawDens)) :
    exists (eta : Real) (K : Nat), 0 < eta /\ eta <= s /\ 5 * eta < 10 /\ 1 <= K /\
      (forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
        sourceZeroFloorGain (ML2Spine.spineDiv varpi eps1)
            (rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16)) +
          acc.epsf m + acc.epsp m +
          (acc.epsc m + sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 1)) +
          s + 2 * eta <= sourceTerminalNetGain beta varpi eps1 rawGain rawDens m) /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED eta ->
        SourceTowerStatistics Q Z ->
        delta ^ eta <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (m a b : Nat), m < ML2Spine.spineCount varpi eps1 ->
        SourceParentUpperWindow Q sourceBottomED sourceLevelED
          (ML2Spine.spineCount varpi eps1) (sourceZeroLadder beta varpi eps1 rawGain rawDens)
          (ML2Spine.spineDiv varpi eps1) a b (m + 1) ->
        forall P : SourceDirectFloor Q (ML2Spine.spineDiv varpi eps1)
          (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2))
          (sourceTerminalParent beta varpi eps1 rawGain rawDens m) a b,
        exists F : SourceRetainedFourFactors Q Z a P.parent b beta
            (acc.epsf m) (acc.epsp m)
            (acc.epsc m + sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 1))
            (sourceTerminalNetGain beta varpi eps1 rawGain rawDens m)
            (sourceFixedPreparationLoss K delta *
              (ShadedBody.fullness S (fun i => (Z i).toShadedBody) : ENNReal)⁻¹ ^ 2),
          (F.seam.stageLoss : ENNReal) ^ 3 <= sourceFixedPreparationLoss K delta /\
          delta ^ (5 * eta) <= F.lambda /\
          sourceFixedPreparationLoss K delta *
              (ShadedBody.fullness S (fun i => (Z i).toShadedBody) : ENNReal)⁻¹ ^ 2 <=
            sourceFixedPreparationLoss K delta *
              ENNReal.ofReal ((delta : Real) ^ (-2 * eta)) /\
          Nonempty (SourceRetainedMiddleAnalysis Q F.seam beta varpi
            (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16)
            (rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16))
            (rawDens (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16))
            (rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16) / 2)
            (ML2Spine.spineDiv varpi eps1)) := by
  classical
  have hBudget {beta varpi eps1 s eta : Real} {rawGain rawDens : Real -> Real}
      {acc : SourceLocalAccuracyData}
      (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
      (hp : Lemma91ParamsAt beta varpi rawGain rawDens)
      (hbudget : SourceLocalBudget beta varpi eps1 rawGain rawDens s acc)
      (heta : eta <= s) (m : Nat) (hm : m < ML2Spine.spineCount varpi eps1) :
      sourceZeroFloorGain (ML2Spine.spineDiv varpi eps1)
          (rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16)) +
        acc.epsf m + acc.epsp m +
        (acc.epsc m + sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 1)) +
        s + 2 * eta <= sourceTerminalNetGain beta varpi eps1 rawGain rawDens m := by
    have hb := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
    have hs := hbudget.accuracy_le_scaled_gain m hm
    rw [hbudget.fine_eq, hbudget.parent_charge_eq, hbudget.parent_accuracy_eq,
      hbudget.coarse_charge_eq, hbudget.outer_accuracy_eq, hbudget.coarse_density_eq]
    simp only [sourceZeroFloorGain, sourceZeroLadder, Nat.add_sub_cancel,
      show m + 2 - 1 = m + 1 by omega, sourceTerminalNetGain,
      sourceMiddleNetGain, sourceMiddleGain]
    nlinarith only [hb.fixed_cost, hb.margin_pos, hb.scaled_gain_pos, hs, heta]
  have hLeaf {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
      (Q : SourceThreadedTower S T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (hst : SourceTowerStatistics Q Z) {lam a : NNReal} (hdelta : delta <= 1)
      (hfull : lam <= ShadedBody.fullness S (fun i => (Z i).toShadedBody))
      (ha : 2 * a * Tube.volume_le.C 3 <= lam * Tube.le_volume.c 3) :
      forall j, j ∈ S -> (a : ENNReal) * volume (T j).carrier <= volume (Z j).shade := by
    intro j hj
    have hcell (i : iota) (hi : i ∈ S) : Q.cell M i = {i} := by
      ext l
      simp only [SourceThreadedTower.cell, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hl, he⟩
        rwa [Q.bottom_place l hl] at he
      · rintro rfl
        exact ⟨hi, Q.bottom_place _ hi⟩
    have hshade (i : iota) (hi : i ∈ S) : volume (Z i).shade <= 2 * volume (Z j).shade := by
      have h := hst.fibre_mass M le_rfl i (Q.bottom_index.symm ▸ hi)
        j (Q.bottom_index.symm ▸ hj)
      simpa only [hcell i hi, hcell j hj, Finset.sum_singleton] using h
    have hlow : (lam : ENNReal) * ((S.card : ENNReal) *
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal)^2)) <=
        ∑ i ∈ S, volume (Z i).shade := by
      apply ShadedBody.coe_fullness_mul_le_sum_volume_shade S
        (fun i => (Z i).toShadedBody) hfull
      intro i hi
      simpa using Tube.le_volume (Z i).toTube
    have hupp : (∑ i ∈ S, volume (Z i).shade) <=
        (S.card : ENNReal) * (2 * volume (Z j).shade) := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hshade
    have hcard0 : (S.card : ENNReal) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨j, hj⟩).ne'
    have hcancel : (lam : ENNReal) * (Tube.le_volume.c 3 : ENNReal) *
          (delta : ENNReal)^2 <= 2 * volume (Z j).shade := by
      apply (ENNReal.mul_le_mul_iff_right hcard0 (by simp)).mp
      convert hlow.trans hupp using 1 <;> first | ring | rfl
    apply (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp
    calc
      2 * ((a : ENNReal) * volume (T j).carrier) <=
          2 * ((a : ENNReal) * ((Tube.volume_le.C 3 : ENNReal) * (delta : ENNReal)^2)) := by
        gcongr
        simpa using Tube.volume_le hdelta (T j)
      _ = (2 * (a : ENNReal) * (Tube.volume_le.C 3 : ENNReal)) * (delta : ENNReal)^2 := by ring
      _ <= ((lam : ENNReal) * (Tube.le_volume.c 3 : ENNReal)) * (delta : ENNReal)^2 := by
        exact mul_le_mul_right' (by exact_mod_cast ha) _
      _ <= 2 * volume (Z j).shade := hcancel
  have hLeafSmall (eta : Real) (heta : eta < 10) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        2 * delta ^ (10 : Real) * Tube.volume_le.C 3 <=
          delta ^ eta * Tube.le_volume.c 3 := by
    have hexp : 0 < 10 - eta := sub_pos.mpr heta
    have hlim : Tendsto (fun delta : NNReal =>
        2 * delta ^ (10 - eta) * Tube.volume_le.C 3) (𝓝[>] 0) (𝓝 0) := by
      have hcont : Continuous (fun delta : NNReal =>
          2 * delta ^ (10 - eta) * Tube.volume_le.C 3) :=
        (continuous_const.mul (NNReal.continuous_rpow_const hexp.le)).mul continuous_const
      simpa only [NNReal.zero_rpow hexp.ne', mul_zero, zero_mul] using
        (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    filter_upwards [hlim.eventually (gt_mem_nhds (Tube.le_volume.c_pos 3)),
      self_mem_nhdsWithin] with delta hsmall hdelta
    have heq : delta ^ (10 : Real) = delta ^ (10 - eta) * delta ^ eta := by
      rw [← NNReal.rpow_add (ne_of_gt hdelta)]
      congr 1
      ring
    calc
      2 * delta ^ (10 : Real) * Tube.volume_le.C 3 =
          (2 * delta ^ (10 - eta) * Tube.volume_le.C 3) * delta ^ eta := by rw [heq]; ring
      _ <= Tube.le_volume.c 3 * delta ^ eta := mul_le_mul_right' hsmall.le _
      _ = delta ^ eta * Tube.le_volume.c 3 := mul_comm _ _
  have hParameters (M A0 A1 C : Nat) {e varpi tau parent etaC R : Real}
      (hM : 2 <= M) (hA0 : 1 <= A0) (hA1 : 1 <= A1) (hC : 1 <= C)
      (he : 0 < e) (hev : e <= varpi / 10) (hv0 : 0 < varpi) (hv1 : varpi < 1 / 2)
      (ht : 0 < tau) (hte : tau <= e) (hp : 0 < parent)
      (hparent : parent <= e^2 * tau / 64) (hmesh : 8 / parent <= (M : Real))
      (heta : 0 < etaC) (hetab : etaC <= e * varpi * (tau / 16) / 100)
      (hR : 2 <= R) (hRN : (Tube.normalization.C 3 : Real) <= R) :
      SourceQCoverParameters M A0 A1 C e varpi (tau / 16) etaC R /\
        1 / (M : Real) < e * (1 - 2 * e) := by
    have hMr : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
    have hmesh' : 1 / (M : Real) <= parent / 8 := by
      rw [div_le_iff₀ hp] at hmesh
      rw [div_le_div_iff₀ hMr (by norm_num : (0 : Real) < 8)]
      nlinarith only [hmesh]
    have hgrid : 1 / (M : Real) <= e^2 * tau / 512 := by
      nlinarith only [hmesh', hparent]
    have he1 : e < 1 / 20 := by linarith
    have ht1 : tau <= 1 := by linarith
    have hgeom : e^2 * tau <= e * varpi / 10 := by
      have h1 := mul_le_mul_of_nonneg_left ht1 (sq_nonneg e)
      have h2 := mul_le_mul_of_nonneg_left hev he.le
      nlinarith only [h1, h2]
    have hgeom' : e^2 * tau <= e * varpi * tau / 10 := by
      have hh := mul_le_mul_of_nonneg_left hev (mul_nonneg he.le ht.le)
      nlinarith only [hh]
    have hmeshMargin : 1 / (M : Real) < e * varpi / 100 := by
      nlinarith only [hgrid, hgeom, mul_pos he hv0]
    have hcount : 6 * etaC + 3 / (M : Real) < e * varpi * (tau / 16) / 4 := by
      have hgrid3 : 3 / (M : Real) <= 3 * (e^2 * tau / 512) := by
        simpa only [div_eq_mul_inv, mul_one, one_mul] using mul_le_mul_of_nonneg_left hgrid (by norm_num : (0 : Real) <= 3)
      nlinarith only [hgrid3, hgeom', hetab, mul_pos (mul_pos he hv0) ht]
    refine ⟨{
      levels := hM
      bottom_ed := hA0
      level_ed := hA1
      threads := hC
      window_pos := he
      window_upper := by linarith
      vns_window_pos := hv0
      vns_window_upper := hv1
      excess_pos := by positivity
      excess_upper := by linarith
      input_pos := heta
      radius_lower := hR
      normalization := hRN
      mesh_margin := hmeshMargin
      count_margin := hcount }, ?_⟩
    have hh := mul_lt_mul_of_pos_left hv1 he
    nlinarith only [hmeshMargin, hh, he1, he, mul_pos he (show 0 < 1 / 20 - e by linarith)]
  have hChoice {e varpi zeta v d s etaL : Real}
      (he : 0 < e) (hv : 0 < varpi) (hz : 0 < zeta)
      (hv0 : 0 < v) (hd : 0 < d) (hs : 0 < s) (hL : 0 < etaL) :
      exists q gamma etaMax : Real,
        0 < q /\ 0 < gamma /\ gamma <= q /\ 2 * gamma < varpi * zeta / 16 /\
        3 * gamma < 3 * q /\ 3 * q <= d /\ v / 2 + 3 * q <= v /\
        0 < etaMax /\ etaMax <= s /\ 5 * etaMax <= etaL /\
        5 * etaMax <= e * gamma / 4 /\ etaMax <= e * varpi * zeta / 100 /\
        q = min v d / 12 := by
    let q := min v d / 12
    let gamma := min (q / 4) (varpi * zeta / 128)
    let etaMax := min s (min (etaL / 10) (min (e * gamma / 100) (e * varpi * zeta / 100)))
    have hq : 0 < q := div_pos (lt_min hv0 hd) (by norm_num)
    have hg : 0 < gamma := lt_min (by dsimp [q]; positivity) (by positivity)
    have hgq : gamma <= q / 4 := min_le_left _ _
    have hgz : gamma <= varpi * zeta / 128 := min_le_right _ _
    have hqv : q <= v / 12 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hqd : q <= d / 12 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hmax : 0 < etaMax := by dsimp [etaMax]; positivity
    have hmaxs : etaMax <= s := min_le_left _ _
    have hmaxL : etaMax <= etaL / 10 := (min_le_right _ _).trans (min_le_left _ _)
    have hmaxg : etaMax <= e * gamma / 100 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hmaxz : etaMax <= e * varpi * zeta / 100 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨q, gamma, etaMax, hq, hg, ?_, ?_, ?_, ?_, ?_, hmax, hmaxs, ?_, ?_, hmaxz, rfl⟩
    · linarith
    · nlinarith only [hgz, mul_pos hv hz]
    · linarith
    · linarith
    · linarith
    · linarith
    · nlinarith only [hmaxg, mul_pos he hg]
  have hRungBound {beta e tau v d parent rung : Real}
      (hbeta : beta <= 1) (he : 0 < e) (hp : 0 < parent)
      (hparent : parent <= sourceParentMinimum e tau v d)
      (hrung : rung <= beta * parent / 100) :
      rung <= e * (min v d / 12) / 1000 := by
    have hpv : parent <= e * v / 1000 := hparent.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hpd : parent <= e * d / 1000 := hparent.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hrp : rung <= parent / 100 := by
      have hh := mul_le_mul_of_nonneg_right hbeta hp.le
      nlinarith only [hrung, hh]
    have hpmin : parent <= e * min v d / 1000 := by
      rw [mul_min_of_nonneg _ _ he.le, ← min_div_div_right (by norm_num : (0 : Real) <= 1000)]
      exact le_min hpv hpd
    have hem : 0 < e * min v d := by linarith
    nlinarith only [hrp, hpmin, hem]
  have hFinite {N : Nat} (f : Fin N -> Real) (hf : forall m, 0 < f m) :
      exists eta : Real, 0 < eta /\ eta <= 1 /\ forall m, eta <= f m := by
    let E : Finset Real := insert 1 (Finset.univ.image f)
    have hE : E.Nonempty := Finset.insert_nonempty _ _
    let eta := E.min' hE
    have hpos (x : Real) (hx : x ∈ E) : 0 < x := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · norm_num
      · obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hx
        exact hf m
    refine ⟨eta, hpos eta (Finset.min'_mem E hE), Finset.min'_le E 1 (Finset.mem_insert_self _ _), ?_⟩
    intro m
    exact Finset.min'_le E (f m) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩))
  have hCard (eta : Real) (heta : eta <= 1) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          {M C A0 A1 : Nat} (Q : SourceThreadedTower S T M C),
          SourceFixedTowerInput Q A0 A1 eta ->
          (S.card : Real) <= (delta : Real)^(-(5 : Real)) := by
    obtain ⟨d0, hd0, hbound⟩ := exists_threshold_const_le_rpow_neg
      (C := max 1 (Tube.card_le_of_densityIn_le.C 3)) (le_max_left _ _) (by norm_num : (0 : Real) < 1)
    filter_upwards [Ioo_mem_nhdsGT hd0, Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)]
      with delta hd hd1
    intro iota S T M C A0 A1 Q hinput
    have hball (i : iota) (hi : i ∈ S) : (T i).carrier <= Metric.closedBall 0 1 :=
      (hinput.geometry.original_ball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
    have hraw := Tube.card_le_of_densityIn_le hd.1.ne' hball
      ((Kakeya.le_maxDensity _ _ _).trans hinput.maximal_density)
    have hcardE : (S.card : ENNReal) <=
        (Tube.card_le_of_densityIn_le.C 3 : ENNReal) * (delta : ENNReal)^(-eta - 2) := by
      have hpow : (delta : ENNReal)^(-(2 : Int)) = (delta : ENNReal)^(-(2 : Real)) := by
        convert (ENNReal.rpow_intCast (delta : ENNReal) (-2 : Int)).symm using 1 <;> norm_num
      norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
        Int.reduceSub, Int.reduceNeg] at hraw
      rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hd.1), ENNReal.ofReal_coe_nnreal,
        hpow, mul_assoc, ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hd.1.ne') ENNReal.coe_ne_top] at hraw
      simpa only [sub_eq_add_neg] using hraw
    have hC : (Tube.card_le_of_densityIn_le.C 3 : ENNReal) <= (delta : ENNReal)^(-(1 : Real)) := by
      rw [← ENNReal.coe_rpow_of_ne_zero hd.1.ne']
      exact ENNReal.coe_le_coe.mpr ((le_max_right _ _).trans (hbound delta hd.1 hd.2.le))
    have hfive : (S.card : ENNReal) <= (delta : ENNReal)^(-(5 : Real)) := by
      calc (S.card : ENNReal) <= (Tube.card_le_of_densityIn_le.C 3 : ENNReal) * (delta : ENNReal)^(-eta-2) := hcardE
        _ <= (delta : ENNReal)^(-(1 : Real)) * (delta : ENNReal)^(-eta-2) := mul_le_mul_right' hC _
        _ = (delta : ENNReal)^(-1 + (-eta-2)) := by
          rw [ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hd.1.ne') ENNReal.coe_ne_top]
        _ <= (delta : ENNReal)^(-(5 : Real)) := ENNReal.rpow_le_rpow_of_exponent_ge
          (by exact_mod_cast hd1.2.le) (by linarith)
    have hfiveN : (S.card : NNReal) <= delta^(-(5 : Real)) := by
      apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_natCast, ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hfive
    exact_mod_cast hfiveN
  have hOuter
      (N M J A0 A1 C : Nat) (hM : 2 <= M)
      (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
      (eta : Nat -> Real) (e eps : Real) (heta : 0 < eta J) (heps : 0 < eps) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
        forall a b : Nat, SourceParentUpperWindow Q A0 A1 N eta e a b J ->
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
          (delta : ENNReal) ^ (-(eta J + eps)) := by
    classical
    let D : Nat := sourceTowerWindowConstant C A0 A1
    let K : NNReal := 1280 ^ 6 * (D : NNReal) ^ N
    have hD : 1 <= D := by
      dsimp [D, sourceTowerWindowConstant]
      omega
    have hDN : (1 : ENNReal) <= (D : ENNReal) ^ N := by
      exact one_le_pow₀ (by exact_mod_cast hD)
    filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : Real) < 1),
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
        (ENNReal.coe_ne_top (r := K)) heps,
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with delta ht hK hd
    intro iota S T Q hgeometry a b hwindow
    have hM0 : 0 < M := by omega
    have hroot : sourceTowerRadius delta M 0 = (1 / 40 : NNReal) := by
      simp [sourceTowerRadius, hM0]
    have hrootcard : ((Q.indexSet 0).card : ENNReal) <= (1280 : ENNReal) ^ 6 := by
      have hh := hgeometry.coarse_card 0 hM0
      rw [hroot] at hh
      norm_num at hh
      exact_mod_cast hh
    have hδ1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd.2.le
    have hone : (1 : ENNReal) <= (delta : ENNReal) ^ (-eta J) := by
      simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (neg_nonpos.mpr heta.le)
    have hbound : Kakeya.maxDensity (Q.indexSet a)
        (fun i => (Q.tube a i).toConvexSpaceBody) <= (K : ENNReal) *
          (delta : ENNReal) ^ (-eta J) := by
      by_cases ha : a = 0
      · subst a
        refine (Kakeya.maxDensity_le_card _ _).trans (hrootcard.trans ?_)
        calc
          (1280 : ENNReal) ^ 6 <= (1280 : ENNReal) ^ 6 * (D : ENNReal) ^ N :=
            le_mul_of_one_le_right' hDN
          _ <= (K : ENNReal) * (delta : ENNReal) ^ (-eta J) := by
            simpa [K] using le_mul_of_one_le_right' (a := (K : ENNReal)) hone
      · have haM : a < M := hwindow.coarse_lt_fine.trans_le hwindow.fine_bound
        have haradius : (delta : Real) <= (sourceTowerRadius delta M a : Real) := by
          have hh := ht.2.2.2.2.1 a haM
          exact_mod_cast (show delta <= sourceTowerRadius delta M a by nlinarith)
        have hratio : (sourceTowerRadius delta M 0 : Real) /
            (sourceTowerRadius delta M a : Real) <= (delta : Real)⁻¹ := by
          rw [hroot]
          have hδ : (0 : Real) < delta := by exact_mod_cast hd.1
          norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
          calc (1 / 40 : Real) / (sourceTowerRadius delta M a : Real) <=
              1 / (sourceTowerRadius delta M a : Real) := by gcongr <;> norm_num
            _ <= (delta : Real)⁻¹ := by simpa [one_div] using one_div_le_one_div_of_le hδ haradius
        have hpow : ENNReal.ofReal
            (((sourceTowerRadius delta M 0 : Real) / (sourceTowerRadius delta M a : Real)) ^ eta J) <=
            (delta : ENNReal) ^ (-eta J) := by
          have hp := Real.rpow_le_rpow (by positivity) hratio heta.le
          have hp' := ENNReal.ofReal_le_ofReal hp
          simpa [Real.inv_rpow (show (0 : Real) <= delta by positivity),
            ← Real.rpow_neg (show (0 : Real) <= delta by positivity),
            ← ENNReal.ofReal_rpow_of_pos (show (0 : Real) < delta by exact_mod_cast hd.1)] using hp'
        have hcover : Q.indexSet a <= (Q.indexSet 0).biUnion (Q.fibre 0 a) := by
          intro j hj
          obtain ⟨i, hi, hij⟩ := Q.place_surjective a haM.le j hj
          refine Finset.mem_biUnion.mpr ⟨Q.place 0 i, Q.place_mem 0 hM0.le i hi, ?_⟩
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hij⟩
        calc
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
              ∑ j ∈ Q.indexSet 0, Kakeya.maxDensity (Q.fibre 0 a j)
                (fun i => (Q.tube a i).toConvexSpaceBody) :=
            Kakeya.maxDensity_le_sum_of_subset_biUnion _ hcover
          _ <= ∑ j ∈ Q.indexSet 0,
              (D : ENNReal) ^ N * (delta : ENNReal) ^ (-eta J) := by
            refine Finset.sum_le_sum fun j hj => (hwindow.coarse_density (by omega) j hj).trans ?_
            exact mul_le_mul_left' hpow _
          _ = ((Q.indexSet 0).card : ENNReal) *
              ((D : ENNReal) ^ N * (delta : ENNReal) ^ (-eta J)) := by simp
          _ <= (1280 : ENNReal) ^ 6 *
              ((D : ENNReal) ^ N * (delta : ENNReal) ^ (-eta J)) := by gcongr
          _ = (K : ENNReal) * (delta : ENNReal) ^ (-eta J) := by simp [K, mul_assoc]
    refine hbound.trans ?_
    calc
      (K : ENNReal) * (delta : ENNReal) ^ (-eta J) <=
          (delta : ENNReal) ^ (-eps) * (delta : ENNReal) ^ (-eta J) := by gcongr
      _ = (delta : ENNReal) ^ (-(eta J + eps)) := by
        rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hd.1.ne') ENNReal.coe_ne_top]
        congr 1
        ring
  have hMiddle (M N J : Nat) (schedule : Nat -> Real)
      (e varpi tau etaParent etaC R beta v d q gamma : Real)
      (hparams : SourceQCoverParameters M sourceBottomED sourceLevelED sourceThreadConstant
        e varpi (tau/16) etaC R)
      (hmesh : 1/(M : Real) < e*(1-2*e))
      (hbeta : 0 <= beta) (hv : 0 < v) (hq : 0 < q) (hg : 0 < gamma)
      (hgq : gamma <= q) (hcard : 2*gamma < varpi*(tau/16)/16)
      (hmass : 3*gamma < 3*q) (h3q : 3*q <= d) (hgain : v/2+3*q <= v)
      (hrung : 0 <= schedule J) (hrungq : schedule J <= e*q/4)
      (hetag : 5*etaC <= e*gamma/4)
      (hraw : ∀ᶠ rho : NNReal in 𝓝[>] 0, Lemma91At.{u} beta varpi (tau/16) v d rho) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceTowerGeometry Q sourceBottomED sourceLevelED -> SourceTowerStatistics Q Z ->
        forall (a b : Nat),
          SourceParentUpperWindow Q sourceBottomED sourceLevelED N schedule e a b J ->
        forall (P : SourceDirectFloor Q e tau etaParent a b) (lambda : NNReal) (loss : ENNReal)
          (X : SourceQMiddleSeam Q Z a P.parent b lambda loss),
        delta^(5*etaC) <= lambda -> (delta : Real)^(6*etaC) <= X.theta0 Q ->
        (S.card : Real) <= (delta : Real)^(-(5 : Real)) ->
        Nonempty (SourceRetainedMiddleAnalysis Q X beta varpi (tau/16) v d (v/2) e) /\
        ShadedBody.multiplicity X.middle (fun i => (X.middleShade i).toShadedBody) <=
          (delta : ENNReal)^(e*v/4) * (X.middle.card : ENNReal)^beta := by
    have hCover {iota : Type u} {delta : NNReal} {S : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
        (Q : SourceThreadedTower S T M C)
        {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
        {a p b : Nat} {lambda : NNReal} {loss : ENNReal}
        (X : SourceQMiddleSeam Q Z a p b lambda loss)
        {e tau etaParent etaC R : Real}
        (F : SourceZeroFloor Q e tau etaParent a b p)
        (hd : 0 < delta) (hd1 : delta < 1) (hd40 : delta <= 1 / 40)
        (hsmall : delta < (40 : NNReal)^(-(M : Real)))
        (hM : 0 < M) (he : 0 < e) (hehalf : e < 1 / 2)
        (hmesh : 1 / (M : Real) < e * (1 - 2 * e))
        (hsep : (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <= (delta : Real)^e)
        (hscales : forall k, k <= M -> delta <= sourceTowerRadius delta M k)
        (hstep : forall k, k < M -> sourceTowerRadius delta M (k + 1) <= sourceTowerRadius delta M k / 2)
        (htheta : (delta : Real)^(6 * etaC) <= X.theta0 Q)
        (hR : 0 < R) (hRnorm : (Tube.normalization.C 3 : Real) <= R) :
        exists (rho : NNReal) (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
            (sourceTowerRadius delta M b) rho R 3),
          SourceQCoverInput Q a p b X.jp X.middle X.middleShade rho e (tau / 16) etaC /\
          SourceQNormalizedRows hsit hR (Q.tube p X.jp) X.middle X.middleShade := by
      have hParentRatio {delta : NNReal} {M a p b : Nat} {e : Real}
          (hd : 0 < delta) (hd1 : delta < 1) (hM : 0 < M)
          (he : 0 < e) (hehalf : e < 1 / 2)
          (hmesh : 1 / (M : Real) < e * (1 - 2 * e))
          (hap : a <= p) (hpb : p < b) (hb : b <= M)
          (hmono : Antitone (fun k : Nat => (sourceTowerRadius delta M k : Real)))
          (hsep : (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
            (delta : Real)^e)
          (hbefore : forall k, SourceTowerWindow delta M e a b k -> p < k) :
          (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M p : Real) <=
            ((sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real))^(1 - e) := by
        let r := fun k : Nat => (sourceTowerRadius delta M k : Real)
        have hdR : 0 < (delta : Real) := by exact_mod_cast hd
        have hdR1 : (delta : Real) < 1 := by exact_mod_cast hd1
        have hMr : 0 < (M : Real) := by exact_mod_cast hM
        have hradEq (k : Nat) : r k = bridgeGrid M (delta : Real) k := by
          simp only [r, sourceTowerRadius, bridgeGrid]
          split <;> simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one,
            NNReal.coe_ofNat, NNReal.coe_rpow]
        have hrpos (k : Nat) : 0 < r k := by rw [hradEq]; exact bridgeGrid_pos hdR k
        let t := r b / r a
        let q := (delta : Real)^(1 / (M : Real))
        have ht0 : 0 < t := div_pos (hrpos b) (hrpos a)
        have ht1 : t < 1 := hsep.trans_lt (Real.rpow_lt_one hdR.le hdR1 he)
        have hq0 : 0 < q := Real.rpow_pos_of_pos hdR _
        have hgap : t^(1 - 2 * e) < q := by
          calc
            t^(1 - 2 * e) <= ((delta : Real)^e)^(1 - 2 * e) :=
              Real.rpow_le_rpow ht0.le hsep (by linarith)
            _ = (delta : Real)^(e * (1 - 2 * e)) := (Real.rpow_mul hdR.le _ _).symm
            _ < q := Real.rpow_lt_rpow_of_exponent_gt hdR hdR1 hmesh
        let cut := r b / t^(1 - e)
        have hcut0 : 0 < cut := div_pos (hrpos b) (Real.rpow_pos_of_pos ht0 _)
        have hcutb : r b <= cut := by
          apply (le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)).mpr
          exact mul_le_of_le_one_right (hrpos b).le (Real.rpow_le_one ht0.le ht1.le (by linarith))
        have hcuta : cut < r a := by
          rw [div_lt_iff₀ (Real.rpow_pos_of_pos ht0 _)]
          have ht : t < t^(1 - e) := by
            simpa using Real.rpow_lt_rpow_of_exponent_gt ht0 ht1 (show 1 - e < 1 by linarith)
          simpa only [mul_comm] using (div_lt_iff₀ (hrpos a)).mp ht
        let candidates := (Finset.range (b + 1)).filter (fun k => r k <= cut)
        have hmemB : b ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcutb⟩
        have hne : candidates.Nonempty := ⟨b, hmemB⟩
        let k := candidates.min' hne
        have hkmem := candidates.min'_mem hne
        obtain ⟨hkb, hkcut⟩ := Finset.mem_filter.mp hkmem
        have hkle : k <= b := by have := Finset.mem_range.mp hkb; omega
        have hak : a < k := by
          by_contra hn
          have hh : r a <= r k := hmono (by omega)
          exact (not_le.mpr hcuta) (hh.trans hkcut)
        have hkpos : 0 < k := by omega
        have hprev : cut < r (k - 1) := by
          by_contra hn
          have hmem : k - 1 ∈ candidates := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), le_of_not_gt hn⟩
          have hh := candidates.min'_le (k - 1) hmem
          omega
        have hstep : q * r (k - 1) <= r k := by
          have hh := (bridgeGrid_step hM hdR (show k - 1 < M by omega)).1
          rw [← hradEq, ← hradEq, show k - 1 + 1 = k by omega] at hh
          exact hh
        have hcutLow : q * cut < r k := (mul_lt_mul_of_pos_left hprev hq0).trans_le hstep
        have hratioUpper : r b / r k < t^e := by
          have hgap' : t^(1 - e) < q * t^e := by
            have hh := mul_lt_mul_of_pos_right hgap (Real.rpow_pos_of_pos ht0 e)
            rw [← Real.rpow_add ht0] at hh
            simpa only [show 1 - 2 * e + e = 1 - e by ring] using hh
          have hcross : r b < t^e * (q * cut) := by
            dsimp [cut]
            rw [← mul_div_assoc, ← mul_div_assoc, lt_div_iff₀ (Real.rpow_pos_of_pos ht0 _)]
            nlinarith only [mul_lt_mul_of_pos_left hgap' (hrpos b)]
          exact (div_lt_iff₀ (hrpos k)).mpr
            (hcross.trans (mul_lt_mul_of_pos_left hcutLow (Real.rpow_pos_of_pos ht0 _)))
        have hkbStrict : k < b := by
          by_contra hn
          have hkEq : k = b := by omega
          rw [hkEq, div_self (hrpos b).ne'] at hratioUpper
          exact (not_lt.mpr (Real.rpow_le_one ht0.le ht1.le he.le)) hratioUpper
        have hwindow : SourceTowerWindow delta M e a b k := by
          refine ⟨hak, hkbStrict, ?_, hratioUpper.le⟩
          apply (le_div_iff₀ (hrpos k)).mpr
          have hh := (le_div_iff₀ (Real.rpow_pos_of_pos ht0 (1 - e))).mp hkcut
          simpa only [mul_comm] using hh
        have hpk := hbefore k hwindow
        have hcutp : cut < r p := hprev.trans_le (hmono (by omega : p <= k - 1))
        apply le_of_lt
        apply (div_lt_iff₀ (hrpos p)).mpr
        have hh := mul_lt_mul_of_pos_left hcutp (Real.rpow_pos_of_pos ht0 (1 - e))
        simpa only [cut, mul_div_cancel₀ _ (Real.rpow_pos_of_pos ht0 (1 - e)).ne'] using hh
      let r := sourceTowerRadius delta M
      have hrpos (k : Nat) : 0 < r k := by
        dsimp [r, sourceTowerRadius]
        split <;> positivity
      have hmono : Antitone (fun k : Nat => (r k : Real)) := by
        apply antitone_nat_of_succ_le
        intro k
        by_cases hk : k < M
        · have hh := hstep k hk
          have hhR : (r (k + 1) : Real) <= (r k : Real) / 2 := by exact_mod_cast hh
          have hpos : 0 < (r k : Real) := by exact_mod_cast hrpos k
          linarith
        · simp only [r, sourceTowerRadius, if_neg hk, if_neg (show ¬k + 1 < M by omega)]
          rfl
      have hpM : p < M := F.parent_lt_fine.trans_le F.fine_bound
      have hpbNat := F.parent_lt_fine
      have hratio := hParentRatio hd hd1 hM he hehalf hmesh F.coarse_le_parent
        F.parent_lt_fine F.fine_bound hmono hsep F.parent_before_window
      have hp40 : r p <= 1 / 40 := by
        change sourceTowerRadius delta M p <= 1 / 40
        rw [sourceTowerRadius, if_pos hpM]
        calc
          (1 / 40 : NNReal) * delta ^ ((p : Real) / (M : Real)) <= (1 / 40) * 1 :=
            mul_le_mul_right (NNReal.rpow_le_one hd1.le (by positivity)) _
          _ = _ := mul_one _
      have hp1 : r p <= 1 := hp40.trans (by norm_num [div_le_iff₀])
      have hpbhalf : r b <= r p / 2 := by
        have hh : r b <= r (p + 1) := by exact_mod_cast hmono (by omega : p + 1 <= b)
        exact hh.trans (hstep p hpM)
      have hpb : r b <= r p := hpbhalf.trans (div_le_self (by positivity) (by norm_num))
      let rho := r b / (2 * r p)
      have hrho : 0 < rho := div_pos (hrpos b) (mul_pos (by norm_num) (hrpos p))
      have hrpR : 0 < (r p : Real) := by exact_mod_cast hrpos p
      have hrbR : 0 < (r b : Real) := by exact_mod_cast hrpos b
      have hdR : 0 < (delta : Real) := by exact_mod_cast hd
      have hrhoEq : (rho : Real) = ((r b : Real) / (r p : Real)) / 2 := by
        dsimp [rho]
        push_cast
        ring
      have hrhoQuarter : (rho : Real) <= 1 / 4 := by
        rw [hrhoEq]
        have hh : (r b : Real) <= (r p : Real) / 2 := by exact_mod_cast hpbhalf
        rw [div_le_iff₀ (by norm_num : (0 : Real) < 2), div_le_iff₀ hrpR]
        linarith
      let hsit : Tube.IsRescalingSituation (r p) (r b) rho R 3 :=
        { pos_ambient := hrpos p
          inner_le_ambient := hpb
          ambient_le_one := hp1
          pos_out := hrho
          out_le_quarter := hrhoQuarter
          out_le_ratio := by rw [hrhoEq]; exact div_le_self (by positivity) (by norm_num)
          normalizationConst_le_radius := hRnorm }
      have hlow : 20 * delta <= rho := by
        apply (le_div_iff₀ (mul_pos (by norm_num : (0 : NNReal) < 2) (hrpos p))).mpr
        have hh := hscales b F.fine_bound
        have hh' : 40 * r p <= 1 := by
          simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : NNReal) < 40)).mp hp40
        nlinarith [mul_le_mul_left hh' delta]
      have hupper : (rho : Real) <= (delta : Real)^(e / 2) / 2 := by
        rw [hrhoEq]
        apply div_le_div_of_nonneg_right _ (by norm_num)
        calc
          (r b : Real) / (r p : Real) <= ((r b : Real) / (r a : Real))^(1 - e) := hratio
          _ <= ((delta : Real)^e)^(1 - e) := Real.rpow_le_rpow (by positivity) hsep (by linarith)
          _ = (delta : Real)^(e * (1 - e)) := (Real.rpow_mul hdR.le _ _).symm
          _ <= (delta : Real)^(e / 2) := Real.rpow_le_rpow_of_exponent_ge hdR
            (by exact_mod_cast hd1.le) (by nlinarith)
      have hparents : X.jp ∈ Q.fibre a p X.ja := X.parents_subset X.parent_member
      have hinput : SourceQCoverInput Q a p b X.jp X.middle X.middleShade rho e (tau / 16) etaC :=
        { delta_pos := hd
          delta_small := hsmall
          coarse_le_parent := F.coarse_le_parent
          parent_lt_middle := F.parent_lt_fine
          middle_bound := F.fine_bound
          parent_member := by
            obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hparents
            exact heq ▸ Q.place_mem p hpM.le i (Finset.mem_filter.mp hi).1
          family_nonempty := ⟨X.jb, X.middle_member⟩
          family_subset := X.middle_subset
          family_tubes := X.middle_tubes
          same_parent_retention := by
            have hNpos : 0 < ((Q.fibre p b X.jp).card : Real) := by
              exact_mod_cast Finset.card_pos.mpr (show (Q.fibre p b X.jp).Nonempty from
                ⟨X.jb, X.middle_subset X.middle_member⟩)
            exact (le_div_iff₀ hNpos).mp htheta
          rho_eq := rfl
          rho_lower := hlow
          rho_upper := hupper
          original_window_separation := hsep
          parent_ratio := by
            apply hratio.trans
            apply le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _)
            exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdR (by exact_mod_cast hd1.le)
              (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
          parent_before_window := F.parent_before_window
          count_floor := fun k hk => F.floor X.ja (X.coarse_subset X.coarse_member) X.jp hparents
            k hk (F.parent_before_window k hk) }
      refine ⟨rho, hsit, hinput, ?_⟩
      have hsub (i : iota) (hi : i ∈ X.middle) : (X.middleShade i).carrier <= (Q.tube p X.jp).carrier := by
        have hanc := sourceQ_ancestor_fibre_identities Q F.parent_lt_fine.le F.fine_bound
        have hmem := X.middle_subset hi
        rw [hanc.2.2.2 X.jp hinput.parent_member] at hmem
        obtain ⟨hiQ, heq⟩ := Finset.mem_filter.mp hmem
        have hh := hanc.2.2.1 i hiQ
        change (Q.tube b i).carrier <= (Q.tube p (sourceQAncestor Q p b i)).carrier at hh
        rw [heq] at hh
        have hcar := congrArg (fun U : Tube (r b) (EuclideanSpace Real (Fin 3)) => U.carrier) (X.middle_tubes i)
        rw [hcar]
        exact hh
      exact sourceQ_normalized_rows hsit hR (Q.tube p X.jp) X.middle X.middleShade
        (by rw [hrhoEq]; nlinarith [div_pos hrbR hrpR]) hsub
    have hBounds {delta rho ra rb lam C : NNReal} {e eta rung q gamma d : Real}
        (hd : 0 < delta) (hd1 : delta <= 1) (hr : 0 < rho)
        (he : 0 < e) (hq : 0 < q) (hg : 0 < gamma) (hgq : gamma <= q)
        (h3q : 3*q <= d) (hrung : 0 <= rung) (hrungq : rung <= e*q/4)
        (hetag : 5*eta <= e*gamma/4) (hC : 0 < C)
        (hpay : C <= delta ^ (-(e*gamma/4)))
        (hscale : rho <= delta ^ (e/2)) (hra : ra <= 1) (hrb : delta <= rb)
        (hfull : delta ^ (5*eta) <= lam) :
        rho ^ gamma <= C⁻¹ * lam /\
        (C : ENNReal) * ENNReal.ofReal (((ra : Real)/(rb : Real))^rung) <=
          (rho : ENNReal)^(-q) /\
        ENNReal.ofReal (((ra : Real)/(rb : Real))^rung) <=
          (rho : ENNReal)^(-(d-q)) := by
      have hrb0 : 0 < rb := hd.trans_le hrb
      have hratio : ra / rb <= delta ^ (-(1 : Real)) := by
        rw [NNReal.rpow_neg, NNReal.rpow_one, ← one_div]
        exact div_le_div₀ (by positivity) hra hd hrb
      have hdens : (ra/rb)^rung <= delta^(-rung) := by
        calc (ra/rb)^rung <= (delta^(-(1 : Real)))^rung := NNReal.rpow_le_rpow hratio hrung
          _ = delta^(-rung) := by rw [← NNReal.rpow_mul]; congr 1; ring
      have hfull' : rho^gamma * C <= lam := by
        calc rho^gamma * C <= (delta^(e/2))^gamma * delta^(-(e*gamma/4)) :=
              mul_le_mul' (NNReal.rpow_le_rpow hscale hg.le) hpay
          _ = delta^(e*gamma/4) := by
            rw [← NNReal.rpow_mul, ← NNReal.rpow_add hd.ne']
            congr 1
            ring
          _ <= delta^(5*eta) := NNReal.rpow_le_rpow_of_exponent_ge hd hd1 hetag
          _ <= lam := hfull
      have hn : C * (ra/rb)^rung <= rho^(-q) := by
        calc C * (ra/rb)^rung <= delta^(-(e*gamma/4)) * delta^(-rung) := mul_le_mul' hpay hdens
          _ = delta^(-(e*gamma/4)-rung) := by rw [← NNReal.rpow_add hd.ne']; congr 1
          _ <= delta^(-(e*q/2)) := NNReal.rpow_le_rpow_of_exponent_ge hd hd1 (by
            have hh := mul_le_mul_of_nonneg_left hgq he.le
            nlinarith only [hh, hrungq])
          _ = (delta^(e/2))^(-q) := by rw [← NNReal.rpow_mul]; congr 1; ring
          _ <= rho^(-q) := NNReal.rpow_le_rpow_of_nonpos hr hscale (by linarith)
      have ho : (ra/rb)^rung <= rho^(-(d-q)) := by
        calc (ra/rb)^rung <= delta^(-rung) := hdens
          _ <= delta^(-(e*(d-q)/2)) := NNReal.rpow_le_rpow_of_exponent_ge hd hd1 (by
            have hh := mul_le_mul_of_nonneg_left h3q he.le
            nlinarith only [hh, hrungq, mul_pos he hq])
          _ = (delta^(e/2))^(-(d-q)) := by rw [← NNReal.rpow_mul]; congr 1; ring
          _ <= rho^(-(d-q)) := NNReal.rpow_le_rpow_of_nonpos hr hscale (by linarith)
      refine ⟨?_, ?_, ?_⟩
      · rw [mul_comm C⁻¹ lam, ← div_eq_mul_inv, le_div_iff₀ hC]
        exact hfull'
      · have hco := ENNReal.coe_le_coe.mpr hn
        rw [← NNReal.coe_div, ← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
        simpa only [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hr.ne'] using hco
      · have hco := ENNReal.coe_le_coe.mpr ho
        rw [← NNReal.coe_div, ← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal]
        simpa only [ENNReal.coe_rpow_of_ne_zero hr.ne'] using hco
    have hPullback {P : NNReal -> Prop} {e : Real} (he : 0 < e)
        (hP : ∀ᶠ rho : NNReal in 𝓝[>] 0, P rho) :
        ∀ᶠ delta : NNReal in 𝓝[>] 0,
          forall rho : NNReal, 0 < rho -> rho <= delta ^ (e/2) -> P rho := by
      obtain ⟨r0, hr0, hsmall⟩ := ML2Reduction.exists_threshold_of_eventually_nhdsGT hP
      filter_upwards [Ioo_mem_nhdsGT (NNReal.rpow_pos hr0 (p := 2/e))] with delta hd
      intro rho hr hs
      apply hsmall rho hr
      apply hs.trans
      calc delta^(e/2) <= (r0^(2/e))^(e/2) := NNReal.rpow_le_rpow hd.2.le (by positivity)
        _ = r0 := by
          rw [← NNReal.rpow_mul, show (2/e)*(e/2) = 1 by field_simp, NNReal.rpow_one]
    have hConstant (C : NNReal) {k : Real} (hk : 0 < k) :
        ∀ᶠ delta : NNReal in 𝓝[>] 0, C <= delta ^ (-k) := by
      obtain ⟨d0, hd0, hbound⟩ := exists_threshold_const_le_rpow_neg
        (C := max 1 C) (le_max_left _ _) hk
      filter_upwards [Ioo_mem_nhdsGT hd0] with delta hd
      exact (le_max_right _ _).trans (hbound delta hd.1 hd.2.le)
    have hRadii (M : Nat) (hM : 2 <= M) :
        ∀ᶠ delta : NNReal in 𝓝[>] 0,
          0 < delta /\ delta <= 1 / 40 /\
          (forall k, k <= M -> delta <= sourceTowerRadius delta M k /\
            sourceTowerRadius delta M k <= 1) /\
          (forall k l, k <= l -> l <= M -> sourceTowerRadius delta M l <= sourceTowerRadius delta M k) := by
      filter_upwards [source_eventually_fixed_tower_radius_conditions M hM (by norm_num : (0 : Real) < 1),
        Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1 / 40)] with delta hrad hd
      have hstep (k : Nat) (hk : k < M) : sourceTowerRadius delta M (k + 1) <= sourceTowerRadius delta M k :=
        (hrad.2.2.2.2.2 k hk).trans (div_le_self (by positivity) (by norm_num))
      have hmono (k l : Nat) (hkl : k <= l) :
          l <= M -> sourceTowerRadius delta M l <= sourceTowerRadius delta M k := by
        induction l, hkl using Nat.le_induction with
        | base => exact fun _ => le_refl _
        | succ l hkl ih =>
          intro hl
          exact (hstep l (by omega)).trans (ih (by omega))
      refine ⟨hrad.2.2.1, hd.2.le, ?_, hmono⟩
      intro k hk
      refine ⟨?_, (hmono 0 k (Nat.zero_le k) hk).trans hrad.2.2.2.1⟩
      by_cases hkm : k < M
      · have hh := hrad.2.2.2.2.1 k hkm
        nlinarith
      · have heq : k = M := by omega
        simp [heq, sourceTowerRadius]
    have he := hparams.window_pos
    have hR : 0 < R := by linarith [hparams.radius_lower]
    have hR1 : 1 <= R := by linarith [hparams.radius_lower]
    have hC : 0 < outerLoss R := zero_lt_one.trans_le (one_le_outerLoss hR1)
    have hK0 : 0 < sourceQMiddleCardPower e := by
      dsimp [sourceQMiddleCardPower]
      omega
    have hselected := sourceQ_exists_selected_middle_estimate.{u} M sourceBottomED sourceLevelED sourceThreadConstant
      (sourceQMiddleCardPower e) e varpi (tau/16) etaC R beta v d q gamma (v/2)
      hparams hK0 hbeta hq hg hgq hcard hmass h3q (by positivity) hgain
    obtain ⟨r0, hr0, huni⟩ := exists_threshold_coe_const_le_rpow_neg
      (C := ShadedTube.ssfUniformConst 3) (ShadedTube.one_le_ssfUniformConst 3) (by linarith : 0 < d)
    have huniEvent : ∀ᶠ rho : NNReal in 𝓝[>] 0,
        ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) <= (rho : ENNReal)^(-d) := by
      filter_upwards [Ioo_mem_nhdsGT hr0] with rho hr
      exact huni rho hr.1 hr.2.le
    filter_upwards [hselected, hPullback he hraw, hPullback he huniEvent,
      hConstant (outerLoss R) (by positivity : 0 < e*gamma/4),
      hRadii M hparams.levels,
      source_eventually_fixed_tower_radius_conditions M hparams.levels he,
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1),
      Ioo_mem_nhdsGT (by positivity : (0 : NNReal) < (40 : NNReal)^(-(M : Real)))]
      with delta hselect hVNS hUni hpay hrad hsteps hd1 hdsmall
    intro iota S T Q Z hgeo hstats a b hwindow P lambda loss X hfull htheta hScard
    obtain ⟨hd, hd40, hscales, hmono⟩ := hrad
    have hpM : P.parent < M := P.geometry.parent_lt_fine.trans_le P.geometry.fine_bound
    have hhalf : e < 1/2 := by
      have h1 := hparams.window_upper
      have h2 := hparams.vns_window_upper
      linarith
    obtain ⟨rho, hsit, hinput, hnormal⟩ := hCover Q X P.geometry hd hd1.2 hd40 hdsmall.2
      (by omega : 0 < M) he hhalf hmesh hwindow.separation
      (fun k hk => (hscales k hk).1) hsteps.2.2.2.2.2 htheta hR hparams.normalization
    have hrho : 0 < rho := hsit.pos_out
    have hrho1 : rho <= 1 := by
      have hh := hsit.out_le_quarter
      exact_mod_cast (show (rho : Real) <= 1 by linarith)
    have hscale : (rho : Real) <= (delta : Real)^(e/2) :=
      hinput.rho_upper.trans (div_le_self (Real.rpow_nonneg delta.coe_nonneg _) (by norm_num))
    have hscaleN : rho <= delta^(e/2) := by exact_mod_cast hscale
    have hraw' : Lemma91At.{u} beta varpi (tau/16) v d rho := hVNS rho hrho hscaleN
    have huni' := hUni rho hrho hscaleN
    obtain ⟨hfullN, hdensN, hdensO⟩ := hBounds hd hd1.2.le hrho he hq hg hgq h3q hrung hrungq hetag hC
      hpay hscaleN (hscales a (hwindow.coarse_lt_fine.le.trans hwindow.fine_bound)).2 (hscales b hwindow.fine_bound).1
      (hfull.trans X.middle_fullness)
    obtain ⟨hcontain, hK, hcardN, hdensityO, hdensityN, hfullO⟩ :=
      sourceQ_retained_middle_original_bounds Q X.middleShade hinput schedule hwindow hsit hR he hrho1
        hScard hfullN hdensN hdensO
    obtain ⟨D, E, U0, U1, hret, hdown, hmiddle⟩ :=
      hselect S T Q Z hgeo hstats a P.parent b X.jp X.middle X.middleShade rho hinput hsit hR
        hcardN hfullO hdensityN hdensityO hraw'
    refine ⟨⟨{
      rho := rho
      R := R
      etaC := etaC
      q := q
      gamma := gamma
      R_pos := hR
      rho_pos := hrho
      rho_le_one := hrho1
      q_pos := hq
      gamma_pos := hg
      gamma_le_q := hgq
      density_budget := h3q
      gain_budget := hgain
      scale_gain := hscale
      cover_parameters := hparams
      cover_input := hinput
      situation := hsit
      normalized := hnormal
      D := D
      E := E
      U0 := U0
      U1 := U1
      retention := hret
      downstairs := hdown
      raw_vns := hraw'
      uniformity_budget := huni' }⟩, ?_⟩
    convert hmiddle using 1
    congr 2
    ring
  let N := ML2Spine.spineCount varpi eps1
  let e := ML2Spine.spineDiv varpi eps1
  let schedule := sourceZeroLadder beta varpi eps1 rawGain rawDens
  let tau := fun m : Nat => schedule (m+2)
  let v := fun m : Nat => rawGain (tau m/16)
  let d := fun m : Nat => rawDens (tau m/16)
  let parent := sourceTerminalParent beta varpi eps1 rawGain rawDens
  have hN : 0 < N := by have := hmesh.count_pos; omega
  have hM : 2 <= M := hmesh.levels_ge_two
  have hs : 0 < s := hbudget.accuracy_pos
  have he : 0 < e := ML2Spine.spineDiv_pos hp.window_pos heps1
  have hparent (m : Fin N) : SourceParentMinBounds beta
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      e (schedule (m+1)) (tau m) (v m) (d m) := by
    simpa only [schedule, tau, v, d, sourceZeroLadder, Nat.add_sub_cancel,
      show (m : Nat)+2-1 = m+1 by omega] using
      sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m m.isLt
  have hparentEq (m : Nat) : parent m = sourceParentMinimum e (tau m) (v m) (d m) := by
    simp only [parent, sourceTerminalParent, e, tau, v, d, schedule, sourceZeroLadder,
      show m+2-1 = m+1 by omega]
  obtain ⟨etaL, hL, hThree⟩ := sourceQ_exists_three_factor_bounds.{u}
    hbeta0 hbeta1 hKT hs hs hs M sourceBottomED sourceLevelED sourceThreadConstant hM
  have hchoose (m : Fin N) : exists q gamma etaMax : Real,
      0 < q /\ 0 < gamma /\ gamma <= q /\ 2 * gamma < varpi * (tau m/16) / 16 /\
      3 * gamma < 3 * q /\ 3 * q <= d m /\ v m / 2 + 3 * q <= v m /\
      0 < etaMax /\ etaMax <= s /\ 5 * etaMax <= etaL /\
      5 * etaMax <= e * gamma / 4 /\ etaMax <= e * varpi * (tau m/16) / 100 /\
      q = min (v m) (d m) / 12 := by
    exact hChoice he hp.window_pos (by have := (hparent m).next_pos; positivity)
      (hparent m).raw_gain_pos (hparent m).raw_dens_pos hs hL
  choose q gamma etaMax hq hg hgq hcard hmass h3q hgain hmax hmaxs hmaxL hmaxg hmaxz hqeq using hchoose
  obtain ⟨eta, heta, heta1, hetamax⟩ := hFinite etaMax hmax
  let m0 : Fin N := ⟨0, hN⟩
  have hetas : eta <= s := (hetamax m0).trans (hmaxs m0)
  have hetaL : 5*eta <= etaL := by linarith [hetamax m0, hmaxL m0]
  have heta10 : 5*eta < 10 := by linarith
  obtain ⟨K, hK, hPaid⟩ := sourceQ_exists_paid_mass_coupled_middle.{u} M sourceBottomED sourceLevelED
    sourceThreadConstant hM (by norm_num [sourceThreadConstant])
    (by norm_num [sourceBottomED]) (by norm_num [sourceLevelED]) eta heta heta10
  let R : Real := max 2 (Tube.normalization.C 3 : Real)
  have hR2 : 2 <= R := le_max_left _ _
  have hRN : (Tube.normalization.C 3 : Real) <= R := le_max_right _ _
  have hMidAll : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall m : Fin N,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M sourceThreadConstant)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceTowerGeometry Q sourceBottomED sourceLevelED -> SourceTowerStatistics Q Z ->
      forall (a b : Nat),
        SourceParentUpperWindow Q sourceBottomED sourceLevelED N schedule e a b (m+1) ->
      forall (P : SourceDirectFloor Q e (tau m) (parent m) a b) (lambda : NNReal) (loss : ENNReal)
        (X : SourceQMiddleSeam Q Z a P.parent b lambda loss),
      delta^(5*eta) <= lambda -> (delta : Real)^(6*eta) <= X.theta0 Q ->
      (S.card : Real) <= (delta : Real)^(-(5 : Real)) ->
      Nonempty (SourceRetainedMiddleAnalysis Q X beta varpi (tau m/16) (v m) (d m) (v m/2) e) /\
      ShadedBody.multiplicity X.middle (fun i => (X.middleShade i).toShadedBody) <=
        (delta : ENNReal)^(e*v m/4) * (X.middle.card : ENNReal)^beta := by
    rw [Filter.eventually_all]
    intro m
    have hb := hparent m
    have hprepare := sourceSpine_middle_preparation hbeta0 hbeta1 heps1 hp m m.isLt
    have hev : e <= varpi/10 := hprepare.div_le_window
    have hpar : parent m <= e^2*tau m/64 := by
      rw [hparentEq]
      exact min_le_left _ _
    have hpc : SourceQCoverParameters M sourceBottomED sourceLevelED sourceThreadConstant
        e varpi (tau m/16) eta R /\ 1/(M : Real) < e*(1-2*e) :=
      hParameters M sourceBottomED sourceLevelED sourceThreadConstant hM
        (by norm_num [sourceBottomED]) (by norm_num [sourceLevelED]) (by norm_num [sourceThreadConstant])
        he hev hp.window_pos hvarpi hb.next_pos hb.next_le_div
        (by simpa only [hparentEq] using hb.parent_pos) hpar (hmesh.all_parent_meshes m m.isLt)
        heta ((hetamax m).trans (hmaxz m)) hR2 hRN
    have hrung : schedule (m+1) <= e*(min (v m) (d m)/12)/1000 :=
      hRungBound hbeta1 he hb.parent_pos (by rw [← hparentEq]) hb.rung_le_beta_parent
    have hrungq : schedule (m+1) <= e*q m/4 := by
      rw [← hqeq m] at hrung
      nlinarith only [hrung, mul_pos he (hq m)]
    have hraw : ∀ᶠ rho : NNReal in 𝓝[>] 0,
        Lemma91At.{u} beta varpi (tau m/16) (v m) (d m) rho :=
      hp.body (tau m/16) (by have := hb.next_pos; positivity) hKT hF
    exact hMiddle M N (m+1) schedule e varpi (tau m) (parent m) eta R beta (v m) (d m) (q m) (gamma m)
      hpc.1 hpc.2 hbeta0.le hb.raw_gain_pos (hq m) (hg m) (hgq m) (hcard m) (hmass m)
      (h3q m) (hgain m) (hb.margin_pos.le.trans hb.margin_le_rung) hrungq
      (by linarith [hetamax m, hmaxg m]) hraw
  have hOuterAll : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall m : Fin N,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M sourceThreadConstant), SourceTowerGeometry Q sourceBottomED sourceLevelED ->
      forall a b : Nat, SourceParentUpperWindow Q sourceBottomED sourceLevelED N schedule e a b (m+1) ->
      Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
        (delta : ENNReal)^(-(schedule (m+1)+s)) := by
    rw [Filter.eventually_all]
    intro m
    exact hOuter N M (m+1) sourceBottomED sourceLevelED sourceThreadConstant hM
      (by norm_num [sourceThreadConstant]) (by norm_num [sourceBottomED]) (by norm_num [sourceLevelED])
      schedule e s ((hparent m).margin_pos.trans_le (hparent m).margin_le_rung) hs
  refine ⟨eta, K, heta, hetas, heta10, hK, ?_, ?_⟩
  · intro m hm
    exact hBudget hbeta0 hbeta1 heps1 hp hbudget hetas m hm
  filter_upwards [hPaid, hThree, hMidAll, hOuterAll, hCard eta heta1,
    hLeafSmall eta (by linarith), Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)]
    with delta hpaid hthree hmiddle houter hcard hleafSmall hd
  intro iota S T Q Z hinput hstats hfull m a b hm hwindow P
  let mi : Fin N := ⟨m, hm⟩
  have hleaf : forall i, i ∈ S -> (delta : ENNReal)^(10 : Real)*volume (T i).carrier <= volume (Z i).shade := by
    have hh := hLeaf Q Z hstats hd.2.le hfull hleafSmall
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hh
  obtain ⟨X, hcompat, hstage, hXfull, htheta0, htheta1, hthetaH, htheta, hpayment⟩ :=
    hpaid S T Q Z hinput hstats hfull hleaf a P.parent b
      P.geometry.coarse_le_parent P.geometry.parent_lt_fine P.geometry.fine_bound
  have hmaxD : Kakeya.maxDensity S (fun i => (T i).toConvexSpaceBody) <= (delta : ENNReal)^(-etaL) := by
    apply hinput.maximal_density.trans
    rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hd.1), ENNReal.ofReal_coe_nnreal]
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd.2.le) (by linarith)
  have hXfullL : delta^etaL <= (sourceQSelectionLoss K delta)⁻¹ *
      ShadedBody.fullness S (fun i => (Z i).toShadedBody) :=
    (NNReal.rpow_le_rpow_of_exponent_ge hd.1 hd.2.le hetaL).trans hXfull
  have hparentD := P.geometry.parent_density X.ja (X.coarse_subset X.coarse_member)
  have houterD : Kakeya.maxDensity X.coarse (fun i => (Q.tube a i).toConvexSpaceBody) <=
      (delta : ENNReal)^(-(s+schedule (m+1))) := by
    simpa only [add_comm s] using
      (Kakeya.maxDensity_mono _ X.coarse_subset).trans (houter mi S T Q hinput.geometry a b hwindow)
  have hthreeX := hthree S T Q Z hinput.geometry hmaxD a P.parent b
    P.geometry.coarse_le_parent P.geometry.parent_lt_fine P.geometry.fine_bound _ _ X
    (2*parent m) (s+schedule (m+1)) hXfullL
    (by have := hmesh.parent_pos m hm; positivity)
    (by have hh := hparent mi; linarith [hh.margin_pos, hh.margin_le_rung])
    (by simpa only [neg_mul] using hparentD) houterD
  have hthreeFinal : SourceQThreeFactorBounds Q X beta (acc.epsf m) (acc.epsp m)
      (acc.epsc m+schedule (m+1)) := by
    rw [hbudget.fine_eq, hbudget.parent_charge_eq, hbudget.parent_accuracy_eq,
      hbudget.coarse_charge_eq, hbudget.outer_accuracy_eq, hbudget.coarse_density_eq]
    simpa only [parent, sourceTerminalParent, add_assoc] using hthreeX
  obtain ⟨hAnalysis, hmid⟩ := hmiddle mi S T Q Z hinput.geometry hstats a b hwindow P _ _ X hXfull htheta
    (hcard S T Q hinput)
  have hmidFinal : ShadedBody.multiplicity X.middle (fun i => (X.middleShade i).toShadedBody) <=
      (delta : ENNReal)^(sourceTerminalNetGain beta varpi eps1 rawGain rawDens m) *
        (X.middle.card : ENNReal)^beta := by
    simpa only [mi, sourceTerminalNetGain, sourceMiddleNetGain, sourceMiddleGain, e, v, tau,
      schedule, sourceZeroLadder, show m+2-1=m+1 by omega,
      show ML2Spine.spineDiv varpi eps1 * (rawGain
        (ML2Spine.spineRung beta varpi eps1 (sourceChoiceGain beta rawGain rawDens)
          (sourceChoiceDens beta rawDens) (m+1) / 16) / 2) / 2 =
        ML2Spine.spineDiv varpi eps1 * rawGain
          (ML2Spine.spineRung beta varpi eps1 (sourceChoiceGain beta rawGain rawDens)
            (sourceChoiceDens beta rawDens) (m+1) / 16) / 4 by ring] using hmid
  let F : SourceRetainedFourFactors Q Z a P.parent b beta (acc.epsf m) (acc.epsp m)
      (acc.epsc m+schedule (m+1)) (sourceTerminalNetGain beta varpi eps1 rawGain rawDens m)
      (sourceFixedPreparationLoss K delta *
        (ShadedBody.fullness S (fun i => (Z i).toShadedBody) : ENNReal)⁻¹^2) :=
    { lambda := _
      seam := X
      three := hthreeFinal
      middle := hmidFinal }
  exact ⟨F, hstage, hXfull, hpayment, hAnalysis⟩

end Kakeya.ML2Core
