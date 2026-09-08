/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalWindowRefinement
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankAnalytic
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectFloorExit
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalGeometryClosed

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

/-- Actual source-ordered trial. It constructs the selection itself and
immediately returns terminal multiplicity or a genuinely paid D step.
No terminal selector law, common-parent witness or analytic exit is an input. -/
theorem source_exists_actual_terminal_nonsticky_trial
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
    exists (eta : Real) (epsBias etaF : Nat -> Real) (Kselect : Nat -> Nat)
      (D : Nat -> NNReal), 0 < eta /\ eta <= s /\
      (forall m, m < ML2Spine.spineCount varpi eps1 ->
        0 < epsBias m /\
        epsBias m <= sourceTerminalParent beta varpi eps1 rawGain rawDens m / 16 /\
        eta <= etaF m /\ 3 * etaF m < 10 /\ 1 <= Kselect m /\ 1 <= D m) /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED eta ->
        SourceTowerStatistics Q Z ->
        delta ^ eta <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (m a b : Nat), m < ML2Spine.spineCount varpi eps1 ->
        SourceTowerDividingWindow Q sourceBottomED sourceLevelED
          (ML2Spine.spineCount varpi eps1) (sourceZeroLadder beta varpi eps1 rawGain rawDens)
          (ML2Spine.spineDiv varpi eps1) a b (m + 1) ->
        exists (R : Finset iota) (Q' : SourceThreadedTower R T M sourceThreadConstant)
          (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
          SourceTerminalWindowOutcome Q Z R Q' Z'
            (ML2Spine.spineCount varpi eps1) (m + 1) sourceBottomED sourceLevelED
            (ML2Spine.spineDiv varpi eps1) (sourceZeroLadder beta varpi eps1 rawGain rawDens)
            (sourceTerminalParent beta varpi eps1 rawGain rawDens m) (epsBias m)
            (etaF m) (Kselect m) (D m) a b /\
          (SourceDirectGoodMass S Z beta (5 * ML2Spine.spineNu beta varpi eps1
            (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)) \/
          SourceDirectPotentialDrop Q R
            (ML2Spine.spineNu beta varpi eps1
              (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) *
              (ML2Spine.spineDiv varpi eps1) ^ 2 / 8)) := by
  set_option maxHeartbeats 4000000 in
  classical
  let N := ML2Spine.spineCount varpi eps1
  let e := ML2Spine.spineDiv varpi eps1
  let ladder := sourceZeroLadder beta varpi eps1 rawGain rawDens
  let P := sourceTerminalParent beta varpi eps1 rawGain rawDens
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hsp := ML2Spine.spineRung_isSpine hbeta0 hbeta1 hp.window_pos heps1
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
  have hexists (j : Fin N) := source_exists_terminal_window_refinement
    hbeta0 hbeta1 hKT hF N M (j.val + 1) sourceBottomED sourceLevelED sourceThreadConstant
    e ladder (P j.val) (hschedule j j.isLt)
    (by norm_num [sourceThreadConstant]) (by norm_num [sourceBottomED]) (by norm_num [sourceLevelED])
  choose Dfin hDfin hselect using hexists
  let D : Nat -> NNReal := fun m => if hm : m < N then Dfin ⟨m, hm⟩ else 1
  have hD (m : Nat) : 1 <= D m := by
    dsimp only [D]
    split_ifs with hm
    · exact hDfin ⟨m, hm⟩
    · exact le_rfl
  obtain ⟨etaA, epsBias, hetaA, hetaAs, hbias, hexit⟩ :=
    source_exists_terminal_geometry_nonsticky_exit hbeta0 hbeta1 heps1 hp hvarpi
      hKT hF hbudget M M1 Mc hmesh D hD
  have hbiased (j : Fin N) := hselect j (epsBias j)
    (hbias j j.isLt).1 (hbias j j.isLt).2
  choose etaP KP deltaP hetaP hthin hKP hdeltaP hdeltaP1 hdeltaPM hactual using hbiased
  let caps : Finset Real := insert etaA ((Finset.univ : Finset (Fin N)).image etaP)
  have hcaps : caps.Nonempty := ⟨etaA, by simp [caps]⟩
  let eta := caps.min' hcaps / 4
  have hmin : 0 < caps.min' hcaps := by
    have hmem := caps.min'_mem hcaps
    simp only [caps, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hmem
    rcases hmem with h | ⟨j, h⟩
    · rw [h]; exact hetaA
    · rw [← h]; exact hetaP j
  have heta : 0 < eta := div_pos hmin (by norm_num)
  have hetaA4 : 4 * eta <= etaA := by
    have hh := caps.min'_le etaA (by simp [caps])
    dsimp only [eta]
    linarith only [hh]
  have hetaP4 (j : Fin N) : 4 * eta <= etaP j := by
    have hh := caps.min'_le (etaP j) (by simp [caps])
    dsimp only [eta]
    linarith only [hh]
  let etaF : Nat -> Real := fun m => if hm : m < N then etaP ⟨m, hm⟩ else 1
  let Kselect : Nat -> Nat := fun m => if hm : m < N then KP ⟨m, hm⟩ else 1
  have hloss (j : Fin N) : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceFixedPreparationLoss (KP j) delta <= (delta : ENNReal) ^ (-eta) := by
    simpa only [sourceFixedPreparationLoss, one_div, one_mul] using
      VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
        (A := (2 : Real)) (B := (1 : Real)) (by norm_num) (by norm_num) (KP j) heta
  refine ⟨eta, epsBias, etaF, Kselect, D, heta, ?_, ?_, ?_⟩
  · exact (show eta <= etaA by linarith only [heta, hetaA4]).trans hetaAs
  · intro m hm
    change m < N at hm
    simp only [etaF, Kselect, D, dif_pos hm]
    exact ⟨(hbias m hm).1, (hbias m hm).2,
      by linarith only [heta, hetaP4 ⟨m, hm⟩], hthin ⟨m, hm⟩, hKP ⟨m, hm⟩, hDfin ⟨m, hm⟩⟩
  · filter_upwards [Filter.eventually_all.mpr (fun j : Fin N => hexit (KP j)),
      Filter.eventually_all.mpr (fun j : Fin N => Ioo_mem_nhdsGT (hdeltaP j)),
      Filter.eventually_all.mpr hloss,
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)]
        with delta hExit hParent hLoss hd
    intro iota S T Q Z hinput hstats hfull m a b hm hwindow
    change m < N at hm
    let j : Fin N := ⟨m, hm⟩
    have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
    have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hd1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd.2.le
    have hinputP : SourceFixedTowerInput Q sourceBottomED sourceLevelED (etaP j) := by
      refine ⟨hinput.geometry, hinput.neighbour_sharing, hinput.maximal_density.trans ?_⟩
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow_of_exponent_ge
        (show (0 : Real) < delta by exact_mod_cast hd.1)
        (show (delta : Real) <= 1 by exact_mod_cast hd.2.le)
      exact neg_le_neg (by linarith only [heta, hetaP4 j])
    have hfullE : (delta : ENNReal) ^ eta <=
        ShadedBody.fullness' S (fun i => (Z i).toShadedBody) := by
      simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne', ShadedBody.coe_fullness] using
        (ENNReal.coe_le_coe.mpr hfull)
    have hfullP : (delta : ENNReal) ^ (3 * etaP j) <=
        ShadedBody.fullness' S (fun i => (Z i).toShadedBody) :=
      (ENNReal.rpow_le_rpow_of_exponent_ge hd1
        (by linarith only [heta, hetaP4 j])).trans hfullE
    obtain ⟨R, Q', Z', H⟩ := hactual j delta hd.1 (hParent j).2 S T Q Z
      hinputP hstats hfullP a b hwindow
    have hinputA : SourceFixedTowerInput Q' sourceBottomED sourceLevelED etaA := by
      have hocc (k : Nat) (hk : k <= M) : Q'.indexSet k <= Q.indexSet k := by
        rw [H.retained.restriction.occupied k hk]
        intro z hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        exact Q.place_mem k hk i (H.retained.restriction.subset hi)
      refine {
        geometry := {
          nonempty := H.retained.nonempty
          original_centred := fun i hi => hinput.geometry.original_centred i (H.retained.restriction.subset hi)
          original_ball := fun i hi => hinput.geometry.original_ball i (H.retained.restriction.subset hi)
          original_ed := hinput.geometry.original_ed.subset H.retained.restriction.subset
          coarse_centred := ?_
          coarse_ball := ?_
          coarse_ed := ?_
          coarse_card := ?_
          segment_sharing := ?_ }
        neighbour_sharing := ?_
        maximal_density := ?_ }
      · simpa only [H.retained.restriction.tubes] using
          (fun k hk z hz => hinput.geometry.coarse_centred k hk z (hocc k hk.le hz))
      · simpa only [H.retained.restriction.tubes] using
          (fun k hk z hz => hinput.geometry.coarse_ball k hk z (hocc k hk.le hz))
      · intro k hk
        simpa only [H.retained.restriction.tubes] using (hinput.geometry.coarse_ed k hk).subset (hocc k hk.le)
      · intro k hk
        exact (show ((Q'.indexSet k).card : Real) <= ((Q.indexSet k).card : Real) from
          Nat.cast_le.mpr (Finset.card_le_card (hocc k hk.le))).trans
            (hinput.geometry.coarse_card k hk)
      · intro k hk x y hxy
        rw [H.retained.restriction.tubes]
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
          (hinput.geometry.segment_sharing k hk x y hxy)
      · intro k hk z hz
        rw [H.retained.restriction.tubes]
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
          (hinput.neighbour_sharing k hk z (hocc k hk.le hz))
      · refine (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody)
          H.retained.restriction.subset).trans
          (hinput.maximal_density.trans (ENNReal.ofReal_le_ofReal ?_))
        exact Real.rpow_le_rpow_of_exponent_ge
          (show (0 : Real) < delta by exact_mod_cast hd.1)
          (show (delta : Real) <= 1 by exact_mod_cast hd.2.le)
          (neg_le_neg (by linarith only [heta, hetaA4]))
    have hprod := (hfullE.trans H.retained.fullness).trans (mul_le_mul_left (hLoss j) _)
    have htwice : (delta : ENNReal) ^ (2 * eta) <=
        ShadedBody.fullness' R (fun i => (Z' i).toShadedBody) := by
      calc
        (delta : ENNReal) ^ (2 * eta) =
            (delta : ENNReal) ^ eta * (delta : ENNReal) ^ eta := by
          rw [← ENNReal.rpow_add _ _ hd0 hdt]
          congr 1
          ring
        _ <= (delta : ENNReal) ^ eta *
            ((delta : ENNReal) ^ (-eta) * ShadedBody.fullness' R (fun i => (Z' i).toShadedBody)) :=
          mul_le_mul_right hprod _
        _ = ShadedBody.fullness' R (fun i => (Z' i).toShadedBody) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 hdt, add_neg_cancel,
            ENNReal.rpow_zero, one_mul]
    have hfullA : delta ^ etaA <= ShadedBody.fullness R (fun i => (Z' i).toShadedBody) := by
      have hh := (ENNReal.rpow_le_rpow_of_exponent_ge hd1
        (show 2 * eta <= etaA by linarith only [heta, hetaA4])).trans htwice
      rw [← ShadedBody.coe_fullness] at hh
      apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hh
    have H' : SourceTerminalWindowOutcome Q Z R Q' Z' N (m + 1)
        sourceBottomED sourceLevelED e ladder (P m) (epsBias m)
        (etaP j) (KP j) (D m) a b := by
      simpa only [D, dif_pos hm, j] using H
    refine ⟨R, Q', Z', ?_, ?_⟩
    · simpa only [etaF, Kselect, dif_pos hm, j, N, e, ladder, P] using H'
    · exact hExit j S T Q Z R Q' Z' hinputA hfullA m a b (etaP j) hm H'

end Kakeya.ML2Core
