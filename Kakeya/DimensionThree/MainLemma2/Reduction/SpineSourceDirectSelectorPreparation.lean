/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

/-- Exact unchanged-shading preparation extracted from the original selector.
The final fixed-input exponent is the supplied etaF. -/
theorem source_direct_prepare_unchanged
    (N M J A0 A1 C : Nat) (e : Real) (eta : Nat -> Real) (etaParent : Real)
    (hschedule : SourceZeroWindowSchedule N M J e eta etaParent)
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    (etaF : Real) (hetaF : 0 < etaF) (hthin : 3 * etaF < 10) :
    exists (K : Nat) (delta0 : NNReal), 1 <= K /\ 0 < delta0 /\ delta0 <= 1 /\
      delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
      (Q : SourceThreadedTower S T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
    SourceFixedTowerInput Q A0 A1 etaF -> SourceTowerStatistics Q Z ->
    (delta : ENNReal) ^ (3 * etaF) <=
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
    exists (R : Finset iota) (Q' : SourceThreadedTower R T M C),
      SourceDirectRetainedState Q Z R Q' Z (sourceFixedPreparationLoss K delta) /\
      SourceFixedTowerInput Q' A0 A1 etaF /\
      (forall i, i ∈ R -> (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <=
        volume (Z i).shade) := by
  classical
  obtain ⟨K0, K, B, delta0, hK0, hK, hB, hd0, hd1, hdM, hprep⟩ :=
    source_exists_fixedTower_preparation M A0 A1 C hschedule.level_bound hC hA0 hA1
      (eta0 := 3 * etaF / 2) (h := 1) (by positivity)
      (by linarith only [hthin]) (by norm_num)
  refine ⟨K, delta0, hK, hd0, hd1, hdM, ?_⟩
  intro delta hdelta hsmall iota S T Q Z hinput hstats hfull
  have hdle : delta <= 1 := hsmall.le.trans hd1
  have hin : SourceFixedTowerInput Q A0 A1 (3 * etaF / 2) := by
    refine ⟨hinput.geometry, hinput.neighbour_sharing, hinput.maximal_density.trans ?_⟩
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_ge
      (show (0 : Real) < delta by exact_mod_cast hdelta)
      (show (delta : Real) <= 1 by exact_mod_cast hdle)
      (by linarith only [hetaF])
  have hfull' : ENNReal.ofReal ((delta : Real) ^ (2 * (3 * etaF / 2))) <=
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody) := by
    rw [show 2 * (3 * etaF / 2) = 3 * etaF by ring]
    simpa only [← ENNReal.ofReal_rpow_of_pos
      (show (0 : Real) < delta by exact_mod_cast hdelta), ENNReal.ofReal_coe_nnreal] using hfull
  obtain ⟨R, Q', hrest, hinput', hstats', hledger, hloss⟩ :=
    hprep delta hdelta hsmall S T Q hin S le_rfl hinput.geometry.nonempty
      Z hstats.same_tubes hfull'
  refine ⟨R, Q', ?_, ?_, hledger.leaf_mass_floor⟩
  · have H : SourceZeroRetainedState Q Z R Z Q' (sourceFixedPreparationLoss K delta) := {
      restriction := hrest
      nonempty := hledger.nonempty
      original_tubes := hstats.same_tubes
      same_tubes := hstats.same_tubes
      subshade := fun _ => Set.Subset.rfl
      mass := hledger.mass.trans (mul_le_mul_left hloss _)
      fullness := hledger.fullness.trans (mul_le_mul_left hloss _)
      statistics := hstats' }
    refine { toSourceZeroRetainedState := H, multiplicity := ?_ }
    apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset S
      (fun i => (Z i).toShadedBody) R (fun i => (Z i).toShadedBody)
      (sourceFixedPreparationLoss K delta) _ H.mass
    exact Set.iUnion₂_subset fun i hi =>
      Set.subset_iUnion₂_of_subset i (hrest.subset hi) Set.Subset.rfl
  · exact ⟨hinput'.geometry, hinput'.neighbour_sharing,
      (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hrest.subset).trans
        hinput.maximal_density⟩

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- Restriction transports the two upper rows only. -/
theorem source_direct_upper_of_restriction
    {R : Finset iota} (Q : SourceThreadedTower S T M C)
    (Q' : SourceThreadedTower R T M C) (hrest : SourceTowerRestriction Q Q')
    {N J A0 A1 a b : Nat} {eta : Nat -> Real} {e : Real}
    (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J) :
    SourceParentUpperWindow Q' A0 A1 N eta e a b J := by
  have hfibre (k l : Nat) (j : iota) : Q'.fibre k l j <= Q.fibre k l j := by
    rw [hrest.full_retained_fibres]
    exact Finset.image_subset_image (Finset.filter_subset_filter _ hrest.subset)
  have hocc (k : Nat) (hk : k <= M) : Q'.indexSet k <= Q.indexSet k := by
    rw [hrest.occupied k hk]
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Q.place_mem k hk i (hrest.subset hi)
  refine {
    coarse_lt_fine := hwindow.coarse_lt_fine
    fine_bound := hwindow.fine_bound
    separation := hwindow.scale_separation
    coarse_density := ?_
    middle_density := ?_ }
  · intro ha j hj
    rw [hrest.tubes]
    exact (Kakeya.maxDensity_mono _ (hfibre 0 a j)).trans
      (hwindow.coarse_density ha j (hocc 0 (Nat.zero_le _) hj))
  · intro j hj
    rw [hrest.tubes]
    exact (Kakeya.maxDensity_mono _ (hfibre a b j)).trans
      (hwindow.middle_density j (hocc a (hwindow.coarse_lt_fine.le.trans hwindow.fine_bound) hj))

/-- The candidate set is finite even when the inset window is empty. -/
noncomputable def sourceDirectAdmissibleParents (Q : SourceThreadedTower S T M C)
    (etaParent e : Real) (a b : Nat) : Finset Nat :=
  (Finset.range b).filter (fun p => a <= p /\
    (forall m, SourceTowerWindow delta M e a b m -> p < m) /\
    SourceQParentAdmissible Q etaParent a p)

theorem source_direct_occupied_same_level_fibre
    (Q : SourceThreadedTower S T M C) {a : Nat} (ha : a <= M)
    {j : iota} (hj : j ∈ Q.indexSet a) : Q.fibre a a j = {j} := by
  ext k
  simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell,
    Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨i, ⟨hi, he⟩, rfl⟩
    exact he
  · intro heq
    subst k
    obtain ⟨i, hi, he⟩ := Q.place_surjective a ha j hj
    exact ⟨i, ⟨hi, he⟩, he⟩

/-- A density-admissible finite maximum, with no transverse interpretation. -/
theorem source_direct_exists_finite_admissible_parent
    (Q : SourceThreadedTower S T M C) (hne : S.Nonempty)
    {etaParent e : Real} {a b : Nat}
    (hdelta : 0 < delta) (hd1 : delta < 1) (heta : 0 < etaParent)
    (hab : a < b) (hbM : b <= M) :
    exists (hA : (sourceDirectAdmissibleParents Q etaParent e a b).Nonempty) (p : Nat),
      p = (sourceDirectAdmissibleParents Q etaParent e a b).max' hA /\
      p ∈ sourceDirectAdmissibleParents Q etaParent e a b /\
      a <= p /\ p < b /\ p <= M /\
      (forall m, SourceTowerWindow delta M e a b m -> p < m) /\
      SourceQParentAdmissible Q etaParent a p /\
      (forall q, q ∈ sourceDirectAdmissibleParents Q etaParent e a b -> q <= p) := by
  classical
  have haa : SourceQParentAdmissible Q etaParent a a := by
    intro j hj
    rw [source_direct_occupied_same_level_fibre Q (hab.le.trans hbM) hj]
    calc
      Kakeya.maxDensity {j} (fun k => (Q.tube a k).toConvexSpaceBody) <= 1 := by
        simpa using Kakeya.maxDensity_le_card {j} (fun k => (Q.tube a k).toConvexSpaceBody)
      _ <= (delta : ENNReal) ^ (-2 * etaParent) := by
        simpa using ENNReal.rpow_le_rpow_of_exponent_ge
          (show (delta : ENNReal) <= 1 by exact_mod_cast hd1.le)
          (show -2 * etaParent <= 0 by linarith)
  have hA : (sourceDirectAdmissibleParents Q etaParent e a b).Nonempty := by
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hab, le_rfl, ?_, haa⟩⟩
    exact fun m hm => hm.1
  let p := (sourceDirectAdmissibleParents Q etaParent e a b).max' hA
  have hp := Finset.max'_mem (sourceDirectAdmissibleParents Q etaParent e a b) hA
  have hprop := Finset.mem_filter.mp hp
  have hpb := Finset.mem_range.mp hprop.1
  exact ⟨hA, p, rfl, hp, hprop.2.1, hpb, hpb.le.trans hbM,
    hprop.2.2.1, hprop.2.2.2, fun q hq => Finset.le_max' _ q hq⟩

/-- Literal F or a strict sparse witness on exactly the supplied parent. -/
theorem source_direct_floor_or_sparse_at_parent
    (Q : SourceThreadedTower S T M C) {e tau etaParent : Real} {a b p : Nat}
    (hap : a <= p) (hpb : p < b) (hbM : b <= M)
    (hbefore : forall m, SourceTowerWindow delta M e a b m -> p < m)
    (hadmissible : SourceQParentAdmissible Q etaParent a p) :
    SourceZeroFloor Q e tau etaParent a b p \/
    exists (m : Nat) (j jp : iota), SourceTowerWindow delta M e a b m /\
      j ∈ Q.indexSet a /\ jp ∈ Q.fibre a p j /\
      ((Q.fibre p m jp).card : Real) <
        ((sourceTowerRadius delta M p : Real) / (sourceTowerRadius delta M m : Real)) ^
          (2 + 4 * (tau / 16)) := by
  classical
  by_cases hfloor : SourceZeroFloor Q e tau etaParent a b p
  · exact Or.inl hfloor
  · right
    by_contra hno
    push_neg at hno
    apply hfloor
    refine ⟨hap, hpb, hbM, hbefore, hadmissible, ?_⟩
    intro j hj jp hjp m hm hpm
    exact hno m j jp hm hj hjp

/-- The final factor-two statistic converts a quarter-threshold local failure
to the original-Q half-threshold assigned-profile failure. -/
theorem source_direct_failed_concentration_of_quarter_cell
    (Q : SourceThreadedTower S T M C) {R : Finset iota} (hR : R.Nonempty)
    (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hrest : SourceTowerRestriction Q Q') (hstats : SourceTowerStatistics Q' Z')
    {N J A0 A1 a b m : Nat} {eta : Nat -> Real} {e : Real}
    (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J)
    (hm : SourceTowerWindow delta M e a b m)
    (hnontruncated : 2 <=
      ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
        (eta (J + 1) / 2))
    (hgap : e ^ 2 / 2 <=
      Real.log ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) /
        Real.log (1 / (delta : Real)))
    {j : iota} (hj : j ∈ Q'.indexSet a)
    (hquarter : Kakeya.maxDensity (Q'.fibre a m j)
      (fun k => (Q'.tube m k).toConvexSpaceBody) <= (1 / 4 : ENNReal) * ENNReal.ofReal
        (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
          (eta (J + 1) / 2))) :
    SourceZeroFailedConcentration Q R a m e (eta (J + 1)) := by
  classical
  have hmM : m <= M := hm.2.1.le.trans hwindow.fine_bound
  have haM : a <= M := hm.1.le.trans hmM
  have hjQ : j ∈ Q.indexSet a := by
    rw [hrest.occupied a haM] at hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Q.place_mem a haM i (hrest.subset hi)
  refine ⟨hrest.subset, hm.1, hmM, ?_, ?_, hnontruncated, hgap⟩
  · exact (hwindow.window_lower m hm j hjQ).le.trans
      (Finset.le_sup (f := fun j => Kakeya.maxDensity
        (Q.retainedAssignedFibre S a m j) (fun k => (Q.tube m k).toConvexSpaceBody))
        (by
          obtain ⟨i, hi, he⟩ := Q.place_surjective a haM j hjQ
          exact Finset.mem_image.mpr ⟨i, hi, he⟩))
  · unfold SourceThreadedTower.assignedProfile
    apply Finset.sup_le
    intro k hk
    have hk' : k ∈ Q'.indexSet a := (hrest.occupied a haM).symm ▸ hk
    rw [← hrest.full_retained_fibres a m k, ← hrest.tubes]
    calc
      _ <= 2 * Kakeya.maxDensity (Q'.fibre a m j)
          (fun k => (Q'.tube m k).toConvexSpaceBody) :=
        hstats.two_level_density a m hm.1 hmM k hk' j hj
      _ <= 2 * ((1 / 4 : ENNReal) * ENNReal.ofReal
          (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
            (eta (J + 1) / 2))) := mul_le_mul_left' hquarter 2
      _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [one_div, one_div, show (4 : ENNReal) = 2 * 2 by norm_num,
          ENNReal.mul_inv (by left; norm_num) (by right; norm_num), ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- The exact complement has a strict quarter threshold, not a half threshold. -/
theorem source_direct_quarter_concentration_of_no_failure
    (Q : SourceThreadedTower S T M C) {R : Finset iota} (hR : R.Nonempty)
    (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hrest : SourceTowerRestriction Q Q') (hstats : SourceTowerStatistics Q' Z')
    {N J A0 A1 a b m : Nat} {eta : Nat -> Real} {e : Real}
    (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J)
    (hm : SourceTowerWindow delta M e a b m)
    (hnontruncated : 2 <=
      ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
        (eta (J + 1) / 2))
    (hgap : e ^ 2 / 2 <=
      Real.log ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) /
        Real.log (1 / (delta : Real)))
    (hno : ¬ SourceZeroFailedConcentration Q R a m e (eta (J + 1))) :
    forall j, j ∈ Q'.indexSet a -> (1 / 4 : ENNReal) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
        (eta (J + 1) / 2)) < Kakeya.maxDensity (Q'.fibre a m j)
          (fun k => (Q'.tube m k).toConvexSpaceBody) := by
  intro j hj
  by_contra hn
  exact hno (source_direct_failed_concentration_of_quarter_cell Q hR Q' Z'
    hrest hstats hwindow hm hnontruncated hgap hj (le_of_not_gt hn))

/-- One cutoff precedes all endpoint and interior level choices. -/
theorem source_direct_window_failure_cutoff
    (N M J : Nat) (e : Real) (eta : Nat -> Real) (etaParent : Real)
    (hschedule : SourceZeroWindowSchedule N M J e eta etaParent) :
    exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
      delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall a b m : Nat, b <= M ->
      (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
        (delta : Real) ^ e -> SourceTowerWindow delta M e a b m ->
      2 <= ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
        (eta (J + 1) / 2) /\
      e ^ 2 / 2 <=
        Real.log ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) /
          Real.log (1 / (delta : Real)) := by
  have hN : (0 : Real) < N := by exact_mod_cast (show 0 < N by have := hschedule.count_bound; omega)
  have he : 0 < e := by rw [hschedule.window_exponent]; positivity
  have htau : 0 < eta (J + 1) := hschedule.rung_positive (J + 1)
    (by omega) (by have := hschedule.source_index_upper; omega)
  obtain ⟨d, hd, hd1, hsmall⟩ := Kakeya.ML2Shaded.exists_threshold_const_le_rpow_neg' 2
    (show 0 < e ^ 2 * eta (J + 1) / 2 by positivity)
  refine ⟨min d ((400 : NNReal) ^ (-(M : Real))), lt_min hd (by positivity),
    (min_le_left _ _).trans hd1, min_le_right _ _, ?_⟩
  intro delta hdelta hdd a b m hbM hsep hm
  have hdR : (0 : Real) < delta := by exact_mod_cast hdelta
  have hdd' : delta < d := hdd.trans_le (min_le_left _ _)
  have hdlt : delta < 1 := hdd'.trans_le hd1
  have hrpos (k : Nat) : (0 : Real) < sourceTowerRadius delta M k := by
    unfold sourceTowerRadius
    split_ifs <;> positivity
  have hqpos : 0 < (sourceTowerRadius delta M b : Real) /
      (sourceTowerRadius delta M a : Real) := div_pos (hrpos b) (hrpos a)
  have hthetap : 0 < (sourceTowerRadius delta M a : Real) /
      (sourceTowerRadius delta M m : Real) := div_pos (hrpos a) (hrpos m)
  have hqlog := Real.log_le_log hqpos hsep
  rw [Real.log_rpow hdR] at hqlog
  have hwinlog := Real.log_le_log (Real.rpow_pos_of_pos hqpos _) hm.2.2.1
  rw [Real.log_rpow hqpos] at hwinlog
  have hlogeq : Real.log ((sourceTowerRadius delta M a : Real) /
        (sourceTowerRadius delta M m : Real)) =
      Real.log ((sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M m : Real)) -
        Real.log ((sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real)) := by
    rw [Real.log_div (hrpos a).ne' (hrpos m).ne',
      Real.log_div (hrpos b).ne' (hrpos m).ne',
      Real.log_div (hrpos b).ne' (hrpos a).ne']
    ring
  have hthetalog : -(e ^ 2) * Real.log (delta : Real) <=
      Real.log ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) := by
    rw [hlogeq]
    have hscale := mul_le_mul_of_nonneg_left hqlog he.le
    nlinarith only [hwinlog, hscale]
  constructor
  · apply (hsmall hdelta hdd'.le).trans
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hdR _)
      (Real.rpow_pos_of_pos hthetap _)).mp
    rw [Real.log_rpow hdR, Real.log_rpow hthetap]
    have hprod := mul_le_mul_of_nonneg_left hthetalog (show 0 <= eta (J + 1) / 2 by positivity)
    nlinarith only [hprod]
  · apply (le_div_iff₀ (log_one_div_pos hdelta hdlt)).mpr
    rw [one_div, Real.log_inv]
    have hlogd : Real.log (delta : Real) <= 0 := Real.log_nonpos hdR.le (by exact_mod_cast hdlt.le)
    have hs := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg e) hlogd
    nlinarith only [hthetalog, hs]

/-- This is only the measured potential drop. A paid retained state is still
required to turn it into the original selector's D outcome. -/
theorem source_direct_drop_of_quarter_cell
    (Q : SourceThreadedTower S T M C) {R : Finset iota} (hR : R.Nonempty)
    (Q' : SourceThreadedTower R T M C)
    (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hrest : SourceTowerRestriction Q Q') (hstats : SourceTowerStatistics Q' Z')
    {N J A0 A1 a b m : Nat} {eta : Nat -> Real} {e : Real}
    (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J)
    (hm : SourceTowerWindow delta M e a b m)
    (hdelta : 0 < delta) (hd1 : delta < 1) (he : 0 < e)
    (heta : 0 < eta 1) (hrung : eta 1 <= eta (J + 1))
    (hnontruncated : 2 <=
      ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
        (eta (J + 1) / 2))
    (hgap : e ^ 2 / 2 <=
      Real.log ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) /
        Real.log (1 / (delta : Real)))
    {j : iota} (hj : j ∈ Q'.indexSet a)
    (hquarter : Kakeya.maxDensity (Q'.fibre a m j)
      (fun k => (Q'.tube m k).toConvexSpaceBody) <= (1 / 4 : ENNReal) * ENNReal.ofReal
        (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
          (eta (J + 1) / 2))) :
    SourceDirectPotentialDrop Q R (eta 1 * e ^ 2 / 8) := by
  have H := source_direct_failed_concentration_of_quarter_cell Q hR Q' Z'
    hrest hstats hwindow hm hnontruncated hgap hj hquarter
  have hrpos (k : Nat) : (0 : Real) < sourceTowerRadius delta M k := by
    unfold sourceTowerRadius
    split_ifs <;> positivity
  let theta : Real := (sourceTowerRadius delta M a : Real) /
    (sourceTowerRadius delta M m : Real)
  have htheta : 0 < theta := div_pos (hrpos a) (hrpos m)
  have hpow : theta ^ eta (J + 1) = (theta ^ (eta (J + 1) / 2)) ^ (2 : Nat) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul htheta.le]
    congr 1
    push_cast
    ring
  have hA : 1 <= (1 / 2 : Real) * theta ^ (eta (J + 1) / 2) := by
    linarith only [hnontruncated]
  have hB : 1 <= (1 / 2 : Real) * theta ^ eta (J + 1) := by
    rw [hpow]
    nlinarith only [hnontruncated]
  have hlog : Real.log ((1 / 2 : Real) * theta ^ (eta (J + 1) / 2)) /
        Real.log (1 / (delta : Real)) + 2 * (eta 1 * e ^ 2 / 8) <=
      Real.log ((1 / 2 : Real) * theta ^ eta (J + 1)) /
        Real.log (1 / (delta : Real)) := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos htheta _).ne',
      Real.log_mul (by norm_num) (Real.rpow_pos_of_pos htheta _).ne',
      Real.log_rpow htheta, Real.log_rpow htheta, add_div, add_div]
    have htau : 0 <= eta (J + 1) / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hgap htau
    have hanchor := mul_le_mul_of_nonneg_right hrung (sq_nonneg e)
    dsimp [theta] at *
    ring_nf at hmul hanchor ⊢
    nlinarith only [hmul, hanchor]
  have hdrop := profileExp_drop_of_bounds hdelta hd1
    (source_assignedProfile_ne_top Q S a m) (source_assignedProfile_ne_top Q R a m)
    hA hB (by simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, theta] using H.old_density)
    (by simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, theta] using H.new_density) hlog
  have hh : 0 < eta 1 * e ^ 2 / 8 := by positivity
  apply Nat.succ_le_of_lt
  apply source_assignedPotential_drop Q hrest.subset hh hdelta hd1 hm.1
    (hm.2.1.le.trans hwindow.fine_bound)
  simpa only [profileExp_of_ne_top (source_assignedProfile_ne_top Q S a m),
    profileExp_of_ne_top (source_assignedProfile_ne_top Q R a m),
    SourceThreadedTower.assignedProfileExp] using hdrop

end Kakeya.ML2Core
