/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedTowerGeometryData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- The unselected geometric stage of the source threaded tower, S:4770-4914.
Neighbour sharing is an additional actual packing obligation, distinct from
the source's bound for tubes containing one fixed unit segment. -/
theorem source_exists_unselected_nested_fixedTower (M : Nat) (hM : 2 <= M) :
    exists (delta0 : NNReal) (C3 : Real),
      0 < delta0 /\ delta0 <= (400 : NNReal) ^ (-(M : Real)) /\ 1 <= C3 /\
      forall delta : NNReal, 0 < delta -> delta < delta0 ->
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3))),
        S.Nonempty -> Set.InjOn (fun i => (T i).toConvexSpaceBody) (S : Set iota) ->
        (forall i, i ∈ S -> (T i).IsCentred) ->
        (forall i, i ∈ S -> (T i).carrier <= Metric.closedBall 0 (3 / 4)) ->
        Kakeya.VeryNotSticky.IsLineEssDistinct sourceBottomED S T ->
      exists Q : SourceThreadedTower S T M sourceThreadConstant,
        SourceTowerGeometry Q sourceBottomED sourceLevelED /\
        SourceTowerNeighbourSharing Q /\
        (forall a b, a < b -> b < M -> forall j, j ∈ Q.indexSet a ->
          ((Q.fibre a b j).card : Real) <= C3 *
            ((sourceTowerRadius delta M a : Real) /
              (sourceTowerRadius delta M b : Real)) ^ 6) := by
  classical
  have hshared {rho : NNReal} (U V : Tube rho (EuclideanSpace Real (Fin 3)))
      {x y : EuclideanSpace Real (Fin 3)} (hxy : dist x y = 1)
      (hxU : segment Real x y <= U.carrier)
      (hxV : segment Real x y <= V.carrier) :
      U.carrier <= Kakeya.VeryNotSticky.lineNbhd V.x V.direction (5 * (rho : Real)) := by
    let P := Tube.mk' (0 : NNReal) hxy
    have hP : P.carrier = segment Real x y := by
      rw [P.carrier_eq_cthickening]
      simpa [P] using (isClosed_segment.closure_eq :
        closure (segment Real x y) = segment Real x y)
    have hPU : P.toConvexSpaceBody <= U.toConvexSpaceBody := by
      change P.carrier <= U.carrier
      rw [hP]
      exact hxU
    have hPV : P.toConvexSpaceBody <= V.toConvexSpaceBody := by
      change P.carrier <= V.carrier
      rw [hP]
      exact hxV
    have hU := Tube.le_rescale_of_subset P U hPU
    have hV := Tube.rescale_le_rescale_of_body_le P V
      (σ := 4 * rho) (θ := 5 * rho) (by positivity) (by ring_nf; rfl) hPV
    have hline := (V.rescale (5 * rho)).carrier_subset_cthickening_line_self (K := 1)
      (by norm_num)
    have hline' : (V.rescale (5 * rho)).carrier <=
        Kakeya.VeryNotSticky.lineNbhd V.x V.direction (5 * (rho : Real)) := by
      simpa [Kakeya.VeryNotSticky.lineNbhd_eq, Tube.rescale, Tube.direction] using hline
    exact fun z hz => hline' (hV (hU hz))
  have hMr : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  refine ⟨(400 : NNReal) ^ (-(M : Real)), 2 * 513 ^ 6, by positivity, le_rfl,
    by norm_num, ?_⟩
  intro delta hdelta hdelta0 iota S T hS hinj hcen hball hed
  let x : NNReal := delta ^ (1 / (M : Real))
  have hx : x <= (1 / 400 : NNReal) := by
    calc x <= ((400 : NNReal) ^ (-(M : Real))) ^ (1 / (M : Real)) :=
        NNReal.rpow_le_rpow hdelta0.le (by positivity)
      _ = 1 / 400 := by
        rw [← NNReal.rpow_mul]
        have hpow : (-(M : Real)) * (1 / (M : Real)) = -1 := by field_simp
        rw [hpow]
        norm_num
  have hx1 : x <= 1 := hx.trans (by
    norm_num [div_le_iff₀ (show (0 : NNReal) < 400 by norm_num)])
  have hrep : ∀ k : Nat, delta ^ ((k : Real) / (M : Real)) = x ^ k := by
    intro k
    rw [show (k : Real) / (M : Real) = (1 / (M : Real)) * (k : Real) by ring,
      NNReal.rpow_mul, NNReal.rpow_natCast]
  have hbottom : delta = x ^ M := by
    simpa [div_self hMr.ne', NNReal.rpow_one] using hrep M
  let rho := sourceTowerRadius delta M
  have hrhopos : ∀ k, 0 < rho k := by
    intro k
    dsimp [rho, sourceTowerRadius]
    split_ifs <;> positivity
  have hrhoM : rho M = delta := by simp [rho, sourceTowerRadius]
  have hrhobound : ∀ k, k < M -> rho k <= 1 / 40 := by
    intro k hk
    rw [show rho k = (1 / 40 : NNReal) * x ^ k by simp [rho, sourceTowerRadius, hk, hrep]]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hx1) (by positivity)).trans_eq
      (mul_one _)
  have hrhofour : ∀ k, k < M -> 4 * rho (k + 1) <= rho k := by
    intro k hk
    simp only [rho, sourceTowerRadius, if_pos hk, hrep]
    by_cases hk1 : k + 1 < M
    · rw [if_pos hk1, pow_succ]
      have hmul := mul_le_mul_of_nonneg_left hx (show 0 <= x ^ k by positivity)
      have hmulR : (x : Real) ^ k * (x : Real) <= (x : Real) ^ k * (1 / 400) := by
        exact_mod_cast hmul
      apply NNReal.coe_le_coe.mp
      push_cast
      nlinarith only [hmulR, pow_nonneg x.coe_nonneg k]
    · rw [if_neg hk1, hbottom, show M = k + 1 by omega, pow_succ]
      have hmul := mul_le_mul_of_nonneg_left hx (show 0 <= x ^ k by positivity)
      have hmulR : (x : Real) ^ k * (x : Real) <= (x : Real) ^ k * (1 / 400) := by
        exact_mod_cast hmul
      apply NNReal.coe_le_coe.mp
      push_cast
      nlinarith only [hmulR, pow_nonneg x.coe_nonneg k]
  have hmid : ∀ i ∈ S, ‖(T i).midpoint‖ <= (3 / 4 : Real) := by
    intro i hi
    have hm := (T i).mem_carrier_of_mem_segment
      ((T i).midpoint_add_smul_mem_segment (t := 0) (by norm_num))
    simpa using hball i hi (by simpa using hm)
  obtain ⟨i0, hi0⟩ := hS
  have hcover (k : Nat) (hk : k < M) (J : Finset iota)
      (W : iota -> Tube (rho (k + 1)) (EuclideanSpace Real (Fin 3)))
      (hWcen : ∀ j ∈ J, (W j).IsCentred)
      (hWmid : ∀ j ∈ J, ‖(W j).midpoint‖ <= (3 / 4 : Real)) :
      ∃ (I : Finset iota) (q : iota -> iota)
        (U : iota -> Tube (rho k) (EuclideanSpace Real (Fin 3))),
        Set.InjOn U (I : Set iota) /\
        (∀ j ∈ J, q j ∈ I) /\
        (∀ i ∈ I, ∃ j ∈ J, q j = i) /\
        (∀ j ∈ J, (W j).toConvexSpaceBody <= (U (q j)).toConvexSpaceBody) /\
        (∀ i ∈ I, (U i).IsCentred) /\
        (∀ i ∈ I, ‖(U i).midpoint‖ <= (3 / 4 : Real)) /\
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j ->
          (rho k : Real) / 8 <= ‖(U i).midpoint - (U j).midpoint‖ +
            ‖(U i).direction - (U j).direction‖) /\
        Kakeya.VeryNotSticky.IsLineEssDistinct sourceLevelED I U := by
    obtain ⟨G, f, hfmem, hfsurj, hfcontain, _, hGcen, hGmid, hGsep, hGed⟩ :=
      Tube.exists_canonicalCentredCover (hrhopos k) (by exact_mod_cast hrhofour k hk)
        (by norm_num : (0 : Real) <= 3 / 4) J W hWcen hWmid
    let pick : Tube (rho k) (EuclideanSpace Real (Fin 3)) -> iota :=
      fun V => if hV : V ∈ G then Classical.choose (hfsurj V hV) else i0
    have hpick : ∀ V ∈ G, pick V ∈ J /\ f (pick V) = V := by
      intro V hV
      simpa only [pick, dif_pos hV] using Classical.choose_spec (hfsurj V hV)
    let q : iota -> iota := fun j => pick (f j)
    let I := J.image q
    have hqf : ∀ j ∈ J, f (q j) = f j := fun j hj => (hpick (f j) (hfmem j hj)).2
    have hIf : ∀ i ∈ I, f i ∈ G := by
      rintro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      rw [hqf j hj]
      exact hfmem j hj
    have hIinj : Set.InjOn f (I : Set iota) := by
      intro i hi j hj heq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      rw [hqf a ha, hqf b hb] at heq
      exact congrArg pick heq
    refine ⟨I, q, f, hIinj, fun j hj => Finset.mem_image_of_mem q hj, ?_, ?_,
      fun i hi => hGcen _ (hIf i hi), fun i hi => hGmid _ (hIf i hi), ?_, ?_⟩
    · intro i hi
      exact Finset.mem_image.mp hi
    · intro j hj
      rw [hqf j hj]
      exact hfcontain j hj
    · intro i hi j hj hij
      exact hGsep _ (hIf i hi) _ (hIf j hj) (fun h => hij (hIinj hi hj h))
    · intro o d hd
      have hcard : ((I.filter (fun i => (f i).carrier <=
          Kakeya.VeryNotSticky.lineNbhd o d (5 * (rho k : Real)))).card : Real) <=
          Tube.canonicalCoverEDConstant 3 (3 / 4) := by
        have hsub : (I.filter (fun i => (f i).carrier <=
            Kakeya.VeryNotSticky.lineNbhd o d (5 * (rho k : Real)))).image f <=
            G.filter (fun V => V.carrier <=
              Metric.cthickening (5 * (rho k : Real)) (Set.range (fun t : Real => o + t • d))) := by
          intro V hV
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hV
          obtain ⟨hi, hline⟩ := Finset.mem_filter.mp hi
          exact Finset.mem_filter.mpr ⟨hIf i hi,
            by simpa only [Kakeya.VeryNotSticky.lineNbhd_eq] using hline⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_image_of_injOn (hIinj.mono (Finset.filter_subset _ _))] at hle
        refine le_trans (b := ((G.filter (fun V => V.carrier <=
          Metric.cthickening (5 * (rho k : Real))
            (Set.range (fun t : Real => o + t • d)))).card : Real)) ?_ ?_
        · exact_mod_cast hle
        · simpa using hGed o d hd
      have hc : Tube.canonicalCoverEDConstant 3 (3 / 4) <= (sourceLevelED : Real) := by
        norm_num [Tube.canonicalCoverEDConstant_eq, sourceLevelED]
      exact_mod_cast hcard.trans hc
  let Row (k : Nat) (I : Finset iota) (p : iota -> iota)
      (U : iota -> Tube (rho k) (EuclideanSpace Real (Fin 3))) : Prop :=
    Set.InjOn U (I : Set iota) /\
    (∀ i ∈ S, p i ∈ I) /\
    (∀ j ∈ I, ∃ i ∈ S, p i = j) /\
    (∀ i ∈ S, (T i).toConvexSpaceBody <= (U (p i)).toConvexSpaceBody) /\
    (∀ j ∈ I, (U j).IsCentred) /\
    (∀ j ∈ I, ‖(U j).midpoint‖ <= (3 / 4 : Real)) /\
    (k < M -> (∀ i ∈ I, ∀ j ∈ I, i ≠ j ->
      (rho k : Real) / 8 <= ‖(U i).midpoint - (U j).midpoint‖ +
        ‖(U i).direction - (U j).direction‖) /\
      Kakeya.VeryNotSticky.IsLineEssDistinct sourceLevelED I U)
  let Partial (n : Nat) (I : Nat -> Finset iota) (p q : Nat -> iota -> iota)
      (U : (k : Nat) -> iota -> Tube (rho k) (EuclideanSpace Real (Fin 3))) : Prop :=
    (∀ k, n <= k -> k <= M -> Row k (I k) (p k) (U k)) /\
    (∀ k, n <= k -> k < M ->
      (∀ j ∈ I (k + 1), q (k + 1) j ∈ I k) /\
      (∀ i ∈ S, p k i = q (k + 1) (p (k + 1) i)) /\
      (∀ j ∈ I (k + 1), (U (k + 1) j).toConvexSpaceBody <=
        (U k (q (k + 1) j)).toConvexSpaceBody)) /\
    I M = S /\ (∀ i ∈ S, p M i = i) /\
    (∀ i ∈ S, (U M i).toConvexSpaceBody = (T i).toConvexSpaceBody)
  have hpartial : ∀ n, n <= M ->
      ∃ (I : Nat -> Finset iota) (p q : Nat -> iota -> iota)
        (U : (k : Nat) -> iota -> Tube (rho k) (EuclideanSpace Real (Fin 3))),
        Partial n I p q U := by
    intro n hn
    induction hn using Nat.decreasingInduction with
    | self =>
      let U := fun (k : Nat) (i : iota) => (T i).rescale (rho k)
      have hbody : ∀ i, (U M i).toConvexSpaceBody = (T i).toConvexSpaceBody := by
        intro i
        change ((T i).rescale (rho M)).toConvexSpaceBody = _
        rw [hrhoM, Tube.toConvexSpaceBody_rescale_self]
      have hdir : ∀ i, (U M i).direction = (T i).direction := fun _ => rfl
      have hmp : ∀ i, (U M i).midpoint = (T i).midpoint := fun _ => rfl
      refine ⟨fun _ => S, fun _ i => i, fun _ i => i, U, ?_, ?_, rfl,
        fun _ _ => rfl, fun i _ => hbody i⟩
      · intro k hk hkM
        obtain rfl : k = M := by omega
        refine ⟨?_, fun _ hi => hi, fun i hi => ⟨i, hi, rfl⟩, ?_, ?_, ?_, ?_⟩
        · intro i hi j hj hij
          apply hinj hi hj
          simpa only [hbody] using congrArg Tube.toConvexSpaceBody hij
        · intro i hi
          exact (hbody i).ge
        · intro i hi
          simpa only [Tube.IsCentred, hdir, hmp] using hcen i hi
        · intro i hi
          simpa only [hmp] using hmid i hi
        · omega
      · intro k hk hkM
        omega
    | of_succ k hk ih =>
      obtain ⟨I, p, q, U, hrows, hparents, hIbot, hpbot, hUbot⟩ := ih
      obtain ⟨hUinj, hpmem, hpsurj, hleaf, hUcen, hUmid, hUcoarse⟩ :=
        hrows (k + 1) le_rfl hk
      obtain ⟨J, r, V, hVinj, hrmem, hrsurj, hrcontain, hVcen, hVmid, hVsep, hVed⟩ :=
        hcover k hk (I (k + 1)) (U (k + 1)) hUcen hUmid
      let I' := Function.update I k J
      let p' := Function.update p k (fun i => r (p (k + 1) i))
      let q' := Function.update q (k + 1) r
      let U' := Function.update U k V
      refine ⟨I', p', q', U', ?_, ?_, ?_, ?_, ?_⟩
      · intro l hkl hlM
        by_cases hl : l = k
        · subst l
          simp only [I', p', U', Function.update_self]
          refine ⟨hVinj, fun i hi => hrmem _ (hpmem i hi), ?_, ?_,
            hVcen, hVmid, fun _ => ⟨hVsep, hVed⟩⟩
          · intro j hj
            obtain ⟨a, ha, rfl⟩ := hrsurj j hj
            obtain ⟨i, hi, rfl⟩ := hpsurj a ha
            exact ⟨i, hi, rfl⟩
          · intro i hi
            exact (hleaf i hi).trans (hrcontain _ (hpmem i hi))
        · simpa only [I', p', U', Function.update_of_ne hl] using
            hrows l (by omega) hlM
      · intro l hkl hlM
        by_cases hl : l = k
        · subst l
          simpa only [I', p', q', U', Function.update_self,
            Function.update_of_ne (show k + 1 ≠ k by omega)] using
            (show (∀ j ∈ I (k + 1), r j ∈ J) /\
              (∀ i ∈ S, r (p (k + 1) i) = r (p (k + 1) i)) /\
              (∀ j ∈ I (k + 1), (U (k + 1) j).toConvexSpaceBody <=
                (V (r j)).toConvexSpaceBody) from
              ⟨hrmem, fun _ _ => rfl, hrcontain⟩)
        · simpa only [I', p', q', U', Function.update_of_ne hl,
            Function.update_of_ne (show l + 1 ≠ k by omega),
            Function.update_of_ne (show l + 1 ≠ k + 1 by omega)] using
            hparents l (by omega) hlM
      · simpa only [I', Function.update_of_ne (show M ≠ k by omega)] using hIbot
      · simpa only [p', Function.update_of_ne (show M ≠ k by omega)] using hpbot
      · simpa only [U', Function.update_of_ne (show M ≠ k by omega)] using hUbot
  obtain ⟨I, p, q, U, hrows, hparents, hIbot, hpbot, hUbot⟩ := hpartial 0 (by omega)
  have hrow (k : Nat) (hk : k <= M) := hrows k (by omega) hk
  have hcoarse (k : Nat) (hk : k < M) := (hrow k hk.le).2.2.2.2.2.2 hk
  have hA1 : sourceLevelED <= sourceThreadConstant := by
    norm_num [sourceLevelED, sourceThreadConstant]
  have hA0 : sourceBottomED <= sourceThreadConstant := by
    norm_num [sourceBottomED, sourceThreadConstant]
  have hneighbours : ∀ k, k < M -> ∀ j ∈ I k,
      ((I k).filter (fun j' => ∃ x y : EuclideanSpace Real (Fin 3), dist x y = 1 /\
        segment Real x y <= (U k j).carrier /\
        segment Real x y <= (U k j').carrier)).card <= sourceThreadConstant := by
    intro k hk j hj
    refine (Finset.card_le_card ?_).trans
      (((hcoarse k hk).2 (U k j).x (U k j).direction (U k j).norm_direction).trans hA1)
    intro l hl
    obtain ⟨hl, x, y, hxy, hxj, hxl⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hl, hshared _ _ hxy hxl hxj⟩
  have hsegments : ∀ k, k < M -> ∀ x y : EuclideanSpace Real (Fin 3), dist x y = 1 ->
      ((I k).filter (fun j => segment Real x y <= (U k j).carrier)).card <=
        sourceThreadConstant := by
    intro k hk x y hxy
    let F := (I k).filter (fun j => segment Real x y <= (U k j).carrier)
    rcases F.eq_empty_or_nonempty with hempty | ⟨j, hj⟩
    · change F.card <= _
      rw [hempty]
      exact Nat.zero_le _
    · obtain ⟨hjI, hjseg⟩ := Finset.mem_filter.mp hj
      refine (Finset.card_le_card ?_).trans (hneighbours k hk j hjI)
      intro l hl
      obtain ⟨hlI, hlseg⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlI, x, y, hxy, hjseg, hlseg⟩
  have hmult : ∀ k, k <= M -> ∀ i ∈ S,
      ((I k).filter (fun j => (T i).toConvexSpaceBody <=
        (U k j).toConvexSpaceBody)).card <= sourceThreadConstant := by
    intro k hk i hi
    by_cases hkM : k < M
    · refine (Finset.card_le_card ?_).trans
        (hsegments k hkM (T i).x (T i).y (T i).dist_eq_one)
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj, fun z hz => hij ((T i).mem_carrier_of_mem_segment hz)⟩
    · obtain rfl : k = M := by omega
      refine (Finset.card_le_card ?_).trans
        ((hed (T i).x (T i).direction (T i).norm_direction).trans hA0)
      intro j hj
      obtain ⟨hj, hij⟩ := Finset.mem_filter.mp hj
      rw [hIbot] at hj
      rw [hUbot j hj] at hij
      exact Finset.mem_filter.mpr ⟨hj, hshared (T j) (T i) (T i).dist_eq_one
        (fun z hz => hij ((T i).mem_carrier_of_mem_segment hz))
        (fun z hz => (T i).mem_carrier_of_mem_segment hz)⟩
  let Q : SourceThreadedTower S T M sourceThreadConstant := {
    indexSet := I
    place := p
    parent := q
    tube := U
    tube_injective := fun k hk => (hrow k hk).1
    place_mem := fun k hk => (hrow k hk).2.1
    place_surjective := fun k hk => (hrow k hk).2.2.1
    leaf_containment := fun k hk => (hrow k hk).2.2.2.1
    parent_mem := fun k hk => (hparents k (by omega) hk).1
    parent_composition := fun k hk => (hparents k (by omega) hk).2.1
    parent_containment := fun k hk => (hparents k (by omega) hk).2.2
    bottom_index := hIbot
    bottom_place := hpbot
    bottom_body := hUbot
    containment_multiplicity := hmult }
  have hUball : ∀ k, k < M -> ∀ j ∈ I k,
      (U k j).carrier <= Metric.closedBall 0 3 := by
    intro k hk j hj z hz
    have hmidj := (hrow k hk.le).2.2.2.2.2.1 j hj
    have hrad : (rho k : Real) <= 1 / 40 := by exact_mod_cast hrhobound k hk
    have hzmid := Kakeya.Tube.carrier_subset_closedBall_midpoint
      (EuclideanSpace Real (Fin 3)) (U k j) hz
    have hnorm : ‖z‖ <= ‖z - (U k j).midpoint‖ + ‖(U k j).midpoint‖ :=
      norm_le_norm_sub_add z (U k j).midpoint
    rw [Metric.mem_closedBall, dist_eq_norm] at hzmid
    have hmidpoint : _root_.midpoint Real (U k j).x (U k j).y = (U k j).midpoint := by
      simp only [midpoint_eq_smul_add, Tube.midpoint]
      norm_num
    rw [hmidpoint] at hzmid
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hglobal : ∀ k, k < M -> ((I k).card : Real) <= (32 / (rho k : Real)) ^ 6 := by
    intro k hk
    have hpos : 0 < (rho k : Real) := by exact_mod_cast hrhopos k
    have hbound : (rho k : Real) <= 1 / 40 := by exact_mod_cast hrhobound k hk
    have hpack := Tube.card_le_of_L1_separated_in_rectangle (I k)
      (fun j => (U k j).midpoint) (fun j => (U k j).direction) 0 0
      (r := (rho k : Real) / 8) (Rx := 3 / 4) (Ry := 1)
      (by positivity) (by positivity) (by positivity) (hcoarse k hk).1
      (fun j hj => by simpa using (hrow k hk.le).2.2.2.2.2.1 j hj)
      (fun j _ => by simp [(U k j).norm_direction])
    norm_num only [finrank_euclideanSpace, Fintype.card_fin] at hpack
    have hprod : ((3 / 4 + (rho k : Real) / 8 / 4) / ((rho k : Real) / 8 / 4)) *
        ((1 + (rho k : Real) / 8 / 4) / ((rho k : Real) / 8 / 4)) <=
          (32 / (rho k : Real)) ^ 2 := by
      calc _ = ((24 + (rho k : Real)) * (32 + (rho k : Real))) /
          (rho k : Real) ^ 2 := by field_simp; ring
        _ <= 1024 / (rho k : Real) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
        _ = (32 / (rho k : Real)) ^ 2 := by ring
    calc ((I k).card : Real) <=
        (((3 / 4 + (rho k : Real) / 8 / 4) / ((rho k : Real) / 8 / 4)) *
          ((1 + (rho k : Real) / 8 / 4) / ((rho k : Real) / 8 / 4))) ^ 3 := by
            simpa only [mul_pow] using hpack
      _ <= ((32 / (rho k : Real)) ^ 2) ^ 3 := by gcongr
      _ = (32 / (rho k : Real)) ^ 6 := by ring
  refine ⟨Q, ?_, hneighbours, ?_⟩
  · exact ⟨⟨i0, hi0⟩, hcen, hball, hed,
      fun k hk => (hrow k hk.le).2.2.2.2.1, hUball,
      fun k hk => (hcoarse k hk).2, hglobal, hsegments⟩
  · have hrhostep : ∀ k, k < M -> rho (k + 1) <= rho k := by
      intro k hk
      nlinarith only [hrhofour k hk, (rho (k + 1)).coe_nonneg]
    have hmono : ∀ a b, a <= b -> b <= M -> rho b <= rho a := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ b hab ih =>
        intro hb
        exact (hrhostep b (by omega)).trans (ih (by omega))
    have hnested : ∀ a b, a <= b -> b <= M -> ∀ i ∈ S,
        (U b (p b i)).toConvexSpaceBody <= (U a (p a i)).toConvexSpaceBody := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => intro _ _ _; exact le_rfl
      | succ b hab ih =>
        intro hb i hi
        have hpar := (hparents b (by omega) (by omega)).2.2 _
          ((hrow (b + 1) hb).2.1 i hi)
        rw [← (hparents b (by omega) (by omega)).2.1 i hi] at hpar
        exact hpar.trans (ih (by omega) i hi)
    intro a b hab hb j hj
    let F := Q.fibre a b j
    have hF : ∀ l ∈ F, l ∈ I b /\
        (U b l).toConvexSpaceBody <= (U a j).toConvexSpaceBody := by
      intro l hl
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨hiS, hip⟩ := Finset.mem_filter.mp hi
      refine ⟨(hrow b hb.le).2.1 i hiS, ?_⟩
      have hh := hnested a b hab.le hb.le i hiS
      change p a i = j at hip
      rwa [hip] at hh
    have ha : a < M := hab.trans hb
    have hra : 0 < (rho a : Real) := by exact_mod_cast hrhopos a
    have hrb : 0 < (rho b : Real) := by exact_mod_cast hrhopos b
    have hrba : (rho b : Real) <= (rho a : Real) := by exact_mod_cast hmono a b hab.le hb.le
    have hparams : ∀ l ∈ F,
        ‖(U b l).midpoint - Tube.lineFoot (U a j).x (U a j).direction‖ <= 4 * (rho a : Real) /\
        (‖(U b l).direction - (1 : Real) • (U a j).direction‖ <= 4 * (rho a : Real) ∨
          ‖(U b l).direction - (-1 : Real) • (U a j).direction‖ <= 4 * (rho a : Real)) := by
      intro l hl
      obtain ⟨hlI, hcontain⟩ := hF l hl
      have hline := (U a j).carrier_subset_cthickening_line_self (K := 1) (by norm_num)
      have hinline : (U b l).carrier <=
          Metric.cthickening (((rho a : Real) / (rho b : Real)) * (rho b : Real))
            (Set.range (fun t : Real => (U a j).x + t • (U a j).direction)) := by
        rw [div_mul_cancel₀ _ hrb.ne']
        intro z hz
        simpa only [one_mul] using hline (hcontain hz)
      obtain ⟨s, hs, hdir, hmp⟩ := Tube.params_close_of_carrier_subset_line (U b l)
        ((hrow b hb.le).2.2.2.2.1 l hlI) ((hrow b hb.le).2.2.2.2.2.1 l hlI)
        (U a j).norm_direction ((one_le_div hrb).mpr hrba) hinline
      have hscale : ((rho a : Real) / (rho b : Real) - 1) * (rho b : Real) =
          (rho a : Real) - (rho b : Real) := by
        rw [sub_mul, div_mul_cancel₀ _ hrb.ne', one_mul]
      rw [hscale] at hmp hdir
      refine ⟨by nlinarith, ?_⟩
      rcases hs with rfl | rfl
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hpack := Tube.card_filter_boxes_le_of_sep F (U b)
      (ε := (rho b : Real) / 8) (by positivity)
      (fun l hl l' hl' hll' => (hcoarse b hb).1 l (hF l hl).1 l' (hF l' hl').1 hll')
      (Tube.lineFoot (U a j).x (U a j).direction) (U a j).direction
      (Rx := 4 * (rho a : Real)) (Ry := 4 * (rho a : Real)) (by positivity) (by positivity)
    have hfilter : F.filter (fun l =>
        ‖(U b l).midpoint - Tube.lineFoot (U a j).x (U a j).direction‖ <= 4 * (rho a : Real) /\
        (‖(U b l).direction - (1 : Real) • (U a j).direction‖ <= 4 * (rho a : Real) ∨
          ‖(U b l).direction - (-1 : Real) • (U a j).direction‖ <= 4 * (rho a : Real))) = F :=
      Finset.filter_eq_self.mpr hparams
    rw [hfilter] at hpack
    norm_num only [finrank_euclideanSpace, Fintype.card_fin] at hpack
    have hquot : (4 * (rho a : Real) + (rho b : Real) / 8 / 4) /
        ((rho b : Real) / 8 / 4) <= 513 * ((rho a : Real) / (rho b : Real)) := by
      apply (div_le_iff₀ (by positivity : (0 : Real) < (rho b : Real) / 8 / 4)).mpr
      have hcancel : 513 * ((rho a : Real) / (rho b : Real)) * ((rho b : Real) / 8 / 4) =
          (513 / 32 : Real) * (rho a : Real) := by field_simp; ring
      rw [hcancel]
      linarith
    have hpows : ((4 * (rho a : Real) + (rho b : Real) / 8 / 4) /
        ((rho b : Real) / 8 / 4)) ^ 6 <=
          (513 * ((rho a : Real) / (rho b : Real))) ^ 6 := by gcongr
    calc ((Q.fibre a b j).card : Real) <=
        2 * ((4 * (rho a : Real) + (rho b : Real) / 8 / 4) /
          ((rho b : Real) / 8 / 4)) ^ 6 := by
            convert hpack using 1 <;> ring
      _ <= 2 * (513 * ((rho a : Real) / (rho b : Real))) ^ 6 :=
        mul_le_mul_of_nonneg_left hpows (by norm_num)
      _ = (2 * 513 ^ 6 : Real) * ((sourceTowerRadius delta M a : Real) /
          (sourceTowerRadius delta M b : Real)) ^ 6 := by dsimp [rho]; ring

end Kakeya.ML2Core
