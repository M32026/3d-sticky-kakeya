/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectSelectorPreparation
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectRawCountPayment
public import Kakeya.MultiScaleSubmult
public import Kakeya.Thickness.BoundingBox
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineBridgeCoverMap
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankSelection

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

set_option maxHeartbeats 8000000 in
/-- Additive actual F/P/D construction in source order. The only change
from the protected stronger selector is the terminal P statistical output. -/
theorem source_exists_terminal_window_refinement
    {beta : Real} (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (N M J A0 A1 C : Nat) (e : Real) (eta : Nat -> Real) (etaParent : Real)
    (hschedule : SourceZeroWindowSchedule N M J e eta etaParent)
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1) :
    exists D : NNReal, 1 <= D /\
    forall bias : Real, 0 < bias -> bias <= etaParent / 16 ->
    exists (etaF : Real) (K : Nat) (delta0 : NNReal),
      0 < etaF /\ 3 * etaF < 10 /\ 1 <= K /\
      0 < delta0 /\ delta0 <= 1 /\ delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
      (Q : SourceThreadedTower S T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceFixedTowerInput Q A0 A1 etaF -> SourceTowerStatistics Q Z ->
      (delta : ENNReal) ^ (3 * etaF) <=
        ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
    forall a b : Nat, SourceTowerDividingWindow Q A0 A1 N eta e a b J ->
    exists (R : Finset iota) (Q' : SourceThreadedTower R T M C)
      (Z' : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceTerminalWindowOutcome Q Z R Q' Z' N J A0 A1 e eta
        etaParent bias etaF K D a b := by
  classical
  have hPBranch (M A0 A1 C : Nat) (hM : 2 <= M) (hC : 1 <= C) :
      exists D : NNReal, 1 <= D /\
      forall bias : Real, 0 < bias ->
      exists (A : NNReal) (Kstage K : Nat), 1 <= A /\ 1 <= Kstage /\ 1 <= K /\
      forall etaF : Real, 3 * etaF < 10 ->
      exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
        delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
      forall delta : NNReal, 0 < delta -> delta < delta0 ->
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceFixedTowerInput Q A0 A1 etaF -> SourceTowerStatistics Q Z ->
      (delta : ENNReal) ^ (3 * etaF) <= ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
      forall (a b N J : Nat) (eta : Nat -> Real) (e etaParent : Real),
      SourceTowerDividingWindow Q A0 A1 N eta e a b J ->
      forall m, SourceTowerWindow delta M e a b m ->
      exists (G : Finset iota) (QG : SourceThreadedTower G T M C)
        (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage)
        (R : Finset iota) (QR : SourceThreadedTower R T M C)
        (F : SourceTerminalCommonFactorBin Q Z B R QR D K),
        SourceFixedTowerInput QR A0 A1 etaF /\
        SourceParentUpperWindow QR A0 A1 N eta e a b J /\
        (F.short / F.middle <= delta ^ etaParent ->
          SourceTerminalWindowOutcome Q Z R QR Z N J A0 A1 e eta etaParent bias etaF K D a b) := by
    clear hbeta0 hbeta1 hKT hF hschedule hA0 hA1
    classical
    have hInherited {iota : Type u} {delta : NNReal} {S R : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
        (Q : SourceThreadedTower S T M C) (QR : SourceThreadedTower R T M C)
        (hrest : SourceTowerRestriction Q QR) (hne : R.Nonempty)
        {A0 A1 N J a b : Nat} {etaF e : Real} {eta : Nat -> Real}
        (hinput : SourceFixedTowerInput Q A0 A1 etaF)
        (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J) :
        SourceFixedTowerInput QR A0 A1 etaF /\
          SourceParentUpperWindow QR A0 A1 N eta e a b J := by
      classical
      have hocc : forall k, k <= M -> QR.indexSet k <= Q.indexSet k := by
        intro k hk j hj
        rw [hrest.occupied k hk] at hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact Q.place_mem k hk i (hrest.subset hi)
      have hfibre : forall a b j, QR.fibre a b j <= Q.fibre a b j := by
        intro a b j
        rw [hrest.full_retained_fibres]
        exact Finset.image_subset_image (Finset.filter_subset_filter _ hrest.subset)
      constructor
      · refine {
          geometry := {
            nonempty := hne
            original_centred := fun i hi => hinput.geometry.original_centred i (hrest.subset hi)
            original_ball := fun i hi => hinput.geometry.original_ball i (hrest.subset hi)
            original_ed := hinput.geometry.original_ed.subset hrest.subset
            coarse_centred := ?_
            coarse_ball := ?_
            coarse_ed := ?_
            coarse_card := ?_
            segment_sharing := ?_ }
          neighbour_sharing := ?_
          maximal_density := (Kakeya.maxDensity_mono _ hrest.subset).trans hinput.maximal_density }
        · intro k hk j hj
          rw [hrest.tubes]
          exact hinput.geometry.coarse_centred k hk j (hocc k hk.le hj)
        · intro k hk j hj
          rw [hrest.tubes]
          exact hinput.geometry.coarse_ball k hk j (hocc k hk.le hj)
        · intro k hk
          rw [hrest.tubes]
          exact (hinput.geometry.coarse_ed k hk).subset (hocc k hk.le)
        · intro k hk
          exact (show ((QR.indexSet k).card : Real) <= (Q.indexSet k).card by
            exact_mod_cast Finset.card_le_card (hocc k hk.le)).trans
              (hinput.geometry.coarse_card k hk)
        · intro k hk x y hxy
          rw [hrest.tubes]
          exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
            (hinput.geometry.segment_sharing k hk x y hxy)
        · intro k hk j hj
          rw [hrest.tubes]
          exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
            (hinput.neighbour_sharing k hk j (hocc k hk.le hj))
      · refine {
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
            (hwindow.middle_density j (hocc a
              (hwindow.coarse_lt_fine.le.trans hwindow.fine_bound) hj))
    have hLeafFloor {etaF : Real} (hthin : 3 * etaF < 10) :
        ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} {S : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
          (Q : SourceThreadedTower S T M C)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
          S.Nonempty -> SourceTowerStatistics Q Z ->
          (delta : ENNReal) ^ (3 * etaF) <=
            ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
          forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) *
            volume (T i).carrier <= volume (Z i).shade := by
      filter_upwards [Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg 2
          (show 0 < 10 - 3 * etaF by linarith),
        Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hsmall hd
      intro iota S T M C Q Z hne hstats hfull
      have hscalarNN : 2 * delta ^ (10 : Real) <= delta ^ (3 * etaF) := by
        calc
          2 * delta ^ (10 : Real) <= delta ^ (-(10 - 3 * etaF)) * delta ^ (10 : Real) := by gcongr
          _ = delta ^ (-(10 - 3 * etaF) + 10) := (NNReal.rpow_add hd.1.ne' _ _).symm
          _ = _ := by congr 1; ring
      have hscalar : (2 : ENNReal) * (delta : ENNReal) ^ (10 : Real) <=
          (delta : ENNReal) ^ (3 * etaF) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hd.1.ne', ← ENNReal.coe_rpow_of_ne_zero hd.1.ne']
        exact_mod_cast hscalarNN
      have hmass : 0 < ∑ i ∈ S, volume (Z i).shade := by
        by_contra h
        have hz := le_antisymm (le_of_not_gt h) zero_le
        have hfzero : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) = 0 := by
          change (∑ i ∈ S, volume (Z i).shade) / _ = 0
          rw [hz, ENNReal.zero_div]
        rw [hfzero] at hfull
        have hp : 0 < (delta : ENNReal) ^ (3 * etaF) := by
          rw [← ENNReal.coe_rpow_of_ne_zero hd.1.ne']
          exact_mod_cast NNReal.rpow_pos (p := 3 * etaF) hd.1
        exact not_le_of_gt hp hfull
      obtain ⟨_, hdense, _⟩ := source_dense_comparable_of_fixed_statistics Q Z hd.1 hne hstats hmass
      intro i hi
      have hf : (delta : ENNReal) ^ (10 : Real) <=
          ShadedBody.fullness' S (fun i => (Z i).toShadedBody) / 2 := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
        simpa only [mul_comm] using hscalar.trans hfull
      have hdense' := hdense i hi
      change (((ShadedBody.fullness S (fun i => (Z i).toShadedBody) / 2 : NNReal) : ENNReal) *
        volume (Z i).carrier) <= volume (Z i).shade at hdense'
      rw [ENNReal.coe_div (by norm_num), ENNReal.coe_two, ShadedBody.coe_fullness] at hdense'
      have hv : volume (Z i).carrier = volume (T i).carrier := by
        change volume (Z i).toTube.carrier = _
        rw [hstats.same_tubes]
      rw [hv] at hdense'
      exact (mul_le_mul_left hf _).trans hdense'
    obtain ⟨D, hD, hbin⟩ := source_exists_terminal_common_factor_bin M A0 A1 C hM hC
    refine ⟨D, hD, ?_⟩
    intro bias hbias
    obtain ⟨A, Kstage, epsO, hA, hKstage, hO, hO1, hOM, hstage⟩ :=
      source_direct_exists_ordinary_cell_stage M A0 A1 C hM hC bias hbias
    obtain ⟨K, epsC, hKK, hK, hC0, hC1, hCM, hcommon⟩ := hbin bias hbias A Kstage hA hKstage
    refine ⟨A, Kstage, K, hA, hKstage, hK, ?_⟩
    intro etaF hthin
    obtain ⟨epsF, hF0, hfloor⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hLeafFloor hthin)
    refine ⟨min epsO (min epsC epsF), lt_min hO (lt_min hC0 hF0),
      (min_le_left _ _).trans hO1, (min_le_left _ _).trans hOM, ?_⟩
    intro delta hd hsmall iota S T Q Z hinput hstats hfull a b N J eta e etaParent hwindow m hm
    have hmM : m < M := hm.2.1.trans_le hwindow.fine_bound
    have hf : forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) *
        volume (T i).carrier <= volume (Z i).shade :=
      hfloor ⟨hd, hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
        Q Z hinput.geometry.nonempty hstats hfull
    have hshade : forall i, i ∈ S -> 0 < volume (Z i).shade := by
      intro i hi
      have hv : 0 < volume (T i).carrier := by
        refine lt_of_lt_of_le ?_ (Tube.le_volume (T i))
        have hc := Tube.le_volume.c_pos (Module.finrank Real (EuclideanSpace Real (Fin 3)))
        positivity
      exact (ENNReal.mul_pos (by positivity) hv.ne').trans_le (hf i hi)
    obtain ⟨G, QG, ⟨B⟩⟩ := hstage delta hd (hsmall.trans_le (min_le_left _ _))
      S T Q hinput.geometry Z hstats.same_tubes hshade a m hm.1 hmM
    obtain ⟨R, QR, ⟨F⟩⟩ := hcommon delta hd
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      S T Q hinput.geometry Z hstats.same_tubes hf a m hm.1 hmM
      (hstats.descendant_count m hmM.le) G QG B
    have hinputR := (hInherited Q QR F.retained.restriction F.nonempty hinput hwindow).1
    have hupper := source_direct_upper_of_restriction Q QR F.retained.restriction hwindow
    refine ⟨G, QG, B, R, QR, F, hinputR, hupper, ?_⟩
    intro hecc
    obtain ⟨P, hPm, hPs, hPb, hPl, hparts, hPstats⟩ :=
      source_terminal_plank_of_eccentric_bin Q Z B F hm hmM.le hecc hf
    exact {
      retained := F.retained
      input := hinputR
      upper := hupper
      alternative := Or.inl ⟨P, hPstats⟩ }
  have hFD (N M J : Nat) (e : Real) (eta : Nat -> Real) (etaParent : Real)
      (hschedule : SourceZeroWindowSchedule N M J e eta etaParent) :
      exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
        delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
      forall delta : NNReal, 0 < delta -> delta < delta0 ->
      forall {iota : Type u} {S R : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {C A0 A1 : Nat}
        (Q : SourceThreadedTower S T M C) (QR : SourceThreadedTower R T M C)
        (ZR : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceTowerRestriction Q QR -> R.Nonempty -> SourceTowerGeometry QR A0 A1 ->
        SourceTowerStatistics QR ZR ->
      forall a b : Nat, SourceTowerDividingWindow Q A0 A1 N eta e a b J ->
      forall m1 p : Nat, SourceTowerWindow delta M e a b m1 ->
        (forall m, SourceTowerWindow delta M e a b m -> m <= m1) -> a <= p -> p < m1 ->
        (forall ja, ja ∈ QR.indexSet a -> Kakeya.maxDensity (QR.fibre a p ja)
          (fun i => (QR.tube p i).toConvexSpaceBody) <= (delta : ENNReal) ^ (-2 * etaParent)) ->
        (forall jp, jp ∈ QR.indexSet p -> IsFrostmanIn (QR.fibre p m1 jp)
          (fun i => (QR.tube m1 i).toConvexSpaceBody) (QR.tube p jp).toConvexSpaceBody
            ((delta : ENNReal) ^ (-2 * etaParent))) ->
        Nonempty (SourceDirectFloor QR e (eta (J + 1)) etaParent a b) \/
          SourceDirectPotentialDrop Q R (eta 1 * e ^ 2 / 8) := by
    clear hbeta0 hbeta1 hKT hF hC hA0 hA1
    clear hPBranch
    classical
    have hTrace : ∃ Ctr : Real, 0 < Ctr /\
        ∀ {ι : Type u} {δ : NNReal} {S : Finset ι}
          {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C A0 A1 a p m : Nat},
        ∀ (Q : SourceThreadedTower S T M C)
          (Z : ι -> ShadedTube δ (EuclideanSpace Real (Fin 3))),
        SourceTowerGeometry Q A0 A1 -> SourceTowerStatistics Q Z ->
        0 < δ -> a <= p -> p < m -> m < M ->
        4 * sourceTowerRadius δ M m <= sourceTowerRadius δ M p ->
        sourceTowerRadius δ M p <= 1 ->
        ∀ D : ENNReal,
        (∀ ja ∈ Q.indexSet a, Kakeya.maxDensity (Q.fibre a p ja)
          (fun i => (Q.tube p i).toConvexSpaceBody) <= D) ->
        ∀ ja ∈ Q.indexSet a, ∀ jp ∈ Q.indexSet p,
          Kakeya.maxDensity (Q.fibre a m ja) (fun i => (Q.tube m i).toConvexSpaceBody) <=
            (2 * ENNReal.ofReal Ctr ^ 2 * D) *
              Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) := by
      classical
      have htwo {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
          [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
          ∃ C : Real, 0 < C /\
            ∀ {ι : Type u} {ρ σ : NNReal}, 0 < σ -> ρ <= 1 -> 4 * σ <= ρ ->
            ∀ (s : Finset ι) (P : ι -> _root_.Tube ρ E) (V : ι -> _root_.Tube σ E)
              (parent : ι -> ι),
            (∀ i ∈ s, (V i).toConvexSpaceBody <= (P (parent i)).toConvexSpaceBody) ->
            (∀ j ∈ s.image parent, (P j).carrier <= Metric.closedBall 0 3) ->
            (∀ i ∈ s, (V i).carrier <= Metric.closedBall 0 3) ->
            Kakeya.maxDensity s (fun i => (V i).toConvexSpaceBody) <=
              ENNReal.ofReal C ^ 2 *
                Kakeya.maxDensity (s.image parent) (fun j => (P j).toConvexSpaceBody) *
                (s.image parent).sup (fun j => Kakeya.maxDensity (s.filter (fun i => parent i = j))
                  (fun i => (V i).toConvexSpaceBody)) := by
        classical
        obtain ⟨C, hC, hmain⟩ :=
          Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax (E := E) 5 (by norm_num) 1 one_pos
        refine ⟨C, hC, ?_⟩
        intro ι ρ σ hσ hρ hgap s P V parent hVP hPball hVball
        obtain hs | hs := s.eq_empty_or_nonempty
        · rw [hs, Kakeya.maxDensity_empty]
          exact zero_le
        let j := hs.choose
        let Q1 := s.image parent
        let W1 := fun j => (P j).toConvexSpaceBody
        let W2 := fun i => (V i).toConvexSpaceBody
        obtain ⟨d, hd⟩ : ∃ d : E, ‖d‖ = 1 := exists_norm_eq E zero_le_one
        let amb : _root_.Tube 4 E := _root_.Tube.ofMidpointDirection 4 0 d hd
        have hambmid : midpoint Real amb.x amb.y = 0 := by
          rw [midpoint_eq_smul_add]
          change (⅟(2 : Real)) • ((0 - (1 / 2 : Real) • d) + (0 + (1 / 2 : Real) • d)) = 0
          simp
        have hamb_ball : amb.carrier ⊆ Metric.closedBall (0 : E) 5 := by
          intro z hz
          have h := Kakeya.Tube.carrier_subset_closedBall_midpoint (E := E) amb hz
          rw [hambmid, Metric.mem_closedBall] at h
          rw [Metric.mem_closedBall, dist_zero_right]
          norm_num at h
          linarith
        have hball_amb : Metric.closedBall (0 : E) 4 ⊆ amb.carrier := by
          intro z hz
          rw [amb.carrier_eq]
          refine Set.mem_biUnion (midpoint_mem_segment amb.x amb.y) ?_
          rw [hambmid]
          exact hz
        let radii : Fin 3 -> NNReal := fun k => match k with
          | ⟨0, _⟩ => 4
          | ⟨1, _⟩ => ρ
          | ⟨_ + 2, _⟩ => σ
        let tb : ∀ k : Fin 3, ι -> _root_.Tube (radii k) E := fun k => match k with
          | ⟨0, _⟩ => fun _ => amb
          | ⟨1, _⟩ => P
          | ⟨_ + 2, _⟩ => V
        let Q : Fin 3 -> Finset ι := fun k => match k with
          | ⟨0, _⟩ => {j}
          | ⟨1, _⟩ => Q1
          | ⟨_ + 2, _⟩ => s
        let pr : Fin 2 -> ι -> ι := fun k => match k with
          | ⟨0, _⟩ => fun _ => j
          | ⟨_ + 1, _⟩ => parent
        have hr0 : 1 <= radii 0 := by change (1 : NNReal) <= 4; norm_num
        have hr04 : radii 0 <= 4 := le_rfl
        have hr2 : 0 < radii 2 := hσ
        have hgap1 : 4 * radii 1 <= radii 0 := by
          change (4 : NNReal) * ρ <= 4
          nlinarith
        have hgap2 : 4 * radii 2 <= radii 1 := hgap
        have key := hmain radii hr0 hr04 hr2 hgap1 hgap2 (κ := fun _ => ι) tb Q pr ?_ ?_ ?_ ?_ ?_
        · have key' : Kakeya.maxDensity s W2 <= ENNReal.ofReal C ^ 2 *
              (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j) *
                Kakeya.MultiScaleSubmult.fibreDeltaMax s W2 Q1 parent) := by
            rw [Fin.prod_univ_two] at key
            exact key
          have hf1 : Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j) =
              Kakeya.maxDensity Q1 W1 := by
            unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
            rw [Finset.sup_singleton]
            congr 1
            exact Finset.filter_true_of_mem (fun _ _ => rfl)
          rw [hf1] at key'
          simpa only [Q1, W1, W2, Kakeya.MultiScaleSubmult.fibreDeltaMax, mul_assoc] using key'
        · intro k
          fin_cases k
          · intro w _
            exact Finset.mem_singleton_self j
          · intro w hw
            exact Finset.mem_image_of_mem parent hw
        · intro k
          fin_cases k
          · intro w hw
            change (P w).toConvexSpaceBody <= amb.toConvexSpaceBody
            exact (hPball w hw).trans ((Metric.closedBall_subset_closedBall (by norm_num)).trans hball_amb)
          · intro w hw
            exact hVP w hw
        · change (({j} : Finset ι).card : Real) <= 1 * (5 + 3) ^ (2 * Module.finrank Real E)
          rw [Finset.card_singleton, one_mul]
          exact_mod_cast one_le_pow₀ (by norm_num : (1 : Real) <= 5 + 3)
        · intro k
          fin_cases k
          · intro w _
            exact hamb_ball
          · intro w hw
            exact (hPball w hw).trans (Metric.closedBall_subset_closedBall (by norm_num))
          · intro w hw
            exact (hVball w hw).trans (Metric.closedBall_subset_closedBall (by norm_num))
        · intro k
          fin_cases k
          · exact Finset.singleton_nonempty j
          · exact hs.image parent
      
    
      obtain ⟨Ctr, hCtr, htwo⟩ := htwo (E := EuclideanSpace Real (Fin 3))
      refine ⟨Ctr, hCtr, ?_⟩
      intro ι δ S T M C A0 A1 a p m Q Z hgeom hstats hδ hap hpm hm hgap hρ D hD ja hja jp hjp
      have hpM : p <= M := hpm.le.trans hm.le
      have hcompatible (c d : Nat) (hcd : c <= d) (hd : d <= M)
          (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
          (heq : Q.place d i = Q.place d j) : Q.place c i = Q.place c j := by
        induction d, hcd using Nat.le_induction with
        | base => exact heq
        | succ d hcd ih =>
          apply ih (Nat.le_of_succ_le hd)
          rw [Q.parent_composition d (Nat.lt_of_succ_le hd) i hi,
            Q.parent_composition d (Nat.lt_of_succ_le hd) j hj, heq]
      have hcontained (c d : Nat) (hcd : c <= d) (hd : d <= M)
          (i : ι) (hi : i ∈ S) :
          (Q.tube d (Q.place d i)).toConvexSpaceBody <= (Q.tube c (Q.place c i)).toConvexSpaceBody := by
        induction d, hcd using Nat.le_induction with
        | base => exact le_rfl
        | succ d hcd ih =>
          have hsub := Q.parent_containment d (Nat.lt_of_succ_le hd)
            (Q.place (d + 1) i) (Q.place_mem (d + 1) hd i hi)
          rw [← Q.parent_composition d (Nat.lt_of_succ_le hd) i hi] at hsub
          exact hsub.trans (ih (Nat.le_of_succ_le hd))
      let leaf (j : ι) := if hj : j ∈ Q.indexSet m then
        Classical.choose (Q.place_surjective m hm.le j hj) else j
      have hleaf (j : ι) (hj : j ∈ Q.indexSet m) :
          leaf j ∈ S /\ Q.place m (leaf j) = j := by
        simpa only [leaf, dif_pos hj] using Classical.choose_spec (Q.place_surjective m hm.le j hj)
      let parent j := Q.place p (leaf j)
      have hplace (i : ι) (hi : i ∈ S) : parent (Q.place m i) = Q.place p i := by
        have hl := hleaf (Q.place m i) (Q.place_mem m hm.le i hi)
        exact hcompatible p m hpm.le hm.le _ hl.1 i hi hl.2
      have hmem (c d : Nat) (j i : ι) : i ∈ Q.fibre c d j ↔
          ∃ x ∈ S, Q.place c x = j /\ Q.place d x = i := by
        simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell, Finset.mem_image,
          Finset.mem_filter]
        aesop
      have hindex (c d : Nat) (hd : d <= M) (j i : ι) (hi : i ∈ Q.fibre c d j) :
          i ∈ Q.indexSet d := by
        obtain ⟨x, hx, hxc, rfl⟩ := (hmem c d j i).mp hi
        exact Q.place_mem d hd x hx
      have himage : (Q.fibre a m ja).image parent = Q.fibre a p ja := by
        ext j
        constructor
        · intro hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          obtain ⟨x, hx, hxa, rfl⟩ := (hmem a m ja i).mp hi
          rw [hplace x hx]
          exact (hmem a p ja _).mpr ⟨x, hx, hxa, rfl⟩
        · intro hj
          obtain ⟨x, hx, hxa, hxp⟩ := (hmem a p ja j).mp hj
          exact Finset.mem_image.mpr ⟨Q.place m x, (hmem a m ja _).mpr ⟨x, hx, hxa, rfl⟩,
            (hplace x hx).trans hxp⟩
      have hfib (j : ι) (hj : j ∈ Q.fibre a p ja) :
          (Q.fibre a m ja).filter (fun i => parent i = j) = Q.fibre p m j := by
        obtain ⟨y, hy, hya, hyp⟩ := (hmem a p ja j).mp hj
        ext i
        rw [Finset.mem_filter, hmem p m j i]
        constructor
        · rintro ⟨hi, hparij⟩
          obtain ⟨x, hx, hxa, hxi⟩ := (hmem a m ja i).mp hi
          refine ⟨x, hx, ?_, hxi⟩
          rw [← hplace x hx, hxi]
          exact hparij
        · rintro ⟨x, hx, hxp, hxi⟩
          have hxa : Q.place a x = ja :=
            (hcompatible a p hap hpM x hx y hy (hxp.trans hyp.symm)).trans hya
          refine ⟨(hmem a m ja i).mpr ⟨x, hx, hxa, hxi⟩, ?_⟩
          rw [← hxi, hplace x hx, hxp]
      have hσ : 0 < sourceTowerRadius δ M m := by
        simp only [sourceTowerRadius, if_pos hm]
        positivity
      have htrace := htwo hσ hρ hgap (Q.fibre a m ja) (Q.tube p) (Q.tube m) parent
        (fun i hi => by
          obtain ⟨x, hx, hxa, rfl⟩ := (hmem a m ja i).mp hi
          rw [hplace x hx]
          exact hcontained p m hpm.le hm.le x hx)
        (fun j hj => hgeom.coarse_ball p (hpm.trans hm) j
          (hindex a p hpM ja j (himage ▸ hj)))
        (fun i hi => hgeom.coarse_ball m hm i (hindex a m hm.le ja i hi))
      rw [himage] at htrace
      have hsup : (Q.fibre a p ja).sup (fun j =>
          Kakeya.maxDensity ((Q.fibre a m ja).filter (fun i => parent i = j))
            (fun i => (Q.tube m i).toConvexSpaceBody)) <=
          2 * Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) := by
        apply Finset.sup_le
        intro j hj
        rw [hfib j hj]
        exact hstats.two_level_density p m hpm hm.le j (hindex a p hpM ja j hj) jp hjp
      calc
        _ <= ENNReal.ofReal Ctr ^ 2 * Kakeya.maxDensity (Q.fibre a p ja)
            (fun i => (Q.tube p i).toConvexSpaceBody) *
            (Q.fibre a p ja).sup (fun j =>
              Kakeya.maxDensity ((Q.fibre a m ja).filter (fun i => parent i = j))
                (fun i => (Q.tube m i).toConvexSpaceBody)) := htrace
        _ <= ENNReal.ofReal Ctr ^ 2 * D *
            (2 * Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody)) :=
          mul_le_mul' (mul_le_mul' le_rfl (hD ja hja)) hsup
        _ = _ := by ring
    have hVolume {ι : Type u} {σ ρ : NNReal} (hσ : σ <= 1) (hρ : 0 < ρ)
        (s : Finset ι) (V : ι -> Tube σ (EuclideanSpace Real (Fin 3)))
        (P : Tube ρ (EuclideanSpace Real (Fin 3))) :
        Kakeya.densityIn s (fun i => (V i).toConvexSpaceBody) P.toConvexSpaceBody <=
          (((_root_.Tube.volume_le.C 3 / _root_.Tube.le_volume.c 3 * (σ / ρ) ^ 2 : NNReal) : ENNReal)) *
            (s.card : ENNReal) := by
      clear hTrace
      classical
      have hnum : (∑ i ∈ s.filter (fun i => (V i).toConvexSpaceBody <= P.toConvexSpaceBody),
          volume (V i).carrier) <= (s.card : ENNReal) *
            ((_root_.Tube.volume_le.C 3 * σ ^ 2 : NNReal) : ENNReal) := by
        calc
          _ <= ∑ i ∈ s, volume (V i).carrier := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          _ <= ∑ i ∈ s, ((_root_.Tube.volume_le.C 3 * σ ^ 2 : NNReal) : ENNReal) := by
            apply Finset.sum_le_sum
            intro i hi
            simpa using _root_.Tube.volume_le hσ (V i)
          _ = _ := by simp
      have hden : ((_root_.Tube.le_volume.c 3 * ρ ^ 2 : NNReal) : ENNReal) <= volume P.carrier := by
        simpa using _root_.Tube.le_volume P
      have hc : _root_.Tube.le_volume.c 3 ≠ 0 := (_root_.Tube.le_volume.c_pos 3).ne'
      calc
        _ <= ((s.card : ENNReal) * ((_root_.Tube.volume_le.C 3 * σ ^ 2 : NNReal) : ENNReal)) /
            ((_root_.Tube.le_volume.c 3 * ρ ^ 2 : NNReal) : ENNReal) := ENNReal.div_le_div hnum hden
        _ = _ := by
          simp only [div_eq_mul_inv, ENNReal.coe_mul, ENNReal.coe_pow,
            ENNReal.coe_inv hc, ENNReal.coe_inv hρ.ne']
          rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hc)) (Or.inl ENNReal.coe_ne_top),
            ENNReal.inv_pow]
          ring
    have hCount (Ctr Cv e tau eta : Real) (hCtr : 0 < Ctr) (hCv : 0 < Cv)
        (he : 0 < e) (htau : 0 < tau) (heta : 0 < eta)
        (hbudget : 4 * eta < e ^ 2 * tau / 8) :
        ∃ delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
        ∀ δ : NNReal, 0 < δ -> δ < delta0 ->
        ∀ Theta r : Real, 1 <= r -> r <= Theta ->
          e ^ 2 / 2 <= Real.log Theta / Real.log (1 / (δ : Real)) ->
        ∀ (n : Nat) (d0 d1 d2 : ENNReal),
          (1 / 4 : ENNReal) * ENNReal.ofReal (Theta ^ (tau / 2)) <= d0 ->
          d0 <= (2 * ENNReal.ofReal Ctr ^ 2 * (δ : ENNReal) ^ (-2 * eta)) * d1 ->
          d1 <= (2 * (δ : ENNReal) ^ (-2 * eta)) * d2 ->
          d2 <= ENNReal.ofReal (Cv / r ^ 2) * (n : ENNReal) ->
          r ^ (2 + 4 * (tau / 16)) <= (n : Real) := by
      clear hTrace hVolume
      have hden : 0 < 16 * Ctr ^ 2 * Cv := by positivity
      obtain ⟨delta0, hd0, hd1, hpay⟩ := source_direct_raw_count_payment
        (16 * Ctr ^ 2 * Cv) 4 e tau eta hden (by norm_num) he htau heta hbudget
      refine ⟨delta0, hd0, hd1, ?_⟩
      intro δ hδ hdd Theta r hr hrT hgap n d0 d1 d2 hquarter htrace hFr hvol
      have hδR : (0 : Real) < δ := by exact_mod_cast hδ
      have hδ0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ.ne'
      have hr0 : 0 < r := zero_lt_one.trans_le hr
      have hT0 : 0 < Theta := hr0.trans_le hrT
      have hpow : (δ : ENNReal) ^ (-2 * eta) * (δ : ENNReal) ^ (-2 * eta) =
          (δ : ENNReal) ^ (-4 * eta) := by
        rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
        congr 1
        ring
      have hchain : (1 / 4 : ENNReal) * ENNReal.ofReal (Theta ^ (tau / 2)) <=
          4 * ENNReal.ofReal Ctr ^ 2 * (δ : ENNReal) ^ (-4 * eta) *
            (ENNReal.ofReal (Cv / r ^ 2) * (n : ENNReal)) := by
        calc
          _ <= d0 := hquarter
          _ <= (2 * ENNReal.ofReal Ctr ^ 2 * (δ : ENNReal) ^ (-2 * eta)) * d1 := htrace
          _ <= (2 * ENNReal.ofReal Ctr ^ 2 * (δ : ENNReal) ^ (-2 * eta)) *
              ((2 * (δ : ENNReal) ^ (-2 * eta)) * d2) := mul_le_mul' le_rfl hFr
          _ = (4 * ENNReal.ofReal Ctr ^ 2 *
              ((δ : ENNReal) ^ (-2 * eta) * (δ : ENNReal) ^ (-2 * eta))) * d2 := by ring
          _ <= _ := by rw [hpow]; exact mul_le_mul' le_rfl hvol
      have hreal := ENNReal.toReal_mono (by finiteness) hchain
      simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
        ENNReal.toReal_one, ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hT0 _).le,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal hCtr.le, ← ENNReal.toReal_rpow,
        ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity : 0 <= Cv / r ^ 2),
        ENNReal.toReal_natCast] at hreal
      have hraw : r ^ 2 * Theta ^ (tau / 2) * (δ : Real) ^ (4 * eta) /
          (16 * Ctr ^ 2 * Cv) <= (n : Real) := by
        apply (div_le_iff₀ hden).mpr
        have hmul := mul_le_mul_of_nonneg_right hreal
          (show 0 <= 4 * r ^ 2 * (δ : Real) ^ (4 * eta) by positivity)
        have hrepr : (4 * Ctr ^ 2 * (δ : Real) ^ (-4 * eta) * (Cv / r ^ 2 * n)) *
            (4 * r ^ 2 * (δ : Real) ^ (4 * eta)) = (n : Real) * (16 * Ctr ^ 2 * Cv) := by
          rw [show -4 * eta = -(4 * eta) by ring, Real.rpow_neg hδR.le]
          field_simp <;> ring
        rw [hrepr] at hmul
        convert hmul using 1 <;> ring
      calc
        _ = r ^ 2 * r ^ (4 * (tau / 16)) := by
          rw [Real.rpow_add hr0, Real.rpow_two]
        _ <= r ^ 2 * (Theta ^ (tau / 2) * (δ : Real) ^ (4 * eta) / (16 * Ctr ^ 2 * Cv)) :=
          mul_le_mul_of_nonneg_left (hpay δ hδ hdd Theta r hr hrT hgap) (sq_nonneg r)
        _ = r ^ 2 * Theta ^ (tau / 2) * (δ : Real) ^ (4 * eta) / (16 * Ctr ^ 2 * Cv) := by ring
        _ <= _ := hraw
    have hOrder {δ : NNReal} {M a b p m1 : Nat} {e : Real}
        (hδ : 0 < δ) (hδ1 : δ <= 1) (hb : b <= M)
        (hmax : SourceTowerWindow δ M e a b m1) (hp : p < m1)
        (hnot : ¬ SourceTowerWindow δ M e a b p) :
        ∀ k, SourceTowerWindow δ M e a b k -> p < k := by
      clear hTrace hVolume hCount
      have hmono (r s : Nat) (hrs : r <= s) (hs : s < M) :
          sourceTowerRadius δ M s <= sourceTowerRadius δ M r := by
        simp only [sourceTowerRadius, if_pos hs, if_pos (hrs.trans_lt hs)]
        apply mul_le_mul_right
        apply NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1
        exact div_le_div_of_nonneg_right (by exact_mod_cast hrs) (Nat.cast_nonneg M)
      have hpos (r : Nat) (hr : r < M) : (0 : Real) < sourceTowerRadius δ M r := by
        simp only [sourceTowerRadius, if_pos hr, NNReal.coe_mul]
        positivity
      have hconvex (r s t : Nat) (hr : SourceTowerWindow δ M e a b r)
          (ht : SourceTowerWindow δ M e a b t) (hrs : r <= s) (hst : s <= t) :
          SourceTowerWindow δ M e a b s := by
        have hsM : s < M := (hst.trans_lt ht.2.1).trans_le hb
        have hrM : r < M := (hr.2.1).trans_le hb
        have htM : t < M := (ht.2.1).trans_le hb
        have hsr : (sourceTowerRadius δ M s : Real) <= sourceTowerRadius δ M r := by
          exact_mod_cast hmono r s hrs hsM
        have hts : (sourceTowerRadius δ M t : Real) <= sourceTowerRadius δ M s := by
          exact_mod_cast hmono s t hst htM
        refine ⟨hr.1.trans_le hrs, hst.trans_lt ht.2.1, ?_, ?_⟩
        · exact hr.2.2.1.trans (div_le_div_of_nonneg_left (NNReal.coe_nonneg _) (hpos s hsM) hsr)
        · exact (div_le_div_of_nonneg_left (NNReal.coe_nonneg _) (hpos t htM) hts).trans ht.2.2.2
      intro k hk
      by_contra hpk
      exact hnot (hconvex k p m1 hk hmax (le_of_not_gt hpk) hp.le)
    have hIntermediate {ι : Type u} {δ : NNReal} {S : Finset ι}
        {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C p m m1 : Nat}
        (Q : SourceThreadedTower S T M C)
        (Z : ι -> ShadedTube δ (EuclideanSpace Real (Fin 3)))
        (hstats : SourceTowerStatistics Q Z) (hpm : p <= m) (hmm : m < m1)
        (hm1 : m1 <= M) (hscale : 0 < sourceTowerRadius δ M m1)
        (hscale1 : sourceTowerRadius δ M m1 <= 1) (jp : ι) (CF : ENNReal)
        (hFr : IsFrostmanIn (Q.fibre p m1 jp)
          (fun i => (Q.tube m1 i).toConvexSpaceBody) (Q.tube p jp).toConvexSpaceBody CF) :
        IsFrostmanIn (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody)
          (Q.tube p jp).toConvexSpaceBody (2 * CF) := by
      clear hTrace hVolume hCount hOrder
      classical
      have hm : m <= M := hmm.le.trans hm1
      have hcompatible (a b : Nat) (hab : a <= b) (hb : b <= M)
          (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
          (heq : Q.place b i = Q.place b j) : Q.place a i = Q.place a j := by
        induction b, hab using Nat.le_induction with
        | base => exact heq
        | succ b hab ih =>
          apply ih (Nat.le_of_succ_le hb)
          rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
            Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
      have hcontained (a b : Nat) (hab : a <= b) (hb : b <= M)
          (i : ι) (hi : i ∈ S) :
          (Q.tube b (Q.place b i)).toConvexSpaceBody <=
            (Q.tube a (Q.place a i)).toConvexSpaceBody := by
        induction b, hab using Nat.le_induction with
        | base => exact le_rfl
        | succ b hab ih =>
          have hsub := Q.parent_containment b (Nat.lt_of_succ_le hb)
            (Q.place (b + 1) i) (Q.place_mem (b + 1) hb i hi)
          rw [← Q.parent_composition b (Nat.lt_of_succ_le hb) i hi] at hsub
          exact hsub.trans (ih (Nat.le_of_succ_le hb))
      let leaf (j : ι) := if hj : j ∈ Q.indexSet m1 then
        Classical.choose (Q.place_surjective m1 hm1 j hj) else j
      have hleaf (j : ι) (hj : j ∈ Q.indexSet m1) :
          leaf j ∈ S /\ Q.place m1 (leaf j) = j := by
        simpa only [leaf, dif_pos hj] using Classical.choose_spec (Q.place_surjective m1 hm1 j hj)
      let parent j := Q.place m (leaf j)
      have hplace (i : ι) (hi : i ∈ S) : parent (Q.place m1 i) = Q.place m i := by
        have hl := hleaf (Q.place m1 i) (Q.place_mem m1 hm1 i hi)
        exact hcompatible m m1 hmm.le hm1 _ hl.1 i hi hl.2
      have hmem (a b : Nat) (j i : ι) : i ∈ Q.fibre a b j ↔
          ∃ x ∈ S, Q.place a x = j /\ Q.place b x = i := by
        simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell, Finset.mem_image,
          Finset.mem_filter]
        aesop
      have hpar : ∀ i ∈ Q.fibre p m1 jp, parent i ∈ Q.fibre p m jp := by
        intro i hi
        obtain ⟨x, hx, hxp, rfl⟩ := (hmem p m1 jp i).mp hi
        rw [hplace x hx]
        exact (hmem p m jp _).mpr ⟨x, hx, hxp, rfl⟩
      have hVW : ∀ i ∈ Q.fibre p m1 jp,
          (Q.tube m1 i).toConvexSpaceBody <= (Q.tube m (parent i)).toConvexSpaceBody := by
        intro i hi
        obtain ⟨x, hx, hxp, rfl⟩ := (hmem p m1 jp i).mp hi
        rw [hplace x hx]
        exact hcontained m m1 hmm.le hm1 x hx
      have hWK : ∀ j ∈ Q.fibre p m jp,
          (Q.tube m j).toConvexSpaceBody <= (Q.tube p jp).toConvexSpaceBody := by
        intro j hj
        obtain ⟨x, hx, hxp, rfl⟩ := (hmem p m jp j).mp hj
        simpa only [hxp] using hcontained p m hpm hm x hx
      have hfib (j : ι) (hj : j ∈ Q.fibre p m jp) :
          (Q.fibre p m1 jp).filter (fun i => parent i = j) = Q.fibre m m1 j := by
        obtain ⟨y, hy, hyp, hym⟩ := (hmem p m jp j).mp hj
        ext i
        rw [Finset.mem_filter, hmem m m1 j i]
        constructor
        · rintro ⟨hi, hparij⟩
          obtain ⟨x, hx, hxp, hxi⟩ := (hmem p m1 jp i).mp hi
          refine ⟨x, hx, ?_, hxi⟩
          rw [← hplace x hx, hxi]
          exact hparij
        · rintro ⟨x, hx, hxm, hxi⟩
          have hxp : Q.place p x = jp :=
            (hcompatible p m hpm hm x hx y hy (hxm.trans hym.symm)).trans hyp
          refine ⟨(hmem p m1 jp i).mpr ⟨x, hx, hxp, hxi⟩, ?_⟩
          rw [← hxi, hplace x hx, hxm]
      have hne (j : ι) (hj : j ∈ Q.fibre p m jp) :
          ((Q.fibre p m1 jp).filter (fun i => parent i = j)).Nonempty := by
        obtain ⟨x, hx, hxp, hxm⟩ := (hmem p m jp j).mp hj
        exact ⟨Q.place m1 x, Finset.mem_filter.mpr
          ⟨(hmem p m1 jp _).mpr ⟨x, hx, hxp, rfl⟩, (hplace x hx).trans hxm⟩⟩
      have hindex (j : ι) (hj : j ∈ Q.fibre p m jp) : j ∈ Q.indexSet m := by
        obtain ⟨x, hx, hxp, rfl⟩ := (hmem p m jp j).mp hj
        exact Q.place_mem m hm x hx
      have hinside (j : ι) : ∀ i ∈ Q.fibre m m1 j,
          (Q.tube m1 i).toConvexSpaceBody <= (Q.tube m j).toConvexSpaceBody := by
        intro i hi
        obtain ⟨x, hx, hxm, rfl⟩ := (hmem m m1 j i).mp hi
        simpa only [hxm] using hcontained m m1 hmm.le hm1 x hx
      have hdensity (j : ι) :
          Kakeya.densityIn (Q.fibre m m1 j) (fun i => (Q.tube m1 i).toConvexSpaceBody)
            (Q.tube m j).toConvexSpaceBody =
          ((Q.fibre m m1 j).card : ENNReal) * volume (Q.tube m1 jp).carrier /
            volume (Q.tube m jp).carrier := by
        rw [Kakeya.densityIn, Finset.filter_eq_self.mpr (hinside j)]
        rw [_root_.Tube.sum_volume_carrier_eq_card_mul (Q.tube m1) (Q.tube m1 jp),
          _root_.Tube.volume_carrier_eq_volume_carrier (Q.tube m j) (Q.tube m jp)]
      refine ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres
        (par := parent) (fib := fun j => (Q.fibre p m1 jp).filter (fun i => parent i = j))
        hFr ?_ hpar hVW hWK (fun _ => rfl) hne ?_
      · intro i hi
        exact (_root_.Tube.volume_pos_and_lt_top hscale hscale1 (Q.tube m1 i)).1
      · intro j hj j' hj'
        rw [hfib j hj, hfib j' hj', hdensity j, hdensity j']
        calc
          _ <= (2 * ((Q.fibre m m1 j').card : ENNReal)) * volume (Q.tube m1 jp).carrier /
              volume (Q.tube m jp).carrier := by
            gcongr
            exact hstats.two_level_count m m1 hmm hm1 j (hindex j hj) j' (hindex j' hj')
          _ = _ := by simp only [div_eq_mul_inv]; ring
    have hRadius {delta : NNReal} {M : Nat} (hM : 2 <= M) (hd : 0 < delta)
        (hd1 : delta <= 1) (hsmall : delta < (400 : NNReal) ^ (-(M : Real))) :
        (forall k, k < M -> 0 < sourceTowerRadius delta M k /\ sourceTowerRadius delta M k <= 1) /\
        (forall p m, p <= m -> m < M -> sourceTowerRadius delta M m <= sourceTowerRadius delta M p) /\
        (forall p m, p < m -> m < M -> 4 * sourceTowerRadius delta M m <= sourceTowerRadius delta M p) := by
      clear hTrace hVolume hCount hOrder hIntermediate
      have hMr : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
      let x : NNReal := delta ^ (1 / (M : Real))
      have hx : x <= (1 / 400 : NNReal) := by
        calc
          x <= ((400 : NNReal) ^ (-(M : Real))) ^ (1 / (M : Real)) :=
            NNReal.rpow_le_rpow hsmall.le (by positivity)
          _ = 1 / 400 := by
            rw [← NNReal.rpow_mul]
            have hp : (-(M : Real)) * (1 / (M : Real)) = -1 := by field_simp
            rw [hp]
            norm_num
      have hx1 : x <= 1 := hx.trans (by
        norm_num [div_le_iff₀ (show (0 : NNReal) < 400 by norm_num)])
      have hx4 : x <= 1 / 4 := hx.trans (by
        norm_num [div_le_div_iff₀ (show (0 : NNReal) < 400 by norm_num)
          (show (0 : NNReal) < 4 by norm_num)])
      have hrep : forall k : Nat, delta ^ ((k : Real) / (M : Real)) = x ^ k := by
        intro k
        rw [show (k : Real) / (M : Real) = (1 / (M : Real)) * (k : Real) by ring,
          NNReal.rpow_mul, NNReal.rpow_natCast]
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        rw [sourceTowerRadius, if_pos hk]
        constructor
        · positivity
        · have hp : delta ^ ((k : Real) / (M : Real)) <= 1 :=
            NNReal.rpow_le_one hd1 (by positivity)
          calc
            _ <= (1 / 40 : NNReal) * 1 := mul_le_mul' le_rfl hp
            _ <= 1 := by norm_num [div_le_iff₀ (show (0 : NNReal) < 40 by norm_num)]
      · intro p m hpm hm
        simp only [sourceTowerRadius, if_pos hm, if_pos (hpm.trans_lt hm)]
        apply mul_le_mul_right
        exact NNReal.rpow_le_rpow_of_exponent_ge hd hd1
          (div_le_div_of_nonneg_right (by exact_mod_cast hpm) hMr.le)
      · intro p m hpm hm
        simp only [sourceTowerRadius, if_pos hm, if_pos (hpm.trans hm), hrep]
        have hp : x ^ m <= x ^ (p + 1) :=
          pow_le_pow_of_le_one (by positivity) hx1 (Nat.succ_le_of_lt hpm)
        rw [pow_succ] at hp
        have hfour : 4 * x <= 1 := by
          have h := (le_div_iff₀ (show (0 : NNReal) < 4 by norm_num)).mp hx4
          simpa only [mul_comm] using h
        calc
          _ <= 4 * ((1 / 40) * (x ^ p * x)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hp)
          _ = ((1 / 40) * x ^ p) * (4 * x) := by ring
          _ <= ((1 / 40) * x ^ p) * 1 := mul_le_mul' le_rfl hfour
          _ = _ := mul_one _
    have hExclusion (e tau etaParent : Real) (he : 0 < e) (htau : 0 < tau)
        (heta : 0 < etaParent) (hbudget : 4 * etaParent < e ^ 2 * tau / 8) :
        exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
        forall delta : NNReal, 0 < delta -> delta < delta0 ->
        forall Theta : Real, 1 <= Theta ->
          e ^ 2 / 2 <= Real.log Theta / Real.log (1 / (delta : Real)) ->
          (delta : ENNReal) ^ (-2 * etaParent) <
            (1 / 4 : ENNReal) * ENNReal.ofReal (Theta ^ (tau / 2)) := by
      clear hTrace hVolume hCount hOrder hIntermediate hRadius
      obtain ⟨eps, heps, heps1, hpay⟩ := source_direct_raw_count_payment
        8 2 e tau etaParent (by norm_num) (by norm_num) he htau heta (by linarith)
      refine ⟨eps, heps, heps1, ?_⟩
      intro delta hd hsmall Theta hTheta hgap
      have hdR : (0 : Real) < delta := by exact_mod_cast hd
      have hTheta0 : 0 < Theta := zero_lt_one.trans_le hTheta
      have hraw := hpay delta hd hsmall Theta 1 le_rfl hTheta hgap
      rw [Real.one_rpow] at hraw
      have hp : 0 < (delta : Real) ^ (2 * etaParent) := Real.rpow_pos_of_pos hdR _
      have hstrict : (delta : Real) ^ (-2 * etaParent) < (1 / 4 : Real) * Theta ^ (tau / 2) := by
        rw [show -2 * etaParent = -(2 * etaParent) by ring, Real.rpow_neg hdR.le, ← one_div]
        apply (div_lt_iff₀ hp).mpr
        nlinarith only [hraw]
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      simpa only [← ENNReal.toReal_rpow, ENNReal.coe_toReal, ENNReal.toReal_mul,
        ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
        ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hTheta0 _).le] using hstrict
    have hN : (0 : Real) < N := by
      exact_mod_cast (show 0 < N by have := hschedule.count_bound; omega)
    have he : 0 < e := by rw [hschedule.window_exponent]; positivity
    have htau : 0 < eta (J + 1) := hschedule.rung_positive (J + 1) (by omega)
      (by have := hschedule.source_index_upper; omega)
    have hbudget : 4 * etaParent < e ^ 2 * eta (J + 1) / 8 := by
      have h := hschedule.parent_upper
      have hp := hschedule.parent_positive
      nlinarith
    obtain ⟨Ctr, hCtr, htrace⟩ := hTrace
    let Cv : Real := (_root_.Tube.volume_le.C 3 / _root_.Tube.le_volume.c 3 : NNReal)
    have hCv : 0 < Cv := by
      exact_mod_cast div_pos (_root_.Tube.volume_le.C_pos 3) (_root_.Tube.le_volume.c_pos 3)
    obtain ⟨epsC, hC, hC1, hcount⟩ := hCount Ctr Cv e (eta (J + 1)) etaParent
      hCtr hCv he htau hschedule.parent_positive hbudget
    obtain ⟨epsP, hP, hP1, hexclusion⟩ := hExclusion e (eta (J + 1)) etaParent
      he htau hschedule.parent_positive hbudget
    obtain ⟨epsW, hW, hW1, hWM, hcutoff⟩ :=
      source_direct_window_failure_cutoff N M J e eta etaParent hschedule
    refine ⟨min epsC (min epsP epsW), lt_min hC (lt_min hP hW),
      (min_le_left _ _).trans hC1,
      ((min_le_right _ _).trans (min_le_right _ _)).trans hWM, ?_⟩
    intro delta hd hsmall iota S R T C A0 A1 Q QR ZR hrest hne hgeom hstats a b hwindow
      m1 p hm1 hmax hap hpm1 hparent hfinest
    have hsC : delta < epsC := hsmall.trans_le (min_le_left _ _)
    have hsP : delta < epsP := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hsW : delta < epsW := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hd1 : delta < 1 := hsW.trans_le hW1
    obtain ⟨hrad, hmono, hscalegap⟩ := hRadius hschedule.level_bound hd hd1.le (hsW.trans_le hWM)
    have hm1M : m1 < M := hm1.2.1.trans_le hwindow.fine_bound
    have hpM : p < M := hpm1.trans hm1M
    have haM : a < M := hap.trans_lt hpM
    have hradR (k : Nat) (hk : k < M) : (0 : Real) < sourceTowerRadius delta M k := by
      exact_mod_cast (hrad k hk).1
    by_cases hquarter : forall m, SourceTowerWindow delta M e a b m ->
        forall j, j ∈ QR.indexSet a -> (1 / 4 : ENNReal) * ENNReal.ofReal
          (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^
            (eta (J + 1) / 2)) < Kakeya.maxDensity (QR.fibre a m j)
              (fun k => (QR.tube m k).toConvexSpaceBody)
    · have hnot : ¬ SourceTowerWindow delta M e a b p := by
        intro hpwindow
        obtain ⟨x, hx⟩ := hne
        have hj : QR.place a x ∈ QR.indexSet a := QR.place_mem a haM.le x hx
        obtain ⟨_, hgap⟩ := hcutoff delta hd hsW a b p hwindow.fine_bound
          hwindow.scale_separation hpwindow
        have hTheta : 1 <= (sourceTowerRadius delta M a : Real) / sourceTowerRadius delta M p := by
          apply (le_div_iff₀ (hradR p hpM)).mpr
          simpa using (show (sourceTowerRadius delta M p : Real) <= sourceTowerRadius delta M a by
            exact_mod_cast hmono a p hap hpM)
        have hstrict := hexclusion delta hd hsP _ hTheta hgap
        exact (not_lt_of_ge (hparent (QR.place a x) hj))
          (hstrict.trans (hquarter p hpwindow (QR.place a x) hj))
      have hbefore := hOrder hd hd1.le hwindow.fine_bound hm1 hpm1 hnot
      have hcontained (c d : Nat) (hcd : c <= d) (hdM : d <= M)
          (i : iota) (hi : i ∈ R) :
          (QR.tube d (QR.place d i)).toConvexSpaceBody <=
            (QR.tube c (QR.place c i)).toConvexSpaceBody := by
        induction d, hcd using Nat.le_induction with
        | base => exact le_rfl
        | succ d hcd ih =>
          have hh := QR.parent_containment d (Nat.lt_of_succ_le hdM)
            (QR.place (d + 1) i) (QR.place_mem (d + 1) hdM i hi)
          rw [← QR.parent_composition d (Nat.lt_of_succ_le hdM) i hi] at hh
          exact hh.trans (ih (Nat.le_of_succ_le hdM))
      refine Or.inl ⟨⟨p, hap, hpm1.trans hm1.2.1, hwindow.fine_bound, hbefore, hparent, ?_⟩⟩
      intro ja hja jp hjp m hm hpm
      have hmM : m < M := hm.2.1.trans_le hwindow.fine_bound
      have hjp' : jp ∈ QR.indexSet p := by
        obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp hjp
        exact hxp ▸ QR.place_mem p hpM.le x (Finset.mem_filter.mp hx).1
      have hFr : IsFrostmanIn (QR.fibre p m jp)
          (fun i => (QR.tube m i).toConvexSpaceBody) (QR.tube p jp).toConvexSpaceBody
            (2 * (delta : ENNReal) ^ (-2 * etaParent)) := by
        rcases (hmax m hm).eq_or_lt with heq | hlt
        · subst m
          exact (hfinest jp hjp').mono (le_mul_of_one_le_left' (by norm_num))
        · exact hIntermediate QR ZR hstats hpm.le hlt hm1M.le
            (hrad m1 hm1M).1 (hrad m1 hm1M).2 jp _ (hfinest jp hjp')
      have hWK : forall i, i ∈ QR.fibre p m jp ->
          (QR.tube m i).toConvexSpaceBody <= (QR.tube p jp).toConvexSpaceBody := by
        intro i hi
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
        have hx' := Finset.mem_filter.mp hx
        simpa only [hxi, hx'.2] using hcontained p m hpm.le hmM.le x hx'.1
      have hFrDensity := hFr.maxDensity_le_of_carrier_subset hWK
      have htr := htrace QR ZR hgeom hstats hd hap hpm hmM (hscalegap p m hpm hmM)
        (hrad p hpM).2 _ hparent ja hja jp hjp'
      let Theta : Real := (sourceTowerRadius delta M a : Real) / sourceTowerRadius delta M m
      let r : Real := (sourceTowerRadius delta M p : Real) / sourceTowerRadius delta M m
      have hr : 1 <= r := by
        apply (le_div_iff₀ (hradR m hmM)).mpr
        simpa using (show (sourceTowerRadius delta M m : Real) <= sourceTowerRadius delta M p by
          exact_mod_cast hmono p m hpm.le hmM)
      have hrT : r <= Theta := div_le_div_of_nonneg_right
        (show (sourceTowerRadius delta M p : Real) <= sourceTowerRadius delta M a by
          exact_mod_cast hmono a p hap hpM) (hradR m hmM).le
      have hvol := hVolume (hrad m hmM).2 (hrad p hpM).1
        (QR.fibre p m jp) (QR.tube m) (QR.tube p jp)
      have hcoef : (((_root_.Tube.volume_le.C 3 / _root_.Tube.le_volume.c 3 *
          (sourceTowerRadius delta M m / sourceTowerRadius delta M p) ^ 2 : NNReal)) : ENNReal) =
          ENNReal.ofReal (Cv / r ^ 2) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        congr 1
        simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow]
        change Cv * ((sourceTowerRadius delta M m : Real) / sourceTowerRadius delta M p) ^ 2 =
          Cv / (((sourceTowerRadius delta M p : Real) / sourceTowerRadius delta M m) ^ 2)
        field_simp [(hradR p hpM).ne', (hradR m hmM).ne']
      rw [hcoef] at hvol
      obtain ⟨_, hgap⟩ := hcutoff delta hd hsW a b m hwindow.fine_bound
        hwindow.scale_separation hm
      exact hcount delta hd hsC Theta r hr hrT hgap (QR.fibre p m jp).card
        _ _ _ (hquarter m hm ja hja).le htr hFrDensity hvol
    · push Not at hquarter
      obtain ⟨m, hm, j, hj, hq⟩ := hquarter
      obtain ⟨hnontruncated, hgap⟩ := hcutoff delta hd hsW a b m hwindow.fine_bound
        hwindow.scale_separation hm
      have heta : 0 < eta 1 := hschedule.rung_positive 1 le_rfl
        (by have := hschedule.count_bound; omega)
      have hrung : eta 1 <= eta (J + 1) := hschedule.rung_mono 1 (J + 1) le_rfl
        (by omega) (by have := hschedule.source_index_upper; omega)
      exact Or.inr (source_direct_drop_of_quarter_cell Q hne QR ZR hrest hstats hwindow hm
        hd hd1 he heta hrung hnontruncated hgap hj hq)
  have hEmpty {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C N J A0 A1 K a b : Nat}
      {e etaParent bias etaF : Real} {eta : Nat -> Real} {D : NNReal}
      (Q : SourceThreadedTower S T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (hd : 0 < delta) (hd1 : delta < 1) (hparent : 0 < etaParent)
      (hinput : SourceFixedTowerInput Q A0 A1 etaF) (hstats : SourceTowerStatistics Q Z)
      (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J)
      (hempty : forall m, ¬ SourceTowerWindow delta M e a b m) :
      SourceTerminalWindowOutcome Q Z S Q Z N J A0 A1 e eta etaParent bias etaF K D a b := by
    clear hbeta0 hbeta1 hKT hF hschedule hC hA0 hA1
    clear hPBranch hFD
    classical
    have hrest : SourceTowerRestriction Q Q := {
      subset := le_rfl
      assignment := rfl
      parent := rfl
      tubes := rfl
      occupied := by
        intro k hk
        ext j
        constructor
        · intro hj
          exact Finset.mem_image.mpr (Q.place_surjective k hk j hj)
        · intro hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          exact Q.place_mem k hk i hi
      full_retained_fibres := fun _ _ _ => rfl }
    have hloss : 1 <= sourceFixedPreparationLoss K delta := by
      unfold sourceFixedPreparationLoss
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hlog := Real.logb_nonneg (by norm_num : (1 : Real) < 2)
        (show (1 : Real) <= 1 / (delta : Real) by
          apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
          simpa using (show (delta : Real) <= 1 by exact_mod_cast hd1.le))
      exact one_le_pow₀ (by linarith)
    have hretained : SourceTerminalRetainedState Q Z S Q Z (sourceFixedPreparationLoss K delta) := {
      restriction := hrest
      nonempty := hinput.geometry.nonempty
      original_tubes := hstats.same_tubes
      same_tubes := hstats.same_tubes
      subshade := fun _ => Set.Subset.rfl
      mass := le_mul_of_one_le_left' hloss
      fullness := le_mul_of_one_le_left' hloss
      multiplicity := le_mul_of_one_le_left' hloss }
    obtain ⟨hA, p, hpmax, hp, hap, hpb, hpM, hbefore, hadmissible, hmax⟩ :=
      source_direct_exists_finite_admissible_parent Q hinput.geometry.nonempty
        hd hd1 hparent hwindow.coarse_lt_fine hwindow.fine_bound
    have hfloor : SourceZeroFloor Q e (eta (J + 1)) etaParent a b p := by
      rcases source_direct_floor_or_sparse_at_parent Q hap hpb hwindow.fine_bound
        hbefore hadmissible with hf | ⟨m, j, jp, hm, _⟩
      · exact hf
      · exact (hempty m hm).elim
    exact {
      retained := hretained
      input := hinput
      upper := source_direct_upper_of_restriction Q Q hrest hwindow
      alternative := Or.inr ⟨hstats, Or.inl ⟨⟨p, hfloor⟩⟩⟩ }
  have hLoss {iota : Type u} {delta : NNReal} {S R : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C N J A0 A1 K K' a b : Nat}
      {e etaParent bias etaF : Real} {eta : Nat -> Real} {D : NNReal}
      (Q : SourceThreadedTower S T M C) (QR : SourceThreadedTower R T M C)
      (Z ZR : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (hd : 0 < delta) (hd1 : delta <= 1) (hKK : K <= K')
      (H : SourceTerminalWindowOutcome Q Z R QR ZR N J A0 A1 e eta etaParent bias etaF K D a b) :
      SourceTerminalWindowOutcome Q Z R QR ZR N J A0 A1 e eta etaParent bias etaF K' D a b := by
    clear hbeta0 hbeta1 hKT hF hschedule hC hA0 hA1
    clear hPBranch hFD hEmpty
    have hloss : sourceFixedPreparationLoss K delta <= sourceFixedPreparationLoss K' delta := by
      unfold sourceFixedPreparationLoss
      apply ENNReal.ofReal_le_ofReal
      have hlog := Real.logb_nonneg (by norm_num : (1 : Real) < 2)
        (show (1 : Real) <= 1 / (delta : Real) by
          apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
          simpa using (show (delta : Real) <= 1 by exact_mod_cast hd1))
      exact pow_le_pow_right₀ (by linarith) hKK
    refine {
      retained := { H.retained with
        mass := H.retained.mass.trans (mul_le_mul_left hloss _)
        fullness := H.retained.fullness.trans (mul_le_mul_left hloss _)
        multiplicity := H.retained.multiplicity.trans (mul_le_mul_left hloss _) }
      input := H.input
      upper := H.upper
      alternative := ?_ }
    rcases H.alternative with ⟨P, hstats⟩ | hFD
    · let stage : SourceDirectPlankCellStage Q Z R ZR P.level K' := {
        P.cell_stage with total_loss := P.cell_stage.total_loss.trans hloss }
      let P' : SourceDirectPlank Q Z R QR ZR e etaParent bias a b K' D := {
        P with cell_stage := stage }
      exact Or.inl ⟨P', hstats⟩
    · exact Or.inr hFD
  have hLeafFloor {etaF : Real} (hthin : 3 * etaF < 10) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} {S : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
        (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        S.Nonempty -> SourceTowerStatistics Q Z ->
        (delta : ENNReal) ^ (3 * etaF) <=
          ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
        forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) *
          volume (T i).carrier <= volume (Z i).shade := by
    clear hbeta0 hbeta1 hKT hF hschedule hC hA0 hA1
    clear hPBranch hFD hEmpty hLoss
    filter_upwards [Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg 2
        (show 0 < 10 - 3 * etaF by linarith),
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hsmall hd
    intro iota S T M C Q Z hne hstats hfull
    have hscalarNN : 2 * delta ^ (10 : Real) <= delta ^ (3 * etaF) := by
      calc
        2 * delta ^ (10 : Real) <= delta ^ (-(10 - 3 * etaF)) * delta ^ (10 : Real) := by gcongr
        _ = delta ^ (-(10 - 3 * etaF) + 10) := (NNReal.rpow_add hd.1.ne' _ _).symm
        _ = _ := by congr 1; ring
    have hscalar : (2 : ENNReal) * (delta : ENNReal) ^ (10 : Real) <=
        (delta : ENNReal) ^ (3 * etaF) := by
      rw [← ENNReal.coe_rpow_of_ne_zero hd.1.ne', ← ENNReal.coe_rpow_of_ne_zero hd.1.ne']
      exact_mod_cast hscalarNN
    have hmass : 0 < ∑ i ∈ S, volume (Z i).shade := by
      by_contra h
      have hz := le_antisymm (le_of_not_gt h) zero_le
      have hfzero : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) = 0 := by
        change (∑ i ∈ S, volume (Z i).shade) / _ = 0
        rw [hz, ENNReal.zero_div]
      rw [hfzero] at hfull
      have hp : 0 < (delta : ENNReal) ^ (3 * etaF) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hd.1.ne']
        exact_mod_cast NNReal.rpow_pos (p := 3 * etaF) hd.1
      exact not_le_of_gt hp hfull
    obtain ⟨_, hdense, _⟩ := source_dense_comparable_of_fixed_statistics Q Z hd.1 hne hstats hmass
    intro i hi
    have hf : (delta : ENNReal) ^ (10 : Real) <=
        ShadedBody.fullness' S (fun i => (Z i).toShadedBody) / 2 := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
      simpa only [mul_comm] using hscalar.trans hfull
    have hdense' := hdense i hi
    change (((ShadedBody.fullness S (fun i => (Z i).toShadedBody) / 2 : NNReal) : ENNReal) *
      volume (Z i).carrier) <= volume (Z i).shade at hdense'
    rw [ENNReal.coe_div (by norm_num), ENNReal.coe_two, ShadedBody.coe_fullness] at hdense'
    have hv : volume (Z i).carrier = volume (T i).carrier := by
      change volume (Z i).toTube.carrier = _
      rw [hstats.same_tubes]
    rw [hv] at hdense'
    exact (mul_le_mul_left hf _).trans hdense'
  have hRetained {iota : Type u} {delta : NNReal} {S R : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
      (Q : SourceThreadedTower S T M C) (QR : SourceThreadedTower R T M C)
      (Z ZR : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (L : ENNReal) (hrest : SourceTowerRestriction Q QR) (hne : R.Nonempty)
      (hZ : forall i, (Z i).toTube = T i) (hZR : forall i, (ZR i).toTube = T i)
      (hsub : forall i, (ZR i).shade <= (Z i).shade)
      (hmass : (∑ i ∈ S, volume (Z i).shade) <= L * ∑ i ∈ R, volume (ZR i).shade) :
      SourceTerminalRetainedState Q Z R QR ZR L := by
    clear hbeta0 hbeta1 hKT hF hschedule hC hA0 hA1
    clear hPBranch hFD hEmpty hLoss hLeafFloor
    have hcarrier : forall i, (ZR i).carrier = (Z i).carrier := by
      intro i
      change (ZR i).toTube.carrier = (Z i).toTube.carrier
      rw [hZR, hZ]
    have hden : (∑ i ∈ R, volume (ZR i).carrier) <= ∑ i ∈ S, volume (Z i).carrier := by
      simp_rw [hcarrier]
      exact Finset.sum_le_sum_of_subset hrest.subset
    refine {
      restriction := hrest
      nonempty := hne
      original_tubes := hZ
      same_tubes := hZR
      subshade := hsub
      mass := hmass
      fullness := ?_
      multiplicity := ?_ }
    · change (∑ i ∈ S, volume (Z i).shade) / (∑ i ∈ S, volume (Z i).carrier) <=
        L * ((∑ i ∈ R, volume (ZR i).shade) / (∑ i ∈ R, volume (ZR i).carrier))
      calc
        _ <= (L * ∑ i ∈ R, volume (ZR i).shade) / (∑ i ∈ R, volume (ZR i).carrier) :=
          ENNReal.div_le_div hmass hden
        _ = _ := mul_div_assoc _ _ _
    · apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset S
        (fun i => (Z i).toShadedBody) R (fun i => (ZR i).toShadedBody) L _ hmass
      exact Set.iUnion₂_subset fun i hi =>
        Set.subset_iUnion₂_of_subset i (hrest.subset hi) (hsub i)
  have hBinInput {iota : Type u} {delta : NNReal} {S G R : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
      {M C A0 A1 a m Kstage K : Nat} {eta0 bias : Real} {A D : NNReal}
      (Q : SourceThreadedTower S T M C) (QG : SourceThreadedTower G T M C)
      (QB : SourceThreadedTower R T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage)
      (F : SourceTerminalCommonFactorBin Q Z B R QB D K)
      (hQ : SourceFixedTowerInput Q A0 A1 eta0) (hstats : SourceTowerStatistics Q Z)
      (hd : 0 < delta) (_hd1 : delta <= 1) (_ham : a < m) (hm : m < M)
      (hfloor : ∀ i ∈ S,
        (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade) :
      SourceFixedTowerInput QB A0 A1 eta0 ∧
      (∀ i, (Z i).toTube = T i) ∧
      (∀ i ∈ R,
        (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade) ∧
      (∀ j ∈ QB.indexSet m, 0 < ∑ i ∈ QB.cell m j, volume (Z i).shade) ∧
      (∀ j ∈ QB.indexSet m, (∑ i ∈ QB.cell m j, volume (Z i).shade) < ⊤) ∧
      (∀ j ∈ QB.indexSet m, ∀ j' ∈ QB.indexSet m,
        (∑ i ∈ QB.cell m j, volume (Z i).shade) <=
          2 * ∑ i ∈ QB.cell m j', volume (Z i).shade) ∧
      (∀ {Rf : Finset iota} (QR : SourceThreadedTower Rf T M C),
        SourceTowerRestriction QB QR -> SourceTowerRestriction Q QR) := by
    clear hbeta0 hbeta1 hKT hF hschedule hC hA0 hA1
    clear hPBranch hFD hEmpty hLoss hLeafFloor hRetained
    classical
    have hrest := F.retained.restriction
    have hocc (k : Nat) (hk : k <= M) : QB.indexSet k <= Q.indexSet k := by
      rw [hrest.occupied k hk]
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Q.place_mem k hk i (hrest.subset hi)
    have hQB : SourceFixedTowerInput QB A0 A1 eta0 := {
      geometry := {
        nonempty := F.nonempty
        original_centred := fun i hi => hQ.geometry.original_centred i (hrest.subset hi)
        original_ball := fun i hi => hQ.geometry.original_ball i (hrest.subset hi)
        original_ed := hQ.geometry.original_ed.subset hrest.subset
        coarse_centred := by
          intro k hk j hj
          rw [hrest.tubes]
          exact hQ.geometry.coarse_centred k hk j (hocc k hk.le hj)
        coarse_ball := by
          intro k hk j hj
          rw [hrest.tubes]
          exact hQ.geometry.coarse_ball k hk j (hocc k hk.le hj)
        coarse_ed := by
          intro k hk
          rw [hrest.tubes]
          exact (hQ.geometry.coarse_ed k hk).subset (hocc k hk.le)
        coarse_card := by
          intro k hk
          exact (show ((QB.indexSet k).card : Real) <= (Q.indexSet k).card by
            exact_mod_cast Finset.card_le_card (hocc k hk.le)).trans (hQ.geometry.coarse_card k hk)
        segment_sharing := by
          intro k hk x y hxy
          rw [hrest.tubes]
          exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
            (hQ.geometry.segment_sharing k hk x y hxy) }
      neighbour_sharing := by
        intro k hk j hj
        rw [hrest.tubes]
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
          (hQ.neighbour_sharing k hk j (hocc k hk.le hj))
      maximal_density := (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody)
        hrest.subset).trans hQ.maximal_density }
    refine ⟨hQB, hstats.same_tubes, fun i hi => hfloor i (hrest.subset hi), ?_, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨i, hi, hij⟩ := QB.place_surjective m hm.le j hj
      have hdelta : (0 : ENNReal) < delta := by exact_mod_cast hd
      have hshade : 0 < volume (Z i).shade :=
        (pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.rpow_pos hdelta ENNReal.coe_ne_top).ne'
          (ML2Shaded.volume_carrier_ne_zero hd (T i)))).trans_le
            (hfloor i (hrest.subset hi))
      exact hshade.trans_le (Finset.single_le_sum (f := fun i => volume (Z i).shade)
        (fun _ _ => zero_le) (Finset.mem_filter.mpr ⟨hi, hij⟩))
    · intro j _
      apply lt_top_iff_ne_top.mpr
      exact ENNReal.sum_ne_top.mpr (fun i _ => ne_top_of_le_ne_top
        (Z i).isCompact'.measure_ne_top (measure_mono (Z i).shade_subset))
    · intro j hj j' hj'
      rw [F.middle_cells j hj, F.middle_cells j' hj']
      exact hstats.fibre_mass m hm.le j (hocc m hm.le hj) j' (hocc m hm.le hj')
    · intro Rf QR hf
      exact {
        subset := hf.subset.trans hrest.subset
        assignment := hf.assignment.trans hrest.assignment
        parent := hf.parent.trans hrest.parent
        tubes := hf.tubes.trans hrest.tubes
        occupied := by
          intro k hk
          rw [hf.occupied k hk]
          simp only [SourceThreadedTower.assignedFootprint, hrest.assignment]
        full_retained_fibres := by
          intro a b j
          rw [hf.full_retained_fibres]
          simp only [SourceThreadedTower.retainedAssignedFibre, hrest.assignment] }
  have hGeometry (M C A0 A1 Kprefix : Nat) (eta0 eta bias : Real) (D c : NNReal)
      (hD : 1 <= D) (hc : 0 < c) (heta : 0 < eta) (hbias : bias <= eta / 16)
      (hmesh : 8 / eta <= (M : Real)) :
      ∃ (K : Nat) (delta0 : NNReal), 1 <= K /\ 0 < delta0 /\ delta0 <= 1 /\
      ∀ δ : NNReal, 0 < δ -> δ < delta0 ->
      ∀ {ι : Type u} {S : Finset ι} {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))},
      ∀ (QB : SourceThreadedTower S T M C), SourceFixedTowerInput QB A0 A1 eta0 ->
      ∀ (Z : ι -> ShadedTube δ (EuclideanSpace Real (Fin 3))),
      (∀ i, (Z i).toTube = T i) ->
      (∀ i ∈ S, (δ : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade) ->
      ∀ (a m1 : Nat), a < m1 -> m1 < M ->
      (∀ j ∈ QB.indexSet m1, 0 < ∑ i ∈ QB.cell m1 j, volume (Z i).shade) ->
      (∀ j ∈ QB.indexSet m1, (∑ i ∈ QB.cell m1 j, volume (Z i).shade) < ⊤) ->
      (∀ j ∈ QB.indexSet m1, ∀ k ∈ QB.indexSet m1,
        (∑ i ∈ QB.cell m1 j, volume (Z i).shade) <= 2 * ∑ i ∈ QB.cell m1 k, volume (Z i).shade) ->
      ∀ (aw bw cw : NNReal), 0 < aw -> aw <= bw -> c <= cw -> δ ^ eta * bw <= aw ->
      ∀ (F : ∀ ja, ja ∈ QB.indexSet a ->
        Factorization (QB.fibre a m1 ja) (fun i => (QB.tube m1 i).toConvexSpaceBody)
          (sourceParentPlankConstant δ bias)),
      (∀ ja, ∀ hja : ja ∈ QB.indexSet a, ∀ part, part ∈ (F ja hja).parts ->
        SourceZeroFactorDimensions D aw bw cw
          (part.convexHull_biUnion (fun i => (QB.tube m1 i).toConvexSpaceBody))) ->
      ∃ (p : Nat) (R : Finset ι) (QR : SourceThreadedTower R T M C),
        a <= p /\ p < m1 /\ R.Nonempty /\ SourceTowerRestriction QB QR /\
        SourceFixedTowerInput QR A0 A1 eta0 /\ SourceTowerStatistics QR Z /\
        sourceFixedPreparationLoss Kprefix δ * (∑ i ∈ S, volume (Z i).shade) <=
          sourceFixedPreparationLoss K δ * ∑ i ∈ R, volume (Z i).shade /\
        (∀ ja ∈ QR.indexSet a, Kakeya.maxDensity (QR.fibre a p ja)
          (fun j => (QR.tube p j).toConvexSpaceBody) <= (δ : ENNReal) ^ (-2 * eta)) /\
        ∀ j ∈ QR.indexSet p, IsFrostmanIn (QR.fibre p m1 j)
          (fun i => (QR.tube m1 i).toConvexSpaceBody) (QR.tube p j).toConvexSpaceBody
          ((δ : ENNReal) ^ (-2 * eta)) := by
    clear hbeta0 hbeta1 hKT hF hschedule hC hA0 hA1
    clear hPBranch hFD hEmpty hLoss hLeafFloor hRetained hBinInput
    classical
    have hchain (M C A0 A1 L Kprefix : Nat) (eta0 : Real) :
        ∃ (K : Nat) (delta0 : NNReal), 1 <= K ∧ 0 < delta0 ∧ delta0 <= 1 ∧
        ∀ delta : NNReal, 0 < delta -> delta < delta0 ->
        ∀ {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M C), SourceFixedTowerInput Q A0 A1 eta0 ->
        ∀ (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
          (∀ i, (Z i).toTube = T i) ->
          (∀ i ∈ S, (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade) ->
        ∀ (p q : Nat), p <= q -> q <= M ->
        ∀ (parts : Finpartition (Q.indexSet q)) (parent : iota -> iota),
          (∀ I ∈ parts.parts, (I.image parent).card <= L) ->
          (∀ i ∈ S, parent (Q.place q i) = Q.place p i) ->
          (∀ j ∈ Q.indexSet q, 0 < ∑ i ∈ Q.cell q j, volume (Z i).shade) ->
          (∀ j ∈ Q.indexSet q, (∑ i ∈ Q.cell q j, volume (Z i).shade) < ⊤) ->
          (∀ j ∈ Q.indexSet q, ∀ k ∈ Q.indexSet q,
            (∑ i ∈ Q.cell q j, volume (Z i).shade) <= 2 * ∑ i ∈ Q.cell q k, volume (Z i).shade) ->
        ∃ (H R : Finset iota) (QH : SourceThreadedTower H T M C)
          (QR : SourceThreadedTower R T M C) (pick : Finset iota -> iota),
          H.Nonempty ∧ R.Nonempty ∧ SourceTowerRestriction Q QH ∧
          SourceTowerRestriction QH QR ∧ SourceFixedTowerInput QH A0 A1 eta0 ∧
          SourceFixedTowerInput QR A0 A1 eta0 ∧ SourceTowerStatistics QR Z ∧
          Nonempty (SourceWholeCellStep Q S H q) ∧
          (∀ I ∈ parts.parts, pick I ∈ I.image parent ∧ pick I ∈ QH.indexSet p ∧
            QH.indexSet q ∩ I = I.filter (fun j => parent j = pick I) ∧
            (∑ j ∈ I, ∑ i ∈ Q.cell q j, volume (Z i).shade) <=
              (L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ I, ∑ i ∈ QH.cell q j, volume (Z i).shade ∧
            (∑ j ∈ I, volume (Q.tube q j).carrier) <=
              (2 * L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ I, volume (QH.tube q j).carrier) ∧
          (∑ i ∈ S, volume (Z i).shade) <= (L : ENNReal) * ∑ i ∈ H, volume (Z i).shade ∧
          sourceFixedPreparationLoss Kprefix delta * (∑ i ∈ S, volume (Z i).shade) <=
            sourceFixedPreparationLoss K delta * ∑ i ∈ R, volume (Z i).shade ∧
          (∀ j ∈ QR.indexSet p,
            (∑ i ∈ QH.cell p j, volume (Z i).shade) <=
              sourceFixedPreparationLoss K delta * ∑ i ∈ QR.cell p j, volume (Z i).shade) ∧
          (∀ j ∈ QR.indexSet p,
            (∑ i ∈ QH.fibre p q j, volume (QH.tube q i).carrier) <=
              sourceFixedPreparationLoss K delta * ∑ i ∈ QR.fibre p q j, volume (QR.tube q i).carrier) := by
      clear hD hc heta hbias hmesh
      classical
      have hChain (M C A0 A1 L : Nat) (eta0 : Real)
          {iota : Type u} {delta : NNReal} {S : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
          (Q : SourceThreadedTower S T M C) (hQ : SourceFixedTowerInput Q A0 A1 eta0)
          (hd : 0 < delta) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
          (hZT : ∀ i, (Z i).toTube = T i)
          (v m : ENNReal) (hv0 : v ≠ 0) (hvt : v ≠ ⊤) (hm0 : m ≠ 0) (hm1 : m <= 1)
          (hvol : ∀ i ∈ S, volume (T i).carrier = v)
          (hfloor : ∀ i ∈ S, m * v <= volume (Z i).shade)
          (J : Nat) (hJ : (S.card : ENNReal) <= 2 ^ J * m)
          (p q : Nat) (hpq : p <= q) (hq : q <= M)
          (parts : Finpartition (Q.indexSet q)) (parent : iota -> iota)
          (hgroups : ∀ I ∈ parts.parts, (I.image parent).card <= L)
          (hancestor : ∀ i ∈ S, parent (Q.place q i) = Q.place p i)
          (hpos : ∀ j ∈ Q.indexSet q, 0 < ∑ i ∈ Q.cell q j, volume (Z i).shade)
          (hfinite : ∀ j ∈ Q.indexSet q, (∑ i ∈ Q.cell q j, volume (Z i).shade) < ⊤)
          (hunif : ∀ j ∈ Q.indexSet q, ∀ k ∈ Q.indexSet q,
            (∑ i ∈ Q.cell q j, volume (Z i).shade) <= 2 * ∑ i ∈ Q.cell q k, volume (Z i).shade) :
          let reg : ENNReal := (((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1)
          let band : ENNReal := ENNReal.ofReal (1 + Real.logb 2 (2 * (Q.indexSet q).card : Real))
          ∃ (H R : Finset iota) (QH : SourceThreadedTower H T M C)
            (QR : SourceThreadedTower R T M C) (pick : Finset iota -> iota),
            H.Nonempty ∧ R.Nonempty ∧ SourceTowerRestriction Q QH ∧
            SourceTowerRestriction QH QR ∧ SourceFixedTowerInput QH A0 A1 eta0 ∧
            SourceFixedTowerInput QR A0 A1 eta0 ∧ SourceTowerStatistics QR Z ∧
            Nonempty (SourceWholeCellStep Q S H q) ∧
            (∀ I ∈ parts.parts, pick I ∈ I.image parent ∧ pick I ∈ QH.indexSet p ∧
              QH.indexSet q ∩ I = I.filter (fun j => parent j = pick I) ∧
              (∑ j ∈ I, ∑ i ∈ Q.cell q j, volume (Z i).shade) <=
                (L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ I, ∑ i ∈ QH.cell q j, volume (Z i).shade ∧
              (∑ j ∈ I, volume (Q.tube q j).carrier) <=
                (2 * L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ I, volume (QH.tube q j).carrier) ∧
            (∑ i ∈ S, volume (Z i).shade) <= (L : ENNReal) * ∑ i ∈ H, volume (Z i).shade ∧
            (∑ i ∈ S, volume (Z i).shade) <= ((L : ENNReal) * band * reg) * ∑ i ∈ R, volume (Z i).shade ∧
            (∀ j ∈ QR.indexSet p,
              (∑ i ∈ QH.cell p j, volume (Z i).shade) <= 4 * reg * ∑ i ∈ QR.cell p j, volume (Z i).shade) ∧
            (∀ j ∈ QR.indexSet p,
              (∑ i ∈ QH.fibre p q j, volume (QH.tube q i).carrier) <=
                (8 * reg) * ∑ i ∈ QR.fibre p q j, volume (QR.tube q i).carrier) := by
        classical
        dsimp only
        have hrestrict : ∀ {delta : NNReal} {iota : Type u} {ambient : Finset iota}
            {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
            (Q : SourceThreadedTower ambient T M C), SourceFixedTowerInput Q A0 A1 eta0 ->
            ∀ R : Finset iota, R <= ambient -> R.Nonempty ->
            ∃ Q' : SourceThreadedTower R T M C,
              SourceTowerRestriction Q Q' /\ SourceFixedTowerInput Q' A0 A1 eta0 := by
          intro delta iota ambient T Q hQ R hR hRne
          have hocc (k : Nat) (hk : k <= M) : Q.assignedFootprint R k <= Q.indexSet k := by
            intro j hj
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
            exact Q.place_mem k hk i (hR hi)
          let Q' : SourceThreadedTower R T M C := {
            indexSet := Q.assignedFootprint R
            place := Q.place
            parent := Q.parent
            tube := Q.tube
            tube_injective := fun k hk i hi j hj => Q.tube_injective k hk (hocc k hk hi) (hocc k hk hj)
            place_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
            place_surjective := fun k _ j hj => Finset.mem_image.mp hj
            leaf_containment := fun k hk i hi => Q.leaf_containment k hk i (hR hi)
            parent_mem := by
              intro k hk j hj
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
              rw [← Q.parent_composition k hk i (hR hi)]
              exact Finset.mem_image_of_mem _ hi
            parent_composition := fun k hk i hi => Q.parent_composition k hk i (hR hi)
            parent_containment := fun k hk j hj => Q.parent_containment k hk j (hocc (k + 1) (by omega) hj)
            bottom_index := by
              ext i
              constructor
              · intro hi
                obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
                rw [Q.bottom_place j (hR hj)] at hji
                exact hji ▸ hj
              · intro hi
                exact Finset.mem_image.mpr ⟨i, hi, Q.bottom_place i (hR hi)⟩
            bottom_place := fun i hi => Q.bottom_place i (hR hi)
            bottom_body := fun i hi => Q.bottom_body i (hR hi)
            containment_multiplicity := by
              intro k hk i hi
              exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk))).trans
                (Q.containment_multiplicity k hk i (hR hi)) }
          have hrest : SourceTowerRestriction Q Q' := {
            subset := hR
            assignment := rfl
            parent := rfl
            tubes := rfl
            occupied := fun _ _ => rfl
            full_retained_fibres := fun _ _ _ => rfl }
          refine ⟨Q', hrest, {
            geometry := {
              nonempty := hRne
              original_centred := fun i hi => hQ.geometry.original_centred i (hR hi)
              original_ball := fun i hi => hQ.geometry.original_ball i (hR hi)
              original_ed := hQ.geometry.original_ed.subset hR
              coarse_centred := fun k hk j hj => hQ.geometry.coarse_centred k hk j (hocc k hk.le hj)
              coarse_ball := fun k hk j hj => hQ.geometry.coarse_ball k hk j (hocc k hk.le hj)
              coarse_ed := fun k hk => (hQ.geometry.coarse_ed k hk).subset (hocc k hk.le)
              coarse_card := by
                intro k hk
                calc ((Q.assignedFootprint R k).card : Real) <= ((Q.indexSet k).card : Real) := by
                      exact_mod_cast Finset.card_le_card (hocc k hk.le)
                  _ <= (32 / (sourceTowerRadius delta M k : Real)) ^ 6 := hQ.geometry.coarse_card k hk
              segment_sharing := ?_ }
            neighbour_sharing := ?_
            maximal_density := (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hR).trans
              hQ.maximal_density }⟩
          · intro k hk x y hxy
            exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
              (hQ.geometry.segment_sharing k hk x y hxy)
          · intro k hk j hj
            exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
              (hQ.neighbour_sharing k hk j (hocc k hk.le hj))
        have hregular : ∀ {delta : NNReal}, 0 < delta ->
            ∀ {iota : Type u} {ambient : Finset iota}
              {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
              (Q : SourceThreadedTower ambient T M C), SourceFixedTowerInput Q A0 A1 eta0 ->
            ∀ (S : Finset iota), S <= ambient -> S.Nonempty ->
            ∀ (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
              (∀ i, (Z i).toTube = T i) ->
            ∀ (v m : ENNReal), v ≠ 0 -> v ≠ ⊤ -> m ≠ 0 -> m <= 1 ->
              (∀ i ∈ ambient, volume (T i).carrier = v) ->
              (∀ i ∈ S, m * v <= volume (Z i).shade) ->
            ∀ J : Nat, (ambient.card : ENNReal) <= 2 ^ J * m ->
            ∃ (R : Finset iota) (Q' : SourceThreadedTower R T M C),
              R <= S /\ R.Nonempty /\ SourceTowerRestriction Q Q' /\
              SourceFixedTowerInput Q' A0 A1 eta0 /\ SourceTowerStatistics Q' Z /\
              (∑ i ∈ S, volume (Z i).shade) <=
                (((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1) * ∑ i ∈ R, volume (Z i).shade := by
          intro delta hdelta iota ambient T Q hQ S hS hSne Z hZT v m hv0 hvtop hm0 hm1 hvol hfloor J hJ
          have hcoarse (b : Nat) (hb : b <= M) : ∀ a, a <= b -> ∀ i ∈ ambient, ∀ j ∈ ambient,
              Q.place b i = Q.place b j -> Q.place a i = Q.place a j := by
            induction b with
            | zero =>
                intro a ha i hi j hj heq
                simpa only [Nat.eq_zero_of_le_zero ha] using heq
            | succ b ih =>
                intro a ha i hi j hj heq
                by_cases hab : a = b + 1
                · simpa only [hab] using heq
                · apply ih (by omega) a (by omega) i hi j hj
                  rw [Q.parent_composition b (by omega) i hi, Q.parent_composition b (by omega) j hj, heq]
          have hradius (k : Nat) : 0 < sourceTowerRadius delta M k := by
            unfold sourceTowerRadius
            split
            · positivity
            · exact hdelta
          let cell (k : Nat) (R : Finset iota) (i : iota) := R.filter fun j => Q.place k j = Q.place k i
          let fib (k b : Nat) (R : Finset iota) (i : iota) := (cell k R i).image (Q.place b)
          let mass (k : Nat) (R : Finset iota) (i : iota) := (∑ j ∈ cell k R i, volume (Z j).shade) / v
          let row (k q : Nat) (R : Finset iota) (i : iota) : ENNReal :=
            if q < M + 1 then Kakeya.maxDensity (fib k q R i) (fun j => (Q.tube q j).toConvexSpaceBody)
            else if q < 2 * M + 2 then ((fib k (q - (M + 1)) R i).card : ENNReal)
            else if q < 2 * M + 3 then ((cell k R i).card : ENNReal)
            else mass k R i
          have hcellmem (k : Nat) {R : Finset iota} {i : iota} (hi : i ∈ R) : i ∈ cell k R i :=
            Finset.mem_filter.mpr ⟨hi, rfl⟩
          have hcellsub (k : Nat) (R : Finset iota) (i : iota) : cell k R i <= R := Finset.filter_subset _ _
          have hfibcard (k b : Nat) (R : Finset iota) (i : iota) : (fib k b R i).card <= R.card :=
            Finset.card_image_le.trans (Finset.card_le_card (hcellsub k R i))
          have hmasslo (k : Nat) {R : Finset iota} (hR : R <= S) {i : iota} (hi : i ∈ R) :
              m <= mass k R i := by
            apply (ENNReal.le_div_iff_mul_le (.inl hv0) (.inl hvtop)).mpr
            exact (hfloor i (hR hi)).trans
              (Finset.single_le_sum (f := fun j => volume (Z j).shade) (fun _ _ => zero_le) (hcellmem k hi))
          have hmasshi (k : Nat) {R : Finset iota} (hR : R <= S) (i : iota) :
              mass k R i <= (ambient.card : ENNReal) := by
            apply (ENNReal.div_le_iff hv0 hvtop).mpr
            calc (∑ j ∈ cell k R i, volume (Z j).shade) <= ∑ j ∈ cell k R i, v := by
                  apply Finset.sum_le_sum
                  intro j hj
                  have hzv : volume (Z j).carrier = v := by
                    change volume (Z j).toTube.carrier = v
                    rw [hZT j]
                    exact hvol j (hS (hR (hcellsub k R i hj)))
                  exact hzv ▸ measure_mono (Z j).shade_subset
              _ = ((cell k R i).card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
              _ <= (ambient.card : ENNReal) * v := by
                  apply mul_le_mul_left
                  exact_mod_cast Finset.card_le_card ((hcellsub k R i).trans (hR.trans hS))
          have hrowlo (k q : Nat) {R : Finset iota} (hR : R <= S) {i : iota} (hi : i ∈ R) :
              m <= row k q R i := by
            unfold row
            split
            · apply hm1.trans
              apply Kakeya.one_le_maxDensity
              refine ⟨Q.place q i, Finset.mem_image_of_mem _ (hcellmem k hi), ?_⟩
              exact pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero (hradius q) (Q.tube q (Q.place q i)))
            · split
              · apply hm1.trans
                exact_mod_cast Finset.card_pos.mpr ⟨Q.place (q - (M + 1)) i,
                  Finset.mem_image_of_mem _ (hcellmem k hi)⟩
              · split
                · apply hm1.trans
                  exact_mod_cast Finset.card_pos.mpr ⟨i, hcellmem k hi⟩
                · exact hmasslo k hR hi
          have hrowhi (k q : Nat) {R : Finset iota} (hR : R <= S) (i : iota) :
              row k q R i <= (ambient.card : ENNReal) := by
            have hRc : R.card <= ambient.card := Finset.card_le_card (hR.trans hS)
            unfold row
            split
            · exact (Kakeya.maxDensity_le_card _ _).trans (by exact_mod_cast (hfibcard k q R i).trans hRc)
            · split
              · exact_mod_cast (hfibcard k (q - (M + 1)) R i).trans hRc
              · split
                · exact_mod_cast (Finset.card_le_card (hcellsub k R i)).trans hRc
                · exact hmasshi k hR i
          have hrowlocal (k q : Nat) : LeafLocalStat (Q.place k) (row k q) := by
            intro R R' i heq
            change cell k R i = cell k R' i at heq
            simp only [row, fib, mass, heq]
          have hroweq (k q : Nat) (R : Finset iota) (i j : iota) (hij : Q.place k i = Q.place k j) :
              row k q R i = row k q R j := by
            have heq : cell k R i = cell k R j := by simp only [cell, hij]
            simp only [row, fib, mass, heq]
          have hmass0 : (∑ i ∈ S, volume (Z i).shade) ≠ 0 := by
            obtain ⟨i, hi⟩ := hSne
            intro hzero
            have hizero := Finset.sum_eq_zero_iff.mp hzero i hi
            exact mul_ne_zero hm0 hv0 (le_antisymm (hizero ▸ hfloor i hi) zero_le)
          obtain ⟨R, hRS, hRne, hmassR, -, Phi, hPhi⟩ :=
            exists_multiLevel_band_wt (n := 2 * M + 4) (γ := iota) S
              (fun i => volume (Z i).shade) hmass0 (fun p => Q.place (M - p))
              (fun p q hpq i hi j hj heq => hcoarse (M - p) (Nat.sub_le _ _) (M - q)
                (Nat.sub_le_sub_left hpq M) i (hS hi) j (hS hj) heq)
              (fun p q R i => row (M - p) q R i)
              (fun p q => hrowlocal (M - p) q)
              (fun p q R i => dyadicScaleBucket m (row (M - p) q R i))
              (fun p q R i j hij => congrArg (dyadicScaleBucket m) (hroweq (M - p) q R i j hij))
              (J + 1) (Nat.succ_pos J)
              (fun p q R hR i _ => dyadicScaleBucket_lt_succ ((hrowhi (M - p) q hR i).trans hJ))
              (fun p q R hR i hi j hj heq => le_two_mul_of_dyadicScaleBucket_eq
                ⟨J, (hrowhi (M - p) q hR i).trans hJ⟩
                ⟨J, (hrowhi (M - p) q hR j).trans hJ⟩ (hrowlo (M - p) q hR hi) heq)
              (fun _ _ => 0) 1 (by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ _ => rfl) M
          obtain ⟨Q', hrest, hQ'⟩ := hrestrict Q hQ R (hRS.trans hS) hRne
          have hband (k : Nat) (hk : k <= M) (q : Fin (2 * M + 4))
              (i : iota) (hi : i ∈ R) (j : iota) (hj : j ∈ R) :
              row k q R i <= 2 * row k q R j := by
            have hi' := hPhi (M - k) (Nat.sub_le _ _) q i hi
            have hj' := hPhi (M - k) (Nat.sub_le _ _) q j hj
            rw [Nat.sub_sub_self hk] at hi' hj'
            exact hi'.2.trans (mul_le_mul_right hj'.1 2)
          have hcellEq (k : Nat) (i : iota) : cell k R i = Q'.cell k (Q'.place k i) := by
            simp only [cell, SourceThreadedTower.cell, hrest.assignment]
          have hfibEq (k b : Nat) (i : iota) : fib k b R i = Q'.fibre k b (Q'.place k i) := by
            simp only [fib, SourceThreadedTower.fibre, hcellEq, hrest.assignment]
          refine ⟨R, Q', hRS, hRne, hrest, hQ', {
            same_tubes := hZT
            descendant_count := ?_
            two_level_count := ?_
            two_level_density := ?_
            fibre_mass := ?_ }, by simpa only [Nat.cast_one, one_mul] using hmassR⟩
          · intro k hk j hj j' hj'
            obtain ⟨i, hi, rfl⟩ := Q'.place_surjective k hk j hj
            obtain ⟨i', hi', rfl⟩ := Q'.place_surjective k hk j' hj'
            have hband' := hband k hk ⟨2 * M + 2, by omega⟩ i hi i' hi'
            simpa only [row, show ¬ 2 * M + 2 < M + 1 by omega, if_false,
              show ¬ 2 * M + 2 < 2 * M + 2 by omega, show 2 * M + 2 < 2 * M + 3 by omega,
              if_true, hcellEq] using hband'
          · intro a b hab hb j hj j' hj'
            obtain ⟨i, hi, rfl⟩ := Q'.place_surjective a (by omega) j hj
            obtain ⟨i', hi', rfl⟩ := Q'.place_surjective a (by omega) j' hj'
            have hband' := hband a (by omega) ⟨M + 1 + b, by omega⟩ i hi i' hi'
            simpa only [row, show ¬ M + 1 + b < M + 1 by omega, if_false,
              show M + 1 + b < 2 * M + 2 by omega, if_true, Nat.add_sub_cancel_left, hfibEq] using hband'
          · intro a b hab hb j hj j' hj'
            obtain ⟨i, hi, rfl⟩ := Q'.place_surjective a (by omega) j hj
            obtain ⟨i', hi', rfl⟩ := Q'.place_surjective a (by omega) j' hj'
            have hband' := hband a (by omega) ⟨b, by omega⟩ i hi i' hi'
            simpa only [row, show b < M + 1 by omega, if_true, hfibEq, hrest.tubes] using hband'
          · intro k hk j hj j' hj'
            obtain ⟨i, hi, rfl⟩ := Q'.place_surjective k hk j hj
            obtain ⟨i', hi', rfl⟩ := Q'.place_surjective k hk j' hj'
            have hband' := hband k hk ⟨2 * M + 3, by omega⟩ i hi i' hi'
            simp only [row, show ¬ 2 * M + 3 < M + 1 by omega, if_false,
              show ¬ 2 * M + 3 < 2 * M + 2 by omega, show ¬ 2 * M + 3 < 2 * M + 3 by omega,
              mass, hcellEq] at hband'
            simpa only [mul_assoc, ENNReal.div_mul_cancel hv0 hvtop] using mul_le_mul_left hband' v
      
        have hheavy {ι κ : Type u} [Nonempty κ] {s : Finset ι}
            (parts : Finpartition s) (parent : ι -> κ) (w : ι -> ENNReal) (L : Nat)
            (hcard : ∀ J ∈ parts.parts, (J.image parent).card <= L) :
            ∃ (pick : Finset ι -> κ) (R : Finset ι), R <= s /\
              (∀ J ∈ parts.parts, pick J ∈ J.image parent /\
                R ∩ J = J.filter (fun i => parent i = pick J) /\
                (∑ i ∈ J, w i) <= (L : ENNReal) * ∑ i ∈ R ∩ J, w i) /\
              (∑ i ∈ s, w i) <= (L : ENNReal) * ∑ i ∈ R, w i := by
          classical
          have hheavy (J : Finset ι) (hJ : J ∈ parts.parts) : ∃ p ∈ J.image parent,
              (∑ i ∈ J, w i) <= (L : ENNReal) * ∑ i ∈ J.filter (fun i => parent i = p), w i := by
            have hne := (parts.nonempty_of_mem_parts hJ).image parent
            let g p := ∑ i ∈ J.filter (fun i => parent i = p), w i
            obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (J.image parent) g hne
            refine ⟨p, hp, ?_⟩
            have hsum : (∑ p ∈ J.image parent, g p) = ∑ i ∈ J, w i :=
              Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem parent hi) w
            calc
              _ = ∑ p ∈ J.image parent, g p := hsum.symm
              _ <= ((J.image parent).card : ENNReal) * g p := by
                simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul (J.image parent) g (g p) hmax
              _ <= (L : ENNReal) * g p := by gcongr; exact_mod_cast hcard J hJ
          have hchoose (J : Finset ι) : ∃ p : κ, J ∈ parts.parts ->
              p ∈ J.image parent /\ (∑ i ∈ J, w i) <=
                (L : ENNReal) * ∑ i ∈ J.filter (fun i => parent i = p), w i := by
            by_cases hJ : J ∈ parts.parts
            · obtain ⟨p, hp, hpay⟩ := hheavy J hJ
              exact ⟨p, fun _ => ⟨hp, hpay⟩⟩
            · exact ⟨Classical.arbitrary κ, fun h => (hJ h).elim⟩
          choose pick hpick using hchoose
          let G (J : Finset ι) := J.filter (fun i => parent i = pick J)
          let R := parts.parts.biUnion G
          have hGsub (J : Finset ι) : G J <= J := Finset.filter_subset _ _
          have hRsub : R <= s := by
            intro i hi
            obtain ⟨J, hJ, hiJ⟩ := Finset.mem_biUnion.mp hi
            exact parts.le hJ (hGsub J hiJ)
          have hinter (J : Finset ι) (hJ : J ∈ parts.parts) : R ∩ J = G J := by
            ext i
            constructor
            · intro hi
              obtain ⟨hRi, hiJ⟩ := Finset.mem_inter.mp hi
              obtain ⟨K, hK, hiK⟩ := Finset.mem_biUnion.mp hRi
              have hKJ : K = J := parts.eq_of_mem_parts hK hJ (hGsub K hiK) hiJ
              simpa only [hKJ] using hiK
            · intro hi
              exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨J, hJ, hi⟩, hGsub J hi⟩
          have hGdis : (parts.parts : Set (Finset ι)).PairwiseDisjoint G := by
            intro J hJ K hK hne
            exact (parts.disjoint hJ hK hne).mono (hGsub J) (hGsub K)
          refine ⟨pick, R, hRsub, ?_, ?_⟩
          · intro J hJ
            refine ⟨(hpick J hJ).1, hinter J hJ, ?_⟩
            rw [hinter J hJ]
            exact (hpick J hJ).2
          · calc
              _ = ∑ J ∈ parts.parts, ∑ i ∈ J, w i := by
                calc
                  _ = ∑ i ∈ parts.parts.biUnion id, w i :=
                    congrArg (fun I : Finset ι => ∑ i ∈ I, w i) parts.biUnion_parts.symm
                  _ = _ := Finset.sum_biUnion parts.disjoint
              _ <= ∑ J ∈ parts.parts, (L : ENNReal) * ∑ i ∈ G J, w i :=
                Finset.sum_le_sum (fun J hJ => (hpick J hJ).2)
              _ = (L : ENNReal) * ∑ J ∈ parts.parts, ∑ i ∈ G J, w i := by rw [Finset.mul_sum]
              _ = (L : ENNReal) * ∑ i ∈ R, w i := by
                dsimp [R]
                rw [Finset.sum_biUnion hGdis]
      
        have hinterval {ι : Type u} (I : Finset ι) (f : ι -> ENNReal) (hne : I.Nonempty)
            (hpos : ∀ i ∈ I, 0 < f i) (hfinite : ∀ i ∈ I, f i < ⊤)
            (hunif : ∀ i ∈ I, ∀ j ∈ I, f i <= 2 * f j) :
            ∃ μ : NNReal, 0 < μ /\ ∀ J : Finset ι, J <= I -> J.Nonempty ->
              (∑ i ∈ J, f i) ∈ Set.Icc (μ : ENNReal) (((2 * I.card) * μ : NNReal) : ENNReal) := by
          classical
          obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image I f hne
          let μ := (f i0).toNNReal
          have hμ : (μ : ENNReal) = f i0 := ENNReal.coe_toNNReal (hfinite i0 hi0).ne
          have hμpos : 0 < μ := by
            have h : (0 : ENNReal) < μ := by rw [hμ]; exact hpos i0 hi0
            exact_mod_cast h
          refine ⟨μ, hμpos, ?_⟩
          intro J hJI hJ
          obtain ⟨j, hj⟩ := hJ
          constructor
          · rw [hμ]
            exact (hmin j (hJI hj)).trans (Finset.single_le_sum (fun i hi => zero_le) hj)
          · calc
              _ <= ∑ i ∈ J, 2 * f i0 := Finset.sum_le_sum (fun i hi => hunif i (hJI hi) i0 hi0)
              _ = ((2 * J.card : NNReal) : ENNReal) * f i0 := by simp; ring
              _ <= ((2 * I.card : NNReal) : ENNReal) * f i0 := by
                gcongr
                exact hJI
              _ = _ := by simp only [ENNReal.coe_mul, hμ]
      
        have hsumCells {ι : Type u} {δ : NNReal} {S : Finset ι}
            {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C p m : Nat}
            (Q : SourceThreadedTower S T M C) (hpm : p <= m) (hm : m <= M) (w : ι -> ENNReal) :
            ∀ jp, (∑ i ∈ Q.cell p jp, w i) =
              ∑ j ∈ Q.fibre p m jp, ∑ i ∈ Q.cell m j, w i := by
          classical
          have hcompatible (a b : Nat) (hab : a <= b) (hb : b <= M)
              (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
              (heq : Q.place b i = Q.place b j) : Q.place a i = Q.place a j := by
            induction b, hab using Nat.le_induction with
            | base => exact heq
            | succ b hab ih =>
              apply ih (Nat.le_of_succ_le hb)
              rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
                Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
          intro jp
          have hsubcell (j : ι) (hj : j ∈ Q.fibre p m jp) :
              (Q.cell p jp).filter (fun i => Q.place m i = j) = Q.cell m j := by
            obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hj
            have hx' := Finset.mem_filter.mp hx
            ext i
            simp only [SourceThreadedTower.cell, Finset.mem_filter]
            constructor
            · exact fun h => ⟨h.1.1, h.2⟩
            · rintro ⟨hi, hij⟩
              exact ⟨⟨hi, (hcompatible p m hpm hm i hi x hx'.1
                (hij.trans hxm.symm)).trans hx'.2⟩, hij⟩
          calc
            _ = ∑ j ∈ Q.fibre p m jp, ∑ i ∈ (Q.cell p jp).filter (fun i => Q.place m i = j), w i := by
              symm
              exact Finset.sum_fiberwise_of_maps_to
                (fun i hi => Finset.mem_image_of_mem (Q.place m) hi) w
            _ = _ := Finset.sum_congr rfl (fun j hj => by rw [hsubcell j hj])
      
        have hband {ι : Type u} {δ : NNReal} {S : Finset ι}
            {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C p : Nat}
            (Q : SourceThreadedTower S T M C) (hp : p <= M) (w : ι -> ENNReal)
            (μ B : NNReal) (hμ : 0 < μ)
            (hmass : 0 < ∑ i ∈ S, w i)
            (hbound : ∀ j ∈ Q.indexSet p,
              (∑ i ∈ Q.cell p j, w i) ∈ Set.Icc (μ : ENNReal) ((B * μ : NNReal) : ENNReal)) :
            ∃ R : Finset ι, R.Nonempty /\ R <= S /\
              Nonempty (SourceWholeCellStep Q S R p) /\
              (∑ i ∈ S, w i) <= ENNReal.ofReal (1 + Real.logb 2 (B : Real)) * ∑ i ∈ R, w i /\
              (∀ j ∈ Q.assignedFootprint R p, ∀ j' ∈ Q.assignedFootprint R p,
                (∑ i ∈ R.filter (fun i => Q.place p i = j), w i) <=
                  2 * ∑ i ∈ R.filter (fun i => Q.place p i = j'), w i) := by
          classical
          let f j := ∑ i ∈ Q.cell p j, w i
          obtain ⟨J, hJsub, hpay, hcomp⟩ := ENNReal.dyadic_pigeonhole₁'' (Q.indexSet p) f f hμ hbound
          have hμr : (μ : Real) ≠ 0 := by exact_mod_cast hμ.ne'
          have hratio : ((B * μ : NNReal) : Real) / μ = B := by
            rw [NNReal.coe_mul, mul_div_cancel_right₀ _ hμr]
          rw [hratio] at hpay
          let R := S.filter (fun i => Q.place p i ∈ J)
          have hRS : R <= S := Finset.filter_subset _ _
          have hsum : (∑ j ∈ Q.indexSet p, f j) = ∑ i ∈ S, w i :=
            Finset.sum_fiberwise_of_maps_to (Q.place_mem p hp) _
          have hsumR : (∑ j ∈ J, f j) = ∑ i ∈ R, w i := by
            exact Finset.sum_fiberwise_eq_sum_filter _ _ _ _
          rw [hsum, hsumR] at hpay
          have hRne : R.Nonempty := by
            by_contra h
            have he := Finset.not_nonempty_iff_eq_empty.mp h
            rw [he, Finset.sum_empty, mul_zero] at hpay
            exact (not_le_of_gt hmass) hpay
          have hwhole (j : ι) (hj : j ∈ J) : R.filter (fun i => Q.place p i = j) = Q.cell p j := by
            ext i
            simp only [SourceThreadedTower.cell, Finset.mem_filter]
            constructor
            · rintro ⟨hi, heq⟩
              exact ⟨hRS hi, heq⟩
            · rintro ⟨hi, heq⟩
              exact ⟨Finset.mem_filter.mpr ⟨hi, heq ▸ hj⟩, heq⟩
          have hfoot : Q.assignedFootprint R p = J := by
            ext j
            constructor
            · intro hj
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
              exact (Finset.mem_filter.mp hi).2
            · intro hj
              obtain ⟨i, hi, hij⟩ := Q.place_surjective p hp j (hJsub hj)
              exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij ▸ hj⟩, hij⟩
          refine ⟨R, hRne, hRS, ⟨{
            selected := J
            selected_subset := ?_
            leaves_eq := rfl
            complete := hwhole }⟩, hpay, ?_⟩
          · intro j hj
            obtain ⟨i, hi, hij⟩ := Q.place_surjective p hp j (hJsub hj)
            exact Finset.mem_image.mpr ⟨i, hi, hij⟩
          · intro j hj j' hj'
            rw [hfoot] at hj hj'
            rw [hwhole j hj, hwhole j' hj']
            exact hcomp j hj j' hj'
      
        have hretention {ι : Type u} {δ : NNReal} {S R : Finset ι}
            {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C p : Nat}
            (Q : SourceThreadedTower S T M C) (Q' : SourceThreadedTower R T M C)
            (Z Z' : ι -> ShadedTube δ (EuclideanSpace Real (Fin 3)))
            (H : ENNReal) (hp : p <= M) (hrest : SourceTowerRestriction Q Q')
            (hbefore : ∀ j ∈ Q.indexSet p, ∀ j' ∈ Q.indexSet p,
              (∑ i ∈ Q.cell p j, volume (Z i).shade) <= 2 * ∑ i ∈ Q.cell p j', volume (Z i).shade)
            (hstats' : SourceTowerStatistics Q' Z')
            (hpaid : (∑ i ∈ S, volume (Z i).shade) <= H * ∑ i ∈ R, volume (Z' i).shade) :
            ∀ j ∈ Q'.indexSet p, (∑ i ∈ Q.cell p j, volume (Z i).shade) <=
              (4 * H) * ∑ i ∈ Q'.cell p j, volume (Z' i).shade := by
          classical
          let f j := ∑ i ∈ Q.cell p j, volume (Z i).shade
          let g j := ∑ i ∈ Q'.cell p j, volume (Z' i).shade
          have hindex : Q'.indexSet p <= Q.indexSet p := by
            rw [hrest.occupied p hp]
            intro j hj
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
            exact Q.place_mem p hp i (hrest.subset hi)
          have hsum : (∑ j ∈ Q.indexSet p, f j) = ∑ i ∈ S, volume (Z i).shade :=
            Finset.sum_fiberwise_of_maps_to (Q.place_mem p hp) _
          have hsum' : (∑ j ∈ Q'.indexSet p, g j) = ∑ i ∈ R, volume (Z' i).shade :=
            Finset.sum_fiberwise_of_maps_to (Q'.place_mem p hp) _
          have hcard : ((Q'.indexSet p).card : ENNReal) <= (Q.indexSet p).card := by
            exact_mod_cast Finset.card_le_card hindex
          intro j hj
          have hIne : ((Q.indexSet p).card : ENNReal) ≠ 0 := by
            exact_mod_cast Finset.card_ne_zero_of_mem (hindex hj)
          apply (ENNReal.mul_le_mul_iff_right hIne (ENNReal.natCast_ne_top _)).mp
          change ((Q.indexSet p).card : ENNReal) * f j <=
            ((Q.indexSet p).card : ENNReal) * ((4 * H) * g j)
          calc
            _ = ∑ i ∈ Q.indexSet p, f j := by simp
            _ <= ∑ i ∈ Q.indexSet p, 2 * f i :=
              Finset.sum_le_sum (fun i hi => hbefore j (hindex hj) i hi)
            _ = 2 * ∑ i ∈ Q.indexSet p, f i := by rw [Finset.mul_sum]
            _ <= 2 * (H * ∑ i ∈ Q'.indexSet p, g i) := by
              rw [hsum, hsum']
              exact mul_le_mul' le_rfl hpaid
            _ <= 2 * (H * ∑ i ∈ Q'.indexSet p, 2 * g j) :=
              mul_le_mul' le_rfl (mul_le_mul' le_rfl
                (Finset.sum_le_sum (fun i hi => hstats'.fibre_mass p hp i hi j hj)))
            _ = 2 * (H * (((Q'.indexSet p).card : ENNReal) * (2 * g j))) := by simp
            _ <= 2 * (H * (((Q.indexSet p).card : ENNReal) * (2 * g j))) := by gcongr
            _ = ((Q.indexSet p).card : ENNReal) * ((4 * H) * g j) := by ring
      
        have hcount {ι : Type u} (I J : Finset ι) (f g : ι -> ENNReal) (H : ENNReal)
            (hJI : J <= I) (hne : J.Nonempty)
            (hpos : ∀ i ∈ I, 0 < f i) (hfinite : ∀ i ∈ I, f i < ⊤)
            (hunif : ∀ i ∈ I, ∀ j ∈ I, f i <= 2 * f j)
            (hg : ∀ j ∈ J, g j <= f j)
            (hpaid : (∑ i ∈ I, f i) <= H * ∑ j ∈ J, g j) :
            (I.card : ENNReal) <= (2 * H) * (J.card : ENNReal) := by
          classical
          obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image I f (hne.mono hJI)
          apply (ENNReal.mul_le_mul_iff_left (hpos i0 hi0).ne' (hfinite i0 hi0).ne).mp
          calc
            (I.card : ENNReal) * f i0 = ∑ i ∈ I, f i0 := by simp
            _ <= ∑ i ∈ I, f i := Finset.sum_le_sum hmin
            _ <= H * ∑ j ∈ J, g j := hpaid
            _ <= H * ∑ j ∈ J, 2 * f i0 := mul_le_mul' le_rfl
              (Finset.sum_le_sum (fun j hj => (hg j hj).trans (hunif j (hJI hj) i0 hi0)))
            _ = ((2 * H) * (J.card : ENNReal)) * f i0 := by simp; ring
      
        have hwhole {iota : Type u} {delta : NNReal} {S R : Finset iota}
            {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C m : Nat}
            (Q : SourceThreadedTower S T M C) (Q' : SourceThreadedTower R T M C)
            (hrest : SourceTowerRestriction Q Q') (step : SourceWholeCellStep Q S R m) :
            forall k, m <= k -> k <= M -> forall j, j ∈ Q'.indexSet k ->
              Q'.cell k j = Q.cell k j := by
          classical
          have hancestor (a b : Nat) (hab : a <= b) (hb : b <= M)
              (i : iota) (hi : i ∈ S) (j : iota) (hj : j ∈ S)
              (heq : Q.place b i = Q.place b j) : Q.place a i = Q.place a j := by
            induction b, hab using Nat.le_induction with
            | base => exact heq
            | succ b hab ih =>
              apply ih (Nat.le_of_succ_le hb)
              rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
                Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
          intro k hmk hk j hj
          obtain ⟨x, hx, hxj⟩ := Q'.place_surjective k hk j hj
          rw [hrest.assignment] at hxj
          have hxsel : Q.place m x ∈ step.selected := by
            have hx' := hx
            rw [step.leaves_eq] at hx'
            exact (Finset.mem_filter.mp hx').2
          ext i
          simp only [SourceThreadedTower.cell, hrest.assignment, Finset.mem_filter]
          constructor
          · rintro ⟨hi, heq⟩
            exact ⟨hrest.subset hi, heq⟩
          · rintro ⟨hi, heq⟩
            refine ⟨?_, heq⟩
            rw [step.leaves_eq]
            exact Finset.mem_filter.mpr ⟨hi,
              (hancestor m k hmk hk i hi x (hrest.subset hx) (heq.trans hxj.symm)) ▸ hxsel⟩
        have htrans {U V W : Finset iota}
            (QU : SourceThreadedTower U T M C) (QV : SourceThreadedTower V T M C)
            (QW : SourceThreadedTower W T M C)
            (huv : SourceTowerRestriction QU QV) (hvw : SourceTowerRestriction QV QW) :
            SourceTowerRestriction QU QW := {
          subset := hvw.subset.trans huv.subset
          assignment := hvw.assignment.trans huv.assignment
          parent := hvw.parent.trans huv.parent
          tubes := hvw.tubes.trans huv.tubes
          occupied := by intro k hk; rw [hvw.occupied k hk]; simp only [SourceThreadedTower.assignedFootprint, huv.assignment]
          full_retained_fibres := by intro a b j; rw [hvw.full_retained_fibres]; simp only [SourceThreadedTower.retainedAssignedFibre, huv.assignment] }
        have hindex {U V : Finset iota} (QU : SourceThreadedTower U T M C)
            (QV : SourceThreadedTower V T M C) (hr : SourceTowerRestriction QU QV)
            (k : Nat) (hk : k <= M) : QV.indexSet k <= QU.indexSet k := by
          rw [hr.occupied k hk]
          intro j hj
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          exact QU.place_mem k hk i (hr.subset hi)
        have hcellsub {U V : Finset iota} (QU : SourceThreadedTower U T M C)
            (QV : SourceThreadedTower V T M C) (hr : SourceTowerRestriction QU QV)
            (k : Nat) (j : iota) : QV.cell k j <= QU.cell k j := by
          intro i hi
          have hi' := Finset.mem_filter.mp hi
          rw [hr.assignment] at hi'
          exact Finset.mem_filter.mpr ⟨hr.subset hi'.1, hi'.2⟩
        let w i := volume (Z i).shade
        let f j := ∑ i ∈ Q.cell q j, w i
        obtain ⟨i0, hi0⟩ := hQ.geometry.nonempty
        letI : Nonempty iota := ⟨i0⟩
        obtain ⟨pick, I, hIsub, hpick, htotal⟩ := hheavy (ι := iota) (κ := iota)
          (s := Q.indexSet q) parts parent f L hgroups
        have hIne : I.Nonempty := by
          obtain ⟨U, hU, hiU⟩ := parts.exists_mem (Q.place_mem q hq i0 hi0)
          obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp (hpick U hU).1
          have hjI : j ∈ I ∩ U := by
            rw [(hpick U hU).2.1]
            exact Finset.mem_filter.mpr ⟨hj, hjp⟩
          exact ⟨j, (Finset.mem_inter.mp hjI).1⟩
        let H := S.filter (fun i => Q.place q i ∈ I)
        have hHS : H <= S := Finset.filter_subset _ _
        have hHne : H.Nonempty := by
          obtain ⟨j, hj⟩ := hIne
          obtain ⟨i, hi, hij⟩ := Q.place_surjective q hq j (hIsub hj)
          exact ⟨i, Finset.mem_filter.mpr ⟨hi, hij ▸ hj⟩⟩
        obtain ⟨QH, hQHrest, hQH⟩ := hrestrict Q hQ H hHS hHne
        have hfoot : QH.indexSet q = I := by
          rw [hQHrest.occupied q hq]
          ext j
          constructor
          · intro hj
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
            exact (Finset.mem_filter.mp hi).2
          · intro hj
            obtain ⟨i, hi, hij⟩ := Q.place_surjective q hq j (hIsub hj)
            exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij ▸ hj⟩, hij⟩
        have hstep : SourceWholeCellStep Q S H q := {
          selected := I
          selected_subset := by
            intro j hj
            obtain ⟨i, hi, hij⟩ := Q.place_surjective q hq j (hIsub hj)
            exact Finset.mem_image.mpr ⟨i, hi, hij⟩
          leaves_eq := rfl
          complete := by
            intro j hj
            ext i
            simp only [H, Finset.mem_filter]
            constructor
            · exact fun h => ⟨h.1.1, h.2⟩
            · exact fun h => ⟨⟨h.1, h.2 ▸ hj⟩, h.2⟩ }
        have hcells (j : iota) (hj : j ∈ QH.indexSet q) : QH.cell q j = Q.cell q j :=
          hwhole Q QH hQHrest hstep q le_rfl hq j hj
        have hsumQ : (∑ j ∈ Q.indexSet q, f j) = ∑ i ∈ S, w i :=
          Finset.sum_fiberwise_of_maps_to (Q.place_mem q hq) w
        have hsumH : (∑ j ∈ I, f j) = ∑ i ∈ H, w i := by
          rw [← hfoot]
          calc
            _ = ∑ j ∈ QH.indexSet q, ∑ i ∈ QH.cell q j, w i :=
              Finset.sum_congr rfl (fun j hj => by dsimp [f]; rw [hcells j hj])
            _ = _ := Finset.sum_fiberwise_of_maps_to (QH.place_mem q hq) w
        rw [hsumQ, hsumH] at htotal
        have hparts : ∀ U ∈ parts.parts, pick U ∈ U.image parent ∧ pick U ∈ QH.indexSet p ∧
            QH.indexSet q ∩ U = U.filter (fun j => parent j = pick U) ∧
            (∑ j ∈ U, ∑ i ∈ Q.cell q j, w i) <=
              (L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ U, ∑ i ∈ QH.cell q j, w i ∧
            (∑ j ∈ U, volume (Q.tube q j).carrier) <=
              (2 * L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ U, volume (QH.tube q j).carrier := by
          intro U hU
          have hpay : (∑ j ∈ U, f j) <= (L : ENNReal) * ∑ j ∈ QH.indexSet q ∩ U, f j := by
            rw [hfoot]
            exact (hpick U hU).2.2
          have hne : (QH.indexSet q ∩ U).Nonempty := by
            obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp (hpick U hU).1
            rw [hfoot, (hpick U hU).2.1]
            exact ⟨j, Finset.mem_filter.mpr ⟨hj, hjp⟩⟩
          have hc := hcount U (QH.indexSet q ∩ U) f f L Finset.inter_subset_right hne
            (fun j hj => hpos j (parts.le hU hj))
            (fun j hj => hfinite j (parts.le hU hj))
            (fun j hj k hk => hunif j (parts.le hU hj) k (parts.le hU hk))
            (fun _ _ => le_rfl) hpay
          have hoccupied : pick U ∈ QH.indexSet p := by
            obtain ⟨k, hk⟩ := hne
            obtain ⟨i, hi, hik⟩ := QH.place_surjective q hq k (Finset.mem_inter.mp hk).1
            have hkp : parent k = pick U := by
              rw [hfoot, (hpick U hU).2.1] at hk
              exact (Finset.mem_filter.mp hk).2
            have hip : QH.place p i = pick U := by
              rw [hQHrest.assignment] at hik ⊢
              exact (hancestor i (hHS hi)).symm.trans ((congrArg parent hik).trans hkp)
            rw [← hip]
            exact QH.place_mem p (hpq.trans hq) i hi
          refine ⟨(hpick U hU).1, hoccupied, by rw [hfoot]; exact (hpick U hU).2.1, ?_, ?_⟩
          · convert hpay using 1
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [f]
            rw [hcells j (Finset.mem_inter.mp hj).1]
          · rw [hQHrest.tubes, _root_.Tube.sum_volume_carrier_eq_card_mul (Q.tube q) (Q.tube q i0),
              _root_.Tube.sum_volume_carrier_eq_card_mul (Q.tube q) (Q.tube q i0)]
            simpa only [mul_assoc] using mul_le_mul' hc (le_rfl :
              volume (Q.tube q i0).carrier <= volume (Q.tube q i0).carrier)
        have hHindex : (QH.indexSet q).Nonempty := by rw [hfoot]; exact hIne
        have hHpos (j : iota) (hj : j ∈ QH.indexSet q) :
            0 < ∑ i ∈ QH.cell q j, w i := by
          rw [hcells j hj]; exact hpos j (hindex Q QH hQHrest q hq hj)
        have hHunif (j : iota) (hj : j ∈ QH.indexSet q) (k : iota) (hk : k ∈ QH.indexSet q) :
            (∑ i ∈ QH.cell q j, w i) <= 2 * ∑ i ∈ QH.cell q k, w i := by
          rw [hcells j hj, hcells k hk]
          exact hunif j (hindex Q QH hQHrest q hq hj) k (hindex Q QH hQHrest q hq hk)
        obtain ⟨mu, hmu, hmuBounds⟩ := hinterval (Q.indexSet q) f
          ⟨Q.place q i0, Q.place_mem q hq i0 hi0⟩ hpos hfinite hunif
        have hmassH : 0 < ∑ i ∈ H, w i := by
          rw [← hsumH]
          obtain ⟨j, hj⟩ := hIne
          exact (hpos j (hIsub hj)).trans_le (Finset.single_le_sum (f := f) (fun _ _ => zero_le) hj)
        have hbounds : ∀ j ∈ QH.indexSet p,
            (∑ i ∈ QH.cell p j, w i) ∈ Set.Icc (mu : ENNReal)
              (((2 * (Q.indexSet q).card) * mu : NNReal) : ENNReal) := by
          intro j hj
          rw [hsumCells QH hpq hq w j]
          have hsub : QH.fibre p q j <= Q.indexSet q := by
            intro k hk
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
            rw [hQHrest.assignment]
            exact Q.place_mem q hq i (hHS (Finset.mem_filter.mp hi).1)
          have hne : (QH.fibre p q j).Nonempty := by
            obtain ⟨i, hi, hij⟩ := QH.place_surjective p (hpq.trans hq) j hj
            exact ⟨QH.place q i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩, rfl⟩⟩
          have heq : (∑ k ∈ QH.fibre p q j, ∑ i ∈ QH.cell q k, w i) =
              ∑ k ∈ QH.fibre p q j, f k := by
            apply Finset.sum_congr rfl
            intro k hk
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
            dsimp [f]
            rw [hcells _ (QH.place_mem q hq i (Finset.mem_filter.mp hi).1)]
          rw [heq]
          exact hmuBounds (QH.fibre p q j) hsub hne
        obtain ⟨P, hPne, hPH, ⟨hPstep⟩, hPmass, hPcomp⟩ :=
          hband QH (hpq.trans hq) w mu (2 * (Q.indexSet q).card) hmu hmassH hbounds
        obtain ⟨QP, hPcrest, hQP⟩ := hrestrict QH hQH P hPH hPne
        obtain ⟨R, QR, hRP, hRne, hRrest, hQR, hstats, hRmass⟩ :=
          hregular hd QP hQP P le_rfl hPne Z hZT v m hv0 hvt hm0 hm1
            (fun i hi => hvol i (hHS (hPH hi)))
            (fun i hi => hfloor i (hHS (hPH hi))) J
            ((show (P.card : ENNReal) <= S.card by exact_mod_cast Finset.card_le_card (hPH.trans hHS)).trans hJ)
        have hHRrest := htrans QH QP QR hPcrest hRrest
        let reg : ENNReal := (((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1)
        have hparent : ∀ j ∈ QR.indexSet p,
            (∑ i ∈ QH.cell p j, w i) <= 4 * reg * ∑ i ∈ QR.cell p j, w i := by
          intro j hj
          have hcomp : ∀ k ∈ QP.indexSet p, ∀ l ∈ QP.indexSet p,
              (∑ i ∈ QP.cell p k, w i) <= 2 * ∑ i ∈ QP.cell p l, w i := by
            intro k hk l hl
            rw [hPcrest.occupied p (hpq.trans hq)] at hk hl
            simpa only [SourceThreadedTower.cell, hPcrest.assignment] using hPcomp k hk l hl
          have hh := hretention QP QR Z Z reg (hpq.trans hq) hRrest hcomp hstats hRmass j hj
          rw [hwhole QH QP hPcrest hPstep p le_rfl (hpq.trans hq) j
            (hindex QP QR hRrest p (hpq.trans hq) hj)] at hh
          exact hh
        refine ⟨H, R, QH, QR, pick, hHne, hRne, hQHrest, hHRrest, hQH, hQR,
          hstats, ⟨hstep⟩, hparts, htotal, ?_, hparent, ?_⟩
        · calc
            _ <= (L : ENNReal) * ∑ i ∈ H, w i := htotal
            _ <= (L : ENNReal) * (ENNReal.ofReal (1 + Real.logb 2 (2 * (Q.indexSet q).card : Real)) *
                (reg * ∑ i ∈ R, w i)) :=
              mul_le_mul' le_rfl (hPmass.trans (mul_le_mul' le_rfl hRmass))
            _ = _ := by ring
        · intro j hj
          let U := QH.fibre p q j
          let V := QR.fibre p q j
          let fH k := ∑ i ∈ QH.cell q k, w i
          let fR k := ∑ i ∈ QR.cell q k, w i
          have hVU : V <= U := by
            dsimp [V, U, SourceThreadedTower.fibre]
            rw [hHRrest.assignment]
            exact Finset.image_mono _ (hcellsub QH QR hHRrest p j)
          have hVne : V.Nonempty := by
            obtain ⟨i, hi, hij⟩ := QR.place_surjective p (hpq.trans hq) j hj
            exact ⟨QR.place q i, Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩, rfl⟩⟩
          have hUindex (k : iota) (hk : k ∈ U) : k ∈ QH.indexSet q := by
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
            exact QH.place_mem q hq i (Finset.mem_filter.mp hi).1
          have hpaid : (∑ k ∈ U, fH k) <= (4 * reg) * ∑ k ∈ V, fR k := by
            dsimp [U, V, fH, fR]
            rw [← hsumCells QH hpq hq w j, ← hsumCells QR hpq hq w j]
            exact hparent j hj
          have hc := hcount U V fH fR (4 * reg) hVU hVne
            (fun k hk => hHpos k (hUindex k hk))
            (fun k hk => by
              dsimp [fH]; rw [hcells k (hUindex k hk)]
              exact hfinite k (hindex Q QH hQHrest q hq (hUindex k hk)))
            (fun k hk l hl => hHunif k (hUindex k hk) l (hUindex l hl))
            (fun k _ => Finset.sum_le_sum_of_subset (hcellsub QH QR hHRrest q k)) hpaid
          rw [hHRrest.tubes, _root_.Tube.sum_volume_carrier_eq_card_mul (QH.tube q) (QH.tube q i0),
            _root_.Tube.sum_volume_carrier_eq_card_mul (QH.tube q) (QH.tube q i0)]
          calc
            _ <= ((2 * (4 * reg)) * V.card) * volume (QH.tube q i0).carrier := mul_le_mul' hc le_rfl
            _ = _ := by ring
      have hScalar (M L Kprefix : Nat) (H : Real) (hH : 1 <= H) :
          ∃ (K : Nat) (delta0 : NNReal), 1 <= K ∧ 0 < delta0 ∧ delta0 <= 1 ∧
          ∀ delta : NNReal, 0 < delta -> delta < delta0 ->
          ∀ n : Nat, (n : Real) <= H * (1 / (delta : Real)) ^ 6 ->
          ∃ J : Nat,
            (n : ENNReal) <= 2 ^ J * (delta : ENNReal) ^ (10 : Real) ∧
            sourceFixedPreparationLoss Kprefix delta *
              ((L : ENNReal) * ENNReal.ofReal (1 + Real.logb 2 (2 * n : Real)) *
                ((((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1))) <=
              sourceFixedPreparationLoss K delta ∧
            8 * ((((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1)) <=
              sourceFixedPreparationLoss K delta := by
        clear hChain
        let e := (2 * M + 4) * (M + 1)
        let A : Real := ((L : Real) + 1) * 8 * 18 ^ e
        obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt A (by norm_num : (1 : Real) < 2)
        let delta0 : NNReal := Real.toNNReal (1 / (2 * H))
        have hH0 : 0 < H := zero_lt_one.trans_le hH
        have hd00 : 0 < delta0 := Real.toNNReal_pos.mpr (by positivity)
        have hd0real : (delta0 : Real) = 1 / (2 * H) := Real.coe_toNNReal _ (by positivity)
        have hd01 : delta0 <= 1 := by
          apply NNReal.coe_le_coe.mp
          rw [hd0real, NNReal.coe_one]
          exact (div_le_one (by positivity)).mpr (by linarith)
        refine ⟨Kprefix + e + 1 + N, delta0, by omega, hd00, hd01, ?_⟩
        intro delta hd hdsmall n hn
        have hdr : (0 : Real) < delta := by exact_mod_cast hd
        have hd1 : delta <= 1 := hdsmall.le.trans hd01
        have hd1r : (delta : Real) <= 1 := by exact_mod_cast hd1
        have hdsm : (delta : Real) < 1 / (2 * H) := by
          rw [← hd0real]; exact_mod_cast hdsmall
        let y : Real := 1 / (delta : Real)
        let x : Real := 2 + Real.logb 2 y
        have hy : 1 <= y := (le_div_iff₀ hdr).mpr (by simpa using hd1r)
        have hy0 : 0 < y := zero_lt_one.trans_le hy
        have hyH : 2 * H <= y := by
          apply (le_div_iff₀ hdr).mpr
          have hh := (lt_div_iff₀ (by positivity : 0 < 2 * H)).mp hdsm
          nlinarith
        have hy2 : 2 <= y := by linarith
        have hlog : 0 <= Real.logb 2 y := Real.logb_nonneg (by norm_num) hy
        have hx : 2 <= x := by dsimp [x]; linarith
        have hn7 : (n : Real) <= y ^ 7 := by
          calc
            _ <= H * y ^ 6 := hn
            _ <= y * y ^ 6 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
            _ = _ := by ring
        have hn8 : (2 * n : Real) <= y ^ 8 := by
          calc
            _ <= y * y ^ 7 := mul_le_mul hy2 hn7 (Nat.cast_nonneg n) (by positivity)
            _ = _ := by ring
        let t : Real := Real.logb 2 (y ^ 18)
        let J := Nat.ceil t
        have ht : t = 18 * Real.logb 2 y := by simp only [t, Real.logb_pow]; norm_num
        have ht0 : 0 <= t := by rw [ht]; positivity
        have hJreal : y ^ 18 <= (2 : Real) ^ J := by
          calc
            _ = (2 : Real) ^ t := (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
            _ <= (2 : Real) ^ (J : Real) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil t)
            _ = _ := Real.rpow_natCast _ _
        have hJrangeReal : (n : Real) <= (2 : Real) ^ J * (delta : Real) ^ 10 := by
          have hn8' : (n : Real) <= y ^ 8 := by nlinarith [show (0 : Real) <= n by positivity]
          calc
            _ <= y ^ 8 := hn8'
            _ = y ^ 18 * (delta : Real) ^ 10 := by dsimp [y]; field_simp
            _ <= _ := mul_le_mul_of_nonneg_right hJreal (by positivity)
        have hJrange : (n : ENNReal) <= 2 ^ J * (delta : ENNReal) ^ (10 : Real) := by
          rw [show (10 : Real) = ((10 : Nat) : Real) by norm_num, ENNReal.rpow_natCast]
          have hh := ENNReal.ofReal_le_ofReal hJrangeReal
          simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity : (0 : Real) <= 2 ^ J),
            ENNReal.ofReal_pow (by norm_num : (0 : Real) <= 2), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_pow hdr.le, ENNReal.ofReal_coe_nnreal, ENNReal.rpow_natCast] using hh
        have hJle : ((J + 1 : Nat) : Real) <= 18 * x := by
          have hh := Nat.ceil_lt_add_one ht0
          simp only [Nat.cast_add, Nat.cast_one]
          dsimp [J, x]
          rw [ht] at hh ⊢
          linarith
        have hreg : ((((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1)) <=
            ENNReal.ofReal ((18 * x) ^ e) := by
          have hh := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hJle e)
          rw [ENNReal.ofReal_pow (by positivity : (0 : Real) <= ((J + 1 : Nat) : Real)),
            ENNReal.ofReal_natCast] at hh
          simpa only [e, pow_mul] using hh
        have hband : ENNReal.ofReal (1 + Real.logb 2 (2 * n : Real)) <= ENNReal.ofReal (8 * x) := by
          apply ENNReal.ofReal_le_ofReal
          by_cases hn0 : n = 0
          · simp only [hn0, Nat.cast_zero, mul_zero, Real.logb_zero, add_zero]
            linarith
          · have hnpos : (0 : Real) < 2 * n := by positivity
            have hh := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2) hnpos hn8
            rw [Real.logb_pow] at hh
            norm_num at hh
            dsimp [x]
            linarith
        have hA : A <= x ^ N := hN.le.trans (pow_le_pow_left₀ (by norm_num) hx N)
        have hx1 : 1 <= x := by linarith
        have hmainReal : x ^ Kprefix * ((L : Real) * (8 * x) * (18 * x) ^ e) <=
            x ^ (Kprefix + e + 1 + N) := by
          calc
            _ <= A * x ^ (Kprefix + e + 1) := by
              calc
                _ <= x ^ Kprefix * (((L : Real) + 1) * (8 * x) * (18 * x) ^ e) := by gcongr; linarith
                _ = _ := by dsimp [A]; simp only [mul_pow, pow_add, pow_one]; ring
            _ <= x ^ N * x ^ (Kprefix + e + 1) := mul_le_mul_of_nonneg_right hA (by positivity)
            _ = _ := by rw [pow_add]; ring
        have hparentReal : 8 * (18 * x) ^ e <= x ^ (Kprefix + e + 1 + N) := by
          calc
            _ <= A * x ^ (Kprefix + e + 1) := by
              have hp : 1 <= x ^ Kprefix * x := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hx1) hx1
              have hL : (1 : Real) <= L + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg L)
              calc
                _ = (8 * 18 ^ e) * x ^ e := by rw [mul_pow]; ring
                _ <= ((L : Real) + 1) * (x ^ Kprefix * x) * ((8 * 18 ^ e) * x ^ e) :=
                  le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le hL hp)
                _ = _ := by dsimp [A]; simp only [pow_add, pow_one]; ring
            _ <= x ^ N * x ^ (Kprefix + e + 1) := mul_le_mul_of_nonneg_right hA (by positivity)
            _ = _ := by rw [pow_add]; ring
        refine ⟨J, hJrange, ?_, ?_⟩
        · calc
            _ <= sourceFixedPreparationLoss Kprefix delta *
                ((L : ENNReal) * ENNReal.ofReal (8 * x) * ENNReal.ofReal ((18 * x) ^ e)) := by gcongr
            _ = ENNReal.ofReal (x ^ Kprefix * ((L : Real) * (8 * x) * (18 * x) ^ e)) := by
              change ENNReal.ofReal (x ^ Kprefix) * _ = _
              rw [ENNReal.ofReal_mul (by positivity : 0 <= x ^ Kprefix),
                ENNReal.ofReal_mul (by positivity : 0 <= (L : Real) * (8 * x)),
                ENNReal.ofReal_mul (Nat.cast_nonneg L), ENNReal.ofReal_natCast]
            _ <= _ := ENNReal.ofReal_le_ofReal hmainReal
        · calc
            _ <= 8 * ENNReal.ofReal ((18 * x) ^ e) := mul_le_mul' le_rfl hreg
            _ = ENNReal.ofReal (8 * (18 * x) ^ e) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
            _ <= _ := ENNReal.ofReal_le_ofReal hparentReal
      have hCard {iota : Type u} {delta : NNReal} {S : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C A0 A1 : Nat}
          (Q : SourceThreadedTower S T M C) (hgeom : SourceTowerGeometry Q A0 A1)
          (hd : 0 < delta) (hd1 : delta <= 1) :
          (S.card : Real) <= (4 * 2000 ^ 6 * (A0 + 1) : Real) * (1 / (delta : Real)) ^ 6 := by
        clear hChain hScalar
        classical
        have hdr : (0 : Real) < delta := by exact_mod_cast hd
        have hd1r : (delta : Real) <= 1 := by exact_mod_cast hd1
        let y : Real := 1 / (delta : Real)
        have hy : 1 <= y := (le_div_iff₀ hdr).mpr (by simpa using hd1r)
        have hmid : forall i, i ∈ S -> ‖(T i).midpoint‖ <= (1 : Real) := by
          intro i hi
          have hh := hgeom.original_ball i hi ((T i).midpoint_mem_carrier hd)
          rw [Metric.mem_closedBall, dist_zero_right] at hh
          exact hh.trans (by norm_num)
        obtain ⟨i0, hi0⟩ := hgeom.nonempty
        have hinside : forall i, i ∈ S -> (T i).carrier ⊆
            Metric.cthickening (y * (delta : Real))
              (Set.range fun t : Real => (0 : EuclideanSpace Real (Fin 3)) + t • (T i0).direction) := by
          intro i hi x hx
          have hxball := hgeom.original_ball i hi hx
          rw [Metric.mem_closedBall, dist_zero_right] at hxball
          apply Metric.mem_cthickening_of_dist_le x 0 _ _
            (show (0 : EuclideanSpace Real (Fin 3)) ∈ Set.range
              (fun t : Real => (0 : EuclideanSpace Real (Fin 3)) + t • (T i0).direction) from
              ⟨0, by simp⟩)
          rw [dist_zero_right, show y * (delta : Real) = 1 by dsimp [y]; field_simp]
          exact hxball.trans (by norm_num)
        have hc := lineED_push_radius hd (R₀ := 1) (by norm_num)
          hgeom.original_centred hmid hgeom.original_ed hy
          (0 : EuclideanSpace Real (Fin 3)) (T i0).direction (T i0).norm_direction
        rw [Finset.filter_eq_self.mpr hinside] at hc
        simp only [Tube.linePackingConstant, finrank_euclideanSpace_fin] at hc
        have h1 : 0 <= (3 / 2 + (y - 1) * (5 + 4 * (1 : Real)) - 1) *
            (1 + 4 * 1) * (4 * 8) + 1 := by nlinarith
        have h2 : 0 <= 4 * (3 / 2 + (y - 1) * (5 + 4 * (1 : Real)) - 1) *
            (4 * 8) + 1 := by nlinarith
        have h1le : (3 / 2 + (y - 1) * (5 + 4 * (1 : Real)) - 1) *
            (1 + 4 * 1) * (4 * 8) + 1 <= 2000 * y := by nlinarith
        have h2le : 4 * (3 / 2 + (y - 1) * (5 + 4 * (1 : Real)) - 1) *
            (4 * 8) + 1 <= 2000 * y := by nlinarith
        calc
          (S.card : Real) <= 2 * (2 *
            ((3 / 2 + (y - 1) * (5 + 4 * (1 : Real)) - 1) * (1 + 4 * 1) * (4 * 8) + 1) ^ 3 *
            (4 * (3 / 2 + (y - 1) * (5 + 4 * (1 : Real)) - 1) * (4 * 8) + 1) ^ 3) * A0 := hc
          _ <= 2 * (2 * (2000 * y) ^ 3 * (2000 * y) ^ 3) * (A0 + 1) := by gcongr <;> linarith
          _ = _ := by dsimp [y]; ring
      let c : Real := 4 * 2000 ^ 6 * (A0 + 1)
      have hc : 1 <= c := by
        dsimp [c]
        have hh : (0 : Real) <= A0 := Nat.cast_nonneg A0
        nlinarith
      obtain ⟨K, delta0, hK, hd0, hd01, hbudget⟩ := hScalar M L Kprefix c hc
      refine ⟨K, delta0, hK, hd0, hd01, ?_⟩
      intro delta hd hsmall iota S T Q hQ Z hZT hfloor p q hpq hq parts parent hgroups hancestor hpos hfinite hunif
      have hd1 : delta <= 1 := hsmall.le.trans hd01
      have hcard := hCard Q hQ.geometry hd hd1
      obtain ⟨J, hJ, hmassBudget, hparentBudget⟩ := hbudget delta hd hsmall S.card hcard
      obtain ⟨i0, hi0⟩ := hQ.geometry.nonempty
      let v := volume (T i0).carrier
      let m : ENNReal := (delta : ENNReal) ^ (10 : Real)
      have hv0 : v ≠ 0 := ML2Shaded.volume_carrier_ne_zero hd (T i0)
      have hvt : v ≠ ⊤ := ML2Shaded.volume_carrier_ne_top (T i0)
      have hm0 : m ≠ 0 := (ENNReal.rpow_pos (by exact_mod_cast hd) ENNReal.coe_ne_top).ne'
      have hm1 : m <= 1 := ENNReal.rpow_le_one (by exact_mod_cast hd1) (by norm_num)
      have hvol (i : iota) (_hi : i ∈ S) : volume (T i).carrier = v :=
        Tube.volume_carrier_eq_volume_carrier (T i) (T i0)
      obtain ⟨H, R, QH, QR, pick, hHne, hRne, hQHrest, hHRrest, hQH, hQR,
        hstats, hstep, hparts, hheavyMass, hmass, hparent, hvolume⟩ :=
        hChain M C A0 A1 L eta0 Q hQ hd Z hZT v m hv0 hvt hm0 hm1 hvol
          (fun i hi => by rw [← hvol i hi]; exact hfloor i hi)
          J hJ p q hpq hq parts parent hgroups hancestor hpos hfinite hunif
      have hnodecard : (Q.indexSet q).card <= S.card := by
        have heq : Q.indexSet q = S.image (Q.place q) := by
          ext j
          constructor
          · intro hj
            obtain ⟨i, hi, hij⟩ := Q.place_surjective q hq j hj
            exact Finset.mem_image.mpr ⟨i, hi, hij⟩
          · intro hj
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
            exact Q.place_mem q hq i hi
        rw [heq]
        exact Finset.card_image_le
      have hband : ENNReal.ofReal (1 + Real.logb 2 (2 * (Q.indexSet q).card : Real)) <=
          ENNReal.ofReal (1 + Real.logb 2 (2 * S.card : Real)) := by
        apply ENNReal.ofReal_le_ofReal
        apply add_le_add le_rfl
        apply Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2)
        · have hne : 0 < (Q.indexSet q).card := Finset.card_pos.mpr
            ⟨Q.place q i0, Q.place_mem q hq i0 hi0⟩
          positivity
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnodecard) (by norm_num)
      have hmassBudget' : sourceFixedPreparationLoss Kprefix delta *
          ((L : ENNReal) * ENNReal.ofReal (1 + Real.logb 2 (2 * (Q.indexSet q).card : Real)) *
            ((((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1))) <= sourceFixedPreparationLoss K delta := by
        exact (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hband) le_rfl)).trans hmassBudget
      refine ⟨H, R, QH, QR, pick, hHne, hRne, hQHrest, hHRrest, hQH, hQR,
        hstats, hstep, hparts, hheavyMass, ?_, ?_, ?_⟩
      · calc
          _ <= sourceFixedPreparationLoss Kprefix delta *
              (((L : ENNReal) * ENNReal.ofReal (1 + Real.logb 2 (2 * (Q.indexSet q).card : Real)) *
                ((((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1))) * ∑ i ∈ R, volume (Z i).shade) :=
            mul_le_mul' le_rfl hmass
          _ <= _ := by rw [← mul_assoc]; exact mul_le_mul' hmassBudget' le_rfl
      · intro j hj
        exact (hparent j hj).trans (mul_le_mul'
          ((mul_le_mul' (by norm_num : (4 : ENNReal) <= 8) le_rfl).trans hparentBudget) le_rfl)
      · intro j hj
        exact (hvolume j hj).trans (mul_le_mul' hparentBudget le_rfl)
    have hparentGeometry {D c : NNReal} {A0 A1 : Nat} {ι : Type u} {δ : NNReal}
        {S : Finset ι} {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))}
        {M C a m1 : Nat} {aw bw cw Cfactor : NNReal} {etaParent : Real}
        (QB : SourceThreadedTower S T M C) (hgeom : SourceTowerGeometry QB A0 A1)
        (hδ : 0 < δ) (hδ1 : δ <= 1) (ham : a < m1) (hm1 : m1 < M)
        (hD : 1 <= D) (hc : 0 < c) (haw : 0 < aw) (hawb : aw <= bw)
        (hlong : c <= cw) (hecc : δ ^ etaParent * bw <= aw)
        (F : ∀ ja, ja ∈ QB.indexSet a -> ConvexSpaceBody.Factorization
          (QB.fibre a m1 ja) (fun i => (QB.tube m1 i).toConvexSpaceBody) Cfactor)
        (hDims : ∀ ja, ∀ hja : ja ∈ QB.indexSet a, ∀ part, part ∈ (F ja hja).parts ->
          SourceZeroFactorDimensions D aw bw cw
            (part.convexHull_biUnion (fun i => (QB.tube m1 i).toConvexSpaceBody))) :
        ∃ p : Nat, ∃ parent : ι -> ι,
          a <= p /\ p < m1 /\
          (∀ i ∈ S, parent (QB.place m1 i) = QB.place p i) /\
          (∀ i ∈ QB.indexSet m1, parent i ∈ QB.indexSet p /\
            (QB.tube m1 i).toConvexSpaceBody <= (QB.tube p (parent i)).toConvexSpaceBody) /\
          (∀ jp, QB.fibre p m1 jp = (QB.indexSet m1).filter (fun i => parent i = jp)) /\
          sourceTowerRadius δ M p < 4 * D * bw * δ ^ (-(1 / (M : Real))) /\
          (a < p -> 4 * D * bw <= sourceTowerRadius δ M p) /\
          (∀ ja, ∀ hja : ja ∈ QB.indexSet a, ∀ part, part ∈ (F ja hja).parts ->
            (part.image parent).card <= max (Nat.ceil (coverFibreConstant 3 3 512 * A1)) 1) /\
          (∀ ja, ∀ hja : ja ∈ QB.indexSet a, ∀ part, part ∈ (F ja hja).parts ->
            ∀ i ∈ part,
            (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)).carrier <=
              (Kakeya.Tube.dilate (QB.tube p (parent i)) 128).carrier) /\
          (∀ ja, ∀ hja : ja ∈ QB.indexSet a, ∀ part, part ∈ (F ja hja).parts ->
            (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)).carrier <=
              Metric.closedBall 0 3) /\
          (∀ jp, ∀ ja, ∀ hja : ja ∈ QB.indexSet a, ∀ part, part ∈ (F ja hja).parts ->
            volume (QB.tube p jp).carrier <=
              (((16 * _root_.Tube.volume_le.C 3 * D ^ 5 /
                (Metric.lt_volume_convexHull.c 3 * c) : NNReal) : ENNReal) *
                ((δ ^ (-etaParent - 2 / (M : Real)) : NNReal) : ENNReal)) *
              volume (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)).carrier) := by
      clear heta hbias hmesh
      clear hchain
      classical
      have hAncestor {δ : NNReal} {S : Finset ι}
          {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C p m : Nat}
          (Q : SourceThreadedTower S T M C) (hpm : p <= m) (hm : m <= M) :
          ∃ parent : ι -> ι,
            (∀ i ∈ S, parent (Q.place m i) = Q.place p i) /\
            (∀ j ∈ Q.indexSet m, parent j ∈ Q.indexSet p /\
              (Q.tube m j).toConvexSpaceBody <= (Q.tube p (parent j)).toConvexSpaceBody) /\
            (∀ jp, Q.fibre p m jp = (Q.indexSet m).filter (fun j => parent j = jp)) := by
        classical
        have hcompatible (a b : Nat) (hab : a <= b) (hb : b <= M)
            (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
            (heq : Q.place b i = Q.place b j) : Q.place a i = Q.place a j := by
          induction b, hab using Nat.le_induction with
          | base => exact heq
          | succ b hab ih =>
            apply ih (Nat.le_of_succ_le hb)
            rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
              Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
        have hcontained (a b : Nat) (hab : a <= b) (hb : b <= M)
            (i : ι) (hi : i ∈ S) :
            (Q.tube b (Q.place b i)).toConvexSpaceBody <= (Q.tube a (Q.place a i)).toConvexSpaceBody := by
          induction b, hab using Nat.le_induction with
          | base => exact le_rfl
          | succ b hab ih =>
            have hsub := Q.parent_containment b (Nat.lt_of_succ_le hb)
              (Q.place (b + 1) i) (Q.place_mem (b + 1) hb i hi)
            rw [← Q.parent_composition b (Nat.lt_of_succ_le hb) i hi] at hsub
            exact hsub.trans (ih (Nat.le_of_succ_le hb))
        let leaf (j : ι) := if hj : j ∈ Q.indexSet m then
          Classical.choose (Q.place_surjective m hm j hj) else j
        have hleaf (j : ι) (hj : j ∈ Q.indexSet m) :
            leaf j ∈ S /\ Q.place m (leaf j) = j := by
          simpa only [leaf, dif_pos hj] using Classical.choose_spec (Q.place_surjective m hm j hj)
        let parent j := Q.place p (leaf j)
        have hplace (i : ι) (hi : i ∈ S) : parent (Q.place m i) = Q.place p i := by
          have hl := hleaf (Q.place m i) (Q.place_mem m hm i hi)
          exact hcompatible p m hpm hm _ hl.1 i hi hl.2
        refine ⟨parent, hplace, ?_, ?_⟩
        · intro j hj
          have hl := hleaf j hj
          refine ⟨Q.place_mem p (hpm.trans hm) _ hl.1, ?_⟩
          have hsub := hcontained p m hpm hm _ hl.1
          simpa only [hl.2] using hsub
        · intro jp
          ext j
          simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell, Finset.mem_image,
            Finset.mem_filter]
          constructor
          · rintro ⟨i, ⟨hi, hip⟩, rfl⟩
            exact ⟨Q.place_mem m hm i hi, (hplace i hi).trans hip⟩
          · rintro ⟨hj, hjp⟩
            have hl := hleaf j hj
            exact ⟨leaf j, ⟨hl.1, hjp⟩, hl.2⟩
      have hGrid {δ w : NNReal} {M a m1 : Nat} (hδ : 0 < δ) (hδ1 : δ <= 1) (hw : 0 < w)
          (ham : a < m1) (hm1 : m1 < M) (hfine : sourceTowerRadius δ M m1 <= w) :
          ∃ p : Nat, a <= p /\ p < m1 /\
            (p = a \/ 4 * w <= sourceTowerRadius δ M p) /\
            (p = a -> sourceTowerRadius δ M a < 4 * w \/
              4 * w <= sourceTowerRadius δ M p) /\
            (sourceTowerRadius δ M p <
              4 * w * δ ^ (-(1 / (M : Real)))) := by
        clear hAncestor
        classical
        let J := (Finset.Icc a m1).filter (fun k => 4 * w <= sourceTowerRadius δ M k)
        have hfine' : sourceTowerRadius δ M m1 < 4 * w :=
          hfine.trans_lt (by nlinarith)
        by_cases ha : sourceTowerRadius δ M a < 4 * w
        · refine ⟨a, le_rfl, ham, Or.inl rfl, fun _ => Or.inl ha, ?_⟩
          have hpow : 1 <= δ ^ (-(1 / (M : Real))) :=
            NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr (by positivity))
          exact ha.trans_le (le_mul_of_one_le_right (by positivity) hpow)
        have haJ : a ∈ J := Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨le_rfl, ham.le⟩, le_of_not_gt ha⟩
        have hJ : J.Nonempty := ⟨a, haJ⟩
        let p := J.max' hJ
        have hpJ : p ∈ J := Finset.max'_mem J hJ
        have hap : a <= p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpJ).1).1
        have hpm : p <= m1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpJ).1).2
        have hwp : 4 * w <= sourceTowerRadius δ M p := (Finset.mem_filter.mp hpJ).2
        have hplt : p < m1 := by
          by_contra h
          have heq : p = m1 := by omega
          rw [heq] at hwp
          exact (not_le_of_gt hfine') hwp
        have hnext : sourceTowerRadius δ M (p + 1) < 4 * w := by
          by_contra h
          have hmem : p + 1 ∈ J := Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, le_of_not_gt h⟩
          have hmax := Finset.le_max' J (p + 1) hmem
          change p + 1 <= p at hmax
          omega
        have hstep : sourceTowerRadius δ M (p + 1) =
            sourceTowerRadius δ M p * δ ^ (1 / (M : Real)) := by
          simp only [sourceTowerRadius, if_pos (show p + 1 < M by omega),
            if_pos (show p < M by omega), Nat.cast_add, Nat.cast_one]
          rw [show ((p : Real) + 1) / M = (p : Real) / M + 1 / M by ring,
            NNReal.rpow_add hδ.ne']
          ring
        have hpow : 0 < δ ^ (1 / (M : Real)) := NNReal.rpow_pos hδ
        refine ⟨p, hap, hplt, Or.inr hwp, fun _ => Or.inr hwp, ?_⟩
        rw [NNReal.rpow_neg]
        have hmul := mul_lt_mul_of_pos_right hnext (inv_pos.mpr hpow)
        rw [hstep, mul_assoc, mul_inv_cancel₀ hpow.ne', mul_one] at hmul
        exact hmul
      have hChord {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
          [FiniteDimensional Real E] {δ b : NNReal} (T : Tube δ E)
          (W : ConvexSpaceBody E) (hb0 : 0 < b) (hb1 : b <= 1 / 8)
          (hTW : T.toConvexSpaceBody <= W)
          (hball : W.carrier <= Metric.closedBall 0 3)
          (hthin : Metric.ethickness Real W.carrier 1 <= (b : ENNReal)) :
          W.carrier <= Metric.cthickening (64 * (b : Real))
            (affineSpan Real ({T.x, T.y} : Set E)) := by
        clear hAncestor hGrid
        classical
        have hlt : Metric.ethickness Real W.carrier 1 < ((2 * b : NNReal) : ENNReal) := by
          apply hthin.trans_lt
          exact_mod_cast (show b < 2 * b by nlinarith)
        obtain ⟨A', hdim, hWA⟩ := Metric.exists_cthickening_of_ethickness_lt hlt
        let A : Set E := A'
        let S := W.carrier
        let p := T.x
        let q := T.y
        let r : Real := 2 * b
        have hr0 : 0 <= r := by positivity
        have hr1 : r <= 1 / 4 := by
          have hb : (b : Real) <= 1 / 8 := by exact_mod_cast hb1
          dsimp [r]
          linarith
        have hA : IsClosed A := A'.closed_of_finiteDimensional
        have hcol : Collinear Real A := by
          rw [collinear_iff_rank_le_one, ← A'.direction_eq_vectorSpan]
          simpa using hdim
        have hS : S <= Metric.cthickening r A := by simpa [S, r, A] using hWA
        have hseg (x : E) (hx : x ∈ segment Real T.x T.y) : x ∈ S := by
          apply hTW
          change x ∈ T.carrier
          rw [T.carrier_eq]
          exact Set.mem_iUnion₂.mpr ⟨x, hx, Metric.mem_closedBall_self δ.coe_nonneg⟩
        have hp : p ∈ S := hseg _ (left_mem_segment Real T.x T.y)
        have hq : q ∈ S := hseg _ (right_mem_segment Real T.x T.y)
        have hpq : dist p q = 1 := T.dist_eq_one
        have hdiam (x : E) (hx : x ∈ S) : dist x p <= 6 := by
          have hx0 := hball hx
          have hp0 := hball hp
          have ht := dist_triangle x 0 p
          rw [dist_comm 0 p] at ht
          exact ht.trans (by linarith [Metric.mem_closedBall.mp hx0, Metric.mem_closedBall.mp hp0])
        rw [show 64 * (b : Real) = 32 * r by dsimp [r]; ring]
        change S <= Metric.cthickening (32 * r) (affineSpan Real ({p, q} : Set E))
        have happrox (x : E) (hx : x ∈ S) : exists y, y ∈ A /\ dist x y <= r := by
          have hxA := hS hx
          rw [hA.cthickening_eq_biUnion_closedBall hr0] at hxA
          obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hxA
          exact ⟨y, hy, hxy⟩
        obtain ⟨p', hp', hpp'⟩ := happrox p hp
        obtain ⟨q', hq', hqq'⟩ := happrox q hq
        have hgap : 1 / 2 <= dist p' q' := by
          have h := dist_triangle4 p p' q' q
          rw [hpq, dist_comm q' q] at h
          linarith
        have hne : p' ≠ q' := by
          intro heq
          simp only [heq, dist_self] at hgap
          norm_num at hgap
        intro x hx
        obtain ⟨x', hx', hxx'⟩ := happrox x hx
        obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
          (hcol.mem_affineSpan_of_mem_of_ne hp' hq' hx' hne)
        have hdist : dist x' p' <= 13 / 2 := by
          have h := dist_triangle4 x' x p p'
          rw [dist_comm x' x] at h
          linarith [hdiam x hx]
        have htBound : |t| <= 13 := by
          have htDist : |t| * dist p' q' <= 13 / 2 := by
            simpa only [← ht, dist_lineMap_left, Real.norm_eq_abs] using hdist
          nlinarith [abs_nonneg t]
        have hOne : |1 - t| <= 14 := by
          calc
            |1 - t| <= |(1 : Real)| + |t| := abs_sub _ _
            _ <= 14 := by norm_num; linarith
        let y := AffineMap.lineMap p q t
        have hy : y ∈ affineSpan Real ({p, q} : Set E) :=
          AffineMap.lineMap_mem_affineSpan_pair t p q
        have hline : dist x' y <= 27 * r := by
          rw [← ht]
          have heq : AffineMap.lineMap p' q' t - y =
              (1 - t) • (p' - p) + t • (q' - q) := by
            simp only [y, AffineMap.lineMap_apply_module]
            module
          rw [dist_eq_norm, heq]
          calc
            _ <= ‖(1 - t) • (p' - p)‖ + ‖t • (q' - q)‖ := norm_add_le _ _
            _ = |1 - t| * dist p' p + |t| * dist q' q := by
              simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
            _ <= 14 * r + 13 * r := by
              gcongr
              · simpa only [dist_comm] using hpp'
              · simpa only [dist_comm] using hqq'
            _ = 27 * r := by ring
        apply Metric.closedBall_subset_cthickening hy (32 * r)
        change dist x y <= 32 * r
        have h := dist_triangle x x' y
        linarith
      have hDilation {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
          [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
          {b ρ : NNReal} {S : Set E} {p q : E} (P : _root_.Tube ρ E)
          (hb1 : b <= 1 / 8) (hbρ : b <= ρ)
          (hp : p ∈ P.carrier) (hq : q ∈ P.carrier) (hpq : dist p q = 1)
          (hdiam : forall x, x ∈ S -> dist x p <= 6)
          (hline : S <= Metric.cthickening (64 * (b : Real))
            (affineSpan Real ({p, q} : Set E))) :
          S <= (Kakeya.Tube.dilate P 128).carrier := by
        clear hAncestor hGrid hChord
        classical
        have hb8 : (b : Real) <= 1 / 8 := by exact_mod_cast hb1
        have hbρ' : (b : Real) <= ρ := by exact_mod_cast hbρ
        have hnear (z : E) (hz : z ∈ P.carrier) : exists s : Real,
            |s| <= 1 / 2 /\ ‖z - (P.center + s • P.direction)‖ <= (ρ : Real) := by
          have hz' := _root_.Tube.subset_dilate P (c := 1) (by norm_num) hz
          simpa only [one_div, one_mul] using
            Kakeya.Tube.exists_axis_repr_of_mem_dilate P (c := 1) (by norm_num) hz'
        obtain ⟨u, hu, hpu⟩ := hnear p hp
        obtain ⟨v, hv, hqv⟩ := hnear q hq
        intro x hx
        have hxline := hline hx
        have hclosed := (affineSpan Real ({p, q} : Set E)).closed_of_finiteDimensional
        rw [hclosed.cthickening_eq_biUnion_closedBall (by positivity)] at hxline
        obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hxline
        obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
        have htBound : |t| <= 14 := by
          have hd := dist_triangle y x p
          rw [dist_comm y x] at hd
          have hyp : dist y p <= 14 := by
            linarith [hdiam x hx, Metric.mem_closedBall.mp hxy]
          simpa only [← ht, dist_lineMap_left, Real.norm_eq_abs, hpq, mul_one] using hyp
        have hOne : |1 - t| <= 15 := by
          have := abs_sub (1 : Real) t
          norm_num at this
          linarith
        let s := (1 - t) * u + t * v
        have hs : |s| <= 128 / 2 := by
          calc
            |s| <= |(1 - t) * u| + |t * v| := abs_add_le _ _
            _ = |1 - t| * |u| + |t| * |v| := by rw [abs_mul, abs_mul]
            _ <= 15 * (1 / 2) + 14 * (1 / 2) := by gcongr
            _ <= 128 / 2 := by norm_num
        have hyAxis : dist y (P.center + s • P.direction) <= 29 * (ρ : Real) := by
          have heq : y - (P.center + s • P.direction) =
              (1 - t) • (p - (P.center + u • P.direction)) +
              t • (q - (P.center + v • P.direction)) := by
            rw [← ht]
            simp only [AffineMap.lineMap_apply_module, s]
            module
          rw [dist_eq_norm, heq]
          calc
            _ <= ‖(1 - t) • (p - (P.center + u • P.direction))‖ +
              ‖t • (q - (P.center + v • P.direction))‖ := norm_add_le _ _
            _ = |1 - t| * ‖p - (P.center + u • P.direction)‖ +
              |t| * ‖q - (P.center + v • P.direction)‖ := by
                simp only [norm_smul, Real.norm_eq_abs]
            _ <= 15 * (ρ : Real) + 14 * (ρ : Real) := by gcongr
            _ = 29 * (ρ : Real) := by ring
        apply Kakeya.Tube.mem_dilate_of_dist_axis_le P (by norm_num) hs
        have hd := dist_triangle x y (P.center + s • P.direction)
        linarith [Metric.mem_closedBall.mp hxy, ρ.coe_nonneg]
      have hCount {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
          [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
          {δ b ρ : NNReal} {A : Nat} (s : Finset ι)
          (P : ι -> _root_.Tube ρ E) (T0 : _root_.Tube δ E) (W : Set E)
          (hρ : 0 < ρ) (hbρ : b <= ρ)
          (hcen : ∀ j ∈ s, (P j).IsCentred)
          (hmid : ∀ j ∈ s, ‖(P j).midpoint‖ <= 3)
          (hED : Kakeya.VeryNotSticky.IsLineEssDistinct A s P)
          (hthin : W <= Metric.cthickening (64 * (b : Real))
            (affineSpan Real ({T0.x, T0.y} : Set E)))
          (hfine : ∀ j ∈ s, ∃ U : _root_.Tube δ E,
            U.carrier <= W /\ U.toConvexSpaceBody <= (P j).toConvexSpaceBody) :
          s.card <= Nat.ceil (coverFibreConstant (Module.finrank Real E) 3 512 * A) := by
        clear hAncestor hGrid hChord hDilation
        classical
        let L := affineSpan Real ({T0.x, T0.y} : Set E)
        have hbρ' : (b : Real) <= ρ := by exact_mod_cast hbρ
        have happrox (x : E) (hx : x ∈ W) : ∃ y, y ∈ L /\ dist x y <= 64 * (b : Real) := by
          have hxL := hthin hx
          rw [L.closed_of_finiteDimensional.cthickening_eq_biUnion_closedBall (by positivity)] at hxL
          obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hxL
          exact ⟨y, hy, Metric.mem_closedBall.mp hxy⟩
        have hlineSet : Kakeya.VeryNotSticky.lineSet T0.x T0.direction = (L : Set E) := by
          ext x
          change (∃ t : Real, x = T0.x + t • T0.direction) <-> x ∈ L
          rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
          constructor
          · rintro ⟨t, rfl⟩
            refine ⟨t, ?_⟩
            simp only [AffineMap.lineMap_apply_module, _root_.Tube.direction]
            module
          · rintro ⟨t, rfl⟩
            refine ⟨t, ?_⟩
            simp only [AffineMap.lineMap_apply_module, _root_.Tube.direction]
            module
        have hPlines (j : ι) (hj : j ∈ s) : (P j).carrier ⊆
            Kakeya.VeryNotSticky.lineNbhd T0.x T0.direction (512 * (ρ : Real)) := by
          obtain ⟨U, hUW, hUP⟩ := hfine j hj
          have hPnear : (P j).carrier <= (Kakeya.Tube.dilate (U.rescale ρ) 6).carrier := by
            apply Kakeya.Tube.subset_dilate_rescale_of_subset_dilate (P j) U (c := 1)
              (by norm_num) (by norm_num) (by norm_num)
            · exact hUP
            · exact _root_.Tube.subset_dilate (P j) (by norm_num)
          obtain ⟨p', hp', hUp'⟩ := happrox U.x (hUW U.x_mem_carrier)
          obtain ⟨q', hq', hUq'⟩ := happrox U.y (hUW U.y_mem_carrier)
          intro z hz
          obtain ⟨v, hv, hzAxis⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate
            (U.rescale ρ) (c := 6) (by norm_num) (hPnear hz)
          have hv3 : |v| <= 3 := by norm_num at hv; exact hv
          let t : Real := v + 1 / 2
          have ht : |t| <= 7 / 2 := by
            have h := abs_add_le v (1 / 2 : Real)
            norm_num at h
            dsimp [t]
            linarith
          have hOne : |1 - t| <= 7 / 2 := by
            have h := abs_sub (1 / 2 : Real) v
            norm_num at h
            rw [show 1 - t = 1 / 2 - v by dsimp [t]; ring]
            linarith
          let y := AffineMap.lineMap p' q' t
          have hyL : y ∈ L := AffineMap.lineMap_mem t hp' hq'
          have haxis : (U.rescale ρ).center + v • (U.rescale ρ).direction =
              AffineMap.lineMap U.x U.y t := by
            change midpoint Real U.x U.y + v • (U.y - U.x) = _
            rw [midpoint_eq_smul_add, AffineMap.lineMap_apply_module]
            simp only [invOf_eq_inv, t]
            module
          have hclose : dist ((U.rescale ρ).center + v • (U.rescale ρ).direction) y <=
              448 * (b : Real) := by
            rw [haxis, dist_eq_norm]
            have heq : AffineMap.lineMap U.x U.y t - y =
                (1 - t) • (U.x - p') + t • (U.y - q') := by
              simp only [AffineMap.lineMap_apply_module, y]
              module
            rw [heq]
            calc
              _ <= ‖(1 - t) • (U.x - p')‖ + ‖t • (U.y - q')‖ := norm_add_le _ _
              _ = |1 - t| * dist U.x p' + |t| * dist U.y q' := by
                simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
              _ <= (7 / 2) * (64 * (b : Real)) + (7 / 2) * (64 * (b : Real)) := by gcongr
              _ = 448 * (b : Real) := by ring
          have hzy : dist z y <= 512 * (ρ : Real) := by
            have hd := dist_triangle z ((U.rescale ρ).center + v • (U.rescale ρ).direction) y
            rw [← dist_eq_norm] at hzAxis
            linarith [ρ.coe_nonneg]
          unfold Kakeya.VeryNotSticky.lineNbhd
          rw [hlineSet]
          exact Metric.mem_cthickening_of_dist_le z y _ _ hyL hzy
        have hpush := isLineEssDistinctAt_push hρ (R₀ := 3) (by norm_num)
          hcen hmid hED (K := 512) (by norm_num)
        have hcard := hpush T0.x T0.direction T0.norm_direction
        rw [Finset.filter_eq_self.mpr hPlines] at hcard
        exact hcard
      have hVolume {δ ρ D aw bw cw c : NNReal} {M : Nat} {eta : Real}
          (W : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
          (P : Tube ρ (EuclideanSpace Real (Fin 3)))
          (hδ : 0 < δ) (hD : 0 < D) (hc : 0 < c) (hρ : ρ <= 1)
          (hDims : SourceZeroFactorDimensions D aw bw cw W)
          (hlong : c <= cw) (hecc : δ ^ eta * bw <= aw)
          (hparent : ρ <= 4 * D * bw * δ ^ (-(1 / (M : Real)))) :
          volume P.carrier <=
            (((16 * _root_.Tube.volume_le.C 3 * D ^ 5 /
              (Metric.lt_volume_convexHull.c 3 * c) : NNReal) : ENNReal) *
              ((δ ^ (-eta - 2 / (M : Real)) : NNReal) : ENNReal)) * volume W.carrier := by
        clear hAncestor hGrid hChord hDilation hCount
        have hprod : (D : ENNReal)⁻¹ * cw * ((D : ENNReal)⁻¹ * bw) *
            ((D : ENNReal)⁻¹ * aw) <=
            ∏ i ∈ Finset.range 3, Metric.ethickness Real W.carrier i := by
          norm_num [Finset.prod_range_succ]
          exact mul_le_mul' (mul_le_mul' hDims.1 hDims.2.2.1) hDims.2.2.2.2.1
        have hVol : ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
            ((D : ENNReal)⁻¹ * cw * ((D : ENNReal)⁻¹ * bw) *
              ((D : ENNReal)⁻¹ * aw)) <= volume W.carrier := by
          refine (mul_le_mul' le_rfl hprod).trans ?_
          simpa using W.convex'.convex.ethickness_prod_le_volume
        let low : NNReal := Metric.lt_volume_convexHull.c 3 / D ^ 3 * c * δ ^ eta * bw ^ 2
        have hlow : (low : ENNReal) <= volume W.carrier := by
          refine le_trans ?_ hVol
          calc
            (low : ENNReal) = ((Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal) *
                ((D : ENNReal)⁻¹ * c * ((D : ENNReal)⁻¹ * bw) *
                  ((D : ENNReal)⁻¹ * (((δ ^ eta : NNReal) : ENNReal) * bw))) := by
              simp only [low, div_eq_mul_inv, ENNReal.coe_mul,
                ENNReal.coe_inv (pow_ne_zero 3 hD.ne'), ENNReal.coe_pow, ENNReal.inv_pow]
              ring
            _ <= _ := by
              have hecc' : (((δ ^ eta : NNReal) : ENNReal) * bw) <= (aw : ENNReal) := by
                exact_mod_cast hecc
              have hlong' : (c : ENNReal) <= (cw : ENNReal) := by exact_mod_cast hlong
              exact mul_le_mul' le_rfl (mul_le_mul'
                (mul_le_mul' (mul_le_mul' le_rfl hlong') le_rfl)
                (mul_le_mul' le_rfl hecc'))
        let ratio : NNReal := 16 * _root_.Tube.volume_le.C 3 * D ^ 5 /
          (Metric.lt_volume_convexHull.c 3 * c) * δ ^ (-eta - 2 / (M : Real))
        have hκ : Metric.lt_volume_convexHull.c 3 ≠ 0 := (Metric.lt_volume_convexHull.c_pos 3).ne'
        have hpow : (δ ^ (-(1 / (M : Real)))) ^ (2 : Nat) = δ ^ (-2 / (M : Real)) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
          congr 1
          ring
        have hcancel : δ ^ (-eta - 2 / (M : Real)) * δ ^ eta = δ ^ (-2 / (M : Real)) := by
          rw [← NNReal.rpow_add hδ.ne']
          congr 1
          ring
        have heq : _root_.Tube.volume_le.C 3 * (4 * D * bw * δ ^ (-(1 / (M : Real)))) ^ 2 =
            ratio * low := by
          dsimp [ratio, low]
          rw [mul_pow, hpow]
          calc
            _ = 16 * _root_.Tube.volume_le.C 3 * D ^ 2 * bw ^ 2 * δ ^ (-2 / (M : Real)) := by ring
            _ = (16 * _root_.Tube.volume_le.C 3 * D ^ 2 * bw ^ 2) *
                (δ ^ (-eta - 2 / (M : Real)) * δ ^ eta) := by rw [hcancel]
            _ = _ := by field_simp [hD.ne', hc.ne', hκ]
        calc
          volume P.carrier <= ((_root_.Tube.volume_le.C 3 * ρ ^ 2 : NNReal) : ENNReal) := by
            simpa using _root_.Tube.volume_le hρ P
          _ <= ((_root_.Tube.volume_le.C 3 *
              (4 * D * bw * δ ^ (-(1 / (M : Real)))) ^ 2 : NNReal) : ENNReal) := by
            exact_mod_cast (mul_le_mul_right (pow_le_pow_left₀ (by positivity) hparent 2) _)
          _ = (ratio : ENNReal) * low := by rw [heq, ENNReal.coe_mul]
          _ <= (ratio : ENNReal) * volume W.carrier := mul_le_mul' le_rfl hlow
          _ = _ := by simp only [ratio, ENNReal.coe_mul]
      have haM : a < M := ham.trans hm1
      have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
      have hbw : 0 < bw := haw.trans_le hawb
      have hw : 0 < D * bw := mul_pos hDpos hbw
      obtain ⟨parentA, hplaceA, hmemA, hfibreA⟩ := hAncestor QB ham.le hm1.le
      have hpartMem (ja : ι) (hja : ja ∈ QB.indexSet a) (part : Finset ι)
          (hpart : part ∈ (F ja hja).parts) (i : ι) (hi : i ∈ part) :
          i ∈ QB.indexSet m1 /\ parentA i = ja := by
        have h := (F ja hja).toFinpartition.subset hpart hi
        rw [hfibreA ja] at h
        exact Finset.mem_filter.mp h
      have hHullA (ja : ι) (hja : ja ∈ QB.indexSet a) (part : Finset ι)
          (hpart : part ∈ (F ja hja).parts) :
          part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody) <=
            (QB.tube a ja).toConvexSpaceBody := by
        apply (((F ja hja).toFinpartition.nonempty_of_mem_parts hpart).convexHull_biUnion_le_iff _ _).mpr
        intro i hi
        have h := hpartMem ja hja part hpart i hi
        simpa only [h.2] using (hmemA i h.1).2
      have hball (ja : ι) (hja : ja ∈ QB.indexSet a) (part : Finset ι)
          (hpart : part ∈ (F ja hja).parts) :
          (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)).carrier <=
            Metric.closedBall 0 3 := by
        intro x hx
        exact hgeom.coarse_ball a haM ja hja (hHullA ja hja part hpart hx)
      have hfine : sourceTowerRadius δ M m1 <= D * bw := by
        obtain ⟨i, hi⟩ := hgeom.nonempty
        let ja := QB.place a i
        have hja : ja ∈ QB.indexSet a := QB.place_mem a haM.le i hi
        have him : QB.place m1 i ∈ QB.fibre a m1 ja := by
          exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩
        obtain ⟨part, hpart, hipart⟩ := (F ja hja).toFinpartition.exists_mem him
        have hthick : (sourceTowerRadius δ M m1 : ENNReal) <=
            ethickness Real (QB.tube m1 (QB.place m1 i)).carrier 2 := by
          simpa using (QB.tube m1 (QB.place m1 i)).le_ethickness_finrank_sub_one
        have hsub := part.le_convexHull_biUnion
          (fun k => (QB.tube m1 k).toConvexSpaceBody) hipart
        have hupper := hDims ja hja part hpart
        have hfinal := hthick.trans ((Metric.ethickness_monotone hsub 2).trans hupper.2.2.2.2.2)
        have hshort : sourceTowerRadius δ M m1 <= D * aw := by exact_mod_cast hfinal
        exact hshort.trans (mul_le_mul_right hawb D)
      obtain ⟨p, hap, hpm, hparentLower, _, hparentUpper⟩ :=
        hGrid hδ hδ1 hw ham hm1 hfine
      have hpM : p < M := hpm.trans hm1
      obtain ⟨parent, hplace, hmem, hfibre⟩ := hAncestor QB hpm.le hm1.le
      have hrpos : 0 < sourceTowerRadius δ M p := by
        simp only [sourceTowerRadius, if_pos hpM]
        positivity
      have hrbound : sourceTowerRadius δ M p <= 1 / 40 := by
        simp only [sourceTowerRadius, if_pos hpM]
        calc
          (1 / 40 : NNReal) * δ ^ ((p : Real) / M) <= (1 / 40) * 1 := by
            gcongr
            exact NNReal.rpow_le_one hδ1 (by positivity)
          _ = 1 / 40 := mul_one _
      have hproper (hpa : p ≠ a) : 4 * D * bw <= sourceTowerRadius δ M p := by
        rcases hparentLower with h | h
        · exact (hpa h).elim
        · simpa only [mul_assoc] using h
      have hsmall (hpa : p ≠ a) : D * bw <= 1 / 8 := by
        have h := (hproper hpa).trans hrbound
        nlinarith
      have hpartParent (ja : ι) (hja : ja ∈ QB.indexSet a) (part : Finset ι)
          (hpart : part ∈ (F ja hja).parts) : part.image parent ⊆ QB.indexSet p := by
        intro jp hjp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjp
        exact (hmem i (hpartMem ja hja part hpart i hi).1).1
      have hAtA (hpa : p = a) (ja : ι) (hja : ja ∈ QB.indexSet a) (part : Finset ι)
          (hpart : part ∈ (F ja hja).parts) (i : ι) (hi : i ∈ part) : parent i = ja := by
        have h := (F ja hja).toFinpartition.subset hpart hi
        rw [← hpa, hfibre ja] at h
        exact (Finset.mem_filter.mp h).2
      have hthin (ja : ι) (hja : ja ∈ QB.indexSet a) (part : Finset ι)
          (hpart : part ∈ (F ja hja).parts) :
          ethickness Real (part.convexHull_biUnion
            (fun k => (QB.tube m1 k).toConvexSpaceBody)).carrier 1 <= ((D * bw : NNReal) : ENNReal) := by
        simpa only [ENNReal.coe_mul] using (hDims ja hja part hpart).2.2.2.1
      refine ⟨p, parent, hap, hpm, hplace, hmem, hfibre, ?_, ?_, ?_, ?_, hball, ?_⟩
      · simpa only [mul_assoc] using hparentUpper
      · intro hpa
        exact hproper (Ne.symm (Nat.ne_of_lt hpa))
      · intro ja hja part hpart
        by_cases hpa : p = a
        · have hsub : part.image parent ⊆ {ja} := by
            intro jp hjp
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjp
            exact Finset.mem_singleton.mpr (hAtA hpa ja hja part hpart i hi)
          exact (Finset.card_le_card hsub).trans (by simp)
        obtain ⟨i0, hi0⟩ := (F ja hja).toFinpartition.nonempty_of_mem_parts hpart
        have hline := hChord (QB.tube m1 i0)
          (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)) hw (hsmall hpa)
          (part.le_convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody) hi0)
          (hball ja hja part hpart) (hthin ja hja part hpart)
        have hbρ : D * bw <= sourceTowerRadius δ M p := by
          have h := hproper hpa
          nlinarith
        have hmid (jp : ι) (hjp : jp ∈ part.image parent) : ‖(QB.tube p jp).midpoint‖ <= 3 := by
          have h := hgeom.coarse_ball p hpM jp (hpartParent ja hja part hpart hjp)
            (_root_.Tube.midpoint_mem_carrier hrpos (QB.tube p jp))
          simpa only [Metric.mem_closedBall, dist_zero_right] using h
        have hcard := hCount (part.image parent) (QB.tube p) (QB.tube m1 i0)
          (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)).carrier
          hrpos hbρ (fun jp hjp => hgeom.coarse_centred p hpM jp (hpartParent ja hja part hpart hjp))
          hmid ((hgeom.coarse_ed p hpM).subset (hpartParent ja hja part hpart)) hline (by
            intro jp hjp
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hjp
            exact ⟨QB.tube m1 i,
              fun _ hx => part.le_convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody) hi hx,
              (hmem i (hpartMem ja hja part hpart i hi).1).2⟩)
        have hcard' : (part.image parent).card <= Nat.ceil (coverFibreConstant 3 3 512 * A1) := by
          simpa using hcard
        exact hcard'.trans (le_max_left _ _)
      · intro ja hja part hpart i hi
        by_cases hpa : p = a
        · rw [hAtA hpa ja hja part hpart i hi, hpa]
          exact (hHullA ja hja part hpart).trans (_root_.Tube.subset_dilate _ (by norm_num))
        have hsub := part.le_convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody) hi
        have hline := hChord (QB.tube m1 i)
          (part.convexHull_biUnion (fun k => (QB.tube m1 k).toConvexSpaceBody)) hw (hsmall hpa)
          hsub (hball ja hja part hpart) (hthin ja hja part hpart)
        have hUP := (hmem i (hpartMem ja hja part hpart i hi).1).2
        apply hDilation (QB.tube p (parent i)) (hsmall hpa) (by have h := hproper hpa; nlinarith)
          (hUP (QB.tube m1 i).x_mem_carrier) (hUP (QB.tube m1 i).y_mem_carrier)
          (QB.tube m1 i).dist_eq_one ?_ hline
        intro x hx
        have hx0 := hball ja hja part hpart hx
        have hp0 := hball ja hja part hpart (hsub (QB.tube m1 i).x_mem_carrier)
        have h := dist_triangle x 0 (QB.tube m1 i).x
        rw [dist_comm 0 (QB.tube m1 i).x] at h
        exact h.trans (by linarith [Metric.mem_closedBall.mp hx0, Metric.mem_closedBall.mp hp0])
      · intro jp ja hja part hpart
        exact hVolume _ (QB.tube p jp) hδ hDpos hc
          (hrbound.trans ((div_le_iff₀ (by norm_num : (0 : NNReal) < 40)).mpr (by norm_num)))
          (hDims ja hja part hpart) hlong hecc (by simpa only [mul_assoc] using hparentUpper.le)
    have hfinalGeometry (A H : ENNReal) (hA : A ≠ ⊤) (hH : H ≠ ⊤) (K M : Nat)
        {eta bias : Real} (heta : 0 < eta) (hbias : bias <= eta / 16)
        (hmesh : 8 / eta <= (M : Real)) :
        ∀ᶠ δ : NNReal in 𝓝[>] 0,
        ∀ {ι : Type u} {S U R : Finset ι}
          {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {C a p m : Nat},
        ∀ (Q : SourceThreadedTower S T M C) (QU : SourceThreadedTower U T M C)
          (QR : SourceThreadedTower R T M C),
        SourceTowerRestriction Q QU -> SourceTowerRestriction QU QR ->
        a <= p -> p <= m -> m <= M ->
        ∀ (F : ∀ ja, ja ∈ Q.indexSet a ->
          Factorization (Q.fibre a m ja) (fun i => (Q.tube m i).toConvexSpaceBody)
            (sourceParentPlankConstant δ bias)) (parent : ι -> ι) (pick : Finset ι -> ι),
        (∀ i ∈ S, parent (Q.place m i) = Q.place p i) ->
        (∀ ja, ∀ hja : ja ∈ Q.indexSet a, ∀ J ∈ (F ja hja).parts,
          QU.indexSet m ∩ J = J.filter (fun i => parent i = pick J)) ->
        (∀ ja, ∀ hja : ja ∈ Q.indexSet a, ∀ J ∈ (F ja hja).parts,
          (∑ i ∈ J, volume (Q.tube m i).carrier) <=
            H * ∑ i ∈ QU.indexSet m ∩ J, volume (Q.tube m i).carrier) ->
        (∀ i ∈ Q.indexSet m, 0 < volume (Q.tube m i).carrier) ->
        (∀ i ∈ QU.indexSet m,
          (Q.tube m i).toConvexSpaceBody <= (Q.tube p (parent i)).toConvexSpaceBody) ->
        (∀ ja, ∀ hja : ja ∈ Q.indexSet a, ∀ J ∈ (F ja hja).parts, ∀ i ∈ J,
          (J.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier <=
            (Kakeya.Tube.dilate (Q.tube p (parent i)) 128).carrier) ->
        (∀ j ∈ QU.indexSet p, ∀ ja, ∀ hja : ja ∈ Q.indexSet a,
          ∀ J ∈ (F ja hja).parts, volume (Q.tube p j).carrier <=
            (A * (δ : ENNReal) ^ (-eta - 2 / (M : Real))) *
              volume (J.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier) ->
        (∀ j ∈ QR.indexSet p,
          (∑ i ∈ QU.fibre p m j, volume (QU.tube m i).carrier) <=
            sourceFixedPreparationLoss K δ * ∑ i ∈ QR.fibre p m j, volume (QR.tube m i).carrier) ->
        (∀ ja ∈ QR.indexSet a, Kakeya.maxDensity (QR.fibre a p ja)
          (fun j => (QR.tube p j).toConvexSpaceBody) <= (δ : ENNReal) ^ (-2 * eta)) /\
        ∀ j ∈ QR.indexSet p, IsFrostmanIn (QR.fibre p m j)
          (fun i => (QR.tube m i).toConvexSpaceBody) (QR.tube p j).toConvexSpaceBody
          ((δ : ENNReal) ^ (-2 * eta)) := by
      clear hD hc
      clear hchain hparentGeometry
      classical
      have hbudget (A : ENNReal) (hA : A ≠ ⊤) (K M : Nat) {eta bias : Real}
          (heta : 0 < eta) (hbias : bias <= eta / 16) (hmesh : 8 / eta <= (M : Real)) :
          ∀ᶠ δ : NNReal in 𝓝[>] 0,
            A * sourceFixedPreparationLoss K δ * (δ : ENNReal) ^ (-3 * bias) *
              (δ : ENNReal) ^ (-eta - 2 / (M : Real)) <= (δ : ENNReal) ^ (-2 * eta) := by
        have hM : 0 < (M : Real) := lt_of_lt_of_le (by positivity : 0 < 8 / eta) hmesh
        have hstep : 2 / (M : Real) <= eta / 4 := by
          have hcross : 8 <= (M : Real) * eta := (div_le_iff₀ heta).mp hmesh
          apply (div_le_iff₀ hM).mpr
          nlinarith
        have hbudget : -2 * eta <= -(eta / 2) + (-3 * bias) + (-eta - 2 / (M : Real)) := by
          linarith
        filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
          (K := A * (2 : ENNReal) ^ K) (by finiteness) (by positivity : 0 < eta / 4),
          ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (by positivity : 0 < eta / 4) K,
          Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with δ hfixed hpoly hd
        have hδ0 : (δ : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
        have hδ1 : (δ : ENNReal) <= 1 := by exact_mod_cast hd.2.le
        have hdreal : (0 : Real) < δ := by exact_mod_cast hd.1
        have hdreal1 : (δ : Real) <= 1 := by exact_mod_cast hd.2.le
        have hlog : 0 <= Real.logb 2 (1 / (δ : Real)) :=
          Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hdreal]; linarith)
        have hbound : sourceFixedPreparationLoss K δ <=
            (2 : ENNReal) ^ K * ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : Real))) ^ K := by
          calc
            _ <= ENNReal.ofReal ((2 * (1 + Real.logb 2 (1 / (δ : Real)))) ^ K) := by
              apply ENNReal.ofReal_le_ofReal
              gcongr
              linarith
            _ = _ := by
              rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), mul_pow]
              norm_num
        have hpaid : A * sourceFixedPreparationLoss K δ <= (δ : ENNReal) ^ (-(eta / 2)) := by
          calc
            _ <= (A * (2 : ENNReal) ^ K) *
                ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : Real))) ^ K := by
              rw [mul_assoc]
              exact mul_le_mul' le_rfl hbound
            _ <= (δ : ENNReal) ^ (-(eta / 4)) * (δ : ENNReal) ^ (-(eta / 4)) :=
              mul_le_mul' hfixed hpoly
            _ = _ := by
              rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
              congr 1
              ring
        calc
          _ <= (δ : ENNReal) ^ (-(eta / 2)) * (δ : ENNReal) ^ (-3 * bias) *
              (δ : ENNReal) ^ (-eta - 2 / (M : Real)) := by gcongr
          _ = (δ : ENNReal) ^ (-(eta / 2) + (-3 * bias) + (-eta - 2 / (M : Real))) := by
            rw [← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ hδ0 ENNReal.coe_ne_top]
          _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hbudget
      have hraw {ι : Type u} {δ : NNReal} {S U : Finset ι}
          {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C a p m : Nat}
          (Q : SourceThreadedTower S T M C) (QU : SourceThreadedTower U T M C)
          (hrest : SourceTowerRestriction Q QU) (hap : a <= p) (hpm : p <= m) (hm : m <= M)
          (CF : NNReal) (H Vratio : ENNReal)
          (F : ∀ ja, ja ∈ Q.indexSet a ->
            Factorization (Q.fibre a m ja) (fun i => (Q.tube m i).toConvexSpaceBody) CF)
          (parent : ι -> ι) (pick : Finset ι -> ι)
          (hplace : ∀ i ∈ S, parent (Q.place m i) = Q.place p i)
          (hgroup : ∀ ja, ∀ hja : ja ∈ Q.indexSet a, ∀ J ∈ (F ja hja).parts,
            QU.indexSet m ∩ J = J.filter (fun i => parent i = pick J))
          (hret : ∀ ja, ∀ hja : ja ∈ Q.indexSet a, ∀ J ∈ (F ja hja).parts,
            (∑ i ∈ J, volume (Q.tube m i).carrier) <=
              H * ∑ i ∈ QU.indexSet m ∩ J, volume (Q.tube m i).carrier)
          (hVpos : ∀ i ∈ Q.indexSet m, 0 < volume (Q.tube m i).carrier)
          (hVP : ∀ i ∈ QU.indexSet m,
            (Q.tube m i).toConvexSpaceBody <= (Q.tube p (parent i)).toConvexSpaceBody)
          (hdilate : ∀ ja, ∀ hja : ja ∈ Q.indexSet a, ∀ J ∈ (F ja hja).parts, ∀ i ∈ J,
            (J.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier <=
              (Kakeya.Tube.dilate (Q.tube p (parent i)) 128).carrier)
          (hvol : ∀ j ∈ QU.indexSet p, ∀ ja, ∀ hja : ja ∈ Q.indexSet a,
            ∀ J ∈ (F ja hja).parts, volume (Q.tube p j).carrier <=
              Vratio * volume (J.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier) :
          (∀ ja ∈ QU.indexSet a, Kakeya.maxDensity (QU.fibre a p ja)
            (fun j => (QU.tube p j).toConvexSpaceBody) <= Vratio * ((512 : ENNReal) ^ 3 * 6) * CF) /\
          ∀ j ∈ QU.indexSet p, IsFrostmanIn (QU.fibre p m j)
            (fun i => (QU.tube m i).toConvexSpaceBody) (QU.tube p j).toConvexSpaceBody
            ((CF : ENNReal) * H * Vratio) := by
        clear hbudget
        classical
        have hheavy {ι : Type u} {σ ρ : NNReal} {s R : Finset ι} (CF : NNReal) (H Vratio : ENNReal)
            (V : ι -> Tube σ (EuclideanSpace Real (Fin 3)))
            (P : ι -> Tube ρ (EuclideanSpace Real (Fin 3)))
            (F : Factorization s (fun i => (V i).toConvexSpaceBody) CF)
            (parent : ι -> ι) (pick : Finset ι -> ι) (hRs : R <= s)
            (hgroup : ∀ J ∈ F.parts, R ∩ J = J.filter (fun i => parent i = pick J))
            (hret : ∀ J ∈ F.parts, (∑ i ∈ J, volume (V i).carrier) <=
              H * ∑ i ∈ R ∩ J, volume (V i).carrier)
            (hVpos : ∀ i ∈ s, 0 < volume (V i).carrier)
            (hVP : ∀ i ∈ R, (V i).toConvexSpaceBody <= (P (parent i)).toConvexSpaceBody)
            (hdilate : ∀ J ∈ F.parts, ∀ i ∈ J,
              (J.convexHull_biUnion (fun k => (V k).toConvexSpaceBody)).carrier <=
                (Kakeya.Tube.dilate (P (parent i)) 128).carrier)
            (hvol : ∀ j ∈ R.image parent, ∀ J ∈ F.parts, volume (P j).carrier <=
              Vratio * volume (J.convexHull_biUnion (fun k => (V k).toConvexSpaceBody)).carrier) :
            Kakeya.maxDensity (R.image parent) (fun j => (P j).toConvexSpaceBody) <=
              Vratio * ((512 : ENNReal) ^ 3 * 6) * CF /\
            ∀ j ∈ R.image parent, IsFrostmanIn (R.filter (fun i => parent i = j))
              (fun i => (V i).toConvexSpaceBody) (P j).toConvexSpaceBody ((CF : ENNReal) * H * Vratio) := by
          classical
          have hcharge {ι κ : Type u} {s R : Finset ι} (parts : Finpartition s)
              (parent : ι -> κ) (pick : Finset ι -> κ) (hRs : R <= s)
              (hgroup : ∀ J ∈ parts.parts, R ∩ J = J.filter (fun i => parent i = pick J)) :
              ∃ charge : κ -> Finset ι,
                (∀ j ∈ R.image parent, charge j ∈ parts.parts /\ pick (charge j) = j /\
                  (R ∩ charge j).Nonempty) /\
                Set.InjOn charge (R.image parent : Set κ) := by
            classical
            have hchoice (j : κ) (hj : j ∈ R.image parent) :
                ∃ J ∈ parts.parts, pick J = j /\ (R ∩ J).Nonempty := by
              obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
              obtain ⟨J, hJ, hiJ⟩ := parts.exists_mem (hRs hi)
              have hgroupi : i ∈ J.filter (fun i => parent i = pick J) :=
                hgroup J hJ ▸ Finset.mem_inter.mpr ⟨hi, hiJ⟩
              exact ⟨J, hJ, (Finset.mem_filter.mp hgroupi).2.symm.trans hij,
                ⟨i, Finset.mem_inter.mpr ⟨hi, hiJ⟩⟩⟩
            let charge (j : κ) := if hj : j ∈ R.image parent then (hchoice j hj).choose else ∅
            have hcharge (j : κ) (hj : j ∈ R.image parent) :
                charge j ∈ parts.parts /\ pick (charge j) = j /\ (R ∩ charge j).Nonempty := by
              simpa only [charge, dif_pos hj] using (hchoice j hj).choose_spec
            refine ⟨charge, hcharge, ?_⟩
            intro j hj j' hj' heq
            calc
              j = pick (charge j) := (hcharge j hj).2.1.symm
              _ = pick (charge j') := congrArg pick heq
              _ = j' := (hcharge j' hj').2.1
          
          have htransfer {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
              [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
              {ι κ : Type u} {ρ : NNReal} (s : Finset ι) (t : Finset κ)
              (P : ι -> _root_.Tube ρ E) (W : κ -> ConvexSpaceBody E) (f : ι -> κ)
              (Vratio : ENNReal)
              (hfinj : ∀ j ∈ s, ∀ j' ∈ s, f j = f j' -> j = j')
              (hft : ∀ j ∈ s, f j ∈ t)
              (hsub : ∀ j ∈ s, (W (f j)).carrier <= (Kakeya.Tube.dilate (P j) 128).carrier)
              (hvol : ∀ j ∈ s, volume (P j).carrier <= Vratio * volume (W (f j)).carrier) :
              Kakeya.maxDensity s (fun j => (P j).toConvexSpaceBody) <=
                Vratio * ((512 : ENNReal) ^ Module.finrank Real E *
                  ((Module.finrank Real E).factorial : ENNReal)) * Kakeya.maxDensity t W := by
            classical
            rw [Kakeya.maxDensity_le_iff]
            intro K
            rw [Kakeya.densityIn_le_iff]
            let A := s.filter (fun j => (P j).toConvexSpaceBody <= K)
            change (∑ j ∈ A, volume (P j).carrier) <= _
            have hAs : A <= s := Finset.filter_subset _ _
            have hjK (j : ι) (hj : j ∈ A) : (P j).toConvexSpaceBody <= K :=
              (Finset.mem_filter.mp hj).2
            by_cases hK0 : volume K.carrier = 0
            · have hzero : ∑ j ∈ A, volume (P j).carrier = 0 := by
                apply Finset.sum_eq_zero
                intro j hj
                exact le_zero_iff.mp ((measure_mono (hjK j hj)).trans hK0.le)
              rw [hzero]
              exact zero_le
            obtain ⟨D, _, hcontainer, hDvol⟩ := K.convex'.convex.exists_homothety_container
              hK0 K.isCompact'.measure_lt_top.ne (lam := 128) (by norm_num)
            have hDvol' : volume D.carrier <=
                ((512 : ENNReal) ^ Module.finrank Real E *
                  ((Module.finrank Real E).factorial : ENNReal)) * volume K.carrier := by
              norm_num only [show (4 : Real) * 128 = 512 by norm_num, ENNReal.ofReal_ofNat] at hDvol
              exact hDvol
            have hPD (j : ι) (hj : j ∈ A) :
                (Kakeya.Tube.dilate (P j) 128).carrier <= D.carrier := by
              have hcenter : (P j).center ∈ (P j).carrier :=
                (P j).convex'.convex.midpoint_mem (P j).x_mem_carrier (P j).y_mem_carrier
              rw [Kakeya.Tube.dilate_carrier]
              rintro x ⟨y, hy, rfl⟩
              simpa only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] using
                hcontainer (P j).center (hjK j hj hcenter) y (hjK j hj hy)
            have hmap : A.image f <= t.filter (fun i => W i <= D.toConvexSpaceBody) := by
              intro i hi
              obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
              exact Finset.mem_filter.mpr ⟨hft j (hAs hj), (hsub j (hAs hj)).trans (hPD j hj)⟩
            have hsum : (∑ j ∈ A, volume (W (f j)).carrier) <=
                Kakeya.maxDensity t W * volume D.carrier := by
              calc
                _ = ∑ i ∈ A.image f, volume (W i).carrier := by
                  rw [Finset.sum_image]
                  exact fun j hj j' hj' h => hfinj j (hAs hj) j' (hAs hj') h
                _ <= ∑ i ∈ t.filter (fun i => W i <= D.toConvexSpaceBody), volume (W i).carrier :=
                  Finset.sum_le_sum_of_subset hmap
                _ <= Kakeya.maxDensity t W * volume D.carrier := by
                  exact Kakeya.sum_volume_le_maxDensity_mul_volume t W D.toConvexSpaceBody
            calc
              _ <= ∑ j ∈ A, Vratio * volume (W (f j)).carrier :=
                Finset.sum_le_sum (fun j hj => hvol j (hAs hj))
              _ = Vratio * ∑ j ∈ A, volume (W (f j)).carrier := by rw [Finset.mul_sum]
              _ <= Vratio * (Kakeya.maxDensity t W * volume D.carrier) := by gcongr
              _ <= Vratio * (Kakeya.maxDensity t W *
                  (((512 : ENNReal) ^ Module.finrank Real E *
                    ((Module.finrank Real E).factorial : ENNReal)) * volume K.carrier)) := by gcongr
              _ = (Vratio * ((512 : ENNReal) ^ Module.finrank Real E *
                  ((Module.finrank Real E).factorial : ENNReal)) * Kakeya.maxDensity t W) *
                  volume K.carrier := by ring
          
          have hfragments {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
              [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
              {ι : Type u} {R : Finset ι} (parts : Finpartition R)
              (V : ι -> ConvexSpaceBody E) (W : Finset ι -> ConvexSpaceBody E)
              (old : Finset ι -> Finset ι) (K : ConvexSpaceBody E) (C H Vratio : ENNReal)
              (hVK : ∀ i ∈ R, V i <= K)
              (hOld : ∀ J ∈ parts.parts, J <= old J)
              (hVW : ∀ J ∈ parts.parts, ∀ i ∈ old J, V i <= W J)
              (hFr : ∀ J ∈ parts.parts, IsFrostmanIn (old J) V (W J) C)
              (hW0 : ∀ J ∈ parts.parts, volume (W J).carrier ≠ 0)
              (hret : ∀ J ∈ parts.parts, (∑ i ∈ old J, volume (V i).carrier) <=
                H * ∑ i ∈ J, volume (V i).carrier)
              (hvol : ∀ J ∈ parts.parts, volume K.carrier <= Vratio * volume (W J).carrier) :
              IsFrostmanIn R V K (C * H * Vratio) := by
            classical
            have hJK (J : Finset ι) (hJ : J ∈ parts.parts) : ∀ i ∈ J, V i <= K :=
              fun i hi => hVK i (parts.le hJ hi)
            have hpart (J : Finset ι) (hJ : J ∈ parts.parts) :
                Kakeya.maxDensity J V <= (C * H * Vratio) * Kakeya.densityIn J V K := by
              apply (ENNReal.mul_le_mul_iff_left (hW0 J hJ) (W J).isCompact'.measure_ne_top).mp
              calc
                Kakeya.maxDensity J V * volume (W J).carrier <=
                    Kakeya.maxDensity (old J) V * volume (W J).carrier := by
                  gcongr
                  exact Kakeya.maxDensity_mono V (hOld J hJ)
                _ <= (C * Kakeya.densityIn (old J) V (W J)) * volume (W J).carrier := by
                  gcongr
                  exact (hFr J hJ).maxDensity_le_of_carrier_subset (hVW J hJ)
                _ = C * ∑ i ∈ old J, volume (V i).carrier := by
                  rw [mul_assoc, ← Kakeya.sum_volume_eq_densityIn_mul_volume' (hVW J hJ)]
                _ <= C * (H * ∑ i ∈ J, volume (V i).carrier) := mul_le_mul' le_rfl (hret J hJ)
                _ = (C * H) * (Kakeya.densityIn J V K * volume K.carrier) := by
                  rw [← mul_assoc, Kakeya.sum_volume_eq_densityIn_mul_volume' (hJK J hJ)]
                _ <= (C * H) * (Kakeya.densityIn J V K * (Vratio * volume (W J).carrier)) :=
                  mul_le_mul' le_rfl (mul_le_mul' le_rfl (hvol J hJ))
                _ = ((C * H * Vratio) * Kakeya.densityIn J V K) * volume (W J).carrier := by ring
            have hsum : (∑ J ∈ parts.parts, Kakeya.densityIn J V K) = Kakeya.densityIn R V K := by
              calc
                _ = ∑ J ∈ parts.parts, (∑ i ∈ J, volume (V i).carrier) / volume K.carrier := by
                  apply Finset.sum_congr rfl
                  intro J hJ
                  simp only [Kakeya.densityIn, Finset.filter_eq_self.mpr (hJK J hJ)]
                _ = (∑ i ∈ R, volume (V i).carrier) / volume K.carrier := by
                  simp only [div_eq_mul_inv]
                  rw [← Finset.sum_mul, ← parts.sum_eq_sum_parts_sum]
                _ = Kakeya.densityIn R V K := by
                  simp only [Kakeya.densityIn, Finset.filter_eq_self.mpr hVK]
            apply IsFrostmanIn.of_maxDensity_le
            calc
              _ <= ∑ J ∈ parts.parts, Kakeya.maxDensity J V :=
                Kakeya.maxDensity_le_sum_of_subset_biUnion V parts.biUnion_parts.ge
              _ <= ∑ J ∈ parts.parts, (C * H * Vratio) * Kakeya.densityIn J V K :=
                Finset.sum_le_sum hpart
              _ = (C * H * Vratio) * Kakeya.densityIn R V K := by rw [← Finset.mul_sum, hsum]
          
        
          obtain ⟨charge, hcharge, hinj⟩ := hcharge F.toFinpartition parent pick hRs hgroup
          constructor
          · have hsub (j : ι) (hj : j ∈ R.image parent) :
                ((charge j).convexHull_biUnion (fun k => (V k).toConvexSpaceBody)).carrier <=
                  (Kakeya.Tube.dilate (P j) 128).carrier := by
              obtain ⟨i, hi⟩ := (hcharge j hj).2.2
              have hi' := Finset.mem_inter.mp hi
              have hipick : parent i = pick (charge j) := by
                have h := hi
                rw [hgroup (charge j) (hcharge j hj).1] at h
                exact (Finset.mem_filter.mp h).2
              have hparent : parent i = j := hipick.trans (hcharge j hj).2.1
              simpa only [hparent] using hdilate (charge j) (hcharge j hj).1 i hi'.2
            have hle := htransfer (R.image parent) F.parts P
              (fun J => J.convexHull_biUnion (fun k => (V k).toConvexSpaceBody)) charge Vratio
              (fun j hj j' hj' heq => hinj hj hj' heq)
              (fun j hj => (hcharge j hj).1) hsub
              (fun j hj => hvol j hj (charge j) (hcharge j hj).1)
            have hle' : Kakeya.maxDensity (R.image parent) (fun j => (P j).toConvexSpaceBody) <=
                Vratio * ((512 : ENNReal) ^ 3 * 6) *
                  Kakeya.maxDensity F.parts
                    (fun J => J.convexHull_biUnion (fun k => (V k).toConvexSpaceBody)) := by
              simpa [Nat.factorial] using hle
            exact hle'.trans (mul_le_mul' le_rfl F.isKatzTao)
          · intro j hj
            let Rj := R.filter (fun i => parent i = j)
            have hRjs : Rj <= s := (Finset.filter_subset _ _).trans hRs
            let G := F.toFinpartition.restrict hRjs
            have hexists (J : Finset ι) (hJ : J ∈ G.parts) :
                ∃ K ∈ F.parts, J = K ∩ Rj := by
              change J ∈ (F.parts.image (fun K => K ∩ Rj)).erase ∅ at hJ
              obtain ⟨K, hK, heq⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hJ)
              exact ⟨K, hK, heq.symm⟩
            let old (J : Finset ι) := if hJ : J ∈ G.parts then (hexists J hJ).choose else ∅
            have hold (J : Finset ι) (hJ : J ∈ G.parts) :
                old J ∈ F.parts /\ J = old J ∩ Rj := by
              simpa only [old, dif_pos hJ] using (hexists J hJ).choose_spec
            have hwhole (J : Finset ι) (hJ : J ∈ G.parts) : J = R ∩ old J := by
              obtain ⟨i, hi⟩ := G.nonempty_of_mem_parts hJ
              have hi' : i ∈ old J ∩ Rj := (hold J hJ).2 ▸ hi
              have hiK := (Finset.mem_inter.mp hi').1
              have hiRj := Finset.mem_filter.mp (Finset.mem_inter.mp hi').2
              have hpick : pick (old J) = j := by
                have hip : i ∈ (old J).filter (fun i => parent i = pick (old J)) := by
                  rw [← hgroup (old J) (hold J hJ).1]
                  exact Finset.mem_inter.mpr ⟨hiRj.1, hiK⟩
                exact (Finset.mem_filter.mp hip).2.symm.trans hiRj.2
              conv_lhs => rw [(hold J hJ).2]
              ext k
              simp only [Finset.mem_inter]
              constructor
              · intro hk
                exact ⟨(Finset.mem_filter.mp hk.2).1, hk.1⟩
              · intro hk
                have hkg : k ∈ (old J).filter (fun i => parent i = pick (old J)) := by
                  rw [← hgroup (old J) (hold J hJ).1]
                  exact Finset.mem_inter.mpr hk
                exact ⟨hk.2, Finset.mem_filter.mpr ⟨hk.1, (Finset.mem_filter.mp hkg).2.trans hpick⟩⟩
            apply hfragments G (fun i => (V i).toConvexSpaceBody)
              (fun J => (old J).convexHull_biUnion (fun i => (V i).toConvexSpaceBody))
              old (P j).toConvexSpaceBody CF H Vratio
            · intro i hi
              have hi' := Finset.mem_filter.mp hi
              simpa only [hi'.2] using hVP i hi'.1
            · intro J hJ
              conv_lhs => rw [(hold J hJ).2]
              exact Finset.inter_subset_left
            · intro J hJ i hi
              exact Finset.le_convexHull_biUnion (fun k => (V k).toConvexSpaceBody) hi
            · intro J hJ
              exact F.isFrostman (old J) (hold J hJ).1
            · intro J hJ
              obtain ⟨i, hi⟩ := F.nonempty_of_mem_parts (hold J hJ).1
              exact (lt_of_lt_of_le (hVpos i (F.le (hold J hJ).1 hi))
                (measure_mono (Finset.le_convexHull_biUnion (fun i => (V i).toConvexSpaceBody) hi))).ne'
            · intro J hJ
              calc
                _ <= H * ∑ i ∈ R ∩ old J, volume (V i).carrier := hret (old J) (hold J hJ).1
                _ = _ := by rw [← hwhole J hJ]
            · intro J hJ
              exact hvol j hj (old J) (hold J hJ).1
        
      
        have hmem {A : Finset ι} (Qt : SourceThreadedTower A T M C) (c d : Nat) (j i : ι) :
            i ∈ Qt.fibre c d j ↔ ∃ x ∈ A, Qt.place c x = j /\ Qt.place d x = i := by
          simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell, Finset.mem_image,
            Finset.mem_filter]
          aesop
        have hcompatible (c d : Nat) (hcd : c <= d) (hd : d <= M)
            (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
            (heq : Q.place d i = Q.place d j) : Q.place c i = Q.place c j := by
          induction d, hcd using Nat.le_induction with
          | base => exact heq
          | succ d hcd ih =>
            apply ih (Nat.le_of_succ_le hd)
            rw [Q.parent_composition d (Nat.lt_of_succ_le hd) i hi,
              Q.parent_composition d (Nat.lt_of_succ_le hd) j hj, heq]
        have hindex {A : Finset ι} (Qt : SourceThreadedTower A T M C)
            (c d : Nat) (hd : d <= M) (j i : ι) (hi : i ∈ Qt.fibre c d j) : i ∈ Qt.indexSet d := by
          obtain ⟨x, hx, hxc, rfl⟩ := (hmem Qt c d j i).mp hi
          exact Qt.place_mem d hd x hx
        have hindexU (k : Nat) (hk : k <= M) : QU.indexSet k <= Q.indexSet k := by
          intro j hj
          obtain ⟨x, hx, hkj⟩ := QU.place_surjective k hk j hj
          rw [hrest.assignment] at hkj
          rw [← hkj]
          exact Q.place_mem k hk x (hrest.subset hx)
        have hinter (c d : Nat) (hcd : c <= d) (hd : d <= M) (j : ι) :
            QU.fibre c d j = QU.indexSet d ∩ Q.fibre c d j := by
          ext i
          constructor
          · intro hi
            have hiU := hindex QU c d hd j i hi
            obtain ⟨x, hx, hxc, hxd⟩ := (hmem QU c d j i).mp hi
            rw [hrest.assignment] at hxc hxd
            exact Finset.mem_inter.mpr ⟨hiU, (hmem Q c d j i).mpr ⟨x, hrest.subset hx, hxc, hxd⟩⟩
          · intro hi
            have hi' := Finset.mem_inter.mp hi
            obtain ⟨x, hx, hxd⟩ := QU.place_surjective d hd i hi'.1
            rw [hrest.assignment] at hxd
            obtain ⟨y, hy, hyc, hyd⟩ := (hmem Q c d j i).mp hi'.2
            have hxc := (hcompatible c d hcd hd x (hrest.subset hx) y hy (hxd.trans hyd.symm)).trans hyc
            apply (hmem QU c d j i).mpr
            exact ⟨x, hx, by simpa only [hrest.assignment] using hxc,
              by simpa only [hrest.assignment] using hxd⟩
        have hplaceU (i : ι) (hi : i ∈ U) : parent (QU.place m i) = QU.place p i := by
          simpa only [hrest.assignment] using hplace i (hrest.subset hi)
        have himage (ja : ι) : (QU.fibre a m ja).image parent = QU.fibre a p ja := by
          ext j
          constructor
          · intro hj
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
            obtain ⟨x, hx, hxa, rfl⟩ := (hmem QU a m ja i).mp hi
            rw [hplaceU x hx]
            exact (hmem QU a p ja _).mpr ⟨x, hx, hxa, rfl⟩
          · intro hj
            obtain ⟨x, hx, hxa, hxp⟩ := (hmem QU a p ja j).mp hj
            exact Finset.mem_image.mpr ⟨QU.place m x, (hmem QU a m ja _).mpr ⟨x, hx, hxa, rfl⟩,
              (hplaceU x hx).trans hxp⟩
        have hfilter (ja j : ι) (hj : j ∈ QU.fibre a p ja) :
            (QU.fibre a m ja).filter (fun i => parent i = j) = QU.fibre p m j := by
          obtain ⟨y, hy, hya, hyp⟩ := (hmem QU a p ja j).mp hj
          ext i
          rw [Finset.mem_filter, hmem QU p m j i]
          constructor
          · rintro ⟨hi, hparij⟩
            obtain ⟨x, hx, hxa, hxi⟩ := (hmem QU a m ja i).mp hi
            refine ⟨x, hx, ?_, hxi⟩
            rw [← hplaceU x hx, hxi]
            exact hparij
          · rintro ⟨x, hx, hxp, hxi⟩
            have hxpy : QU.place p x = QU.place p y := hxp.trans hyp.symm
            rw [hrest.assignment] at hxpy
            have hxay := hcompatible a p hap (hpm.trans hm) x (hrest.subset hx) y (hrest.subset hy) hxpy
            have hxa : QU.place a x = ja := by
              rw [hrest.assignment]
              exact hxay.trans (by simpa only [hrest.assignment] using hya)
            refine ⟨(hmem QU a m ja i).mpr ⟨x, hx, hxa, hxi⟩, ?_⟩
            rw [← hxi, hplaceU x hx, hxp]
        have hlocal (ja : ι) (hjaU : ja ∈ QU.indexSet a) :
            Kakeya.maxDensity (QU.fibre a p ja) (fun j => (Q.tube p j).toConvexSpaceBody) <=
              Vratio * ((512 : ENNReal) ^ 3 * 6) * CF /\
            ∀ j ∈ QU.fibre a p ja, IsFrostmanIn (QU.fibre p m j)
              (fun i => (Q.tube m i).toConvexSpaceBody) (Q.tube p j).toConvexSpaceBody
              ((CF : ENNReal) * H * Vratio) := by
          have hja := hindexU a (hap.trans (hpm.trans hm)) hjaU
          have hRsub : QU.fibre a m ja <= Q.fibre a m ja := by
            rw [hinter a m (hap.trans hpm) hm ja]
            exact Finset.inter_subset_right
          have hpart (J : Finset ι) (hJ : J ∈ (F ja hja).parts) :
              QU.fibre a m ja ∩ J = QU.indexSet m ∩ J := by
            rw [hinter a m (hap.trans hpm) hm ja]
            ext i
            simp only [Finset.mem_inter]
            constructor
            · exact fun hi => ⟨hi.1.1, hi.2⟩
            · exact fun hi => ⟨⟨hi.1, (F ja hja).le hJ hi.2⟩, hi.2⟩
          obtain ⟨hdens, hFr⟩ := hheavy CF H Vratio (Q.tube m) (Q.tube p) (F ja hja)
            parent pick hRsub
            (fun J hJ => (hpart J hJ).trans (hgroup ja hja J hJ))
            (fun J hJ => by rw [hpart J hJ]; exact hret ja hja J hJ)
            (fun i hi => hVpos i (hindex Q a m hm ja i hi))
            (fun i hi => hVP i (hindex QU a m hm ja i hi))
            (fun J hJ i hi => hdilate ja hja J hJ i hi)
            (fun j hj J hJ => hvol j (hindex QU a p (hpm.trans hm) ja j (himage ja ▸ hj)) ja hja J hJ)
          rw [himage ja] at hdens hFr
          refine ⟨hdens, ?_⟩
          intro j hj
          simpa only [hfilter ja j hj] using hFr j hj
        constructor
        · intro ja hja
          simpa only [hrest.tubes] using (hlocal ja hja).1
        · intro j hj
          obtain ⟨x, hx, hxp⟩ := QU.place_surjective p (hpm.trans hm) j hj
          have hja : QU.place a x ∈ QU.indexSet a := QU.place_mem a (hap.trans (hpm.trans hm)) x hx
          have hjf : j ∈ QU.fibre a p (QU.place a x) := (hmem QU a p _ j).mpr ⟨x, hx, rfl, hxp⟩
          simpa only [hrest.tubes] using (hlocal (QU.place a x) hja).2 j hjf
      let B : ENNReal := (Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6) : NNReal)
      have hB : B ≠ ⊤ := ENNReal.coe_ne_top
      filter_upwards [hbudget (A * ((512 : ENNReal) ^ 3 * 6) * B) (by finiteness)
          0 M heta hbias hmesh,
        hbudget (A * H * B) (by finiteness) K M heta hbias hmesh,
        Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with δ hpaidD hpaidF hd
      intro ι S U R T C a p m Q QU QR hrest hfinal hap hpm hm F parent pick
        hplace hgroup hret hVpos hVP hdilate hvol hfinalret
      have hCF : (sourceParentPlankConstant δ bias : ENNReal) =
          B * (δ : ENNReal) ^ (-3 * bias) := by
        simp only [sourceParentPlankConstant, ENNReal.coe_mul,
          ENNReal.coe_rpow_of_ne_zero hd.1.ne', B]
      obtain ⟨hparent, hFr⟩ := hraw Q QU hrest hap hpm hm
        (sourceParentPlankConstant δ bias) H (A * (δ : ENNReal) ^ (-eta - 2 / (M : Real)))
        F parent pick hplace hgroup hret hVpos hVP hdilate hvol
      have hindex (k : Nat) (hk : k <= M) : QR.indexSet k <= QU.indexSet k := by
        intro j hj
        obtain ⟨x, hx, hxj⟩ := QR.place_surjective k hk j hj
        rw [hfinal.assignment] at hxj
        rw [← hxj]
        exact QU.place_mem k hk x (hfinal.subset hx)
      have hfibre (c d : Nat) (j : ι) : QR.fibre c d j <= QU.fibre c d j := by
        intro i hi
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
        have hx' := Finset.mem_filter.mp hx
        rw [hfinal.assignment] at hx' hxi
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨hfinal.subset hx'.1, hx'.2⟩, hxi⟩
      have hcontained (c d : Nat) (hcd : c <= d) (hd : d <= M)
          (i : ι) (hi : i ∈ U) :
          (QU.tube d (QU.place d i)).toConvexSpaceBody <=
            (QU.tube c (QU.place c i)).toConvexSpaceBody := by
        induction d, hcd using Nat.le_induction with
        | base => exact le_rfl
        | succ d hcd ih =>
          have hsub := QU.parent_containment d (Nat.lt_of_succ_le hd)
            (QU.place (d + 1) i) (QU.place_mem (d + 1) hd i hi)
          rw [← QU.parent_composition d (Nat.lt_of_succ_le hd) i hi] at hsub
          exact hsub.trans (ih (Nat.le_of_succ_le hd))
      constructor
      · intro ja hja
        rw [hfinal.tubes]
        calc
          _ <= Kakeya.maxDensity (QU.fibre a p ja) (fun j => (QU.tube p j).toConvexSpaceBody) :=
            Kakeya.maxDensity_mono _ (hfibre a p ja)
          _ <= _ := hparent ja (hindex a (hap.trans (hpm.trans hm)) hja)
          _ <= _ := by
            rw [hCF]
            simpa only [sourceFixedPreparationLoss, pow_zero, ENNReal.ofReal_one, mul_one, one_mul,
              mul_assoc, mul_comm, mul_left_comm] using hpaidD
      · intro j hj
        have hbase := hFr j (hindex p (hpm.trans hm) hj)
        have hsubFr : IsFrostmanIn (QR.fibre p m j)
            (fun i => (QU.tube m i).toConvexSpaceBody) (QU.tube p j).toConvexSpaceBody
            (((sourceParentPlankConstant δ bias : ENNReal) * H *
              (A * (δ : ENNReal) ^ (-eta - 2 / (M : Real)))) * sourceFixedPreparationLoss K δ) := by
          refine hbase.of_le_of_subset ?_ (hfibre p m j) ?_
          · intro i hi
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
            have hx' := Finset.mem_filter.mp hx
            simpa only [hx'.2] using hcontained p m hpm hm x hx'.1
          · simpa only [hfinal.tubes] using hfinalret j hj
        rw [hfinal.tubes]
        refine hsubFr.mono ?_
        rw [hCF]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hpaidF
    have hglobalPartition {ι : Type u} {δ : NNReal} {S : Finset ι}
        {T : ι -> Tube δ (EuclideanSpace Real (Fin 3))} {M C a m : Nat} {CF : NNReal}
        (Q : SourceThreadedTower S T M C) (ham : a <= m) (hm : m <= M)
        (F : ∀ j, j ∈ Q.indexSet a ->
          Factorization (Q.fibre a m j) (fun i => (Q.tube m i).toConvexSpaceBody) CF) :
        ∃ P : Finpartition (Q.indexSet m),
          (∀ j, ∀ hj : j ∈ Q.indexSet a, (F j hj).parts <= P.parts) /\
          ∀ J ∈ P.parts, ∃ j, ∃ hj : j ∈ Q.indexSet a, J ∈ (F j hj).parts := by
      clear hD hc heta hbias hmesh
      clear hchain hparentGeometry hfinalGeometry
      classical
      have hancestor (b : Nat) (hab : a <= b) (hb : b <= M)
          (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S)
          (heq : Q.place b i = Q.place b j) : Q.place a i = Q.place a j := by
        induction b, hab using Nat.le_induction with
        | base => exact heq
        | succ b hab ih =>
          apply ih (Nat.le_of_succ_le hb)
          rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
            Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
      have hfibre_disjoint {j j' : ι} (hne : j ≠ j') :
          Disjoint (Q.fibre a m j) (Q.fibre a m j') := by
        apply Finset.disjoint_left.mpr
        intro k hk hk'
        obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
        obtain ⟨i', hi', hi'k⟩ := Finset.mem_image.mp hk'
        obtain ⟨hiS, hij⟩ := Finset.mem_filter.mp hi
        obtain ⟨hiS', hij'⟩ := Finset.mem_filter.mp hi'
        exact hne (hij.symm.trans ((hancestor m ham hm i hiS i' hiS'
          (hik.trans hi'k.symm)).trans hij'))
      let parts := (Q.indexSet a).attach.biUnion (fun j => (F j.val j.property).parts)
      have hpart (J : Finset ι) (hJ : J ∈ parts) :
          ∃ j, ∃ hj : j ∈ Q.indexSet a, J ∈ (F j hj).parts := by
        obtain ⟨j, _, hjp⟩ := Finset.mem_biUnion.mp hJ
        exact ⟨j.val, j.property, hjp⟩
      have hsub : ∀ J ∈ parts, J <= Q.indexSet m := by
        intro J hJ k hk
        obtain ⟨j, hj, hJj⟩ := hpart J hJ
        obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp ((F j hj).subset hJj hk)
        exact hik ▸ Q.place_mem m hm i (Finset.mem_filter.mp hi).1
      have hexists : ∀ k ∈ Q.indexSet m, ∃ J ∈ parts, k ∈ J := by
        intro k hk
        obtain ⟨i, hi, hik⟩ := Q.place_surjective m hm k hk
        have hj : Q.place a i ∈ Q.indexSet a := Q.place_mem a (ham.trans hm) i hi
        have hkf : k ∈ Q.fibre a m (Q.place a i) :=
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hik⟩
        obtain ⟨J, hJ, hkJ⟩ := (F (Q.place a i) hj).exists_mem hkf
        exact ⟨J, Finset.mem_biUnion.mpr ⟨⟨Q.place a i, hj⟩, by simp, hJ⟩, hkJ⟩
      have hdisjoint : (parts : Set (Finset ι)).PairwiseDisjoint id := by
        intro J hJ J' hJ' hne
        obtain ⟨j, hj, hJj⟩ := hpart J hJ
        obtain ⟨j', hj', hJj'⟩ := hpart J' hJ'
        by_cases hjj : j = j'
        · subst j'
          exact (F j hj).disjoint hJj hJj' hne
        · exact (hfibre_disjoint hjj).mono ((F j hj).subset hJj) ((F j' hj').subset hJj')
      let P : Finpartition (Q.indexSet m) := Finpartition.ofExistsUnique parts hsub
        (by
          intro k hk
          obtain ⟨J, hJ, hkJ⟩ := hexists k hk
          refine ⟨J, ⟨hJ, hkJ⟩, ?_⟩
          intro J' hJ'
          by_contra hne
          exact Finset.disjoint_left.mp (hdisjoint hJ'.1 hJ hne) hJ'.2 hkJ)
        (by
          intro hJ
          obtain ⟨j, hj, hJj⟩ := hpart ∅ hJ
          exact Finset.not_nonempty_empty ((F j hj).nonempty_of_mem_parts hJj))
      refine ⟨P, ?_, hpart⟩
      intro j hj J hJ
      exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, by simp, hJ⟩
    let L : Nat := max (Nat.ceil (coverFibreConstant 3 3 512 * A1)) 1
    let A : ENNReal := ((16 * _root_.Tube.volume_le.C 3 * D ^ 5 /
      (Metric.lt_volume_convexHull.c 3 * c) : NNReal) : ENNReal)
    obtain ⟨K, deltaH, hK, hdH, hdH1, hkeep⟩ := hchain M C A0 A1 L Kprefix eta0
    have hevent := hfinalGeometry A (2 * L) ENNReal.coe_ne_top (by finiteness)
      K M heta hbias hmesh
    obtain ⟨eps, heps, hgeo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
    refine ⟨K, min deltaH eps, hK, lt_min hdH heps, (min_le_left _ _).trans hdH1, ?_⟩
    intro δ hd hd0 ι S T QB hQB Z hZT hfloor a m1 ham hm1 hpos hfinite hunif
      aw bw cw haw hawb hlong hecc F hDims
    have hdH' : δ < deltaH := hd0.trans_le (min_le_left _ _)
    have hd1 : δ <= 1 := hdH'.le.trans hdH1
    obtain ⟨p, parent, hap, hpm, hplace, hVP, hfibre, hupper, hlower,
      hcount, hdilate, hball, hvolume⟩ :=
      hparentGeometry QB hQB.geometry hd hd1 ham hm1 hD hc haw hawb hlong hecc F hDims
    obtain ⟨P, hlocal, hglobal⟩ := hglobalPartition QB ham.le hm1.le F
    have hgroups (I : Finset ι) (hI : I ∈ P.parts) : (I.image parent).card <= L := by
      obtain ⟨ja, hja, hI⟩ := hglobal I hI
      exact hcount ja hja I hI
    obtain ⟨H, R, QH, QR, pick, hHne, hRne, hrest, hfinal, hQH, hQR, hstats,
      hwhole, hparts, hglobalMass, hpaid, hparentMass, hfineRet⟩ :=
      hkeep δ hd hdH' S T QB hQB Z hZT hfloor p m1 hpm.le hm1.le P parent
        hgroups hplace hpos hfinite hunif
    have hrpos : 0 < sourceTowerRadius δ M m1 := by
      simp only [sourceTowerRadius, if_pos hm1]
      positivity
    have hrbound : sourceTowerRadius δ M m1 <= 1 := by
      simp only [sourceTowerRadius, if_pos hm1]
      calc
        (1 / 40 : NNReal) * δ ^ ((m1 : Real) / M) <= (1 / 40) * 1 := by
          gcongr
          exact NNReal.rpow_le_one hd1 (by positivity)
        _ <= 1 := by
          rw [mul_one]
          exact (div_le_iff₀ (by norm_num : (0 : NNReal) < 40)).mpr (by norm_num)
    have hindex (k : Nat) (hk : k <= M) : QH.indexSet k <= QB.indexSet k := by
      intro j hj
      obtain ⟨x, hx, hxj⟩ := QH.place_surjective k hk j hj
      rw [hrest.assignment] at hxj
      rw [← hxj]
      exact QB.place_mem k hk x (hrest.subset hx)
    have hgeometry := hgeo (show δ ∈ Set.Ioo 0 eps from
      ⟨hd, hd0.trans_le (min_le_right _ _)⟩) QB QH QR hrest hfinal hap hpm.le hm1.le F parent pick hplace
      (fun ja hja I hI => (hparts I (hlocal ja hja hI)).2.2.1)
      (fun ja hja I hI => by
        simpa only [hrest.tubes] using (hparts I (hlocal ja hja hI)).2.2.2.2)
      (fun i hi => (_root_.Tube.volume_pos_and_lt_top hrpos hrbound (QB.tube m1 i)).1)
      (fun i hi => (hVP i (hindex m1 hm1.le hi)).2)
      hdilate
      (fun j hj ja hja I hI => by
        simpa only [A, ENNReal.coe_rpow_of_ne_zero hd.ne'] using hvolume j ja hja I hI)
      hfineRet
    have hrestriction : SourceTowerRestriction QB QR := {
      subset := hfinal.subset.trans hrest.subset
      assignment := hfinal.assignment.trans hrest.assignment
      parent := hfinal.parent.trans hrest.parent
      tubes := hfinal.tubes.trans hrest.tubes
      occupied := by
        intro k hk
        rw [hfinal.occupied k hk]
        simp only [SourceThreadedTower.assignedFootprint, hrest.assignment]
      full_retained_fibres := by
        intro c d j
        rw [hfinal.full_retained_fibres]
        simp only [SourceThreadedTower.retainedAssignedFibre, hrest.assignment] }
    exact ⟨p, R, QR, hap, hpm, hRne, hrestriction, hQR, hstats, hpaid,
      hgeometry.1, hgeometry.2⟩
  obtain ⟨D, hD, hP⟩ := hPBranch M A0 A1 C hschedule.level_bound hC
  refine ⟨D, hD, ?_⟩
  intro bias hbias hbiasUpper
  obtain ⟨A, Kstage, Kp, hA, hKstage, hKp, hPeta⟩ := hP bias hbias
  obtain ⟨epsP, hepsP, hepsP1, hepsPM, hPrepare⟩ := hPeta 1 (by norm_num)
  let c : NNReal := Real.toNNReal (1 / (4 * Real.sqrt 3))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Kg, epsG, hKg, hepsG, hepsG1, hGeometryDelta⟩ :=
    hGeometry M C A0 A1 Kp 1 etaParent bias D c hD hc hschedule.parent_positive
      hbiasUpper hschedule.parent_mesh
  obtain ⟨epsFD, hepsFD, hepsFD1, hepsFDM, hContinue⟩ :=
    hFD N M J e eta etaParent hschedule
  obtain ⟨epsL, hepsL, hLeaf⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hLeafFloor (etaF := 1) (by norm_num))
  let K := max Kp Kg
  let delta0 := min epsP (min epsG (min epsFD epsL))
  refine ⟨1, K, delta0, by norm_num, by norm_num, hKp.trans (le_max_left _ _),
    lt_min hepsP (lt_min hepsG (lt_min hepsFD hepsL)),
    (min_le_left _ _).trans hepsP1, (min_le_left _ _).trans hepsPM, ?_⟩
  intro delta hd hsmall iota S T Q Z hinput hstats hfull a b hwindow
  have hdP : delta < epsP := hsmall.trans_le (min_le_left _ _)
  have hdG : delta < epsG := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdFD : delta < epsFD :=
    hsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdL : delta < epsL :=
    hsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hd1 : delta < 1 := hdP.trans_le hepsP1
  by_cases hex : ∃ m, SourceTowerWindow delta M e a b m
  · let window := (Finset.range M).filter (SourceTowerWindow delta M e a b)
    have hwindowNe : window.Nonempty := by
      obtain ⟨m, hm⟩ := hex
      exact ⟨m, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hm.2.1.trans_le hwindow.fine_bound), hm⟩⟩
    let m1 := window.max' hwindowNe
    have hm1 : SourceTowerWindow delta M e a b m1 :=
      (Finset.mem_filter.mp (window.max'_mem hwindowNe)).2
    have hmax : ∀ m, SourceTowerWindow delta M e a b m -> m <= m1 := by
      intro m hm
      exact Finset.le_max' window m (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hm.2.1.trans_le hwindow.fine_bound), hm⟩)
    have hmM : m1 < M := hm1.2.1.trans_le hwindow.fine_bound
    obtain ⟨G, QG, B, SB, QB, F, hQB, hUpperB, hPout⟩ :=
      hPrepare delta hd hdP S T Q Z hinput hstats hfull a b N J eta e etaParent hwindow m1 hm1
    by_cases hecc : F.short / F.middle <= delta ^ etaParent
    · exact ⟨SB, QB, Z, hLoss Q QB Z Z hd hd1.le (le_max_left Kp Kg) (hPout hecc)⟩
    have hfloor : ∀ i ∈ S, (delta : ENNReal) ^ (10 : Real) *
        volume (T i).carrier <= volume (Z i).shade :=
      hLeaf ⟨hd, hdL⟩ Q Z hinput.geometry.nonempty hstats hfull
    obtain ⟨hQB', hZT, hfloorB, hposB, hfiniteB, hunifB, hRestrict⟩ :=
      hBinInput Q QG QB Z B F hinput hstats hd hd1.le hm1.1 hmM hfloor
    have hnonEcc : delta ^ etaParent * F.middle <= F.short :=
      ((lt_div_iff₀ (F.short_positive.trans_le F.short_le_middle)).mp (lt_of_not_ge hecc)).le
    obtain ⟨p, R, QR, hap, hpm, hRne, hrestB, hQR, hStatsR, hpaid, hparent, hFrostman⟩ :=
      hGeometryDelta delta hd hdG QB hQB' Z hZT hfloorB a m1 hm1.1 hmM
        hposB hfiniteB hunifB F.short F.middle F.long F.short_positive F.short_le_middle
        F.long_lower hnonEcc F.factor F.dimensions
    have hrest : SourceTowerRestriction Q QR := hRestrict QR hrestB
    have hmass : (∑ i ∈ S, volume (Z i).shade) <=
        sourceFixedPreparationLoss Kg delta * ∑ i ∈ R, volume (Z i).shade :=
      F.retained.mass.trans hpaid
    have hretained := hRetained Q QR Z Z (sourceFixedPreparationLoss Kg delta)
      hrest hRne hstats.same_tubes hStatsR.same_tubes (fun _ => Set.Subset.rfl) hmass
    have hcontinue := hContinue delta hd hdFD Q QR Z hrest hRne hQR.geometry hStatsR
      a b hwindow m1 p hm1 hmax hap hpm hparent hFrostman
    have hout : SourceTerminalWindowOutcome Q Z R QR Z N J A0 A1 e eta
        etaParent bias 1 Kg D a b := {
      retained := hretained
      input := hQR
      upper := source_direct_upper_of_restriction Q QR hrest hwindow
      alternative := Or.inr ⟨hStatsR, hcontinue⟩ }
    exact ⟨R, QR, Z, hLoss Q QR Z Z hd hd1.le (le_max_right Kp Kg) hout⟩
  · exact ⟨S, Q, Z, hEmpty Q Z hd hd1 hschedule.parent_positive hinput hstats hwindow
      (fun m hm => hex ⟨m, hm⟩)⟩

end Kakeya.ML2Core
