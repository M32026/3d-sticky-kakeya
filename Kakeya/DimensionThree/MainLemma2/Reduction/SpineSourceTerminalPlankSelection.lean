/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceTerminalPlankData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- A whole m-cell selection preserves every surviving descendant cell at
finer levels. The assignment is the original named Q throughout. -/
theorem source_terminal_whole_cell_preserves_descendants
    (Q : SourceThreadedTower S T M C) {R : Finset iota}
    (QR : SourceThreadedTower R T M C) (hrest : SourceTowerRestriction Q QR)
    {m : Nat} (step : SourceWholeCellStep Q S R m) :
    forall k, m <= k -> k <= M -> forall j, j ∈ QR.indexSet k ->
      QR.cell k j = Q.cell k j := by
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
  obtain ⟨x, hx, hxj⟩ := QR.place_surjective k hk j hj
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

/-- Weighted count binning selects whole a-cells of the current family.
It establishes the a comparison and preserves the m comparison and every
old factor inside each retained a-cell, at one explicit dyadic price. -/
theorem source_exists_terminal_outer_count_bin
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {a m : Nat} (ham : a < m) (hmM : m <= M)
    (htubes : forall i, (Z i).toTube = T i)
    (hcounts : SourceTerminalDescendantCounts Q m)
    (hmass : 0 < ∑ i ∈ S, volume (Z i).shade) :
    exists (R : Finset iota) (QR : SourceThreadedTower R T M C),
      SourceTowerRestriction Q QR /\ R.Nonempty /\
      Nonempty (SourceWholeCellStep Q S R a) /\
      (∑ i ∈ S, volume (Z i).shade) <=
        (Kakeya.dyadicPigeonholeNatConstant S.card : ENNReal) *
          ∑ i ∈ R, volume (Z i).shade /\
      SourceTerminalPlankStatistics QR Z a m /\
      (forall k, a <= k -> k <= M -> forall j, j ∈ QR.indexSet k ->
        QR.cell k j = Q.cell k j) /\
      (forall j, j ∈ QR.indexSet a -> QR.fibre a m j = Q.fibre a m j) := by
  classical
  let w := fun i => volume (Z i).shade
  let f := fun i => (Q.cell a (Q.place a i)).card
  have hf : forall i, i ∈ S -> 1 <= f i ∧ f i <= S.card := by
    intro i hi
    exact ⟨Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩,
      Finset.card_filter_le _ _⟩
  obtain ⟨k, hk, hpaid⟩ := Nat.dyadic_pigeonhole_ennreal S w f hf
  let R := S.filter (fun i => 2 ^ k <= f i ∧ f i < 2 ^ (k + 1))
  have hRS : R <= S := Finset.filter_subset _ _
  have hRne : R.Nonempty := by
    by_contra h
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    change (∑ i ∈ S, w i) <= _ * ∑ i ∈ R, w i at hpaid
    simp only [he, Finset.sum_empty, mul_zero] at hpaid
    exact (not_le_of_gt hmass) hpaid
  have hwhole (j : iota) (hj : j ∈ Q.assignedFootprint R a) :
      R.filter (fun i => Q.place a i = j) = Q.cell a j := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
    have hxbin := (Finset.mem_filter.mp hx).2
    ext i
    simp only [Finset.mem_filter, SourceThreadedTower.cell]
    constructor
    · rintro ⟨hi, heq⟩
      exact ⟨hRS hi, heq⟩
    · rintro ⟨hi, heq⟩
      refine ⟨Finset.mem_filter.mpr ⟨hi, ?_⟩, heq⟩
      simpa only [f, heq] using hxbin
  have hleaves : R = S.filter (fun i => Q.place a i ∈ Q.assignedFootprint R a) := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_filter.mpr ⟨hRS hi, Finset.mem_image_of_mem _ hi⟩
    · intro hi
      have hj := (Finset.mem_filter.mp hi).2
      have hiCell : i ∈ Q.cell a (Q.place a i) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, rfl⟩
      rw [← hwhole (Q.place a i) hj] at hiCell
      exact (Finset.mem_filter.mp hiCell).1
  let step : SourceWholeCellStep Q S R a := {
    selected := Q.assignedFootprint R a
    selected_subset := Finset.image_subset_image hRS
    leaves_eq := hleaves
    complete := hwhole }
  have hocc (k : Nat) (hk : k <= M) : Q.assignedFootprint R k <= Q.indexSet k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Q.place_mem k hk i (hRS hi)
  let QR : SourceThreadedTower R T M C := {
    indexSet := Q.assignedFootprint R
    place := Q.place
    parent := Q.parent
    tube := Q.tube
    tube_injective := fun k hk i hi j hj => Q.tube_injective k hk (hocc k hk hi) (hocc k hk hj)
    place_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
    place_surjective := fun k _ j hj => Finset.mem_image.mp hj
    leaf_containment := fun k hk i hi => Q.leaf_containment k hk i (hRS hi)
    parent_mem := by
      intro k hk j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [← Q.parent_composition k hk i (hRS hi)]
      exact Finset.mem_image_of_mem _ hi
    parent_composition := fun k hk i hi => Q.parent_composition k hk i (hRS hi)
    parent_containment := fun k hk j hj => Q.parent_containment k hk j (hocc (k + 1) (by omega) hj)
    bottom_index := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
        rw [Q.bottom_place j (hRS hj)] at hji
        exact hji ▸ hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, Q.bottom_place i (hRS hi)⟩
    bottom_place := fun i hi => Q.bottom_place i (hRS hi)
    bottom_body := fun i hi => Q.bottom_body i (hRS hi)
    containment_multiplicity := by
      intro k hk i hi
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk))).trans
        (Q.containment_multiplicity k hk i (hRS hi)) }
  have hrest : SourceTowerRestriction Q QR := {
    subset := hRS
    assignment := rfl
    parent := rfl
    tubes := rfl
    occupied := fun _ _ => rfl
    full_retained_fibres := fun _ _ _ => rfl }
  have hpres := source_terminal_whole_cell_preserves_descendants Q QR hrest step
  refine ⟨R, QR, hrest, hRne, ⟨step⟩, hpaid, ⟨htubes, ?_, ?_⟩, hpres, ?_⟩
  · intro j hj j' hj'
    rw [hpres a le_rfl (ham.le.trans hmM) j hj,
      hpres a le_rfl (ham.le.trans hmM) j' hj']
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hj'
    have hleft := (Finset.mem_filter.mp hi).2.2
    have hright := (Finset.mem_filter.mp hi').2.1
    have hnat : f i <= 2 * f i' := by
      calc
        f i <= 2 ^ (k + 1) := hleft.le
        _ = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
        _ <= 2 * f i' := Nat.mul_le_mul_left _ hright
    exact_mod_cast hnat
  · intro j hj j' hj'
    rw [hpres m ham.le hmM j hj, hpres m ham.le hmM j' hj']
    exact hcounts j (hocc m hmM hj) j' (hocc m hmM hj')
  · intro j hj
    change (QR.cell a j).image (QR.place m) = (Q.cell a j).image (Q.place m)
    rw [hpres a le_rfl (ham.le.trans hmM) j hj]

set_option maxHeartbeats 8000000 in
/-- Actual dimension binning on whole B5 parts, followed by the preceding
a-cell bin. This creates the common dimensions before their eccentricity
is tested; it assumes neither a buffer nor retained fragments. -/
theorem source_exists_terminal_common_factor_bin
    (M A0 A1 C : Nat) (hM : 2 <= M) (hC : 1 <= C) :
    exists D : NNReal, 1 <= D /\
    forall bias : Real, 0 < bias ->
    forall (A : NNReal) (Kstage : Nat), 1 <= A -> 1 <= Kstage ->
    exists (K : Nat) (delta0 : NNReal),
      Kstage <= K /\ 1 <= K /\ 0 < delta0 /\ delta0 <= 1 /\
      delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
      (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
    forall Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)),
      (forall i, (Z i).toTube = T i) ->
      (forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) *
        volume (T i).carrier <= volume (Z i).shade) ->
    forall a m : Nat, a < m -> m < M -> SourceTerminalDescendantCounts Q m ->
    forall (G : Finset iota) (QG : SourceThreadedTower G T M C)
      (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage),
    exists (R : Finset iota) (QR : SourceThreadedTower R T M C),
      Nonempty (SourceTerminalCommonFactorBin Q Z B R QR D K) := by
  classical
  have hGlobal {iota : Type u} {delta : NNReal} {S G : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C a m : Nat}
      {bias : Real} {A : NNReal} {Kstage : Nat}
      (Q : SourceThreadedTower S T M C) (QG : SourceThreadedTower G T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (ham : a < m) (hm : m <= M)
      (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage) :
      exists P0 : Finpartition (QG.indexSet m),
        P0.parts = (Q.indexSet a).attach.biUnion (fun j => (B.factor j.val j.property).parts) ∧
        (forall part, part ∈ P0.parts -> exists j, exists hj : j ∈ Q.indexSet a,
          part ∈ (B.factor j hj).parts) ∧
        (∑ i ∈ G, volume (Z i).shade) =
          ∑ part ∈ P0.parts, ∑ i ∈ G.filter (fun i => Q.place m i ∈ part), volume (Z i).shade ∧
        (forall P, P <= P0.parts ->
          (∑ i ∈ G.filter (fun i => Q.place m i ∈ P.biUnion id), volume (Z i).shade) =
            ∑ part ∈ P, ∑ i ∈ G.filter (fun i => Q.place m i ∈ part), volume (Z i).shade) := by
    classical
    have hancestor (b : Nat) (hab : a <= b) (hb : b <= M)
        (i : iota) (hi : i ∈ G) (j : iota) (hj : j ∈ G)
        (heq : QG.place b i = QG.place b j) : QG.place a i = QG.place a j := by
      induction b, hab using Nat.le_induction with
      | base => exact heq
      | succ b hab ih =>
        apply ih (Nat.le_of_succ_le hb)
        rw [QG.parent_composition b (Nat.lt_of_succ_le hb) i hi,
          QG.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
    have hfibre_disjoint {j j' : iota} (hne : j ≠ j') :
        Disjoint (QG.fibre a m j) (QG.fibre a m j') := by
      apply Finset.disjoint_left.mpr
      intro k hk hk'
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
      obtain ⟨i', hi', hi'k⟩ := Finset.mem_image.mp hk'
      obtain ⟨hiG, hij⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiG', hij'⟩ := Finset.mem_filter.mp hi'
      exact hne (hij.symm.trans ((hancestor m ham.le hm i hiG i' hiG'
        (hik.trans hi'k.symm)).trans hij'))
    let parts := (Q.indexSet a).attach.biUnion (fun j => (B.factor j.val j.property).parts)
    have hpart (part : Finset iota) (hp : part ∈ parts) :
        exists j, exists hj : j ∈ Q.indexSet a, part ∈ (B.factor j hj).parts := by
      obtain ⟨j, _, hjp⟩ := Finset.mem_biUnion.mp hp
      exact ⟨j.val, j.property, hjp⟩
    have hsub : forall part, part ∈ parts -> part <= QG.indexSet m := by
      intro part hp k hk
      obtain ⟨j, hj, hpj⟩ := hpart part hp
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp ((B.factor j hj).subset hpj hk)
      exact hik ▸ QG.place_mem m hm i (Finset.mem_filter.mp hi).1
    have hexists : forall k, k ∈ QG.indexSet m -> exists part, part ∈ parts ∧ k ∈ part := by
      intro k hk
      obtain ⟨i, hi, hik⟩ := QG.place_surjective m hm k hk
      have hj : QG.place a i ∈ Q.indexSet a :=
        B.same_coarse ▸ QG.place_mem a (ham.le.trans hm) i hi
      have hkf : k ∈ QG.fibre a m (QG.place a i) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hik⟩
      obtain ⟨part, hp, hkp⟩ := (B.factor (QG.place a i) hj).exists_mem hkf
      exact ⟨part, Finset.mem_biUnion.mpr ⟨⟨QG.place a i, hj⟩, by simp, hp⟩, hkp⟩
    have hdisjoint : (parts : Set (Finset iota)).PairwiseDisjoint id := by
      intro part hp part' hp' hne
      obtain ⟨j, hj, hpj⟩ := hpart part hp
      obtain ⟨j', hj', hpj'⟩ := hpart part' hp'
      by_cases hjj : j = j'
      · subst j'
        exact (B.factor j hj).disjoint hpj hpj' hne
      · exact (hfibre_disjoint hjj).mono ((B.factor j hj).subset hpj)
          ((B.factor j' hj').subset hpj')
    let P0 : Finpartition (QG.indexSet m) := Finpartition.ofExistsUnique parts hsub
      (by
        intro k hk
        obtain ⟨part, hp, hkp⟩ := hexists k hk
        refine ⟨part, ⟨hp, hkp⟩, ?_⟩
        intro part' hp'
        by_contra hne
        exact Finset.disjoint_left.mp (hdisjoint hp'.1 hp hne) hp'.2 hkp)
      (by
        intro hp
        obtain ⟨j, hj, hpj⟩ := hpart ∅ hp
        exact Finset.not_nonempty_empty ((B.factor j hj).nonempty_of_mem_parts hpj))
    have hpreimage (P : Finset (Finset iota)) :
        G.filter (fun i => Q.place m i ∈ P.biUnion id) =
          P.biUnion (fun part => G.filter (fun i => Q.place m i ∈ part)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_biUnion, id_eq]
      aesop
    have hmass (P : Finset (Finset iota)) (hP : P <= P0.parts) :
        (∑ i ∈ G.filter (fun i => Q.place m i ∈ P.biUnion id), volume (Z i).shade) =
          ∑ part ∈ P, ∑ i ∈ G.filter (fun i => Q.place m i ∈ part), volume (Z i).shade := by
      rw [hpreimage P]
      apply Finset.sum_biUnion
      intro part hp part' hp' hne
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      exact Finset.disjoint_left.mp (P0.disjoint (hP hp) (hP hp') hne)
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
    refine ⟨P0, rfl, hpart, ?_, hmass⟩
    convert hmass P0.parts le_rfl using 2
    rw [P0.biUnion_parts]
    exact (Finset.filter_eq_self.mpr (by
      intro i hi
      rw [← B.restriction.assignment]
      exact QG.place_mem m hm i hi)).symm
  have hDimension {iota : Type u} {delta : NNReal} {S G : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C A0 A1 m : Nat}
      (Q : SourceThreadedTower S T M C) (QG : SourceThreadedTower G T M C)
      (hrest : SourceTowerRestriction Q QG) (hgeom : SourceTowerGeometry Q A0 A1)
      (hd : 0 < delta) (hd1 : delta <= 1) (hm : m < M)
      (P0 : Finpartition (QG.indexSet m)) (w : Finset iota -> ENNReal)
      (hmass : 0 < ∑ part ∈ P0.parts, w part) :
      exists (P : Finset (Finset iota)) (aw bw cw : NNReal),
        P <= P0.parts ∧ P.Nonempty ∧ 0 < aw ∧ aw <= bw ∧ bw <= cw ∧
        Real.toNNReal (1 / (4 * Real.sqrt 3)) <= cw ∧ cw <= 64 ∧
        (∑ part ∈ P0.parts, w part) <=
          ENNReal.ofReal (1 + Real.logb 2 (3 / (delta : Real))) ^ 3 * ∑ part ∈ P, w part ∧
        forall part, part ∈ P -> SourceZeroFactorDimensions 2 aw bw cw
          (part.convexHull_biUnion (fun k => (QG.tube m k).toConvexSpaceBody)) := by
    classical
    let W := fun part : Finset iota =>
      part.convexHull_biUnion (fun k => (QG.tube m k).toConvexSpaceBody)
    have hocc (k : Nat) (hk : k <= M) : QG.indexSet k <= Q.indexSet k := by
      intro j hj
      obtain ⟨i, hi, heq⟩ := QG.place_surjective k hk j hj
      rw [hrest.assignment] at heq
      exact heq ▸ Q.place_mem k hk i (hrest.subset hi)
    have hrange (part : Finset iota) (hp : part ∈ P0.parts) (k : Fin 3) :
        (delta : ENNReal) <= ethickness Real (W part).carrier k ∧
          ethickness Real (W part).carrier k <= 3 := by
      have hpne := P0.nonempty_of_mem_parts hp
      have hball : (W part).carrier <= Metric.closedBall 0 3 := by
        change (part.convexHull_biUnion (fun k => (QG.tube m k).toConvexSpaceBody)).carrier ⊆ _
        rw [hpne.convexHull_biUnion_subset_iff]
        · intro j hj
          change (QG.tube m j).carrier <= Metric.closedBall 0 3
          rw [hrest.tubes]
          exact hgeom.coarse_ball m hm j (hocc m hm.le (P0.subset hp hj))
        · exact (convex_closedBall 0 3).isConvexSet
      refine ⟨?_, ?_⟩
      · obtain ⟨j, hj⟩ := hpne
        obtain ⟨i, hi, hij⟩ := QG.place_surjective m hm.le j (P0.subset hp hj)
        have hbody : (T i).carrier <= (W part).carrier := by
          change (T i).toConvexSpaceBody <= W part
          have hleaf := QG.leaf_containment m hm.le i hi
          rw [hij] at hleaf
          exact hleaf.trans (Finset.le_convexHull_biUnion (fun k => (QG.tube m k).toConvexSpaceBody) hj)
        exact (T i).le_ethickness_scale.trans
          ((ethickness.scale_le (T i).carrier (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using k.isLt)).trans
            (ethickness_monotone hbody k))
      · exact ethickness_le_of_subset_closedBall (𝕜 := Real) 3 hball k
    have hlong (part : Finset iota) (hp : part ∈ P0.parts) :
        (1 / 2 : ENNReal) <= ethickness Real (W part).carrier 0 := by
      obtain ⟨j, hj⟩ := P0.nonempty_of_mem_parts hp
      have hbody : (QG.tube m j).carrier <= (W part).carrier :=
        Finset.le_convexHull_biUnion (fun k => (QG.tube m k).toConvexSpaceBody) hj
      exact (QG.tube m j).le_ethickness_zero.trans (ethickness_monotone hbody 0)
    obtain ⟨P, hP, hpaid, hdim⟩ := ENNReal.dyadic_pigeonhole P0.parts w
      (fun part (k : Fin 3) => ethickness Real (W part).carrier k)
      (show (0 : Real) < delta by exact_mod_cast hd)
      (show (delta : Real) <= 3 by exact_mod_cast hd1.trans (by norm_num : (1 : NNReal) <= 3))
      (by
        intro part hp
        simpa only [Set.mem_Icc, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat,
          Function.const_apply, Pi.le_def] using
          And.intro (fun k => (hrange part hp k).1) (fun k => (hrange part hp k).2))
    have hPne : P.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, mul_zero] at hpaid
      exact not_le_of_gt hmass hpaid
    obtain ⟨part0, hp0⟩ := hPne.exists_mem
    let aw := (ethickness Real (W part0).carrier 2).toNNReal
    let bw := (ethickness Real (W part0).carrier 1).toNNReal
    let cw := (ethickness Real (W part0).carrier 0).toNNReal
    have hfinite (part : Finset iota) (hp : part ∈ P0.parts) (k : Fin 3) :
        ethickness Real (W part).carrier k ≠ ⊤ :=
      ne_top_of_le_ne_top (by norm_num : (3 : ENNReal) ≠ ⊤) (hrange part hp k).2
    have haw : (aw : ENNReal) = ethickness Real (W part0).carrier 2 :=
      ENNReal.coe_toNNReal (hfinite part0 (hP hp0) 2)
    have hbw : (bw : ENNReal) = ethickness Real (W part0).carrier 1 :=
      ENNReal.coe_toNNReal (hfinite part0 (hP hp0) 1)
    have hcw : (cw : ENNReal) = ethickness Real (W part0).carrier 0 :=
      ENNReal.coe_toNNReal (hfinite part0 (hP hp0) 0)
    have haw0 : 0 < aw := by
      apply ENNReal.coe_pos.mp
      rw [haw]
      exact (show (0 : ENNReal) < delta by exact_mod_cast hd).trans_le
        (hrange part0 (hP hp0) 2).1
    have hawbw : aw <= bw := by
      apply ENNReal.coe_le_coe.mp
      rw [haw, hbw]
      exact ethickness_antitone (by norm_num : 1 <= (2 : Nat))
    have hbwcw : bw <= cw := by
      apply ENNReal.coe_le_coe.mp
      rw [hbw, hcw]
      exact ethickness_antitone (by norm_num : 0 <= (1 : Nat))
    have hcwlo : (1 / 2 : NNReal) <= cw := by
      have hh := hlong part0 (hP hp0)
      rw [← hcw] at hh
      apply ENNReal.coe_le_coe.mp
      rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
      exact hh
    have hcwup : cw <= 3 := by
      have hh := (hrange part0 (hP hp0) 0).2
      change ethickness Real (W part0).carrier 0 <= 3 at hh
      rw [← hcw] at hh
      exact_mod_cast hh
    have hlo : Real.toNNReal (1 / (4 * Real.sqrt 3)) <= (1 / 2 : NNReal) := by
      have hreal : (1 / (4 * Real.sqrt 3) : Real) <= 1 / 2 := by
        have hs : 1 <= Real.sqrt 3 := by
          have hsq := Real.sq_sqrt (show (0 : Real) <= 3 by norm_num)
          nlinarith [Real.sqrt_nonneg 3]
        apply (div_le_div_iff₀ (by positivity : (0 : Real) < 4 * Real.sqrt 3)
          (by norm_num : (0 : Real) < 2)).mpr
        nlinarith
      rw [Real.toNNReal_le_iff_le_coe]
      exact hreal
    refine ⟨P, aw, bw, cw, hP, hPne, haw0, hawbw, hbwcw,
      hlo.trans hcwlo, hcwup.trans (by norm_num), hpaid, ?_⟩
    intro part hp
    have hlower (k : Fin 3) :
        (2 : ENNReal)⁻¹ * ethickness Real (W part0).carrier k <=
          ethickness Real (W part).carrier k := by
      apply (ENNReal.inv_mul_le_iff (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)).mpr
      simpa only [Pi.smul_apply, smul_eq_mul] using hdim part0 hp0 part hp k
    have hupper (k : Fin 3) : ethickness Real (W part).carrier k <=
        (2 : ENNReal) * ethickness Real (W part0).carrier k := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hdim part hp part0 hp0 k
    change (2 : ENNReal)⁻¹ * cw <= _ ∧ _ <= (2 : ENNReal) * cw ∧
      (2 : ENNReal)⁻¹ * bw <= _ ∧ _ <= (2 : ENNReal) * bw ∧
      (2 : ENNReal)⁻¹ * aw <= _ ∧ _ <= (2 : ENNReal) * aw
    rw [haw, hbw, hcw]
    exact ⟨hlower 0, hupper 0, hlower 1, hupper 1, hlower 2, hupper 2⟩
  have hPartTower {iota : Type u} {delta : NNReal} {S G : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C a m : Nat}
      {bias : Real} {A : NNReal} {Kstage : Nat}
      (Q : SourceThreadedTower S T M C) (QG : SourceThreadedTower G T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (ham : a < m) (hm : m <= M)
      (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage)
      (P0 : Finpartition (QG.indexSet m))
      (hlocal : forall j, forall hj : j ∈ Q.indexSet a, (B.factor j hj).parts <= P0.parts)
      (P : Finset (Finset iota)) (hP : P <= P0.parts) (hPne : P.Nonempty) :
      exists (Gp : Finset iota) (Qp : SourceThreadedTower Gp T M C),
        Gp = G.filter (fun i => Q.place m i ∈ P.biUnion id) ∧
        SourceTowerRestriction QG Qp ∧ Gp.Nonempty ∧
        Nonempty (SourceWholeCellStep Q G Gp m) ∧
        (forall k, m <= k -> k <= M -> forall j, j ∈ Qp.indexSet k ->
          Qp.cell k j = Q.cell k j) ∧
        (forall j, forall hj : j ∈ Q.indexSet a,
          Qp.fibre a m j = ((B.factor j hj).parts ∩ P).biUnion id) := by
    classical
    let selected := P.biUnion id
    let Gp := G.filter (fun i => Q.place m i ∈ selected)
    have hGpG : Gp <= G := Finset.filter_subset _ _
    have hselected : selected <= QG.indexSet m := by
      intro k hk
      obtain ⟨part, hp, hkp⟩ := Finset.mem_biUnion.mp hk
      exact P0.subset (hP hp) hkp
    have hselFoot : selected <= Q.assignedFootprint G m := by
      intro k hk
      obtain ⟨i, hi, hik⟩ := QG.place_surjective m hm k (hselected hk)
      exact Finset.mem_image.mpr ⟨i, hi, by simpa only [B.restriction.assignment] using hik⟩
    have hGpne : Gp.Nonempty := by
      obtain ⟨part, hp⟩ := hPne
      obtain ⟨k, hk⟩ := P0.nonempty_of_mem_parts (hP hp)
      obtain ⟨i, hi, hik⟩ := QG.place_surjective m hm k (P0.subset (hP hp) hk)
      refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
      rw [B.restriction.assignment] at hik
      rw [hik]
      exact Finset.mem_biUnion.mpr ⟨part, hp, hk⟩
    let step : SourceWholeCellStep Q G Gp m := {
      selected := selected
      selected_subset := hselFoot
      leaves_eq := rfl
      complete := by
        intro j hj
        ext i
        simp only [Gp, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hi, _⟩, heq⟩
          exact ⟨hi, heq⟩
        · rintro ⟨hi, heq⟩
          exact ⟨⟨hi, heq ▸ hj⟩, heq⟩ }
    have hocc (k : Nat) (hk : k <= M) : QG.assignedFootprint Gp k <= QG.indexSet k := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact QG.place_mem k hk i (hGpG hi)
    let Qp : SourceThreadedTower Gp T M C := {
      indexSet := QG.assignedFootprint Gp
      place := QG.place
      parent := QG.parent
      tube := QG.tube
      tube_injective := fun k hk i hi j hj => QG.tube_injective k hk (hocc k hk hi) (hocc k hk hj)
      place_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
      place_surjective := fun k _ j hj => Finset.mem_image.mp hj
      leaf_containment := fun k hk i hi => QG.leaf_containment k hk i (hGpG hi)
      parent_mem := by
        intro k hk j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        rw [← QG.parent_composition k hk i (hGpG hi)]
        exact Finset.mem_image_of_mem _ hi
      parent_composition := fun k hk i hi => QG.parent_composition k hk i (hGpG hi)
      parent_containment := fun k hk j hj => QG.parent_containment k hk j
        (hocc (k + 1) (by omega) hj)
      bottom_index := by
        ext i
        constructor
        · intro hi
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
          rw [QG.bottom_place j (hGpG hj)] at hji
          exact hji ▸ hj
        · intro hi
          exact Finset.mem_image.mpr ⟨i, hi, QG.bottom_place i (hGpG hi)⟩
      bottom_place := fun i hi => QG.bottom_place i (hGpG hi)
      bottom_body := fun i hi => QG.bottom_body i (hGpG hi)
      containment_multiplicity := by
        intro k hk i hi
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk))).trans
          (QG.containment_multiplicity k hk i (hGpG hi)) }
    have hrest : SourceTowerRestriction QG Qp := {
      subset := hGpG
      assignment := rfl
      parent := rfl
      tubes := rfl
      occupied := fun _ _ => rfl
      full_retained_fibres := fun _ _ _ => rfl }
    have stepG : SourceWholeCellStep QG G Gp m := {
      selected := selected
      selected_subset := by simpa only [SourceThreadedTower.assignedFootprint,
        B.restriction.assignment] using hselFoot
      leaves_eq := by simpa only [B.restriction.assignment] using step.leaves_eq
      complete := by simpa only [B.restriction.assignment] using step.complete }
    refine ⟨Gp, Qp, rfl, hrest, hGpne, ⟨step⟩, ?_, ?_⟩
    · intro k hmk hk j hj
      rw [source_terminal_whole_cell_preserves_descendants QG Qp hrest stepG k hmk hk j hj]
      exact source_terminal_whole_cell_preserves_descendants Q QG B.restriction B.whole_cell
        k hmk hk j (hocc k hk hj)
    · intro j hj
      ext k
      constructor
      · intro hk
        obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
        obtain ⟨hiGp, hij⟩ := Finset.mem_filter.mp hi
        have hisel := (Finset.mem_filter.mp hiGp).2
        change QG.place m i = k at hik
        rw [B.restriction.assignment] at hik
        rw [hik] at hisel
        obtain ⟨part, hp, hkp⟩ := Finset.mem_biUnion.mp hisel
        have hkf : k ∈ QG.fibre a m j :=
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hGpG hiGp, hij⟩,
            by simpa only [B.restriction.assignment] using hik⟩
        obtain ⟨part', hp', hkp'⟩ := (B.factor j hj).exists_mem hkf
        have heq := P0.eq_of_mem_parts (hP hp) (hlocal j hj hp') hkp hkp'
        exact Finset.mem_biUnion.mpr ⟨part, Finset.mem_inter.mpr ⟨heq ▸ hp', hp⟩, hkp⟩
      · intro hk
        obtain ⟨part, hp, hkp⟩ := Finset.mem_biUnion.mp hk
        obtain ⟨hpj, hpP⟩ := Finset.mem_inter.mp hp
        have hkf := (B.factor j hj).subset hpj hkp
        obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hkf
        obtain ⟨hiG, hij⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨?_, hij⟩, hik⟩
        refine Finset.mem_filter.mpr ⟨hiG, ?_⟩
        rw [B.restriction.assignment] at hik
        rw [hik]
        exact Finset.mem_biUnion.mpr ⟨part, hpP, hkp⟩
  have hAssembly {iota : Type u} {delta : NNReal} {S G Gp : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C a m K : Nat}
      {bias : Real} {A D aw bw cw : NNReal} {Kstage : Nat}
      (Q : SourceThreadedTower S T M C) (QG : SourceThreadedTower G T M C)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
      (ham : a < m) (hm : m <= M)
      (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage)
      (hcounts : SourceTerminalDescendantCounts Q m)
      (Qp : SourceThreadedTower Gp T M C) (hrestp : SourceTowerRestriction QG Qp)
      (hGpne : Gp.Nonempty) (step : SourceWholeCellStep Q G Gp m)
      (hcells : forall k, m <= k -> k <= M -> forall j, j ∈ Qp.indexSet k ->
        Qp.cell k j = Q.cell k j)
      (kept : forall j, j ∈ Q.indexSet a -> Finset (Finset iota))
      (hkept : forall j, forall hj : j ∈ Q.indexSet a, kept j hj <= (B.factor j hj).parts)
      (hfib : forall j, forall hj : j ∈ Q.indexSet a, Qp.fibre a m j = (kept j hj).biUnion id)
      (hD : 1 <= D) (haw : 0 < aw) (hab : aw <= bw) (hbc : bw <= cw)
      (hclo : Real.toNNReal (1 / (4 * Real.sqrt 3)) <= cw) (hchi : cw <= 64)
      (hdim : forall j, forall hj : j ∈ Q.indexSet a,
        forall part, part ∈ kept j hj -> SourceZeroFactorDimensions D aw bw cw
          (part.convexHull_biUnion (fun k => (QG.tube m k).toConvexSpaceBody)))
      (hcoeff : B.C0 <= sourceParentPlankConstant delta bias)
      (L : ENNReal) (hL : 1 <= L) (hLt : L < ⊤)
      (hpaid : (∑ i ∈ G, volume (Z i).shade) <= L * ∑ i ∈ Gp, volume (Z i).shade)
      (hpos : 0 < ∑ i ∈ Gp, volume (Z i).shade)
      (hbudget : B.stageLoss * L * (Kakeya.dyadicPigeonholeNatConstant Gp.card : ENNReal) <=
        sourceFixedPreparationLoss K delta) :
      exists (R : Finset iota) (QR : SourceThreadedTower R T M C),
        Nonempty (SourceTerminalCommonFactorBin Q Z B R QR D K) := by
    classical
    have hassp : Qp.place = Q.place := hrestp.assignment.trans B.restriction.assignment
    have hsubp : Gp <= S := hrestp.subset.trans B.restriction.subset
    have hocc (k : Nat) (hk : k <= M) : Qp.indexSet k <= Q.indexSet k := by
      intro j hj
      obtain ⟨i, hi, hij⟩ := Qp.place_surjective k hk j hj
      rw [hassp] at hij
      exact hij ▸ Q.place_mem k hk i (hsubp hi)
    have hcountsp : SourceTerminalDescendantCounts Qp m := by
      intro j hj j' hj'
      rw [hcells m le_rfl hm j hj, hcells m le_rfl hm j' hj']
      exact hcounts j (hocc m hm hj) j' (hocc m hm hj')
    obtain ⟨R, QR, hrest, hRne, ⟨outer⟩, hmass, hstats, hpres, hfibre⟩ :=
      source_exists_terminal_outer_count_bin Qp Z ham hm B.same_tubes hcountsp hpos
    have hsub : R <= S := hrest.subset.trans hsubp
    have hass : QR.place = Q.place := hrest.assignment.trans hassp
    have htubes : QR.tube = QG.tube := hrest.tubes.trans hrestp.tubes
    have hcoarse (j : iota) (hj : j ∈ QR.indexSet a) : j ∈ Q.indexSet a := by
      obtain ⟨i, hi, hij⟩ := QR.place_surjective a (ham.le.trans hm) j hj
      rw [hass] at hij
      exact hij ▸ Q.place_mem a (ham.le.trans hm) i (hsub hi)
    have hrestQ : SourceTowerRestriction Q QR := {
      subset := hsub
      assignment := hass
      parent := hrest.parent.trans (hrestp.parent.trans B.restriction.parent)
      tubes := htubes.trans B.restriction.tubes
      occupied := by
        intro k hk
        rw [hrest.occupied k hk]
        simp only [SourceThreadedTower.assignedFootprint, hassp]
      full_retained_fibres := by
        intro x y j
        simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell,
          SourceThreadedTower.retainedAssignedFibre, hass] }
    have hfactor : forall j, forall hj : j ∈ QR.indexSet a,
        exists F : Factorization (QR.fibre a m j)
            (fun k => (QR.tube m k).toConvexSpaceBody) (sourceParentPlankConstant delta bias),
          F.parts = kept j (hcoarse j hj) := by
      intro j hj
      rw [htubes]
      have heq : (kept j (hcoarse j hj)).sup id = QR.fibre a m j := by
        rw [Finset.sup_eq_biUnion]
        exact ((hfibre j hj).trans (hfib j (hcoarse j hj))).symm
      let F0 := (B.factor j (hcoarse j hj)).ofSubsetParts (hkept j (hcoarse j hj)) heq
      let F : Factorization (QR.fibre a m j)
          (fun k => (QG.tube m k).toConvexSpaceBody) (sourceParentPlankConstant delta bias) := {
        toFinpartition := F0.toFinpartition
        isKatzTao := F0.isKatzTao.trans (ENNReal.coe_le_coe.mpr hcoeff)
        maxDensity_le_mul := by
          intro part hp
          exact (F0.maxDensity_le_mul part hp).trans
            (mul_le_mul_left (ENNReal.coe_le_coe.mpr hcoeff) _)
        simDims := by
          intro part hp part' hp' k
          exact (F0.simDims part hp part' hp' k).trans
            (mul_le_mul_left (ENNReal.coe_le_coe.mpr hcoeff) _) }
      exact ⟨F, Factorization.ofSubsetParts_parts _ _ _⟩
    choose factors hparts using hfactor
    let Lout : ENNReal := Kakeya.dyadicPigeonholeNatConstant Gp.card
    have hLout : 1 <= Lout := by
      change 1 <= (Kakeya.dyadicPigeonholeNatConstant Gp.card : ENNReal)
      exact_mod_cast (show 1 <= Kakeya.dyadicPigeonholeNatConstant Gp.card by
        unfold Kakeya.dyadicPigeonholeNatConstant
        omega)
    have hLoutt : Lout < ⊤ := ENNReal.natCast_lt_top _
    have hsuffix : (∑ i ∈ G, volume (Z i).shade) <=
        (L * Lout) * ∑ i ∈ R, volume (Z i).shade := by
      calc
        _ <= L * ∑ i ∈ Gp, volume (Z i).shade := hpaid
        _ <= L * (Lout * ∑ i ∈ R, volume (Z i).shade) := mul_le_mul_right hmass _
        _ = _ := (mul_assoc _ _ _).symm
    have htotal : (∑ i ∈ S, volume (Z i).shade) <=
        sourceFixedPreparationLoss K delta * ∑ i ∈ R, volume (Z i).shade := by
      calc
        _ <= B.stageLoss * ∑ i ∈ G, volume (Z i).shade := B.mass
        _ <= B.stageLoss * ((L * Lout) * ∑ i ∈ R, volume (Z i).shade) :=
          mul_le_mul_right hsuffix _
        _ = (B.stageLoss * L * Lout) * ∑ i ∈ R, volume (Z i).shade := by ring
        _ <= _ := mul_le_mul_left hbudget _
    let cellStage : SourceDirectPlankCellStage Q Z R Z m K := {
      before := S
      after := G
      before_subset := le_rfl
      before_nonempty := B.before_nonempty
      after_nonempty := B.after_nonempty
      selected := B.whole_cell
      final_subset := hrest.subset.trans hrestp.subset
      stageShade := Z
      same_tubes := B.same_tubes
      subshade := fun _ => le_rfl
      final_subshade := fun _ => le_rfl
      prefixLoss := 1
      stageLoss := B.stageLoss
      suffixLoss := L * Lout
      prefix_one := le_rfl
      loss_one := B.loss_one
      suffix_one := one_le_mul hL hLout
      prefix_finite := by norm_num
      loss_finite := B.loss_finite
      suffix_finite := ENNReal.mul_lt_top hLt hLoutt
      prefix_paid := by simp only [one_mul, le_refl]
      stage_paid := B.mass
      suffix_paid := hsuffix
      total_loss := by simpa only [one_mul, ← mul_assoc] using hbudget }
    refine ⟨R, QR, ⟨{
      partFamily := Gp
      partTower := Qp
      part_restriction := hrestp
      part_nonempty := hGpne
      part_step := step
      kept := kept
      kept_subset := hkept
      part_fibres := hfib
      final_restriction := hrest
      outer_step := {
        selected := outer.selected
        selected_subset := by simpa only [SourceThreadedTower.assignedFootprint, hassp]
          using outer.selected_subset
        leaves_eq := by simpa only [hassp] using outer.leaves_eq
        complete := by simpa only [hassp] using outer.complete }
      nonempty := hRne
      coarse_origin := hcoarse
      middle_cells := ?_
      statistics := hstats
      short := aw
      middle := bw
      long := cw
      comparison_one := hD
      short_positive := haw
      short_le_middle := hab
      middle_le_long := hbc
      long_lower := hclo
      long_upper := hchi
      factor := factors
      factor_parts := hparts
      dimensions := ?_
      retained := {
        restriction := hrestQ
        nonempty := hRne
        original_tubes := B.same_tubes
        same_tubes := B.same_tubes
        subshade := fun _ => le_rfl
        mass := htotal
        fullness := ?_
        multiplicity := ?_ }
      cell_stage := cellStage
      stage_before := rfl
      stage_after := rfl
      stage_shading := rfl
      part_loss := L
      outer_loss := Lout
      part_loss_one := hL
      outer_loss_one := hLout
      part_loss_finite := hLt
      outer_loss_finite := hLoutt
      part_mass := hpaid
      outer_mass := hmass
      total_loss := hbudget }⟩⟩
    · intro j hj
      rw [hpres m ham.le hm j hj]
      have hjp : j ∈ Qp.indexSet m := by
        obtain ⟨i, hi, hij⟩ := QR.place_surjective m hm j hj
        rw [hrest.assignment] at hij
        exact hij ▸ Qp.place_mem m hm i (hrest.subset hi)
      exact hcells m le_rfl hm j hjp
    · intro j hj part hp
      rw [htubes]
      rw [hparts] at hp
      exact hdim j (hcoarse j hj) part hp
    · change (∑ i ∈ S, volume (Z i).shade) / _ <=
        sourceFixedPreparationLoss K delta * ((∑ i ∈ R, volume (Z i).shade) / _)
      rw [← mul_div_assoc]
      exact ENNReal.div_le_div htotal (Finset.sum_le_sum_of_subset hsub)
    · rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, ← mul_div_assoc]
      apply ENNReal.div_le_div htotal
      exact measure_mono (Set.iUnion₂_subset fun i hi =>
        Set.subset_iUnion₂_of_subset i (hsub hi) le_rfl)
  have hCard {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C A0 A1 : Nat}
      (Q : SourceThreadedTower S T M C) (hgeom : SourceTowerGeometry Q A0 A1)
      (hd : 0 < delta) (hd1 : delta <= 1) :
      (S.card : Real) <= (4 * 2000 ^ 6 * (A0 + 1) : Real) * (1 / (delta : Real)) ^ 6 := by
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
  have hLoss (H : Real) (hH : 1 <= H) (Kstage : Nat) :
      exists K : Nat, Kstage <= K ∧
        forall delta : NNReal, 0 < delta -> delta <= 1 ->
        forall n : Nat, (n : Real) <= H * (1 / (delta : Real)) ^ 6 ->
          sourceFixedPreparationLoss Kstage delta *
            (ENNReal.ofReal (1 + Real.logb 2 (3 / (delta : Real))) ^ 3) *
              (Kakeya.dyadicPigeonholeNatConstant n : ENNReal) <= sourceFixedPreparationLoss K delta := by
    let C : Real := 8 + |Real.logb 2 H|
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (27 * C) (by norm_num : (1 : Real) < 2)
    refine ⟨Kstage + 4 + N, by omega, ?_⟩
    intro delta hd hd1 n hn
    have hdr : (0 : Real) < delta := by exact_mod_cast hd
    have hd1r : (delta : Real) <= 1 := by exact_mod_cast hd1
    let y : Real := 1 / (delta : Real)
    let x : Real := 2 + Real.logb 2 y
    have hy : 1 <= y := (le_div_iff₀ hdr).mpr (by simpa using hd1r)
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hlog : 0 <= Real.logb 2 y := Real.logb_nonneg (by norm_num) hy
    have hx : 2 <= x := by dsimp [x]; linarith
    have hC : 8 <= C := by dsimp [C]; linarith [abs_nonneg (Real.logb 2 H)]
    have hH0 : 0 < H := zero_lt_one.trans_le hH
    have houter : (Kakeya.dyadicPigeonholeNatConstant n : Real) <= C * x := by
      unfold Kakeya.dyadicPigeonholeNatConstant
      rw [Nat.cast_add, Nat.cast_one]
      by_cases hn0 : n = 0
      · simp only [hn0, Nat.log_zero_right, Nat.cast_zero, zero_add]
        nlinarith
      · have hnpos : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        have hh := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2) hnpos hn
        rw [Real.logb_mul hH0.ne' (pow_pos hy0 6).ne', Real.logb_pow] at hh
        have hlogn := Real.natLog_le_logb n 2
        norm_num only [Nat.cast_ofNat] at hlogn hh
        have habs := le_abs_self (Real.logb 2 H)
        dsimp [C, x]
        nlinarith [mul_nonneg (abs_nonneg (Real.logb 2 H)) hlog]
    have hlog3 : Real.logb 2 3 <= 2 := by
      apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : Real) < 2)
        (by norm_num : (0 : Real) < 3)).mpr
      norm_num
    have hdim0 : 0 <= 1 + Real.logb 2 (3 / (delta : Real)) := by
      have hh : 1 <= (3 : Real) / delta := (le_div_iff₀ hdr).mpr (by linarith)
      linarith [Real.logb_nonneg (by norm_num : (1 : Real) < 2) hh]
    have hdim : 1 + Real.logb 2 (3 / (delta : Real)) <= 3 * x := by
      rw [show (3 : Real) / delta = 3 * y by dsimp [y]; ring,
        Real.logb_mul (by norm_num : (3 : Real) ≠ 0) hy0.ne']
      dsimp [x]
      linarith
    have houterE : (Kakeya.dyadicPigeonholeNatConstant n : ENNReal) <= ENNReal.ofReal (C * x) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal houter
    have hreal : x ^ Kstage * (3 * x) ^ 3 * (C * x) <= x ^ (Kstage + 4 + N) := by
      calc
        _ = (27 * C) * x ^ (Kstage + 4) := by rw [pow_add]; ring
        _ <= x ^ N * x ^ (Kstage + 4) := by
          apply mul_le_mul_of_nonneg_right
            (hN.le.trans (pow_le_pow_left₀ (by norm_num) hx N))
          positivity
        _ = _ := by rw [pow_add]; ring
    change ENNReal.ofReal (x ^ Kstage) *
        ENNReal.ofReal (1 + Real.logb 2 (3 / (delta : Real))) ^ 3 *
          (Kakeya.dyadicPigeonholeNatConstant n : ENNReal) <=
        ENNReal.ofReal (x ^ (Kstage + 4 + N))
    calc
      _ <= ENNReal.ofReal (x ^ Kstage) * ENNReal.ofReal (3 * x) ^ 3 * ENNReal.ofReal (C * x) := by
        gcongr
      _ = ENNReal.ofReal (x ^ Kstage * (3 * x) ^ 3 * (C * x)) := by
        rw [← ENNReal.ofReal_pow (by positivity : 0 <= 3 * x),
          ← ENNReal.ofReal_mul (by positivity : 0 <= x ^ Kstage),
          ← ENNReal.ofReal_mul (by positivity : 0 <= x ^ Kstage * (3 * x) ^ 3)]
      _ <= _ := ENNReal.ofReal_le_ofReal hreal
  have hCoefficient (A : NNReal) {bias : Real} (hbias : 0 < bias) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        A * delta ^ (-4 * (bias / 16)) <= sourceParentPlankConstant delta bias := by
    have hc : (1 : NNReal) <= Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6) := by
      apply (Real.le_toNNReal_iff_coe_le (by positivity)).mpr
      have hp : (1 : Real) <= (3 : Real) ^ ((9 : Real) / 2) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      norm_num only [NNReal.coe_one]
      nlinarith
    filter_upwards [Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg A hbias,
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hA hd
    calc
      A * delta ^ (-4 * (bias / 16)) <= delta ^ (-bias) * delta ^ (-4 * (bias / 16)) := by gcongr
      _ = delta ^ (-bias + -4 * (bias / 16)) := (NNReal.rpow_add hd.1.ne' _ _).symm
      _ <= delta ^ (-3 * bias) := NNReal.rpow_le_rpow_of_exponent_ge hd.1 hd.2.le (by linarith)
      _ <= _ := by
        unfold sourceParentPlankConstant
        exact le_mul_of_one_le_left' hc
  refine ⟨2, by norm_num, ?_⟩
  intro bias hbias A Kstage hA hKstage
  have hH : (1 : Real) <= 4 * 2000 ^ 6 * (A0 + 1) := by
    have hA0 : (0 : Real) <= A0 := Nat.cast_nonneg _
    nlinarith
  obtain ⟨K, hK, hLossBound⟩ := hLoss (4 * 2000 ^ 6 * (A0 + 1)) hH Kstage
  obtain ⟨eps, heps, hcoeff⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hCoefficient A hbias)
  let cap : NNReal := (400 : NNReal) ^ (-(M : Real))
  have hcap : 0 < cap := by positivity
  refine ⟨K, min eps (min 1 cap), hK, hKstage.trans hK,
    lt_min heps (lt_min zero_lt_one hcap),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro delta hd hsmall iota S T Q hgeom Z hZT hfloor a m ham hm hcounts G QG B
  have hd1 : delta <= 1 := hsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcoeff' : B.C0 <= sourceParentPlankConstant delta bias :=
    B.coefficient_bound.trans (hcoeff ⟨hd, hsmall.trans_le (min_le_left _ _)⟩)
  have hshade : forall i, i ∈ S -> 0 < volume (Z i).shade := by
    intro i hi
    have hv : 0 < volume (T i).carrier := by
      refine lt_of_lt_of_le ?_ (Tube.le_volume (T i))
      have hc := Tube.le_volume.c_pos (Module.finrank Real (EuclideanSpace Real (Fin 3)))
      positivity
    exact (ENNReal.mul_pos (by positivity) hv.ne').trans_le (hfloor i hi)
  have hGpos : 0 < ∑ i ∈ G, volume (Z i).shade := by
    obtain ⟨i, hi⟩ := B.after_nonempty
    exact (hshade i (B.restriction.subset hi)).trans_le
      (Finset.single_le_sum (f := fun i => volume (Z i).shade) (fun _ _ => zero_le) hi)
  obtain ⟨P0, hP0, hOrigin, hmassTotal, hmassSelected⟩ := hGlobal Q QG Z ham hm.le B
  let weight := fun part : Finset iota =>
    ∑ i ∈ G.filter (fun i => Q.place m i ∈ part), volume (Z i).shade
  have hweight : 0 < ∑ part ∈ P0.parts, weight part := by
    change 0 < ∑ part ∈ P0.parts, ∑ i ∈ G.filter (fun i => Q.place m i ∈ part), volume (Z i).shade
    rw [← hmassTotal]
    exact hGpos
  obtain ⟨P, aw, bw, cw, hP, hPne, haw, hab, hbc, hclo, hchi, hpaidBin, hdims⟩ :=
    hDimension Q QG B.restriction hgeom hd hd1 hm P0 weight hweight
  have hlocal : forall j, forall hj : j ∈ Q.indexSet a, (B.factor j hj).parts <= P0.parts := by
    intro j hj part hp
    rw [hP0]
    exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, by simp, hp⟩
  obtain ⟨Gp, Qp, hGp, hrestp, hGpne, ⟨hstep⟩, hcells, hfib⟩ :=
    hPartTower Q QG Z ham hm.le B P0 hlocal P hP hPne
  let L := ENNReal.ofReal (1 + Real.logb 2 (3 / (delta : Real))) ^ 3
  have hL : 1 <= L := by
    have hh : 1 <= (3 : Real) / delta :=
      (le_div_iff₀ (show (0 : Real) < delta by exact_mod_cast hd)).mpr
        (by simpa using (show (delta : Real) <= 3 by
          exact_mod_cast hd1.trans (by norm_num : (1 : NNReal) <= 3)))
    have hl := Real.logb_nonneg (by norm_num : (1 : Real) < 2) hh
    apply one_le_pow₀
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hLt : L < ⊤ := by dsimp [L]; finiteness
  have hpaid : (∑ i ∈ G, volume (Z i).shade) <= L * ∑ i ∈ Gp, volume (Z i).shade := by
    rw [hmassTotal, hGp, hmassSelected P hP]
    exact hpaidBin
  have hpos : 0 < ∑ i ∈ Gp, volume (Z i).shade := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) zero_le
    rw [hz, mul_zero] at hpaid
    exact not_le_of_gt hGpos hpaid
  have hcard := hCard Q hgeom hd hd1
  have hGpS : Gp <= S := hrestp.subset.trans B.restriction.subset
  have hcardp : (Gp.card : Real) <= (4 * 2000 ^ 6 * (A0 + 1) : Real) * (1 / (delta : Real)) ^ 6 :=
    (show (Gp.card : Real) <= S.card by exact_mod_cast Finset.card_le_card hGpS).trans hcard
  have hbudget : B.stageLoss * L * (Kakeya.dyadicPigeonholeNatConstant Gp.card : ENNReal) <=
      sourceFixedPreparationLoss K delta := by
    calc
      _ <= sourceFixedPreparationLoss Kstage delta * L *
          (Kakeya.dyadicPigeonholeNatConstant Gp.card : ENNReal) := by
        gcongr
        exact B.loss_bound
      _ <= _ := hLossBound delta hd hd1 Gp.card hcardp
  exact hAssembly Q QG Z ham hm.le B hcounts Qp hrestp hGpne hstep hcells
    (fun j hj => (B.factor j hj).parts ∩ P)
    (fun _ _ => Finset.inter_subset_left) hfib (by norm_num) haw hab hbc hclo hchi
    (fun j hj part hp => hdims part (Finset.mem_inter.mp hp).2)
    hcoeff' L hL hLt hpaid hpos hbudget

/-- Reading the eccentric side of an already constructed common bin. The
explicit eccentricity premise belongs only to this conditional readback;
the actual exhaustive producer below must construct or avoid this case. -/
theorem source_terminal_plank_of_eccentric_bin
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {G : Finset iota} {QG : SourceThreadedTower G T M C}
    {a m : Nat} {bias : Real} {A : NNReal} {Kstage : Nat}
    (B : SourceDirectOrdinaryCellStage Q Z G QG a m bias A Kstage)
    {R : Finset iota} {QR : SourceThreadedTower R T M C} {D : NNReal} {K : Nat}
    (F : SourceTerminalCommonFactorBin Q Z B R QR D K)
    {etaParent e : Real} {b : Nat}
    (hwindow : SourceTowerWindow delta M e a b m) (hmM : m <= M)
    (hecc : F.short / F.middle <= delta ^ etaParent)
    (hfloor : forall i, i ∈ S -> (delta : ENNReal) ^ (10 : Real) *
      volume (T i).carrier <= volume (Z i).shade) :
    exists P : SourceDirectPlank Q Z R QR Z e etaParent bias a b K D,
      P.level = m /\ P.short = F.short /\ P.middle = F.middle /\ P.long = F.long /\
      (forall j, forall hj : j ∈ QR.indexSet a,
        (P.factors.factor j hj).parts = (F.factor j hj).parts) /\
      SourceTerminalPlankStatistics QR Z a P.level := by
  classical
  have hancestor (a b : Nat) (hab : a <= b) (hb : b <= M)
      (i : iota) (hi : i ∈ R) (j : iota) (hj : j ∈ R)
      (heq : QR.place b i = QR.place b j) : QR.place a i = QR.place a j := by
    induction b, hab using Nat.le_induction with
    | base => exact heq
    | succ b hab ih =>
      apply ih (Nat.le_of_succ_le hb)
      rw [QR.parent_composition b (Nat.lt_of_succ_le hb) i hi,
        QR.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
  have hpartition (j : iota) (hj : j ∈ QR.indexSet a) :
      QR.cell a j = (F.factor j hj).parts.biUnion
        (fun part => R.filter (fun i => QR.place m i ∈ part)) := by
    ext i
    constructor
    · intro hi
      have him : QR.place m i ∈ QR.fibre a m j := Finset.mem_image_of_mem _ hi
      obtain ⟨part, hp, hip⟩ := (F.factor j hj).exists_mem him
      exact Finset.mem_biUnion.mpr ⟨part, hp,
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hip⟩⟩
    · intro hi
      obtain ⟨part, hp, hip⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨hiR, him⟩ := Finset.mem_filter.mp hip
      have him' := (F.factor j hj).subset hp him
      obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp him'
      obtain ⟨hxR, hxj⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hiR,
        (hancestor a m hwindow.1.le hmM i hiR x hxR hxi.symm).trans hxj⟩
  have hmass (j : iota) (hj : j ∈ QR.indexSet a) :
      (∑ i ∈ QR.cell a j, volume (Z i).shade) =
        ∑ part ∈ (F.factor j hj).parts,
          ∑ i ∈ R.filter (fun i => QR.place m i ∈ part), volume (Z i).shade := by
    rw [hpartition j hj]
    apply Finset.sum_biUnion
    intro part hp part' hp' hne
    apply Finset.disjoint_left.mpr
    intro i hi hi'
    exact Finset.disjoint_left.mp ((F.factor j hj).disjoint hp hp' hne)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2
  let factors : SourceDirectPlankFactors QR Z a m etaParent bias D
      F.short F.middle F.long := {
    factor := F.factor
    coarse_lt_middle := hwindow.1
    middle_bound := hmM
    comparison_one := F.comparison_one
    short_positive := F.short_positive
    short_le_middle := F.short_le_middle
    middle_le_long := F.middle_le_long
    long_lower := F.long_lower
    long_upper := F.long_upper
    eccentric := hecc
    dimensions := F.dimensions
    same_tubes := F.statistics.same_tubes
    shade_floor := fun i hi => hfloor i (F.retained.restriction.subset hi)
    nonempty_parts := fun j hj part hp => (F.factor j hj).nonempty_of_mem_parts hp
    assigned_partition := hpartition
    assigned_mass := hmass }
  exact ⟨{
    level := m
    in_window := hwindow
    short := F.short
    middle := F.middle
    long := F.long
    factors := factors
    cell_stage := F.cell_stage }, rfl, rfl, rfl, rfl, fun _ _ => rfl, F.statistics⟩

end Kakeya.ML2Core
