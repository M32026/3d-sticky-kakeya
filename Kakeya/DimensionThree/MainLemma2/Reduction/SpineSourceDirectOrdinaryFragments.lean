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

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- Actual common affine normalization, including identities absent from the
older existential interface. All geometry is attached to the same maps. -/
structure SourceDirectCommonWindowNormalization
    (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (a m : Nat) (P : ML2Assembly.SourceBiasedLossParameters) where
  partition : forall j, ML2Assembly.SourceDescendantPartition (Q.cell a j) (Q.fibre a m j)
  normalization : iota -> EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3)
  comparison : iota -> NNReal
  thickness : iota -> NNReal
  assign_eq : forall j, (partition j).assign = Q.place m
  common_map : forall j, (normalization j : EuclideanSpace Real (Fin 3) ->
    EuclideanSpace Real (Fin 3)) = AffineMap.homothety 0 (3 : Real)⁻¹
  thickness_eq : forall j, thickness j = delta / 3
  geometry : ML2Assembly.SourceBiasedParentGeometry
    (Q.indexSet a) (Q.cell a) (Q.fibre a m)
    (fun i => (Z i).toShadedBody) (fun _ i => (Q.tube m i).toConvexSpaceBody)
    (fun j => (Q.tube a j).toConvexSpaceBody) normalization comparison thickness
  polynomial : forall j, j ∈ Q.indexSet a ->
    ML2Assembly.SourceBiasedPolynomialScale P delta (Q.fibre a m j).card (thickness j)

/-- Additive extraction of the actual 1/3 construction. -/
theorem source_direct_common_window_normalization
    (M A0 A1 C : Nat) (hM : 2 <= M) (hC : 1 <= C)
    {bias : Real} (hbias : 0 < bias) :
    exists P : ML2Assembly.SourceBiasedLossParameters,
      P.bias = bias /\ P.cardCoefficient = 32 ^ 6 /\
      P.thicknessCoefficient = 1 / 3 /\ P.cardPower = 6 /\ P.thicknessPower = 1 /\
    exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
      (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
    forall Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)),
      (forall i, (Z i).toTube = T i) ->
      (forall i, i ∈ S -> 0 < volume (Z i).shade) ->
    forall a m : Nat, a < m -> m < M ->
      Nonempty (SourceDirectCommonWindowNormalization Q Z a m P) := by
  classical
  let P : ML2Assembly.SourceBiasedLossParameters :=
    ⟨bias, hbias, 32 ^ 6, by norm_num, 1 / 3, by norm_num,
      by norm_num [div_le_iff₀ (show (0 : NNReal) < 3 by norm_num)], 6, 1⟩
  obtain ⟨eps, heps, hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (source_eventually_fixed_tower_radius_conditions M hM (e := 1) zero_lt_one)
  refine ⟨P, rfl, rfl, rfl, rfl, rfl, min eps 1, lt_min heps zero_lt_one, min_le_right _ _, ?_⟩
  intro delta hdelta hsmall iota S T Q hgeometry Z hZT hshade a m ham hmM
  have hdelta1 : delta <= 1 := hsmall.le.trans (min_le_right _ _)
  have hscale := hall ⟨hdelta, hsmall.trans_le (min_le_left _ _)⟩
  have hradius : forall k, k < M -> delta <= sourceTowerRadius delta M k := by
    intro k hk
    exact (show delta <= 4 * delta by nlinarith).trans (hscale.2.2.2.2.1 k hk)
  have hradiusPos : forall k, k < M -> 0 < sourceTowerRadius delta M k :=
    fun k hk => hdelta.trans_le (hradius k hk)
  have hdescendant : forall k l, k <= l -> l <= M -> forall i, i ∈ S ->
      (Q.tube l (Q.place l i)).toConvexSpaceBody <=
        (Q.tube k (Q.place k i)).toConvexSpaceBody := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => intros; exact le_rfl
    | succ l hkl ih =>
      intro hl i hi
      have hstep := Q.parent_containment l (by omega) (Q.place (l + 1) i)
        (Q.place_mem (l + 1) hl i hi)
      rw [← Q.parent_composition l (by omega) i hi] at hstep
      exact hstep.trans (ih (by omega) i hi)
  let partition : forall j,
      ML2Assembly.SourceDescendantPartition (Q.cell a j) (Q.fibre a m j) := fun j =>
    { cells := fun k => (Q.cell a j).filter (fun i => Q.place m i = k)
      assign := Q.place m
      assigned_mem := fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
      cells_eq := fun _ _ => rfl
      cells_nonempty := by
        intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
        exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
      union_eq := by
        ext i
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨k, hk, hi, heq⟩; exact hi
        · intro hi
          exact ⟨Q.place m i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hi, rfl⟩
      disjoint := by
        intro k hk l hl hne
        rw [Function.onFun, Finset.disjoint_left]
        intro i hi hil
        exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hil).2) }
  let f : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3) :=
    AffineEquiv.homothetyUnitsMulHom 0 (Units.mk0 (3 : Real)⁻¹ (by norm_num))
  have hf : (f : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin 3)) =
      AffineMap.homothety 0 (3 : Real)⁻¹ := rfl
  let comparison : iota -> NNReal := fun j => max 1
    (volume (ML2Assembly.sourceAffineReference f).carrier /
      volume (Q.tube a j).carrier).toNNReal
  have hparentPos : forall j, 0 < volume (Q.tube a j).carrier := by
    intro j
    refine lt_of_lt_of_le ?_ (Tube.le_volume (Q.tube a j))
    have hc := Tube.le_volume.c_pos
      (Module.finrank Real (EuclideanSpace Real (Fin 3)))
    have hr := hradiusPos a (by omega)
    positivity
  have hreference : forall j,
      volume (ML2Assembly.sourceAffineReference f).carrier <=
        (comparison j : ENNReal) * volume (Q.tube a j).carrier := by
    intro j
    have hfinite : volume (ML2Assembly.sourceAffineReference f).carrier /
        volume (Q.tube a j).carrier ≠ ⊤ := ENNReal.div_ne_top
      (ML2Assembly.sourceAffineReference f).isCompact.measure_ne_top (hparentPos j).ne'
    calc
      volume (ML2Assembly.sourceAffineReference f).carrier =
          ((volume (ML2Assembly.sourceAffineReference f).carrier /
            volume (Q.tube a j).carrier).toNNReal : ENNReal) *
              volume (Q.tube a j).carrier := by
        rw [ENNReal.coe_toNNReal hfinite,
          ENNReal.div_mul_cancel (hparentPos j).ne'
            (Q.tube a j).toConvexSpaceBody.isCompact.measure_ne_top]
      _ <= (comparison j : ENNReal) * volume (Q.tube a j).carrier := by
        gcongr
        exact le_max_right _ _
  have hgeo : ML2Assembly.SourceBiasedParentGeometry (Q.indexSet a) (Q.cell a)
      (Q.fibre a m) (fun i => (Z i).toShadedBody)
      (fun _ i => (Q.tube m i).toConvexSpaceBody)
      (fun j => (Q.tube a j).toConvexSpaceBody) (fun _ => f) comparison
      (fun _ => delta / 3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hgeometry.nonempty
      exact ⟨Q.place a i, Q.place_mem a (by omega) i hi⟩
    · intro j hj k hk hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i hi hik
      exact hne ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hik).2)
    · intro j hj
      obtain ⟨i, hi, hplace⟩ := Q.place_surjective a (by omega) j hj
      exact (hshade i hi).trans_le (Finset.single_le_sum_of_canonicallyOrdered
        (f := fun i => volume (Z i).shade) (Finset.mem_filter.mpr ⟨hi, hplace⟩))
    · intro j hj; positivity
    · intro j hj k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      simpa only [heq] using hdescendant a m ham.le hmM.le i hi
    · intro j hj
      change f '' (Q.tube a j).carrier ⊆ Metric.closedBall 0 1
      rw [hf]
      exact Kakeya.exists_finite_test_family_maxDensity_closedBall.homothety_subset_closedBall_one
        (R := 3) (by norm_num) (hgeometry.coarse_ball a (by omega) j hj)
    · intro j hj k hk
      rw [ConvexSpaceBody.mapAffine_carrier, hf]
      exact Kakeya.exists_finite_test_family_maxDensity_closedBall.le_scale_homothety_inv
        (R := 3) (by norm_num)
        ((show (delta : ENNReal) <= (sourceTowerRadius delta M m : ENNReal) by
          exact_mod_cast hradius m hmM).trans (Q.tube m k).le_ethickness_scale)
    · intro j hj; exact le_max_left _ _
    · intro j hj; exact hreference j
  refine ⟨{
    partition := partition
    normalization := fun _ => f
    comparison := comparison
    thickness := fun _ => delta / 3
    assign_eq := fun _ => rfl
    common_map := fun _ => hf
    thickness_eq := fun _ => rfl
    geometry := hgeo
    polynomial := ?_ }⟩
  apply ML2Assembly.sourceBiased_parent_polynomialScale P hdelta hdelta1
    (Q.indexSet a) (Q.cell a) (Q.fibre a m) partition
    (fun i => (Z i).toShadedBody) (fun _ i => (Q.tube m i).toConvexSpaceBody)
    (fun j => (Q.tube a j).toConvexSpaceBody) (fun _ => f) comparison
    (fun _ => delta / 3) hgeo
  · intro j hj
    have hsub : Q.fibre a m j ⊆ Q.indexSet m := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact Q.place_mem m hmM.le i (Finset.mem_filter.mp hi).1
    calc
      ((Q.fibre a m j).card : Real) <= ((Q.indexSet m).card : Real) := by
        exact_mod_cast Finset.card_le_card hsub
      _ <= (32 / (sourceTowerRadius delta M m : Real)) ^ 6 :=
        hgeometry.coarse_card m hmM
      _ <= (32 / (delta : Real)) ^ 6 := by
        gcongr
        exact_mod_cast hradius m hmM
      _ = (P.cardCoefficient : Real) * (delta : Real) ^ (-(P.cardPower : Real)) := by
        change (32 / (delta : Real)) ^ 6 = 32 ^ 6 * (delta : Real) ^ (-(6 : Real))
        rw [Real.rpow_neg (by positivity)]
        norm_num [div_eq_mul_inv, mul_pow, inv_pow]
  · intro j hj
    simp only [P, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, Real.rpow_one]
    ring_nf
    exact le_rfl

/-- A genuine immediate B5 stage. Its factors are on the actual after-family;
no statistics or common physical dimension bin is asserted here. -/
structure SourceDirectOrdinaryCellStage (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (G : Finset iota) (QG : SourceThreadedTower G T M C)
    (a m : Nat) (bias : Real) (A : NNReal) (K : Nat) where
  parameters : ML2Assembly.SourceBiasedLossParameters
  internal_bias : parameters.bias = bias / 16
  card_coefficient : parameters.cardCoefficient = 32 ^ 6
  thickness_coefficient : parameters.thicknessCoefficient = 1 / 3
  card_power : parameters.cardPower = 6
  thickness_power : parameters.thicknessPower = 1
  normalized : SourceDirectCommonWindowNormalization Q Z a m parameters
  actual : forall j, j ∈ Q.indexSet a ->
    ML2Assembly.SourceAffineWeightedParent (normalized.partition j)
      (fun i => (Z i).toShadedBody) (fun k => (Q.tube m k).toConvexSpaceBody)
      (Q.tube a j).toConvexSpaceBody (normalized.normalization j)
      (normalized.comparison j) (normalized.thickness j) (bias / 16)
  restriction : SourceTowerRestriction Q QG
  before_nonempty : S.Nonempty
  after_nonempty : G.Nonempty
  whole_cell : SourceWholeCellStep Q S G m
  same_coarse : QG.indexSet a = Q.indexSet a
  same_tubes : forall i, (Z i).toTube = T i
  selected_fibre : forall j, forall hj : j ∈ Q.indexSet a,
    QG.fibre a m j = (actual j hj).selection.selected
  selected_leaves : G = (Q.indexSet a).attach.biUnion (fun j =>
    ML2Assembly.sourceDescendantUnion (normalized.partition j.val)
      (actual j.val j.property).selection.selected)
  local_leaves : forall j, forall hj : j ∈ Q.indexSet a,
    G ∩ Q.cell a j = ML2Assembly.sourceDescendantUnion (normalized.partition j)
      (actual j hj).selection.selected
  C0 : NNReal
  coefficient_one : 1 <= C0
  coefficient_bound : C0 <= A * delta ^ (-4 * (bias / 16))
  factor : forall j, j ∈ Q.indexSet a ->
    Factorization (QG.fibre a m j) (fun k => (QG.tube m k).toConvexSpaceBody) C0
  factor_parts : forall j, forall hj : j ∈ Q.indexSet a,
    (factor j hj).parts = (actual j hj).selection.parts
  hull_ratio : forall j, forall hj : j ∈ Q.indexSet a,
    forall part, part ∈ (actual j hj).selection.parts ->
      (delta : ENNReal) ^ (4 : Real) <=
        volume (part.convexHull_biUnion
          (fun k => (Q.tube m k).toConvexSpaceBody)).carrier /
        volume (ML2Assembly.sourceAffineReference (normalized.normalization j)).carrier
  stageLoss : ENNReal
  loss_one : 1 <= stageLoss
  loss_finite : stageLoss < ⊤
  local_loss : forall j, j ∈ Q.indexSet a ->
    nonempty_biasedFactorization.L 3 (Q.fibre a m j).card
      (normalized.thickness j) (bias / 16) <= stageLoss
  mass : (∑ i ∈ S, volume (Z i).shade) <= stageLoss * ∑ i ∈ G, volume (Z i).shade
  loss_bound : stageLoss <= sourceFixedPreparationLoss K delta

/-- The ordinary coefficient pays the actual q=4 hull/reference lower ratio.
All scale-independent constants precede the runtime tower and level. -/
theorem source_direct_exists_ordinary_cell_stage
    (M A0 A1 C : Nat) (hM : 2 <= M) (hC : 1 <= C)
    (bias : Real) (hbias : 0 < bias) :
    exists (A : NNReal) (K : Nat) (delta0 : NNReal),
      1 <= A /\ 1 <= K /\ 0 < delta0 /\ delta0 <= 1 /\
      delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
      (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
    forall Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)),
      (forall i, (Z i).toTube = T i) ->
      (forall i, i ∈ S -> 0 < volume (Z i).shade) ->
    forall a m : Nat, a < m -> m < M ->
    exists (G : Finset iota) (QG : SourceThreadedTower G T M C),
      Nonempty (SourceDirectOrdinaryCellStage Q Z G QG a m bias A K) := by
  classical
  have hb : 0 < bias / 16 := by positivity
  obtain ⟨P, hPb, hPc, hPt, hPcp, hPtp, eps, heps, heps1, hnorm⟩ :=
    source_direct_common_window_normalization M A0 A1 C hM hC hb
  obtain ⟨epsL, hepsL, hepsL1, hpoly⟩ := ML2Assembly.sourceBiased_exists_polylog_threshold 3 P
  let A : NNReal := max 2 (nonempty_biasedFactorization.C 3 (bias / 16))
  let delta0 := min (min eps epsL) (min (1 / 1296) ((400 : NNReal) ^ (-(M : Real))))
  have hA2 : 2 <= A := le_max_left _ _
  have hA1 : 1 <= A := le_trans (by norm_num) hA2
  refine ⟨A, 5, delta0, hA1, by norm_num, ?_, ?_, ?_, ?_⟩
  · dsimp [delta0]; positivity
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans heps1)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  intro delta hd hs iota S T Q hgeo Z hZT hshade a m ham hmM
  have hsN : delta < eps := hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hsL : delta < epsL := hs.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hd1 : delta <= 1 := hsN.le.trans heps1
  have hdsmall : delta <= 1 / 1296 := hs.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨N⟩ := hnorm delta hd hsN S T Q hgeo Z hZT hshade a m ham hmM
  have hlocal : forall j, j ∈ Q.indexSet a ->
      nonempty_biasedFactorization.L 3 (Q.fibre a m j).card
        (N.thickness j) (bias / 16) <= polylogLoss 5 delta := by
    intro j hj
    simpa only [hPb] using (hpoly delta (N.thickness j) _ hsL (N.polynomial j hj)).2.2
  have hLf : polylogLoss 5 delta < ⊤ := by
    unfold polylogLoss
    finiteness
  obtain ⟨D, G, hGeq, hGsub, hGne, hGlocal, _, _, _, hmass⟩ :=
    ML2Assembly.sourceBiased_exists_parentAggregation
      (Q.indexSet a) N.geometry.parents_nonempty (Q.cell a) (Q.fibre a m) N.partition
      N.geometry.parent_fibres_disjoint (fun i => (Z i).toShadedBody)
      (fun _ k => (Q.tube m k).toConvexSpaceBody) (fun j => (Q.tube a j).toConvexSpaceBody)
      N.normalization N.comparison N.thickness (bias / 16) hb
      (polylogLoss 5 delta) hLf N.geometry.mass_pos N.geometry.thickness_pos
      N.geometry.contained N.geometry.normalized_ball N.geometry.normalized_thickness
      (fun j hj => ⟨N.geometry.comparison_one_le j hj, N.geometry.reference_comparison j hj⟩)
      (by simpa using hlocal)
  have hunion : (Q.indexSet a).biUnion (Q.cell a) = S := by
    ext i
    simp only [Finset.mem_biUnion, SourceThreadedTower.cell, Finset.mem_filter]
    exact ⟨fun ⟨j, hj, hi, heq⟩ => hi,
      fun hi => ⟨Q.place a i, Q.place_mem a (by omega) i hi, hi, rfl⟩⟩
  have hGS : G <= S := by
    change G ⊆ S
    simpa only [hunion] using hGsub
  have hmem (j : {j // j ∈ Q.indexSet a}) (i : iota) :
      i ∈ ML2Assembly.sourceDescendantUnion (N.partition j.val) (D j).selection.selected ↔
        i ∈ Q.cell a j.val ∧ Q.place m i ∈ (D j).selection.selected := by
    simp only [ML2Assembly.sourceDescendantUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨k, hk, hi⟩
      rw [(N.partition j.val).cells_eq k ((D j).selection.selected_subset hk)] at hi
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      rw [N.assign_eq] at heq
      exact ⟨hi, heq ▸ hk⟩
    · rintro ⟨hi, hk⟩
      refine ⟨Q.place m i, hk, ?_⟩
      rw [(N.partition j.val).cells_eq _ ((D j).selection.selected_subset hk), N.assign_eq]
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hcoarse (b : Nat) (hbM : b <= M) : forall c, c <= b ->
      forall i, i ∈ S -> forall j, j ∈ S ->
        Q.place b i = Q.place b j -> Q.place c i = Q.place c j := by
    induction b with
    | zero => intro c hc i hi j hj heq; simpa only [Nat.eq_zero_of_le_zero hc] using heq
    | succ b ih =>
      intro c hc i hi j hj heq
      by_cases heq' : c = b + 1
      · simpa only [heq'] using heq
      · apply ih (by omega) c (by omega) i hi j hj
        rw [Q.parent_composition b (by omega) i hi,
          Q.parent_composition b (by omega) j hj, heq]
  have hsat : forall i, i ∈ G -> forall k, k ∈ S -> Q.place m k = Q.place m i -> k ∈ G := by
    intro i hi k hk hki
    let j : {j // j ∈ Q.indexSet a} := ⟨Q.place a i, Q.place_mem a (by omega) i (hGS hi)⟩
    have hic : i ∈ Q.cell a j.val := Finset.mem_filter.mpr ⟨hGS hi, rfl⟩
    have him := (hmem j i).mp ((hGlocal j) ▸ Finset.mem_inter.mpr ⟨hi, hic⟩)
    have hkc : k ∈ Q.cell a j.val := Finset.mem_filter.mpr
      ⟨hk, hcoarse m hmM.le a ham.le k hk i (hGS hi) hki⟩
    have hkm := (hmem j k).mpr ⟨hkc, hki ▸ him.2⟩
    rw [← hGlocal j] at hkm
    exact (Finset.mem_inter.mp hkm).1
  have hocc (k : Nat) (hk : k <= M) : Q.assignedFootprint G k <= Q.indexSet k := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Q.place_mem k hk i (hGS hi)
  let QG : SourceThreadedTower G T M C := {
    indexSet := Q.assignedFootprint G
    place := Q.place
    parent := Q.parent
    tube := Q.tube
    tube_injective := fun k hk i hi j hj => Q.tube_injective k hk (hocc k hk hi) (hocc k hk hj)
    place_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
    place_surjective := fun k _ j hj => Finset.mem_image.mp hj
    leaf_containment := fun k hk i hi => Q.leaf_containment k hk i (hGS hi)
    parent_mem := by
      intro k hk j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [← Q.parent_composition k hk i (hGS hi)]
      exact Finset.mem_image_of_mem _ hi
    parent_composition := fun k hk i hi => Q.parent_composition k hk i (hGS hi)
    parent_containment := fun k hk j hj => Q.parent_containment k hk j (hocc (k + 1) (by omega) hj)
    bottom_index := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
        rw [Q.bottom_place j (hGS hj)] at hji
        exact hji ▸ hj
      · intro hi
        exact Finset.mem_image.mpr ⟨i, hi, Q.bottom_place i (hGS hi)⟩
    bottom_place := fun i hi => Q.bottom_place i (hGS hi)
    bottom_body := fun i hi => Q.bottom_body i (hGS hi)
    containment_multiplicity := by
      intro k hk i hi
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk))).trans
        (Q.containment_multiplicity k hk i (hGS hi)) }
  have hrest : SourceTowerRestriction Q QG := {
    subset := hGS
    assignment := rfl
    parent := rfl
    tubes := rfl
    occupied := fun _ _ => rfl
    full_retained_fibres := fun _ _ _ => rfl }
  have hcell (j : iota) : QG.cell a j = G ∩ Q.cell a j := by
    ext i
    simp only [SourceThreadedTower.cell, Finset.mem_filter, Finset.mem_inter]
    change (i ∈ G ∧ Q.place a i = j) ↔ (i ∈ G ∧ i ∈ S ∧ Q.place a i = j)
    exact ⟨fun h => ⟨h.1, hGS h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hfibre (j : {j // j ∈ Q.indexSet a}) : QG.fibre a m j.val = (D j).selection.selected := by
    change (QG.cell a j.val).image (Q.place m) = _
    rw [hcell, hGlocal j]
    ext k
    constructor
    · rintro hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      exact ((hmem j i).mp hi).2
    · intro hk
      obtain ⟨i, hi⟩ := (N.partition j.val).cells_nonempty k ((D j).selection.selected_subset hk)
      have hic := hi
      rw [(N.partition j.val).cells_eq k ((D j).selection.selected_subset hk), N.assign_eq] at hic
      refine Finset.mem_image.mpr ⟨i, ?_, (Finset.mem_filter.mp hic).2⟩
      exact Finset.mem_biUnion.mpr ⟨k, hk, hi⟩
  have hsame : QG.indexSet a = Q.indexSet a := by
    apply Finset.Subset.antisymm (hocc a (by omega))
    intro j hj
    obtain ⟨k, hk⟩ := (D ⟨j, hj⟩).selection.selected_nonempty
    rw [← hfibre ⟨j, hj⟩] at hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_image.mp hk
    obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_image.mpr ⟨i, hi, heq⟩
  have hwhole : SourceWholeCellStep Q S G m := {
    selected := Q.assignedFootprint G m
    selected_subset := Finset.image_subset_image hGS
    leaves_eq := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · intro hi; exact ⟨hGS hi, Finset.mem_image_of_mem _ hi⟩
      · rintro ⟨hi, hpi⟩
        obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hpi
        exact hsat k hk i hi hki.symm
    complete := by
      intro j hj
      obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hGS h.1, h.2⟩,
        fun h => ⟨hsat k hk i h.1 (h.2.trans hkj.symm), h.2⟩⟩ }
  let C0 : NNReal := A * delta ^ (-4 * (bias / 16))
  have hpow : 1 <= delta ^ (-4 * (bias / 16)) := NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  have hAC : A <= C0 := le_mul_of_one_le_right' hpow
  have hC01 : 1 <= C0 := hA1.trans hAC
  have hC02 : 2 <= C0 := hA2.trans hAC
  have hCf : (nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) *
      (delta : ENNReal) ^ (-4 * (bias / 16)) <= (C0 : ENNReal) := by
    simpa only [C0, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hd.ne'] using
      mul_le_mul_right'
        (show (nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) <= A from
          ENNReal.coe_le_coe.mpr (le_max_right _ _)) ((delta : ENNReal) ^ (-4 * (bias / 16)))
  have hratio (j : {j // j ∈ Q.indexSet a}) (part : Finset iota)
      (hp : part ∈ (D j).selection.parts) :
      (delta : ENNReal) ^ (4 : Real) <=
        volume (part.convexHull_biUnion (fun k => (Q.tube m k).toConvexSpaceBody)).carrier /
        volume (ML2Assembly.sourceAffineReference (N.normalization j.val)).carrier := by
    rw [← (D j).ratio_map part hp]
    obtain ⟨k, hk⟩ := (D j).selection.factor.nonempty_of_mem_parts
      ((D j).selection.factor_parts.symm ▸ hp)
    have hkI : k ∈ Q.fibre a m j.val := (D j).selection.selected_subset
      ((D j).selection.factor.le ((D j).selection.factor_parts.symm ▸ hp) hk)
    have hv := ((Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val)).convex.le_volume_of_le_scale
      (N.geometry.normalized_thickness j.val j.property k hkI)
    rw [N.thickness_eq] at hv
    have hh : volume ((Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val)).carrier <=
        volume (part.convexHull_biUnion
          (fun k => (Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val))).carrier :=
      measure_mono (Finset.le_convexHull_biUnion
        (fun k => (Q.tube m k).toConvexSpaceBody.mapAffine (N.normalization j.val)) hk)
    have hball : volume (closedUnitBall (E := EuclideanSpace Real (Fin 3))).carrier <= 8 := by
      simpa only [closedUnitBall_carrier, finrank_euclideanSpace_fin, show (2 : ENNReal) ^ 3 = 8 by norm_num] using
        (volume_closedBall_le_two_pow_finrank (E := EuclideanSpace Real (Fin 3)))
    apply (ENNReal.le_div_iff_mul_le (.inl closedUnitBall_volume_pos.ne')
      (.inl closedUnitBall.isCompact.measure_ne_top)).mpr
    calc (delta : ENNReal) ^ (4 : Real) * volume (closedUnitBall (E := EuclideanSpace Real (Fin 3))).carrier
        <= (delta : ENNReal) ^ (4 : Real) * 8 := by gcongr
      _ <= (Metric.lt_volume_convexHull.c 3 : ENNReal) * ((delta / 3 : NNReal) : ENNReal) ^ 3 := by
        have he : delta ^ 4 * 8 <= (1 / 6 : NNReal) * (delta / 3) ^ 3 := by
          have hmul := mul_le_mul_right' hdsmall (delta ^ 3)
          nlinarith
        have he' := ENNReal.coe_le_coe.mpr he
        norm_num [ENNReal.rpow_natCast, Metric.lt_volume_convexHull.c,
          ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_div] at he' ⊢
        exact he'
      _ <= _ := le_trans (by simpa only [finrank_euclideanSpace_fin] using hv) hh
  have hfactor (j : {j // j ∈ Q.indexSet a}) :
      exists F : Factorization (QG.fibre a m j.val)
        (fun k => (QG.tube m k).toConvexSpaceBody) C0, F.parts = (D j).selection.parts := by
    let V := fun k => (Q.tube m k).toConvexSpaceBody
    have hcost (part : Finset iota) (hp : part ∈ (D j).selection.parts) :
        (nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) *
          (volume (part.convexHull_biUnion V).carrier /
            volume (ML2Assembly.sourceAffineReference (N.normalization j.val)).carrier) ^ (-(bias / 16)) <= C0 := by
      refine le_trans ?_ hCf
      apply mul_le_mul_left'
      rw [show -4 * (bias / 16) = -(4 * (bias / 16)) by ring,
        ENNReal.rpow_neg, ENNReal.rpow_neg]
      have hr := ENNReal.rpow_le_rpow (hratio j part hp) hb.le
      rw [← ENNReal.rpow_mul] at hr
      exact ENNReal.inv_le_inv.mpr hr
    have hcapture (part : Finset iota) (hp : part ∈ (D j).selection.parts) :
        Kakeya.maxDensity (D j).selection.selected V <=
          (C0 : ENNReal) * Kakeya.densityIn part V (part.convexHull_biUnion V) := by
      let r := volume (part.convexHull_biUnion V).carrier /
        volume (ML2Assembly.sourceAffineReference (N.normalization j.val)).carrier
      have hr0 : r ≠ 0 := ENNReal.div_ne_zero.mpr
        ⟨((D j).hull_pos part hp).ne', (D j).reference_finite.ne⟩
      have hrt : r ≠ ⊤ := ENNReal.div_ne_top ((D j).hull_finite part hp).ne (D j).reference_pos.ne'
      have hc0 : (nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) ≠ 0 := by
        dsimp [nonempty_biasedFactorization.C]
        positivity
      have hc := (D j).capture_reference part hp
      simp only [show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp] at hc
      have hcancel :
          ((nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) * r ^ (-(bias / 16))) *
          ((nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal)⁻¹ * r ^ (bias / 16)) = 1 := by
        rw [ENNReal.rpow_neg]
        calc _ = ((nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) *
            (nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal)⁻¹) *
            ((r ^ (bias / 16))⁻¹ * r ^ (bias / 16)) := by ring
          _ = 1 := by rw [ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top,
            ENNReal.inv_mul_cancel (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hr0) hrt).ne'
              (ENNReal.rpow_ne_top_of_ne_zero hr0 hrt), one_mul]
      have hcap : Kakeya.maxDensity (D j).selection.selected V <=
          ((nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) * r ^ (-(bias / 16))) *
            Kakeya.densityIn part V (part.convexHull_biUnion V) := by
        calc _ = ((nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal) * r ^ (-(bias / 16))) *
            ((nonempty_biasedFactorization.C 3 (bias / 16) : ENNReal)⁻¹ * r ^ (bias / 16) *
              Kakeya.maxDensity (D j).selection.selected V) := by rw [← mul_assoc, hcancel, one_mul]
          _ <= _ := mul_le_mul_left' hc _
      exact hcap.trans (mul_le_mul_right' (hcost part hp) _)
    have hdim (part : Finset iota) (hp : part ∈ (D j).selection.parts) (k : Nat) :
        ethickness Real
          (part.convexHull_biUnion (fun k => (V k).mapAffine (N.normalization j.val))).carrier k =
          (1 / 3 : ENNReal) * ethickness Real (part.convexHull_biUnion V).carrier k := by
      rw [← (D j).hull_map part hp, ConvexSpaceBody.mapAffine_carrier, N.common_map,
        Metric.ethickness_homothety_image _ (by norm_num : (3 : Real)⁻¹ ≠ 0)]
      norm_num [V]
    have hsim : forall part, part ∈ (D j).selection.parts ->
        forall part', part' ∈ (D j).selection.parts -> forall k : Nat,
          ethickness Real (part.convexHull_biUnion V).carrier k <=
            (C0 : ENNReal) * ethickness Real (part'.convexHull_biUnion V).carrier k := by
      intro part hp part' hp' k
      by_cases hk : k < 3
      · have hh := (D j).selection.dimensions part hp part' hp' ⟨k, by simpa using hk⟩
        rw [hdim part hp k, hdim part' hp' k] at hh
        have hh' : ethickness Real (part.convexHull_biUnion V).carrier k <=
            2 * ethickness Real (part'.convexHull_biUnion V).carrier k := by
          apply (ENNReal.mul_le_mul_iff_right (by norm_num : (1 / 3 : ENNReal) ≠ 0) (by norm_num)).mp
          simpa only [mul_left_comm (2 : ENNReal)] using hh
        exact hh'.trans (mul_le_mul_right' (by exact_mod_cast hC02) _)
      · rw [ethickness_eq_zero_of_finrank_le (show Module.finrank Real (EuclideanSpace Real (Fin 3)) <= k by simpa using Nat.le_of_not_gt hk)]
        exact zero_le
    have hkt : ConvexSpaceBody.IsKatzTao (D j).selection.parts
        (fun part => part.convexHull_biUnion V) C0 := by
      obtain ⟨part, hp⟩ := (D j).selection.parts_nonempty
      exact ((D j).outer_katzTao part hp).trans (by simpa using hcost part hp)
    let F0 : Factorization (D j).selection.selected V C0 := {
      toFinpartition := (D j).selection.factor.toFinpartition
      isKatzTao := by simpa only [(D j).selection.factor_parts] using hkt
      maxDensity_le_mul := by simpa only [(D j).selection.factor_parts] using hcapture
      simDims := by
        intro part hp part' hp' k
        exact hsim part ((D j).selection.factor_parts ▸ hp) part'
          ((D j).selection.factor_parts ▸ hp') k }
    change exists F : Factorization (QG.fibre a m j.val) V C0, F.parts = (D j).selection.parts
    rw [hfibre j]
    exact ⟨F0, (D j).selection.factor_parts⟩
  choose F hF using hfactor
  refine ⟨G, QG, ⟨{
    parameters := P
    internal_bias := hPb
    card_coefficient := hPc
    thickness_coefficient := hPt
    card_power := hPcp
    thickness_power := hPtp
    normalized := N
    actual := fun j hj => D ⟨j, hj⟩
    restriction := hrest
    before_nonempty := hgeo.nonempty
    after_nonempty := hGne
    whole_cell := hwhole
    same_coarse := hsame
    same_tubes := hZT
    selected_fibre := fun j hj => hfibre ⟨j, hj⟩
    selected_leaves := hGeq
    local_leaves := fun j hj => hGlocal ⟨j, hj⟩
    C0 := C0
    coefficient_one := hC01
    coefficient_bound := le_rfl
    factor := fun j hj => F ⟨j, hj⟩
    factor_parts := fun j hj => hF ⟨j, hj⟩
    hull_ratio := fun j hj => hratio ⟨j, hj⟩
    stageLoss := polylogLoss 5 delta
    loss_one := by
      unfold polylogLoss
      exact ENNReal.one_le_ofReal.mpr (le_max_left _ _)
    loss_finite := hLf
    local_loss := hlocal
    mass := by simpa only [hunion] using hmass
    loss_bound := ?_ }⟩⟩
  rw [polylogLoss, max_eq_right (one_le_polylog hd1 5), sourceFixedPreparationLoss]
  apply ENNReal.ofReal_le_ofReal
  have hdR : (0 : Real) < delta := by exact_mod_cast hd
  have hlog : Real.log (delta : Real) <= 0 := Real.log_nonpos hdR.le (by exact_mod_cast hd1)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 <= 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)]
  have hbase : 1 - Real.log (delta : Real) <= 2 + Real.logb 2 (1 / (delta : Real)) := by
    rw [Real.logb, one_div, Real.log_inv]
    have hh : -Real.log (delta : Real) <= -Real.log (delta : Real) / Real.log 2 := by
      apply (le_div_iff₀ htwo).mpr
      exact mul_le_of_le_one_right (neg_nonneg.mpr hlog) htwo1
    linarith
  exact pow_le_pow_left₀ (by linarith) hbase 5

/-- The used old tags are exactly those with a nonempty literal intersection. -/
noncomputable def sourceOrdinaryUsedParts {I : Finset iota}
    (F : Finpartition I) (J : Finset iota) : Finset (Finset iota) :=
  F.parts.filter (fun part => (part ∩ J).Nonempty)

noncomputable def sourceOrdinaryFragmentParts {I : Finset iota}
    (F : Finpartition I) (J : Finset iota) : Finset (Finset iota) :=
  (sourceOrdinaryUsedParts F J).image (fun part => part ∩ J)

/-- Literal finite intersections, their coverage, disjointness and tag injectivity. -/
theorem source_ordinary_fragment_partition {I J : Finset iota}
    (F : Finpartition I) (hJI : J <= I) :
    (sourceOrdinaryUsedParts F J).biUnion (fun part => part ∩ J) = J /\
    ((sourceOrdinaryFragmentParts F J : Set (Finset iota)).PairwiseDisjoint id) /\
    Set.InjOn (fun part => part ∩ J) (sourceOrdinaryUsedParts F J : Set (Finset iota)) /\
    (forall part, part ∈ sourceOrdinaryUsedParts F J -> (part ∩ J).Nonempty) /\
    exists P : Finpartition J, P.parts = sourceOrdinaryFragmentParts F J := by
  classical
  have hne (part : Finset iota) (hp : part ∈ sourceOrdinaryUsedParts F J) :
      (part ∩ J).Nonempty := (Finset.mem_filter.mp hp).2
  have hparts (part : Finset iota) (hp : part ∈ sourceOrdinaryUsedParts F J) :
      part ∈ F.parts := (Finset.mem_filter.mp hp).1
  have hcover : (sourceOrdinaryUsedParts F J).biUnion (fun part => part ∩ J) = J := by
    ext i
    constructor
    · intro hi
      obtain ⟨part, hp, hi⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_inter.mp hi).2
    · intro hi
      obtain ⟨part, hp, hip⟩ := F.exists_mem (hJI hi)
      exact Finset.mem_biUnion.mpr ⟨part, Finset.mem_filter.mpr
        ⟨hp, ⟨i, Finset.mem_inter.mpr ⟨hip, hi⟩⟩⟩, Finset.mem_inter.mpr ⟨hip, hi⟩⟩
  have hinj : Set.InjOn (fun part => part ∩ J) (sourceOrdinaryUsedParts F J : Set (Finset iota)) := by
    intro p hp q hq heq
    obtain ⟨i, hi⟩ := hne p hp
    have hiq : i ∈ q ∩ J := by
      change p ∩ J = q ∩ J at heq
      rwa [← heq]
    exact F.eq_of_mem_parts (hparts p hp) (hparts q hq)
      (Finset.mem_inter.mp hi).1 (Finset.mem_inter.mp hiq).1
  have hdis : (sourceOrdinaryFragmentParts F J : Set (Finset iota)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact (F.disjoint (hparts p hp) (hparts q hq) (fun h => hxy (h ▸ rfl))).mono
      Finset.inter_subset_left Finset.inter_subset_left
  refine ⟨hcover, hdis, hinj, hne, ⟨{
    parts := sourceOrdinaryFragmentParts F J
    supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr hdis
    sup_parts := ?_
    bot_notMem := ?_ }, rfl⟩⟩
  · simpa [sourceOrdinaryFragmentParts, Finset.sup_image, Finset.sup_eq_biUnion] using hcover
  · intro hempty
    obtain ⟨part, hp, heq⟩ := Finset.mem_image.mp hempty
    exact (hne part hp).ne_empty heq

/-- Quantitative geometric rows on exactly the literal final fragments. -/
structure SourceOrdinaryFragmentGeometry {I J : Finset iota}
    (V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
    (C0 L : NNReal) (F : Factorization I V C0) : Prop where
  old_positive : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    0 < volume (part.convexHull_biUnion V).carrier
  retained_positive : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    0 < volume ((part ∩ J).convexHull_biUnion V).carrier
  contained : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    (part ∩ J).convexHull_biUnion V <= part.convexHull_biUnion V
  old_volume : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    volume (part.convexHull_biUnion V).carrier <=
      (C0 * L : NNReal) * volume ((part ∩ J).convexHull_biUnion V).carrier
  capture : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    Kakeya.maxDensity J V <= (C0 * L : NNReal) *
      Kakeya.densityIn (part ∩ J) V ((part ∩ J).convexHull_biUnion V)
  simultaneous_test : forall K : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
    exists Kplus : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
      volume Kplus.carrier <= (384 * (2 ^ 50 * C0 * L) ^ 3 : NNReal) * volume K.carrier /\
      forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
        (part ∩ J).convexHull_biUnion V <= K -> part.convexHull_biUnion V <= Kplus
  thickness : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
    forall k : Nat, ethickness Real (part.convexHull_biUnion V).carrier k <=
      (2 ^ 50 * C0 * L : NNReal) * ethickness Real ((part ∩ J).convexHull_biUnion V).carrier k

set_option maxHeartbeats 6000000 in
/-- Ordinary factor transport needs actual unshaded volume retention on every
used old part. Global retained shading mass alone is not this hypothesis. -/
theorem source_ordinary_fragment_geometry {I J : Finset iota}
    (V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
    (C0 L : NNReal) (hC0 : 1 <= C0) (hL : 1 <= L)
    (F : Factorization I V C0) (hJI : J <= I)
    (hpositive : forall i, i ∈ I -> 0 < volume (V i).carrier)
    (hretention : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
      (∑ i ∈ part, volume (V i).carrier) <=
        (L : ENNReal) * ∑ i ∈ part ∩ J, volume (V i).carrier) :
    SourceOrdinaryFragmentGeometry (J := J) V C0 L F := by
  have hRetained {iota : Type u} {r : Finset iota}
      {V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3))} {C0 L : NNReal}
      (F : ConvexSpaceBody.Factorization r V C0) {part q : Finset iota}
      (hpart : part ∈ F.parts) (hq : q <= part) (hqne : q.Nonempty)
      (hpositive : forall i, i ∈ part -> 0 < volume (V i).carrier)
      (hret : (∑ i ∈ part, volume (V i).carrier) <=
        (L : ENNReal) * ∑ i ∈ q, volume (V i).carrier) :
      volume (part.convexHull_biUnion V).carrier <=
        (C0 : ENNReal) * L * volume (q.convexHull_biUnion V).carrier := by
    classical
    let v := volume (part.convexHull_biUnion V).carrier
    let w := volume (q.convexHull_biUnion V).carrier
    let s := ∑ i ∈ part, volume (V i).carrier
    let t := ∑ i ∈ q, volume (V i).carrier
    have hvtop : v ≠ ⊤ := (part.convexHull_biUnion V).isCompact'.measure_lt_top.ne
    have hwtop : w ≠ ⊤ := (q.convexHull_biUnion V).isCompact'.measure_lt_top.ne
    have hstop : s ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).isCompact'.measure_lt_top.ne
    have httop : t ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (V i).isCompact'.measure_lt_top.ne
    obtain ⟨i0, hi0⟩ := hqne
    have hi0p := hq hi0
    have hvpos : 0 < v := (hpositive i0 hi0p).trans_le
      (measure_mono (Finset.le_convexHull_biUnion V hi0p))
    have hwpos : 0 < w := (hpositive i0 hi0p).trans_le
      (measure_mono (Finset.le_convexHull_biUnion V hi0))
    have hspos : 0 < s := by
      refine (hpositive i0 hi0p).trans_le ?_
      dsimp [s]
      exact Finset.single_le_sum (f := fun i => volume (V i).carrier) (fun _ _ => bot_le) hi0p
    have hden : t / w <= (C0 : ENNReal) * (s / v) := by
      have hqR := hq.trans (F.toFinpartition.le hpart)
      have hbound := (le_maxDensity q V (q.convexHull_biUnion V)).trans
        ((maxDensity_mono V hqR).trans (F.maxDensity_le_mul part hpart))
      rw [densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi),
        densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi)] at hbound
      exact hbound
    have hrreal : s.toReal <= L * t.toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top httop) hret
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using h
    have hdreal : t.toReal / w.toReal <= C0 * (s.toReal / v.toReal) := by
      have hden_top : (C0 : ENNReal) * (s / v) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.div_ne_top hstop hvpos.ne')
      have h := ENNReal.toReal_mono hden_top hden
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.coe_toReal] using h
    have hvreal : 0 < v.toReal := ENNReal.toReal_pos hvpos.ne' hvtop
    have hwreal : 0 < w.toReal := ENNReal.toReal_pos hwpos.ne' hwtop
    have hsreal : 0 < s.toReal := ENNReal.toReal_pos hspos.ne' hstop
    have hcross : t.toReal * v.toReal <= (C0 : Real) * s.toReal * w.toReal := by
      apply (div_le_iff₀ hwreal).mp at hdreal
      apply (mul_le_mul_iff_left₀ hvreal).2 at hdreal
      field_simp at hdreal
      nlinarith [hdreal]
    have hgoal : v.toReal <= (C0 : Real) * L * w.toReal := by
      have h1 := mul_le_mul_of_nonneg_right hrreal hvreal.le
      have h2 := mul_le_mul_of_nonneg_left hcross L.coe_nonneg
      nlinarith
    apply (ENNReal.toReal_le_toReal hvtop
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hwtop)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hgoal
  have hTest {jota : Type u} (q : Finset jota)
      (B O N : jota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
      (A : EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3))
      (L : NNReal) (hL : 1 <= L)
      (hBpos : forall i, i ∈ q -> 0 < volume (B i).carrier)
      (hBO : forall i, i ∈ q -> B i <= O i)
      (hOBvol : forall i, i ∈ q -> volume (O i).carrier <= (L : ENNReal) * volume (B i).carrier)
      (hBN : forall i, i ∈ q -> (B i).mapAffine A <= N i) :
      forall V : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
        exists W : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          volume W.carrier <= ((384 * (2^50 * L)^3 : NNReal) : ENNReal) /
            affineJacobian A * volume V.carrier ∧
          forall i, i ∈ q -> N i <= V -> O i <= W := by
    have hEnlarge (K : NNReal) (hK : 1 <= K)
        (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) (hM : 0 < volume M.carrier) :
        ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
          Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
      have hNormalized (K : NNReal) (hK : 1 <= K)
          (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
          (hMball : M.carrier <= Metric.closedBall 0 3)
          (hMvol : (6 : ENNReal)⁻¹ <= volume M.carrier) :
          ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
            M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
            Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
        have hMvol' : ENNReal.ofReal (1 / 6 : Real) <= volume M.carrier := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 6)]
          norm_num
          exact hMvol
        obtain ⟨z, hzM, hzball⟩ := exists_closedBall_subset_of_le_volume (by norm_num : 1 <= 3)
          (by norm_num : (0 : Real) < 3) M hMball (by norm_num : (0 : Real) < 1 / 6) hMvol'
        norm_num at hzball
        let r : NNReal := 1 / 1728
        have hball : Metric.closedBall z (r : Real) <= M.carrier := by
          simpa [r] using hzball
        have hMu : volume M.carrier <= 216 := by
          have h := volume_le_prod_ethickness M.carrier
          have hth : forall n, ethickness Real M.carrier n <= (3 : NNReal) :=
            fun n => ethickness_le_of_subset_closedBall (𝕜 := Real) 3 hMball n
          norm_num [Finset.prod_range_succ] at h
          calc volume M.carrier <=
              8 * (ethickness Real M.carrier 0 * ethickness Real M.carrier 1 *
                ethickness Real M.carrier 2) := h
            _ <= 8 * ((3 : ENNReal) * 3 * 3) := by gcongr <;> exact hth _
            _ = 216 := by norm_num
        refine ⟨z, hzM, ?_⟩
        intro Q hMQ hQvol x hxQ
        have hQu : volume Q.carrier <= (216 : ENNReal) * K :=
          hQvol.trans (by simpa only [mul_comm] using mul_le_mul_left' hMu (K : ENNReal))
        have hr1 : (r : ENNReal) <= ethickness Real Q.carrier 1 :=
          (le_ethickness_closedBall (x := z) (n := 1) r (by norm_num)).trans
            (ethickness_monotone (hball.trans hMQ) 1)
        have hr2 : (r : ENNReal) <= ethickness Real Q.carrier 2 :=
          (le_ethickness_closedBall (x := z) (n := 2) r (by norm_num)).trans
            (ethickness_monotone (hball.trans hMQ) 2)
        have htfin : forall n, ethickness Real Q.carrier n ≠ ⊤ := by
          intro n
          change ethickness Real (Q : Set (EuclideanSpace Real (Fin 3))) n ≠ ⊤
          rw [ethickness_thickness' Q.isCompact.isBounded]
          exact ENNReal.ofReal_ne_top
        have hQr : (volume Q.carrier).toReal <= 216 * (K : Real) := by
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hQu
          simpa using this
        have hr1r : (r : Real) <= (ethickness Real Q.carrier 1).toReal := by
          simpa using ENNReal.toReal_mono (htfin 1) hr1
        have hr2r : (r : Real) <= (ethickness Real Q.carrier 2).toReal := by
          simpa using ENNReal.toReal_mono (htfin 2) hr2
        have hprod := Q.convex.ethickness_prod_le_volume
        norm_num [Finset.prod_range_succ, Metric.lt_volume_convexHull.c] at hprod
        have hprodr := ENNReal.toReal_mono Q.isCompact.measure_lt_top.ne hprod
        change ((6 : ENNReal)⁻¹ * (ethickness Real Q.carrier 0 * ethickness Real Q.carrier 1 *
          ethickness Real Q.carrier 2)).toReal <= (volume Q.carrier).toReal at hprodr
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hprodr
        have ht0 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 0)
        have ht1 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 1)
        have ht2 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 2)
        have hmul : (r : Real)^2 <= (ethickness Real Q.carrier 1).toReal *
            (ethickness Real Q.carrier 2).toReal := by
          nlinarith only [hr1r, hr2r, ht1, ht2, r.coe_nonneg,
            mul_nonneg (sub_nonneg.mpr hr1r) (sub_nonneg.mpr hr2r)]
        have ht0u : (ethickness Real Q.carrier 0).toReal <= 1296 * 1728^2 * (K : Real) := by
          have hmul0 := mul_le_mul_of_nonneg_left hmul ht0
          norm_num [r] at hmul0
          nlinarith only [hmul0, hprodr, hQr]
        have hdist := half_dist_le_ethickness_zero (𝕜 := Real) hxQ (hMQ hzM)
        have hdistr := ENNReal.toReal_mono (htfin 0) hdist
        rw [ENNReal.toReal_ofReal (by positivity)] at hdistr
        have hdistu : dist x z <= 2592 * 1728^2 * (K : Real) := by
          nlinarith only [hdistr, ht0u]
        have hK0 : (0 : Real) < K := by exact_mod_cast zero_lt_one.trans_le hK
        let lam : Real := (2 : Real)^50 * K
        have hlam : 0 < lam := by dsimp [lam]; positivity
        refine ⟨z + lam⁻¹ • (x - z), hball ?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hlam), ← dist_eq_norm]
          apply (inv_mul_le_iff₀ hlam).2
          dsimp [r, lam]
          push_cast
          nlinarith only [hdistu, hK0]
        · change AffineMap.homothety z lam (z + lam⁻¹ • (x - z)) = x
          simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
            add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
          abel
      obtain ⟨c, b, len, hlen, hsub, hvol⟩ := M.convex.exists_boundingBox hM.ne'
        M.isCompact.measure_lt_top.ne (by simp : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3)
      let P := PrismNDim.mk' c b (fun i => (len i).toNNReal)
      have hMP : M.carrier <= P.carrier := by
        intro x hx
        rw [PrismNDim.mem_carrier_iff]
        intro i
        rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
          Real.coe_toNNReal _ (hlen i).le]
        simpa [vsub_eq_sub] using hsub x hx i
      have hPvol : volume P.carrier <= 48 * volume M.carrier := by
        rw [PrismNDim.volume_carrier, PrismNDim.thicknesses_mk']
        have hcoe : ∏ i, (((len i).toNNReal : NNReal) : ENNReal) =
            ENNReal.ofReal (∏ i, len i) := by
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hlen i).le)]
          exact Finset.prod_congr rfl fun i _ => rfl
        rw [hcoe]
        norm_num at hvol ⊢
        calc 8 * ENNReal.ofReal (∏ i, len i) <= 8 * (6 * volume M.carrier) :=
            mul_le_mul_left' hvol 8
          _ = 48 * volume M.carrier := by ring
      have hPv : 0 < volume P.carrier := hM.trans_le (measure_mono hMP)
      obtain ⟨A, hAcube, hAv⟩ := P.exists_affineEquiv_image_eq_cube hPv
      let N := M.mapAffine A
      have hNball : N.carrier <= Metric.closedBall 0 3 := by
        have hsub : N.carrier <= (PrismNDim.mk' 0 P.basis (fun _ => (1 : NNReal))).carrier := by
          change A '' M.carrier <= _
          rw [← hAcube]
          exact Set.image_mono hMP
        have hball := (PrismNDim.mk' (0 : EuclideanSpace Real (Fin 3)) P.basis
          (fun _ => (1 : NNReal))).carrier_subset_closedBall_euclidean
        norm_num [PrismNDim.center_mk', PrismNDim.thicknesses_mk'] at hball
        exact hsub.trans (hball.trans (Metric.closedBall_subset_closedBall (show Real.sqrt 3 <= (3 : Real) by
          rw [Real.sqrt_le_iff]
          norm_num)))
      have hNvol : (6 : ENNReal)⁻¹ <= volume N.carrier := by
        have hmfin : volume M.carrier ≠ ⊤ := M.isCompact.measure_lt_top.ne
        have hnfin : volume N.carrier ≠ ⊤ := N.isCompact.measure_lt_top.ne
        have hpfin : volume P.carrier ≠ ⊤ := P.toConvexSpaceBody.isCompact.measure_lt_top.ne
        have hpos := ENNReal.toReal_pos hM.ne' hmfin
        have hPn := hAv M.carrier
        change volume P.carrier * volume N.carrier = 2 ^ 3 * volume M.carrier at hPn
        have hPnr := congrArg ENNReal.toReal hPn
        norm_num only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hPnr
        norm_num at hPvol
        have hPvr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hmfin) hPvol
        change (volume P.carrier).toReal <= ((48 : ENNReal) * volume M.carrier).toReal at hPvr
        simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hPvr
        have hmul := mul_le_mul_of_nonneg_right hPvr (ENNReal.toReal_nonneg (a := volume N.carrier))
        apply (ENNReal.toReal_le_toReal (by simp) hnfin).mp
        norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
        nlinarith only [hpos, hPnr, hmul]
      obtain ⟨z, hzN, hz⟩ := hNormalized K hK N hNball hNvol
      have hzM : A.symm z ∈ M.carrier := by
        obtain ⟨w, hw, hwz⟩ := hzN
        simpa [← hwz] using hw
      refine ⟨A.symm z, hzM, ?_⟩
      intro Q hMQ hQv x hx
      have hNQ : N <= Q.mapAffine A := Set.image_mono hMQ
      have hQAv : volume (Q.mapAffine A).carrier <= (K : ENNReal) * volume N.carrier := by
        change volume (A '' Q.carrier) <= (K : ENNReal) * volume (A '' M.carrier)
        rw [volume_image_affineEquiv, volume_image_affineEquiv]
        simpa only [mul_assoc, mul_left_comm] using mul_le_mul_left' hQv (affineJacobian A)
      have hAx := hz (Q.mapAffine A) hNQ hQAv (Set.mem_image_of_mem A hx)
      obtain ⟨y, hyN, hyx⟩ := hAx
      obtain ⟨w, hw, hwy⟩ := hyN
      refine ⟨w, hw, A.injective ?_⟩
      rw [← hyx, ← hwy]
      simp only [AffineMap.homothety_apply]
      rw [A.map_vadd, map_smul]
      change (2 ^ 50 * (K : Real)) • A.toAffineMap.linear (w -ᵥ A.symm z) +ᵥ A (A.symm z) = _
      rw [A.toAffineMap.linearMap_vsub]
      simp
    let lam : NNReal := 2^50 * L
    have hlam : (1 : Real) <= lam := by
      have h : (1 : NNReal) <= lam := one_le_mul_of_one_le_of_one_le (by norm_num) hL
      exact_mod_cast h
    have hcost : (1 : ENNReal) <= ((384 * lam^3 : NNReal) : ENNReal) := by
      exact_mod_cast (show (1 : NNReal) <= 384 * lam^3 by
        apply one_le_mul_of_one_le_of_one_le (by norm_num)
        exact one_le_pow₀ (by exact_mod_cast hlam))
    have hJac0 := affineJacobian_ne_zero A
    have hJactop := affineJacobian_ne_top A
    have hpull (V : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) :
        affineJacobian A * volume (V.mapAffine A.symm).carrier = volume V.carrier := by
      rw [← volume_mapAffine, symm_mapAffine_mapAffine]
    intro V
    by_cases hex : ∃ i ∈ q, N i <= V
    · obtain ⟨i0, hi0, hiV⟩ := hex
      have hVpos : 0 < volume V.carrier := by
        have himg : 0 < volume ((B i0).mapAffine A).carrier := by
          rw [volume_mapAffine]
          exact ENNReal.mul_pos hJac0 (hBpos i0 hi0).ne'
        exact himg.trans_le (measure_mono ((hBN i0 hi0).trans hiV))
      obtain ⟨D, hVD, hhomD, hDvol⟩ := V.convex.exists_homothety_container hVpos.ne'
        V.isCompact.measure_lt_top.ne hlam
      refine ⟨D.toConvexSpaceBody.mapAffine A.symm, ?_, ?_⟩
      · apply (ENNReal.mul_le_mul_iff_right hJac0 hJactop).mp
        rw [hpull]
        have hcancel : affineJacobian A *
            (((384 * lam^3 : NNReal) : ENNReal) / affineJacobian A * volume V.carrier) =
            ((384 * lam^3 : NNReal) : ENNReal) * volume V.carrier := by
          rw [div_eq_mul_inv]
          calc _ = ((384 * lam^3 : NNReal) : ENNReal) *
              (affineJacobian A * (affineJacobian A)⁻¹) * volume V.carrier := by ring
            _ = _ := by rw [ENNReal.mul_inv_cancel hJac0 hJactop, mul_one]
        change volume D.carrier <= affineJacobian A *
          (((384 * lam^3 : NNReal) : ENNReal) / affineJacobian A * volume V.carrier)
        rw [hcancel]
        convert hDvol using 1 <;>
          norm_num [ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul,
            ENNReal.coe_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm]
        ring
      · intro i hi hiV x hx
        obtain ⟨z, hz, hOz⟩ := hEnlarge L hL (B i) (hBpos i hi)
        obtain ⟨y, hy, hyx⟩ := hOz (O i) (hBO i hi) (hOBvol i hi) hx
        have hzV : A z ∈ V.carrier := hiV (hBN i hi (Set.mem_image_of_mem A hz))
        have hyV : A y ∈ V.carrier := hiV (hBN i hi (Set.mem_image_of_mem A hy))
        have hAx : A x = (lam : Real) • (A y - A z) + A z := by
          rw [← hyx, AffineMap.homothety_apply, A.map_vadd, map_smul]
          change (2^50 * (L : Real)) • A.toAffineMap.linear (y -ᵥ z) +ᵥ A z = _
          rw [A.toAffineMap.linearMap_vsub]
          rfl
        exact ⟨A x, by rw [hAx]; exact hhomD _ hzV _ hyV, A.symm_apply_apply x⟩
    · refine ⟨V.mapAffine A.symm, ?_, ?_⟩
      · apply (ENNReal.mul_le_mul_iff_right hJac0 hJactop).mp
        rw [hpull]
        calc volume V.carrier <= ((384 * lam^3 : NNReal) : ENNReal) * volume V.carrier :=
            le_mul_of_one_le_left' hcost
          _ = _ := by
            change _ = affineJacobian A *
              (((384 * lam^3 : NNReal) : ENNReal) / affineJacobian A * volume V.carrier)
            rw [div_eq_mul_inv]
            calc _ = ((384 * lam^3 : NNReal) : ENNReal) *
                (affineJacobian A * (affineJacobian A)⁻¹) * volume V.carrier := by
                  rw [ENNReal.mul_inv_cancel hJac0 hJactop, mul_one]
              _ = _ := by ring
      · intro i hi hiV
        exact (hex ⟨i, hi, hiV⟩).elim
  have hRetThickness (K B : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) (L : NNReal) (hL : 1 <= L)
      (hB : 0 < volume B.carrier) (hBK : B <= K)
      (hvol : volume K.carrier <= (L : ENNReal) * volume B.carrier) :
      forall j : Nat, ethickness Real K.carrier j <=
        ((2^50 * L : NNReal) : ENNReal) * ethickness Real B.carrier j := by
    have hEnlarge (K : NNReal) (hK : 1 <= K)
        (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3))) (hM : 0 < volume M.carrier) :
        ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
          M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
          Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
      have hNormalized (K : NNReal) (hK : 1 <= K)
          (M : ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
          (hMball : M.carrier <= Metric.closedBall 0 3)
          (hMvol : (6 : ENNReal)⁻¹ <= volume M.carrier) :
          ∃ z ∈ M.carrier, forall Q : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
            M <= Q -> volume Q.carrier <= (K : ENNReal) * volume M.carrier ->
            Q.carrier <= AffineMap.homothety z ((2 : Real)^50 * K) '' M.carrier := by
        have hMvol' : ENNReal.ofReal (1 / 6 : Real) <= volume M.carrier := by
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 6)]
          norm_num
          exact hMvol
        obtain ⟨z, hzM, hzball⟩ := exists_closedBall_subset_of_le_volume (by norm_num : 1 <= 3)
          (by norm_num : (0 : Real) < 3) M hMball (by norm_num : (0 : Real) < 1 / 6) hMvol'
        norm_num at hzball
        let r : NNReal := 1 / 1728
        have hball : Metric.closedBall z (r : Real) <= M.carrier := by
          simpa [r] using hzball
        have hMu : volume M.carrier <= 216 := by
          have h := volume_le_prod_ethickness M.carrier
          have hth : forall n, ethickness Real M.carrier n <= (3 : NNReal) :=
            fun n => ethickness_le_of_subset_closedBall (𝕜 := Real) 3 hMball n
          norm_num [Finset.prod_range_succ] at h
          calc volume M.carrier <=
              8 * (ethickness Real M.carrier 0 * ethickness Real M.carrier 1 *
                ethickness Real M.carrier 2) := h
            _ <= 8 * ((3 : ENNReal) * 3 * 3) := by gcongr <;> exact hth _
            _ = 216 := by norm_num
        refine ⟨z, hzM, ?_⟩
        intro Q hMQ hQvol x hxQ
        have hQu : volume Q.carrier <= (216 : ENNReal) * K :=
          hQvol.trans (by simpa only [mul_comm] using mul_le_mul_left' hMu (K : ENNReal))
        have hr1 : (r : ENNReal) <= ethickness Real Q.carrier 1 :=
          (le_ethickness_closedBall (x := z) (n := 1) r (by norm_num)).trans
            (ethickness_monotone (hball.trans hMQ) 1)
        have hr2 : (r : ENNReal) <= ethickness Real Q.carrier 2 :=
          (le_ethickness_closedBall (x := z) (n := 2) r (by norm_num)).trans
            (ethickness_monotone (hball.trans hMQ) 2)
        have htfin : forall n, ethickness Real Q.carrier n ≠ ⊤ := by
          intro n
          change ethickness Real (Q : Set (EuclideanSpace Real (Fin 3))) n ≠ ⊤
          rw [ethickness_thickness' Q.isCompact.isBounded]
          exact ENNReal.ofReal_ne_top
        have hQr : (volume Q.carrier).toReal <= 216 * (K : Real) := by
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hQu
          simpa using this
        have hr1r : (r : Real) <= (ethickness Real Q.carrier 1).toReal := by
          simpa using ENNReal.toReal_mono (htfin 1) hr1
        have hr2r : (r : Real) <= (ethickness Real Q.carrier 2).toReal := by
          simpa using ENNReal.toReal_mono (htfin 2) hr2
        have hprod := Q.convex.ethickness_prod_le_volume
        norm_num [Finset.prod_range_succ, Metric.lt_volume_convexHull.c] at hprod
        have hprodr := ENNReal.toReal_mono Q.isCompact.measure_lt_top.ne hprod
        change ((6 : ENNReal)⁻¹ * (ethickness Real Q.carrier 0 * ethickness Real Q.carrier 1 *
          ethickness Real Q.carrier 2)).toReal <= (volume Q.carrier).toReal at hprodr
        simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hprodr
        have ht0 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 0)
        have ht1 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 1)
        have ht2 := ENNReal.toReal_nonneg (a := ethickness Real Q.carrier 2)
        have hmul : (r : Real)^2 <= (ethickness Real Q.carrier 1).toReal *
            (ethickness Real Q.carrier 2).toReal := by
          nlinarith only [hr1r, hr2r, ht1, ht2, r.coe_nonneg,
            mul_nonneg (sub_nonneg.mpr hr1r) (sub_nonneg.mpr hr2r)]
        have ht0u : (ethickness Real Q.carrier 0).toReal <= 1296 * 1728^2 * (K : Real) := by
          have hmul0 := mul_le_mul_of_nonneg_left hmul ht0
          norm_num [r] at hmul0
          nlinarith only [hmul0, hprodr, hQr]
        have hdist := half_dist_le_ethickness_zero (𝕜 := Real) hxQ (hMQ hzM)
        have hdistr := ENNReal.toReal_mono (htfin 0) hdist
        rw [ENNReal.toReal_ofReal (by positivity)] at hdistr
        have hdistu : dist x z <= 2592 * 1728^2 * (K : Real) := by
          nlinarith only [hdistr, ht0u]
        have hK0 : (0 : Real) < K := by exact_mod_cast zero_lt_one.trans_le hK
        let lam : Real := (2 : Real)^50 * K
        have hlam : 0 < lam := by dsimp [lam]; positivity
        refine ⟨z + lam⁻¹ • (x - z), hball ?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hlam), ← dist_eq_norm]
          apply (inv_mul_le_iff₀ hlam).2
          dsimp [r, lam]
          push_cast
          nlinarith only [hdistu, hK0]
        · change AffineMap.homothety z lam (z + lam⁻¹ • (x - z)) = x
          simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
            add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
          abel
      obtain ⟨c, b, len, hlen, hsub, hvol⟩ := M.convex.exists_boundingBox hM.ne'
        M.isCompact.measure_lt_top.ne (by simp : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3)
      let P := PrismNDim.mk' c b (fun i => (len i).toNNReal)
      have hMP : M.carrier <= P.carrier := by
        intro x hx
        rw [PrismNDim.mem_carrier_iff]
        intro i
        rw [PrismNDim.basis_mk', PrismNDim.center_mk', PrismNDim.thicknesses_mk',
          Real.coe_toNNReal _ (hlen i).le]
        simpa [vsub_eq_sub] using hsub x hx i
      have hPvol : volume P.carrier <= 48 * volume M.carrier := by
        rw [PrismNDim.volume_carrier, PrismNDim.thicknesses_mk']
        have hcoe : ∏ i, (((len i).toNNReal : NNReal) : ENNReal) =
            ENNReal.ofReal (∏ i, len i) := by
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (hlen i).le)]
          exact Finset.prod_congr rfl fun i _ => rfl
        rw [hcoe]
        norm_num at hvol ⊢
        calc 8 * ENNReal.ofReal (∏ i, len i) <= 8 * (6 * volume M.carrier) :=
            mul_le_mul_left' hvol 8
          _ = 48 * volume M.carrier := by ring
      have hPv : 0 < volume P.carrier := hM.trans_le (measure_mono hMP)
      obtain ⟨A, hAcube, hAv⟩ := P.exists_affineEquiv_image_eq_cube hPv
      let N := M.mapAffine A
      have hNball : N.carrier <= Metric.closedBall 0 3 := by
        have hsub : N.carrier <= (PrismNDim.mk' 0 P.basis (fun _ => (1 : NNReal))).carrier := by
          change A '' M.carrier <= _
          rw [← hAcube]
          exact Set.image_mono hMP
        have hball := (PrismNDim.mk' (0 : EuclideanSpace Real (Fin 3)) P.basis
          (fun _ => (1 : NNReal))).carrier_subset_closedBall_euclidean
        norm_num [PrismNDim.center_mk', PrismNDim.thicknesses_mk'] at hball
        exact hsub.trans (hball.trans (Metric.closedBall_subset_closedBall (show Real.sqrt 3 <= (3 : Real) by
          rw [Real.sqrt_le_iff]
          norm_num)))
      have hNvol : (6 : ENNReal)⁻¹ <= volume N.carrier := by
        have hmfin : volume M.carrier ≠ ⊤ := M.isCompact.measure_lt_top.ne
        have hnfin : volume N.carrier ≠ ⊤ := N.isCompact.measure_lt_top.ne
        have hpfin : volume P.carrier ≠ ⊤ := P.toConvexSpaceBody.isCompact.measure_lt_top.ne
        have hpos := ENNReal.toReal_pos hM.ne' hmfin
        have hPn := hAv M.carrier
        change volume P.carrier * volume N.carrier = 2 ^ 3 * volume M.carrier at hPn
        have hPnr := congrArg ENNReal.toReal hPn
        norm_num only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hPnr
        norm_num at hPvol
        have hPvr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hmfin) hPvol
        change (volume P.carrier).toReal <= ((48 : ENNReal) * volume M.carrier).toReal at hPvr
        simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hPvr
        have hmul := mul_le_mul_of_nonneg_right hPvr (ENNReal.toReal_nonneg (a := volume N.carrier))
        apply (ENNReal.toReal_le_toReal (by simp) hnfin).mp
        norm_num only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
        nlinarith only [hpos, hPnr, hmul]
      obtain ⟨z, hzN, hz⟩ := hNormalized K hK N hNball hNvol
      have hzM : A.symm z ∈ M.carrier := by
        obtain ⟨w, hw, hwz⟩ := hzN
        simpa [← hwz] using hw
      refine ⟨A.symm z, hzM, ?_⟩
      intro Q hMQ hQv x hx
      have hNQ : N <= Q.mapAffine A := Set.image_mono hMQ
      have hQAv : volume (Q.mapAffine A).carrier <= (K : ENNReal) * volume N.carrier := by
        change volume (A '' Q.carrier) <= (K : ENNReal) * volume (A '' M.carrier)
        rw [volume_image_affineEquiv, volume_image_affineEquiv]
        simpa only [mul_assoc, mul_left_comm] using mul_le_mul_left' hQv (affineJacobian A)
      have hAx := hz (Q.mapAffine A) hNQ hQAv (Set.mem_image_of_mem A hx)
      obtain ⟨y, hyN, hyx⟩ := hAx
      obtain ⟨w, hw, hwy⟩ := hyN
      refine ⟨w, hw, A.injective ?_⟩
      rw [← hyx, ← hwy]
      simp only [AffineMap.homothety_apply]
      rw [A.map_vadd, map_smul]
      change (2 ^ 50 * (K : Real)) • A.toAffineMap.linear (w -ᵥ A.symm z) +ᵥ A (A.symm z) = _
      rw [A.toAffineMap.linearMap_vsub]
      simp
    obtain ⟨z, hz, hgeom⟩ := hEnlarge L hL B hB
    have hn : ‖((2 : Real)^50 * L)‖₊ = (2^50 * L : NNReal) := by
      apply NNReal.coe_injective
      rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      push_cast
      rfl
    intro j
    calc ethickness Real K.carrier j <=
        ethickness Real (AffineMap.homothety z ((2 : Real)^50 * L) '' B.carrier) j :=
          ethickness_monotone (hgeom K hBK hvol) j
      _ <= _ := by
        have h := ethickness_homothety_image_le z ((2 : Real)^50 * L) B.carrier j
        change ethickness Real (AffineMap.homothety z ((2 : Real)^50 * L) '' B.carrier) j <=
          ((‖((2 : Real)^50 * L)‖₊ : NNReal) : ENNReal) * ethickness Real B.carrier j at h
        rw [hn] at h
        exact h
  classical
  let U := sourceOrdinaryUsedParts F.toFinpartition J
  let H := fun part : Finset iota => part.convexHull_biUnion V
  let R := fun part : Finset iota => (part ∩ J).convexHull_biUnion V
  have hp (part : Finset iota) (hpart : part ∈ U) : part ∈ F.parts :=
    (Finset.mem_filter.mp hpart).1
  have hne (part : Finset iota) (hpart : part ∈ U) : (part ∩ J).Nonempty :=
    (Finset.mem_filter.mp hpart).2
  have hRp (part : Finset iota) (hpart : part ∈ U) : 0 < volume (R part).carrier := by
    obtain ⟨i, hi⟩ := hne part hpart
    exact (hpositive i (hJI (Finset.mem_inter.mp hi).2)).trans_le
      (measure_mono (Finset.le_convexHull_biUnion V hi))
  have hRH (part : Finset iota) (hpart : part ∈ U) : R part <= H part := by
    exact ((hne part hpart).convexHull_biUnion_le_iff V _).mpr fun i hi =>
      Finset.le_convexHull_biUnion V (Finset.mem_inter.mp hi).1
  have hHp (part : Finset iota) (hpart : part ∈ U) : 0 < volume (H part).carrier :=
    (hRp part hpart).trans_le (measure_mono (hRH part hpart))
  have hv (part : Finset iota) (hpart : part ∈ U) :
      volume (H part).carrier <= (C0 * L : NNReal) * volume (R part).carrier := by
    simpa only [ENNReal.coe_mul] using hRetained F (hp part hpart)
      Finset.inter_subset_left (hne part hpart)
      (fun i hi => hpositive i (F.le (hp part hpart) hi)) (hretention part hpart)
  have hc (part : Finset iota) (hpart : part ∈ U) :
      Kakeya.maxDensity J V <= (C0 * L : NNReal) *
        Kakeya.densityIn (part ∩ J) V (R part) := by
    have hdensity : Kakeya.densityIn part V (H part) <=
        (L : ENNReal) * Kakeya.densityIn (part ∩ J) V (R part) := by
      rw [Kakeya.densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi),
        Kakeya.densityIn_of_all_le (fun i hi => Finset.le_convexHull_biUnion V hi)]
      calc (∑ i ∈ part, volume (V i).carrier) / volume (H part).carrier
          <= ((L : ENNReal) * ∑ i ∈ part ∩ J, volume (V i).carrier) / volume (R part).carrier :=
            ENNReal.div_le_div (hretention part hpart) (measure_mono (hRH part hpart))
        _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    calc Kakeya.maxDensity J V <= Kakeya.maxDensity I V := Kakeya.maxDensity_mono V hJI
      _ <= (C0 : ENNReal) * Kakeya.densityIn part V (H part) := F.maxDensity_le_mul part (hp part hpart)
      _ <= (C0 : ENNReal) * ((L : ENNReal) * Kakeya.densityIn (part ∩ J) V (R part)) :=
        mul_le_mul_left' hdensity _
      _ = _ := by rw [ENNReal.coe_mul, mul_assoc]
  refine ⟨hHp, hRp, hRH, hv, hc, ?_, ?_⟩
  · intro K
    obtain ⟨Kplus, hvol, hsub⟩ := hTest U R H R (AffineEquiv.refl Real _)
      (C0 * L) (one_le_mul_of_one_le_of_one_le hC0 hL) hRp hRH hv (by
        intro p hp
        change (AffineEquiv.refl Real _) '' (R p).carrier ⊆ (R p).carrier
        rintro x ⟨y, hy, rfl⟩
        exact hy) K
    refine ⟨Kplus, ?_, hsub⟩
    simpa [affineJacobian, mul_assoc] using hvol
  · intro part hpart k
    simpa only [mul_assoc] using hRetThickness (H part) (R part) (C0 * L)
      (one_le_mul_of_one_le_of_one_le hC0 hL) (hRp part hpart) (hRH part hpart) (hv part hpart) k

noncomputable def sourceOrdinaryFragmentConstant (C0 L : NNReal) : NNReal :=
  max (max (C0 * L) (384 * 2 ^ 150 * C0 ^ 4 * L ^ 3)) (2 ^ 50 * C0 ^ 2 * L)

/-- All three ordinary rows, including every raw thickness rank, are required. -/
theorem source_ordinary_fragment_factorization {I J : Finset iota}
    (V : iota -> ConvexSpaceBody (EuclideanSpace Real (Fin 3)))
    (C0 L : NNReal) (hC0 : 1 <= C0) (hL : 1 <= L)
    (F : Factorization I V C0) (hJI : J <= I)
    (hpositive : forall i, i ∈ I -> 0 < volume (V i).carrier)
    (hretention : forall part, part ∈ sourceOrdinaryUsedParts F.toFinpartition J ->
      (∑ i ∈ part, volume (V i).carrier) <=
        (L : ENNReal) * ∑ i ∈ part ∩ J, volume (V i).carrier) :
    exists F' : Factorization J V (sourceOrdinaryFragmentConstant C0 L),
      F'.parts = sourceOrdinaryFragmentParts F.toFinpartition J := by
  classical
  obtain ⟨_, _, hinj, _, P, hP⟩ := source_ordinary_fragment_partition F.toFinpartition hJI
  have G := source_ordinary_fragment_geometry V C0 L hC0 hL F hJI hpositive hretention
  let U := sourceOrdinaryUsedParts F.toFinpartition J
  let H := fun part : Finset iota => part.convexHull_biUnion V
  let R := fun part : Finset iota => (part ∩ J).convexHull_biUnion V
  let c := sourceOrdinaryFragmentConstant C0 L
  have hc1 : C0 * L <= c := le_trans (le_max_left _ _) (le_max_left _ _)
  have hc2 : 384 * 2 ^ 150 * C0 ^ 4 * L ^ 3 <= c := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc3 : 2 ^ 50 * C0 ^ 2 * L <= c := le_max_right _ _
  have hpartMem {part : Finset iota} (hpart : part ∈ U) : part ∈ F.parts := (Finset.mem_filter.mp hpart).1
  have hKT : IsKatzTao U R c := by
    rw [isKatzTao_iff]
    intro K
    obtain ⟨Kplus, hvol, hsub⟩ := G.simultaneous_test K
    have hfilter : U.filter (fun p => R p <= K) <= F.parts.filter (fun p => H p <= Kplus) := by
      intro p h
      obtain ⟨hp', hR⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hpartMem hp', hsub p hp' hR⟩
    calc (∑ p ∈ U with R p <= K, volume (R p).carrier)
        <= ∑ p ∈ U with R p <= K, volume (H p).carrier :=
          Finset.sum_le_sum fun p hp' => measure_mono (G.contained p (Finset.mem_filter.mp hp').1)
      _ <= ∑ p ∈ F.parts with H p <= Kplus, volume (H p).carrier :=
        Finset.sum_le_sum_of_subset hfilter
      _ <= (C0 : ENNReal) * volume Kplus.carrier := (isKatzTao_iff F.parts H C0).mp F.isKatzTao Kplus
      _ <= (C0 : ENNReal) * ((384 * (2 ^ 50 * C0 * L) ^ 3 : NNReal) * volume K.carrier) :=
        mul_le_mul_left' hvol _
      _ = (384 * 2 ^ 150 * C0 ^ 4 * L ^ 3 : NNReal) * volume K.carrier := by
        push_cast
        ring
      _ <= (c : ENNReal) * volume K.carrier := mul_le_mul_right' (ENNReal.coe_le_coe.mpr hc2) _
  have hKT' : IsKatzTao P.parts (fun p => p.convexHull_biUnion V) c := by
    rw [isKatzTao_iff]
    intro K
    rw [hP, sourceOrdinaryFragmentParts, Finset.filter_image, Finset.sum_image]
    · exact (isKatzTao_iff U R c).mp hKT K
    · intro p hp q hq heq
      exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 heq
  refine ⟨{
    toFinpartition := P
    isKatzTao := hKT'
    maxDensity_le_mul := ?_
    simDims := ?_ }, hP⟩
  · intro p hp
    rw [hP] at hp
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hp
    exact (G.capture old hold).trans (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hc1) _)
  · intro p hp q hq k
    rw [hP] at hp hq
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨old', hold', rfl⟩ := Finset.mem_image.mp hq
    calc ethickness Real ((old ∩ J).convexHull_biUnion V).carrier k
        <= ethickness Real (old.convexHull_biUnion V).carrier k :=
          ethickness_monotone (G.contained old hold) k
      _ <= (C0 : ENNReal) * ethickness Real (old'.convexHull_biUnion V).carrier k :=
        F.simDims old (hpartMem hold) old' (hpartMem hold') k
      _ <= (C0 : ENNReal) * ((2 ^ 50 * C0 * L : NNReal) *
          ethickness Real ((old' ∩ J).convexHull_biUnion V).carrier k) :=
        mul_le_mul_left' (G.thickness old' hold' k) _
      _ = (2 ^ 50 * C0 ^ 2 * L : NNReal) *
          ethickness Real ((old' ∩ J).convexHull_biUnion V).carrier k := by push_cast; ring
      _ <= _ := mul_le_mul_right' (ENNReal.coe_le_coe.mpr hc3) _

/-- The coefficient budget is entirely geometric; no delta-power is charged
to the selector's retained-mass ledger. -/
theorem source_direct_ordinary_fragment_budget
    (A : NNReal) (hA : 1 <= A) (l : Nat) (bias : Real) (hbias : 0 < bias) :
    exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall C0 L : NNReal, 1 <= C0 -> 1 <= L ->
      C0 <= A * delta ^ (-4 * (bias / 16)) ->
      (L : ENNReal) <= sourceFixedPreparationLoss l delta ->
      sourceOrdinaryFragmentConstant C0 L <= sourceParentPlankConstant delta bias := by
  have hLL : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceFixedPreparationLoss l delta <= (delta : ENNReal) ^ (-(bias / 4)) := by
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (2 : ENNReal) ^ l) (by finiteness) (by positivity : 0 < bias / 8),
      ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (by positivity : 0 < bias / 8) l,
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with delta hc hl hd
    have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
    have hdR : (0 : Real) < delta := by exact_mod_cast hd.1
    have hdR1 : (delta : Real) <= 1 := by exact_mod_cast hd.2.le
    have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hdR]; linarith)
    calc sourceFixedPreparationLoss l delta <=
        ENNReal.ofReal ((2 * (1 + Real.logb 2 (1 / (delta : Real)))) ^ l) := by
          apply ENNReal.ofReal_le_ofReal
          gcongr
          linarith
      _ = (2 : ENNReal) ^ l * ENNReal.ofReal (1 + Real.logb 2 (1 / (delta : Real))) ^ l := by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), mul_pow]
          norm_num
      _ <= (delta : ENNReal) ^ (-(bias / 8)) * (delta : ENNReal) ^ (-(bias / 8)) := mul_le_mul' hc hl
      _ = (delta : ENNReal) ^ (-(bias / 4)) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
  let B : NNReal := 384 * 2 ^ 150 * A ^ 4
  have hB : ∀ᶠ delta : NNReal in 𝓝[>] 0, (B : ENNReal) <= (delta : ENNReal) ^ (-(bias / 4)) :=
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg (by finiteness) (by positivity)
  obtain ⟨eps, heps, hevent⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hLL.and hB)
  refine ⟨min eps 1, lt_min heps zero_lt_one, min_le_right _ _, ?_⟩
  intro delta hd hs C0 L hC0 hL hCb hLb
  have hev := hevent ⟨hd, hs.trans_le (min_le_left _ _)⟩
  have hd1 : delta <= 1 := hs.le.trans (min_le_right _ _)
  let t := delta ^ (-(bias / 4))
  have ht : 1 <= t := NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  have hBt : B <= t := ENNReal.coe_le_coe.mp (by
    simpa only [t, ENNReal.coe_rpow_of_ne_zero hd.ne'] using hev.2)
  have hLt : L <= t := ENNReal.coe_le_coe.mp (by
    simpa only [t, ENNReal.coe_rpow_of_ne_zero hd.ne'] using hLb.trans hev.1)
  have hCt : C0 <= A * t := by
    simpa only [t, show -4 * (bias / 16) = -(bias / 4) by ring] using hCb
  have hAB : A <= B := by
    calc A <= A ^ 4 := by simpa using pow_le_pow_right₀ hA (by norm_num : 1 <= 4)
      _ <= B := le_mul_of_one_le_left' (by norm_num : (1 : NNReal) <= 384 * 2 ^ 150)
  have hAB2 : 2 ^ 50 * A ^ 2 <= B := by
    dsimp [B]
    apply mul_le_mul'
    · norm_num
    · exact pow_le_pow_right₀ hA (by norm_num)
  have hgeom : sourceOrdinaryFragmentConstant C0 L <= B * t ^ 7 := by
    unfold sourceOrdinaryFragmentConstant
    apply max_le
    · apply max_le
      · calc C0 * L <= (A * t) * t := mul_le_mul' hCt hLt
          _ = A * t ^ 2 := by ring
          _ <= B * t ^ 7 := mul_le_mul' hAB (pow_le_pow_right₀ ht (by norm_num))
      · calc 384 * 2 ^ 150 * C0 ^ 4 * L ^ 3 <= 384 * 2 ^ 150 * (A * t) ^ 4 * t ^ 3 := by gcongr
          _ = B * t ^ 7 := by dsimp [B]; ring
    · calc 2 ^ 50 * C0 ^ 2 * L <= 2 ^ 50 * (A * t) ^ 2 * t := by gcongr
        _ = (2 ^ 50 * A ^ 2) * t ^ 3 := by ring
        _ <= B * t ^ 7 := mul_le_mul' hAB2 (pow_le_pow_right₀ ht (by norm_num))
  have ht8 : t ^ 8 = delta ^ (-2 * bias) := by
    dsimp [t]
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    congr 1
    ring
  have hbase : 1 <= Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6) := by
    apply Real.one_le_toNNReal.mpr
    have hh := Real.one_le_rpow (by norm_num : (1 : Real) <= 3) (by norm_num : (0 : Real) <= 9 / 2)
    nlinarith
  calc sourceOrdinaryFragmentConstant C0 L <= B * t ^ 7 := hgeom
    _ <= t * t ^ 7 := mul_le_mul_right' hBt _
    _ = t ^ 8 := by ring
    _ = delta ^ (-2 * bias) := ht8
    _ <= delta ^ (-3 * bias) := NNReal.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
    _ <= sourceParentPlankConstant delta bias := le_mul_of_one_le_left' hbase

end Kakeya.ML2Core
