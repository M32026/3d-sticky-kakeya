/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentGeometry
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceChosenTowerRealization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceUnselectedNestedTower

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- Only the upper window rows pass to a subfamily by monotonicity. -/
structure SourceParentUpperWindow (Q : SourceThreadedTower S T M C)
    (A0 A1 N : Nat) (eta : Nat -> Real) (e : Real) (a b J : Nat) : Prop where
  coarse_lt_fine : a < b
  fine_bound : b <= M
  separation : (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
    (delta : Real) ^ e
  coarse_density : a > 0 -> forall j, j ∈ Q.indexSet 0 ->
    Kakeya.maxDensity (Q.fibre 0 a j) (fun i => (Q.tube a i).toConvexSpaceBody) <=
      (sourceTowerWindowConstant C A0 A1 : ENNReal) ^ N * ENNReal.ofReal
        (((sourceTowerRadius delta M 0 : Real) / (sourceTowerRadius delta M a : Real)) ^ eta J)
  middle_density : forall j, j ∈ Q.indexSet a ->
    Kakeya.maxDensity (Q.fibre a b j) (fun i => (Q.tube b i).toConvexSpaceBody) <=
      ENNReal.ofReal
        (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J)

/-- The actual eccentric alternative keeps the selected hulls and their complete
leaf partitions. It is not an eccentric scale predicate or a newly chosen shading. -/
structure SourceParentEccentric (Q : SourceThreadedTower S T M C)
    {e bias : Real} {a b : Nat} (B : SourceJointWindowFactors Q e a b bias)
    (etaParent : Real) where
  level : Nat
  in_window : SourceTowerWindow delta M e a b level
  eccentric : B.short level / B.middle level <= delta ^ etaParent
  factorization : forall j, j ∈ Q.indexSet a ->
    Factorization (Q.fibre a level j) (fun i => (Q.tube level i).toConvexSpaceBody)
      (sourceParentPlankConstant delta bias)
  same_parts : forall j, forall hj : j ∈ Q.indexSet a,
    (factorization j hj).parts = (B.factor level in_window j hj).partition.parts

/-- Coarse and reparented factorings share one actual weighted history and one
fixed-polylog payment. Each local L is paid by its parent-aggregate stage. -/
structure SourceParentCompleteHistory (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {R : Finset iota} (Q' : SourceThreadedTower R T M C)
    {e bias etaParent tau : Real} {a b : Nat} {transverseCap : NNReal}
    (B : SourceJointWindowFactors Q' e a b bias)
    (P : SourceActualParent Q' B etaParent tau transverseCap)
    (K : Nat) where
  coarse_history : SourceCompatibleWholeFactors Q Z Q' B K
  stage : Nat -> iota -> iota -> Nat
  stage_bound : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      stage m j jp < coarse_history.trace.length
  origin : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      SourceFactorStageOrigin Q Z (coarse_history.trace.state (stage m j jp)) R Q'
        P.parent m jp bias (P.reparented m hm j hj jp hjp).factor
  stage_level : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      coarse_history.trace.level (stage m j jp) = m
  stage_selected : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      Q.retainedAssignedFibre (coarse_history.trace.state (stage m j jp + 1)) P.parent m jp =
        (origin m hm j hj jp hjp).actual.selection.selected
  stage_blocks : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      (origin m hm j hj jp hjp).actual.selection.parts <=
        coarse_history.trace.retainedBlocks (stage m j jp)
  actual_loss_paid : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q'.indexSet a,
    forall jp, forall hjp : jp ∈ Q'.fibre a P.parent j,
      nonempty_biasedFactorization.L 3
        (Q.retainedAssignedFibre (coarse_history.trace.state (stage m j jp)) P.parent m jp).card
        (origin m hm j hj jp hjp).normalizedThickness bias <=
          coarse_history.trace.stepLoss (stage m j jp)

/-- The source normalization produces actual B5 inputs; fixed polynomial controls
are chosen before delta. These are not assumptions on a future parent. -/
theorem source_exists_window_normalization
    (M A0 A1 C : Nat) (hM : 2 <= M) (hC : 1 <= C)
    {bias : Real} (hbias : 0 < bias) :
    exists P : ML2Assembly.SourceBiasedLossParameters, P.bias = bias /\
    exists delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
    forall delta : NNReal, 0 < delta -> delta < delta0 ->
    forall {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
      (Q : SourceThreadedTower S T M C), SourceTowerGeometry Q A0 A1 ->
    forall Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)),
      (forall i, (Z i).toTube = T i) ->
      (forall i, i ∈ S -> 0 < volume (Z i).shade) ->
    forall a m : Nat, a < m -> m < M ->
    exists (partition : forall j,
      ML2Assembly.SourceDescendantPartition (Q.cell a j) (Q.fibre a m j))
      (normalization : iota ->
        EuclideanSpace Real (Fin 3) ≃ᵃ[Real] EuclideanSpace Real (Fin 3))
      (comparison d : iota -> NNReal),
      (forall j, (partition j).assign = Q.place m) /\
      ML2Assembly.SourceBiasedParentGeometry (Q.indexSet a) (Q.cell a) (Q.fibre a m)
        (fun i => (Z i).toShadedBody) (fun _ i => (Q.tube m i).toConvexSpaceBody)
        (fun j => (Q.tube a j).toConvexSpaceBody) normalization comparison d /\
      (forall j, j ∈ Q.indexSet a ->
        ML2Assembly.SourceBiasedPolynomialScale P delta (Q.fibre a m j).card (d j)) := by
  classical
  let P : ML2Assembly.SourceBiasedLossParameters :=
    ⟨bias, hbias, 32 ^ 6, by norm_num, 1 / 3, by norm_num,
      by norm_num [div_le_iff₀ (show (0 : NNReal) < 3 by norm_num)], 6, 1⟩
  obtain ⟨eps, heps, hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (source_eventually_fixed_tower_radius_conditions M hM (e := 1) zero_lt_one)
  refine ⟨P, rfl, min eps 1, lt_min heps zero_lt_one, min_le_right _ _, ?_⟩
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
  refine ⟨partition, fun _ => f, comparison, fun _ => delta / 3,
    fun _ => rfl, hgeo, ?_⟩
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

/-- The same-Q neighbour-sharing construction stays an explicit geometric
obligation. It is not inferred from the weaker fixed-segment row. -/
theorem source_exists_chosen_tower_neighbour_realization (M : Nat) (hM : 2 <= M) :
    SourceChosenTowerNeighbourRealization.{u} M := by
  classical
  obtain ⟨delta0, C3, hdelta0, _, _, hbuild⟩ :=
    source_exists_unselected_nested_fixedTower M hM
  filter_upwards [Ioo_mem_nhdsGT hdelta0] with delta hdelta
  intro iota S T hS hinj hcentred hball hed w hw hwtop
  obtain ⟨Q, hgeometry, hneighbours, _⟩ :=
    hbuild delta hdelta.1 hdelta.2 S T hS hinj hcentred hball hed
  refine ⟨S, Q, le_rfl, hS, hgeometry, hneighbours, ?_⟩
  have hloss : 1 <= sourceTowerSelectionLoss M S.card := by
    unfold sourceTowerSelectionLoss
    apply one_le_pow₀
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact le_mul_of_one_le_left' hloss

end Kakeya.ML2Core
