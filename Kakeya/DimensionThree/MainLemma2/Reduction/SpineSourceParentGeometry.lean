/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParentData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

def SourceQParentAdmissible (Q : SourceThreadedTower S T M C)
    (etaParent : Real) (a p : Nat) : Prop :=
  forall j, j ∈ Q.indexSet a ->
    Kakeya.maxDensity (Q.fibre a p j) (fun k => (Q.tube p k).toConvexSpaceBody) <=
      (delta : ENNReal) ^ (-2 * etaParent)

open scoped Classical in
/-- The maximal admissible index before this exact finite source window. -/
noncomputable def sourceQGenuineParent (Q : SourceThreadedTower S T M C)
    (etaParent e : Real) (a b : Nat) : Nat :=
  ((Finset.range (M + 1)).filter (fun p => a <= p /\
    (forall m, SourceTowerWindow delta M e a b m -> p < m) /\
    SourceQParentAdmissible Q etaParent a p)).sup id

noncomputable def sourceQTransverseFloor (Q : SourceThreadedTower S T M C)
    {e bias : Real} {a b : Nat} (B : SourceJointWindowFactors Q e a b bias) : ENNReal :=
  (sourceParentWindow delta M e a b).inf (fun m => (B.middle m : ENNReal))

noncomputable def sourceQTransverseParent (delta : NNReal) (M : Nat) (B : ENNReal) : Nat :=
  sInf {q : Nat | q <= M /\ (sourceTowerRadius delta M q : ENNReal) <= B}

open scoped Classical in
/-- Charge actual q-cells to factors, with the convex test-body comparison needed
for maximal-density transfer. A charge map without the test-volume row is insufficient. -/
structure SourceParentDensityTransfer (Q : SourceThreadedTower S T M C)
    {a m : Nat} {j : iota} {bias : Real}
    (B : SourceParentBiasedFactors Q a m j bias) (q : Nat) where
  charge : iota -> Finset iota
  testBody : ConvexSpaceBody (EuclideanSpace Real (Fin 3)) ->
    ConvexSpaceBody (EuclideanSpace Real (Fin 3))
  geometryConstant : NNReal
  outerConstant : ENNReal
  ratioFloor : NNReal
  geometry_one_le : 1 <= geometryConstant
  ratio_positive : 0 < ratioFloor
  ratio_le_one : ratioFloor <= 1
  outer_finite : outerConstant < ⊤
  charge_mem : forall jp, jp ∈ Q.fibre a q j -> charge jp ∈ B.partition.parts
  convex_test_containment : forall V : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
    forall jp, jp ∈ Q.fibre a q j -> (Q.tube q jp).toConvexSpaceBody <= V ->
      (charge jp).convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody) <= testBody V
  charge_mass : forall part, part ∈ B.partition.parts ->
    (∑ jp ∈ (Q.fibre a q j).filter (fun jp => charge jp = part), volume (Q.tube q jp).carrier) <=
      (geometryConstant : ENNReal) *
        volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier
  test_volume : forall V : ConvexSpaceBody (EuclideanSpace Real (Fin 3)),
    volume (testBody V).carrier <= (geometryConstant : ENNReal) * volume V.carrier
  ratio_floor : forall part, part ∈ B.partition.parts ->
    (ratioFloor : ENNReal) <=
      volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
        volume (ML2Assembly.sourceAffineReference B.normalization).carrier
  outer_constant_eq : outerConstant =
    (nonempty_biasedFactorization.C 3 bias : ENNReal) * (ratioFloor : ENNReal) ^ (-bias)
  outer_density : ConvexSpaceBody.IsKatzTao B.partition.parts
    (fun part => part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)) outerConstant

open scoped Classical in
/-- The new p-cell factorization uses its actual cells. Its paid capture retains
the a-to-p volume ratio even when the selected parts are newly factored. -/
structure SourceReparentedFactors (Q : SourceThreadedTower S T M C)
    (a p m : Nat) (j jp : iota) (bias : Real)
    (B : SourceParentBiasedFactors Q a m j bias) where
  factor : SourceParentBiasedFactors Q p m jp bias
  old_part : iota -> Finset iota
  old_part_mem : forall i, i ∈ Q.fibre p m jp -> old_part i ∈ B.partition.parts
  old_part_contains : forall i, i ∈ Q.fibre p m jp -> i ∈ old_part i
  inherited_cells : Q.fibre p m jp =
    B.partition.parts.biUnion (fun part => part ∩ Q.fibre p m jp)
  coarse_parent : jp ∈ Q.fibre a p j
  reference_containment : (Q.tube p jp).toConvexSpaceBody <= (Q.tube a j).toConvexSpaceBody
  parent_volume_positive : 0 < volume (Q.tube p jp).carrier
  parent_volume_finite : volume (Q.tube p jp).carrier < ⊤
  coarse_volume_positive : 0 < volume (Q.tube a j).carrier
  coarse_volume_finite : volume (Q.tube a j).carrier < ⊤
  parentVolumeRatio : ENNReal
  ratio_eq : parentVolumeRatio = volume (Q.tube a j).carrier / volume (Q.tube p jp).carrier
  ratio_one_le : 1 <= parentVolumeRatio
  ratio_finite : parentVolumeRatio < ⊤
  captureConstant : ENNReal
  constant_eq : captureConstant = (nonempty_biasedFactorization.C 3 bias : ENNReal) *
    (factor.comparison : ENNReal) ^ bias * parentVolumeRatio ^ bias
  constant_positive : 0 < captureConstant
  constant_finite : captureConstant < ⊤
  transverseComparison : NNReal
  transverse_comparison_one_le : 1 <= transverseComparison
  transverse_lower : forall part, part ∈ factor.partition.parts ->
    (sourceTowerRadius delta M p : ENNReal) <= (transverseComparison : ENNReal) *
      ethickness Real
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1
  capture_paid : forall part, part ∈ factor.partition.parts ->
    captureConstant⁻¹ *
      (volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
        volume (Q.tube p jp).carrier) ^ bias *
      Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) <=
      Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody)
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody))

/-- The geometric parent contains the previously missing coarseness and density
comparisons as outputs. Every transverse inequality refers to an actual used hull. -/
structure SourceActualParent (Q : SourceThreadedTower S T M C)
    {e bias : Real} {a b : Nat} (B : SourceJointWindowFactors Q e a b bias)
    (etaParent tau : Real) (transverseCap : NNReal) where
  window_nonempty : (sourceParentWindow delta M e a b).Nonempty
  low : Nat
  low_eq : low = (sourceParentWindow delta M e a b).min' window_nonempty
  transverse : Nat
  transverse_eq : transverse = sourceQTransverseParent delta M (sourceQTransverseFloor Q B)
  coarse_transverse : a <= transverse
  transverse_before_window : transverse < low
  transverse_scale : (sourceTowerRadius delta M transverse : ENNReal) <= sourceQTransverseFloor Q B
  coarse_floor : (sourceTowerRadius delta M (low - 1) : ENNReal) <= sourceQTransverseFloor Q B
  strict_coarse : forall k, k < a -> sourceQTransverseFloor Q B <
    (sourceTowerRadius delta M k : ENNReal)
  density_level : Nat
  density_level_in_window : SourceTowerWindow delta M e a b density_level
  transfer : forall j, forall hj : j ∈ Q.indexSet a,
    SourceParentDensityTransfer Q (B.factor density_level density_level_in_window j hj) transverse
  transfer_payment : forall j, forall hj : j ∈ Q.indexSet a,
    ((transfer j hj).geometryConstant : ENNReal) ^ 2 * (transfer j hj).outerConstant <=
      (delta : ENNReal) ^ (-2 * etaParent)
  transverse_admissible : SourceQParentAdmissible Q etaParent a transverse
  parent : Nat
  parent_eq : parent = sourceQGenuineParent Q etaParent e a b
  coarse_le_parent : a <= parent
  parent_before_window : forall m, SourceTowerWindow delta M e a b m -> parent < m
  parent_bound : parent <= M
  parent_admissible : SourceQParentAdmissible Q etaParent a parent
  maximal : forall q, a <= q -> q <= M ->
    (forall m, SourceTowerWindow delta M e a b m -> q < m) ->
    SourceQParentAdmissible Q etaParent a q -> q <= parent
  transverse_le_parent : transverse <= parent
  transverse_all_factors : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a, forall part,
    part ∈ (B.factor m hm j hj).partition.parts ->
      (sourceTowerRadius delta M parent : ENNReal) <= ethickness Real
        (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1
  reparented : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a, forall jp, jp ∈ Q.fibre a parent j ->
      SourceReparentedFactors Q a parent m j jp bias (B.factor m hm j hj)
  reparented_comparison : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a,
    forall jp, forall hjp : jp ∈ Q.fibre a parent j,
      (reparented m hm j hj jp hjp).transverseComparison <= transverseCap
  reparented_transverse : forall m, forall hm : SourceTowerWindow delta M e a b m,
    forall j, forall hj : j ∈ Q.indexSet a,
    forall jp, forall hjp : jp ∈ Q.fibre a parent j, forall part,
    part ∈ (reparented m hm j hj jp hjp).factor.partition.parts ->
      (sourceTowerRadius delta M parent : ENNReal) <= (transverseCap : ENNReal) *
        ethickness Real
          (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier 1
  counted_floor : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q.indexSet a -> forall jp, jp ∈ Q.fibre a parent j ->
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^ (tau / 2) *
        (delta : Real) ^ (4 * etaParent) / (24 * 300 ^ 9 * (C : Real))) *
        ((sourceTowerRadius delta M parent : Real) / (sourceTowerRadius delta M m : Real)) ^ 2 <=
          ((Q.fibre parent m jp).card : Real)
  floor_payment : forall m, SourceTowerWindow delta M e a b m ->
    ((sourceTowerRadius delta M parent : Real) / (sourceTowerRadius delta M m : Real)) ^
      (4 * (tau / 16)) <=
        ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M m : Real)) ^ (tau / 2) *
          (delta : Real) ^ (4 * etaParent) / (24 * 300 ^ 9 * (C : Real))
  floor : forall m, SourceTowerWindow delta M e a b m ->
    forall j, j ∈ Q.indexSet a -> forall jp, jp ∈ Q.fibre a parent j ->
      ((sourceTowerRadius delta M parent : Real) / (sourceTowerRadius delta M m : Real)) ^
        (2 + 4 * (tau / 16)) <= ((Q.fibre parent m jp).card : Real)

/-- The displayed charge and test-volume rows imply the maximal-density comparison. -/
theorem source_parent_density_from_charge
    (Q : SourceThreadedTower S T M C) {a m q : Nat} {j : iota} {bias : Real}
    (B : SourceParentBiasedFactors Q a m j bias)
    (D : SourceParentDensityTransfer Q B q) :
    Kakeya.maxDensity (Q.fibre a q j) (fun i => (Q.tube q i).toConvexSpaceBody) <=
      (D.geometryConstant : ENNReal) ^ 2 * D.outerConstant := by
  classical
  rw [Kakeya.maxDensity_le_iff]
  intro V
  rw [Kakeya.densityIn_le_iff]
  let U := (Q.fibre a q j).filter (fun i => (Q.tube q i).toConvexSpaceBody <= V)
  let H := fun part : Finset iota =>
    part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)
  let parts := B.partition.parts.filter (fun part => H part <= D.testBody V)
  have hmap : forall i, i ∈ U -> D.charge i ∈ parts := by
    intro i hi
    obtain ⟨hi, hV⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨D.charge_mem i hi,
      D.convex_test_containment V i hi hV⟩
  have hcharge : (∑ i ∈ U, volume (Q.tube q i).carrier) <=
      (D.geometryConstant : ENNReal) * ∑ part ∈ parts, volume (H part).carrier := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap, Finset.mul_sum]
    refine Finset.sum_le_sum fun part hpart => ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by simp))
      (D.charge_mass part (Finset.mem_filter.mp hpart).1)
    intro i hi
    obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, heq⟩
  have houter : (∑ part ∈ parts, volume (H part).carrier) <=
      D.outerConstant * volume (D.testBody V).carrier := by
    exact (Kakeya.densityIn_le_iff _ _ _ _).mp
      ((Kakeya.le_maxDensity _ _ _).trans D.outer_density)
  calc
    (∑ i ∈ (Q.fibre a q j).filter (fun i => (Q.tube q i).toConvexSpaceBody <= V),
        volume (Q.tube q i).carrier) <=
        (D.geometryConstant : ENNReal) * ∑ part ∈ parts, volume (H part).carrier := hcharge
    _ <= (D.geometryConstant : ENNReal) *
        (D.outerConstant * volume (D.testBody V).carrier) := mul_le_mul_right houter _
    _ <= (D.geometryConstant : ENNReal) *
        (D.outerConstant * ((D.geometryConstant : ENNReal) * volume V.carrier)) :=
      mul_le_mul_right (mul_le_mul_right (D.test_volume V) _) _
    _ = (D.geometryConstant : ENNReal) ^ 2 * D.outerConstant * volume V.carrier := by ring

/-- Biased capture is converted to the exact charged fill condition.
This is the source-Q counterpart of B24:113; the volume-ratio power remains. -/
theorem source_parent_fill_from_paid_capture
    (Q : SourceThreadedTower S T M C) {a p m : Nat} {j jp : iota} {bias : Real}
    (B : SourceParentBiasedFactors Q a m j bias)
    (P : SourceReparentedFactors Q a p m j jp bias B)
    {part : Finset iota} (hpart : part ∈ P.factor.partition.parts)
    {kappa : ENNReal} (hkappa : kappa < ⊤) (hbias : 0 < bias)
    (hbudget : kappa * P.captureConstant <=
      (volume (part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)).carrier /
        volume (Q.tube p jp).carrier) ^ (1 + bias)) :
    kappa * Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) <=
      Kakeya.densityIn (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody)
        (Q.tube p jp).toConvexSpaceBody := by
  classical
  let W := part.convexHull_biUnion (fun i => (Q.tube m i).toConvexSpaceBody)
  let r : ENNReal := volume W.carrier / volume (Q.tube p jp).carrier
  have hr0 : r ≠ 0 := ENNReal.div_ne_zero.mpr
    ⟨(P.factor.hull_positive part hpart).ne', P.parent_volume_finite.ne⟩
  have hrtop : r ≠ ⊤ := ENNReal.div_ne_top
    W.isCompact.measure_ne_top P.parent_volume_positive.ne'
  have hpow : r ^ bias * r = r ^ (1 + bias) := by
    rw [add_comm, ENNReal.rpow_add bias 1 hr0 hrtop, ENNReal.rpow_one]
  have hk : kappa <= P.captureConstant⁻¹ * r ^ (1 + bias) := by
    calc
      kappa = P.captureConstant⁻¹ * (kappa * P.captureConstant) := by
        rw [show P.captureConstant⁻¹ * (kappa * P.captureConstant) =
          (P.captureConstant⁻¹ * P.captureConstant) * kappa by ring,
          ENNReal.inv_mul_cancel P.constant_positive.ne' P.constant_finite.ne, one_mul]
      _ <= P.captureConstant⁻¹ * r ^ (1 + bias) := mul_le_mul_right hbudget _
  have hcontained : forall i, i ∈ Q.fibre p m jp ->
      (Q.tube m i).toConvexSpaceBody <= (Q.tube p jp).toConvexSpaceBody := by
    intro i hi
    obtain ⟨part', hpart', hi'⟩ := P.factor.partition.exists_mem hi
    exact (Finset.le_convexHull_biUnion _ hi').trans (P.factor.hull_contained part' hpart')
  have hsum : Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody) W *
      volume W.carrier <= ∑ i ∈ Q.fibre p m jp, volume (Q.tube m i).carrier := by
    rw [← Kakeya.sum_volume_eq_densityIn_mul_volume]
    exact Finset.sum_le_sum_of_subset
      ((Finset.filter_subset _ _).trans (P.factor.partition.subset hpart))
  rw [Kakeya.densityIn_of_all_le hcontained,
    ENNReal.le_div_iff_mul_le (.inl P.parent_volume_positive.ne')
      (.inl P.parent_volume_finite.ne)]
  calc
    kappa * Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) *
        volume (Q.tube p jp).carrier <=
        (P.captureConstant⁻¹ * r ^ (1 + bias)) *
          Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody) *
            volume (Q.tube p jp).carrier := mul_le_mul_left (mul_le_mul_left hk _) _
    _ = (P.captureConstant⁻¹ * r ^ bias *
        Kakeya.maxDensity (Q.fibre p m jp) (fun i => (Q.tube m i).toConvexSpaceBody)) *
          (r * volume (Q.tube p jp).carrier) := by rw [← hpow]; ring
    _ <= Kakeya.densityIn part (fun i => (Q.tube m i).toConvexSpaceBody) W *
        volume W.carrier := mul_le_mul' (P.capture_paid part hpart)
          (ENNReal.mul_le_of_le_div le_rfl)
    _ <= ∑ i ∈ Q.fibre p m jp, volume (Q.tube m i).carrier := hsum

end Kakeya.ML2Core
