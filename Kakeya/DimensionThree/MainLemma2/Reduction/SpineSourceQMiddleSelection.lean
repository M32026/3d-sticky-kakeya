/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedPreparation
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceMiddleCaller
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineBridgeAbstractConstant
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineBridgePullbackGrid

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Kakeya.ML2Core Kakeya.ML2Reduction Kakeya.VeryNotSticky
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The parent recursion starts at level b and takes exactly b-a steps. -/
def sourceQAncestor (Q : SourceThreadedTower S T M C) (a b : Nat) (j : iota) : iota :=
  Nat.rec j (fun k x => Q.parent (b - k) x) (b - a)

/-- Assigned fibres, including both endpoints, rather than geometric nodesUnder. -/
theorem sourceQ_ancestor_fibre_identities (Q : SourceThreadedTower S T M C)
    {a b : Nat} (hab : a <= b) (hb : b <= M) :
    (forall i, i ∈ S -> sourceQAncestor Q a b (Q.place b i) = Q.place a i) /\
    (forall j, j ∈ Q.indexSet b -> sourceQAncestor Q a b j ∈ Q.indexSet a) /\
    (forall j, j ∈ Q.indexSet b -> (Q.tube b j).toConvexSpaceBody <=
      (Q.tube a (sourceQAncestor Q a b j)).toConvexSpaceBody) /\
    (forall j, j ∈ Q.indexSet a -> Q.fibre a b j =
      (open scoped Classical in (Q.indexSet b).filter
        (fun k => sourceQAncestor Q a b k = j))) := by
  classical
  have hbody (k k' : Nat) (hk : k = k') (j : iota) :
      (Q.tube k j).carrier = (Q.tube k' j).carrier := by subst k'; rfl
  have hwalk (n : Nat) (hn : n <= b) :
      (forall i, i ∈ S ->
        Nat.rec (Q.place b i) (fun k x => Q.parent (b - k) x) n = Q.place (b - n) i) /\
      (forall j, j ∈ Q.indexSet b ->
        Nat.rec j (fun k x => Q.parent (b - k) x) n ∈ Q.indexSet (b - n)) /\
      (forall j, j ∈ Q.indexSet b -> (Q.tube b j).carrier <=
        (Q.tube (b - n) (Nat.rec j (fun k x => Q.parent (b - k) x) n)).carrier) := by
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨hp, hm, ht⟩ := ih (by omega)
      have hk : b - (n + 1) < M := by omega
      have heq : b - (n + 1) + 1 = b - n := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        simp only [Nat.rec_add_one, hp i hi]
        rw [Q.parent_composition _ hk i hi, heq]
      · intro j hj
        simpa only [Nat.rec_add_one, heq] using
          Q.parent_mem (b - (n + 1)) hk _ (by simpa only [heq] using hm j hj)
      · intro j hj
        exact (ht j hj).trans (by
          have hc := Q.parent_containment (b - (n + 1)) hk _
            (by simpa only [heq] using hm j hj)
          change (Q.tube (b - (n + 1) + 1) _).carrier <=
            (Q.tube (b - (n + 1)) _).carrier at hc
          rw [hbody _ _ heq] at hc
          simpa only [Nat.rec_add_one, heq] using
            hc)
  obtain ⟨hp, hm, ht⟩ := hwalk (b - a) (by omega)
  have heq : b - (b - a) = a := by omega
  simp only [heq] at hp hm ht
  refine ⟨hp, hm, ?_, ?_⟩
  · intro j hj
    have hh := ht j hj
    rw [hbody _ _ heq] at hh
    exact hh
  intro j hj
  ext k
  simp only [SourceThreadedTower.fibre, SourceThreadedTower.cell,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hia⟩, rfl⟩
    exact ⟨Q.place_mem b hb i hi, (hp i hi).trans hia⟩
  · rintro ⟨hk, hka⟩
    obtain ⟨i, hi, rfl⟩ := Q.place_surjective b hb k hk
    exact ⟨i, ⟨hi, (hp i hi).symm.trans hka⟩, rfl⟩

open scoped Classical in
/-- The fixed-Q version of the source's same-tag four-factor selection.
All analytic factor bounds are deliberately absent from this geometric output. -/
structure SourceQMiddleSeam (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (a p b : Nat) (lambda : NNReal) (loss : ENNReal) where
  coarse : Finset iota
  parents : Finset iota
  middle : Finset iota
  ja : iota
  jp : iota
  jb : iota
  fineShade : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))
  middleShade : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3))
  parentShade : iota -> ShadedTube (sourceTowerRadius delta M p) (EuclideanSpace Real (Fin 3))
  outerShade : iota -> ShadedTube (sourceTowerRadius delta M a) (EuclideanSpace Real (Fin 3))
  coarse_subset : coarse <= Q.indexSet a
  parents_subset : parents <= Q.fibre a p ja
  middle_subset : middle <= Q.fibre p b jp
  coarse_member : ja ∈ coarse
  parent_member : jp ∈ parents
  middle_member : jb ∈ middle
  fine_tubes : forall i, (fineShade i).toTube = T i
  middle_tubes : forall i, (middleShade i).toTube = Q.tube b i
  parent_tubes : forall i, (parentShade i).toTube = Q.tube p i
  outer_tubes : forall i, (outerShade i).toTube = Q.tube a i
  fine_subshade : forall i, (fineShade i).shade <= (Z i).shade
  retainedMiddle : Finset iota
  retainedParents : Finset iota
  middleSeed : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3))
  parentSeed : iota -> ShadedTube (sourceTowerRadius delta M p) (EuclideanSpace Real (Fin 3))
  stageLoss : NNReal
  stage_loss_one : 1 <= stageLoss
  stages_paid : (stageLoss : ENNReal) ^ 3 <= loss
  retained_middle_subset : retainedMiddle <= Q.indexSet b
  retained_parents_subset : retainedParents <= Q.indexSet p
  middle_fibre : middle = retainedMiddle.filter (fun j => sourceQAncestor Q p b j = jp)
  parent_fibre : parents = retainedParents.filter (fun j => sourceQAncestor Q a p j = ja)
  middle_seed_tubes : forall j, (middleSeed j).toTube = Q.tube b j
  parent_seed_tubes : forall j, (parentSeed j).toTube = Q.tube p j
  middle_refined : forall j, (middleShade j).shade <= (middleSeed j).shade
  parent_refined : forall j, (parentShade j).shade <= (parentSeed j).shade
  fine_in_middle_seed : forall i, i ∈ S -> Q.place b i ∈ retainedMiddle ->
    (fineShade i).shade <= (middleSeed (Q.place b i)).shade
  middle_in_parent_seed : forall j, j ∈ retainedMiddle ->
    sourceQAncestor Q p b j ∈ retainedParents ->
      (middleShade j).shade <= (parentSeed (sourceQAncestor Q p b j)).shade
  parent_in_outer : forall j, j ∈ retainedParents -> sourceQAncestor Q a p j ∈ coarse ->
    (parentShade j).shade <= (outerShade (sourceQAncestor Q a p j)).shade
  fine_refinement : ShadedBody.IsCRefinement
    (S.filter (fun i => Q.place b i ∈ retainedMiddle))
    (fun i => (fineShade i).toShadedBody) S (fun i => (Z i).toShadedBody) stageLoss⁻¹
  middle_refinement : ShadedBody.IsCRefinement
    (retainedMiddle.filter (fun j => sourceQAncestor Q p b j ∈ retainedParents))
    (fun j => (middleShade j).toShadedBody) retainedMiddle
    (fun j => (middleSeed j).toShadedBody) stageLoss⁻¹
  parent_refinement : ShadedBody.IsCRefinement
    (retainedParents.filter (fun j => sourceQAncestor Q a p j ∈ coarse))
    (fun j => (parentShade j).toShadedBody) retainedParents
    (fun j => (parentSeed j).toShadedBody) stageLoss⁻¹
  refined_middle_mass :
    (∑ i ∈ S.filter (fun i => Q.place b i ∈ middle), volume (fineShade i).shade) =
      ∑ j ∈ middle, ∑ i ∈ Q.cell b j, volume (fineShade i).shade
  complete_middle_leaves :
    (open scoped Classical in S.filter (fun i => Q.place b i ∈ middle)) =
      (open scoped Classical in middle.biUnion (Q.cell b))
  complete_middle_mass :
    (∑ i ∈ (open scoped Classical in S.filter (fun i => Q.place b i ∈ middle)),
      volume (Z i).shade) = ∑ j ∈ middle, ∑ i ∈ Q.cell b j, volume (Z i).shade
  fine_fullness : lambda <= ShadedBody.fullness (Q.cell b jb)
    (fun i => (fineShade i).toShadedBody)
  middle_fullness : lambda <= ShadedBody.fullness middle (fun i => (middleShade i).toShadedBody)
  parent_fullness : lambda <= ShadedBody.fullness parents (fun i => (parentShade i).toShadedBody)
  outer_fullness : lambda <= ShadedBody.fullness coarse (fun i => (outerShade i).toShadedBody)
  card_product : ((Q.cell b jb).card : ENNReal) * (middle.card : ENNReal) *
    (parents.card : ENNReal) * (coarse.card : ENNReal) <= 16 * (S.card : ENNReal)
  split : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <= loss *
    ShadedBody.multiplicity (Q.cell b jb) (fun i => (fineShade i).toShadedBody) *
    ShadedBody.multiplicity middle (fun i => (middleShade i).toShadedBody) *
    ShadedBody.multiplicity parents (fun i => (parentShade i).toShadedBody) *
    ShadedBody.multiplicity coarse (fun i => (outerShade i).toShadedBody)

/-- theta0 is the actual chosen middle/complete-fibre cardinal ratio. -/
noncomputable def SourceQMiddleSeam.theta0 (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a p b : Nat} {lambda : NNReal} {loss : ENNReal}
    (X : SourceQMiddleSeam Q Z a p b lambda loss) : Real :=
  (X.middle.card : Real) / ((Q.fibre p b X.jp).card : Real)

/-- The source's fixed finite product of selection losses, before absorption. -/
noncomputable def sourceQSelectionLoss (K : Nat) (delta : NNReal) : NNReal :=
  Real.toNNReal ((2 + Real.logb 2 (1 / (delta : Real))) ^ K)


/-- Exact original-index normalization, valid for any genuinely contained family. -/
structure SourceQNormalizedRows {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (F : Finset iota)
    (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))) : Prop where
  map_eq : (spineRescaleUnit hsit.pos_ambient T0 hR).toAffineMap = T0.rescaleMap R
  jacobian_eq : affineJacobian (spineRescaleUnit hsit.pos_ambient T0 hR) =
    ENNReal.ofReal ((4 * R)⁻¹ ^ (3 : Nat)) * (b : ENNReal)⁻¹ ^ (2 : Nat)
  jacobian_pos : 0 < affineJacobian (spineRescaleUnit hsit.pos_ambient T0 hR)
  jacobian_finite : affineJacobian (spineRescaleUnit hsit.pos_ambient T0 hR) < (⊤ : ENNReal)
  shade_eq : forall i, i ∈ F -> (outerFamily hsit.pos_ambient T0 hR rho Z i).shade =
    spineRescaleUnit hsit.pos_ambient T0 hR '' (Z i).shade
  mass_eq : forall I : Finset iota, I <= F ->
    (∑ i ∈ I, volume (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) =
      affineJacobian (spineRescaleUnit hsit.pos_ambient T0 hR) *
        ∑ i ∈ I, volume (Z i).shade
  union_eq : forall I : Finset iota, I <= F ->
    volume (⋃ i ∈ I, (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) =
      affineJacobian (spineRescaleUnit hsit.pos_ambient T0 hR) *
        volume (⋃ i ∈ I, (Z i).shade)
  multiplicity_eq : ShadedBody.multiplicity F
    (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) =
      ShadedBody.multiplicity F (fun i => (Z i).toShadedBody)

theorem sourceQ_normalized_rows {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (F : Finset iota)
    (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3)))
    (hratio : (tau : Real) / (b : Real) <= 4 * (rho : Real))
    (hsub : forall i, i ∈ F -> (Z i).carrier <= T0.carrier) :
    SourceQNormalizedRows hsit hR T0 F Z := by
  let A := spineRescaleUnit hsit.pos_ambient T0 hR
  have hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
  have hshade : forall i, i ∈ F ->
      (outerFamily hsit.pos_ambient T0 hR rho Z i).shade = A '' (Z i).shade :=
    outerFamily_shade_eq hn hsit hR hratio hsub
  have hjac : affineJacobian A = ENNReal.ofReal ((4 * R)⁻¹ ^ (3 : Nat)) *
      (b : ENNReal)⁻¹ ^ (2 : Nat) := by
    let B := (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).carrier
    have hB0 : volume B ≠ 0 := ConvexSpaceBody.closedUnitBall_volume_pos.ne'
    have hBt : volume B ≠ ⊤ :=
      (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).isCompact'.measure_lt_top.ne
    apply (ENNReal.mul_left_inj hB0 hBt).mp
    rw [← Kakeya.volume_image_affineEquiv]
    have hm : (A : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin 3)) = T0.rescaleMap R :=
      spineRescaleUnit_coe hsit.pos_ambient T0 hR
    rw [hm, Tube.volume_image_rescaleMap hsit.pos_ambient hR T0 B, hn]
    norm_num [mul_assoc]
  refine {
    map_eq := spineRescaleUnit_toAffineMap hsit.pos_ambient T0 hR
    jacobian_eq := hjac
    jacobian_pos := pos_iff_ne_zero.mpr (Kakeya.affineJacobian_ne_zero A)
    jacobian_finite := lt_top_iff_ne_top.mpr (Kakeya.affineJacobian_ne_top A)
    shade_eq := hshade
    mass_eq := ?_
    union_eq := ?_
    multiplicity_eq := outerFamily_multiplicity hn hsit hR hratio hsub }
  · intro I hI
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hshade i (hI hi)]
    exact Kakeya.volume_image_affineEquiv A _
  · intro I hI
    have heq : (⋃ i ∈ I, (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) =
        A '' (⋃ i ∈ I, (Z i).shade) := by
      simp only [Set.image_iUnion]
      apply Set.iUnion_congr
      intro i
      apply Set.iUnion_congr
      intro hi
      exact hshade i (hI hi)
    rw [heq]
    exact Kakeya.volume_image_affineEquiv A _

end Kakeya.ML2Assembly
