/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon

/-!
# Balanced hierarchy covers for the WZ stopping construction

This module packages one level of a uniform tube hierarchy as balanced parent classes and proves
the partition, cardinality, and cross-level nesting facts used by the WZ dynamic producer.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

open Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- One level of a WZ balanced partitioning cover. The classes are defined by
the assignment function; `branch` and `balance` give their common cardinality
band. -/
structure BalancedNodeCover {ι : Type u} {delta rho : NNReal}
    (s : Finset ι) (T : ι → Tube delta E) (balance : NNReal) where
  parent : Finset ι
  assign : ι → ι
  part : ι → Finset ι
  part_eq : ∀ j, part j = _root_.Tube.coverClass s assign j
  mem_part_iff : ∀ i j, i ∈ part j ↔ i ∈ s ∧ assign i = j
  parentTube : ι → Tube rho E
  branch : NNReal
  assign_mem : ∀ i ∈ s, assign i ∈ parent
  leaf_le_parent : ∀ i ∈ s,
    (T i).toConvexSpaceBody ≤ (parentTube (assign i)).toConvexSpaceBody
  parentTube_injOn : Set.InjOn parentTube (parent : Set ι)
  card_class_le : ∀ j ∈ parent,
    ((part j).card : NNReal) ≤ balance * branch
  le_card_class : ∀ j ∈ parent,
    branch ≤ balance * ((part j).card : NNReal)

namespace BalancedNodeCover

variable {ι : Type u} [DecidableEq ι] {delta rho balance : NNReal} {s : Finset ι}
  {T : ι → Tube delta E}

/-- The assignment classes of a balanced cover exactly cover the leaf family. -/
theorem biUnion_coverClass (B : BalancedNodeCover (rho := rho) s T balance) :
    B.parent.biUnion B.part = s := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hi
    exact (B.mem_part_iff i j).mp hi |>.1
  · intro i hi
    exact Finset.mem_biUnion.mpr
      ⟨B.assign i, B.assign_mem i hi, (B.mem_part_iff i (B.assign i)).mpr ⟨hi, rfl⟩⟩

/-- Different parents have disjoint assignment classes. -/
theorem pairwiseDisjoint_coverClass (B : BalancedNodeCover (rho := rho) s T balance) :
    ((B.parent : Finset ι) : Set ι).PairwiseDisjoint B.part := by
  intro j _ j' _ hjj'
  rw [Function.onFun, Finset.disjoint_left]
  intro i hi hi'
  exact hjj' (((B.mem_part_iff i j).mp hi).2.symm.trans
    ((B.mem_part_iff i j').mp hi').2)

/-- A nonempty leaf family gives nonempty parent classes. This follows only
from the two-sided balance bracket, including the zero-branch edge case. -/
theorem coverClass_nonempty (B : BalancedNodeCover (rho := rho) s T balance)
    (hs : s.Nonempty) {j : ι} (hj : j ∈ B.parent) :
    (B.part j).Nonempty := by
  classical
  by_contra hne
  have hcls0 : B.part j = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hne
  have hbranch0 : B.branch = 0 := by
    have hle := B.le_card_class j hj
    rw [hcls0] at hle
    apply le_antisymm
    · simpa [hcls0] using hle
    · exact bot_le
  obtain ⟨i, hi⟩ := hs
  have hp := B.assign_mem i hi
  have hu := B.card_class_le (B.assign i) hp
  rw [hbranch0, mul_zero] at hu
  have hzero : B.part (B.assign i) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact Nat.eq_zero_of_le_zero (by simpa [hbranch0] using hu)
  have himem : i ∈ B.part (B.assign i) := by
    exact (B.mem_part_iff i (B.assign i)).mpr ⟨hi, rfl⟩
  simpa [hzero] using himem

/-- Cardinality of the leaf family is the sum of the balanced classes. -/
theorem card_eq_sum_card_coverClass (B : BalancedNodeCover (rho := rho) s T balance) :
    s.card = ∑ j ∈ B.parent, (B.part j).card := by
  calc
    s.card = (B.parent.biUnion B.part).card :=
      congrArg Finset.card B.biUnion_coverClass.symm
    _ = ∑ j ∈ B.parent, (B.part j).card :=
      Finset.card_biUnion B.pairwiseDisjoint_coverClass

/-- The upper cardinality comparison for a balanced partitioning cover. -/
theorem card_le_balance_mul_parent_card_mul_branch
    (B : BalancedNodeCover (rho := rho) s T balance) :
    (s.card : NNReal) ≤ balance * (B.parent.card : NNReal) * B.branch := by
  rw [show (s.card : NNReal) = ∑ j ∈ B.parent, ((B.part j).card : NNReal) by
    exact_mod_cast B.card_eq_sum_card_coverClass]
  calc
    (∑ j ∈ B.parent, ((B.part j).card : NNReal)) ≤
        ∑ j ∈ B.parent, balance * B.branch :=
      Finset.sum_le_sum fun j hj => B.card_class_le j hj
    _ = balance * (B.parent.card : NNReal) * B.branch := by
      rw [Finset.sum_const]
      simp
      ring

/-- The lower cardinality comparison for a balanced partitioning cover. -/
theorem parent_card_mul_branch_le_balance_mul_card
    (B : BalancedNodeCover (rho := rho) s T balance) :
    (B.parent.card : NNReal) * B.branch ≤ balance * (s.card : NNReal) := by
  rw [show (s.card : NNReal) = ∑ j ∈ B.parent, ((B.part j).card : NNReal) by
    exact_mod_cast B.card_eq_sum_card_coverClass]
  calc
    (B.parent.card : NNReal) * B.branch =
        ∑ j ∈ B.parent, B.branch := by rw [Finset.sum_const]; simp
    _ ≤ ∑ j ∈ B.parent, balance * ((B.part j).card : NNReal) :=
      Finset.sum_le_sum fun j hj => B.le_card_class j hj
    _ = balance * ∑ j ∈ B.parent, ((B.part j).card : NNReal) := by
      rw [Finset.mul_sum]

end BalancedNodeCover

/-- Every level of a `_root_.Tube.UniformTubeSet` is a source-style balanced partitioning
cover, with exactly the hierarchy's balance and branching constants. -/
def balancedNodeCoverOfUniformTubeSet {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι → Tube delta E} {N : ℕ} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (k : ℕ) (hk : k ≤ N) :
    BalancedNodeCover (rho := _root_.Tube.gridScale delta N k) s T C where
  parent := U.cover.indexSet k
  assign := U.cover.assign k
  part := fun j => _root_.Tube.coverClass s (U.cover.assign k) j
  part_eq := fun _ => rfl
  mem_part_iff := fun i j => by
    classical
    simp [_root_.Tube.coverClass]
  parentTube := U.cover.tube k
  branch := U.branchingN k
  assign_mem i hi := U.cover.assign_mem k hk i hi
  leaf_le_parent i hi := U.cover.le_tube_assign k hk i hi
  parentTube_injOn := U.tube_injOn k hk
  card_class_le j hj := U.card_class_le k hk j hj
  le_card_class j hj := U.le_card_class k hk j hj

/-- Fine assignment classes refine coarse assignment classes. -/
theorem coverClass_subset_of_uniform_levels {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι → Tube delta E} {N : ℕ} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (i : ι) (hi : i ∈ s) :
    _root_.Tube.coverClass s (U.cover.assign b) (U.cover.assign b i) ⊆
      _root_.Tube.coverClass s (U.cover.assign a) (U.cover.assign a i) := by
  classical
  intro i' hi'
  rw [_root_.Tube.coverClass, Finset.mem_filter] at hi' ⊢
  refine ⟨hi'.1, ?_⟩
  exact U.cover.assign_eq_of_le hab hb hi'.1 hi
    (hi'.2.trans rfl)

/-- Node containment iterated across arbitrary grid levels. -/
theorem node_le_node_of_uniform_levels {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι → Tube delta E} {N : ℕ} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (i : ι) (hi : i ∈ s) :
    (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody ≤
      (U.cover.tube a (U.cover.assign a i)).toConvexSpaceBody := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (U.cover.tube_nested b (by omega) i hi).trans (ih (by omega))

/-- Every fine parent has an actual coarse parent; its full fine assignment
class refines the coarse class, and the fine node lies in that coarse node. -/
theorem exists_coarse_parent_of_fine_parent {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι → Tube delta E} {N : ℕ} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) {j : ι}
    (hj : j ∈ U.cover.indexSet b) :
    ∃ q ∈ U.cover.indexSet a,
      _root_.Tube.coverClass s (U.cover.assign b) j ⊆
        _root_.Tube.coverClass s (U.cover.assign a) q ∧
      (U.cover.tube b j).toConvexSpaceBody ≤
        (U.cover.tube a q).toConvexSpaceBody := by
  classical
  obtain ⟨i, hi⟩ :=
    _root_.Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent U hb hs hj
  have hi' := Finset.mem_filter.mp hi
  let q := U.cover.assign a i
  refine ⟨q, U.cover.assign_mem a (hab.trans hb) i hi'.1, ?_, ?_⟩
  · intro i' hi''
    rw [_root_.Tube.coverClass, Finset.mem_filter] at hi'' ⊢
    refine ⟨hi''.1, ?_⟩
    exact U.cover.assign_eq_of_le hab hb hi''.1 hi'.1
      (hi''.2.trans hi'.2.symm)
  · simpa only [hi'.2] using node_le_node_of_uniform_levels U hab hb i hi'.1

end

end Kakeya.WangZahl
