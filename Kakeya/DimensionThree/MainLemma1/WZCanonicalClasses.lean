/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.WZBalancedCover
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# Canonical hierarchy classes for the WZ rho selection

This module partitions a retained family of fine hierarchy nodes by the assignment ancestor map.
Unlike `UniformTubeSet.nodesUnder`, these classes are disjoint by construction.  The geometric
containment of every class member in its assigned ancestor is proved separately.
-/

@[expose] public section

namespace Kakeya.WangZahl

noncomputable section

open Tube

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The retained fine nodes canonically assigned to the coarse node `p`. -/
def tauAncestorClass {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι)
    (p : ι) : Finset ι :=
  open scoped Classical in
  tauNodes.filter fun w => U.nodeAncestor b a w = p

/-- The coarse parents used by a retained fine-node family. -/
def activeRhoParents {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat)
    (tauNodes : Finset ι) : Finset ι :=
  open scoped Classical in
  tauNodes.image (U.nodeAncestor b a)

@[simp] theorem mem_tauAncestorClass {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) (p w : ι) :
    w ∈ tauAncestorClass U b a tauNodes p ↔
      w ∈ tauNodes ∧ U.nodeAncestor b a w = p := by
  classical
  simp [tauAncestorClass]

open scoped Classical in
/-- The canonical classes exactly partition the retained fine-node family. -/
theorem biUnion_tauAncestorClass {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) :
    (activeRhoParents U b a tauNodes).biUnion (tauAncestorClass U b a tauNodes) = tauNodes := by
  apply Finset.Subset.antisymm
  · intro w hw
    obtain ⟨p, _hp, hwp⟩ := Finset.mem_biUnion.mp hw
    exact (mem_tauAncestorClass U b a tauNodes p w).mp hwp |>.1
  · intro w hw
    exact Finset.mem_biUnion.mpr ⟨U.nodeAncestor b a w, Finset.mem_image_of_mem _ hw,
      (mem_tauAncestorClass U b a tauNodes _ _).mpr ⟨hw, rfl⟩⟩

/-- Distinct active coarse parents have disjoint canonical classes. -/
theorem pairwiseDisjoint_tauAncestorClass {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) :
    ((activeRhoParents U b a tauNodes : Finset ι) : Set ι).PairwiseDisjoint
      (tauAncestorClass U b a tauNodes) := by
  classical
  intro p _hp q _hq hpq
  rw [Function.onFun, Finset.disjoint_left]
  intro w hwp hwq
  have hp := (mem_tauAncestorClass U b a tauNodes p w).mp hwp |>.2
  have hq := (mem_tauAncestorClass U b a tauNodes q w).mp hwq |>.2
  exact hpq (hp.symm.trans hq)

open scoped Classical in
/-- The retained fine-node count is the exact sum of its canonical coarse-parent classes. -/
theorem card_eq_sum_card_tauAncestorClass {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) :
    tauNodes.card = ∑ p ∈ activeRhoParents U b a tauNodes,
      (tauAncestorClass U b a tauNodes p).card := by
  calc
    tauNodes.card =
        ((activeRhoParents U b a tauNodes).biUnion
          (tauAncestorClass U b a tauNodes)).card :=
      congrArg Finset.card (biUnion_tauAncestorClass U b a tauNodes).symm
    _ = ∑ p ∈ activeRhoParents U b a tauNodes,
        (tauAncestorClass U b a tauNodes p).card :=
      Finset.card_biUnion (pairwiseDisjoint_tauAncestorClass U b a tauNodes)

/-- Every active coarse parent has a nonempty canonical class. -/
theorem tauAncestorClass_nonempty {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) {p : ι}
    (hp : p ∈ activeRhoParents U b a tauNodes) :
    (tauAncestorClass U b a tauNodes p).Nonempty := by
  classical
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨w, (mem_tauAncestorClass U b a tauNodes _ _).mpr ⟨hw, rfl⟩⟩

/-- Active coarse parents are honest nodes of the hierarchy. -/
theorem activeRhoParents_subset_indexSet {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (ha : a <= N) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b) :
    activeRhoParents U b a tauNodes ⊆ U.cover.indexSet a := by
  classical
  intro p hp
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
  exact U.nodeAncestor_mem ha hb hs (htau hw)

/-- Every fine node in a canonical class lies in the assigned coarse parent node. -/
theorem tauAncestorClass_tube_le_parent {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b) {p w : ι}
    (hw : w ∈ tauAncestorClass U b a tauNodes p) :
    (U.cover.tube b w).toConvexSpaceBody <= (U.cover.tube a p).toConvexSpaceBody := by
  have hmem := (mem_tauAncestorClass U b a tauNodes p w).mp hw
  simpa [hmem.2] using U.tube_le_tube_nodeAncestor hab hb hs (htau hmem.1)

/-- Following the fine node assigned to a leaf gives that leaf's coarse assignment. -/
theorem nodeAncestor_assign_eq {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) {i : ι} (hi : i ∈ s) :
    U.nodeAncestor b a (U.cover.assign b i) = U.cover.assign a i := by
  obtain ⟨i', hi', hbi', hanc⟩ := U.exists_nodeAncestor_witness hb hs
    (U.cover.assign_mem b hb i hi)
  rw [hanc]
  exact U.cover.assign_eq_of_le hab hb hi' hi hbi'

open scoped Classical in
/-- A coarse leaf-class is the disjoint union of the fine leaf-classes of its canonical children. -/
theorem coverClass_eq_biUnion_tauAncestorClass {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) (p : ι) :
    _root_.Tube.coverClass s (U.cover.assign a) p =
      (tauAncestorClass U b a (U.cover.indexSet b) p).biUnion
        (fun w => _root_.Tube.coverClass s (U.cover.assign b) w) := by
  apply Finset.Subset.antisymm
  · intro i hi
    have hi' := Finset.mem_filter.mp hi
    refine Finset.mem_biUnion.mpr ⟨U.cover.assign b i, ?_, ?_⟩
    · exact (mem_tauAncestorClass U b a _ _ _).mpr
        ⟨U.cover.assign_mem b hb i hi'.1, (nodeAncestor_assign_eq U hs hab hb hi'.1).trans hi'.2⟩
    · exact Finset.mem_filter.mpr ⟨hi'.1, rfl⟩
  · intro i hi
    obtain ⟨w, hw, hiw⟩ := Finset.mem_biUnion.mp hi
    have hw' := (mem_tauAncestorClass U b a _ p w).mp hw
    have hiw' := Finset.mem_filter.mp hiw
    refine Finset.mem_filter.mpr ⟨hiw'.1, ?_⟩
    have hanc := nodeAncestor_assign_eq U hs hab hb hiw'.1
    rw [hiw'.2] at hanc
    exact hanc.symm.trans hw'.2

/-- Fine leaf-classes belonging to distinct canonical children are disjoint. -/
theorem pairwiseDisjoint_fine_coverClass {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (p : ι) :
    ((tauAncestorClass U b a (U.cover.indexSet b) p : Finset ι) : Set ι).PairwiseDisjoint
      (fun w => _root_.Tube.coverClass s (U.cover.assign b) w) := by
  classical
  intro w _hw w' _hw' hww'
  rw [Function.onFun, Finset.disjoint_left]
  intro i hi hi'
  exact hww' ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hi').2)

open scoped Classical in
/-- Exact leaf-count decomposition over the canonical children of a coarse parent. -/
theorem card_coverClass_eq_sum_canonical_children {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) (p : ι) :
    (_root_.Tube.coverClass s (U.cover.assign a) p).card =
      ∑ w ∈ tauAncestorClass U b a (U.cover.indexSet b) p,
        (_root_.Tube.coverClass s (U.cover.assign b) w).card := by
  rw [coverClass_eq_biUnion_tauAncestorClass U hs hab hb p]
  exact Finset.card_biUnion (pairwiseDisjoint_fine_coverClass U b a p)

/-- Pure arithmetic adapter for the two branching inequalities supplied by a producer. -/
theorem card_le_mul_of_branching_bounds {C Bfine Bcoarse x y : NNReal}
    (hB : 0 < Bfine) (hx : x * Bfine <= C ^ 2 * Bcoarse)
    (hy : Bcoarse <= C ^ 2 * (y * Bfine)) :
    x <= C ^ 4 * y := by
  apply le_of_mul_le_mul_right _ hB
  calc
    x * Bfine <= C ^ 2 * Bcoarse := hx
    _ <= C ^ 2 * (C ^ 2 * (y * Bfine)) := mul_le_mul_right hy _
    _ = (C ^ 4 * y) * Bfine := by ring

/-- Sum a lower class-size bracket and an upper bound for the total size. -/
theorem card_mul_le_sq_mul_of_sum_bounds {ι : Type*}
    {u : Finset ι} {size : ι -> NNReal} {total C Bfine Bcoarse : NNReal}
    (hsum : total = ∑ i ∈ u, size i)
    (hlower : ∀ i ∈ u, Bfine <= C * size i)
    (hupper : total <= C * Bcoarse) :
    (u.card : NNReal) * Bfine <= C ^ 2 * Bcoarse := by
  calc
    (u.card : NNReal) * Bfine = ∑ _i ∈ u, Bfine := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ i ∈ u, C * size i := Finset.sum_le_sum hlower
    _ = C * total := by rw [← Finset.mul_sum, ← hsum]
    _ <= C * (C * Bcoarse) := mul_le_mul_right hupper C
    _ = C ^ 2 * Bcoarse := by ring

/-- Sum an upper class-size bracket and a lower bound for the total size. -/
theorem coarse_le_sq_mul_card_of_sum_bounds {ι : Type*}
    {u : Finset ι} {size : ι -> NNReal} {total C Bfine Bcoarse : NNReal}
    (hsum : total = ∑ i ∈ u, size i)
    (hupper : ∀ i ∈ u, size i <= C * Bfine)
    (hlower : Bcoarse <= C * total) :
    Bcoarse <= C ^ 2 * ((u.card : NNReal) * Bfine) := by
  calc
    Bcoarse <= C * total := hlower
    _ = C * ∑ i ∈ u, size i := by rw [hsum]
    _ <= C * ∑ _i ∈ u, C * Bfine := by
      exact mul_le_mul_right (Finset.sum_le_sum hupper) C
    _ = C ^ 2 * ((u.card : NNReal) * Bfine) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Number of full level-`b` hierarchy nodes canonically assigned to `p` at level `a`. -/
def canonicalChildCount {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (p : ι) : NNReal :=
  (tauAncestorClass U b a (U.cover.indexSet b) p).card

open scoped Classical in
/-- `NNReal` form of the exact leaf-count decomposition over canonical children. -/
theorem coe_card_coverClass_eq_sum_canonical_children {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) (p : ι) :
    ((_root_.Tube.coverClass s (U.cover.assign a) p).card : NNReal) =
      ∑ w ∈ tauAncestorClass U b a (U.cover.indexSet b) p,
        ((_root_.Tube.coverClass s (U.cover.assign b) w).card : NNReal) := by
  have h := congrArg (fun n : Nat => (n : NNReal))
    (card_coverClass_eq_sum_canonical_children U hs hab hb p)
  simpa [Nat.cast_sum] using h

/-- Upper branching bound for the canonical children of one full hierarchy parent. -/
theorem canonicalChildCount_mul_branching_le {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) {p : ι} (hp : p ∈ U.cover.indexSet a) :
    canonicalChildCount U b a p * U.branchingN b <= C ^ 2 * U.branchingN a := by
  classical
  apply card_mul_le_sq_mul_of_sum_bounds
      (total := ((_root_.Tube.coverClass s (U.cover.assign a) p).card : NNReal))
      (size := fun w => ((_root_.Tube.coverClass s (U.cover.assign b) w).card : NNReal))
  · exact coe_card_coverClass_eq_sum_canonical_children U hs hab hb p
  · intro w hw
    exact U.le_card_class b hb w ((mem_tauAncestorClass U b a _ p w).mp hw).1
  · exact U.card_class_le a (hab.trans hb) p hp

/-- Lower branching bound for the canonical children of one full hierarchy parent. -/
theorem branching_le_canonicalChildCount_mul {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) {p : ι} (hp : p ∈ U.cover.indexSet a) :
    U.branchingN a <= C ^ 2 * (canonicalChildCount U b a p * U.branchingN b) := by
  classical
  apply coarse_le_sq_mul_card_of_sum_bounds
      (total := ((_root_.Tube.coverClass s (U.cover.assign a) p).card : NNReal))
      (size := fun w => ((_root_.Tube.coverClass s (U.cover.assign b) w).card : NNReal))
  · exact coe_card_coverClass_eq_sum_canonical_children U hs hab hb p
  · intro w hw
    exact U.card_class_le b hb w ((mem_tauAncestorClass U b a _ p w).mp hw).1
  · exact U.le_card_class a (hab.trans hb) p hp

/-- Canonical child counts at a full hierarchy level are pairwise comparable. -/
theorem canonicalChildCount_le {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {p q : ι}
    (hp : p ∈ U.cover.indexSet a) (hq : q ∈ U.cover.indexSet a) :
    canonicalChildCount U b a p <= C ^ 4 * canonicalChildCount U b a q := by
  let i := hs.choose
  have hi : i ∈ s := hs.choose_spec
  have himem : i ∈ _root_.Tube.coverClass s (U.cover.assign b) (U.cover.assign b i) := by
    classical
    simp [_root_.Tube.coverClass, hi]
  have hone : (1 : NNReal) <= C * U.branchingN b := by
    calc
      1 <= ((_root_.Tube.coverClass s (U.cover.assign b)
          (U.cover.assign b i)).card : NNReal) := by
        exact_mod_cast Finset.one_le_card.mpr ⟨i, himem⟩
      _ <= C * U.branchingN b :=
        U.card_class_le b hb _ (U.cover.assign_mem b hb i hi)
  have hbranch : 0 < U.branchingN b := by
    rcases eq_zero_or_pos (U.branchingN b) with hzero | hpos
    · simp [hzero] at hone
    · exact hpos
  exact card_le_mul_of_branching_bounds
    hbranch
    (canonicalChildCount_mul_branching_le U hs hab hb hp)
    (branching_le_canonicalChildCount_mul U hs hab hb hq)

open scoped Classical in
/-- Every full coarse-level node is the ancestor of a full fine-level node. -/
theorem activeRhoParents_full_level {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) :
    activeRhoParents U b a (U.cover.indexSet b) = U.cover.indexSet a := by
  apply Finset.Subset.antisymm
  · exact activeRhoParents_subset_indexSet U hs (hab.trans hb) hb Finset.Subset.rfl
  · intro p hp
    obtain ⟨i, hi⟩ :=
      _root_.Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent U (hab.trans hb) hs hp
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_image.mpr ⟨U.cover.assign b i, U.cover.assign_mem b hb i hi'.1,
      (nodeAncestor_assign_eq U hs hab hb hi'.1).trans hi'.2⟩

/-- Full fine-level cardinality is the sum of canonical child counts over the coarse level. -/
theorem card_fineLevel_eq_sum_canonicalChildCount {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {b a : Nat}
    (hab : a <= b) (hb : b <= N) :
    ((U.cover.indexSet b).card : NNReal) =
      ∑ p ∈ U.cover.indexSet a, canonicalChildCount U b a p := by
  have hnat := card_eq_sum_card_tauAncestorClass U b a (U.cover.indexSet b)
  rw [activeRhoParents_full_level U hs hab hb] at hnat
  have h := congrArg (fun n : Nat => (n : NNReal)) hnat
  simpa [canonicalChildCount, Nat.cast_sum] using h

/-- A canonical class is at most `C^4` times the global average, cross-multiplied. -/
theorem coarseCard_mul_canonicalChildCount_le {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {p : ι}
    (hp : p ∈ U.cover.indexSet a) :
    ((U.cover.indexSet a).card : NNReal) * canonicalChildCount U b a p <=
      C ^ 4 * ((U.cover.indexSet b).card : NNReal) := by
  rw [card_fineLevel_eq_sum_canonicalChildCount U hs hab hb]
  calc
    ((U.cover.indexSet a).card : NNReal) * canonicalChildCount U b a p =
        ∑ _q ∈ U.cover.indexSet a, canonicalChildCount U b a p := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ q ∈ U.cover.indexSet a, C ^ 4 * canonicalChildCount U b a q := by
      exact Finset.sum_le_sum fun q hq => canonicalChildCount_le U hs hab hb hp hq
    _ = C ^ 4 * ∑ q ∈ U.cover.indexSet a, canonicalChildCount U b a q := by
      rw [Finset.mul_sum]

/-- The global average is at most `C^4` times every canonical class, cross-multiplied. -/
theorem fineCard_le_coarseCard_mul_canonicalChildCount {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {p : ι}
    (hp : p ∈ U.cover.indexSet a) :
    ((U.cover.indexSet b).card : NNReal) <=
      C ^ 4 * ((U.cover.indexSet a).card : NNReal) * canonicalChildCount U b a p := by
  rw [card_fineLevel_eq_sum_canonicalChildCount U hs hab hb]
  calc
    (∑ q ∈ U.cover.indexSet a, canonicalChildCount U b a q) <=
        ∑ _q ∈ U.cover.indexSet a, C ^ 4 * canonicalChildCount U b a p := by
      exact Finset.sum_le_sum fun q hq => canonicalChildCount_le U hs hab hb hq hp
    _ = C ^ 4 * ((U.cover.indexSet a).card : NNReal) *
        canonicalChildCount U b a p := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Number of retained level-`b` nodes canonically assigned to `p` at level `a`. -/
def retainedCanonicalChildCount {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι)
    (p : ι) : NNReal :=
  (tauAncestorClass U b a tauNodes p).card

/-- Restricting the fine level can only decrease each canonical child count. -/
theorem retainedCanonicalChildCount_le {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) {b a : Nat} {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b) (p : ι) :
    retainedCanonicalChildCount U b a tauNodes p <= canonicalChildCount U b a p := by
  unfold retainedCanonicalChildCount canonicalChildCount
  exact_mod_cast Finset.card_le_card fun w hw =>
    (mem_tauAncestorClass U b a _ p w).mpr
      ⟨htau ((mem_tauAncestorClass U b a _ p w).mp hw).1,
        ((mem_tauAncestorClass U b a _ p w).mp hw).2⟩

/-- Exact retained fine-node count as a sum over its active canonical parents. -/
theorem card_tauNodes_eq_sum_retainedCanonicalChildCount {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b a : Nat) (tauNodes : Finset ι) :
    (tauNodes.card : NNReal) =
      ∑ p ∈ activeRhoParents U b a tauNodes,
        retainedCanonicalChildCount U b a tauNodes p := by
  have h := congrArg (fun n : Nat => (n : NNReal))
    (card_eq_sum_card_tauAncestorClass U b a tauNodes)
  simpa [retainedCanonicalChildCount, Nat.cast_sum] using h

/-- A uniform per-live-fibre retention fraction preserves canonical balance. -/
theorem retainedCanonicalChildCount_le_of_fraction {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C kappa : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hretain : ∀ p ∈ activeRhoParents U b a tauNodes,
      kappa * canonicalChildCount U b a p <=
        retainedCanonicalChildCount U b a tauNodes p)
    {p q : ι} (hp : p ∈ activeRhoParents U b a tauNodes)
    (hq : q ∈ activeRhoParents U b a tauNodes) :
    kappa * retainedCanonicalChildCount U b a tauNodes p <=
      C ^ 4 * retainedCanonicalChildCount U b a tauNodes q := by
  have hparents := activeRhoParents_subset_indexSet U hs (hab.trans hb) hb htau
  calc
    kappa * retainedCanonicalChildCount U b a tauNodes p <=
        kappa * canonicalChildCount U b a p :=
      mul_le_mul_right (retainedCanonicalChildCount_le U htau p) kappa
    _ <= kappa * (C ^ 4 * canonicalChildCount U b a q) :=
      mul_le_mul_right
        (canonicalChildCount_le U hs hab hb (hparents hp) (hparents hq)) kappa
    _ = C ^ 4 * (kappa * canonicalChildCount U b a q) := by ring
    _ <= C ^ 4 * retainedCanonicalChildCount U b a tauNodes q :=
      mul_le_mul_right (hretain q hq) (C ^ 4)

/-- Every retained class is bounded by the retained global average, without division. -/
theorem retainedCoarseCard_mul_childCount_le {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C kappa : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hretain : ∀ p ∈ activeRhoParents U b a tauNodes,
      kappa * canonicalChildCount U b a p <=
        retainedCanonicalChildCount U b a tauNodes p)
    {p : ι} (hp : p ∈ activeRhoParents U b a tauNodes) :
    kappa * ((activeRhoParents U b a tauNodes).card : NNReal) *
        retainedCanonicalChildCount U b a tauNodes p <=
      C ^ 4 * (tauNodes.card : NNReal) := by
  rw [card_tauNodes_eq_sum_retainedCanonicalChildCount U b a tauNodes]
  calc
    kappa * ((activeRhoParents U b a tauNodes).card : NNReal) *
        retainedCanonicalChildCount U b a tauNodes p =
        ∑ _q ∈ activeRhoParents U b a tauNodes,
          kappa * retainedCanonicalChildCount U b a tauNodes p := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ <= ∑ q ∈ activeRhoParents U b a tauNodes,
        C ^ 4 * retainedCanonicalChildCount U b a tauNodes q := by
      exact Finset.sum_le_sum fun q hq =>
        retainedCanonicalChildCount_le_of_fraction U hs hab hb htau hretain hp hq
    _ = C ^ 4 * ∑ q ∈ activeRhoParents U b a tauNodes,
        retainedCanonicalChildCount U b a tauNodes q := by
      rw [Finset.mul_sum]

/-- The retained global average is bounded by every retained class, without division. -/
theorem retainedFineCard_le_coarseCard_mul_childCount {ι : Type u} {delta : NNReal}
    {s : Finset ι} {T : ι -> Tube delta E} {N : Nat} {C kappa : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hretain : ∀ p ∈ activeRhoParents U b a tauNodes,
      kappa * canonicalChildCount U b a p <=
        retainedCanonicalChildCount U b a tauNodes p)
    {p : ι} (hp : p ∈ activeRhoParents U b a tauNodes) :
    kappa * (tauNodes.card : NNReal) <=
      C ^ 4 * ((activeRhoParents U b a tauNodes).card : NNReal) *
        retainedCanonicalChildCount U b a tauNodes p := by
  rw [card_tauNodes_eq_sum_retainedCanonicalChildCount U b a tauNodes]
  calc
    kappa * ∑ q ∈ activeRhoParents U b a tauNodes,
        retainedCanonicalChildCount U b a tauNodes q =
        ∑ q ∈ activeRhoParents U b a tauNodes,
          kappa * retainedCanonicalChildCount U b a tauNodes q := by
      rw [Finset.mul_sum]
    _ <= ∑ _q ∈ activeRhoParents U b a tauNodes,
        C ^ 4 * retainedCanonicalChildCount U b a tauNodes p := by
      exact Finset.sum_le_sum fun q hq =>
        retainedCanonicalChildCount_le_of_fraction U hs hab hb htau hretain hq hp
    _ = C ^ 4 * ((activeRhoParents U b a tauNodes).card : NNReal) *
        retainedCanonicalChildCount U b a tauNodes p := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end

end Kakeya.WangZahl
