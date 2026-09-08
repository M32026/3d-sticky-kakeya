/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeHostObstruction

/-!
# `Tube.UniformTubeSet.self` — the first concrete **multi-node** hierarchy in the tree

Every `T-S2`-style certificate needs a *concrete* `Tube.UniformTubeSet` with more than one node, and
the run has had exactly one concrete hierarchy — `Kakeya.ML2Core.singletonUniform`, which has a
single node per level and therefore cannot host any separation at all
(`nodesUnder` is a singleton, so `Δ_max = Δ` and `Kakeya.ML2Core.FillAt` is trivially true).
Obtaining one from `Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` does not help
either: the uniformiser's `cover` is opaque, so no clause about `nodesUnder` or the node tubes can
be proved about it.

**This file builds one outright, and cheaply.**  Take the members themselves as the nodes:

```
 indexSet k := s      assign k := id      tube k i := (T i).rescale (gridScale δ N k)
```

Every field is then a one-liner:

| field | why |
|---|---|
| `assign_mem` | `id` |
| `le_tube_assign` | `Tube.le_rescale`, since `δ ≤ ρ_k` for `k ≤ N` |
| `nested` | `id` |
| `tube_nested` | `Tube.rescale_le_rescale_of_radius_le`, since `Tube.gridScale` is antitone |
| `tube_injOn` | the hypothesis `hinj` — distinct members must have distinct rescales |
| `boundedOverlap` | the filter is inside `indexSet k = s`, so `#s` bounds it |
| `card_class_le` / `le_card_class` | classes are singletons, `branchingN := 1` |

The constant is `max 1 s.card` — **`δ`-free**, which is what  requires of `Cu₀` and
what 's budget check consumes.

## The one real hypothesis, and why it is the honest one

`hinj` — *distinct members have distinct rescales at every level* — is exactly
`Tube.UniformTubeSet.tube_injOn`, and it is the clause
 showed cannot be waived: a family with a **repeated** tube (like
`Kakeya.ML2Core.SpineFloorGateRed.redBody`'s `inl` block) has no self-hierarchy, because two equal
members would have to be two distinct nodes with the same tube.  So this constructor is available
precisely for families of *distinct* tubes — which, is also the only kind that can carry a
node-level statement at all.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section SelfHierarchy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

open scoped Classical in
/-- **The self-hierarchy**: each member is its own node at every level, the node being the member's
own rescale to the grid radius.  See the module docstring; the constant `max 1 s.card` is
`δ`-free. -/
noncomputable def _root_.Tube.UniformTubeSet.self (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (hinj : ∀ k ≤ N, Set.InjOn (fun i => (T i).rescale (Tube.gridScale δ N k)) (s : Set ι)) :
    Tube.UniformTubeSet s T N (max 1 (s.card : NNReal)) where
  cover :=
    { indexSet := fun _ => s
      assign := fun _ i => i
      tube := fun k i => (T i).rescale (Tube.gridScale δ N k)
      assign_mem := fun _ _ i hi => hi
      le_tube_assign := fun k hk i _ =>
        Tube.le_rescale (T i) (delta_le_gridScale hδ0 hδ1 hk)
      nested := fun _ _ _ _ _ _ h => h
      tube_nested := fun k hk i _ =>
        Tube.rescale_le_rescale_of_radius_le (T i)
          (Tube.gridScale_antitone hδ0 hδ1 N (Nat.le_succ k)) }
  branchingN := fun _ => 1
  tube_injOn := fun k hk => hinj k hk
  boundedOverlap := by
    intro k hk V
    refine le_trans ?_ (le_max_right 1 (s.card : NNReal))
    exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
  card_class_le := by
    intro k hk j hj
    rw [mul_one]
    refine le_trans ?_ (le_max_left 1 (s.card : NNReal))
    have h1 : (Tube.coverClass s (fun i => i) j).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Tube.coverClass, Finset.mem_filter] at ha hb
      rw [ha.2, hb.2]
    exact_mod_cast Nat.cast_le.mpr h1
  le_card_class := by
    intro k hk j hj
    have hjmem : j ∈ Tube.coverClass s (fun i => i) j := by
      simp [Tube.coverClass, hj]
    have h1 : 1 ≤ (Tube.coverClass s (fun i => i) j).card :=
      Finset.card_pos.mpr ⟨j, hjmem⟩
    calc (1 : NNReal) ≤ ((Tube.coverClass s (fun i => i) j).card : NNReal) := by
          exact_mod_cast Nat.one_le_cast.mpr h1
      _ ≤ max 1 (s.card : NNReal) * ((Tube.coverClass s (fun i => i) j).card : NNReal) :=
          le_mul_of_one_le_left (by simp) (le_max_left _ _)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem self_indexSet (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι)
    (T : ι → Tube δ E) (hinj : ∀ k ≤ N, Set.InjOn
      (fun i => (T i).rescale (Tube.gridScale δ N k)) (s : Set ι)) (k : ℕ) :
    (Tube.UniformTubeSet.self hδ0 hδ1 s T hinj).cover.indexSet k = s :=
  rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem self_tube (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι)
    (T : ι → Tube δ E) (hinj : ∀ k ≤ N, Set.InjOn
      (fun i => (T i).rescale (Tube.gridScale δ N k)) (s : Set ι)) (k : ℕ) (i : ι) :
    (Tube.UniformTubeSet.self hδ0 hδ1 s T hinj).cover.tube k i
      = (T i).rescale (Tube.gridScale δ N k) :=
  rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The self-hierarchy's `nodesUnder`, computed.**  A level-`c` node sits under a level-`k` node
exactly when its rescale is contained in the other's — no assignment bookkeeping survives. -/
theorem self_nodesUnder (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι)
    (T : ι → Tube δ E) (hinj : ∀ k ≤ N, Set.InjOn
      (fun i => (T i).rescale (Tube.gridScale δ N k)) (s : Set ι)) (c k : ℕ) (j : ι) :
    (Tube.UniformTubeSet.self hδ0 hδ1 s T hinj).nodesUnder c k j
      = s.filter (fun i => ((T i).rescale (Tube.gridScale δ N c)).toConvexSpaceBody
          ≤ ((T j).rescale (Tube.gridScale δ N k)).toConvexSpaceBody) :=
  rfl

end SelfHierarchy

end Kakeya.ML2Core
