/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloorObstruction

/-!
# The genuine parent

The refined source's alternative (F) (l.4062–4076) names a **genuine parent** level `p` of the
window's coarse level `a`: a level at which every level-`a` node still has parent density at most
`δ^{-2η'}` on its `p`-cells, and which lies **before the whole window** (`p < m'` for every window
level `m'`).  The source's stopping-time sentence (l.4133–4136, "the first scale at which the
transverse factor becomes small determines a genuine parent `p` before the whole window") is read
here as the **last admissible level below the window's lowest level `mlo`**:

* `ParentAdmissible 𝒰 η' a k` — the parent-density clause of (F) at level `k`, exactly the second
  clause of the existing `hfloor` binder (`Reduction/SpineRefinedFloor.lean:141–143`,
  `Kakeya.ML2Core.geometricCoreAt_of_floor_middleFactor`);
* `genuineParent 𝒰 η' a mlo` — the largest admissible `k ∈ [a, mlo)`, as a `Finset.sup`, so that no
  nonemptiness proof is threaded through the definition;
* `genuineParent_spec` — the three (F) clauses on `p := genuineParent …`: `a ≤ p`, `p < mlo`, and
  admissibility, plus maximality, **given** that the level `a` itself is admissible and `a < mlo`;
* `parentAdmissible_self` — the level `a` is admissible as soon as the hierarchy's uniformity
  constant is below `δ^{-2η'}`: the level-`a` cells inside one level-`a` node all meet that node
  through their class members (`coverClass_nonempty_of_mem_parent`), so `boundedOverlap` caps their
  number by `C` and `Kakeya.maxDensity_le_card` does the rest.  This is the blueprint's remark
  that the set is nonempty at `k = a` "not with `= 1`: the producer must carry the constant".

The window's lowest level `mlo` and the exponent `η'` are parameters here; F6 pins them.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

/-- **The parent-density clause of alternative (F) at level `k`**: every level-`a` node has
`Δ_max` of its level-`k` cells at most `δ^{-2η'}`.  Byte-for-byte the second clause of the existing
`hfloor` binder, with `p := k`. -/
def ParentAdmissible {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (η' : ℝ) (a k : ℕ) : Prop :=
  ∀ jθ ∈ 𝒰.cover.indexSet a,
    Kakeya.maxDensity (𝒰.nodesUnder k a jθ) (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-(2 * η'))

open scoped Classical in
/-- **The genuine parent**: the largest admissible level in `[a, mlo)`. -/
noncomputable def genuineParent {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (η' : ℝ) (a mlo : ℕ) : ℕ :=
  ((Finset.range mlo).filter (fun k => a ≤ k ∧ ParentAdmissible 𝒰 η' a k)).sup id

omit [Nontrivial E] in
/-- **F2 — the specification of the genuine parent.**  If the level `a` itself is admissible and
`a < mlo`, then `p := genuineParent 𝒰 η' a mlo` satisfies `a ≤ p`, `p < mlo`, is admissible, and
dominates every admissible level of `[a, mlo)`. -/
theorem genuineParent_spec {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {η' : ℝ} {a mlo : ℕ} (hamlo : a < mlo)
    (ha : ParentAdmissible 𝒰 η' a a) :
    a ≤ genuineParent 𝒰 η' a mlo ∧ genuineParent 𝒰 η' a mlo < mlo ∧
      ParentAdmissible 𝒰 η' a (genuineParent 𝒰 η' a mlo) ∧
      ∀ k, a ≤ k → k < mlo → ParentAdmissible 𝒰 η' a k → k ≤ genuineParent 𝒰 η' a mlo := by
  classical
  set S : Finset ℕ := (Finset.range mlo).filter (fun k => a ≤ k ∧ ParentAdmissible 𝒰 η' a k)
    with hS
  have hmemS : ∀ k, k ∈ S ↔ k < mlo ∧ a ≤ k ∧ ParentAdmissible 𝒰 η' a k := by
    intro k
    simp only [hS, Finset.mem_filter, Finset.mem_range]
  have haS : a ∈ S := (hmemS a).mpr ⟨hamlo, le_rfl, ha⟩
  have hne : S.Nonempty := ⟨a, haS⟩
  have hp : genuineParent 𝒰 η' a mlo = S.sup id := rfl
  obtain ⟨p, hpS, hpeq⟩ := Finset.exists_mem_eq_sup S hne id
  have hpdef : genuineParent 𝒰 η' a mlo = p := by rw [hp, hpeq]; rfl
  obtain ⟨hpmlo, hap, hpadm⟩ := (hmemS p).mp hpS
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpdef]; exact hap
  · rw [hpdef]; exact hpmlo
  · rw [hpdef]; exact hpadm
  · intro k hak hkmlo hkadm
    rw [hp]
    exact Finset.le_sup (f := id) ((hmemS k).mpr ⟨hkmlo, hak, hkadm⟩)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The level-`a` cells inside a level-`a` node number at most `C`.**  Every such cell has a class
member (`coverClass_nonempty_of_mem_parent`), which lies in the cell and hence in the node, so the
cell is counted by `boundedOverlap` at the node's own tube. -/
theorem card_nodesUnder_self_le {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {a : ℕ} (ha : a ≤ N) (hs : s.Nonempty) (j : ι) :
    ((𝒰.nodesUnder a a j).card : NNReal) ≤ C := by
  classical
  have hsub : 𝒰.nodesUnder a a j ⊆ (𝒰.cover.indexSet a).filter (fun j' => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j').toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody) := by
    intro j' hj'
    have hj'' := hj'
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at hj''
    obtain ⟨hidx, hle⟩ := hj''
    obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 ha hs hidx
    simp only [Tube.coverClass, Finset.mem_filter] at hi
    have hTi : (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j').toConvexSpaceBody := by
      have := 𝒰.cover.le_tube_assign a ha i hi.1
      rwa [hi.2] at this
    exact Finset.mem_filter.mpr ⟨hidx, i, hi.1, hTi, hTi.trans hle⟩
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub)
    (𝒰.boundedOverlap a ha (𝒰.cover.tube a j))

omit [Nontrivial E] in
/-- **The level `a` is itself admissible** once the uniformity constant is below `δ^{-2η'}`. -/
theorem parentAdmissible_self {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {a : ℕ} (ha : a ≤ N) (hs : s.Nonempty) {η' : ℝ}
    (hC : (C : ENNReal) ≤ (δ : ENNReal) ^ (-(2 * η'))) :
    ParentAdmissible 𝒰 η' a a := by
  intro jθ _
  refine (Kakeya.maxDensity_le_card _ _).trans (le_trans ?_ hC)
  exact_mod_cast card_nodesUnder_self_le 𝒰 ha hs jθ

end Kakeya.ML2Core

end
