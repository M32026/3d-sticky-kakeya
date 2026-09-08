/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.NodeFamilies

/-!
# The fixed carrier skeleton of a dividing block, with no injectivity assumed

`Kakeya.ml1Boot.exists_isTwoScaleFactors_of_dens` — the assembled producer of
`Kakeya.ml1Boot.IsTwoScaleFactors` — takes as its first input a **fixed carrier skeleton**

```
amb --pτ--> tτAmb --pθ--> tθAmb
```

together with two `Kakeya.ml1Boot.IsParentFamily` certificates.  This file builds that
skeleton at the two ends `τ = ρ_b`, `θ = ρ_a` of a `StickyKakeya.IsFrostmanDividingBlock`,
and it does so **without assuming injectivity of the node tubes**, which the older Case (ii)
endpoint `Kakeya.ml1Boot.multiplicity_le_caseTwo` had to carry as two extra hypotheses and
which the repaired leaf `Kakeya.ml1Boot.exists_isTwoScaleFactors_of_frostmanDividingBlock`
does not.

Two observations make that possible.

* **The carriers are existentially bound in the leaf.**  Nothing forces `tτAmb` to be the
  whole of `𝒰'.cover.indexSet b`; any subset carrying the same *convex bodies* serves.
  `Kakeya.ml1Boot.exists_dedupParentFamily` deduplicates: it turns the two raw clauses
  "`p` maps into `t`" and "`V i` is contained in its parent" into a genuine
  `Kakeya.ml1Boot.IsParentFamily` over a subset `t' ⊆ t` on which `k ↦ (W k).toConvexSpaceBody`
  *is* injective, at no cost — the reindexed parent of every `i` has literally the same convex
  body as the old one.  This is what `Kakeya/DimensionThree/MainLemma1/NodeFamilies.lean`
  records as "the caller supplies it, after deduplicating".

* **The parent map may be made total.**  `Tube.GridCoverSystem.assign_mem` places
  `assign b i` in `𝒰'.cover.indexSet b` only for `i ∈ s'`, while the leaf's
  `Kakeya.ml1Boot.IsTwoScaleFactors.skeleton_fine` clause is quantified over the whole
  ambient family `s ⊇ s'`.  The deduplicated map produced here is total into `t'` by
  construction — off `t` it takes a fixed representative — so the skeleton clause holds on all
  of `s` while the containment clause is claimed only on `s'`, where it is true.

The coarse half needs the induced map `ϖ_{b→a}` on nodes.  It is produced by
`Kakeya.ml1Boot.exists_coarseNodeMap`, which is
`Kakeya.ml1Boot.exists_nodeParentFamilies_coarse` with its injectivity hypothesis and
conclusion dropped: only the descent along the nested cover is used, and that needs no
injectivity.

## What is *not* here

The three analytic multiplicity bounds, the density lower bound on the active support, and the
ledger clauses `hvol` / `habsorb` of the leaf.  The skeleton is input (1) of four.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody StickyKakeya Tube

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## Deduplication: injectivity is free -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Deduplicating a parent family** (blueprint §2, the "fixed skeleton" invariant).

`Kakeya.ml1Boot.IsParentFamily` asks its parent index set to be injectively indexed by convex
bodies.  A hierarchy does not supply that: two node indices may carry the same tube.  This
lemma shows the clause costs nothing whenever the parent carrier is allowed to shrink, which
is the case for every consumer that binds the carrier existentially.

From the two *raw* clauses — `p` maps `s` into `t`, and every `V i` is contained in its parent
— one obtains a subset `t' ⊆ t` and a map `p'` which is **total** into `t'` (not merely on
`s`), which agrees with `p` up to equality of the parent convex body on `s`, and which is a
genuine parent family.

Totality is what lets the caller state the skeleton clause on an ambient family strictly larger
than the one on which the containment is known. -/
theorem exists_dedupParentFamily {ι κ : Type*} {σ ρ : NNReal}
    {s : Finset ι} {V : ι → Tube σ E} {t : Finset κ} {W : κ → Tube ρ E} {p : ι → κ}
    (ht : t.Nonempty) (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody) :
    ∃ (t' : Finset κ) (p' : ι → κ), t' ⊆ t ∧ (∀ i, p' i ∈ t') ∧
      (∀ i ∈ s, (W (p' i)).toConvexSpaceBody = (W (p i)).toConvexSpaceBody) ∧
      IsParentFamily s V t' W p' := by
  classical
  obtain ⟨j₀, hj₀⟩ := ht
  set f : κ → ConvexSpaceBody E := fun k => (W k).toConvexSpaceBody with hf
  -- a representative of every convex body realized in `t`
  set repOf : ConvexSpaceBody E → κ := fun B =>
    if h : ∃ j, j ∈ t ∧ f j = B then h.choose else j₀ with hrepOf
  have hrepMem : ∀ B, repOf B ∈ t := by
    intro B
    by_cases h : ∃ j, j ∈ t ∧ f j = B
    · rw [hrepOf]; simp only [dif_pos h]; exact h.choose_spec.1
    · rw [hrepOf]; simp only [dif_neg h]; exact hj₀
  have hrepEq : ∀ j ∈ t, f (repOf (f j)) = f j := by
    intro j hj
    have h : ∃ j', j' ∈ t ∧ f j' = f j := ⟨j, hj, rfl⟩
    rw [hrepOf]; simp only [dif_pos h]; exact h.choose_spec.2
  set rep : κ → κ := fun k => repOf (f k) with hrep
  refine ⟨t.image rep, fun i => if p i ∈ t then rep (p i) else rep j₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact hrepMem _
  · intro i
    by_cases h : p i ∈ t
    · simp only [if_pos h]; exact Finset.mem_image_of_mem rep h
    · simp only [if_neg h]; exact Finset.mem_image_of_mem rep hj₀
  · intro i hi
    have h : p i ∈ t := hmaps i hi
    simp only [if_pos h]
    exact hrepEq _ h
  · -- `mapsTo`
    intro i _
    by_cases h : p i ∈ t
    · simp only [if_pos h]; exact Finset.mem_image_of_mem rep h
    · simp only [if_neg h]; exact Finset.mem_image_of_mem rep hj₀
  · -- `injOn`
    intro x hx y hy hxy
    obtain ⟨k₁, hk₁, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k₂, hk₂, rfl⟩ := Finset.mem_image.mp hy
    have h₁ : f (rep k₁) = f k₁ := hrepEq _ hk₁
    have h₂ : f (rep k₂) = f k₂ := hrepEq _ hk₂
    have : f k₁ = f k₂ := by rw [← h₁, ← h₂]; exact hxy
    change rep k₁ = rep k₂
    rw [hrep]
    exact congrArg repOf this
  · -- `le_parent`
    intro i hi
    have h : p i ∈ t := hmaps i hi
    simp only [if_pos h]
    have := hrepEq _ h
    calc (V i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody := hle i hi
      _ = f (rep (p i)) := (hrepEq _ h).symm
      _ = (W (rep (p i))).toConvexSpaceBody := rfl

/-! ## The two ends of a block -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The scale bracket of a dividing block**: `δ ≤ ρ_b ≤ ρ_a ≤ 1`.

The three inequalities `Kakeya.ml1Boot.exists_isTwoScaleFactors_of_dens` and the leaf
`Kakeya.ml1Boot.exists_isTwoScaleFactors_of_frostmanDividingBlock` both open with, read off
`Tube.gridScale_antitone`, `Tube.gridScale_self` and `Tube.gridScale_le_one`. -/
theorem gridScale_block_bracket {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {N a b : ℕ}
    (hab : a < b) (hb : b ≤ N) :
    δ ≤ Tube.gridScale δ N b ∧ Tube.gridScale δ N b ≤ Tube.gridScale δ N a ∧
      Tube.gridScale δ N a ≤ 1 := by
  have hN : 0 < N := lt_of_lt_of_le (by omega) hb
  refine ⟨?_, Tube.gridScale_antitone hδ0 hδ1 N hab.le, Tube.gridScale_le_one hδ1 N a⟩
  have := Tube.gridScale_antitone hδ0 hδ1 N hb
  rwa [Tube.gridScale_self δ hN] at this

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The induced map on nodes, without injectivity** (blueprint
`lem:ml1bootParentFamiliesFromNodesCoarse`, the containment half).

This is `Kakeya.ml1Boot.exists_nodeParentFamilies_coarse` with the injectivity hypothesis
`hinjCoarse` and the `Kakeya.ml1Boot.IsParentFamily` packaging removed: only the descent along
the nested cover is used, and the descent needs no injectivity.  The caller recovers the
packaged form by deduplicating with `Kakeya.ml1Boot.exists_dedupParentFamily`.

It is stated over an arbitrary set `tb` of `b`-nodes that carry a leaf rather than over the
whole of `𝒰'.cover.indexSet b`, because the standing hypothesis "every `b`-node carries a
leaf" is *not* a consequence of `Tube.UniformTubeSet`, while the image
`s'.image (𝒰'.cover.assign b)` satisfies it by construction. -/
theorem exists_coarseNodeMap {ι : Type*} [Nontrivial E] {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ N) (tb : Finset ι)
    (hnodes : ∀ k ∈ tb, ∃ i ∈ s', 𝒰'.cover.assign b i = k) :
    ∃ pθ : ι → ι,
      (∀ i ∈ s', pθ (𝒰'.cover.assign b i) = 𝒰'.cover.assign a i) ∧
        (∀ k ∈ tb, pθ k ∈ 𝒰'.cover.indexSet a) ∧
        (∀ k ∈ tb,
          (𝒰'.cover.tube b k).toConvexSpaceBody ≤
            (𝒰'.cover.tube a (pθ k)).toConvexSpaceBody) := by
  classical
  let pθ : ι → ι := fun k =>
    if h : ∃ i, i ∈ s' ∧ 𝒰'.cover.assign b i = k then
      𝒰'.cover.assign a h.choose
    else k
  have hd : ∀ (m d : ℕ), m + d ≤ b → ∀ i ∈ s', ∀ j ∈ s',
      𝒰'.cover.assign (m + d) i = 𝒰'.cover.assign (m + d) j →
      𝒰'.cover.assign m i = 𝒰'.cover.assign m j := by
    intro m d
    induction d with
    | zero =>
        intro h i hi j hj heq
        simpa using heq
    | succ d ih =>
        intro h i hi j hj heq
        have hmN : (m + d) + 1 ≤ N := le_trans (by omega) hb
        rw [show m + (d + 1) = (m + d) + 1 by omega] at heq
        exact ih (by omega) i hi j hj (𝒰'.cover.nested (m + d) hmN i hi j hj heq)
  have hnest : ∀ m : ℕ, m ≤ b → ∀ i ∈ s', ∀ j ∈ s',
      𝒰'.cover.assign b i = 𝒰'.cover.assign b j →
      𝒰'.cover.assign m i = 𝒰'.cover.assign m j := by
    intro m hm i hi j hj heq
    have hle : m + (b - m) ≤ b := by omega
    have heq' : 𝒰'.cover.assign (m + (b - m)) i = 𝒰'.cover.assign (m + (b - m)) j := by
      rw [← Nat.add_sub_cancel' hm] at heq
      exact heq
    exact hd m (b - m) hle i hi j hj heq'
  have hcd : ∀ (m d : ℕ), m + d ≤ b → ∀ i ∈ s',
      (𝒰'.cover.tube (m + d) (𝒰'.cover.assign (m + d) i)).toConvexSpaceBody ≤
      (𝒰'.cover.tube m (𝒰'.cover.assign m i)).toConvexSpaceBody := by
    intro m d
    induction d with
    | zero =>
        intro h i hi
        exact le_rfl
    | succ d ih =>
        intro h i hi
        have hmN : (m + d) + 1 ≤ N := le_trans (by omega) hb
        rw [show m + (d + 1) = (m + d) + 1 by omega]
        exact le_trans (𝒰'.cover.tube_nested (m + d) hmN i hi) (ih (by omega) i hi)
  have hchain : ∀ m : ℕ, m ≤ b → ∀ i ∈ s',
      (𝒰'.cover.tube b (𝒰'.cover.assign b i)).toConvexSpaceBody ≤
      (𝒰'.cover.tube m (𝒰'.cover.assign m i)).toConvexSpaceBody := by
    intro m hm i hi
    have hle : m + (b - m) ≤ b := by omega
    have h' := hcd m (b - m) hle i hi
    rw [Nat.add_sub_cancel' hm] at h'
    exact h'
  refine ⟨pθ, ?_, ?_, ?_⟩
  · intro i hi
    change (if h : ∃ j, j ∈ s' ∧ 𝒰'.cover.assign b j = 𝒰'.cover.assign b i then
        𝒰'.cover.assign a h.choose else _) = _
    have h : ∃ j, j ∈ s' ∧ 𝒰'.cover.assign b j = 𝒰'.cover.assign b i := ⟨i, hi, rfl⟩
    rw [dif_pos h]
    exact hnest a hab h.choose h.choose_spec.1 i hi h.choose_spec.2
  · intro k hk
    have h := hnodes k hk
    change (if h : ∃ i, i ∈ s' ∧ 𝒰'.cover.assign b i = k then
        𝒰'.cover.assign a h.choose else k) ∈ _
    rw [dif_pos h]
    exact 𝒰'.cover.assign_mem a (le_trans hab hb) h.choose h.choose_spec.1
  · intro k hk
    have h := hnodes k hk
    change (𝒰'.cover.tube b k).toConvexSpaceBody ≤
      (𝒰'.cover.tube a (if h : ∃ i, i ∈ s' ∧ 𝒰'.cover.assign b i = k then
        𝒰'.cover.assign a h.choose else k)).toConvexSpaceBody
    rw [dif_pos h]
    have hbc : (𝒰'.cover.tube b (𝒰'.cover.assign b h.choose)).toConvexSpaceBody ≤
        (𝒰'.cover.tube a (𝒰'.cover.assign a h.choose)).toConvexSpaceBody :=
      hchain a hab h.choose h.choose_spec.1
    simpa [h.choose_spec.2] using hbc

/-! ## The skeleton of a dividing block -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The fixed carrier skeleton at the two ends of a dividing block** (leaf input (1)).

Input (1) of the four the leaf
`Kakeya.ml1Boot.exists_isTwoScaleFactors_of_frostmanDividingBlock` still needs: the fixed
carrier/parent families at `τ = ρ_b` and `θ = ρ_a`, in exactly the shape
`Kakeya.ml1Boot.exists_isTwoScaleFactors_of_dens` consumes them.

Note what is **not** assumed: neither node level is assumed to be injectively indexed by convex
bodies.  The carriers `tτAmb`, `tθAmb` returned here are deduplicated subsets of
`𝒰'.cover.indexSet b` and `𝒰'.cover.indexSet a`
(`Kakeya.ml1Boot.exists_dedupParentFamily`), which is legitimate precisely because the leaf
binds them existentially.

Note also that both parent maps are **total** into their carriers, so the skeleton clauses
`Kakeya.ml1Boot.IsTwoScaleFactors.skeleton_fine` and `.skeleton_mid` hold over *any* ambient
family, in particular over the leaf's `s ⊇ s'`, while the containment clauses are claimed only
where they are true.

There is **no** standing hypothesis "every `b`-node carries a leaf" either — the one clause
`Kakeya.ml1Boot.IsCoarseNodeParents` has to assume, and without which the induced map on nodes
is undefined at the empty nodes.  It is discharged here by taking the fine carrier inside
`s'.image (𝒰'.cover.assign b)`, whose members carry a leaf by construction; the leaf binds the
carrier existentially, so nothing is lost.

So the whole of input (1) is unconditional given the block: no injectivity, no carry-leaf
clause, only `s'.Nonempty` and `a ≤ b ≤ N`. -/
theorem exists_blockSkeleton {ι : Type*} [Nontrivial E] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰' : UniformTubeSet s' T N Cu) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (hs'ne : s'.Nonempty) :
    ∃ (tτAmb tθAmb : Finset ι) (pτ pθ : ι → ι),
      tτAmb ⊆ 𝒰'.cover.indexSet b ∧ tθAmb ⊆ 𝒰'.cover.indexSet a ∧
      (∀ i, pτ i ∈ tτAmb) ∧ (∀ k, pθ k ∈ tθAmb) ∧
      IsParentFamily s' T tτAmb (𝒰'.cover.tube b) pτ ∧
      IsParentFamily tτAmb (𝒰'.cover.tube b) tθAmb (𝒰'.cover.tube a) pθ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs'ne
  -- the `b`-nodes that actually carry a leaf
  set tb : Finset ι := s'.image (𝒰'.cover.assign b) with htb
  have htbsub : tb ⊆ 𝒰'.cover.indexSet b := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact 𝒰'.cover.assign_mem b hb i hi
  have htbcarry : ∀ k ∈ tb, ∃ i ∈ s', 𝒰'.cover.assign b i = k := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨i, hi, rfl⟩
  have hbNe : tb.Nonempty := ⟨_, Finset.mem_image_of_mem _ hi₀⟩
  -- the fine end, deduplicated
  obtain ⟨tτAmb, pτ, hτsub, hτtot, _hτeq, hparent₁⟩ :=
    exists_dedupParentFamily (V := T) (W := 𝒰'.cover.tube b) (p := 𝒰'.cover.assign b)
      hbNe (fun i hi => Finset.mem_image_of_mem _ hi) (𝒰'.cover.le_tube_assign b hb)
  -- the coarse end: the induced map on nodes, then deduplicate again
  obtain ⟨pθ₀, _hcomp, hθmaps, hθle⟩ := exists_coarseNodeMap 𝒰' hab hb tb htbcarry
  have haNe : (𝒰'.cover.indexSet a).Nonempty :=
    ⟨_, 𝒰'.cover.assign_mem a (le_trans hab hb) i₀ hi₀⟩
  obtain ⟨tθAmb, pθ, hθsub, hθtot, _hθeq, hparent₂⟩ :=
    exists_dedupParentFamily (s := tτAmb) (V := 𝒰'.cover.tube b)
      (W := 𝒰'.cover.tube a) (p := pθ₀) haNe
      (fun k hk => hθmaps k (hτsub hk)) (fun k hk => hθle k (hτsub hk))
  exact ⟨tτAmb, tθAmb, pτ, pθ, hτsub.trans htbsub, hθsub, hτtot, hθtot, hparent₁, hparent₂⟩

end ml1Boot

end Kakeya

end

