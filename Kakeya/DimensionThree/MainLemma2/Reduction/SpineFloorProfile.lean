/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorCount
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorGate

/-!
# The branching profile, the two-level count band, and the fill

The pieces of the (F) descent that are theorems of the hierarchy alone, ahead of the
descent's assembly.

* **X2′** `le_ethickness_of_tube_le`: a convex body containing a `ρ`-cell is at least `ρ` thick at
  every rank `≤ n−1` (`Tube.le_ethickness_finrank_sub_one` + the two monotonicities of
  `Metric.ethickness`).
* **X4b** `branchingN_pos` / `uniform_C_pos`: the branching numbers and the constant of a
  `Tube.UniformTubeSet` on a nonempty family are positive — otherwise `card_class_le` empties the
  class of a member's own node.  Every ratio below is vacuous without it.
* **X4** `card_nodesUnder_band`: the **two-level count band**, a theorem of GWZ Definition 2.1(iii)
  and the nesting: `branchingN p ≤ C² · branchingN c · #𝕋_c[T_p]` and
  `#𝕋_c[T_p] · branchingN c ≤ C³ · branchingN p` at every pair `p ≤ c` and every level-`p` node.
  The refined source's "descendant counts and two-level counts … pairwise within a factor two at
  every fixed level or pair of levels" (l.4032-4035) is carried already; the window twin needs no
  third field.
* **X5** `card_nodesUnder_ge_of_profile`: with `parentProfile 𝒰 ζ k := branchingN k / ρ_k^{2+4ζ}`,
  the existing `hfloor` clause 4 at **every** level-`p` cell follows from the single scalar inequality
  `C² · parentProfile c ≤ parentProfile p`.
* **X7** `exists_parentProfile_max`: the genuine parent as the admissible level of `[a, mlo)` with
  the largest normalised profile (`Finset.exists_max_image`; X1 is the existing
  `parentAdmissible_self`).  `Kakeya.ML2Core.genuineParent` stays as existing.
* **X6a** `card_nodesUnder_ge_of_fillAt`: the fill at one cell counts —
  `κ · Λ · c_vol ρ_k^{n−1} ≤ #𝕋_c[T_k] · C_vol ρ_c^{n−1}` whenever `Λ ≤ Δ_max(𝕋_c[T_k])`.
* **X6b (core)** `exists_maximizer_small_of_not_fillAt`: when the fill fails, the biased maximizer's
  hull is small — `(|W|/|T_k|)^{1+ϖ} < κ` — on the unrestricted family, through G2′
  (`exists_biasedMaximizer_densityIn_ge`).  Its thickness reading and the descent (X6c, H-8) follow.
-/

@[expose] public section

open MeasureTheory Tube Metric
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

/-! ### X2′ — a body containing a cell is at least a cell thick -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **X2′.**  Any convex body containing a `ρ`-cell is at least `ρ` thick at every rank
`n ≤ finrank − 1`: the maximizer of the level-`c` cells inside a level-`k` node can never be thinner
than one cell of the grid. -/
theorem le_ethickness_of_tube_le {ρ : NNReal} (V : Tube ρ E) {W : ConvexSpaceBody E}
    (hVW : V.toConvexSpaceBody ≤ W) {n : ℕ} (hn' : n ≤ Module.finrank ℝ E - 1) :
    (ρ : ENNReal) ≤ ethickness ℝ W.carrier n :=
  calc (ρ : ENNReal) ≤ ethickness ℝ V.carrier (Module.finrank ℝ E - 1) :=
        V.le_ethickness_finrank_sub_one
    _ ≤ ethickness ℝ V.carrier n := ethickness_antitone hn'
    _ ≤ ethickness ℝ W.carrier n :=
        ethickness_monotone (SetLike.coe_subset_coe.mpr hVW) n

/-! ### X4b — non-vacuity -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **X4b.**  On a nonempty family every branching number is positive: a member's own node has a
nonempty class, and `card_class_le` bounds it by `C · branchingN k`. -/
theorem branchingN_pos {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {k : ℕ} (hk : k ≤ N) :
    0 < 𝒰.branchingN k := by
  classical
  obtain ⟨i, hi⟩ := hs
  have hle := 𝒰.card_class_le k hk _ (𝒰.cover.assign_mem k hk i hi)
  have hne : (coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i)).Nonempty :=
    ⟨i, by simp [coverClass, hi]⟩
  have h1 : (1 : NNReal)
      ≤ ((coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr hne
  by_contra h
  have h0 : 𝒰.branchingN k = 0 := le_antisymm (not_lt.mp h) bot_le
  rw [h0, mul_zero] at hle
  exact absurd (h1.trans hle) (by norm_num)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **X4b′.**  On a nonempty family the constant of the hierarchy is positive. -/
theorem uniform_C_pos {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (hs : s.Nonempty) {k : ℕ} (hk : k ≤ N) : 0 < C := by
  classical
  obtain ⟨i, hi⟩ := hs
  have hle := 𝒰.card_class_le k hk _ (𝒰.cover.assign_mem k hk i hi)
  have hne : (coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i)).Nonempty :=
    ⟨i, by simp [coverClass, hi]⟩
  have h1 : (1 : NNReal)
      ≤ ((coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr hne
  by_contra h
  have h0 : C = 0 := le_antisymm (not_lt.mp h) bot_le
  have hc : C * 𝒰.branchingN k = 0 := by
    have := congrArg (fun x : NNReal => x * 𝒰.branchingN k) h0
    simpa using this
  exact absurd (h1.trans (hle.trans_eq hc)) (by norm_num)

/-! ### X4 — the two-level count band -/

/-- **X4 — the two-level count band, a theorem of `Tube.UniformTubeSet`.**

GWZ Definition 2.1(iii) already pins the one-level descendant counts to the profile `branchingN`
within `C` (`card_class_le`, `le_card_class`).  Because the assignments nest
(`ChainCoverSystem.tube_assign_le`), the level-`c` classes of the cells inside a level-`p` node cover
the level-`p` class and are pairwise disjoint subsets of the contained set, so the number of
level-`c` cells inside a level-`p` node is pinned to `branchingN p / branchingN c` within `C ^ 3`,
**at every pair of levels and every level-`p` node**.  This is the refined source's "descendant
counts and two-level counts... pairwise within a factor two at every fixed level or pair of levels"
(l.4032-4035); the tree carries the hypothesis already and the window twin needs no third field.  The upper half uses the existing containment bracket
`Tube.UniformTubeSet.card_familyIn_le` (`C ^ 2`). -/
theorem card_nodesUnder_band {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C)
    {p c : ℕ} (hpc : p ≤ c) (hc : c ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet p) :
    𝒰.branchingN p ≤ C ^ 2 * (𝒰.branchingN c * ((𝒰.nodesUnder c p j).card : NNReal)) ∧
      ((𝒰.nodesUnder c p j).card : NNReal) * 𝒰.branchingN c ≤ C ^ 3 * 𝒰.branchingN p := by
  classical
  have hpN : p ≤ N := hpc.trans hc
  have hmem_nodes : ∀ j', j' ∈ 𝒰.nodesUnder c p j ↔ j' ∈ 𝒰.cover.indexSet c ∧
      (𝒰.cover.tube c j').toConvexSpaceBody ≤ (𝒰.cover.tube p j).toConvexSpaceBody := by
    intro j'
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn, Finset.mem_filter]
  have hmem_cls : ∀ (k : ℕ) (j' i : ι),
      i ∈ coverClass s (𝒰.cover.assign k) j' ↔ i ∈ s ∧ 𝒰.cover.assign k i = j' := by
    intro k j' i
    simp only [coverClass, Finset.mem_filter]
  -- the iterated nesting, through the chain view of the cover
  have htube : ∀ i ∈ s, (𝒰.cover.tube c (𝒰.cover.assign c i)).toConvexSpaceBody
      ≤ (𝒰.cover.tube p (𝒰.cover.assign p i)).toConvexSpaceBody := fun i hi =>
    𝒰.cover.toChain.tube_assign_le hpc hc hi
  constructor
  · -- lower half: the level-`p` class is covered by the classes of its cells' level-`c` nodes
    have hlow := 𝒰.le_card_class p hpN j hj
    have himg_sub : (coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c)
        ⊆ 𝒰.nodesUnder c p j := by
      intro j' hj'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      obtain ⟨his, hip⟩ := (hmem_cls p j i).mp hi
      refine (hmem_nodes _).mpr ⟨𝒰.cover.assign_mem c hc i his, ?_⟩
      have h := htube i his
      rwa [hip] at h
    have hsub : coverClass s (𝒰.cover.assign p) j
        ⊆ ((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c)).biUnion
            (fun j' => coverClass s (𝒰.cover.assign c) j') := by
      intro i hi
      obtain ⟨his, -⟩ := (hmem_cls p j i).mp hi
      exact Finset.mem_biUnion.mpr
        ⟨_, Finset.mem_image_of_mem _ hi, (hmem_cls c _ i).mpr ⟨his, rfl⟩⟩
    have hcard : ((coverClass s (𝒰.cover.assign p) j).card : NNReal)
        ≤ ((𝒰.nodesUnder c p j).card : NNReal) * (C * 𝒰.branchingN c) := by
      calc ((coverClass s (𝒰.cover.assign p) j).card : NNReal)
          ≤ ((((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c)).biUnion
              (fun j' => coverClass s (𝒰.cover.assign c) j')).card : NNReal) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ((∑ x ∈ (coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c),
              (coverClass s (𝒰.cover.assign c) x).card : ℕ) : NNReal) := by
            exact_mod_cast Finset.card_biUnion_le
        _ = ∑ x ∈ (coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c),
              ((coverClass s (𝒰.cover.assign c) x).card : NNReal) := by
            rw [Nat.cast_sum]
        _ ≤ ∑ _x ∈ (coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c),
              (C * 𝒰.branchingN c) := by
            refine Finset.sum_le_sum (fun x hx => ?_)
            exact 𝒰.card_class_le c hc x ((hmem_nodes x).mp (himg_sub hx)).1
        _ = (((coverClass s (𝒰.cover.assign p) j).image (𝒰.cover.assign c)).card : NNReal)
              * (C * 𝒰.branchingN c) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((𝒰.nodesUnder c p j).card : NNReal) * (C * 𝒰.branchingN c) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card himg_sub)
              (by positivity)
    calc 𝒰.branchingN p ≤ C * ((coverClass s (𝒰.cover.assign p) j).card : NNReal) := hlow
      _ ≤ C * (((𝒰.nodesUnder c p j).card : NNReal) * (C * 𝒰.branchingN c)) := by gcongr
      _ = C ^ 2 * (𝒰.branchingN c * ((𝒰.nodesUnder c p j).card : NNReal)) := by ring
  · -- upper half: the cells' classes are disjoint subsets of the contained set of `T_p`
    have hdisj : ((𝒰.nodesUnder c p j : Finset ι) : Set ι).PairwiseDisjoint
        (fun j' => coverClass s (𝒰.cover.assign c) j') := by
      intro j₁ _ j₂ _ hne
      refine Finset.disjoint_left.mpr (fun i h1 h2 => hne ?_)
      exact ((hmem_cls c j₁ i).mp h1).2.symm.trans ((hmem_cls c j₂ i).mp h2).2
    have hbi_sub : (𝒰.nodesUnder c p j).biUnion (fun j' => coverClass s (𝒰.cover.assign c) j')
        ⊆ Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
            (𝒰.cover.tube p j).toConvexSpaceBody := by
      intro i hi
      obtain ⟨j', hj', hij'⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨his, hic⟩ := (hmem_cls c j' i).mp hij'
      simp only [Kakeya.familyIn, Finset.mem_filter]
      refine ⟨his, ?_⟩
      have h1 := 𝒰.cover.le_tube_assign c hc i his
      rw [hic] at h1
      exact h1.trans ((hmem_nodes j').mp hj').2
    have hsum : (∑ x ∈ 𝒰.nodesUnder c p j, ((coverClass s (𝒰.cover.assign c) x).card : NNReal))
        ≤ C ^ 2 * 𝒰.branchingN p := by
      calc (∑ x ∈ 𝒰.nodesUnder c p j, ((coverClass s (𝒰.cover.assign c) x).card : NNReal))
          = ((((𝒰.nodesUnder c p j).biUnion
              (fun j' => coverClass s (𝒰.cover.assign c) j')).card : ℕ) : NNReal) := by
            rw [Finset.card_biUnion hdisj, Nat.cast_sum]
        _ ≤ ((Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
              (𝒰.cover.tube p j).toConvexSpaceBody).card : NNReal) := by
            exact_mod_cast Finset.card_le_card hbi_sub
        _ ≤ C ^ 2 * 𝒰.branchingN p := 𝒰.card_familyIn_le hpN j
    calc ((𝒰.nodesUnder c p j).card : NNReal) * 𝒰.branchingN c
        = ∑ _x ∈ 𝒰.nodesUnder c p j, 𝒰.branchingN c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ 𝒰.nodesUnder c p j, C * ((coverClass s (𝒰.cover.assign c) x).card : NNReal) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          exact 𝒰.le_card_class c hc x ((hmem_nodes x).mp hx).1
      _ = C * ∑ x ∈ 𝒰.nodesUnder c p j, ((coverClass s (𝒰.cover.assign c) x).card : NNReal) := by
          rw [Finset.mul_sum]
      _ ≤ C * (C ^ 2 * 𝒰.branchingN p) := by gcongr
      _ = C ^ 3 * 𝒰.branchingN p := by ring

/-! ### X5 — clause 4 from one scalar inequality on the profile -/

/-- The normalised branching profile of the hierarchy at a level: `#class / ρ_k^{2+4ζ}`.  The count
floor at the pair `(p, c)` is exactly `C² · parentProfile c ≤ parentProfile p` (X5). -/
noncomputable def parentProfile {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (ζ : ℝ) (k : ℕ) : ℝ :=
  (𝒰.branchingN k : ℝ) / (Tube.gridScale δ N k : ℝ) ^ (2 + 4 * ζ)

/-- **X5 — the count floor is a statement about the branching profile.**  By X4 the two-level count
is pinned to `branchingN p / branchingN c` at *every* level-`p` node, so the existing `hfloor`
clause 4 -- universally quantified over every level-`a` node and every level-`p` cell -- follows
from the single inequality `C² · parentProfile c ≤ parentProfile p`.  The per-cell universality that
 priced inside H5 is free. -/
theorem card_nodesUnder_ge_of_profile {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (hδ0 : 0 < δ) (hs : s.Nonempty) {ζ : ℝ}
    {p c : ℕ} (hpc : p ≤ c) (hc : c ≤ N)
    (hprofile : (C : ℝ) ^ 2 * parentProfile 𝒰 ζ c ≤ parentProfile 𝒰 ζ p) :
    ∀ j ∈ 𝒰.cover.indexSet p,
      ((Tube.gridScale δ N p : ℝ) / (Tube.gridScale δ N c : ℝ)) ^ (2 + 4 * ζ)
        ≤ ((𝒰.nodesUnder c p j).card : ℝ) := by
  intro j hj
  have hlow := (card_nodesUnder_band 𝒰 hpc hc hj).1
  have hbc : (0 : ℝ) < 𝒰.branchingN c := by exact_mod_cast branchingN_pos 𝒰 hs hc
  have hC : (0 : ℝ) < C := by exact_mod_cast uniform_C_pos 𝒰 hs hc
  have hρp : (0 : ℝ) < (Tube.gridScale δ N p : ℝ) := by exact_mod_cast gridScale_pos hδ0 _ _
  have hρc : (0 : ℝ) < (Tube.gridScale δ N c : ℝ) := by exact_mod_cast gridScale_pos hδ0 _ _
  have hlowR : (𝒰.branchingN p : ℝ)
      ≤ (C : ℝ) ^ 2 * ((𝒰.branchingN c : ℝ) * ((𝒰.nodesUnder c p j).card : ℝ)) := by
    exact_mod_cast hlow
  unfold parentProfile at hprofile
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)] at hprofile
  rw [Real.div_rpow hρp.le hρc.le, div_le_iff₀ (by positivity)]
  have hpos : (0 : ℝ) < (C : ℝ) ^ 2 * (𝒰.branchingN c : ℝ) := by positivity
  have h2 : (C : ℝ) ^ 2 * (𝒰.branchingN c : ℝ)
        * (Tube.gridScale δ N p : ℝ) ^ (2 + 4 * ζ)
      ≤ (C : ℝ) ^ 2 * (𝒰.branchingN c : ℝ)
        * (((𝒰.nodesUnder c p j).card : ℝ) * (Tube.gridScale δ N c : ℝ) ^ (2 + 4 * ζ)) := by
    calc (C : ℝ) ^ 2 * (𝒰.branchingN c : ℝ) * (Tube.gridScale δ N p : ℝ) ^ (2 + 4 * ζ)
        ≤ (𝒰.branchingN p : ℝ) * (Tube.gridScale δ N c : ℝ) ^ (2 + 4 * ζ) := hprofile
      _ ≤ ((C : ℝ) ^ 2 * ((𝒰.branchingN c : ℝ) * ((𝒰.nodesUnder c p j).card : ℝ)))
            * (Tube.gridScale δ N c : ℝ) ^ (2 + 4 * ζ) := by gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 hpos

/-! ### X7 — the genuine parent as the profile's argmax -/

/-- **X7 — the genuine parent, as the profile's argmax over the admissible levels.**  If the level
`a` itself is admissible (X1, the existing `parentAdmissible_self`) and `a < mlo`, some admissible
`p ∈ [a, mlo)` maximises `parentProfile` among the admissible levels of `[a, mlo)`.  This is *not* a
re-cut of `Kakeya.ML2Core.genuineParent`, which stays as existing and continues to serve clause 3. -/
theorem exists_parentProfile_max {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) {η' ζ : ℝ} {a mlo : ℕ} (hamlo : a < mlo)
    (ha : ParentAdmissible 𝒰 η' a a) :
    ∃ p, a ≤ p ∧ p < mlo ∧ ParentAdmissible 𝒰 η' a p ∧
      ∀ k, a ≤ k → k < mlo → ParentAdmissible 𝒰 η' a k →
        parentProfile 𝒰 ζ k ≤ parentProfile 𝒰 ζ p := by
  classical
  set S : Finset ℕ := (Finset.range mlo).filter (fun k => a ≤ k ∧ ParentAdmissible 𝒰 η' a k)
    with hS
  have hmemS : ∀ k, k ∈ S ↔ k < mlo ∧ a ≤ k ∧ ParentAdmissible 𝒰 η' a k := by
    intro k
    simp only [hS, Finset.mem_filter, Finset.mem_range]
  obtain ⟨p, hpS, hmax⟩ :=
    Finset.exists_max_image S (parentProfile 𝒰 ζ) ⟨a, (hmemS a).mpr ⟨hamlo, le_rfl, ha⟩⟩
  obtain ⟨hp1, hp2, hp3⟩ := (hmemS p).mp hpS
  exact ⟨p, hp2, hp1, hp3, fun k hak hk hadm => hmax k ((hmemS k).mpr ⟨hk, hak, hadm⟩)⟩

/-! ### X6a — the fill at one cell counts -/

/-- **X6a — the fill gives the count at one cell.**  `FillAt 𝒰 κ k c j` and `Λ ≤ Δ_max(𝕋_c[T_k])`
give `κ · Λ · c_vol ρ_k^{n−1} ≤ #𝕋_c[T_k] · C_vol ρ_c^{n−1}`: the density on the cell times the
cell's volume is the total volume of the cells inside it
(`Kakeya.sum_volume_eq_densityIn_mul_volume'`), each of volume `≤ C_vol ρ_c^{n−1}`
(`Tube.volume_le`), and the cell's volume is `≥ c_vol ρ_k^{n−1}` (`Tube.le_volume`). -/
theorem card_nodesUnder_ge_of_fillAt {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) (hδ1 : δ ≤ 1) {κ : ℝ} {k c : ℕ} {j : ι}
    (hfill : FillAt 𝒰 κ k c j) {Λ : ENNReal}
    (hΛ : Λ ≤ Kakeya.maxDensity (𝒰.nodesUnder c k j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ENNReal.ofReal κ * Λ
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((Tube.gridScale δ N k : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ ((𝒰.nodesUnder c k j).card : ENNReal)
        * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  unfold FillAt at hfill
  have hall : ∀ j' ∈ 𝒰.nodesUnder c k j,
      (𝒰.cover.tube c j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody := by
    intro j' hj'
    have h := hj'
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.2
  have hsum := Kakeya.sum_volume_eq_densityIn_mul_volume'
    (s := 𝒰.nodesUnder c k j) (W := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) hall
  have hsumle : ∑ j' ∈ 𝒰.nodesUnder c k j, volume ((𝒰.cover.tube c j').toConvexSpaceBody).carrier
      ≤ ((𝒰.nodesUnder c k j).card : ENNReal)
        * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((Tube.gridScale δ N c : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _
      (fun j' _ => Tube.volume_le (gridScale_le_one hδ1 _ _) (𝒰.cover.tube c j'))
  have hUlo : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((Tube.gridScale δ N k : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)
      ≤ volume ((𝒰.cover.tube k j).toConvexSpaceBody).carrier :=
    Tube.le_volume (𝒰.cover.tube k j)
  calc ENNReal.ofReal κ * Λ
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((Tube.gridScale δ N k : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        * volume ((𝒰.cover.tube k j).toConvexSpaceBody).carrier :=
        mul_le_mul' (mul_le_mul' le_rfl hΛ) hUlo
    _ ≤ Kakeya.densityIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          (𝒰.cover.tube k j).toConvexSpaceBody
        * volume ((𝒰.cover.tube k j).toConvexSpaceBody).carrier := mul_le_mul' hfill le_rfl
    _ = ∑ j' ∈ 𝒰.nodesUnder c k j, volume ((𝒰.cover.tube c j').toConvexSpaceBody).carrier :=
        hsum.symm
    _ ≤ _ := hsumle

/-! ### X6b (core) — when the fill fails, the biased maximizer is small -/

open scoped Classical in
/-- **X6b, the core: failure of the fill makes the biased maximizer small.**  On the unrestricted
family `𝕋_c[T_k]`, G2′ (`exists_biasedMaximizer_densityIn_ge`) supplies `t ⊆ 𝕋_c[T_k]` with hull `W`
and `(|W|/|T_k|)^ϖ · Δ_max ≤ Δ(·, W)`; the mass inside `W` is at most the mass inside `T_k`, i.e.
`Δ(·, W)·|W| ≤ Δ(·, T_k)·|T_k|`; and `¬ FillAt` says `Δ(·, T_k) < κ · Δ_max`.  Cancelling `Δ_max`
(positive, finite) and `|T_k|`: `(|W|/|T_k|)^{1+ϖ} < κ`.  The thickness reading — `W` contains a
`ρ_c`-cell, so `c₃ · a_W b_W c_W ≤ |W|` with `c_W ≥ 1/2` bounds `a_W b_W` — and the eccentric/thin
dichotomy are the next rows. -/
theorem exists_maximizer_small_of_not_fillAt {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) (hδ0 : 0 < δ) {ϖ : ℝ} (hϖ : 0 < ϖ)
    {κ : ℝ} {k c : ℕ} {j : ι} (hnodes : (𝒰.nodesUnder c k j).Nonempty)
    (hnf : ¬ FillAt 𝒰 κ k c j) :
    ∃ t ⊆ 𝒰.nodesUnder c k j, t.Nonempty ∧
      (volume (t.convexHull_biUnion (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
          / volume (𝒰.cover.tube k j).carrier) ^ (1 + ϖ) < ENNReal.ofReal κ := by
  unfold FillAt at hnf
  have hall : ∀ j' ∈ 𝒰.nodesUnder c k j,
      (𝒰.cover.tube c j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody := by
    intro j' hj'
    have h := hj'
    simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn,
      Finset.mem_filter] at h
    exact h.2
  have hvolpos : ∀ j', 0 < volume ((𝒰.cover.tube c j').toConvexSpaceBody).carrier := by
    intro j'
    refine lt_of_lt_of_le ?_ (Tube.le_volume (𝒰.cover.tube c j'))
    have hc0 : (0 : ENNReal) < ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) := by
      exact_mod_cast Tube.le_volume.c_pos _
    have hρ : (0 : ENNReal) < ((Tube.gridScale δ N c : NNReal) : ENNReal) := by
      exact_mod_cast gridScale_pos hδ0 N c
    exact ENNReal.mul_pos hc0.ne' (pow_ne_zero _ hρ.ne')
  obtain ⟨j₀, hj₀⟩ := hnodes
  have hpos : ∃ i ∈ 𝒰.nodesUnder c k j,
      0 < volume ((𝒰.cover.tube c i).toConvexSpaceBody).carrier := ⟨j₀, hj₀, hvolpos j₀⟩
  obtain ⟨t, hts, htne, hden⟩ := exists_biasedMaximizer_densityIn_ge hϖ hpos hall
  refine ⟨t, hts, htne, ?_⟩
  set V := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody with hV
  set U := (𝒰.cover.tube k j).toConvexSpaceBody with hU
  set W := t.convexHull_biUnion V with hW
  set Δ := Kakeya.maxDensity (𝒰.nodesUnder c k j) V with hΔ
  have hUtop : volume U.carrier ≠ ⊤ := U.isCompact.measure_ne_top
  have hU0 : volume U.carrier ≠ 0 :=
    ((hvolpos j₀).trans_le (measure_mono (SetLike.coe_subset_coe.mpr (hall j₀ hj₀)))).ne'
  have hWtop : volume W.carrier ≠ ⊤ := W.isCompact.measure_ne_top
  obtain ⟨i₁, hi₁⟩ := htne
  have hW0 : volume W.carrier ≠ 0 :=
    ((hvolpos i₁).trans_le (measure_mono
      (SetLike.coe_subset_coe.mpr (t.le_convexHull_biUnion V hi₁)))).ne'
  have hΔ0 : Δ ≠ 0 := (lt_of_lt_of_le zero_lt_one (Kakeya.one_le_maxDensity hpos)).ne'
  have hΔtop : Δ ≠ ⊤ := Kakeya.maxDensity_ne_top _ _
  have hlt : Kakeya.densityIn (𝒰.nodesUnder c k j) V U < ENNReal.ofReal κ * Δ := not_le.mp hnf
  -- the mass inside `W` is at most the mass inside `U`
  have hmass : Kakeya.densityIn (𝒰.nodesUnder c k j) V W * volume W.carrier
      ≤ Kakeya.densityIn (𝒰.nodesUnder c k j) V U * volume U.carrier := by
    rw [← Kakeya.sum_volume_eq_densityIn_mul_volume, ← Kakeya.sum_volume_eq_densityIn_mul_volume' hall]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hchain : (volume W.carrier / volume U.carrier) ^ ϖ * Δ * volume W.carrier
      < ENNReal.ofReal κ * Δ * volume U.carrier :=
    calc (volume W.carrier / volume U.carrier) ^ ϖ * Δ * volume W.carrier
        ≤ Kakeya.densityIn (𝒰.nodesUnder c k j) V W * volume W.carrier := mul_le_mul' hden le_rfl
      _ ≤ Kakeya.densityIn (𝒰.nodesUnder c k j) V U * volume U.carrier := hmass
      _ < ENNReal.ofReal κ * Δ * volume U.carrier := ENNReal.mul_lt_mul_left hU0 hUtop hlt
  -- cancel `Δ`
  have h2 : (volume W.carrier / volume U.carrier) ^ ϖ * volume W.carrier
      < ENNReal.ofReal κ * volume U.carrier := by
    have h := hchain
    rw [show (volume W.carrier / volume U.carrier) ^ ϖ * Δ * volume W.carrier
        = (volume W.carrier / volume U.carrier) ^ ϖ * volume W.carrier * Δ by ring,
      show ENNReal.ofReal κ * Δ * volume U.carrier = ENNReal.ofReal κ * volume U.carrier * Δ by ring]
      at h
    exact lt_of_mul_lt_mul_right' h
  -- divide by `|U|`
  have h3 : (volume W.carrier / volume U.carrier) ^ ϖ * (volume W.carrier / volume U.carrier)
      < ENNReal.ofReal κ := by
    rw [← mul_div_assoc]
    exact (ENNReal.div_lt_iff (Or.inl hU0) (Or.inl hUtop)).mpr h2
  have hr0 : volume W.carrier / volume U.carrier ≠ 0 :=
    (ENNReal.div_pos hW0 hUtop).ne'
  have hrtop : volume W.carrier / volume U.carrier ≠ ⊤ := (ENNReal.div_lt_top hWtop hU0).ne
  rw [ENNReal.rpow_add _ _ hr0 hrtop, ENNReal.rpow_one, mul_comm]
  exact h3

end Kakeya.ML2Core

end
