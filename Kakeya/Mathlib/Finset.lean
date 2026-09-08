/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push

/-!
# Fiberwise summation over a selected set of blocks

Following the blueprint notation `fiberwiseSetup` of the subsection
`subsec:fiberwiseSum` ("Fiberwise summation over a selected set of blocks"),

* `{i ∈ u | p i = j}` is the fiber `u_j` of `p` over `j` inside `u`;
* `{i ∈ u | p i ∈ t'}` is the part `u'` of `u` lying over the selected blocks `t'`;
* `{i ∈ u' | p i = j}` is `u'_j`.

Everything the development needs about this setup is already in Mathlib:
`Finset.disjiUnion_filter_eq` (with `Set.pairwiseDisjoint_filter`) decomposes `u'` as the
disjoint union of the `u_j`, `Finset.sum_fiberwise_eq_sum_filter` turns a sum over `u'` into a
double sum, and `Finset.sum_fiberwise_of_maps_to` (with `Finset.filter_true_of_mem`) does the
same when `t'` already contains the image of `u`. The one missing identity is recorded below;
it is a candidate for Mathlib.
-/

@[expose] public section

namespace Finset

variable {ι κ : Type*} [DecidableEq κ] {p : ι → κ} {s u : Finset ι} {t' : Finset κ} {j : κ}

/-- **Collapse of the selection condition on a selected fiber** (blueprint
`lem:fiberwiseFilterCollapse`): for a selected block `j ∈ t'` one has `u'_j = u_j`. -/
theorem filter_mem_filter_eq (hj : j ∈ t') :
    {i ∈ {i ∈ u | p i ∈ t'} | p i = j} = {i ∈ u | p i = j} := by
  rw [Finset.filter_filter]
  refine Finset.filter_congr (fun i hi => ?_)
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h ▸ hj, h⟩

/-- **The selected blocks are already blocks of the selected part** (blueprint
`lem:factoringStep2BlocksSubsetImage`): if `t' ⊆ p '' u` then `t' ⊆ p '' u'`, where
`u' = {i ∈ u | p i ∈ t'}`. -/
theorem subset_image_filter_mem (ht' : t' ⊆ u.image p) :
    t' ⊆ {i ∈ u | p i ∈ t'}.image p := by
  intro j hj
  have hj_image : j ∈ u.image p := ht' hj
  rcases Finset.mem_image.mp hj_image with ⟨i, hi, hp⟩
  have hi_filter : i ∈ {i ∈ u | p i ∈ t'} := by
    apply Finset.mem_filter.mpr
    exact ⟨hi, by
      rw [hp]
      exact hj⟩
  apply Finset.mem_image.mpr
  exact ⟨i, hi_filter, hp⟩

/-- **The selected blocks are not more numerous than the ambient index set** (blueprint
`lem:factoringStep2BlockBound`): `|t'| ≤ |p '' u'| ≤ |u'| ≤ |s|`, where
`u' = {i ∈ u | p i ∈ t'}`. -/
theorem card_le_card_of_subset_image (hu : u ⊆ s) (ht' : t' ⊆ u.image p) : t'.card ≤ s.card := by
  let u' := {i ∈ u | p i ∈ t'}
  have h1 : t' ⊆ u'.image p := subset_image_filter_mem ht'
  have h1card : t'.card ≤ (u'.image p).card := Finset.card_le_card h1
  have h2card : (u'.image p).card ≤ u'.card := Finset.card_image_le
  have h3 : u' ⊆ u := Finset.filter_subset _ _
  have h3' : u' ⊆ s := Finset.Subset.trans h3 hu
  have h3card : u'.card ≤ s.card := Finset.card_le_card h3'
  calc
    t'.card ≤ (u'.image p).card := h1card
    _ ≤ u'.card := h2card
    _ ≤ s.card := h3card


/-- **Carrier-injective subset** (dedup): any finite family `f : κ → Set E` over a
`Finset t` has a subset `t' ⊆ t` on which `f` is injective (one representative per
distinct value).  Used to feed the shaded uniformization a carrier-injective
index when the translated family's essential distinctness is not available. -/
lemma exists_carrier_injOn_subset {κ E : Type*} (t : Finset κ) (f : κ → Set E) :
    ∃ t' : Finset κ, t' ⊆ t ∧ Set.InjOn f (t' : Set κ) ∧ (t.Nonempty → t'.Nonempty) := by
  classical
  choose g hg_mem hg_eq using
    (fun b : {b : Set E // b ∈ t.image f} => Finset.mem_image.mp b.2)
  refine ⟨(t.image f).attach.image g, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ha
    exact hg_mem b
  · intro a ha a' ha' hfa
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha ha'
    obtain ⟨b, -, rfl⟩ := ha
    obtain ⟨b', -, rfl⟩ := ha'
    exact congrArg g (Subtype.ext (by rw [← hg_eq b, ← hg_eq b', hfa]))
  · intro ht
    obtain ⟨x, hx⟩ := ht
    exact Finset.Nonempty.image
      ⟨⟨f x, Finset.mem_image_of_mem f hx⟩, Finset.mem_attach _ _⟩ g

open scoped Classical in
/-- **Greedy maximal separated subset.**  For a symmetric "distance" `d` with `d a a = 0` and
a threshold `ε ≥ 0`, every `Finset` `s` contains a subset `s'` that is `ε`-separated and
`ε`-dense in `s`.  Taking `s'` of maximal cardinality among `ε`-separated subsets, an element
of `s` at distance `> ε` from all of `s'` could be added, contradicting maximality. -/
theorem exists_separated_net {α : Type*} (s : Finset α) (d : α → α → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (hd_self : ∀ a, d a a = 0) (hd_symm : ∀ a b, d a b = d b a) :
    ∃ s' ⊆ s, (∀ a ∈ s', ∀ b ∈ s', a ≠ b → ε < d a b) ∧ ∀ a ∈ s, ∃ b ∈ s', d a b ≤ ε := by
  let S := s.powerset.filter fun t : Finset α => ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ε < d a b
  have hS_nonempty : S.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [S]
  obtain ⟨s', hs'mem, hs'max⟩ := Finset.exists_max_image S Finset.card hS_nonempty
  rcases Finset.mem_filter.mp hs'mem with ⟨hs'pows, hs'sep⟩
  have hs'sub : s' ⊆ s := Finset.mem_powerset.mp hs'pows
  refine ⟨s', hs'sub, hs'sep, ?_⟩
  intro a ha
  by_cases h : ∃ b ∈ s', d a b ≤ ε
  · rcases h with ⟨b, hb, hle⟩
    exact ⟨b, hb, hle⟩
  · push Not at h
    have ha_not_mem : a ∉ s' := by
      intro ha_mem
      have hlt : ε < d a a := h a ha_mem
      rw [hd_self a] at hlt
      linarith
    have hd_symm_a : ∀ x : α, d x a = d a x := by
      intro x
      exact hd_symm x a
    have h_insert_sep : ∀ a' ∈ insert a s', ∀ b' ∈ insert a s', a' ≠ b' → ε < d a' b' := by
      intro a' ha' b' hb' hne
      have ha'_cases : a' = a ∨ a' ∈ s' := by simpa using ha'
      have hb'_cases : b' = a ∨ b' ∈ s' := by simpa using hb'
      rcases ha'_cases with (rfl | ha's')
      · rcases hb'_cases with (rfl | hb's')
        · exfalso; exact hne rfl
        · exact h b' hb's'
      · rcases hb'_cases with (rfl | hb's')
        · rw [hd_symm_a a']
          exact h a' ha's'
        · exact hs'sep a' ha's' b' hb's' hne
    have h_insert_pow : insert a s' ∈ s.powerset := by
      apply Finset.mem_powerset.mpr
      intro x hx
      have hx_cases : x = a ∨ x ∈ s' := by simpa using hx
      rcases hx_cases with (rfl | hx')
      · exact ha
      · exact hs'sub hx'
    have h_insert_mem : insert a s' ∈ S :=
      Finset.mem_filter.mpr ⟨h_insert_pow, h_insert_sep⟩
    have hcard_lt : s'.card < (insert a s').card := by
      rw [Finset.card_insert_of_notMem ha_not_mem]
      omega
    have hcard_le : (insert a s').card ≤ s'.card := hs'max (insert a s') h_insert_mem
    omega

end Finset
