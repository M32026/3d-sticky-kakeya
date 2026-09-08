/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting lemmas for GWZ Lemma 7.5

Two double-counting bounds on the cardinality of a `Finset.biUnion`, used to convert the per-scale
translate construction of Lemma 7.5 into a cardinality lower bound on the assembled family.
Both are statements about finite sets only.
-/

@[expose] public section

namespace Kakeya

namespace StickyKakeya

/-- Multiplicity lower bound on a `biUnion` cardinality (double counting): if every element of
`s.biUnion t` lies in at most `μ` of the sets `t a` (`a ∈ s`), then the summed cardinality
`∑ a ∈ s, (t a).card` is at most `μ` times `(s.biUnion t).card`.  Used in the count-LB telescope to
turn the path-count into a lower bound on the distinct leaf count. -/
lemma card_biUnion_ge_of_fiber_le {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : α → Finset β} {μ : ℕ}
    (h_cover : ∀ b ∈ s.biUnion t, (s.filter (fun a => b ∈ t a)).card ≤ μ) :
    (∑ a ∈ s, (t a).card) ≤ μ * (s.biUnion t).card := by
  classical
  calc (∑ a ∈ s, (t a).card)
      = ∑ a ∈ s, ∑ b ∈ s.biUnion t, (if b ∈ t a then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem t ha)]
        exact Finset.card_eq_sum_ones _
    _ = ∑ b ∈ s.biUnion t, ∑ a ∈ s, (if b ∈ t a then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ = ∑ b ∈ s.biUnion t, (s.filter (fun a => b ∈ t a)).card := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.card_filter]
    _ ≤ ∑ _b ∈ s.biUnion t, μ := Finset.sum_le_sum h_cover
    _ = μ * (s.biUnion t).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Cardinality lower bound for a `biUnion` over images of a fixed translation map: if each fibre
lies in at most `μ` of the source sets, the distinct count of the union is at least the summed
per-source image count divided by `μ`.  Count-side companion to `card_biUnion_ge_of_fiber_le`,
specialized so that each per-source image has the *same* cardinality as its preimage. -/
lemma card_biUnion_image_translate_ge {α : Type*} {ι E : Type*}
    [DecidableEq ι] [DecidableEq E] [AddGroup E]
    {s : Finset α} {U : α → Finset (ι × E)} {c : α → E} {μ : ℕ}
    (h_cover : ∀ q ∈ s.biUnion (fun a => (U a).image (fun pr => (pr.1, c a + pr.2))),
        (s.filter (fun a => q ∈ (U a).image (fun pr => (pr.1, c a + pr.2)))).card ≤ μ) :
    (∑ a ∈ s, (U a).card)
      ≤ μ * (s.biUnion (fun a => (U a).image (fun pr => (pr.1, c a + pr.2)))).card := by
  classical
  have hinj : ∀ a ∈ s, ((U a).image (fun pr : ι × E => (pr.1, c a + pr.2))).card
      = (U a).card := by
    intro a _
    refine Finset.card_image_of_injective _ ?_
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (add_left_cancel hxy.2)
  calc (∑ a ∈ s, (U a).card)
      = ∑ a ∈ s, ((U a).image (fun pr : ι × E => (pr.1, c a + pr.2))).card := by
        exact (Finset.sum_congr rfl hinj).symm
    _ ≤ μ * (s.biUnion (fun a => (U a).image (fun pr => (pr.1, c a + pr.2)))).card :=
        card_biUnion_ge_of_fiber_le h_cover
end StickyKakeya

end Kakeya
