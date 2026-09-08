/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Card

/-!
# Greedy selection in a bounded-degree graph

A finite symmetric irreflexive relation of degree at most `D` on a weighted finite index set
admits an independent subset carrying at least a `1 / (D + 1)` fraction of the total weight
(`Kakeya.exists_pairwise_not_of_degree_le`, blueprint `lem:greedyWeightedIndependentSet`).

This is the combinatorial half of the subfamily selection of the plank presentation: the
clustering relation on the enclosing planks has bounded degree
(`Kakeya.VeryNotSticky.plankClusterBound`), and the selection
(`Kakeya.VeryNotSticky.plankSubfamilySelection`) is this lemma applied to it, with the shaded
masses as weights.

Mathlib has `SimpleGraph.IsIndepSet` and the existence of *maximum* independent sets, but no
weighted greedy bound of this shape. The weights live in `ℝ≥0∞` and no finiteness is needed:
if some weight is `∞` then the greedily chosen maximal weight is `∞` and both sides of the
conclusion are `∞`.

The blueprint's auxiliary statement `lem:sumLeCardMulMax` — a finite sum in `[0, ∞]` is at
most the cardinality times a uniform upper bound for its terms — is Mathlib's
`Finset.sum_le_card_nsmul` and is not restated here.
-/

@[expose] public section

open Finset

namespace Kakeya

/-- **Greedy selection in a bounded-degree graph** (blueprint
`lem:greedyWeightedIndependentSet`).

Let `r` be a symmetric irreflexive relation on a finite index set `J` all of whose degrees are
at most `D`, and let `y` be `[0, ∞]`-valued weights. Then some `r`-independent `J' ⊆ J`
carries at least a `1 / (D + 1)` fraction of the total weight, stated multiplicatively as
`∑_{J} y ≤ (D + 1) ∑_{J'} y` so that no division in `ℝ≥0∞` occurs.

The proof is strong induction on `#J`: pick `i` maximising `y`, discard its closed
neighbourhood — whose weight is at most `(D + 1) y i` by `Finset.sum_le_card_nsmul` — and
recurse on the rest.

The degree bound is stated with `Set.ncard` and not with `Finset.card`, so that `r` needs no
`DecidableRel` instance. At the one call site
(`Kakeya.VeryNotSticky.plankSubfamilySelection`) the relation is
`fun i j ↦ ¬ IsEssentiallyDistinct …`, which is not decidable, and every caller would
otherwise have to insert `Classical.decRel`; `Kakeya.VeryNotSticky.plankClusterBound` already
states its degree bound in the `Set.ncard` form. -/
theorem exists_pairwise_not_of_degree_le {ι : Type*} (J : Finset ι)
    (r : ι → ι → Prop) (hsymm : ∀ i j, r i j → r j i) (hirr : ∀ i, ¬ r i i)
    {D : ℕ} (hdeg : ∀ i ∈ J, {j ∈ (J : Set ι) | r j i}.ncard ≤ D) (y : ι → ENNReal) :
    ∃ J' ⊆ J, (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
      ∑ j ∈ J, y j ≤ (D + 1 : ℕ) * ∑ j ∈ J', y j := by
  classical
  let q : Finset ι → Prop := fun S =>
    (∀ i ∈ S, (S.filter (fun j => r j i)).card ≤ D) →
      ∃ J' ⊆ S, (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
        ∑ j ∈ S, y j ≤ (D + 1 : ℕ) * ∑ j ∈ J', y j
  let step : ∀ s : Finset ι, (∀ t ⊂ s, q t) → q s := by
    intro S ih hdegS
    by_cases hS : S = ∅
    · subst S
      refine ⟨∅, by simp, by simp, ?_⟩
      simp
    · have hnonempty : S.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.mpr hS
      rcases Finset.exists_max_image S y hnonempty with ⟨i, hiS, himax⟩
      let T : Finset ι := S.filter (fun j => r j i)
      let N : Finset ι := insert i T
      have hTcard : T.card ≤ D := by
        simpa [T] using hdegS i hiS
      have hNcard : N.card ≤ D + 1 := by
        calc
          N.card = (insert i T).card := by rfl
          _ ≤ T.card + 1 := Finset.card_insert_le i T
          _ ≤ D + 1 := Nat.add_le_add_right hTcard 1
      have hle : ∀ j ∈ N, y j ≤ y i := by
        intro j hj
        simp only [N, T, Finset.mem_insert, Finset.mem_filter] at hj
        rcases hj with rfl | ⟨hjS, _⟩
        · rfl
        · exact himax j hjS
      have hNsum : ∑ j ∈ N, y j ≤ (D + 1 : ℕ) * y i := by
        calc
          ∑ j ∈ N, y j ≤ N.card • y i :=
            Finset.sum_le_card_nsmul N (fun j => y j) (y i) hle
          _ ≤ (D + 1 : ℕ) • y i := by
            exact nsmul_le_nsmul_left zero_le hNcard
          _ = (D + 1 : ℕ) * y i := by rw [nsmul_eq_mul]
      have hNS : N ⊆ S := by
        intro x hx
        simp only [N, T, Finset.mem_insert, Finset.mem_filter] at hx
        rcases hx with rfl | ⟨hxS, _⟩
        · exact hiS
        · exact hxS
      have hsubN : S \ N ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · exact Finset.sdiff_subset
        · intro hEq
          have : i ∈ S \ N := by rw [hEq]; exact hiS
          exact (Finset.mem_sdiff.mp this).2 (by simp [N])
      have hdegSub : ∀ i ∈ S \ N, ((S \ N).filter (fun j => r j i)).card ≤ D := by
        intro i' hiSub
        have hi'S : i' ∈ S := (Finset.mem_sdiff.mp hiSub).1
        have hsubf : (S \ N).filter (fun j => r j i') ⊆ S.filter (fun j => r j i') := by
          intro j hj
          have hjf := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hjf.1).1, hjf.2⟩
        exact le_trans (Finset.card_le_card hsubf) (hdegS i' hi'S)
      rcases ih (S \ N) hsubN hdegSub with ⟨A, hAsub, hApair, hAsum⟩
      have hiNotA : i ∉ A := by
        intro hmem
        have : i ∈ S \ N := hAsub hmem
        exact (Finset.mem_sdiff.mp this).2 (by simp [N])
      have hnotI : ∀ a ∈ S \ N, ¬ r a i := by
        intro a haN hri
        have haS : a ∈ S := (Finset.mem_sdiff.mp haN).1
        exact (Finset.mem_sdiff.mp haN).2 (by simp [N, T, haS, hri])
      let ans : Finset ι := insert i A
      have hansSub : ans ⊆ S := by
        intro x hx
        rcases by simpa [ans] using hx with rfl | hxA
        · exact hiS
        · exact (Finset.mem_sdiff.mp (hAsub hxA)).1
      have hpair : (ans : Set ι).Pairwise (fun i j => ¬ r i j) := by
        intro a ha b hb hab
        have ha' : a = i ∨ a ∈ A := by
          simpa [ans, Finset.mem_insert, Finset.mem_coe] using ha
        have hb' : b = i ∨ b ∈ A := by
          simpa [ans, Finset.mem_insert, Finset.mem_coe] using hb
        rcases ha' with ha_eq | haA
        · rcases hb' with hb_eq | hbA
          · subst a
            subst b
            exact hirr i
          · subst a
            exact fun hrib => hnotI b (hAsub hbA) (hsymm i b hrib)
        · rcases hb' with hb_eq | hbA
          · subst b
            exact hnotI a (hAsub haA)
          · exact hApair haA hbA hab
      have hsumAns : ∑ j ∈ ans, y j = y i + ∑ j ∈ A, y j := by
        unfold ans
        rw [Finset.sum_insert hiNotA]
      have hsplit : ∑ j ∈ S, y j = ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j := by
        calc
          ∑ j ∈ S, y j = (∑ j ∈ S \ N, y j) + ∑ j ∈ N, y j :=
            (Finset.sum_sdiff (s₁ := N) (s₂ := S) (f := fun j => y j) hNS).symm
          _ = ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j := by rw [add_comm]
      have hfinal : ∑ j ∈ S, y j ≤ (D + 1 : ℕ) * ∑ j ∈ ans, y j := by
        rw [hsplit]
        calc
          ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j ≤ (D + 1 : ℕ) * y i + (D + 1 : ℕ) * ∑ j ∈ A, y j :=
            add_le_add hNsum hAsum
          _ = (D + 1 : ℕ) * (y i + ∑ j ∈ A, y j) := by rw [mul_add]
          _ = (D + 1 : ℕ) * ∑ j ∈ ans, y j := by rw [hsumAns]
      exact ⟨ans, hansSub, hpair, hfinal⟩
  let hJ : ∀ i ∈ J, (J.filter (fun j => r j i)).card ≤ D := by
    intro i hiJ
    have hTset : (J.filter (fun j => r j i) : Set ι) = {j ∈ (J : Set ι) | r j i} := by
      ext j
      simp
    have hcard : (J.filter (fun j => r j i)).card =
        (J.filter (fun j => r j i) : Set ι).ncard := by
      rw [Set.ncard_coe_finset]
    rw [hcard]
    rw [hTset]
    exact hdeg i hiJ
  exact (Finset.strongInductionOn (p := q) J step) hJ

end Kakeya

end
