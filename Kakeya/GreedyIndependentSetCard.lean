/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.GreedyIndependentSet

/-!
# Greedy selection in a bounded-degree graph, with the cardinality clause

`Kakeya.exists_pairwise_not_of_degree_le` retains a `1/(D+1)` fraction of **one** weight `y`.
Two of the fields of `Kakeya.VeryNotSticky.ThickPlankPresentation` are retention clauses for
*different* weights on the *same* selected subfamily — `sel_card` at the constant weight `1`
and `fullness_ge` at the shaded mass — so a second, independent call of the greedy lemma at
the second weight does **not** discharge them: it returns a second, unrelated subfamily.

Retaining two arbitrary weights at once is genuinely impossible for an independent subset of a
bounded-degree graph (a clique on `D + 1` vertices admits only singletons, and two weights may
be concentrated on different vertices). What *is* true, and is what this file records, is that
the greedy set of `Kakeya.exists_pairwise_not_of_degree_le` is **maximal**, and a maximal
independent set of a graph of degree at most `D` always carries a `1/(D+1)` fraction of the
*cardinality*: every discarded vertex is adjacent to a selected one, and each selected vertex
absorbs at most `D` of them. So the single greedy run at the weight `y` retains `y` *and* the
cardinality simultaneously.

The proof is `Kakeya.exists_pairwise_not_of_degree_le`'s strong induction on `#J`, carrying the
second invariant `#S ≤ (D+1) #ans` alongside `∑_S y ≤ (D+1) ∑_ans y`. Both come from the same
split `S = N ⊎ (S \ N)` at the greedily chosen vertex `i`: the closed neighbourhood `N` has at
most `D + 1` elements and weight at most `(D + 1) y i`, and `ans = insert i A` with `i ∉ A`.

The one-weight statement is left exactly as it is; this is an additive twin.
-/

@[expose] public section

open Finset

namespace Kakeya

/-- **Greedy selection in a bounded-degree graph, retaining the weight and the cardinality**
(the twin of `Kakeya.exists_pairwise_not_of_degree_le`).

Same hypotheses, same subfamily, one further conclusion: `#J ≤ (D + 1) #J'`. The cardinality
clause is not a second application of the weighted statement at the constant weight — that
would produce a different `J'` — but the *maximality* of the greedy set, proved along the same
induction. -/
theorem exists_pairwise_not_of_degree_le_card {ι : Type*} (J : Finset ι)
    (r : ι → ι → Prop) (hsymm : ∀ i j, r i j → r j i) (hirr : ∀ i, ¬ r i i)
    {D : ℕ} (hdeg : ∀ i ∈ J, {j ∈ (J : Set ι) | r j i}.ncard ≤ D) (y : ι → ENNReal) :
    ∃ J' ⊆ J, (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
      ∑ j ∈ J, y j ≤ (D + 1 : ℕ) * ∑ j ∈ J', y j ∧
      J.card ≤ (D + 1) * J'.card := by
  classical
  let q : Finset ι → Prop := fun S =>
    (∀ i ∈ S, (S.filter (fun j => r j i)).card ≤ D) →
      ∃ J' ⊆ S, (J' : Set ι).Pairwise (fun i j => ¬ r i j) ∧
        ∑ j ∈ S, y j ≤ (D + 1 : ℕ) * ∑ j ∈ J', y j ∧
        S.card ≤ (D + 1) * J'.card
  let step : ∀ s : Finset ι, (∀ t ⊂ s, q t) → q s := by
    intro S ih hdegS
    by_cases hS : S = ∅
    · subst S
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
    · have hnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
      rcases Finset.exists_max_image S y hnonempty with ⟨i, hiS, himax⟩
      let T : Finset ι := S.filter (fun j => r j i)
      let N : Finset ι := insert i T
      have hTcard : T.card ≤ D := by simpa [T] using hdegS i hiS
      have hNcard : N.card ≤ D + 1 := by
        calc
          N.card = (insert i T).card := rfl
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
          _ ≤ (D + 1 : ℕ) • y i := nsmul_le_nsmul_left zero_le hNcard
          _ = (D + 1 : ℕ) * y i := by rw [nsmul_eq_mul]
      have hNS : N ⊆ S := by
        intro x hx
        simp only [N, T, Finset.mem_insert, Finset.mem_filter] at hx
        rcases hx with rfl | ⟨hxS, _⟩
        · exact hiS
        · exact hxS
      have hsubN : S \ N ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro hEq
        have hmem : i ∈ S \ N := by rw [hEq]; exact hiS
        exact (Finset.mem_sdiff.mp hmem).2 (by simp [N])
      have hdegSub : ∀ i ∈ S \ N, ((S \ N).filter (fun j => r j i)).card ≤ D := by
        intro i' hiSub
        have hi'S : i' ∈ S := (Finset.mem_sdiff.mp hiSub).1
        have hsubf : (S \ N).filter (fun j => r j i') ⊆ S.filter (fun j => r j i') := by
          intro j hj
          have hjf := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hjf.1).1, hjf.2⟩
        exact le_trans (Finset.card_le_card hsubf) (hdegS i' hi'S)
      rcases ih (S \ N) hsubN hdegSub with ⟨A, hAsub, hApair, hAsum, hAcard⟩
      have hiNotA : i ∉ A := by
        intro hmem
        have hmem' : i ∈ S \ N := hAsub hmem
        exact (Finset.mem_sdiff.mp hmem').2 (by simp [N])
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
          · subst a; subst b; exact hirr i
          · subst a; exact fun hrib => hnotI b (hAsub hbA) (hsymm i b hrib)
        · rcases hb' with hb_eq | hbA
          · subst b; exact hnotI a (hAsub haA)
          · exact hApair haA hbA hab
      have hsumAns : ∑ j ∈ ans, y j = y i + ∑ j ∈ A, y j := by
        unfold ans; rw [Finset.sum_insert hiNotA]
      have hcardAns : ans.card = A.card + 1 := by
        unfold ans; rw [Finset.card_insert_of_notMem hiNotA]
      have hsplit : ∑ j ∈ S, y j = ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j := by
        calc
          ∑ j ∈ S, y j = (∑ j ∈ S \ N, y j) + ∑ j ∈ N, y j :=
            (Finset.sum_sdiff (s₁ := N) (s₂ := S) (f := fun j => y j) hNS).symm
          _ = ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j := by rw [add_comm]
      have hcardsplit : S.card = N.card + (S \ N).card := by
        rw [add_comm]
        exact (Finset.card_sdiff_add_card_eq_card hNS).symm
      have hfinal : ∑ j ∈ S, y j ≤ (D + 1 : ℕ) * ∑ j ∈ ans, y j := by
        rw [hsplit]
        calc
          ∑ j ∈ N, y j + ∑ j ∈ S \ N, y j ≤ (D + 1 : ℕ) * y i + (D + 1 : ℕ) * ∑ j ∈ A, y j :=
            add_le_add hNsum hAsum
          _ = (D + 1 : ℕ) * (y i + ∑ j ∈ A, y j) := by rw [mul_add]
          _ = (D + 1 : ℕ) * ∑ j ∈ ans, y j := by rw [hsumAns]
      have hfinalcard : S.card ≤ (D + 1) * ans.card := by
        rw [hcardsplit, hcardAns]
        calc
          N.card + (S \ N).card ≤ (D + 1) + (D + 1) * A.card :=
            Nat.add_le_add hNcard hAcard
          _ = (D + 1) * (A.card + 1) := by ring
      exact ⟨ans, hansSub, hpair, hfinal, hfinalcard⟩
  let hJ : ∀ i ∈ J, (J.filter (fun j => r j i)).card ≤ D := by
    intro i hiJ
    have hTset : (J.filter (fun j => r j i) : Set ι) = {j ∈ (J : Set ι) | r j i} := by
      ext j; simp
    have hcard : (J.filter (fun j => r j i)).card =
        (J.filter (fun j => r j i) : Set ι).ncard := by
      rw [Set.ncard_coe_finset]
    rw [hcard, hTset]
    exact hdeg i hiJ
  exact (Finset.strongInductionOn (p := q) J step) hJ

end Kakeya

end
