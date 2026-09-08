/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Submodule
-/

@[expose] public section

/-- not sure if this is already in Mathlib.
Any submodule of finrank `≤ k` in a finite-dimensional space, with `k ≤ finrank V`,
can be extended to a submodule of finrank exactly `k`. -/
theorem FiniteDimensional.exists_le_finrank_eq_of_le_finrank {𝕜 V} [DivisionRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    {N : Submodule 𝕜 V}
    {k : ℕ} (h1 : Module.finrank 𝕜 N ≤ k) (h2 : k ≤ Module.finrank 𝕜 V) :
    ∃ W : Submodule 𝕜 V, N ≤ W ∧ Module.finrank 𝕜 W = k := by
  induction k generalizing N with
  | zero =>
    have hNbot : N = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp h1)
    exact ⟨⊥, hNbot.le, by simp⟩
  | succ k ih =>
    rcases Nat.lt_or_ge (Module.finrank 𝕜 N) (k + 1) with hlt | hge
    · obtain ⟨W', hNW', hW'⟩ := ih (Nat.lt_succ_iff.mp hlt) (Nat.le_of_succ_le h2)
      have hW'_lt : Module.finrank 𝕜 W' < Module.finrank 𝕜 V := by rw [hW']; exact h2
      obtain ⟨v, hv⟩ := W'.exists_of_finrank_lt hW'_lt
      refine ⟨W' ⊔ Submodule.span 𝕜 {v}, hNW'.trans le_sup_left, ?_⟩
      have hdisj : Disjoint W' (Submodule.span 𝕜 {v}) := by
        rw [Submodule.disjoint_def]
        intro x hxW' hxsp
        rw [Submodule.mem_span_singleton] at hxsp
        obtain ⟨a, rfl⟩ := hxsp
        by_contra hne
        have ha : a ≠ 0 := fun h => by subst h; simp at hne
        exact hv a ha hxW'
      have hfr_span : Module.finrank 𝕜 (Submodule.span 𝕜 ({v} : Set V)) = 1 := by
        rw [finrank_span_singleton]
        intro h; subst h
        exact hv 1 one_ne_zero (by simp)
      have hkey := Submodule.finrank_sup_add_finrank_inf_eq W' (Submodule.span 𝕜 ({v} : Set V))
      rw [hdisj.eq_bot, finrank_bot, hW', hfr_span] at hkey
      omega
    · exact ⟨N, le_refl _, le_antisymm h1 hge⟩
