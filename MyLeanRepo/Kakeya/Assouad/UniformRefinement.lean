import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Lower-uniformity refinement lemma

Given a finite set `A` and `T` levels of nested partitions, produce a subset
`A' ⊆ A` such that at every level, every non-empty cell contains at least
`|A'| / (C · #cells)` points. Retention: `((C-1)/C)^T · |A|`.
-/

open Finset

namespace Kakeya.Assouad

lemma lower_uniformity_refinement
  {α : Type*} [DecidableEq α]
  (C : ℕ) (hC : 2 ≤ C)
  (T : ℕ)
  (A : Finset α)
  (P : ℕ → Finset (Finset α))
  (h_partition : ∀ k < T,
    (∀ c ∈ P k, c ⊆ A) ∧
    (∀ c₁ ∈ P k, ∀ c₂ ∈ P k, c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
    (A ⊆ Finset.biUnion (P k) id))
  (h_refine : ∀ k < T, ∀ c ∈ P (k + 1), ∃ p ∈ P k, c ⊆ p) :
  ∃ (A' : Finset α), A' ⊆ A ∧
    (∀ k < T, ∀ c ∈ P k,
      (A' ∩ c).Nonempty →
        (C : ℝ) * (A' ∩ c).card ≥ (A'.card : ℝ) / (P k).card) ∧
    (A'.card : ℝ) ≥ ((C - 1 : ℝ) / C)^T * (A.card : ℝ) := by
  have main : ∀ (n : ℕ) (X : Finset α) (Q : ℕ → Finset (Finset α))
    (hpart : ∀ k < n,
      (∀ c ∈ Q k, c ⊆ X) ∧
      (∀ c₁ ∈ Q k, ∀ c₂ ∈ Q k, c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
      (X ⊆ Finset.biUnion (Q k) id))
    (href : ∀ k < n, ∀ c ∈ Q (k + 1), ∃ p ∈ Q k, c ⊆ p),
    ∃ (X' : Finset α), X' ⊆ X ∧
      (∀ k < n, ∀ c ∈ Q k,
        (X' ∩ c).Nonempty →
          (C : ℝ) * (X' ∩ c).card ≥ (X'.card : ℝ) / (Q k).card) ∧
      (X'.card : ℝ) ≥ ((C - 1 : ℝ) / C)^n * (X.card : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro X Q _ _
      refine ⟨X, rfl.subset, ?_, ?_⟩
      · intro k hk; exfalso; linarith
      · norm_num
    | succ n ih =>
      intro X Q hpart href
      by_cases hX : X = ∅
      · subst hX
        refine ⟨∅, by simp, ?_, ?_⟩
        · intro k _ c _ h; simp at h
        · simp
      · have hX_ne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX
        let Q' : ℕ → Finset (Finset α) := fun k => Q (k + 1)
        have hQ'part : ∀ k < n,
            (∀ c ∈ Q' k, c ⊆ X) ∧
            (∀ c₁ ∈ Q' k, ∀ c₂ ∈ Q' k, c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
            (X ⊆ Finset.biUnion (Q' k) id) := by
          intro k hk; exact hpart (k + 1) (by linarith)
        have hQ'ref : ∀ k < n, ∀ c ∈ Q' (k + 1), ∃ p ∈ Q' k, c ⊆ p := by
          intro k hk c hc; exact href (k + 1) (by linarith) c hc
        rcases ih X Q' hQ'part hQ'ref with ⟨X'', hX''sub, hX''unif, hX''ret⟩

        let N0 := (Q 0).card
        have hQ0_nonempty : (Q 0).Nonempty := by
          have hcov := (hpart 0 (by norm_num)).2.2
          by_contra h
          have h2 : Q 0 = ∅ := by simpa using h
          rw [h2] at hcov
          have h3 : X = ∅ := by simpa using hcov
          exact hX h3
        have hN0_pos : 0 < N0 := hQ0_nonempty.card_pos
        let avg : ℝ := (X''.card : ℝ) / N0
        let light : Finset (Finset α) :=
          (Q 0).filter fun c => (C : ℝ) * (X'' ∩ c).card < avg
        let removed : Finset α := Finset.biUnion light id
        let X' : Finset α := X'' \ removed

        have h_disj0 := (hpart 0 (by norm_num)).2.1

        have h_light_disj : ∀ c₁ ∈ light, ∀ c₂ ∈ light, c₁ ≠ c₂ → Disjoint c₁ c₂ := by
          intro c₁ hc₁ c₂ hc₂ hne
          exact h_disj0 c₁ (mem_filter.mp hc₁).1 c₂ (mem_filter.mp hc₂).1 hne

        have h_inter_card : (X'' ∩ removed).card = ∑ c ∈ light, (X'' ∩ c).card := by
          have h1 : X'' ∩ removed = Finset.biUnion light (fun c => X'' ∩ c) := by
            ext x; simp only [removed, mem_inter, mem_biUnion]
            constructor
            · rintro ⟨hx'', ⟨c, hc, hxc⟩⟩; exact ⟨c, hc, ⟨hx'', hxc⟩⟩
            · rintro ⟨c, hc, ⟨hx'', hxc⟩⟩; exact ⟨hx'', ⟨c, hc, hxc⟩⟩
          rw [h1]
          have h_disj : (light : Set (Finset α)).PairwiseDisjoint (fun c => X'' ∩ c) := by
            intro c₁ hc₁ c₂ hc₂ hne
            have h_base : Disjoint c₁ c₂ := h_light_disj c₁ hc₁ c₂ hc₂ hne
            have h1 : (X'' ∩ c₁) ⊆ c₁ := by
              intro x hx; exact (mem_inter.mp hx).2
            have h2 : (X'' ∩ c₂) ⊆ c₂ := by
              intro x hx; exact (mem_inter.mp hx).2
            exact h_base.mono h1 h2
          rw [Finset.card_biUnion h_disj]

        have h_removed_lt : (X'' ∩ removed).card < (X''.card : ℝ) / C := by
          rw [h_inter_card]
          have h2 : ∀ c ∈ light, (C : ℝ) * (X'' ∩ c).card < avg :=
            fun c hc => (mem_filter.mp hc).2
          have hCpos' : 0 < C := by omega
          have hX''pos : 0 < (X''.card : ℝ) := by
            have hpos1 : 0 < ((C - 1 : ℝ) / C)^n * (X.card : ℝ) := by
              have hCfrac : 0 < ((C : ℝ) - 1) / C := by
                have h1 : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos'
                have h2 : (1 : ℝ) < (C : ℝ) := by exact_mod_cast (show 1 < C from by omega)
                have h3 : (0 : ℝ) < (C : ℝ) - 1 := sub_pos.mpr h2
                positivity
              have hXpos : 0 < (X.card : ℝ) := Nat.cast_pos.mpr hX_ne.card_pos
              positivity
            linarith [hX''ret]
          by_cases hlight : light = ∅
          · rw [hlight]
            simp [hX''pos]
            <;> positivity
          · have hlight_ne : light.Nonempty := Finset.nonempty_iff_ne_empty.mpr hlight
            have h3 : ∑ c ∈ light, (C : ℝ) * (X'' ∩ c).card < ∑ c ∈ light, avg :=
              Finset.sum_lt_sum_of_nonempty hlight_ne (fun c hc => h2 c hc)
            have h4 : ∑ c ∈ light, avg = (light.card : ℝ) * avg := by
              have h5 : ∑ c ∈ light, (1 : ℝ) = (light.card : ℝ) := by simp
              have h61 : ∑ c ∈ light, avg = ∑ c ∈ light, avg * (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro _ _ <;> ring
              have h6 : ∑ c ∈ light, avg = avg * ∑ c ∈ light, (1 : ℝ) := by
                rw [h61, Finset.mul_sum]
              rw [h6, h5] <;> ring
            have h3' : ∑ c ∈ light, (C : ℝ) * (X'' ∩ c).card < (light.card : ℝ) * avg := by
              rw [h4] at h3
              exact h3
            have h4 : (C : ℝ) * (∑ c ∈ light, (X'' ∩ c).card : ℝ) < (light.card : ℝ) * avg := by
              have h_eq : (C : ℝ) * (∑ c ∈ light, (X'' ∩ c).card : ℝ) = ∑ c ∈ light, (C : ℝ) * (X'' ∩ c).card := by
                rw [Finset.mul_sum]
              rw [h_eq]
              exact h3'
            have h5 : (light.card : ℝ) ≤ (N0 : ℝ) := Nat.cast_le.mpr (card_le_card (filter_subset _ _))
            have h6 : (C : ℝ) * (∑ c ∈ light, (X'' ∩ c).card : ℝ) < (N0 : ℝ) * avg := by
              calc _ < (light.card : ℝ) * avg := h4
                   _ ≤ (N0 : ℝ) * avg := by gcongr
            have hN0_ne : (N0 : ℝ) ≠ 0 := by exact_mod_cast hN0_pos.ne'
            have h7 : (N0 : ℝ) * avg = (X''.card : ℝ) := by
              dsimp only [avg]
              field_simp [hN0_ne]
            rw [h7] at h6
            have h8 : (C : ℝ) * (∑ c ∈ light, (X'' ∩ c).card : ℝ) < (X''.card : ℝ) := h6
            have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos'
            have hCne : (C : ℝ) ≠ 0 := hCpos.ne'
            have h9 : (∑ c ∈ light, (X'' ∩ c).card : ℝ) < (X''.card : ℝ) / C := by
              let S : ℝ := (∑ c ∈ light, (X'' ∩ c).card : ℝ)
              have h_mul_div : (C : ℝ) * S / C = S := by
                have h1 : (C : ℝ) * S / C = (C : ℝ) / C * S := by ring
                rw [h1]
                have h2 : (C : ℝ) / C = 1 := div_self hCne
                rw [h2] <;> ring
              have h10 : (C : ℝ) * S / C < (X''.card : ℝ) / C :=
                div_lt_div_of_pos_right h8 hCpos
              rw [h_mul_div] at h10
              exact h10
            have h9' : (↑(∑ c ∈ light, (X'' ∩ c).card) : ℝ) < (X''.card : ℝ) / C := by
              simpa [Nat.cast_sum] using h9
            exact h9'

        have hX'_card : (X'.card : ℝ) = (X''.card : ℝ) - ((X'' ∩ removed).card : ℝ) := by
          have h_le : (X'' ∩ removed).card ≤ X''.card := by
            apply Finset.card_le_card
            intro x hx; exact (mem_inter.mp hx).1
          have h' : X'.card = X''.card - (X'' ∩ removed).card := by
            rw [show X' = X'' \ removed from rfl]
            have h_card : (X'' \ removed).card = X''.card - (removed ∩ X'').card := Finset.card_sdiff
            rw [h_card]
            have h_comm : removed ∩ X'' = X'' ∩ removed := by
              ext y; simp [and_comm]
            rw [h_comm]
          rw [h']
          rw [Nat.cast_sub h_le]

        have h_ret : (X'.card : ℝ) ≥ ((C - 1 : ℝ) / C) * (X''.card : ℝ) := by
          rw [hX'_card]
          have h10 : (X''.card : ℝ) - ((X'' ∩ removed).card : ℝ) ≥
              (X''.card : ℝ) - (X''.card : ℝ) / C := by
            exact sub_le_sub_left h_removed_lt.le (X''.card : ℝ)
          have hCne2 : (C : ℝ) ≠ 0 := by positivity
          have h_cast : ((C - 1 : ℝ) / C) = ((C : ℝ) - 1) / C := by
            norm_cast
          have h11 : (X''.card : ℝ) - (X''.card : ℝ) / C =
              ((C - 1 : ℝ) / C) * (X''.card : ℝ) := by
            rw [h_cast]
            field_simp [hCne2]
          rw [h11] at h10; exact h10

        have h_keeps : ∀ (c : Finset α), c ∈ Q 0 → c ∉ light → X' ∩ c = X'' ∩ c := by
          intro c hc hnl
          ext x; simp only [X', mem_inter, mem_sdiff]
          constructor
          · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            have hnr : x ∉ removed := by
              intro hr; rcases mem_biUnion.mp hr with ⟨d, hd, hxd⟩
              have hdisj : Disjoint c d := h_disj0 c hc d (mem_filter.mp hd).1 (by
                intro eq
                have h_cont : c ∈ light := by rw [eq]; exact hd
                exact hnl h_cont)
              have h_singleton : ({x} : Finset α) ≤ c := by simp [h2]
              have hxd' : x ∈ d := by simpa using hxd
              have h_singleton2 : ({x} : Finset α) ≤ d := by simp [hxd']
              have h_bot : ({x} : Finset α) ≤ (∅ : Finset α) := hdisj h_singleton h_singleton2
              simp at h_bot
            exact ⟨⟨h1, hnr⟩, h2⟩

        have h_unif_0 : ∀ c ∈ Q 0, (X' ∩ c).Nonempty →
            (C : ℝ) * (X' ∩ c).card ≥ (X'.card : ℝ) / N0 := by
          intro c hc hne
          have hnl : c ∉ light := by
            by_contra h
            have hsub : c ⊆ removed := by
              intro y hy
              exact Finset.mem_biUnion.mpr ⟨c, h, hy⟩
            rcases hne with ⟨x, hx⟩
            have h1 : x ∈ X' := (mem_inter.mp hx).1
            have h2 : x ∈ c := (mem_inter.mp hx).2
            have h3 : x ∈ removed := hsub h2
            have h4 : x ∉ removed := (mem_sdiff.mp h1).2
            exact h4 h3
          have h_heavy : (C : ℝ) * (X'' ∩ c).card ≥ avg := by
            have h_not_light : ¬((C : ℝ) * (X'' ∩ c).card < avg) := by
              by_contra h6
              exact hnl (mem_filter.mpr ⟨hc, h6⟩)
            linarith
          have h_eq : X' ∩ c = X'' ∩ c := h_keeps c hc hnl
          rw [h_eq] at *
          have h13 : (X'.card : ℝ) ≤ (X''.card : ℝ) := by
            have h : X' ⊆ X'' := by
              intro y hy
              exact (mem_sdiff.mp hy).1
            exact Nat.cast_le.mpr (card_le_card h)
          calc (C : ℝ) * (X'' ∩ c).card ≥ avg := h_heavy
            _ = (X''.card : ℝ) / N0 := by rfl
            _ ≥ (X'.card : ℝ) / N0 := by gcongr

        have h_ancestor : ∀ (j : ℕ), j ≤ n + 1 → ∀ (c : Finset α), c ∈ Q j → ∃ (p0 : Finset α), p0 ∈ Q 0 ∧ c ⊆ p0 := by
          intro j
          induction j with
          | zero =>
            intro hj c hc
            exact ⟨c, hc, rfl.subset⟩
          | succ j ih =>
            intro hj c hc
            rcases href j (by linarith) c hc with ⟨p, hp, hsub⟩
            rcases ih (by linarith) p hp with ⟨p0, hp0, hsub0⟩
            exact ⟨p0, hp0, hsub.trans hsub0⟩

        have h_unif_k : ∀ k < n, ∀ c ∈ Q (k + 1), (X' ∩ c).Nonempty →
            (C : ℝ) * (X' ∩ c).card ≥ (X'.card : ℝ) / (Q (k + 1)).card := by
          intro k hk c hc hne
          rcases h_ancestor (k + 1) (by linarith) c hc with ⟨p0, hp0, hsub0⟩
          have hpnl : p0 ∉ light := by
            by_contra hpl
            have hsub2 : c ⊆ removed := by
              intro y hy
              exact Finset.mem_biUnion.mpr ⟨p0, hpl, hsub0 hy⟩
            rcases hne with ⟨x, hx⟩
            have h1 : x ∈ X' := (mem_inter.mp hx).1
            have h2 : x ∈ removed := hsub2 (mem_inter.mp hx).2
            have h3 : x ∉ removed := (mem_sdiff.mp h1).2
            exact h3 h2
          have h_eq : X' ∩ c = X'' ∩ c := by
            ext x; simp only [X', mem_inter, mem_sdiff]
            constructor
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              have hnr : x ∉ removed := by
                intro hr; rcases mem_biUnion.mp hr with ⟨d, hd, hxd⟩
                have hdisj : Disjoint p0 d := h_disj0 p0 hp0 d (mem_filter.mp hd).1 (by
                  intro eq
                  have h_cont : p0 ∈ light := by rw [eq]; exact hd
                  exact hpnl h_cont)
                have hxp0 : x ∈ p0 := hsub0 h2
                have h_singleton : ({x} : Finset α) ≤ p0 := by simp [hxp0]
                have hxd' : x ∈ d := by simpa using hxd
                have h_singleton2 : ({x} : Finset α) ≤ d := by simp [hxd']
                have h_bot : ({x} : Finset α) ≤ (∅ : Finset α) := hdisj h_singleton h_singleton2
                simp at h_bot
              exact ⟨⟨h1, hnr⟩, h2⟩
          have h_ih := hX''unif k hk c hc
          rcases hne with ⟨x, hx⟩
          have h_x_in : x ∈ X'' ∩ c := by
            rw [←h_eq]
            exact hx
          have hne2 : (X'' ∩ c).Nonempty := ⟨x, h_x_in⟩
          have h14 : (C : ℝ) * (X'' ∩ c).card ≥ (X''.card : ℝ) / (Q (k + 1)).card := h_ih hne2
          have h15 : (X'.card : ℝ) ≤ (X''.card : ℝ) := by
            have h : X' ⊆ X'' := by
              intro y hy
              exact (mem_sdiff.mp hy).1
            exact Nat.cast_le.mpr (card_le_card h)
          calc (C : ℝ) * (X' ∩ c).card = (C : ℝ) * (X'' ∩ c).card := by rw [h_eq]
            _ ≥ (X''.card : ℝ) / (Q (k + 1)).card := h14
            _ ≥ (X'.card : ℝ) / (Q (k + 1)).card := by gcongr

        have hX'sub : X' ⊆ X'' := by
          intro y hy
          exact (mem_sdiff.mp hy).1
        refine ⟨X', hX'sub.trans hX''sub, ?_, ?_⟩
        · intro k hk
          by_cases h : k = 0
          · rw [h]; exact h_unif_0
          · have h' : ∃ j : ℕ, k = j + 1 := by refine ⟨k - 1, ?_⟩; omega
            rcases h' with ⟨j, rfl⟩
            have hj : j < n := by omega
            exact h_unif_k j hj
        · calc
            (X'.card : ℝ) ≥ ((C - 1 : ℝ) / C) * (X''.card : ℝ) := h_ret
            _ ≥ ((C - 1 : ℝ) / C) * (((C - 1 : ℝ) / C)^n * (X.card : ℝ)) := by
              have h_nonneg : 0 ≤ ((C - 1 : ℝ) / C) := by
                have h1 : 0 ≤ (C - 1 : ℝ) := by
                  have h2 : 1 ≤ C := by omega
                  exact_mod_cast (show 0 ≤ C - 1 from by omega)
                have h3 : 0 < (C : ℝ) := by exact_mod_cast (show 0 < C from by omega)
                exact div_nonneg h1 (by linarith)
              exact mul_le_mul_of_nonneg_left hX''ret h_nonneg
            _ = ((C - 1 : ℝ) / C)^(n + 1) * (X.card : ℝ) := by ring
  exact main T A P h_partition h_refine

end Kakeya.Assouad
