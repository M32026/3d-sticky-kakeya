module

/-
  Separated subset lemma (OS Lemmas 3-4, Section 5).

  Given a finite set with a symmetric "compatibility" relation (non-separation),
  if every element is compatible with at most K elements (including itself),
  then there exists a separated subset of size ≥ |S| / K.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open Finset

namespace DiscretisedFurstenbergEstimate.InductionOnScales.Separated

variable {α : Type*} [DecidableEq α]

/-- Given a finite set `U` and a symmetric, reflexive "compatible" relation `R`
    (where `R x y` means x and y are NOT separated), if every element
    is compatible with at most `K` elements of `U` (including itself),
    then there exists a separated subset `S' ⊆ U` of size ≥ |U| / K. -/
lemma exists_separated_subset
    (U : Finset α)
    (R : α → α → Prop)
    [hRdec : ∀ x, DecidablePred (R x)]
    (hR_sym : ∀ x ∈ U, ∀ y ∈ U, R x y → R y x)
    (hR_refl : ∀ x ∈ U, R x x)
    (K : ℕ) (hK_pos : 0 < K)
    (h_bound : ∀ x ∈ U, (U.filter (R x)).card ≤ K) :
    ∃ (S' : Finset α), S' ⊆ U ∧
      (∀ x ∈ S', ∀ y ∈ S', x ≠ y → ¬ R x y) ∧
      (S'.card : ℝ) ≥ (U.card : ℝ) / (K : ℝ) := by
  have h_main : ∀ (n : ℕ), n ≤ U.card →
      ∀ (V : Finset α), V ⊆ U → V.card = n →
        (∀ x ∈ V, (V.filter (R x)).card ≤ K) →
        (∀ x ∈ V, ∀ y ∈ V, R x y → R y x) →
      ∃ (S' : Finset α), S' ⊆ V ∧
        (∀ x ∈ S', ∀ y ∈ S', x ≠ y → ¬ R x y) ∧
        (S'.card : ℝ) ≥ (V.card : ℝ) / (K : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn V hV_sub hV_card hV_bound hV_sym
      by_cases hV_empty : V = ∅
      · subst hV_empty
        exact ⟨∅, by simp, by simp, by simp⟩
      · -- V nonempty
        have hV_nonempty : V.Nonempty := by
          simpa [Finset.nonempty_iff_ne_empty] using hV_empty
        rcases hV_nonempty with ⟨x, hx⟩
        let compat : Finset α := V.filter (R x)
        have hx_compat : x ∈ compat := by
          exact Finset.mem_filter.mpr ⟨hx, hR_refl x (hV_sub hx)⟩
        have hcompat_sub : compat ⊆ V := Finset.filter_subset _ _
        have hcompat_card : compat.card ≤ K := hV_bound x hx
        let remaining : Finset α := V \ compat
        have h_rem_sub : remaining ⊆ V := by
          intro z hz; exact (Finset.mem_sdiff.mp hz).1
        have h_rem_to_U : remaining ⊆ U := h_rem_sub.trans hV_sub
        have h_disj : Disjoint compat remaining := by
          simp [Finset.disjoint_left, remaining] <;> tauto
        have h_eq_card : remaining.card + compat.card = V.card := by
          have h : (compat ∪ remaining).card = compat.card + remaining.card :=
            Finset.card_union_of_disjoint h_disj
          have h2 : compat ∪ remaining = V := by
            rw [Finset.union_comm]
            exact Finset.sdiff_union_of_subset hcompat_sub
          rw [h2] at h
          have h3 : compat.card + remaining.card = V.card := h.symm
          omega
        have h_rem_card_lt : remaining.card < n := by
          rw [hV_card] at h_eq_card
          have h_pos : 0 < compat.card := Finset.card_pos.mpr ⟨x, hx_compat⟩
          omega
        have h_rem_bound : ∀ y ∈ remaining, (remaining.filter (R y)).card ≤ K := by
          intro y hy
          have h_y_V : y ∈ V := h_rem_sub hy
          have h1 : remaining.filter (R y) ⊆ V.filter (R y) := by
            intro z hz
            have hz1 : z ∈ remaining := (Finset.mem_filter.mp hz).1
            have hz2 : R y z := (Finset.mem_filter.mp hz).2
            exact Finset.mem_filter.mpr ⟨h_rem_sub hz1, hz2⟩
          have h2 : (remaining.filter (R y)).card ≤ (V.filter (R y)).card :=
            Finset.card_le_card h1
          exact le_trans h2 (hV_bound y h_y_V)
        have h_rem_sym : ∀ x ∈ remaining, ∀ y ∈ remaining, R x y → R y x := by
          intro a ha b hb h
          exact hV_sym a (h_rem_sub ha) b (h_rem_sub hb) h
        have ih_rem := ih remaining.card h_rem_card_lt (by omega) remaining h_rem_to_U rfl h_rem_bound h_rem_sym
        rcases ih_rem with ⟨S_rem, hSrem_sub, hSrem_sep, hSrem_size⟩
        let S' : Finset α := insert x S_rem
        have h_x_not_rem : x ∉ remaining := by
          simp [remaining, hx_compat]
        have h_x_not_Srem : x ∉ S_rem := by
          intro h; exact h_x_not_rem (hSrem_sub h)
        have hS'_sub : S' ⊆ V := by
          intro z hz
          simp only [S', Finset.mem_insert] at hz
          rcases hz with (rfl | hz)
          · exact hx
          · exact h_rem_sub (hSrem_sub hz)
        have h_no_R_x_rem : ∀ w ∈ S_rem, ¬ R x w := by
          intro w hw
          have h_w_rem : w ∈ remaining := hSrem_sub hw
          have h_w_not_compat : w ∉ compat := (Finset.mem_sdiff.mp h_w_rem).2
          have h9 : w ∉ V.filter (R x) := h_w_not_compat
          have h10 : ¬ R x w := by
            by_contra h11
            exact h9 (Finset.mem_filter.mpr ⟨h_rem_sub h_w_rem, h11⟩)
          exact h10
        have hS'_sep : ∀ z ∈ S', ∀ w ∈ S', z ≠ w → ¬ R z w := by
          intro z hz w hw hne
          have hz_main : z = x ∨ z ∈ S_rem := by
            simp only [S', Finset.mem_insert] at hz; tauto
          have hw_main : w = x ∨ w ∈ S_rem := by
            simp only [S', Finset.mem_insert] at hw; tauto
          -- Case 1: z = x
          by_cases hzx : z = x
          · -- z = x, so w ≠ x (since z ≠ w)
            have hwx : w ≠ x := by
              intro h; apply hne; rw [hzx, h]
            have hw_rem : w ∈ S_rem := by
              simp only [S', Finset.mem_insert] at hw; tauto
            rw [hzx]
            exact h_no_R_x_rem w hw_rem
          · -- z ≠ x, so z ∈ S_rem
            have hz_rem : z ∈ S_rem := by tauto
            by_cases hwx : w = x
            · -- w = x
              have h1 : ¬ R x z := h_no_R_x_rem z hz_rem
              have h2 : z ∈ V := h_rem_sub (hSrem_sub hz_rem)
              have h3 : ¬ R z x := by
                intro h4
                have h5 : R x z := hV_sym z h2 x hx h4
                exact h1 h5
              rw [hwx]
              exact h3
            · -- w ≠ x, so w ∈ S_rem
              have hw_rem : w ∈ S_rem := by tauto
              exact hSrem_sep z hz_rem w hw_rem hne
        have hS'_card : (S'.card : ℝ) = (S_rem.card : ℝ) + 1 := by
          have h : S'.card = S_rem.card + 1 := by
            simp [S', h_x_not_Srem] <;> omega
          exact_mod_cast h
        have h_rem_card_eq : (remaining.card : ℝ) = (V.card : ℝ) - (compat.card : ℝ) := by
          have h_eq : (remaining.card : ℝ) + (compat.card : ℝ) = (V.card : ℝ) := by
            exact_mod_cast h_eq_card
          linarith
        have h_main_ineq : (S'.card : ℝ) ≥ (V.card : ℝ) / (K : ℝ) := by
          rw [hS'_card]
          have h2 : (S_rem.card : ℝ) ≥ (remaining.card : ℝ) / (K : ℝ) := hSrem_size
          rw [h_rem_card_eq] at h2
          have h3 : (compat.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcompat_card
          have h4 : 0 < (K : ℝ) := by exact_mod_cast hK_pos
          have h5 : (S_rem.card : ℝ) + 1 ≥ (V.card : ℝ) / (K : ℝ) := by
            calc (S_rem.card : ℝ) + 1
              ≥ ((V.card : ℝ) - (compat.card : ℝ)) / (K : ℝ) + 1 := by linarith
            _ = ((V.card : ℝ) - (compat.card : ℝ) + (K : ℝ)) / (K : ℝ) := by
                field_simp [h4.ne'] <;> ring
            _ ≥ (V.card : ℝ) / (K : ℝ) := by
                apply div_le_div_of_nonneg_right
                · linarith
                · positivity
          exact h5
        exact ⟨S', hS'_sub, hS'_sep, h_main_ineq⟩
  have hU_sym : ∀ x ∈ U, ∀ y ∈ U, R x y → R y x := hR_sym
  exact h_main U.card (by linarith) U (by rfl) rfl h_bound hU_sym

end DiscretisedFurstenbergEstimate.InductionOnScales.Separated
