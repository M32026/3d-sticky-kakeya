import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-!
# Greedy weighted independent set

A finite symmetric conflict relation of maximum degree `D` admits an
independent subset carrying at least a `1 / (D + 1)` fraction of any
`ENNReal` weight.  This is the generic finite-graph input beneath the
specialized weighted essentially-distinct tube selections.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

variable {α : Type*} [DecidableEq α]

/-- Greedy weighted independent-set selection on a finite symmetric graph. -/
lemma greedy_weighted_independent_set
    (S : Finset α) (w : α → ENNReal)
    (R : α → α → Prop) [DecidableRel R]
    (hR_symm : ∀ x y, R x y → R y x)
    (D : ℕ)
    (hD : ∀ x ∈ S, (S.filter (R x)).card ≤ D) :
    ∃ I : Finset α, I ⊆ S ∧
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ R x y) ∧
      (D + 1 : ENNReal) * ∑ x ∈ I, w x ≥ ∑ x ∈ S, w x := by
  classical
  have H_main : ∀ X : Finset α, X ⊆ S →
      ∃ I : Finset α, I ⊆ X ∧
        (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ R x y) ∧
        (D + 1 : ENNReal) * ∑ x ∈ I, w x ≥ ∑ x ∈ X, w x := by
    intro X
    induction X using Finset.strongInduction with
    | H X ih =>
      intro hX_sub_S
      by_cases hX : X = ∅
      · subst hX
        refine ⟨∅, by simp, by simp, by simp⟩
      · have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hX
        rcases Finset.exists_max_image X w hXne with ⟨x, hx, hmax⟩
        let N := insert x (X.filter (R x))
        have hN_sub_X : N ⊆ X := by
          exact Finset.insert_subset_iff.mpr
            ⟨hx, Finset.filter_subset _ _⟩
        have h_filter_S :
            X.filter (R x) ⊆ S.filter (R x) := by
          apply Finset.filter_subset_filter
          exact hX_sub_S
        have h1_card : (X.filter (R x)).card ≤ D :=
          (Finset.card_le_card h_filter_S).trans (hD x (hX_sub_S hx))
        have hN_card : N.card ≤ D + 1 := by
          have h4 : N.card ≤ (X.filter (R x)).card + 1 := by
            simp [N, Finset.card_insert_le]
          linarith
        have h_max_in_N : ∀ y ∈ N, w y ≤ w x := by
          intro y hy
          exact hmax y (hN_sub_X hy)
        have h_weight_N :
            (∑ y ∈ N, w y) ≤ (D + 1 : ENNReal) * w x := by
          have h_sum :
              (∑ y ∈ N, w y) ≤ ∑ y ∈ N, w x :=
            Finset.sum_le_sum h_max_in_N
          have h_eq :
              ∑ y ∈ N, w x = (N.card : ENNReal) * w x := by
            simp [Finset.sum_const]
          have h_le : (N.card : ENNReal) ≤ (D + 1 : ENNReal) := by
            exact_mod_cast hN_card
          calc
            (∑ y ∈ N, w y) ≤ (N.card : ENNReal) * w x := by
              rwa [h_eq] at h_sum
            _ ≤ (D + 1 : ENNReal) * w x := by gcongr
        let X' := X \ N
        have hX'_sub_X : X' ⊆ X := sdiff_subset
        have h_x_not_in_X' : x ∉ X' := by
          simp only [X', Finset.mem_sdiff, N, Finset.mem_insert]
          tauto
        have hX'_not_supset : ¬ X ⊆ X' := by
          intro h
          exact h_x_not_in_X' (h hx)
        have hX'_lt : X' ⊂ X := ⟨hX'_sub_X, hX'_not_supset⟩
        have hX'_sub_S : X' ⊆ S := hX'_sub_X.trans hX_sub_S
        rcases ih X' hX'_lt hX'_sub_S with
          ⟨I', hI'_sub, hI'_indep, hI'_mass⟩
        let I := insert x I'
        have h_x_not_in_I' : x ∉ I' := by
          exact fun h2 => h_x_not_in_X' (hI'_sub h2)
        have hI'_sub_X : I' ⊆ X := hI'_sub.trans hX'_sub_X
        have hI_sub : I ⊆ X :=
          Finset.insert_subset_iff.mpr ⟨hx, hI'_sub_X⟩
        have hI_indep :
            ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ R a b := by
          intro a ha b hb hne
          have ha_x : a = x ∨ a ∈ I' := by
            simpa [I] using ha
          have hb_x : b = x ∨ b ∈ I' := by
            simpa [I] using hb
          by_cases ha_eq : a = x
          · rw [ha_eq]
            by_cases hb_eq : b = x
            · exfalso
              exact hne (by rw [ha_eq, hb_eq])
            · have hbI : b ∈ I' := by tauto
              have hbN : b ∉ N := by
                have h5 : b ∈ X' := hI'_sub hbI
                exact (Finset.mem_sdiff.mp h5).2
              intro hxb
              have h6 : b ∈ X.filter (R x) :=
                Finset.mem_filter.mpr ⟨hI'_sub_X hbI, hxb⟩
              exact hbN (by
                simp only [N, Finset.mem_insert]
                exact Or.inr h6)
          · have haI : a ∈ I' := by tauto
            by_cases hb_eq : b = x
            · rw [hb_eq]
              have haN : a ∉ N := by
                have h5 : a ∈ X' := hI'_sub haI
                exact (Finset.mem_sdiff.mp h5).2
              intro hax
              have hxa : R x a := hR_symm a x hax
              have h6 : a ∈ X.filter (R x) :=
                Finset.mem_filter.mpr ⟨hI'_sub_X haI, hxa⟩
              exact haN (by
                simp only [N, Finset.mem_insert]
                exact Or.inr h6)
            · have hbI : b ∈ I' := by tauto
              exact hI'_indep a haI b hbI hne
        have h_disj : Disjoint N X' := by
          simp only [X', Finset.disjoint_left, Finset.mem_sdiff]
          tauto
        have h4 : X = N ∪ X' := by
          rw [Finset.union_sdiff_of_subset hN_sub_X]
        have h_mass :
            (D + 1 : ENNReal) * ∑ z ∈ I, w z ≥ ∑ z ∈ X, w z := by
          have h_sum_I :
              ∑ z ∈ I, w z = w x + ∑ z ∈ I', w z := by
            rw [Finset.sum_insert h_x_not_in_I']
          rw [h_sum_I]
          have h6 :
              ∑ z ∈ X, w z =
                (∑ z ∈ N, w z) + ∑ z ∈ X', w z := by
            rw [h4, Finset.sum_union h_disj]
          rw [h6, mul_add]
          exact add_le_add h_weight_N hI'_mass
        exact ⟨I, hI_sub, hI_indep, h_mass⟩
  exact H_main S (by rfl)

end Kakeya.Assouad
