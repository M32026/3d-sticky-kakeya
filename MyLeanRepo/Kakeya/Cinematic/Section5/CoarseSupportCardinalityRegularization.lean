import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseSupportCardinalityRegularizationInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Regularize coarse support cardinalities

This is the final finite cardinality uniformization before applying the
coarse Proposition 26 count.
-/

namespace Kakeya.Cinematic

theorem coarse_support_cardinality_regularization :
    CoarseSupportCardinalityRegularizationStatement := by
  intro α γ _ _ ambient active support h_active h_support_nonempty h_support_subset

  have h_ambient_pos : 0 < ambient.card := by
    obtain ⟨coarse₀, hcoarse₀⟩ := h_active
    have h1 : (support coarse₀).Nonempty := h_support_nonempty coarse₀ hcoarse₀
    have h2 : 0 < (support coarse₀).card := Finset.Nonempty.card_pos h1
    have h3 : (support coarse₀).card ≤ ambient.card :=
      Finset.card_le_card (h_support_subset coarse₀ hcoarse₀)
    exact lt_of_lt_of_le h2 h3

  let f : γ → ℕ := fun coarse => Nat.log2 (support coarse).card

  let L : Finset ℕ := Finset.range (Nat.log2 ambient.card + 1)

  have h_f_in_L : ∀ coarse ∈ active, f coarse ∈ L := by
    intro coarse hcoarse
    have h1 : (support coarse).card ≤ ambient.card :=
      Finset.card_le_card (h_support_subset coarse hcoarse)
    have h2 : f coarse ≤ Nat.log2 ambient.card := by
      dsimp only [f]
      have h21 : Nat.log 2 (support coarse).card ≤ Nat.log 2 ambient.card :=
        Nat.log_mono_right h1
      simpa [Nat.log2_eq_log_two] using h21
    simp only [L, Finset.mem_range]
    exact Nat.lt_succ_of_le h2

  have h_mapsTo : (active : Set γ).MapsTo f L := by
    intro x hx
    exact h_f_in_L x hx

  have h_sum :
      active.card =
        Finset.sum L
          (fun l => (active.filter (fun coarse => f coarse = l)).card) := by
    have h_filter_all : active.filter (fun coarse => f coarse ∈ L) = active := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, _⟩
        exact hx
      · intro hx
        exact ⟨hx, h_f_in_L x hx⟩
    have h :
        Finset.sum L
            (fun l => (active.filter (fun coarse => f coarse = l)).card) =
          (active.filter (fun coarse => f coarse ∈ L)).card :=
      Finset.sum_card_fiberwise_eq_card_filter active L f
    rw [h_filter_all] at h
    exact h.symm

  have h_L_nonempty : L.Nonempty := by
    refine' ⟨0, _⟩
    simp only [L, Finset.mem_range]
    omega

  obtain ⟨level, hlevel_in_L, hlevel_max⟩ :=
    Finset.exists_max_image L
      (fun l : ℕ => (active.filter (fun coarse => f coarse = l)).card)
      h_L_nonempty

  let fiber : Finset γ := active.filter (fun coarse => f coarse = level)

  have h_pigeonhole : active.card ≤ L.card * fiber.card := by
    have h1 :
        ∀ l ∈ L,
          (active.filter (fun coarse => f coarse = l)).card ≤ fiber.card := by
      intro l hl
      exact hlevel_max l hl
    have h2 :
        Finset.sum L
            (fun l => (active.filter (fun coarse => f coarse = l)).card) ≤
          L.card * fiber.card :=
      Finset.sum_le_card_nsmul L
        (fun l => (active.filter (fun coarse => f coarse = l)).card)
        fiber.card h1
    rw [h_sum]
    exact h2

  have h_L_card : L.card = Nat.log2 ambient.card + 1 := by
    simp [L]

  have h_main_ineq :
      active.card ≤ (Nat.log2 ambient.card + 1) * fiber.card := by
    rw [h_L_card] at h_pigeonhole
    exact h_pigeonhole

  have h_equiv :
      ∀ (n : ℕ), 0 < n →
        (Nat.log2 n = level ↔
          2 ^ level ≤ n ∧ n < 2 ^ (level + 1)) := by
    intro n hn
    have hb : 1 < (2 : ℕ) := Nat.one_lt_two
    constructor
    · intro h
      have h1 : 2 ^ (Nat.log2 n) ≤ n := by
        simpa [Nat.log2_eq_log_two] using
          Nat.pow_log_le_self 2 (ne_of_gt hn)
      have h2 : n < 2 ^ (Nat.log2 n + 1) := by
        simpa [Nat.log2_eq_log_two] using
          Nat.lt_pow_succ_log_self hb n
      have h3 : 2 ^ level ≤ n := by
        rw [h] at h1
        exact h1
      have h4 : n < 2 ^ (level + 1) := by
        rw [h] at h2
        exact h2
      exact ⟨h3, h4⟩
    · rintro ⟨h1, h2⟩
      have h3 : level ≤ Nat.log2 n := by
        have h41 : Nat.log 2 (2 ^ level) ≤ Nat.log 2 n :=
          Nat.log_mono_right h1
        have h42 : Nat.log2 (2 ^ level) = level := by
          rw [Nat.log2_eq_log_two]
          exact Nat.log_pow hb level
        have h43 : Nat.log2 (2 ^ level) ≤ Nat.log2 n := by
          simpa [Nat.log2_eq_log_two] using h41
        rw [h42] at h43
        exact h43
      have h6 : Nat.log2 n ≤ level := by
        have h7 : 2 ^ (Nat.log2 n) ≤ n := by
          simpa [Nat.log2_eq_log_two] using
            Nat.pow_log_le_self 2 (ne_of_gt hn)
        have h8 : 2 ^ (Nat.log2 n) < 2 ^ (level + 1) :=
          lt_of_le_of_lt h7 h2
        have h9 : Nat.log2 n < level + 1 :=
          (Nat.pow_lt_pow_iff_right hb).mp h8
        omega
      omega

  let selected : Finset γ := active.filter (fun coarse =>
    2 ^ level ≤ (support coarse).card ∧
      (support coarse).card < 2 ^ (level + 1))

  have h_selected_eq : fiber = selected := by
    ext x
    simp only [fiber, selected, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hfx⟩
      have h_pos : 0 < (support x).card :=
        Finset.Nonempty.card_pos (h_support_nonempty x hx)
      have h := (h_equiv (support x).card h_pos).mp hfx
      exact ⟨hx, h⟩
    · rintro ⟨hx, h⟩
      have h_pos : 0 < (support x).card :=
        Finset.Nonempty.card_pos (h_support_nonempty x hx)
      have hfx : f x = level :=
        (h_equiv (support x).card h_pos).mpr h
      exact ⟨hx, hfx⟩

  have h_fiber_nonempty : fiber.Nonempty := by
    have h1 : 0 < active.card := Finset.Nonempty.card_pos h_active
    have h2 : 0 < fiber.card := by
      by_contra h3
      have h4 : fiber.card = 0 := by omega
      rw [h4] at h_main_ineq
      omega
    exact Finset.card_pos.mp h2

  have h_selected_nonempty : selected.Nonempty := by
    rw [← h_selected_eq]
    exact h_fiber_nonempty

  have h_level_le : level ≤ Nat.log2 ambient.card := by
    have h : level ∈ L := hlevel_in_L
    simp only [L, Finset.mem_range] at h
    omega

  have h_main_ineq' :
      active.card ≤
        (Nat.log2 ambient.card + 1) * selected.card := by
    have h : fiber.card = selected.card := by
      rw [h_selected_eq]
    rw [h] at h_main_ineq
    exact h_main_ineq

  refine' ⟨level, selected, h_level_le, h_selected_nonempty,
    rfl, h_main_ineq', _⟩
  intro coarse hcoarse
  have h : coarse ∈ selected := hcoarse
  simp only [selected, Finset.mem_filter] at h
  exact h.2

end Kakeya.Cinematic
