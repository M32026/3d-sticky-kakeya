import MyLeanRepo.Kakeya.Cinematic.Section5.JointFiberCardinalityRegularizationInputs
import Mathlib.Combinatorics.Pigeonhole

/-!
# Joint dyadic regularization of two fiber cardinalities

Given a finite set of items each carrying two positive cardinalities bounded by
`upper`, pigeonhole over the pair of dyadic scales and retain the exact squared
logarithmic loss.
-/

namespace Kakeya.Cinematic

theorem joint_fiber_cardinality_regularization :
    JointFiberCardinalityRegularizationStatement := by
  intro α _ items metricCard retainedCard upper hitems hbound
  let label : α → ℕ × ℕ := fun item =>
    (Nat.log2 (metricCard item), Nat.log2 (retainedCard item))
  let n : ℕ := Nat.log2 upper + 1
  let R : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n

  have h_n_pos : 0 < n := by
    dsimp only [n] <;> omega

  have hR_card : R.card = n ^ 2 := by
    simp [R, Finset.card_product, n] <;> ring

  have hR_pos : 0 < R.card := by
    rw [hR_card]
    exact pow_pos h_n_pos 2

  have h1 : ∀ item ∈ items, label item ∈ R := by
    intro item hitem
    have hmb := hbound item hitem
    have h_pos1 : 0 < metricCard item := hmb.1
    have h_le1 : metricCard item ≤ upper := hmb.2.1
    have h_pos2 : 0 < retainedCard item := hmb.2.2.1
    have h_le2 : retainedCard item ≤ upper := hmb.2.2.2
    have h_log1 : Nat.log2 (metricCard item) ≤ Nat.log2 upper := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right h_le1
    have h_log2 : Nat.log2 (retainedCard item) ≤ Nat.log2 upper := by
      rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact Nat.log_mono_right h_le2
    have h_ml : Nat.log2 (metricCard item) < n := by
      dsimp only [n] <;> omega
    have h_rl : Nat.log2 (retainedCard item) < n := by
      dsimp only [n] <;> omega
    simpa [R, label, Finset.mem_product, Finset.mem_range] using
      ⟨h_ml, h_rl⟩

  let n0 : ℕ := (items.card - 1) / R.card
  have h_items_pos : 0 < items.card := Finset.card_pos.mpr hitems
  have h_n0_le : R.card * n0 ≤ items.card - 1 :=
    Nat.mul_div_le (items.card - 1) R.card
  have h_n0_lt : R.card * n0 < items.card := by omega

  have h_pigeon : ∃ (y : ℕ × ℕ), y ∈ R ∧
      n0 < (items.filter (fun item => label item = y)).card :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to h1 h_n0_lt

  rcases h_pigeon with ⟨⟨ml, rl⟩, hl_in_R, h_fiber_gt⟩
  let selected := items.filter (fun item => label item = (ml, rl))

  have h_fiber_ge : n0 + 1 ≤ selected.card := by
    have h : n0 < selected.card := by
      simpa [selected] using h_fiber_gt
    omega

  have h_div_lt : items.card - 1 < R.card * (n0 + 1) := by
    have h2 :
        items.card - 1 =
          R.card * n0 + (items.card - 1) % R.card := by
      rw [Nat.div_add_mod]
    have h3 : (items.card - 1) % R.card < R.card :=
      Nat.mod_lt _ hR_pos
    have h4 : R.card * (n0 + 1) = R.card * n0 + R.card := by
      rw [Nat.mul_succ]
    rw [h2, h4]
    exact add_lt_add_right h3 (R.card * n0)

  have h_ineq : items.card ≤ R.card * selected.card := by
    have h5 : items.card ≤ R.card * (n0 + 1) := by omega
    have h6 : R.card * (n0 + 1) ≤ R.card * selected.card :=
      Nat.mul_le_mul_left R.card h_fiber_ge
    exact le_trans h5 h6

  have hml : ml < n := by
    have h : ml ∈ Finset.range n := (Finset.mem_product.mp hl_in_R).1
    exact Finset.mem_range.mp h

  have hrl : rl < n := by
    have h : rl ∈ Finset.range n := (Finset.mem_product.mp hl_in_R).2
    exact Finset.mem_range.mp h

  have hml' : ml ≤ Nat.log2 upper := by
    dsimp only [n] at hml <;> omega

  have hrl' : rl ≤ Nat.log2 upper := by
    dsimp only [n] at hrl <;> omega

  have h_selected_nonempty : selected.Nonempty := by
    by_contra h
    have h10 : selected.card = 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h10] at h_ineq
    have h11 : items.card = 0 := by omega
    exact Finset.nonempty_iff_ne_empty.mp hitems (by simpa using h11)

  have h_log2_iff : ∀ (x : ℕ), 0 < x → ∀ (k : ℕ),
      Nat.log2 x = k ↔
        (2 ^ k ≤ x ∧ x < 2 ^ (k + 1)) := by
    intro x hx k
    constructor
    · intro h
      have h1 : 2 ^ Nat.log2 x ≤ x := by
        rw [Nat.log2_eq_log_two]
        exact Nat.pow_le_of_le_log (ne_of_gt hx) (le_refl _)
      have h2 : x < 2 ^ (Nat.log2 x + 1) := by
        rw [Nat.log2_eq_log_two]
        exact Nat.lt_pow_succ_log_self (by norm_num) x
      rw [h] at h1 h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have h3 : k ≤ Nat.log2 x := by
        have h4 : Nat.log2 (2 ^ k) ≤ Nat.log2 x := by
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          exact Nat.log_mono_right h1
        have h5 : Nat.log2 (2 ^ k) = k := by
          rw [Nat.log2_eq_log_two, Nat.log_pow (by norm_num) k]
        rw [h5] at h4
        exact h4
      have h6 : Nat.log2 x < k + 1 := by
        by_contra h7
        have h8 : k + 1 ≤ Nat.log2 x := by omega
        have h9 : k + 1 ≤ Nat.log 2 x := by
          rw [← Nat.log2_eq_log_two]
          exact h8
        have h10 : 2 ^ (k + 1) ≤ x :=
          Nat.pow_le_of_le_log (ne_of_gt hx) h9
        omega
      omega

  have h_filter_eq : selected = items.filter (fun item =>
      2 ^ ml ≤ metricCard item ∧
        metricCard item < 2 ^ (ml + 1) ∧
        2 ^ rl ≤ retainedCard item ∧
        retainedCard item < 2 ^ (rl + 1)) := by
    ext item
    simp only [selected, Finset.mem_filter]
    constructor
    · rintro ⟨hitem, h_eq⟩
      have h_pos1 : 0 < metricCard item := (hbound item hitem).1
      have h_pos2 : 0 < retainedCard item :=
        (hbound item hitem).2.2.1
      have h_eq1 : Nat.log2 (metricCard item) = ml := by
        exact (Prod.ext_iff.mp h_eq).1
      have h_eq2 : Nat.log2 (retainedCard item) = rl := by
        exact (Prod.ext_iff.mp h_eq).2
      have h1 := (h_log2_iff (metricCard item) h_pos1 ml).mp h_eq1
      have h2 := (h_log2_iff (retainedCard item) h_pos2 rl).mp h_eq2
      exact ⟨hitem, h1.1, h1.2, h2.1, h2.2⟩
    · rintro ⟨hitem, h1, h2, h3, h4⟩
      have h_pos1 : 0 < metricCard item := (hbound item hitem).1
      have h_pos2 : 0 < retainedCard item :=
        (hbound item hitem).2.2.1
      have h_eq1 : Nat.log2 (metricCard item) = ml :=
        (h_log2_iff (metricCard item) h_pos1 ml).mpr ⟨h1, h2⟩
      have h_eq2 : Nat.log2 (retainedCard item) = rl :=
        (h_log2_iff (retainedCard item) h_pos2 rl).mpr ⟨h3, h4⟩
      exact ⟨hitem, Prod.ext h_eq1 h_eq2⟩

  have h_ineq' :
      items.card ≤ (Nat.log2 upper + 1) ^ 2 * selected.card := by
    rw [hR_card] at h_ineq
    exact h_ineq

  have h_final : ∀ item ∈ selected,
      2 ^ ml ≤ metricCard item ∧
        metricCard item < 2 ^ (ml + 1) ∧
        2 ^ rl ≤ retainedCard item ∧
        retainedCard item < 2 ^ (rl + 1) := by
    intro item hitem
    rw [h_filter_eq] at hitem
    exact (Finset.mem_filter.mp hitem).2

  exact
    ⟨ml, rl, selected, hml', hrl', h_selected_nonempty,
      h_filter_eq, h_ineq', h_final⟩

end Kakeya.Cinematic
