import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellFiberRegularizationStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
WZ2 Proposition 7.1: regularize complete indexed tube fibers over terminal
delta-scale parameter cells.
-/

namespace Kakeya.Assouad

theorem tube_parameter_terminal_cell_fiber_regularization :
    TubeParameterTerminalCellFiberRegularizationStatement := by
  intro delta family active h_active base levels
  let f : Fin family.card → (Fin 4 → ℤ) :=
    indexedTubeTerminalCellIndex base levels
  let m : (Fin 4 → ℤ) → ℕ := fun p =>
    (active.filter (fun i => f i = p)).card
  let img := active.image f
  have h_m_pos : ∀ p ∈ img, 0 < m p := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  have h_m_le : ∀ p ∈ img, m p ≤ active.card := by
    intro p _
    exact Finset.card_le_card (Finset.filter_subset _ _)
  let levelOf : Fin family.card → ℕ := fun i => Nat.log 2 (m (f i))
  let K := Finset.range (Nat.log 2 active.card + 1)
  have h_level_in_K : ∀ i ∈ active, levelOf i ∈ K := by
    intro i hi
    have hfi : f i ∈ img := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have h1 : m (f i) ≤ active.card := h_m_le (f i) hfi
    have h2 : levelOf i ≤ Nat.log 2 active.card := by
      dsimp only [levelOf]
      exact Nat.log_mono_right h1
    simp only [K, Finset.mem_range]
    exact Nat.lt_succ_of_le h2
  let classIndices (k : ℕ) : Finset (Fin family.card) :=
    active.filter (fun i => levelOf i = k)
  have h_sum : ∑ k ∈ K, (classIndices k).card = active.card := by
    have h1 : ∑ k ∈ K, (classIndices k).card =
        (active.filter (fun i => levelOf i ∈ K)).card :=
      Finset.sum_card_fiberwise_eq_card_filter active K levelOf
    have h2 : active.filter (fun i => levelOf i ∈ K) = active := by
      apply Finset.filter_true_of_mem
      exact h_level_in_K
    rw [h1, h2]
  have hK_nonempty : K.Nonempty := by
    simp [K]
  rcases Finset.exists_max_image K (fun k => (classIndices k).card) hK_nonempty
    with ⟨k_opt, _, h_max⟩
  have hK_card : K.card = Nat.log 2 active.card + 1 := by
    simp [K]
  have h_pigeon : active.card ≤ K.card * (classIndices k_opt).card := by
    calc
      active.card = ∑ k ∈ K, (classIndices k).card := h_sum.symm
      _ ≤ ∑ k ∈ K, (classIndices k_opt).card :=
        Finset.sum_le_sum (fun j hj => h_max j hj)
      _ = K.card * (classIndices k_opt).card := by simp
  set selected := classIndices k_opt
  set fiberMultiplicity := 2 ^ k_opt
  have h_selected_subset : selected ⊆ active :=
    Finset.filter_subset _ _
  have h_selected_nonempty : selected.Nonempty := by
    have h : 0 < selected.card := by
      by_contra h'
      have h' : selected.card = 0 := by omega
      have h_all : ∀ j ∈ K, (classIndices j).card = 0 := by
        intro j hj
        have h_le : (classIndices j).card ≤ selected.card := by
          simpa [selected] using h_max j hj
        omega
      have h_sum0 : ∑ k ∈ K, (classIndices k).card = 0 := by
        rw [Finset.sum_congr rfl h_all]; simp
      rw [h_sum] at h_sum0
      exact (Finset.Nonempty.card_pos h_active).ne' h_sum0
    exact Finset.card_pos.mp h
  have h_fm_pos : 0 < fiberMultiplicity := by
    simp [fiberMultiplicity]
  have h_saturated : ∀ i ∈ active, f i ∈ selected.image f → i ∈ selected := by
    intro i hi hfi
    rcases Finset.mem_image.mp hfi with ⟨j, hj, h_eq⟩
    have h_j_level : levelOf j = k_opt := by
      simp only [selected, classIndices, Finset.mem_filter] at hj
      exact hj.2
    have h_i_level : levelOf i = levelOf j := by
      dsimp only [levelOf]
      rw [h_eq]
    have h_ik : levelOf i = k_opt := by
      rw [h_i_level, h_j_level]
    simp only [selected, classIndices, Finset.mem_filter]
    exact ⟨hi, h_ik⟩
  let cells := selected.image f
  have h_cells_eq : cells = selected.image f := rfl
  have h_cells_nonempty : cells.Nonempty :=
    Finset.Nonempty.image h_selected_nonempty f
  have h_fiber_eq : ∀ p ∈ cells,
      (selected.filter (fun i => f i = p)).card = m p := by
    intro p hp
    have h_eq :
        selected.filter (fun i => f i = p) =
          active.filter (fun i => f i = p) := by
      ext x
      simp only [selected, classIndices, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx1, _⟩, hx2⟩
        exact ⟨hx1, hx2⟩
      · rintro ⟨hx1, hx2⟩
        have h3 : f x ∈ cells := by
          rw [hx2]
          exact hp
        have h5 : x ∈ selected := h_saturated x hx1 h3
        have h6 : x ∈ active ∧ levelOf x = k_opt := by
          simp only [selected, classIndices, Finset.mem_filter] at h5
          exact h5
        exact ⟨h6, hx2⟩
    exact congr_arg Finset.card h_eq
  have h_level_bounds : ∀ p ∈ cells,
      2 ^ k_opt ≤ m p ∧ m p < 2 ^ (k_opt + 1) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    have h_j_level : levelOf j = k_opt := by
      simp only [selected, classIndices, Finset.mem_filter] at hj
      exact hj.2
    have h_j_in_active : j ∈ active := by
      simp only [selected, classIndices, Finset.mem_filter] at hj
      exact hj.1
    have hfj : f j ∈ img := Finset.mem_image.mpr ⟨j, h_j_in_active, rfl⟩
    have hmp_pos : m (f j) ≠ 0 := (h_m_pos (f j) hfj).ne'
    have h_log_eq : Nat.log 2 (m (f j)) = k_opt := by
      simpa [levelOf] using h_j_level
    exact (Nat.log_eq_iff (Or.inr ⟨by norm_num, hmp_pos⟩)).mp h_log_eq
  have h_fiber_lower : ∀ p ∈ cells,
      fiberMultiplicity ≤ (selected.filter (fun i => f i = p)).card := by
    intro p hp
    have h10 : 2 ^ k_opt ≤ m p := (h_level_bounds p hp).1
    rw [h_fiber_eq p hp]
    simpa [fiberMultiplicity] using h10
  have h_fiber_upper : ∀ p ∈ cells,
      (selected.filter (fun i => f i = p)).card < 2 * fiberMultiplicity := by
    intro p hp
    have h10 : m p < 2 ^ (k_opt + 1) := (h_level_bounds p hp).2
    rw [h_fiber_eq p hp]
    have h11 : 2 * fiberMultiplicity = 2 ^ (k_opt + 1) := by
      simp [fiberMultiplicity, pow_succ]; ring
    rw [h11]
    exact h10
  have h_active_card_le :
      active.card ≤ (Nat.log 2 active.card + 1) * selected.card := by
    have h12 : active.card ≤ K.card * selected.card := by
      simpa [selected] using h_pigeon
    rw [hK_card] at h12
    exact h12
  exact
    ⟨selected, h_selected_subset, h_selected_nonempty, cells, h_cells_eq,
      h_cells_nonempty, fiberMultiplicity, h_fm_pos, h_fiber_lower,
      h_fiber_upper, h_saturated, h_active_card_le⟩

end Kakeya.Assouad
