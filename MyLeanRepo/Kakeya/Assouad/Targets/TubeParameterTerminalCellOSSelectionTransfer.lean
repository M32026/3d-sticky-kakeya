import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterTerminalCellOSSelectionTransferStatement

/-!
WZ2 Proposition 7.1: transfer per-tube density and a cardinality fraction to
the surviving complete terminal-cell OS selection.
-/

namespace Kakeya.Assouad

theorem tube_parameter_terminal_cell_os_selection_transfer :
    TubeParameterTerminalCellOSSelectionTransferStatement := by
  intro hvol delta hdelta_pos hdelta_le family shading lambda q hpertube hmass
  dsimp only
  intro base levels terminal representatives uniform
  let active := positiveMassIndices shading
  let selected := uniform.selected
  let selectedFamily := selectedTubeFamily family selected
  let selectedShading := selectedTubeShading shading selected
  let loss := tubeParameterTerminalCellOSLoss active.card base levels
  have hvol_eq : ∀ (T : Kakeya.DeltaTube delta), T.volume = Kakeya.deltaTubeVolume delta :=
    hvol.1 delta
  have hvol_pos : 0 < Kakeya.deltaTubeVolume delta := (hvol.2.1 delta hdelta_pos hdelta_le).1
  have hvol_ne_top : Kakeya.deltaTubeVolume delta ≠ ⊤ := (hvol.2.1 delta hdelta_pos hdelta_le).2
  have hvol_ne_zero : Kakeya.deltaTubeVolume delta ≠ 0 := hvol_pos.ne'

  -- Helper: family.toBodyFamily.mass = (family.card : ENNReal) * deltaTubeVolume delta
  have h_family_mass : family.toBodyFamily.mass = (family.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
    have h : family.toBodyFamily.mass = ∑ i : Fin family.card, (family.tube i).volume := rfl
    rw [h]
    have h2 : ∑ i : Fin family.card, (family.tube i).volume = ∑ i : Fin family.card, Kakeya.deltaTubeVolume delta := by
      apply Finset.sum_congr rfl
      intro i _
      exact hvol_eq (family.tube i)
    rw [h2]
    simp [Finset.sum_const]

  -- Helper: selectedFamily.toBodyFamily.mass = (selected.card : ENNReal) * deltaTubeVolume delta
  have h_selected_family_mass : selectedFamily.toBodyFamily.mass = (selected.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
    rw [selectedTubeFamily_mass family selected]
    have h : ∑ i ∈ selected, (family.tube i).volume = ∑ i ∈ selected, Kakeya.deltaTubeVolume delta := by
      apply Finset.sum_congr rfl
      intro i _
      exact hvol_eq (family.tube i)
    rw [h]
    simp [Finset.sum_const]

  -- Helper: selected ⊆ active
  have h_selected_subset_active : selected ⊆ active := by
    calc selected ⊆ terminal.selected := uniform.selected_subset
         _ ⊆ active := terminal.selected_subset

  -- 1. Nonemptiness
  have h1 : selectedFamily.Nonempty := by
    have h : 0 < selected.card := uniform.selected_nonempty.card_pos
    exact h

  -- 2. Density transfer
  have h2 : selectedShading.IsLambdaDense lambda := by
    have h_per_tube : ∀ i ∈ selected, lambda * Kakeya.deltaTubeVolume delta ≤ MeasureTheory.volume (shading.carrier i) := by
      intro i hi
      have h_i_active : i ∈ active := h_selected_subset_active hi
      have h_vol_ne_zero : MeasureTheory.volume (shading.carrier i) ≠ 0 :=
        volume_ne_zero_of_mem_positiveMassIndices shading h_i_active
      have h := hpertube i
      rcases h with (h_empty | h_ge)
      · rw [h_empty] at h_vol_ne_zero
        simp at h_vol_ne_zero
      · exact h_ge
    have h_sum : (selected.card : ENNReal) * (lambda * Kakeya.deltaTubeVolume delta) ≤ ∑ i ∈ selected, MeasureTheory.volume (shading.carrier i) := by
      calc
        (selected.card : ENNReal) * (lambda * Kakeya.deltaTubeVolume delta)
          = ∑ i ∈ selected, (lambda * Kakeya.deltaTubeVolume delta) := by
            simp [Finset.sum_const]
        _ ≤ ∑ i ∈ selected, MeasureTheory.volume (shading.carrier i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact h_per_tube i hi
    have h_main : lambda * selectedFamily.toBodyFamily.mass ≤ selectedShading.mass := by
      rw [h_selected_family_mass, selectedTubeShading_mass shading selected]
      have h_comm : lambda * ((selected.card : ENNReal) * Kakeya.deltaTubeVolume delta) =
          (selected.card : ENNReal) * (lambda * Kakeya.deltaTubeVolume delta) := by ring
      rw [h_comm]
      exact h_sum
    exact h_main

  -- 3. Cardinality fraction
  -- shading.mass = ∑ i ∈ active, volume(shading.carrier i)
  have h_shading_mass_active : shading.mass = ∑ i ∈ active, MeasureTheory.volume (shading.carrier i) := by
    have h : shading.mass = ∑ i : Fin family.card, MeasureTheory.volume (shading.carrier i) := rfl
    rw [h]
    symm
    rw [Finset.sum_subset (show active ⊆ Finset.univ from by simp)]
    intro i _ hi
    have h_not_in : i ∉ active := hi
    have h_vol_zero : MeasureTheory.volume (shading.carrier i) = 0 := by
      by_contra hnz
      have h_in : i ∈ active := by
        dsimp only [active]
        simp [positiveMassIndices, hnz]
      exact h_not_in h_in
    exact h_vol_zero

  -- For i ∈ active, volume(shading.carrier i) ≤ deltaTubeVolume delta
  have h_vol_le : ∀ i ∈ active, MeasureTheory.volume (shading.carrier i) ≤ Kakeya.deltaTubeVolume delta := by
    intro i hi
    have h_subset : shading.carrier i ⊆ (family.tube i).carrier := shading.subset_body i
    have h1 : MeasureTheory.volume (shading.carrier i) ≤ MeasureTheory.volume (family.tube i).carrier :=
      MeasureTheory.measure_mono h_subset
    have h2 : MeasureTheory.volume (family.tube i).carrier = (family.tube i).volume := rfl
    have h3 : (family.tube i).volume = Kakeya.deltaTubeVolume delta := hvol_eq (family.tube i)
    rw [h2, h3] at h1
    exact h1

  -- shading.mass ≤ (active.card : ENNReal) * deltaTubeVolume delta
  have h_shading_le : shading.mass ≤ (active.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
    rw [h_shading_mass_active]
    calc
      (∑ i ∈ active, MeasureTheory.volume (shading.carrier i))
        ≤ ∑ i ∈ active, Kakeya.deltaTubeVolume delta := by
          apply Finset.sum_le_sum
          intro i hi
          exact h_vol_le i hi
      _ = (active.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
        simp [Finset.sum_const]

  -- q * (family.card : ENNReal) ≤ (active.card : ENNReal)
  have h_q_active : q * (family.card : ENNReal) ≤ (active.card : ENNReal) := by
    have h : q * family.toBodyFamily.mass ≤ shading.mass := hmass
    rw [h_family_mass] at h
    have h' : q * ((family.card : ENNReal) * Kakeya.deltaTubeVolume delta) ≤ (active.card : ENNReal) * Kakeya.deltaTubeVolume delta :=
      h.trans h_shading_le
    have h4 : (q * (family.card : ENNReal)) * Kakeya.deltaTubeVolume delta ≤ (active.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using h'
    rw [ENNReal.mul_le_mul_iff_left hvol_ne_zero hvol_ne_top] at h4
    exact h4

  -- terminal.active_card_le in ENNReal
  have h_terminal_card : (active.card : ENNReal) ≤ (Nat.log 2 active.card + 1 : ENNReal) * (terminal.selected.card : ENNReal) := by
    have h := terminal.active_card_le
    exact_mod_cast h

  -- uniform.retention in ENNReal
  let L2_nat : ℕ := (2 * (Nat.log 2 ((base + 1) ^ 4) + 1)) ^ levels
  have h_retention_ennreal : (terminal.selected.card : ENNReal) ≤ (2 : ENNReal) * (L2_nat : ENNReal) * (selected.card : ENNReal) := by
    have h_real := uniform.retention
    exact_mod_cast h_real

  -- Combine: active.card ≤ loss * selected.card
  have h_loss_def : loss = (Nat.log 2 active.card + 1 : ENNReal) * (2 : ENNReal) * (L2_nat : ENNReal) := by
    rfl
  have h_active_le_loss : (active.card : ENNReal) ≤ loss * (selected.card : ENNReal) := by
    rw [h_loss_def]
    calc
      (active.card : ENNReal)
        ≤ (Nat.log 2 active.card + 1 : ENNReal) * (terminal.selected.card : ENNReal) := h_terminal_card
      _ ≤ (Nat.log 2 active.card + 1 : ENNReal) * ((2 : ENNReal) * (L2_nat : ENNReal) * (selected.card : ENNReal)) := by
          exact mul_le_mul_right h_retention_ennreal ((Nat.log 2 active.card + 1 : ENNReal))
      _ = (Nat.log 2 active.card + 1 : ENNReal) * (2 : ENNReal) * (L2_nat : ENNReal) * (selected.card : ENNReal) := by ring

  -- loss ≠ 0 and loss ≠ ⊤
  have h_loss_ne_zero : loss ≠ 0 := by
    rw [h_loss_def]
    positivity
  have h_loss_ne_top : loss ≠ ⊤ := by
    rw [h_loss_def]
    simp [ENNReal.mul_eq_top]

  -- loss⁻¹ * active.card ≤ selected.card
  have h_inv : loss⁻¹ * (active.card : ENNReal) ≤ (selected.card : ENNReal) := by
    have h : loss⁻¹ * (active.card : ENNReal) ≤ loss⁻¹ * (loss * (selected.card : ENNReal)) := by
      exact mul_le_mul_right h_active_le_loss loss⁻¹
    rw [← mul_assoc] at h
    have h_cancel : loss⁻¹ * loss = 1 := ENNReal.inv_mul_cancel h_loss_ne_zero h_loss_ne_top
    rw [h_cancel] at h
    simpa using h

  -- Final conclusion
  have h3 : (q * loss⁻¹) * family.enncard ≤ selectedFamily.enncard := by
    have h : (q * loss⁻¹) * family.enncard = loss⁻¹ * (q * family.enncard) := by ring
    rw [h]
    have h' : loss⁻¹ * (q * family.enncard) ≤ loss⁻¹ * (active.card : ENNReal) := by
      exact mul_le_mul_right h_q_active loss⁻¹
    exact h'.trans h_inv

  exact ⟨h1, h2, h3⟩

end Kakeya.Assouad
