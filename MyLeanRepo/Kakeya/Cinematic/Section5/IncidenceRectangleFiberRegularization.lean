import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceRectangleFiberRegularizationInputs

/-!
# Regularize selected incidence fibers below one coarse parent

Select the fine rectangles whose selected incidence fibers retain at least
half the parent-average lower scale, while preserving a quantitative fraction
of the parent edge mass.
-/

namespace Kakeya.Cinematic

theorem incidence_rectangle_fiber_regularization :
    IncidenceRectangleFiberRegularizationStatement := by
  intro α β γ _ _ _ edges parent coarse fiberLower logLoss fiberBound
    hfiberLower hlogLoss hfiberBoundPos hparentNonempty haggregate hfiberBound
  let threshold : ℝ := (fiberLower : ℝ) / (2 * logLoss)
  let rectangles := incidenceRectangleSupport edges parent coarse
  let parentEdges := incidenceParentEdges edges parent coarse
  let selectedRectangles := rectangles.filter fun rectangle =>
    threshold ≤ ((incidenceRectangleFiber edges rectangle).card : ℝ)
  let pairLower : ℕ := Nat.ceil threshold
  have hlogLossPos : 0 < logLoss := by linarith
  have hthresholdPos : 0 < threshold := by
    dsimp only [threshold]
    positivity
  have hthresholdNonneg : 0 ≤ threshold := by positivity
  have hsum : (parentEdges.card : ℝ) =
      ∑ rectangle ∈ rectangles,
        ((incidenceRectangleFiber edges rectangle).card : ℝ) := by
    exact_mod_cast
      incidenceParentEdges_card_eq_rectangle_sum edges parent coarse
  have hlightContrib :
      (rectangles.card : ℝ) * threshold ≤
        (parentEdges.card : ℝ) / 2 := by
    have h2 : (rectangles.card : ℝ) * threshold =
        ((rectangles.card : ℝ) * (fiberLower : ℝ)) /
          (2 * logLoss) := by
      dsimp only [threshold]
      field_simp [hlogLossPos.ne']
    rw [h2]
    have h3 :
        ((rectangles.card : ℝ) * (fiberLower : ℝ)) /
              (2 * logLoss) ≤
          (logLoss * (parentEdges.card : ℝ)) /
              (2 * logLoss) := by
      gcongr
    have h4 :
        (logLoss * (parentEdges.card : ℝ)) /
            (2 * logLoss) =
          (parentEdges.card : ℝ) / 2 := by
      field_simp [hlogLossPos.ne']
    rw [h4] at h3
    exact h3
  have hcardBound :
      ((parentEdges.card : ℝ) / 2) / fiberBound ≤
        (selectedRectangles.card : ℝ) := by
    have h := heavy_card_lower rectangles
      (fun rectangle =>
        ((incidenceRectangleFiber edges rectangle).card : ℝ))
      threshold fiberBound (parentEdges.card : ℝ)
      hthresholdNonneg hfiberBoundPos hfiberBound hsum.le
    have h5 :
        ((parentEdges.card : ℝ) / 2) / fiberBound ≤
          (((parentEdges.card : ℝ) -
              (rectangles.card : ℝ) * threshold) /
            fiberBound) := by
      have h51 :
          (parentEdges.card : ℝ) / 2 ≤
            (parentEdges.card : ℝ) -
              (rectangles.card : ℝ) * threshold := by
        linarith
      exact div_le_div_of_nonneg_right h51 hfiberBoundPos.le
    exact h5.trans h
  have hselectedNonempty : selectedRectangles.Nonempty := by
    have hparentCardPos : 0 < (parentEdges.card : ℝ) := by
      exact_mod_cast hparentNonempty.card_pos
    have hpos :
        0 < ((parentEdges.card : ℝ) / 2) / fiberBound := by
      positivity
    have hcardPos : 0 < (selectedRectangles.card : ℝ) :=
      hpos.trans_le hcardBound
    exact Finset.card_pos.mp (by exact_mod_cast hcardPos)
  have hpairLowerPos : 0 < pairLower := by
    dsimp only [pairLower]
    exact Nat.ceil_pos.mpr hthresholdPos
  have hfiberLower_le :
      (fiberLower : ℝ) ≤
        2 * logLoss * (pairLower : ℝ) := by
    dsimp only [pairLower]
    have h : threshold ≤ (Nat.ceil threshold : ℝ) :=
      Nat.le_ceil threshold
    dsimp only [threshold] at h
    have h6 :
        (fiberLower : ℝ) / (2 * logLoss) ≤
          (Nat.ceil threshold : ℝ) := h
    have h7 :
        (fiberLower : ℝ) ≤
          2 * logLoss * (Nat.ceil threshold : ℝ) := by
      calc
        (fiberLower : ℝ) =
            2 * logLoss *
              ((fiberLower : ℝ) / (2 * logLoss)) := by
          field_simp [hlogLossPos.ne']
        _ ≤ 2 * logLoss * (Nat.ceil threshold : ℝ) := by
          gcongr
    exact h7
  have hselectedFiber :
      ∀ rectangle ∈ selectedRectangles,
        pairLower ≤
          (incidenceRectangleFiber edges rectangle).card := by
    intro rectangle hrect
    have h8 :
        threshold ≤
          ((incidenceRectangleFiber edges rectangle).card : ℝ) :=
      (Finset.mem_filter.mp hrect).2
    dsimp only [pairLower]
    exact Nat.ceil_le.mpr h8
  exact
    ⟨pairLower, selectedRectangles, rfl, hpairLowerPos, rfl,
      hselectedNonempty, hcardBound, hfiberLower_le,
      hselectedFiber⟩

end Kakeya.Cinematic
