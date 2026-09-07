import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteGridEveryScaleLocalAD

/-!
# Integer-aligned finite schedule for Proposition 6.3

The Lemma 4.12 iteration only needs finitely many internal query scales.
Whole-cell pullback to the fixed root family requires each such scale to be
an exact integer multiple of the root tube radius.  This module rounds each
finite target upward to the root grid and records both the exact alignment
and its one-grid-step error.

This rounding is internal to Lemma 4.12.  In particular, it does not alter
either of the two main Proposition 6.2 calls at their exact power scale
`Delta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- A finite list of requested Lemma 4.12 scales, each aligned with the fixed
root `delta` grid and lying less than one grid step above its target. -/
structure Proposition63AlignedFiniteSchedule
    (delta : ℝ) (N : ℕ) (target : Fin N → ℝ) where
  requested : Fin N → WZ2PaperRequestedScale delta
  scaleFactor : Fin N → ℕ
  scaleFactor_pos : ∀ coordinate, 0 < scaleFactor coordinate
  requested_aligned : ∀ coordinate,
    (requested coordinate).1 = (scaleFactor coordinate : ℝ) * delta
  target_le_requested : ∀ coordinate,
    target coordinate ≤ (requested coordinate).1
  requested_lt_target_add_delta : ∀ coordinate,
    (requested coordinate).1 < target coordinate + delta

/-- The exact alignment package consumed by one dependent whole-cell
pullback step. -/
theorem Proposition63AlignedFiniteSchedule.alignment
    {delta : ℝ} {N : ℕ} {target : Fin N → ℝ}
    (schedule : Proposition63AlignedFiniteSchedule delta N target)
    (coordinate : Fin N) :
    ∃ scaleFactor : ℕ, 0 < scaleFactor ∧
      (schedule.requested coordinate).1 =
        (scaleFactor : ℝ) * delta :=
  ⟨schedule.scaleFactor coordinate, schedule.scaleFactor_pos coordinate,
    schedule.requested_aligned coordinate⟩

/-- Round every member of a finite target list upward to the root grid. -/
theorem proposition63_aligned_finite_schedule
    {delta : ℝ} {N : ℕ} (target : Fin N → ℝ)
    (hdelta : 0 < delta)
    (htargetLower : ∀ coordinate, delta ≤ target coordinate)
    (htargetUpper : ∀ coordinate, target coordinate + delta ≤ 1) :
    Nonempty (Proposition63AlignedFiniteSchedule delta N target) := by
  let scaleFactor : Fin N → ℕ := fun coordinate =>
    Nat.ceil (target coordinate / delta)
  let aligned : Fin N → ℝ := fun coordinate =>
    (scaleFactor coordinate : ℝ) * delta
  have htargetPos : ∀ coordinate, 0 < target coordinate := by
    intro coordinate
    exact hdelta.trans_le (htargetLower coordinate)
  have hfactorPos : ∀ coordinate, 0 < scaleFactor coordinate := by
    intro coordinate
    dsimp only [scaleFactor]
    exact Nat.ceil_pos.mpr (div_pos (htargetPos coordinate) hdelta)
  have htargetAligned : ∀ coordinate, target coordinate ≤ aligned coordinate := by
    intro coordinate
    have hceil : target coordinate / delta ≤
        (scaleFactor coordinate : ℝ) := by
      dsimp only [scaleFactor]
      exact Nat.le_ceil _
    have hscaled := mul_le_mul_of_nonneg_right hceil hdelta.le
    dsimp only [aligned]
    simpa [div_mul_cancel₀ (target coordinate) hdelta.ne'] using hscaled
  have halignedUpper : ∀ coordinate,
      aligned coordinate < target coordinate + delta := by
    intro coordinate
    have hceil : (scaleFactor coordinate : ℝ) <
        target coordinate / delta + 1 := by
      dsimp only [scaleFactor]
      exact Nat.ceil_lt_add_one
        (div_nonneg (htargetPos coordinate).le hdelta.le)
    have hscaled := mul_lt_mul_of_pos_right hceil hdelta
    dsimp only [aligned]
    simpa [div_mul_cancel₀ (target coordinate) hdelta.ne', add_mul] using
      hscaled
  have hdeltaAligned : ∀ coordinate, delta ≤ aligned coordinate := by
    intro coordinate
    have hone : (1 : ℝ) ≤ scaleFactor coordinate := by
      exact_mod_cast hfactorPos coordinate
    dsimp only [aligned]
    nlinarith
  have halignedOne : ∀ coordinate, aligned coordinate ≤ 1 := by
    intro coordinate
    exact (halignedUpper coordinate).le.trans (htargetUpper coordinate)
  let requested : Fin N → WZ2PaperRequestedScale delta := fun coordinate =>
    ⟨aligned coordinate, hdeltaAligned coordinate, halignedOne coordinate⟩
  exact ⟨{
    requested := requested
    scaleFactor := scaleFactor
    scaleFactor_pos := hfactorPos
    requested_aligned := fun _ => rfl
    target_le_requested := htargetAligned
    requested_lt_target_add_delta := halignedUpper
  }⟩

/-- The power grid used by the finite Lemma 4.12 interpolation, with an
explicit starting coordinate. -/
def proposition63FiniteGridTarget
    (delta : ℝ) (gridSteps start count : ℕ) (coordinate : Fin count) : ℝ :=
  finiteGridScaleVal delta gridSteps (start + coordinate.val)

/-- Integer-align a finite consecutive segment of the Lemma 4.12 power grid.
The caller retains the two elementary endpoint bounds because their eventual
values are fixed by the Proposition 6.3 epsilon hierarchy. -/
theorem proposition63_aligned_finiteGrid_schedule
    {delta : ℝ} {gridSteps start count : ℕ}
    (hdelta : 0 < delta)
    (hgridLower : ∀ coordinate : Fin count,
      delta ≤ proposition63FiniteGridTarget
        delta gridSteps start count coordinate)
    (hgridUpper : ∀ coordinate : Fin count,
      proposition63FiniteGridTarget delta gridSteps start count coordinate +
          delta ≤ 1) :
    Nonempty (Proposition63AlignedFiniteSchedule delta count
      (proposition63FiniteGridTarget delta gridSteps start count)) :=
  proposition63_aligned_finite_schedule
    (proposition63FiniteGridTarget delta gridSteps start count) hdelta
    hgridLower hgridUpper

end Kakeya.Assouad.PureWZ2

end
