import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityBalancedFiniteLipschitz

/-!
# One-coordinate finite Lipschitz schedule

The cropped paper shadings have diameter at most four.  Consequently a single
integer-aligned spatial scale `ceil(4 / delta) * delta` covers every relevant
distance.  Taking variation `coefficient * delta` gives the desired
`coefficient * d` bound for every `d > delta`.  No logarithmic scale grid is
needed by the finite planiness theorem.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The elementary one-coordinate schedule used by both balanced planiness
branches. -/
structure OneScaleFiniteCoordinationSchedule
    (delta coefficient : ℝ) where
  requested : ℕ → WZ2PaperRequestedScale delta
  requested_eq_delta : ∀ coordinate, (requested coordinate).1 = delta
  spatialScale : ℕ → ℝ
  variationScale : ℕ → ℝ
  K : ℕ → ℕ
  K_pos : ∀ coordinate, coordinate < 1 → 0 < K coordinate
  spatial_pos : ∀ coordinate, coordinate < 1 → 0 < spatialScale coordinate
  variation_pos : ∀ coordinate, coordinate < 1 →
    0 < variationScale coordinate
  spatial_aligned : ∀ coordinate, coordinate < 1 →
    spatialScale coordinate = (K coordinate : ℝ) * delta
  covers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
    ∃ coordinate, coordinate < 1 ∧ d ≤ spatialScale coordinate ∧
      variationScale coordinate ≤ coefficient * d

/-- Construct the one-coordinate schedule. -/
theorem one_scale_finite_coordination_schedule
    (delta coefficient : ℝ)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hcoefficient : 0 < coefficient) :
    Nonempty (OneScaleFiniteCoordinationSchedule delta coefficient) := by
  let requestedScale : WZ2PaperRequestedScale delta :=
    ⟨delta, le_rfl, hdeltaOne⟩
  let K0 : ℕ := Nat.ceil (4 / delta)
  let spatial : ℝ := (K0 : ℝ) * delta
  let variation : ℝ := coefficient * delta
  have hratio : 0 < 4 / delta := by positivity
  have hK0 : 0 < K0 := by
    exact (Nat.ceil_pos.mpr hratio)
  have hspatial : 0 < spatial := by
    dsimp only [spatial]
    positivity
  have hvariation : 0 < variation := by
    dsimp only [variation]
    positivity
  have hfour : 4 ≤ spatial := by
    have hceil : 4 / delta ≤ (K0 : ℝ) := Nat.le_ceil _
    have hscaled := mul_le_mul_of_nonneg_right hceil hdelta.le
    simpa [spatial, div_mul_cancel₀ 4 hdelta.ne'] using hscaled
  exact ⟨{
    requested := fun _ => requestedScale
    requested_eq_delta := fun _ => rfl
    spatialScale := fun _ => spatial
    variationScale := fun _ => variation
    K := fun _ => K0
    K_pos := fun _ _ => hK0
    spatial_pos := fun _ _ => hspatial
    variation_pos := fun _ _ => hvariation
    spatial_aligned := fun _ _ => rfl
    covers := by
      intro d hdeltaD hdFour _
      refine ⟨0, by norm_num, hdFour.trans hfour, ?_⟩
      dsimp only [variation]
      exact mul_le_mul_of_nonneg_left hdeltaD.le hcoefficient.le
  }⟩

end Kakeya.Assouad.PureWZ2

end
