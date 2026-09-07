import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleFiniteCoordinationSchedule

/-!
# The finite power-scale schedule in Proposition 6.3

The Lipschitz regularization in the analogue of Lemma 4.7 is performed at a
fixed finite list of power scales, not at every dyadic scale between the fine
scale and one.  For ratio `q > 1`, coordinate `k` requests the nearby CWA
witness at `q^k * delta`, uses the next scale (rounded upwards to the fine
grid) as its spatial scale, and asks for normal variation at most
`coefficient * q^k * delta`.

If `q^N * delta` reaches `2 / coefficient`, these coordinates cover exactly
the nontrivial distance range for a `coefficient`-Lipschitz map.  Distances
above that range are handled by the diameter-two bound for unit normals.
Keeping `N` as an outer parameter is important: in Proposition 6.3 it is
chosen from the epsilon hierarchy and is independent of `delta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The paper's finite geometric schedule for the Lemma 4.7 iteration. -/
structure Proposition63FiniteLipschitzSchedule
    (delta coefficient ratio : ℝ) (N : ℕ) where
  requested : ℕ → WZ2PaperRequestedScale delta
  spatialScale : ℕ → ℝ
  variationScale : ℕ → ℝ
  K : ℕ → ℕ
  requested_value : ∀ coordinate, coordinate < N →
    (requested coordinate).1 = ratio ^ coordinate * delta
  spatial_value : ∀ coordinate,
    spatialScale coordinate =
      (Nat.ceil (ratio ^ (coordinate + 1)) : ℝ) * delta
  variation_value : ∀ coordinate,
    variationScale coordinate =
      coefficient * (ratio ^ coordinate * delta)
  K_value : ∀ coordinate,
    K coordinate = Nat.ceil (ratio ^ (coordinate + 1))
  K_pos : ∀ coordinate, coordinate < N → 0 < K coordinate
  spatial_pos : ∀ coordinate, coordinate < N →
    0 < spatialScale coordinate
  variation_pos : ∀ coordinate, coordinate < N →
    0 < variationScale coordinate
  spatial_aligned : ∀ coordinate, coordinate < N →
    spatialScale coordinate = (K coordinate : ℝ) * delta
  covers : ∀ d : ℝ, delta < d → d ≤ 4 → coefficient * d < 2 →
    ∃ coordinate, coordinate < N ∧
      d ≤ spatialScale coordinate ∧
      variationScale coordinate ≤ coefficient * d

/-- Construct the fixed-length power-scale schedule used in Proposition 6.3.

The endpoint assumptions say that the last power scale both remains
admissible and reaches the distance at which the unit-normal estimate takes
over. -/
theorem proposition63_finite_lipschitz_schedule
    {delta coefficient ratio : ℝ} {N : ℕ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hcoefficient : 0 < coefficient)
    (hratio : 1 < ratio)
    (hN : 0 < N)
    (hreaches : 2 / coefficient ≤ ratio ^ N * delta)
    (htop : ratio ^ N * delta ≤ 1) :
    Nonempty
      (Proposition63FiniteLipschitzSchedule
        delta coefficient ratio N) := by
  let grid : ℕ → ℝ := fun coordinate => ratio ^ coordinate * delta
  have hratioNonnegative : 0 ≤ ratio := by linarith
  have hratioOne : 1 ≤ ratio := hratio.le
  have hgridPositive : ∀ coordinate, 0 < grid coordinate := by
    intro coordinate
    dsimp only [grid]
    positivity
  have hgridLower : ∀ coordinate, delta ≤ grid coordinate := by
    intro coordinate
    dsimp only [grid]
    calc
      delta = 1 * delta := by ring
      _ ≤ ratio ^ coordinate * delta := by
        gcongr
        exact one_le_pow₀ hratioOne
  have hgridTop : ∀ coordinate, coordinate < N →
      grid coordinate ≤ 1 := by
    intro coordinate hcoordinate
    have hpower : ratio ^ coordinate ≤ ratio ^ N := by
      exact pow_le_pow_right₀ hratioOne (Nat.le_of_lt hcoordinate)
    calc
      grid coordinate ≤ ratio ^ N * delta := by
        dsimp only [grid]
        gcongr
      _ ≤ 1 := htop
  let requested : ℕ → WZ2PaperRequestedScale delta := fun coordinate =>
    ⟨min (grid coordinate) 1,
      le_min (hgridLower coordinate) hdeltaOne,
      min_le_right _ _⟩
  let K : ℕ → ℕ := fun coordinate =>
    Nat.ceil (ratio ^ (coordinate + 1))
  let spatialScale : ℕ → ℝ := fun coordinate =>
    (K coordinate : ℝ) * delta
  let variationScale : ℕ → ℝ := fun coordinate =>
    coefficient * grid coordinate
  have hKPositive : ∀ coordinate, 0 < K coordinate := by
    intro coordinate
    apply Nat.ceil_pos.mpr
    positivity
  have hspatialPositive : ∀ coordinate, 0 < spatialScale coordinate := by
    intro coordinate
    dsimp only [spatialScale]
    positivity
  have hvariationPositive : ∀ coordinate, 0 < variationScale coordinate := by
    intro coordinate
    dsimp only [variationScale]
    positivity
  refine ⟨{
    requested := requested
    spatialScale := spatialScale
    variationScale := variationScale
    K := K
    requested_value := ?_
    spatial_value := fun _ => rfl
    variation_value := fun _ => rfl
    K_value := fun _ => rfl
    K_pos := fun coordinate _ => hKPositive coordinate
    spatial_pos := fun coordinate _ => hspatialPositive coordinate
    variation_pos := fun coordinate _ => hvariationPositive coordinate
    spatial_aligned := fun _ _ => rfl
    covers := ?_
  }⟩
  · intro coordinate hcoordinate
    change min (grid coordinate) 1 = ratio ^ coordinate * delta
    rw [min_eq_left (hgridTop coordinate hcoordinate)]
  · intro d hdeltaD _hdFour hcoefficientD
    have hdEndpoint : d < 2 / coefficient := by
      rw [lt_div_iff₀ hcoefficient]
      simpa [mul_comm] using hcoefficientD
    have hdTop : d ≤ grid N := by
      exact (hdEndpoint.trans_le hreaches).le
    let reaches : ℕ → Prop := fun coordinate =>
      d ≤ grid (coordinate + 1)
    have htopCoordinate : reaches (N - 1) := by
      dsimp only [reaches]
      have hsuccessor : N - 1 + 1 = N := by omega
      rwa [hsuccessor]
    let coordinate : ℕ := Nat.find ⟨N - 1, htopCoordinate⟩
    have hcoordinateProperty : reaches coordinate := by
      exact Nat.find_spec (H := ⟨N - 1, htopCoordinate⟩)
    have hcoordinateLe : coordinate ≤ N - 1 := by
      exact Nat.find_min' (H := ⟨N - 1, htopCoordinate⟩)
        (m := N - 1) htopCoordinate
    have hcoordinateLt : coordinate < N := by omega
    have hgridBefore : grid coordinate < d := by
      by_cases hzero : coordinate = 0
      · rw [hzero]
        simpa [grid] using hdeltaD
      · have hprevious : ¬ reaches (coordinate - 1) := by
          exact Nat.find_min (H := ⟨N - 1, htopCoordinate⟩)
            (m := coordinate - 1) (by omega)
        have hsuccessor : coordinate - 1 + 1 = coordinate := by omega
        dsimp only [reaches] at hprevious
        rw [hsuccessor] at hprevious
        exact lt_of_not_ge hprevious
    refine ⟨coordinate, hcoordinateLt, ?_, ?_⟩
    · have hceil : ratio ^ (coordinate + 1) ≤
          (Nat.ceil (ratio ^ (coordinate + 1)) : ℝ) :=
        Nat.le_ceil _
      calc
        d ≤ grid (coordinate + 1) := hcoordinateProperty
        _ ≤ (Nat.ceil (ratio ^ (coordinate + 1)) : ℝ) * delta := by
          dsimp only [grid]
          gcongr
        _ = spatialScale coordinate := rfl
    · change coefficient * grid coordinate ≤ coefficient * d
      exact mul_le_mul_of_nonneg_left hgridBefore.le hcoefficient.le

/-- The literal power schedule from the proof of Lemma 4.7.  Its ratio is
the `N`-th root of `(2 / coefficient) / delta`, so its `N`-th endpoint is
exactly `2 / coefficient`.  This is the first distance at which the
diameter-two bound for unit normals proves the desired Lipschitz estimate.
For `coefficient = delta^(-epsilon)` this is, up to the harmless factor two,
the paper's list `delta^(j/N)`. -/
theorem proposition63_power_lipschitz_schedule
    {delta coefficient : ℝ} {N : ℕ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (hcoefficient : 0 < coefficient)
    (hfinest : coefficient * delta < 2)
    (hN : 0 < N)
    (hcoefficientTwo : 2 ≤ coefficient) :
    Nonempty
      (Proposition63FiniteLipschitzSchedule
        delta coefficient
        (Real.rpow ((2 / coefficient) / delta) ((N : ℝ)⁻¹)) N) := by
  let endpoint : ℝ := 2 / coefficient
  let base : ℝ := endpoint / delta
  let ratio : ℝ := Real.rpow base ((N : ℝ)⁻¹)
  have hendpointPositive : 0 < endpoint := by
    dsimp only [endpoint]
    positivity
  have hdeltaEndpoint : delta < endpoint := by
    dsimp only [endpoint]
    exact (lt_div_iff₀ hcoefficient).2 (by simpa [mul_comm] using hfinest)
  have hbaseOne : 1 < base := by
    dsimp only [base]
    exact (lt_div_iff₀ hdelta).2 (by simpa using hdeltaEndpoint)
  have hratio : 1 < ratio := by
    dsimp only [ratio]
    exact Real.one_lt_rpow hbaseOne
      (inv_pos.mpr (by exact_mod_cast hN))
  have hratioPower : ratio ^ N = base := by
    dsimp only [ratio]
    exact Real.rpow_inv_natCast_pow (by positivity : 0 ≤ base) hN.ne'
  have htopEq : ratio ^ N * delta = endpoint := by
    rw [hratioPower]
    dsimp only [base]
    field_simp [hdelta.ne']
  apply proposition63_finite_lipschitz_schedule hdelta hdeltaOne.le
    hcoefficient hratio hN
  · rw [htopEq]
  · rw [htopEq]
    dsimp only [endpoint]
    exact (div_le_one hcoefficient).2 hcoefficientTwo

end Kakeya.Assouad.PureWZ2

end
