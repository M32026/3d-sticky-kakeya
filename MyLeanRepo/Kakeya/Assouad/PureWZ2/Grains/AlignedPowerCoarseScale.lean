import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import Mathlib.Tactic

/-!
# Integer-aligned power coarse scales

For a fine scale `delta` and an exponent `a` in `(0,1]`, round
`delta^a / delta` upward to an integer.  The resulting scale is an exact
integer multiple of `delta` and lies between `delta^a` and `2 delta^a`.
This is the alignment needed by the whole-cell Property-Three pullback; no
exact real-power equality is imposed on the coarse scale.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- An exact integer-grid scale quantitatively comparable to `delta^a`. -/
structure AlignedPowerCoarseScale (delta exponent : ℝ) where
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  rho : ℝ
  rho_eq : rho = (multiplicity : ℝ) * delta
  requested : WZ2PaperRequestedScale delta
  requested_eq : requested.1 = rho
  power_le : Real.rpow delta exponent ≤ rho
  lt_two_power : rho < 2 * Real.rpow delta exponent

/-- Upward integer rounding constructs an aligned requested scale.  The
explicit half-power hypothesis is only used to keep the rounded scale below
one. -/
theorem aligned_power_coarse_scale
    {delta exponent : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hexponent : 0 < exponent)
    (hexponentOne : exponent ≤ 1)
    (hpowerHalf : Real.rpow delta exponent ≤ 1 / 2) :
    Nonempty (AlignedPowerCoarseScale delta exponent) := by
  let power : ℝ := Real.rpow delta exponent
  have hpower : 0 < power := by
    dsimp only [power]
    exact Real.rpow_pos_of_pos hdelta _
  let multiplicity : ℕ := Nat.ceil (power / delta)
  have hmultiplicity : 0 < multiplicity := by
    dsimp only [multiplicity]
    exact Nat.ceil_pos.mpr (div_pos hpower hdelta)
  let rho : ℝ := (multiplicity : ℝ) * delta
  have hceilLower : power / delta ≤ (multiplicity : ℝ) := by
    dsimp only [multiplicity]
    exact Nat.le_ceil _
  have hpowerRho : power ≤ rho := by
    dsimp only [rho]
    have hscaled := mul_le_mul_of_nonneg_right hceilLower hdelta.le
    field_simp [hdelta.ne'] at hscaled
    simpa [mul_comm] using hscaled
  have hceilUpper : (multiplicity : ℝ) < power / delta + 1 := by
    dsimp only [multiplicity]
    exact Nat.ceil_lt_add_one (div_nonneg hpower.le hdelta.le)
  have hrhoUpper : rho < power + delta := by
    dsimp only [rho]
    have hscaled := mul_lt_mul_of_pos_right hceilUpper hdelta
    have hsimp : (power / delta + 1) * delta = power + delta := by
      field_simp [hdelta.ne']
    rwa [hsimp] at hscaled
  have hdeltaPower : delta ≤ power := by
    dsimp only [power]
    have hone : Real.rpow delta 1 ≤ Real.rpow delta exponent :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponentOne
    simpa using hone
  have hrhoTwo : rho < 2 * power := by
    calc
      rho < power + delta := hrhoUpper
      _ ≤ power + power := by gcongr
      _ = 2 * power := by ring
  have hdeltaRho : delta ≤ rho := hdeltaPower.trans hpowerRho
  have hrhoOne : rho ≤ 1 := by
    have htwo : 2 * power ≤ 1 := by
      dsimp only [power] at hpowerHalf ⊢
      linarith
    exact hrhoTwo.le.trans htwo
  let requested : WZ2PaperRequestedScale delta :=
    ⟨rho, hdeltaRho, hrhoOne⟩
  exact ⟨{
    multiplicity := multiplicity
    multiplicity_pos := hmultiplicity
    rho := rho
    rho_eq := rfl
    requested := requested
    requested_eq := rfl
    power_le := hpowerRho
    lt_two_power := hrhoTwo
  }⟩

/-- A power scale separated from the fine scale by a factor six retains that
separation after upward integer rounding. -/
lemma AlignedPowerCoarseScale.six_mul_delta_le
    {delta exponent : ℝ}
    (scale : AlignedPowerCoarseScale delta exponent)
    (hseparated : 6 * delta ≤ Real.rpow delta exponent) :
    6 * delta ≤ scale.rho :=
  hseparated.trans scale.power_le

/-- An integer-grid scale obtained by rounding a power scale downward.  The
extra separation hypothesis keeps the multiplier positive and shows that the
rounded scale loses less than a factor two.  This is the form needed when a
sticky window imposes an upper, rather than a lower, power-scale bound. -/
structure FloorAlignedPowerCoarseScale (delta exponent : ℝ) where
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  rho : ℝ
  rho_eq : rho = (multiplicity : ℝ) * delta
  requested : WZ2PaperRequestedScale delta
  requested_eq : requested.1 = rho
  rho_le_power : rho ≤ Real.rpow delta exponent
  half_power_lt : Real.rpow delta exponent / 2 < rho

/-- Round a power scale downward to the fine grid while retaining a
two-sided constant-factor comparison. -/
theorem floor_aligned_power_coarse_scale
    {delta exponent : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hexponent : 0 < exponent)
    (hexponentOne : exponent ≤ 1)
    (hseparated : 2 * delta ≤ Real.rpow delta exponent) :
    Nonempty (FloorAlignedPowerCoarseScale delta exponent) := by
  let power : ℝ := Real.rpow delta exponent
  have hpower : 0 < power := Real.rpow_pos_of_pos hdelta _
  have hratioTwo : 2 ≤ power / delta := by
    exact (le_div_iff₀ hdelta).2 hseparated
  let multiplicity : ℕ := Nat.floor (power / delta)
  have hmultiplicity : 0 < multiplicity := by
    exact Nat.floor_pos.mpr (by linarith)
  have hfloor : (multiplicity : ℝ) ≤ power / delta := by
    exact Nat.floor_le (by positivity)
  let rho : ℝ := (multiplicity : ℝ) * delta
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    positivity
  have hrhoLePower : rho ≤ power := by
    dsimp only [rho]
    have hscaled := mul_le_mul_of_nonneg_right hfloor hdelta.le
    simpa [div_mul_cancel₀ power hdelta.ne'] using hscaled
  have hpowerLt : power < rho + delta := by
    have hfloorUpper : power / delta < (multiplicity : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hscaled := mul_lt_mul_of_pos_right hfloorUpper hdelta
    dsimp only [rho]
    simpa [div_mul_cancel₀ power hdelta.ne', add_mul] using hscaled
  have hdeltaRho : delta ≤ rho := by
    have hone : (1 : ℝ) ≤ multiplicity := by exact_mod_cast hmultiplicity
    dsimp only [rho]
    nlinarith
  have hhalfPower : power / 2 < rho := by linarith
  have hrhoOne : rho ≤ 1 :=
    hrhoLePower.trans (Real.rpow_le_one hdelta.le hdeltaOne hexponent.le)
  let requested : WZ2PaperRequestedScale delta :=
    ⟨rho, hdeltaRho, hrhoOne⟩
  exact ⟨{
    multiplicity := multiplicity
    multiplicity_pos := hmultiplicity
    rho := rho
    rho_eq := rfl
    requested := requested
    requested_eq := rfl
    rho_le_power := hrhoLePower
    half_power_lt := hhalfPower
  }⟩

end Kakeya.Assouad.PureWZ2

end
