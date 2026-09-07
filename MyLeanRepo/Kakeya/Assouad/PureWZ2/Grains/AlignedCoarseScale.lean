import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import Mathlib.Tactic

/-!
# Integer-aligned coarse scales for one-scale local AD

The Property-P fine pullback is cubical at the original fine scale only when
the coarse scale is an integer multiple of that fine scale.  For a query
scale `rho`, we round `sqrt (rho / 48)` upward to the next such multiple.

The hypotheses below isolate the harmless small-scale condition needed to
control the rounding error.  In particular, the selected scale is comparable
to `sqrt rho` from both sides; no sticky-provision range is assumed here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Integer multiplier used to align the Córdoba coarse scale to the fine
`delta` grid. -/
def alignedCoarseMultiplicity (delta rho : ℝ) : ℕ :=
  Nat.ceil (Real.sqrt (rho / 48) / delta)

/-- The aligned coarse scale `K * delta`. -/
def alignedCoarseScale (delta rho : ℝ) : ℝ :=
  (alignedCoarseMultiplicity delta rho : ℝ) * delta

lemma alignedCoarseMultiplicity_pos
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho) :
    0 < alignedCoarseMultiplicity delta rho := by
  apply Nat.ceil_pos.mpr
  exact div_pos (Real.sqrt_pos.mpr (by positivity)) hdelta_pos

lemma alignedCoarseScale_pos
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho) :
    0 < alignedCoarseScale delta rho := by
  exact mul_pos (by exact_mod_cast alignedCoarseMultiplicity_pos hdelta_pos hrho_pos)
    hdelta_pos

/-- The aligned scale is at least the original fine scale. -/
lemma delta_le_alignedCoarseScale
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho) :
    delta ≤ alignedCoarseScale delta rho := by
  have hK : 1 ≤ alignedCoarseMultiplicity delta rho :=
    alignedCoarseMultiplicity_pos hdelta_pos hrho_pos
  dsimp only [alignedCoarseScale]
  have hKreal : (1 : ℝ) ≤ alignedCoarseMultiplicity delta rho := by
    exact_mod_cast hK
  nlinarith

/-- Rounding upward gives the containment-side critical-scale inequality. -/
lemma query_le_fortyEight_mul_alignedCoarseScale_sq
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho) :
    rho ≤ 48 * alignedCoarseScale delta rho ^ 2 := by
  let x : ℝ := Real.sqrt (rho / 48)
  let K : ℕ := alignedCoarseMultiplicity delta rho
  have hx_pos : 0 < x :=
    Real.sqrt_pos.mpr (div_pos hrho_pos (by norm_num))
  have hceil : x / delta ≤ (K : ℝ) := by
    dsimp only [K, alignedCoarseMultiplicity]
    exact Nat.le_ceil _
  have hx_le : x ≤ (K : ℝ) * delta := by
    have := mul_le_mul_of_nonneg_right hceil hdelta_pos.le
    field_simp [hdelta_pos.ne'] at this
    simpa [mul_comm] using this
  have hx_sq : x ^ 2 = rho / 48 := by
    dsimp only [x]
    rw [Real.sq_sqrt] <;> positivity
  have hsq : x ^ 2 ≤ ((K : ℝ) * delta) ^ 2 := by nlinarith
  dsimp only [alignedCoarseScale]
  change rho ≤ 48 * ((K : ℝ) * delta) ^ 2
  rw [hx_sq] at hsq
  nlinarith

/-- If the fine scale is below the unrounded target, the upward rounding loses
less than a factor two. -/
lemma alignedCoarseScale_lt_two_mul_sqrt
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho)
    (hround : delta ≤ Real.sqrt (rho / 48)) :
    alignedCoarseScale delta rho < 2 * Real.sqrt (rho / 48) := by
  let x : ℝ := Real.sqrt (rho / 48)
  let K : ℕ := alignedCoarseMultiplicity delta rho
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hceil : (K : ℝ) < x / delta + 1 := by
    dsimp only [K, alignedCoarseMultiplicity]
    exact Nat.ceil_lt_add_one (div_nonneg hx_nonneg hdelta_pos.le)
  have hscaled : (K : ℝ) * delta < (x / delta + 1) * delta :=
    mul_lt_mul_of_pos_right hceil hdelta_pos
  have hsimp : (x / delta + 1) * delta = x + delta := by
    field_simp [hdelta_pos.ne']
  rw [hsimp] at hscaled
  have hdelta_le_x : delta ≤ x := by simpa [x] using hround
  dsimp only [alignedCoarseScale]
  change (K : ℝ) * delta < 2 * x
  linarith

/-- A convenient sufficient condition for the rounding hypothesis. -/
lemma delta_le_sqrt_query_div_fortyEight
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho)
    (hscale : 48 * delta ^ 2 ≤ rho) :
    delta ≤ Real.sqrt (rho / 48) := by
  have hdiv : delta ^ 2 ≤ rho / 48 := by nlinarith
  have hsqrt : Real.sqrt (delta ^ 2) ≤ Real.sqrt (rho / 48) :=
    Real.sqrt_le_sqrt hdiv
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta_pos] at hsqrt
  exact hsqrt

/-- The aligned scale is quantitatively comparable to the query scale. -/
lemma fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho)
    (hscale : 48 * delta ^ 2 ≤ rho) :
    48 * alignedCoarseScale delta rho ^ 2 < 4 * rho := by
  have hround : delta ≤ Real.sqrt (rho / 48) :=
    delta_le_sqrt_query_div_fortyEight hdelta_pos hrho_pos hscale
  have hlt : alignedCoarseScale delta rho <
      2 * Real.sqrt (rho / 48) :=
    alignedCoarseScale_lt_two_mul_sqrt hdelta_pos hrho_pos hround
  have hpos : 0 < alignedCoarseScale delta rho :=
    alignedCoarseScale_pos hdelta_pos hrho_pos
  have hsqrt_sq : (Real.sqrt (rho / 48)) ^ 2 = rho / 48 := by
    rw [Real.sq_sqrt] <;> positivity
  nlinarith

/-- Rounding upward really puts the square-root target below the aligned
scale.  This is the lower half of the comparison used when the target query
is `48 * delta`. -/
lemma sqrt_div_fortyEight_le_alignedCoarseScale
    {delta rho : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho) :
    Real.sqrt (rho / 48) ≤ alignedCoarseScale delta rho := by
  let x : ℝ := Real.sqrt (rho / 48)
  let K : ℕ := alignedCoarseMultiplicity delta rho
  have hceil : x / delta ≤ (K : ℝ) := by
    dsimp only [K, alignedCoarseMultiplicity, x]
    exact Nat.le_ceil _
  have hscaled := mul_le_mul_of_nonneg_right hceil hdelta_pos.le
  have hx : x ≤ (K : ℝ) * delta := by
    field_simp [hdelta_pos.ne'] at hscaled
    simpa [mul_comm] using hscaled
  simpa only [x, K, alignedCoarseScale] using hx

/-- A loss-only threshold paying the one-grid-step error when the upper
power-window endpoint is rounded to an integer multiple of the root scale. -/
structure Proposition63AlignedPowerWindowCutoffData
    (windowLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
    2 * Real.sqrt delta ≤ Real.rpow delta windowLoss

/-- Freeze the power-window rounding loss before the critical sequence chooses
`delta`. -/
theorem proposition63_aligned_power_window_cutoff
    (windowLoss : ℝ)
    (hwindow_pos : 0 < windowLoss)
    (hwindow_half : windowLoss < 1 / 2) :
    Nonempty (Proposition63AlignedPowerWindowCutoffData windowLoss) := by
  rcases exists_delta_mul_rpow_le_rpow (2 : ℝ) (by norm_num)
      hwindow_half with
    ⟨delta₀, delta₀_pos, delta₀_le_one, absorb⟩
  exact ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀_pos
    delta₀_le_one := delta₀_le_one
    absorb := by
      intro delta delta_pos delta_le
      calc
        2 * Real.sqrt delta =
            2 * Real.rpow delta (1 / 2 : ℝ) := by
              exact congrArg (fun value : ℝ => 2 * value)
                (Real.sqrt_eq_rpow delta)
        _ ≤ Real.rpow delta windowLoss := absorb delta delta_pos delta_le
  }⟩

/-- An integer-aligned requested scale in the Node-3 power window.  It is
obtained by rounding `delta^windowLoss / 2` upward on the `delta` grid. -/
structure Proposition63AlignedPowerRequestedScaleData
    (delta windowLoss : ℝ) where
  requested : WZ2PaperRequestedScale delta
  scaleFactor : ℕ
  scaleFactor_pos : 0 < scaleFactor
  requested_aligned :
    requested.1 = (scaleFactor : ℝ) * delta
  lower_window :
    Real.rpow delta (1 - windowLoss) ≤ requested.1
  upper_window :
    requested.1 ≤ Real.rpow delta windowLoss
  half_upper_le :
    Real.rpow delta windowLoss / 2 ≤ requested.1

/-- Materialize the aligned upper-window request after the runtime root scale
is known, using only the loss-only cutoff selected beforehand. -/
theorem Proposition63AlignedPowerWindowCutoffData.requestedScale
    {windowLoss delta : ℝ}
    (cutoff : Proposition63AlignedPowerWindowCutoffData windowLoss)
    (hwindow_pos : 0 < windowLoss)
    (hwindow_half : windowLoss < 1 / 2)
    (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ cutoff.delta₀) :
    Nonempty (Proposition63AlignedPowerRequestedScaleData delta windowLoss) := by
  have hdelta_one : delta ≤ 1 := hdelta_le.trans cutoff.delta₀_le_one
  let target : ℝ := Real.rpow delta windowLoss / 2
  have htarget_pos : 0 < target := by
    dsimp only [target]
    exact div_pos (Real.rpow_pos_of_pos hdelta_pos windowLoss) (by norm_num)
  have hdelta_sqrt : delta ≤ Real.sqrt delta := by
    have hsqrt_sq : (Real.sqrt delta) ^ 2 = delta :=
      Real.sq_sqrt hdelta_pos.le
    have hsqrt_nonnegative := Real.sqrt_nonneg delta
    nlinarith
  have hdelta_target : delta ≤ target := by
    dsimp only [target]
    have absorbed := cutoff.absorb hdelta_pos hdelta_le
    linarith
  let query : ℝ := 48 * target ^ 2
  have hquery_pos : 0 < query := by
    dsimp only [query]
    positivity
  have hgrid : 48 * delta ^ 2 ≤ query := by
    dsimp only [query]
    nlinarith [sq_nonneg (target - delta)]
  let scale : ℝ := alignedCoarseScale delta query
  have hscale_pos : 0 < scale :=
    alignedCoarseScale_pos hdelta_pos hquery_pos
  have hdelta_scale : delta ≤ scale :=
    delta_le_alignedCoarseScale hdelta_pos hquery_pos
  have hsqrt_target : Real.sqrt (query / 48) = target := by
    have query_div : query / 48 = target ^ 2 := by
      dsimp only [query]
      ring
    rw [query_div, Real.sqrt_sq htarget_pos.le]
  have htarget_le : target ≤ scale := by
    rw [← hsqrt_target]
    exact sqrt_div_fortyEight_le_alignedCoarseScale hdelta_pos hquery_pos
  have hscale_lt : scale < 2 * target := by
    have hround := alignedCoarseScale_lt_two_mul_sqrt hdelta_pos hquery_pos
      (delta_le_sqrt_query_div_fortyEight hdelta_pos hquery_pos hgrid)
    rwa [hsqrt_target] at hround
  have hlower_target : Real.rpow delta (1 - windowLoss) ≤ target := by
    have lower_sqrt : Real.rpow delta (1 - windowLoss) ≤
        Real.sqrt delta := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
        (by linarith)
    have sqrt_target : Real.sqrt delta ≤ target := by
      dsimp only [target]
      linarith [cutoff.absorb hdelta_pos hdelta_le]
    exact lower_sqrt.trans sqrt_target
  have hupper : scale ≤ Real.rpow delta windowLoss :=
    hscale_lt.le.trans <| by
      dsimp only [target]
      linarith
  let requested : WZ2PaperRequestedScale delta :=
    ⟨scale, hdelta_scale, hupper.trans <|
      Real.rpow_le_one hdelta_pos.le hdelta_one hwindow_pos.le⟩
  exact ⟨{
    requested := requested
    scaleFactor := alignedCoarseMultiplicity delta query
    scaleFactor_pos := alignedCoarseMultiplicity_pos hdelta_pos hquery_pos
    requested_aligned := rfl
    lower_window := hlower_target.trans htarget_le
    upper_window := hupper
    half_upper_le := htarget_le
  }⟩

/-- Rounding a requested power scale upward is harmless for the inverse-cube
budget in the critical Córdoba estimate.  This is the paper-faithful
replacement for the unnecessarily exact identity
`L = delta ^ stickyLoss`. -/
lemma aligned_scale_inv_cube_bound
    {delta L stickyLoss outputLoss : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta < 1)
    (hL : Real.rpow delta stickyLoss ≤ L)
    (hbudget : 3 * stickyLoss ≤ outputLoss) :
    Real.rpow L (-3 : ℝ) ≤
      Real.rpow delta (-outputLoss) := by
  have hrequestedPositive :
      0 < Real.rpow delta stickyLoss :=
    Real.rpow_pos_of_pos hdelta _
  have hLPositive : 0 < L := hrequestedPositive.trans_le hL
  have hrounding :
      Real.rpow L (-3 : ℝ) ≤
        Real.rpow (Real.rpow delta stickyLoss) (-3 : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos hrequestedPositive hL (by norm_num)
  have hpower :
      Real.rpow (Real.rpow delta stickyLoss) (-3 : ℝ) =
        Real.rpow delta (-3 * stickyLoss) := by
    calc
      Real.rpow (Real.rpow delta stickyLoss) (-3 : ℝ) =
          Real.rpow delta (stickyLoss * (-3 : ℝ)) :=
        (Real.rpow_mul hdelta.le stickyLoss (-3 : ℝ)).symm
      _ = Real.rpow delta (-3 * stickyLoss) := by ring_nf
  have hexponent : -outputLoss ≤ -3 * stickyLoss := by linarith
  calc
    Real.rpow L (-3 : ℝ) ≤
        Real.rpow (Real.rpow delta stickyLoss) (-3 : ℝ) := hrounding
    _ = Real.rpow delta (-3 * stickyLoss) := hpower
    _ ≤ Real.rpow delta (-outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne.le hexponent

end Kakeya.Assouad.PureWZ2

end
