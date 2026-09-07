import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.WZ1.RpowHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.SourceDeltaLeRhoSquared

/-!
# The distinguished power scale in Proposition 6.3

This is the exact scale choice from `wz2_63.tex`, lines 78--88.  It is kept
separate from integer-aligned auxiliary scales: the paper's metric-fibre
rescaling uses the exact identity `h^(sigma/2) = Delta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The exact distinguished scale `Delta` and rescaled fine radius `h`. -/
structure Proposition63PowerScale (tau sigma : ℝ) where
  Delta : ℝ
  Delta_eq : Delta = Real.rpow tau (sigma / (2 + sigma))
  requested : WZ2PaperRequestedScale tau
  requested_eq : requested.1 = Delta
  h : ℝ
  h_eq : h = tau / Delta
  h_pos : 0 < h
  h_le_one : h ≤ 1
  tau_le_Delta_sq : tau ≤ Delta ^ 2
  scale_identity : Real.rpow h (sigma / 2) = Delta

/-- Construct the exact power-scale data used before selecting a metric
fibre in Proposition 6.3. -/
theorem proposition63_power_scale
    {tau sigma : ℝ}
    (htau : 0 < tau)
    (htauOne : tau < 1)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63PowerScale tau sigma) := by
  let Delta : ℝ := Real.rpow tau (sigma / (2 + sigma))
  have hDeltaPos : 0 < Delta := by
    exact Real.rpow_pos_of_pos htau _
  have hExponentPos : 0 < sigma / (2 + sigma) := by positivity
  have hExponentOne : sigma / (2 + sigma) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  have htauDelta : tau ≤ Delta := by
    have hpower := Real.rpow_le_rpow_of_exponent_ge
      htau htauOne.le hExponentOne
    simpa [Delta] using hpower
  have hDeltaOne : Delta ≤ 1 := by
    exact Real.rpow_le_one htau.le htauOne.le hExponentPos.le
  let requested : WZ2PaperRequestedScale tau :=
    ⟨Delta, htauDelta, hDeltaOne⟩
  let h : ℝ := tau / Delta
  have hhPos : 0 < h := div_pos htau hDeltaPos
  have hhOne : h ≤ 1 := (div_le_one hDeltaPos).2 htauDelta
  have htauDeltaSq : tau ≤ Delta ^ 2 := by
    exact sourceDelta_le_rho_squared hsigma hsigmaOne htau htauOne
      (by rfl)
  have hidentity : Real.rpow h (sigma / 2) = Delta := by
    exact sourceDelta_div_rho_rpow_half hsigma htau (by rfl)
  exact ⟨{
    Delta := Delta
    Delta_eq := rfl
    requested := requested
    requested_eq := rfl
    h := h
    h_eq := rfl
    h_pos := hhPos
    h_le_one := hhOne
    tau_le_Delta_sq := htauDeltaSq
    scale_identity := hidentity
  }⟩

/-- Express a power of the outer root scale through the exact rescaled
ratio `h = tau / Delta`.  The distinguished identity
`Delta = h^(sigma/2)` gives `tau = h^(1 + sigma/2)`. -/
theorem Proposition63PowerScale.root_power_eq_ratio_power
    {tau sigma exponent : ℝ}
    (power : Proposition63PowerScale tau sigma) :
    Kakeya.realRpowENN tau exponent =
      Kakeya.realRpowENN power.h ((1 + sigma / 2) * exponent) := by
  have hDelta : 0 < power.Delta := by
    rw [← power.scale_identity]
    exact Real.rpow_pos_of_pos power.h_pos _
  have htau : tau = power.h * power.Delta := by
    rw [power.h_eq]
    field_simp [hDelta.ne']
  have htauRpow : tau = Real.rpow power.h (1 + sigma / 2) := by
    calc
      tau = power.h * power.Delta := htau
      _ = Real.rpow power.h 1 *
            Real.rpow power.h (sigma / 2) := by
        rw [power.scale_identity]
        congr 1
        exact (Real.rpow_one power.h).symm
      _ = Real.rpow power.h (1 + sigma / 2) := by
        exact (Real.rpow_add power.h_pos 1 (sigma / 2)).symm
  unfold Kakeya.realRpowENN
  congr 1
  calc
    Real.rpow tau exponent =
        Real.rpow (Real.rpow power.h (1 + sigma / 2)) exponent := by
      rw [← htauRpow]
    _ = Real.rpow power.h ((1 + sigma / 2) * exponent) :=
      (Real.rpow_mul power.h_pos.le _ _).symm

end Kakeya.Assouad.PureWZ2

end
