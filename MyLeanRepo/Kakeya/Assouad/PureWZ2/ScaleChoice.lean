import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Generalized scale choice for the pure WZ2 refinement

Given CWA at scale `delta` with `C = delta^(-inputEta)`, and an exponent `c`
with `inputEta ≤ c ≤ 1`, choose the requested scale `rho₀ = delta^c`.

The `within_factor` bound then gives `rho < C * delta^c = delta^(c - inputEta)`.
Since `c ≥ inputEta` and `0 < delta ≤ 1`, we have `delta^(c - inputEta) ≤ 1`,
so `rho ≤ 1`.  Moreover `rho ≥ delta^c ≥ delta`, giving `delta / rho ≤ 1`
and the scale-separation lower bound `delta^c ≤ rho`.

-/

noncomputable section

open Kakeya MeasureTheory

namespace Kakeya.Assouad

/--
Generalized scale+nearby production with exponent `c`.

Chooses `requested.1 = delta^c`.  Produces `nearby.rho` satisfying:
  - `nearby.rho ≤ 1`
  - `delta / nearby.rho ≤ 1`
  - `delta^c ≤ nearby.rho` (scale-separation lower bound)

Requires `0 < inputEta ≤ c ≤ 1` and `0 < delta ≤ 1`.
-/
lemma pure_wz2_scale_and_nearby_generalized
    {delta : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {inputEta c : ℝ}
    (hinput_eta_pos : 0 < inputEta)
    (hinput_eta_le_c : inputEta ≤ c)
    (hc_le_one : c ≤ 1)
    {C : ENNReal}
    (hC : C = Kakeya.realRpowENN delta (-inputEta))
    (hCWA : WZ2PaperPureCWAAtNearbyScales family C) :
    ∃ (requested : WZ2PaperRequestedScale delta)
      (nearby : WZ2PaperPureNearbyScaleCoverData family requested C),
      nearby.rho < Real.rpow delta (c - inputEta)
      ∧ nearby.rho ≤ 1
      ∧ delta / nearby.rho ≤ 1
      ∧ Real.rpow delta c ≤ nearby.rho
      ∧ 0 < nearby.rho := by
  have hc_pos : 0 < c := by linarith
  -- delta^c is a valid requested scale: delta ≤ delta^c ≤ 1
  have h1 : delta ≤ Real.rpow delta c := by
    have h : Real.rpow delta 1 ≤ Real.rpow delta c :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one hc_le_one
    simpa using h
  have h2 : Real.rpow delta c ≤ 1 := by
    apply Real.rpow_le_one hdelta_pos.le hdelta_le_one
    <;> linarith
  let requested : WZ2PaperRequestedScale delta :=
    ⟨Real.rpow delta c, h1, h2⟩
  -- Obtain nearby cover from CWA
  have h_main : ∀ (rho₀ : WZ2PaperRequestedScale delta),
      Nonempty (WZ2PaperPureNearbyScaleCoverData family rho₀ C) :=
    hCWA.2.2.2
  rcases h_main requested with ⟨nearby⟩
  have hrho_pos : 0 < nearby.rho := nearby.scaleData.rho_pos
  -- requested_le: delta^c ≤ nearby.rho
  have h_ge : Real.rpow delta c ≤ nearby.rho := nearby.requested_le
  -- delta / nearby.rho ≤ 1 since nearby.rho ≥ delta^c ≥ delta
  have h_ge_delta : delta ≤ nearby.rho := by
    calc delta ≤ Real.rpow delta c := h1
         _ ≤ nearby.rho := h_ge
  have h_div_le_one : delta / nearby.rho ≤ 1 := by
    apply (div_le_one hrho_pos).mpr
    exact h_ge_delta
  -- within_factor: ofReal nearby.rho < C * ofReal (delta^c)
  have h_factor : ENNReal.ofReal nearby.rho < C * ENNReal.ofReal (Real.rpow delta c) := by
    simpa [requested] using nearby.within_factor
  -- C * ofReal (delta^c) = ofReal (delta^(c - inputEta))
  have h_rhs : C * ENNReal.ofReal (Real.rpow delta c) =
      ENNReal.ofReal (Real.rpow delta (c - inputEta)) := by
    rw [hC]
    simp only [Kakeya.realRpowENN]
    have h_a : 0 ≤ Real.rpow delta (-inputEta) := Real.rpow_nonneg (by linarith) _
    have h_mul_eq : ENNReal.ofReal (Real.rpow delta (-inputEta) * Real.rpow delta c) =
        ENNReal.ofReal (Real.rpow delta (-inputEta)) * ENNReal.ofReal (Real.rpow delta c) :=
      ENNReal.ofReal_mul h_a
    have h_mul : ENNReal.ofReal (Real.rpow delta (-inputEta)) * ENNReal.ofReal (Real.rpow delta c) =
        ENNReal.ofReal (Real.rpow delta (-inputEta) * Real.rpow delta c) :=
      h_mul_eq.symm
    rw [h_mul]
    have h_rpow : Real.rpow delta (-inputEta) * Real.rpow delta c =
        Real.rpow delta (c - inputEta) := by
      have h_add : Real.rpow delta ((-inputEta) + c) =
          Real.rpow delta (-inputEta) * Real.rpow delta c :=
        Real.rpow_add hdelta_pos (-inputEta) c
      have h_comm : (-inputEta) + c = c - inputEta := by ring
      rw [h_comm] at h_add
      exact h_add.symm
    rw [h_rpow]
  have h_lt : ENNReal.ofReal nearby.rho <
      ENNReal.ofReal (Real.rpow delta (c - inputEta)) :=
    lt_of_lt_of_eq h_factor h_rhs
  -- delta^(c - inputEta) ≤ 1 since c - inputEta ≥ 0 and 0 < delta ≤ 1
  have h_exp_nonneg : 0 ≤ c - inputEta := by linarith
  have h_rpow_le_one : Real.rpow delta (c - inputEta) ≤ 1 := by
    apply Real.rpow_le_one hdelta_pos.le hdelta_le_one h_exp_nonneg
  -- nearby.rho < 1
  have h_lt_one : nearby.rho < 1 := by
    have h11 : ENNReal.ofReal nearby.rho < ENNReal.ofReal 1 := by
      calc ENNReal.ofReal nearby.rho
        < ENNReal.ofReal (Real.rpow delta (c - inputEta)) := h_lt
      _ ≤ ENNReal.ofReal 1 := by gcongr
    have h12 : 0 ≤ nearby.rho := by linarith
    simpa [ENNReal.ofReal_lt_ofReal_iff] using h11
  have h_rho_upper :
      nearby.rho < Real.rpow delta (c - inputEta) := by
    have hnonneg : 0 ≤ nearby.rho := hrho_pos.le
    have hrpowPos :
        0 < Real.rpow delta (c - inputEta) :=
      Real.rpow_pos_of_pos hdelta_pos _
    exact
      (ENNReal.ofReal_lt_ofReal_iff hrpowPos).mp h_lt
  exact
    ⟨requested, nearby, h_rho_upper, by linarith,
      h_div_le_one, h_ge, hrho_pos⟩

end Kakeya.Assouad

end
