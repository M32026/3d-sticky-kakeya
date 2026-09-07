module

/-
  Scale transfer mass bound for the bridge.

  Proves: Ncover(δ_n, P_oriented) ≥ δ_n^{ρ_mass} * Ncover(δ_n, P)
  given:
  - Ncover(δ, P_oriented) ≥ c_slope * Ncover(δ, P)  (from slope partition)
  - δ/2 < δ_n ≤ δ
  - c_slope / 9 ≥ δ_n^{ρ_mass}  (small-δ absorption)

  Uses:
  - externalCoveringNumber_anti: finer scale → larger Ncover
  - externalCoveringNumber_half_le_plane: Ncover(δ/2, P) ≤ 9 * Ncover(δ, P)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate

abbrev Ncover' {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  (Metric.externalCoveringNumber δ.toNNReal E : ENNReal)

/-- Scale transfer mass bound. -/
lemma mass_scale_transfer
    {δ δ_n : ℝ} (hδ_pos : 0 < δ) (hδn_pos : 0 < δ_n)
    (hδn_leδ : δ_n ≤ δ) (hδ_lt2δn : δ < 2 * δ_n)
    (P P_oriented : Set Plane)
    (c_slope : ℝ) (hc_slope_pos : 0 < c_slope)
    (h_retention : Ncover' δ P_oriented ≥ ENNReal.ofReal c_slope * Ncover' δ P)
    (ρ_mass : ℝ) (hρ_mass_nonneg : 0 ≤ ρ_mass)
    (h_absorb : ENNReal.ofReal (δ_n ^ ρ_mass) ≤ ENNReal.ofReal (c_slope / 9)) :
    Ncover' δ_n P_oriented ≥ ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P := by
  have hδn_toNNReal_le : δ_n.toNNReal ≤ δ.toNNReal := by
    exact Real.toNNReal_mono hδn_leδ
  have hhalf_toNNReal_le : (δ / 2).toNNReal ≤ δ_n.toNNReal := by
    have h : δ / 2 ≤ δ_n := by linarith
    exact Real.toNNReal_mono h
  -- Anti-monotonicity
  have h1 : Ncover' δ P_oriented ≤ Ncover' δ_n P_oriented := by
    have h := Metric.externalCoveringNumber_anti hδn_toNNReal_le (A := P_oriented)
    exact_mod_cast h
  -- Doubling: Ncover(δ_n, P) ≤ Ncover(δ/2, P) ≤ 9 * Ncover(δ, P)
  have h23 : Ncover' δ_n P ≤ Ncover' (δ / 2) P := by
    have h := Metric.externalCoveringNumber_anti hhalf_toNNReal_le (A := P)
    exact_mod_cast h
  have hhalf_eq : (δ / 2).toNNReal = δ.toNNReal / 2 := by
    apply NNReal.coe_injective
    have hpos1 : 0 ≤ δ / 2 := by linarith
    have hpos2 : 0 ≤ δ := by linarith
    simp [Real.toNNReal_of_nonneg hpos1, Real.toNNReal_of_nonneg hpos2]
    <;> ring
  have h24 : Ncover' (δ / 2) P ≤ (9 : ENNReal) * Ncover' δ P := by
    have h25 : Ncover' (δ / 2) P = (Metric.externalCoveringNumber (δ.toNNReal / 2) P : ENNReal) := by
      simp [Ncover', hhalf_eq]
      <;> rfl
    rw [h25]
    have h := RobustKaufmanProjection.externalCoveringNumber_half_le_plane P δ.toNNReal
    have h' : (Metric.externalCoveringNumber (δ.toNNReal / 2) P : ENNReal) ≤
        (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      exact_mod_cast h
    simpa [Ncover'] using h'
  have h2 : Ncover' δ_n P ≤ (9 : ENNReal) * Ncover' δ P :=
    le_trans h23 h24
  -- Retention at finer scale
  have h3 : Ncover' δ_n P_oriented ≥ ENNReal.ofReal c_slope * Ncover' δ P :=
    le_trans h_retention h1
  -- Key inequality: (c_slope/9) * Ncover(δ_n, P) ≤ c_slope * Ncover(δ, P)
  have h4 : ENNReal.ofReal (c_slope / 9) * Ncover' δ_n P ≤
      ENNReal.ofReal c_slope * Ncover' δ P := by
    have h5 : ENNReal.ofReal (c_slope / 9) * Ncover' δ_n P ≤
        ENNReal.ofReal (c_slope / 9) * ((9 : ENNReal) * Ncover' δ P) := by
      gcongr
    have h6 : ENNReal.ofReal (c_slope / 9) * ((9 : ENNReal) * Ncover' δ P) =
        ENNReal.ofReal c_slope * Ncover' δ P := by
      have h7 : ENNReal.ofReal (c_slope / 9) * (9 : ENNReal) = ENNReal.ofReal c_slope := by
        have h8 : ENNReal.ofReal (c_slope / 9) * ENNReal.ofReal (9 : ℝ) = ENNReal.ofReal ((c_slope / 9) * 9) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [show (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) from by norm_cast] at *
        rw [h8]
        have h9 : (c_slope / 9) * 9 = c_slope := by ring
        rw [h9]
      have h6 : ENNReal.ofReal (c_slope / 9) * ((9 : ENNReal) * Ncover' δ P) =
          (ENNReal.ofReal (c_slope / 9) * (9 : ENNReal)) * Ncover' δ P := by
        ring
      rw [h6, h7]
    rw [h6] at h5
    exact h5
  have h_main : Ncover' δ_n P_oriented ≥ ENNReal.ofReal (c_slope / 9) * Ncover' δ_n P :=
    le_trans h4 h3
  -- Apply absorption
  calc Ncover' δ_n P_oriented
    ≥ ENNReal.ofReal (c_slope / 9) * Ncover' δ_n P := h_main
  _ ≥ ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P := by
    gcongr

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
