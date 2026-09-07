module

/-
# Normalization Helpers for ExactEndgame V3

Standalone lemmas for projective coordinate normalization.
Extracted from ExactEndgameGeneralizedV2 Step 9.

## Helper lemmas

1. `rpow_scaling_bound`: monotonicity of negative rpow for scaling coefficients
2. `three_direction_coeffs`: construct b3, a3 from separated directions with lower bounds
3. `riesz_energy_rescaling`: combine scaling with projected energy bound
4. `coordinate_energy_combined`: full coordinate energy bound

## Whiteprint node
`normalization_helpers`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.ProductLikeIncidence.CoordinateNormalization
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Riesz energy scaling under pushforward by `c · id` on `ℝ`.
For `0 < c ≤ 1`, `I(c • μ) ≤ c^{-α} · I(μ)`. -/
lemma rieszEnergy_scaling_map {δ α : ℝ} (hδ_pos : 0 < δ) (hα_pos : 0 < α)
    {μ : Measure ℝ} [SFinite μ] {c : ℝ} (hc_pos : 0 < c) (hc_le_one : c ≤ 1) :
    robust_projection_main.rieszEnergy α hδ_pos (Measure.map (fun x : ℝ => c * x) μ) ≤
    ENNReal.ofReal (c ^ (-α)) * robust_projection_main.rieszEnergy α hδ_pos μ := by
  have hα_neg : -α < 0 := by linarith
  have h_cδ_pos : 0 < c * δ := mul_pos hc_pos hδ_pos
  have h_cδ_leδ : c * δ ≤ δ := by nlinarith
  have h_mono_floor : robust_projection_main.rieszEnergy α hδ_pos (Measure.map (fun x : ℝ => c * x) μ) ≤
      robust_projection_main.rieszEnergy α h_cδ_pos (Measure.map (fun x : ℝ => c * x) μ) := by
    dsimp only [robust_projection_main.rieszEnergy]
    apply lintegral_mono' (le_refl _)
    intro x
    apply lintegral_mono' (le_refl _)
    intro y
    have h4 : max (dist x y) δ ≥ max (dist x y) (c * δ) := by gcongr
    have h5 : 0 < max (dist x y) (c * δ) := by positivity
    have h6 : 0 < max (dist x y) δ := by positivity
    have h_strict_anti : StrictAntiOn (fun t : ℝ => t ^ (-α)) (Set.Ioi 0) :=
      Real.strictAntiOn_rpow_Ioi_of_exponent_neg hα_neg
    have h7 : (max (dist x y) δ) ^ (-α) ≤ (max (dist x y) (c * δ)) ^ (-α) := by
      by_cases h_eq : max (dist x y) δ = max (dist x y) (c * δ)
      · rw [h_eq]
      · have h_ne : max (dist x y) (c * δ) ≠ max (dist x y) δ := by
          intro h; exact h_eq h.symm
        have h_lt : max (dist x y) (c * δ) < max (dist x y) δ :=
          lt_of_le_of_ne h4 h_ne
        exact (h_strict_anti (by exact Set.mem_Ioi.mpr h5) (by exact Set.mem_Ioi.mpr h6) h_lt).le
    exact ENNReal.ofReal_le_ofReal h7
  have h_eq : robust_projection_main.rieszEnergy α h_cδ_pos (Measure.map (fun x : ℝ => c * x) μ) =
      ENNReal.ofReal (c ^ (-α)) * robust_projection_main.rieszEnergy α hδ_pos μ :=
    rieszEnergy_affine_scaling (hδ := hδ_pos) (c := c) hc_pos
      (fun x : ℝ => c * x) (by fun_prop)
      (fun x y => by
        rw [Real.dist_eq, Real.dist_eq]
        have h1 : c * x - c * y = c * (x - y) := by ring
        rw [h1, abs_mul, abs_of_pos hc_pos] <;> ring) μ
  calc
    robust_projection_main.rieszEnergy α hδ_pos (Measure.map (fun x : ℝ => c * x) μ)
      ≤ robust_projection_main.rieszEnergy α h_cδ_pos (Measure.map (fun x : ℝ => c * x) μ) := h_mono_floor
    _ = ENNReal.ofReal (c ^ (-α)) * robust_projection_main.rieszEnergy α hδ_pos μ := h_eq

/-- **Negative rpow scaling bound**: If `0 < r ≤ b ≤ 1` and `α > 0`,
then `b^(-α) ≤ r^(-α)`. -/
lemma rpow_scaling_bound {r b α : ℝ} (hr_pos : 0 < r) (hr_le_b : r ≤ b)
    (hb_le_one : b ≤ 1) (hα_pos : 0 < α) :
    b ^ (-α) ≤ r ^ (-α) := by
  have h_exp_neg : -α < 0 := by linarith
  have h_b_pos : 0 < b := by linarith
  have h_strict_anti : StrictAntiOn (fun t : ℝ => t ^ (-α)) (Set.Ioi 0) :=
    Real.strictAntiOn_rpow_Ioi_of_exponent_neg h_exp_neg
  have h_r_in : r ∈ Set.Ioi 0 := Set.mem_Ioi.mpr hr_pos
  have h_b_in : b ∈ Set.Ioi 0 := Set.mem_Ioi.mpr h_b_pos
  by_cases h_eq : b = r
  · rw [h_eq]
  · have h_lt : r < b := lt_of_le_of_ne hr_le_b (Ne.symm h_eq)
    exact (h_strict_anti h_r_in h_b_in h_lt).le

/-- **Three-direction normalization coefficients**: Given `θ1 < θ3 < θ2`
all in `[0,1]` with pairwise separation at least `r`, define
`b3 = (θ3-θ1)/(θ2-θ1)` and `a3 = (θ2-θ3)/(θ2-θ1)`.
Then `0 < b3, a3 ≤ 1` and `b3, a3 ≥ r`. -/
lemma three_direction_coeffs {θ1 θ2 θ3 r : ℝ}
    (hθ1_in : θ1 ∈ Set.Icc (0 : ℝ) 1)
    (hθ2_in : θ2 ∈ Set.Icc (0 : ℝ) 1)
    (hθ3_in : θ3 ∈ Set.Icc (0 : ℝ) 1)
    (h_ord13 : θ1 < θ3) (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ r)
    (h_sep23 : |θ2 - θ3| ≥ r)
    (hr_pos : 0 < r) (hr_le_one : r ≤ 1) :
    ∃ (b3 a3 : ℝ),
      b3 = (θ3 - θ1) / (θ2 - θ1) ∧
      a3 = (θ2 - θ3) / (θ2 - θ1) ∧
      0 < b3 ∧ b3 ≤ 1 ∧ b3 ≥ r ∧
      0 < a3 ∧ a3 ≤ 1 ∧ a3 ≥ r := by
  have hD_pos : 0 < θ2 - θ1 := by linarith
  have h31_pos : 0 < θ3 - θ1 := by linarith
  have h23_pos : 0 < θ2 - θ3 := by linarith
  have hD_le_one : θ2 - θ1 ≤ 1 := by linarith [hθ1_in.1, hθ2_in.2]
  let b3 : ℝ := (θ3 - θ1) / (θ2 - θ1)
  let a3 : ℝ := (θ2 - θ3) / (θ2 - θ1)
  have hb3_pos : 0 < b3 := by dsimp only [b3] <;> positivity
  have hb3_le_one : b3 ≤ 1 := by
    dsimp only [b3]
    have h : θ3 - θ1 ≤ θ2 - θ1 := by linarith
    exact (div_le_one hD_pos).mpr h
  have ha3_pos : 0 < a3 := by dsimp only [a3] <;> positivity
  have ha3_le_one : a3 ≤ 1 := by
    dsimp only [a3]
    have h : θ2 - θ3 ≤ θ2 - θ1 := by linarith
    exact (div_le_one hD_pos).mpr h
  have hb3_lower : b3 ≥ r := by
    dsimp only [b3]
    have h1 : θ3 - θ1 ≥ r := by
      have h2 : |θ3 - θ1| ≥ r := by
        have h3 : |θ1 - θ3| ≥ r := h_sep13
        have h4 : |θ3 - θ1| = |θ1 - θ3| := by exact abs_sub_comm θ3 θ1
        rw [h4]; exact h3
      rw [abs_of_pos h31_pos] at h2 <;> exact h2
    have h3 : (θ3 - θ1) / (θ2 - θ1) ≥ r / 1 := by gcongr
    simpa using h3
  have ha3_lower : a3 ≥ r := by
    dsimp only [a3]
    have h1 : θ2 - θ3 ≥ r := by
      have h2 : |θ2 - θ3| ≥ r := h_sep23
      rw [abs_of_pos h23_pos] at h2 <;> exact h2
    have h3 : (θ2 - θ3) / (θ2 - θ1) ≥ r / 1 := by gcongr
    simpa using h3
  exact ⟨b3, a3, rfl, rfl, hb3_pos, hb3_le_one, hb3_lower, ha3_pos, ha3_le_one, ha3_lower⟩

/-- **Riesz energy rescaling**: If `0 < c ≤ 1` and `I(μ) ≤ B`, then
`I(c • μ) ≤ c^(-α) · B`. -/
lemma riesz_energy_rescaling {δ α c : ℝ} (hδ_pos : 0 < δ) (hα_pos : 0 < α)
    (hc_pos : 0 < c) (hc_le_one : c ≤ 1)
    {μ : Measure ℝ} [SFinite μ] {B : ENNReal}
    (h_bound : robust_projection_main.rieszEnergy α hδ_pos μ ≤ B) :
    robust_projection_main.rieszEnergy α hδ_pos
      (Measure.map (fun x : ℝ => c * x) μ) ≤
    ENNReal.ofReal (c ^ (-α)) * B := by
  have h1 := rieszEnergy_scaling_map (μ := μ) hδ_pos hα_pos hc_pos hc_le_one
  calc
    robust_projection_main.rieszEnergy α hδ_pos (Measure.map (fun x : ℝ => c * x) μ)
      ≤ ENNReal.ofReal (c ^ (-α)) * robust_projection_main.rieszEnergy α hδ_pos μ := h1
    _ ≤ ENNReal.ofReal (c ^ (-α)) * B := by gcongr

/-- **Coordinate energy bound (combined)**: Given three separated directions
with normalization coefficients `b3, a3 ≥ r`, and absolute projected energy
bound `I(π_θ μE3) ≤ E_abs`, then the rescaled coordinate energies satisfy:
`I(b3 · π_θ2 μE3) ≤ r^(-2κ0) · E_abs` and similarly for `a3`. -/
lemma coordinate_energy_combined {δ κ0 r : ℝ} (hδ_pos : 0 < δ) (hκ0_pos : 0 < κ0)
    (hr_pos : 0 < r)
    {μE3 : Measure (EuclideanSpace ℝ (Fin 2))} [SFinite μE3]
    {θ1 θ2 θ3 b3 a3 : ℝ}
    (hb3_pos : 0 < b3) (hb3_le_one : b3 ≤ 1) (hb3_lower : b3 ≥ r)
    (ha3_pos : 0 < a3) (ha3_le_one : a3 ≤ 1) (ha3_lower : a3 ≥ r)
    {E_abs : ENNReal}
    (hE2_abs : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ2 + p 1) μE3) ≤ E_abs)
    (hE1_abs : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ1 + p 1) μE3) ≤ E_abs) :
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        b3 * (p 0 * θ2 + p 1)) μE3) ≤
    ENNReal.ofReal (r ^ (-(2 * κ0))) * E_abs ∧
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        a3 * (p 0 * θ1 + p 1)) μE3) ≤
    ENNReal.ofReal (r ^ (-(2 * κ0))) * E_abs := by
  have hb3_scaling : b3 ^ (-(2 * κ0)) ≤ r ^ (-(2 * κ0)) :=
    rpow_scaling_bound hr_pos hb3_lower hb3_le_one (by linarith)
  have ha3_scaling : a3 ^ (-(2 * κ0)) ≤ r ^ (-(2 * κ0)) :=
    rpow_scaling_bound hr_pos ha3_lower ha3_le_one (by linarith)
  let πθ2 := fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ2 + p 1
  let πθ1 := fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ1 + p 1
  have h_meas1 : Measurable (fun x : ℝ => b3 * x) := by fun_prop
  have h_meas2 : Measurable πθ2 := by fun_prop
  have hq0_eq : Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => b3 * (p 0 * θ2 + p 1)) μE3 =
      Measure.map (fun x : ℝ => b3 * x) (Measure.map πθ2 μE3) := by
    rw [Measure.map_map h_meas1 h_meas2] <;> congr <;> funext p <;> ring
  have h_meas3 : Measurable (fun x : ℝ => a3 * x) := by fun_prop
  have h_meas4 : Measurable πθ1 := by fun_prop
  have hq1_eq : Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => a3 * (p 0 * θ1 + p 1)) μE3 =
      Measure.map (fun x : ℝ => a3 * x) (Measure.map πθ1 μE3) := by
    rw [Measure.map_map h_meas3 h_meas4] <;> congr <;> funext p <;> ring
  have h1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun x : ℝ => b3 * x) (Measure.map πθ2 μE3)) ≤
      ENNReal.ofReal (b3 ^ (-(2 * κ0))) *
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map πθ2 μE3) :=
    rieszEnergy_scaling_map hδ_pos (by linarith) hb3_pos hb3_le_one
  have h2 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun x : ℝ => a3 * x) (Measure.map πθ1 μE3)) ≤
      ENNReal.ofReal (a3 ^ (-(2 * κ0))) *
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map πθ1 μE3) :=
    rieszEnergy_scaling_map hδ_pos (by linarith) ha3_pos ha3_le_one
  constructor
  · rw [hq0_eq]
    calc
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun x : ℝ => b3 * x) (Measure.map πθ2 μE3))
        ≤ ENNReal.ofReal (b3 ^ (-(2 * κ0))) *
            robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map πθ2 μE3) := h1
      _ ≤ ENNReal.ofReal (b3 ^ (-(2 * κ0))) * E_abs := by gcongr
      _ ≤ ENNReal.ofReal (r ^ (-(2 * κ0))) * E_abs := by
        gcongr <;> exact ENNReal.ofReal_le_ofReal hb3_scaling
  · rw [hq1_eq]
    calc
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun x : ℝ => a3 * x) (Measure.map πθ1 μE3))
        ≤ ENNReal.ofReal (a3 ^ (-(2 * κ0))) *
            robust_projection_main.rieszEnergy (2 * κ0) hδ_pos (Measure.map πθ1 μE3) := h2
      _ ≤ ENNReal.ofReal (a3 ^ (-(2 * κ0))) * E_abs := by gcongr
      _ ≤ ENNReal.ofReal (r ^ (-(2 * κ0))) * E_abs := by
        gcongr <;> exact ENNReal.ofReal_le_ofReal ha3_scaling

end ProductLikeIncidence.ProductReduction
