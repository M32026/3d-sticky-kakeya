module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics

@[expose] public section

/-!
# Grid and line residual scaling lemmas

This module proves two elementary scaling facts used in the product-structure
rescaling theorem:

1. `grid_scaling`: multiplying a fine `δ = Δ²` grid point by `Δ⁻¹` lands in
   the coarse `Δ` grid.
2. `lineResidual_scaling`: the line residual transforms by a factor of `Δ⁻¹`
   when the parameter is scaled and the point is horizontally unscaled.

Whiteprint node: `grid_residual_scaling`.
-/

noncomputable section

open scoped ENNReal NNReal

/--
Scaling a fine-grid parameter `p` by `Δ⁻¹` maps it to the coarse grid.
If `p ∈ parameterGrid δ` with `δ = Δ²`, then `Δ⁻¹ • p ∈ parameterGrid Δ`.
-/
lemma grid_scaling {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : δ = Δ ^ 2)
    (p : EuclideanPlane) (hp_grid : p ∈ parameterGrid δ) :
    (Δ⁻¹ : ℝ) • p ∈ parameterGrid Δ := by
  have h0 : p 0 ∈ integerGrid δ := hp_grid.1
  have h1 : p 1 ∈ integerGrid δ := hp_grid.2
  rcases h0 with ⟨k0, hk0⟩
  rcases h1 with ⟨k1, hk1⟩
  have hq0_eq : ((Δ⁻¹ : ℝ) • p) 0 = Δ * (k0 : ℝ) := by
    have h_smul : ((Δ⁻¹ : ℝ) • p) 0 = Δ⁻¹ * (p 0) := by simp
    rw [h_smul, hk0, hδ]
    field_simp [hΔ.ne'] <;> ring
  have hq1_eq : ((Δ⁻¹ : ℝ) • p) 1 = Δ * (k1 : ℝ) := by
    have h_smul : ((Δ⁻¹ : ℝ) • p) 1 = Δ⁻¹ * (p 1) := by simp
    rw [h_smul, hk1, hδ]
    field_simp [hΔ.ne'] <;> ring
  have hq0 : ((Δ⁻¹ : ℝ) • p) 0 ∈ integerGrid Δ := ⟨k0, hq0_eq⟩
  have hq1 : ((Δ⁻¹ : ℝ) • p) 1 ∈ integerGrid Δ := ⟨k1, hq1_eq⟩
  exact ⟨hq0, hq1⟩

/--
The line residual transforms by `Δ⁻¹` under simultaneous horizontal un-scaling
of the point and scaling of the parameter.
-/
lemma lineResidual_scaling {z θ : EuclideanPlane} {Δ : ℝ} (hΔ : 0 < Δ) :
    lineResidual z ((Δ⁻¹ : ℝ) • θ) =
      Δ⁻¹ * lineResidual (unscaleHorizontal Δ z) θ := by
  have huz0 : (unscaleHorizontal Δ z) 0 = Δ * z 0 := by
    simp [unscaleHorizontal, EuclideanSpace.equiv] <;> aesop
  have huz1 : (unscaleHorizontal Δ z) 1 = z 1 := by
    simp [unscaleHorizontal, EuclideanSpace.equiv] <;> aesop
  have hθ0 : ((Δ⁻¹ : ℝ) • θ) 0 = Δ⁻¹ * θ 0 := by simp
  have hθ1 : ((Δ⁻¹ : ℝ) • θ) 1 = Δ⁻¹ * θ 1 := by simp
  rw [lineResidual, lineResidual, huz0, huz1, hθ0, hθ1]
  have h_eq : z 0 - (Δ⁻¹ * θ 0 * z 1 + Δ⁻¹ * θ 1) =
      Δ⁻¹ * (Δ * z 0 - (θ 0 * z 1 + θ 1)) := by
    field_simp [hΔ.ne'] <;> ring
  rw [h_eq, abs_mul, abs_of_pos (inv_pos.mpr hΔ)]
  <;> ring

/--
Corollary: if the fine residual is bounded by `3 * δ` with `δ = Δ²`,
then the scaled residual is bounded by `3 * Δ`.
-/
lemma lineResidual_scaling_bound {z θ : EuclideanPlane} {Δ δ : ℝ}
    (hΔ : 0 < Δ) (hδ : δ = Δ ^ 2)
    (h : lineResidual (unscaleHorizontal Δ z) θ ≤ 3 * δ) :
    lineResidual z ((Δ⁻¹ : ℝ) • θ) ≤ 3 * Δ := by
  rw [lineResidual_scaling hΔ]
  have h2 : Δ⁻¹ * lineResidual (unscaleHorizontal Δ z) θ ≤ Δ⁻¹ * (3 * δ) := by
    exact mul_le_mul_of_nonneg_left h (by positivity)
  rw [hδ] at h2
  have h3 : Δ⁻¹ * (3 * Δ ^ 2) = 3 * Δ := by
    field_simp [hΔ.ne'] <;> ring
  rw [h3] at h2
  exact h2

/--
Generalized: if the fine residual is bounded by `K * δ` with `δ = Δ²`,
then the scaled residual is bounded by `K * Δ`.
-/
lemma lineResidual_scaling_bound_general {z θ : EuclideanPlane} {Δ δ K : ℝ}
    (hΔ : 0 < Δ) (hδ : δ = Δ ^ 2)
    (h : lineResidual (unscaleHorizontal Δ z) θ ≤ K * δ) :
    lineResidual z ((Δ⁻¹ : ℝ) • θ) ≤ K * Δ := by
  rw [lineResidual_scaling hΔ]
  have h2 : Δ⁻¹ * lineResidual (unscaleHorizontal Δ z) θ ≤ Δ⁻¹ * (K * δ) := by
    exact mul_le_mul_of_nonneg_left h (by positivity)
  rw [hδ] at h2
  have h3 : Δ⁻¹ * (K * Δ ^ 2) = K * Δ := by
    field_simp [hΔ.ne'] <;> ring
  rw [h3] at h2
  exact h2

end
