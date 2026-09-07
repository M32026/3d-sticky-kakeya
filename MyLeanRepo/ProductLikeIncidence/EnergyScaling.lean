module

/-
# Riesz Energy Scaling for Normalization Map

Wrapper around `cobalt_rieszEnergy_affine_scaling` for the normalization map
`normalizeMap R L x = (x + R) / L`.

## Key identity

`rieszEnergy α (δ/L) (map (normalizeMap R L ∘ h) μ) = L^α * rieszEnergy α δ (map h μ)`

## Whiteprint node
`riesz_energy_normalization_scaling`
-/

public import MyLeanRepo.ProductLikeIncidence.Obligation3ProjectiveTransform
public import MyLeanRepo.ProductLikeIncidence.CoordinateNormalization
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Riesz energy scales by `L^α` under the normalization map `(x + R)/L`.

Since `normalizeMap R L` scales all distances by `1/L`, the energy at scale `δ/L`
of the normalized measure equals `L^α` times the energy at scale `δ` of the
original measure. -/
lemma rieszEnergy_normalizeMap_scaling
    {α : ℝ} {δ : ℝ} (hδ : 0 < δ)
    {R L : ℝ} (hL_pos : 0 < L)
    {X : Type*} [MeasurableSpace X]
    {h : X → ℝ} (hh_meas : Measurable h)
    {μ : Measure X} [SFinite μ] :
    robust_projection.rieszEnergy α (show 0 < δ / L from div_pos hδ hL_pos)
      (Measure.map (normalizeMap R L ∘ h) μ) =
    ENNReal.ofReal (L ^ α) * robust_projection.rieszEnergy α hδ (Measure.map h μ) := by
  let T : ℝ → ℝ := normalizeMap R L
  have hT_cont : Continuous T := by
    have h : Continuous (fun x : ℝ => (x + R) / L) := by
      continuity
    exact h
  have hT_meas : Measurable T := hT_cont.measurable
  have hT_dist : ∀ (x y : ℝ), dist (T x) (T y) = (1 / L) * dist x y := by
    intro x y
    simp only [T, normalizeMap, dist_eq_norm]
    have h : |(x + R) / L - (y + R) / L| = (1 / L) * |x - y| := by
      have h2 : (x + R) / L - (y + R) / L = (x - y) / L := by
        field_simp [hL_pos.ne'] <;> ring
      rw [h2, abs_div, abs_of_pos hL_pos] <;> ring
    exact h
  have hc_pos : 0 < (1 / L : ℝ) := by positivity
  have h_scale_eq : (1 / L : ℝ) * δ = δ / L := by
    field_simp [hL_pos.ne'] <;> ring
  have h_main : robust_projection.rieszEnergy α (hδ := mul_pos hc_pos hδ) (Measure.map T (Measure.map h μ)) =
      ENNReal.ofReal ((1 / L : ℝ) ^ (-α)) * robust_projection.rieszEnergy α hδ (Measure.map h μ) :=
    cobalt_rieszEnergy_affine_scaling (α := α) (hδ := hδ) (hc := hc_pos) (T := T) hT_meas hT_dist (Measure.map h μ)
  have h_map_comp : Measure.map T (Measure.map h μ) = Measure.map (T ∘ h) μ := by
    rw [Measure.map_map hT_meas hh_meas] <;> rfl
  rw [h_map_comp] at h_main
  have h_exp : (1 / L : ℝ) ^ (-α) = L ^ α := by
    have h_pos1 : 0 < (1 / L : ℝ) := by positivity
    have h1 : (1 / L : ℝ) ^ (-α) = ((1 / L : ℝ) ^ α)⁻¹ := by
      rw [Real.rpow_neg h_pos1.le]
      <;> ring
    rw [h1]
    have h2 : (1 / L : ℝ) ^ α = (L ^ α)⁻¹ := by
      have h3 : (1 / L : ℝ) = L⁻¹ := by field_simp [hL_pos.ne']
      rw [h3]
      exact Real.inv_rpow (by linarith) α
    rw [h2]
    have h4 : ((L ^ α)⁻¹)⁻¹ = L ^ α := by
      have h5 : 0 < L ^ α := by positivity
      field_simp [h5.ne']
    rw [h4]
  rw [h_exp] at h_main
  have h_helper : ∀ (x : ℝ) (hx : 0 < x), x = (1 / L) * δ →
      robust_projection.rieszEnergy α (hδ := hx) (Measure.map (T ∘ h) μ) =
      ENNReal.ofReal (L ^ α) * robust_projection.rieszEnergy α hδ (Measure.map h μ) := by
    intro x hx h_eq
    subst h_eq
    exact h_main
  exact h_helper (δ / L) (div_pos hδ hL_pos) h_scale_eq.symm

end ProductLikeIncidence.ProductReduction
