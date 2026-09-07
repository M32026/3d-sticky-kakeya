module

/-
# Box Bound Threshold (Production)

Proves the box-size threshold condition `hδ_box_small` for sufficiently
small dyadic scales, **uniformly in C**.

## Uniformity

The constant `C` is quantified inside the δ scope, with the bound
`C ≤ δ^(-η_work/2)`. This ensures δ₀ does not depend on C.

## Exponent calculation

Inside the τ-root: `42 * (35*C)^3 * 2^τ / δ^(η_work/2)`.
Given `C ≤ δ^(-η_work/2)`:
- `C^3 ≤ δ^(-3η_work/2)`, so `(35*C)^3 ≤ 35^3 * δ^(-3η_work/2)`
- Total inside root grows as `35^3 * δ^(-3η_work/2) * δ^(-η_work/2) = 35^3 * δ^(-2η_work)`
- After 1/τ root: growth exponent `2η_work/τ`, constant `(42*35^3*2^τ)^(1/τ)`
- `qBox = 4η_work/τ + η_work/100`
- Gap: `qBox - 2η_work/τ = 2η_work/τ + η_work/100 > 0`

The C-independent constant `(42*35^3*2^τ)^(1/τ)` is absorbed by the gap.

## Dependencies

- `MyLeanRepo.ProductLikeIncidence.WireBudgets` — `qBox`, `qAbsorb`
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Real

namespace ProductLikeIncidence.ProductReduction

/-- Box-size threshold (uniform in C): for sufficiently small δ, and any
`C` satisfying `C ≤ δ^(-η_work/2)`, the box expression is bounded by
`δ^(-qBox η_work τ)`. This discharges the `hδ_box_small` hypothesis of
`phase0_threshold_wiring_v3`. -/
lemma box_bound_threshold_uniform {η_work τ : ℝ}
    (hη_work_pos : 0 < η_work) (hτ_pos : 0 < τ) :
    ∃ δ₀ > 0, ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
      ∀ (C : ℝ), 0 < C → C ≤ δ^(-η_work/2) →
        δ ^ (-(qBox η_work τ)) ≥
          8 * (1 + (1 + 12 * δ) *
            ((6 * (35 * C) * 2 ^ τ) /
             (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ) := by
  set α : ℝ := qBox η_work τ - 2 * η_work / τ with hα_def
  have hα_pos : 0 < α := by
    have h1 : qBox η_work τ = 4 * η_work / τ + η_work / 100 := by
      simp [qBox, qAbsorb] <;> ring
    have h2 : α = 2 * η_work / τ + η_work / 100 := by
      rw [hα_def, h1] <;> ring
    rw [h2]
    have h3 : 0 < 2 * η_work / τ := by positivity
    have h4 : 0 < η_work / 100 := by positivity
    exact add_pos h3 h4
  set K0 : ℝ := (42 * (35 : ℝ)^3 * 2^τ)^(1/τ) with hK0_def
  have hK0_nonneg : 0 ≤ K0 := by positivity
  set M : ℝ := 8 * (7 + 13 * K0) with hM_def
  have hM_pos : 0 < M := by positivity
  set threshold : ℝ := (1/M)^(1/α) with hthreshold_def
  have h1M_pos : 0 < 1/M := by positivity
  have hthreshold_pos : 0 < threshold := Real.rpow_pos_of_pos h1M_pos (1/α)
  set δ₀ : ℝ := min (1/2) threshold with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    have h1 : 0 < (1/2 : ℝ) := by norm_num
    exact lt_min h1 hthreshold_pos
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le C hC_pos hC_bound => ?_⟩
  have hδ_le_one : δ ≤ 1 := by
    have h : δ ≤ 1/2 := le_trans hδ_le (min_le_left _ _)
    linarith
  have hδ_le_thresh : δ ≤ threshold := le_trans hδ_le (min_le_right _ _)

  set C' : ℝ := 35 * C with hC'_def
  have hC'_pos : 0 < C' := by positivity

  -- Step 1: C^3 ≤ δ^(-3η/2)
  have h1 : C^3 ≤ δ^(-3*η_work/2) := by
    have h1a : C^3 ≤ (δ^(-η_work/2))^3 := by gcongr <;> exact hC_bound
    have h1b : (δ^(-η_work/2))^3 = δ^(-3*η_work/2) := by
      have h_pow3 : (δ^(-η_work/2))^3 = δ^(-η_work/2) * δ^(-η_work/2) * δ^(-η_work/2) := by ring
      rw [h_pow3]
      have h_add1 : δ^(-η_work/2) * δ^(-η_work/2) = δ^(-η_work) := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf
      rw [h_add1]
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h1b] at h1a
    exact h1a

  -- Step 2: C'^3 * δ^(-η/2) ≤ 35^3 * δ^(-2η)
  have hC3_bound : C'^3 * δ^(-η_work/2) ≤ (35 : ℝ)^3 * δ^(-2*η_work) := by
    have h2a : C'^3 = (35 : ℝ)^3 * C^3 := by
      simp [hC'_def] <;> ring
    have h2b : δ^(-3*η_work/2) * δ^(-η_work/2) = δ^(-2*η_work) := by
      have h : (-3*η_work/2) + (-η_work/2) = -2*η_work := by ring
      rw [← Real.rpow_add hδ_pos, h]
    calc
      C'^3 * δ^(-η_work/2)
        = (35 : ℝ)^3 * C^3 * δ^(-η_work/2) := by rw [h2a] <;> ring
      _ ≤ (35 : ℝ)^3 * δ^(-3*η_work/2) * δ^(-η_work/2) := by gcongr <;> linarith
      _ = (35 : ℝ)^3 * (δ^(-3*η_work/2) * δ^(-η_work/2)) := by ring
      _ = (35 : ℝ)^3 * δ^(-2*η_work) := by rw [h2b]

  -- Step 3: Inner fraction simplification
  have h_pos_eta2 : 0 < δ^(η_work/2) := Real.rpow_pos_of_pos hδ_pos (η_work/2)
  have h_frac : (6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2)) = (42*C'^3*2^τ) * δ^(-η_work/2) := by
    have h_inv : (δ^(η_work/2) / (7*C'^2))⁻¹ = (7*C'^2) / δ^(η_work/2) := by
      field_simp [h_pos_eta2.ne'] <;> ring
    have h_neg : δ^(-η_work/2) = (δ^(η_work/2))⁻¹ := by
      have h_eq : (-η_work/2 : ℝ) = -(η_work/2) := by ring
      rw [h_eq]
      exact Real.rpow_neg hδ_pos.le (η_work/2)
    calc
      (6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2))
        = (6*C'*2^τ) * ((7*C'^2) / δ^(η_work/2)) := by rw [div_div_eq_mul_div] <;> ring
      _ = (42*C'^3*2^τ) / δ^(η_work/2) := by ring
      _ = (42*C'^3*2^τ) * δ^(-η_work/2) := by rw [h_neg] <;> ring

  -- Step 4: Inner^(1/τ) ≤ K0 * δ^(-2η/τ)
  have h_inner_bound : ((6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2)))^(1/τ) ≤ K0 * δ^(-2*η_work/τ) := by
    rw [h_frac]
    have h4a : (42*C'^3*2^τ) * δ^(-η_work/2) ≤ (42*(35 : ℝ)^3*2^τ) * δ^(-2*η_work) := by
      calc
        (42*C'^3*2^τ) * δ^(-η_work/2)
          = 42 * (C'^3 * δ^(-η_work/2)) * 2^τ := by ring
        _ ≤ 42 * ((35 : ℝ)^3 * δ^(-2*η_work)) * 2^τ := by gcongr <;> linarith
        _ = (42*(35 : ℝ)^3*2^τ) * δ^(-2*η_work) := by ring
    have h4b : ((42*C'^3*2^τ) * δ^(-η_work/2))^(1/τ) ≤
               ((42*(35 : ℝ)^3*2^τ) * δ^(-2*η_work))^(1/τ) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact h4a
      · positivity
    have h4c : ((42*(35 : ℝ)^3*2^τ) * δ^(-2*η_work))^(1/τ) =
               (42*(35 : ℝ)^3*2^τ)^(1/τ) * (δ^(-2*η_work))^(1/τ) := by
      rw [mul_rpow (by positivity) (by positivity)]
    have h4d : (δ^(-2*η_work))^(1/τ) = δ^(-2*η_work/τ) := by
      rw [← Real.rpow_mul hδ_pos.le] <;> ring_nf
    have h4e : (42*(35 : ℝ)^3*2^τ)^(1/τ) = K0 := by
      simp [hK0_def]
    rw [h4c, h4d, h4e] at h4b
    exact h4b

  -- Step 5: 1 ≤ δ^(-2η/τ) since δ ≤ 1
  have h_exp_pos : 0 < 2*η_work/τ := by positivity
  have h_one_le : (1 : ℝ) ≤ δ^(-2*η_work/τ) := by
    have h5a : δ^(2*η_work/τ) ≤ 1 := by
      have h : δ^(2*η_work/τ) ≤ (1:ℝ)^(2*η_work/τ) :=
        Real.rpow_le_rpow (by linarith) hδ_le_one h_exp_pos.le
      have h1 : (1:ℝ)^(2*η_work/τ) = 1 := by simp
      rw [h1] at h
      exact h
    have h5b : 0 < δ^(2*η_work/τ) := Real.rpow_pos_of_pos hδ_pos (2*η_work/τ)
    have h5c : δ^(-2*η_work/τ) = (δ^(2*η_work/τ))⁻¹ := by
      have h_eq : (-2*η_work/τ : ℝ) = -(2*η_work/τ) := by ring
      rw [h_eq]
      exact Real.rpow_neg hδ_pos.le (2*η_work/τ)
    rw [h5c]
    have h5d : (1:ℝ)⁻¹ ≤ (δ^(2*η_work/τ))⁻¹ := by
      gcongr
      <;> linarith
    simpa using h5d

  -- Step 6: δ ≤ δ^(-2η/τ)
  have hδ_le_exp : δ ≤ δ^(-2*η_work/τ) := by
    have h6a : δ ≤ 1 := hδ_le_one
    have h6b : (1 : ℝ) ≤ δ^(-2*η_work/τ) := h_one_le
    linarith

  set E : ℝ := 1 + (1+12*δ) * (((6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2)))^(1/τ)) + 6*δ with hE_def

  -- Step 7: E ≤ (7 + 13*K0) * δ^(-2η/τ)
  have hE_bound : E ≤ (7 + 13*K0) * δ^(-2*η_work/τ) := by
    rw [hE_def]
    have h7a : (1+12*δ) * (((6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2)))^(1/τ)) ≤
               13 * K0 * δ^(-2*η_work/τ) := by
      have h7a1 : 1+12*δ ≤ 13 := by linarith
      have h7a2 : 0 ≤ K0 * δ^(-2*η_work/τ) := by positivity
      calc
        (1+12*δ) * (((6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2)))^(1/τ))
          ≤ (1+12*δ) * (K0 * δ^(-2*η_work/τ)) := by gcongr
        _ ≤ 13 * (K0 * δ^(-2*η_work/τ)) := by
          gcongr <;> linarith
        _ = 13 * K0 * δ^(-2*η_work/τ) := by ring
    have h7b : 6*δ ≤ 6 * δ^(-2*η_work/τ) := by
      have h7b1 : δ ≤ δ^(-2*η_work/τ) := hδ_le_exp
      nlinarith
    have h7c : (1 : ℝ) ≤ δ^(-2*η_work/τ) := h_one_le
    have h7d : 1 + (1+12*δ) * (((6*C'*2^τ) / (δ^(η_work/2) / (7*C'^2)))^(1/τ)) + 6*δ ≤
               1 + 13 * K0 * δ^(-2*η_work/τ) + 6 * δ^(-2*η_work/τ) := by
      have h7d1 : (1 : ℝ) ≤ 1 := by norm_num
      exact add_le_add (add_le_add h7d1 h7a) h7b
    have h7e : 1 + 13 * K0 * δ^(-2*η_work/τ) + 6 * δ^(-2*η_work/τ) =
               1 + (13*K0 + 6) * δ^(-2*η_work/τ) := by ring
    have h7f : 1 + (13*K0 + 6) * δ^(-2*η_work/τ) ≤
               δ^(-2*η_work/τ) + (13*K0 + 6) * δ^(-2*η_work/τ) := by
      have h7f1 : (1 : ℝ) ≤ δ^(-2*η_work/τ) := h7c
      nlinarith
    have h7g : δ^(-2*η_work/τ) + (13*K0 + 6) * δ^(-2*η_work/τ) =
               (7 + 13*K0) * δ^(-2*η_work/τ) := by ring
    rw [h7e] at h7d
    exact le_trans h7d (le_trans h7f (by rw [h7g]))

  -- Step 8: 8*E ≤ M * δ^(-2η/τ)
  have h_main2 : 8 * E ≤ M * δ^(-2*η_work/τ) := by
    calc 8 * E ≤ 8 * ((7 + 13*K0) * δ^(-2*η_work/τ)) := by gcongr
         _ = M * δ^(-2*η_work/τ) := by simp [hM_def] <;> ring

  -- Step 9: δ^α ≤ 1/M
  have h9a : δ^α ≤ threshold^α := Real.rpow_le_rpow (by linarith) hδ_le_thresh (by linarith)
  have hα_ne_zero : α ≠ 0 := hα_pos.ne'
  have h9b : threshold^α = 1/M := by
    simp only [hthreshold_def]
    have h : ((1/M)^(1/α))^α = (1/M)^((1/α) * α) := by
      rw [← Real.rpow_mul h1M_pos.le]
    rw [h]
    have h2 : (1/α) * α = 1 := by
      field_simp [hα_ne_zero] <;> ring
    rw [h2]
    simp
  have h9c : δ^α ≤ 1/M := by
    rw [h9b] at h9a
    exact h9a

  -- Step 10: M ≤ δ^(-α)
  have h10a : 0 < δ^α := Real.rpow_pos_of_pos hδ_pos α
  have h10b : M ≤ 1 / δ^α := by
    have h10c : 1 / (1/M) ≤ 1 / δ^α := one_div_le_one_div_of_le h10a h9c
    have h10d : 1 / (1/M) = M := by
      field_simp [hM_pos.ne'] <;> ring
    rw [h10d] at h10c
    exact h10c
  have h10e : δ^(-α) = 1 / δ^α := by
    rw [Real.rpow_neg hδ_pos.le] <;> ring
  have h10f : M ≤ δ^(-α) := by
    rw [h10e]
    exact h10b

  -- Step 11: M * δ^(-2η/τ) ≤ δ^(-2η/τ) * δ^(-α)
  have h11 : M * δ^(-2*η_work/τ) ≤ δ^(-2*η_work/τ) * δ^(-α) := by
    have h11a : 0 ≤ δ^(-2*η_work/τ) := by positivity
    have h11b : M * δ^(-2*η_work/τ) ≤ δ^(-α) * δ^(-2*η_work/τ) :=
      mul_le_mul_of_nonneg_right h10f h11a
    have h11c : δ^(-α) * δ^(-2*η_work/τ) = δ^(-2*η_work/τ) * δ^(-α) := by ring
    rw [h11c] at h11b
    exact h11b

  -- Step 12: δ^(-qBox) = δ^(-2η/τ) * δ^(-α)
  have h12a : qBox η_work τ = 2*η_work/τ + α := by
    simp only [hα_def, qBox, qAbsorb] <;> ring
  have h12b : δ^(-(qBox η_work τ)) = δ^(-2*η_work/τ) * δ^(-α) := by
    have h12c : -(qBox η_work τ) = -2*η_work/τ - α := by
      rw [h12a] <;> ring
    rw [h12c]
    have h12d : δ^(-2*η_work/τ - α) = δ^(-2*η_work/τ) * δ^(-α) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    exact h12d

  rw [h12b]
  exact le_trans h_main2 h11

end ProductLikeIncidence.ProductReduction
