module

/-
# Phase0 Threshold Wiring

Derives the four threshold conditions required by `phase0_composition_v3`
from the outer `δ₀` threshold hypotheses of `incidence_to_ring_contradiction`.

## Contents
1. `hδ_pbar_v3`: Pbar popularity threshold
2. `hδ_box_small_v3`: Box-size threshold
3. `hP_small_v3`: Union covering-number upper bound
4. `h_cY_large_v3`: Y-cardinality lower bound

Also includes helper lemmas `delta_set_ncard_lower` and `cY_large_v3`.

## Whiteprint node
`phase0_threshold_wiring` under `IncidenceToRingContradiction`.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.Compat
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Classical Real ENNReal

namespace ProductLikeIncidence.ProductReduction

/-! ## Helper lemmas -/

/-- Lower bound on the cardinality of a real δ-set: |Y| ≥ δ^(-τ)/C. -/
lemma delta_set_ncard_lower {δ τ C : ℝ} {Y : Set ℝ}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hτ_pos : 0 < τ)
    (hC_pos : 0 < C)
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hY_fin : Y.Finite) :
    (δ ^ (-τ) / C) ≤ (Y.ncard : ℝ) := by
  have h1 : ENNReal.ofReal (1 / (C * δ ^ τ)) ≤
      ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (productLikeRealLineCopy Y)) :=
    IsProductLikeRealDeltaSCSet.min_size hY_delta hY_sub hδ_pos hδ_dyadic hτ_pos hC_pos
  have h_line_eq : realLineCopy Y = productLikeRealLineCopy Y := by
    ext x; simp [realLineCopy, productLikeRealLineCopy]
  have hY_grid' : Y ⊆ deltaGrid δ := by
    intro y hy
    have h : y ∈ productLikeUnitGrid δ := hY_sub hy
    exact h.1
  have h4 : dyadicCoveringNumber δ (realLineCopy Y) = Y.encard :=
    dyadicCoveringNumber_realLineCopy hδ_pos hY_grid'
  have h7 : ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy Y)) =
      ENNReal.ofReal (Y.ncard : ℝ) := by
    rw [h4]
    have h8 : Y.encard = ↑Y.ncard := by
      letI : Fintype Y := Set.Finite.fintype hY_fin
      simp
    rw [h8]
    simp <;> norm_cast
  have h1' : ENNReal.ofReal (1 / (C * δ ^ τ)) ≤
      ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy Y)) := by
    have h_eq : productLikeRealLineCopy Y = realLineCopy Y := h_line_eq.symm
    rw [h_eq] at h1
    exact h1
  rw [h7] at h1'
  have h9 : (1 / (C * δ ^ τ)) = (δ ^ (-τ) / C) := by
    have h10 : 0 < δ ^ τ := Real.rpow_pos_of_pos hδ_pos τ
    have h11 : δ ^ (-τ) = 1 / δ ^ τ := by
      rw [Real.rpow_neg hδ_pos.le] <;> field_simp
    rw [h11] <;> field_simp [h10.ne'] <;> ring
  rw [h9] at h1'
  exact_mod_cast h1'

/-- c_Y large: popularity threshold absorbed by δ-set lower bound.
Given 35*C ≤ δ^(-η_work) and 4*η_work < τ, proves
2 < (δ^(η_work/2) / (7*(35*C)^2)) * Y.ncard. -/
lemma cY_large_v3 {δ η_work τ C C_work : ℝ} {Y : Set ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hη_work_pos : 0 < η_work)
    (hτ_pos : 0 < τ)
    (hC_pos : 0 < C)
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hC_work_eq : C_work = 35 * C)
    (hC_work_le : C_work ≤ δ ^ (-η_work))
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hY_fin : Y.Finite) :
    2 < (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ) := by
  have h_ncard_lower : (δ ^ (-τ) / C) ≤ (Y.ncard : ℝ) :=
    delta_set_ncard_lower hδ_pos (by exact hY_delta.2.2.2.1) hτ_pos hC_pos hY_sub hY_delta hY_fin
  have hC_le : C ≤ δ ^ (-η_work) / 35 := by
    have h1 : 35 * C ≤ δ ^ (-η_work) := by
      rw [hC_work_eq] at hC_work_le; exact hC_work_le
    linarith
  have hC3_le : C ^ 3 ≤ (δ ^ (-η_work)) ^ 3 / 35 ^ 3 := by
    have h2 : (δ ^ (-η_work) / 35) ^ 3 = (δ ^ (-η_work)) ^ 3 / 35 ^ 3 := by
      field_simp <;> ring
    have h3 : C ^ 3 ≤ (δ ^ (-η_work) / 35) ^ 3 := by gcongr <;> linarith
    rw [h2] at h3
    exact h3
  have h_rpow3 : (δ ^ (-η_work)) ^ 3 = δ ^ (-3 * η_work) := by
    have h_nonneg : 0 ≤ δ := by linarith
    have h1 : (δ ^ (-η_work)) ^ 3 = (δ ^ (-η_work)) ^ (3 : ℝ) := by
      exact (Real.rpow_natCast (δ ^ (-η_work)) 3).symm
    rw [h1]
    have h2 : (δ ^ (-η_work)) ^ (3 : ℝ) = δ ^ ((-η_work) * (3 : ℝ)) := by
      rw [Real.rpow_mul h_nonneg]
    rw [h2]
    have h3 : (-η_work) * (3 : ℝ) = -3 * η_work := by ring
    rw [h3]
  have hC3_le' : C ^ 3 ≤ δ ^ (-3 * η_work) / 35 ^ 3 := by
    rw [h_rpow3] at hC3_le
    exact hC3_le
  have h_main_lower : (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ) ≥
      δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) := by
    have h_simp : (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (δ ^ (-τ) / C) =
        δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) := by
      have h_mul : δ ^ (η_work / 2) * δ ^ (-τ) = δ ^ (η_work / 2 - τ) := by
        have h_exp : η_work / 2 + (-τ) = η_work / 2 - τ := by ring
        have h : δ ^ (η_work / 2) * δ ^ (-τ) = δ ^ (η_work / 2 + (-τ)) := by
          rw [← Real.rpow_add hδ_pos]
        rw [h, h_exp]
      calc
        (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (δ ^ (-τ) / C)
          = (δ ^ (η_work / 2) * δ ^ (-τ)) / (7 * (35 * C) ^ 2 * C) := by ring
        _ = δ ^ (η_work / 2 - τ) / (7 * (35 * C) ^ 2 * C) := by rw [h_mul]
        _ = δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) := by
          have h_denom : (7 * (35 * C) ^ 2 * C) = 7 * 35 ^ 2 * C ^ 3 := by ring
          rw [h_denom]
    calc
      (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ)
        ≥ (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (δ ^ (-τ) / C) := by gcongr
      _ = δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) := h_simp
  have h_exp_neg : 7 / 2 * η_work - τ < 0 := by linarith
  have hδ_inv_gt_one : δ ^ (7 / 2 * η_work - τ) > 1 := by
    have h1 : 0 < τ - 7 / 2 * η_work := by linarith
    have h2 : δ ^ (τ - 7 / 2 * η_work) < 1 := by
      apply Real.rpow_lt_one (by linarith) (by linarith) h1
    have h3 : δ ^ (7 / 2 * η_work - τ) = (δ ^ (τ - 7 / 2 * η_work))⁻¹ := by
      have h4 : 7 / 2 * η_work - τ = -(τ - 7 / 2 * η_work) := by ring
      rw [h4]
      rw [← Real.rpow_neg (by linarith)] <;> ring
    rw [h3]
    have h5 : 0 < δ ^ (τ - 7 / 2 * η_work) := by positivity
    have h6 : (δ ^ (τ - 7 / 2 * η_work))⁻¹ > 1 := by
      have h7 : δ ^ (τ - 7 / 2 * η_work) < 1 := h2
      have h8 : 0 < δ ^ (τ - 7 / 2 * η_work) := h5
      have h9 : 1 < (δ ^ (τ - 7 / 2 * η_work))⁻¹ := by
        calc 1
          = (δ ^ (τ - 7 / 2 * η_work)) / (δ ^ (τ - 7 / 2 * η_work)) := by field_simp [h8.ne']
        _ < (1 : ℝ) / (δ ^ (τ - 7 / 2 * η_work)) := by gcongr
        _ = (δ ^ (τ - 7 / 2 * η_work))⁻¹ := by ring
      exact h9
    exact h6
  have h_gt : (2 : ℝ) < δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) := by
    have h2_pos : 0 < 7 * 35 ^ 2 * C ^ 3 := by positivity
    have h3_pos : 0 < 7 * 35 ^ 2 * (δ ^ (-3 * η_work) / 35 ^ 3) := by positivity
    have h_denom_le : 7 * 35 ^ 2 * C ^ 3 ≤ 7 * 35 ^ 2 * (δ ^ (-3 * η_work) / 35 ^ 3) := by
      have h_pos : 0 ≤ 7 * (35 : ℝ) ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left hC3_le' h_pos
    have h_num_pos : 0 < δ ^ (η_work / 2 - τ) := by positivity
    have h3 : δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) ≥
        δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * (δ ^ (-3 * η_work) / 35 ^ 3)) := by
      exact div_le_div_of_nonneg_left h_num_pos.le h2_pos h_denom_le
    have h4 : δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * (δ ^ (-3 * η_work) / 35 ^ 3)) =
        5 * δ ^ (7 / 2 * η_work - τ) := by
      have h_denom2 : 7 * 35 ^ 2 * (δ ^ (-3 * η_work) / 35 ^ 3) = (1 / 5 : ℝ) * δ ^ (-3 * η_work) := by ring
      rw [h_denom2]
      have h_pos2 : 0 < δ ^ (-3 * η_work) := by positivity
      have h_div : δ ^ (η_work / 2 - τ) / ((1 / 5 : ℝ) * δ ^ (-3 * η_work)) =
          5 * δ ^ (η_work / 2 - τ) / δ ^ (-3 * η_work) := by
        field_simp [h_pos2.ne'] <;> ring
      rw [h_div]
      have h_rpow_div : δ ^ (η_work / 2 - τ) / δ ^ (-3 * η_work) =
          δ ^ (7 / 2 * η_work - τ) := by
        have h_pos3 : 0 < δ ^ (-3 * η_work) := by positivity
        have h_eq1 : δ ^ (η_work / 2 - τ) =
            δ ^ (7 / 2 * η_work - τ) * δ ^ (-3 * η_work) := by
          have h : δ ^ (7 / 2 * η_work - τ) * δ ^ (-3 * η_work) =
              δ ^ ((7 / 2 * η_work - τ) + (-3 * η_work)) := by
            rw [← Real.rpow_add hδ_pos] <;> ring
          rw [h]
          have h_exp : (7 / 2 * η_work - τ) + (-3 * η_work) = η_work / 2 - τ := by ring
          rw [h_exp]
        rw [h_eq1]
        field_simp [h_pos3.ne'] <;> ring
      have h_goal : (5 * δ ^ (η_work / 2 - τ)) / δ ^ (-3 * η_work) = 5 * δ ^ (7 / 2 * η_work - τ) := by
        have h_assoc : (5 * δ ^ (η_work / 2 - τ)) / δ ^ (-3 * η_work) =
            5 * (δ ^ (η_work / 2 - τ) / δ ^ (-3 * η_work)) := by ring
        rw [h_assoc, h_rpow_div] <;> ring
      exact h_goal
    have h5 : 5 * δ ^ (7 / 2 * η_work - τ) > 2 := by
      have h6 : 1 < δ ^ (7 / 2 * η_work - τ) := hδ_inv_gt_one
      nlinarith
    have h9 : δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3) ≥ 5 * δ ^ (7 / 2 * η_work - τ) := by
      calc δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * C ^ 3)
          ≥ δ ^ (η_work / 2 - τ) / (7 * 35 ^ 2 * (δ ^ (-3 * η_work) / 35 ^ 3)) := h3
        _ = 5 * δ ^ (7 / 2 * η_work - τ) := h4
    exact lt_of_lt_of_le h5 h9
  exact lt_of_lt_of_le h_gt h_main_lower

/-! ## Main lemma -/

/-- Derive the four Phase0 V3 threshold conditions from outer hypotheses.

Given the outer `δ₀` thresholds and the theorem's setup, produce:
1. `hδ_pbar`: `δ^(-(2s - 2κ0 - η_work/2 - 4η_work)) ≥ 98`
2. `hδ_box_small`: box-size threshold at `qBox η_work τ`
3. `hP_small`: `Nδ(⋃ Pz z) < δ^(-(2s + η_work/2))`
4. `h_cY_large`: `2 < (δ^(η_work/2) / (7·(35C)^2)) · |Y|`
-/
lemma phase0_threshold_wiring
    {δ s τ κ0 η η_work C C_work : ℝ}
    {Y : Set ℝ} {X : ℝ → Set ℝ}
    {P : Set (EuclideanSpace ℝ (Fin 2))}
    {Zf : Finset (EuclideanSpace ℝ (Fin 2))}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s)
    (hκ0_pos : 0 < κ0)
    (hτ_pos : 0 < τ)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hC_pos : 0 < C)
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hC_work_eq : C_work = 35 * C)
    (hC_work_le : C_work ≤ δ ^ (-η_work))
    -- Outer δ₀ thresholds
    (h_pbar_98 : (98 : ℝ) ≤ δ ^ (-(2 * s - 2 * κ0 - 5 * η_work)))
    (hδ_box_small : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ))
    -- Setup
    (hZf : (Zf : Set _) = productLikeIncidenceSet Y X)
    (hPz : ∀ z ∈ Zf, Pz z ⊆ P ∧ IsDeltaSCSet δ s C (Pz z) ∧
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hP_small : ENat.toENNReal (dyadicCoveringNumber δ P) <
      ENNReal.ofReal (δ ^ (-(2 * s + η))))
    (hY_sub : Y ⊆ productLikeUnitGrid δ)
    (hY_delta : IsProductLikeRealDeltaSCSet δ τ C Y)
    (hY_fin : Y.Finite) :
    (δ ^ (-(2 * s - 2 * κ0 - (η_work / 2) - 4 * η_work)) ≥ 98) ∧
    (δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
        ((6 * (35 * C) * 2 ^ τ) /
         (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ)) ∧
    (ENat.toENNReal (dyadicCoveringNumber δ
        (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) <
      ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2)))) ∧
    (2 < (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ)) := by
  -- 1. Pbar popularity threshold
  have hδ_pbar_v3 : δ ^ (-(2 * s - 2 * κ0 - (η_work / 2) - 4 * η_work)) ≥ 98 := by
    set exp_small := -(2 * s - 2 * κ0 - (η_work / 2) - 4 * η_work) with hexp_small
    set exp_large := -(2 * s - 2 * κ0 - 5 * η_work) with hexp_large
    have h_exp_le : exp_small ≤ exp_large := by
      simp only [hexp_small, hexp_large] <;> linarith [hη_work_pos]
    have h_mono : δ ^ exp_large ≤ δ ^ exp_small :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp_le
    have h98 : (98 : ℝ) ≤ δ ^ exp_large := h_pbar_98
    linarith
  -- 2. Box threshold is identical to outer hypothesis
  have hδ_box_small_v3 : δ ^ (-(qBox η_work τ)) ≥ 8 * (1 + (1 + 12 * δ) *
      ((6 * (35 * C) * 2 ^ τ) /
       (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2))) ^ (1 / τ) + 6 * δ) :=
    hδ_box_small
  -- 3. Union covering-number bound
  have hP_small_v3 : ENat.toENNReal (dyadicCoveringNumber δ
        (⋃ z ∈ productLikeIncidenceSet Y X, Pz z)) <
      ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2))) := by
    have h_union_sub_P : (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) ⊆ P := by
      intro p hp
      rcases Set.mem_iUnion₂.mp hp with ⟨z, hz, hpz⟩
      have hz' : z ∈ Zf := by
        have hz_set : z ∈ (Zf : Set _) := hZf.symm ▸ hz
        exact_mod_cast hz_set
      exact (hPz z hz').1 hpz
    have h_mono : dyadicCoveringNumber δ (⋃ z ∈ productLikeIncidenceSet Y X, Pz z) ≤
        dyadicCoveringNumber δ P := by
      apply dyadicCoveringNumber_mono
      exact h_union_sub_P
    have h_eta_eq : η_work / 2 = η := by linarith [hη_work_eq_two]
    have h_bound : ENat.toENNReal (dyadicCoveringNumber δ P) <
        ENNReal.ofReal (δ ^ (-(2 * s + η_work / 2))) := by
      rw [h_eta_eq] at *
      exact hP_small
    exact lt_of_le_of_lt (ENat.toENNReal_mono h_mono) h_bound
  -- 4. Y-cardinality lower bound
  have h_cY_large_v3 : 2 < (δ ^ (η_work / 2) / (7 * (35 * C) ^ 2)) * (Y.ncard : ℝ) :=
    cY_large_v3 (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one) (hη_work_pos := hη_work_pos)
      (hτ_pos := hτ_pos) (hC_pos := hC_pos) (h4η_work_lt_tau := h4η_work_lt_tau)
      (hC_work_eq := hC_work_eq) (hC_work_le := hC_work_le)
      (hY_sub := hY_sub) (hY_delta := hY_delta) (hY_fin := hY_fin)
  exact ⟨hδ_pbar_v3, hδ_box_small_v3, hP_small_v3, h_cY_large_v3⟩

end ProductLikeIncidence.ProductReduction
