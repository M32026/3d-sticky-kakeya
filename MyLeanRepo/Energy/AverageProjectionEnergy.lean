module

/-
# Average Projection Energy Bound

Proves the average projection energy bound via Riesz energy averaging (Kaufman).

Components:
- `general_fubini3_swap`: triple Tonelli swap
- `projection_energy_to_double_integral`: pushforward expansion
- `frostman_negative_power_integral`: Frostman strip estimate via layer cake
- `directional_energy_integral`: directional energy bound with vector bound
- `average_projection_energy_bound`: main theorem

## Whiteprint node
`robust_projection/AverageProjectionEnergy`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace robust_projection_main

/-! ## Riesz energy definition -/

def rieszEnergy (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {X : Type*} [MeasurableSpace X] [MetricSpace X] (ν : Measure X) : ENNReal :=
  ∫⁻ (x : X), ∫⁻ (y : X),
    ENNReal.ofReal ((max (dist x y) δ) ^ (-α)) ∂ν ∂ν

/-! ## Triple Fubini swap -/

lemma general_fubini3_swap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {f : α → β → γ → ENNReal}
    (hf : Measurable (fun p : α × β × γ => f p.1 p.2.1 p.2.2)) :
    ∫⁻ (a : α), ∫⁻ (b : β), ∫⁻ (c : γ), f a b c ∂ρ ∂ν ∂μ =
    ∫⁻ (b : β), ∫⁻ (c : γ), ∫⁻ (a : α), f a b c ∂μ ∂ρ ∂ν := by
  let h : α → β → ENNReal := fun a b => ∫⁻ (c : γ), f a b c ∂ρ
  have h_uncurry_meas : Measurable (Function.uncurry h : α × β → ENNReal) := by
    let reindex : (α × β) × γ → α × β × γ := fun p => (p.1.1, p.1.2, p.2)
    have h_reindex_meas : Measurable reindex := by fun_prop
    have h_map : Measurable (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2) :=
      hf.comp h_reindex_meas
    exact h_map.lintegral_prod_right'
  have h_step1 : ∫⁻ (a : α), ∫⁻ (b : β), h a b ∂ν ∂μ =
      ∫⁻ (b : β), ∫⁻ (a : α), h a b ∂μ ∂ν := by
    let g : α × β → ENNReal := Function.uncurry h
    have hg_meas : Measurable g := h_uncurry_meas
    have h_eq1 : ∫⁻ (a : α), ∫⁻ (b : β), h a b ∂ν ∂μ =
        ∫⁻ (p : α × β), g p ∂(μ.prod ν) := by
      rw [lintegral_prod g hg_meas.aemeasurable] <;> rfl
    have h_eq2 : ∫⁻ (p : α × β), g p ∂(μ.prod ν) =
        ∫⁻ (p : β × α), g (p.2, p.1) ∂(ν.prod μ) := by
      have h_swap := lintegral_prod_swap (μ := μ) (ν := ν) g
      simpa [Prod.swap] using h_swap.symm
    have h_eq3 : ∫⁻ (p : β × α), g (p.2, p.1) ∂(ν.prod μ) =
        ∫⁻ (b : β), ∫⁻ (a : α), h a b ∂μ ∂ν := by
      rw [lintegral_prod (fun p : β × α => g (p.2, p.1)) (by fun_prop)] <;> rfl
    calc
      ∫⁻ (a : α), ∫⁻ (b : β), h a b ∂ν ∂μ
        = ∫⁻ (p : α × β), g p ∂(μ.prod ν) := h_eq1
      _ = ∫⁻ (p : β × α), g (p.2, p.1) ∂(ν.prod μ) := h_eq2
      _ = ∫⁻ (b : β), ∫⁻ (a : α), h a b ∂μ ∂ν := h_eq3
  have h_step2 : ∀ (b : β),
      ∫⁻ (a : α), h a b ∂μ =
      ∫⁻ (c : γ), ∫⁻ (a : α), f a b c ∂μ ∂ρ := by
    intro b
    let k : α → γ → ENNReal := fun a c => f a b c
    let reindex2 : α × γ → α × β × γ := fun p => (p.1, b, p.2)
    have h_reindex2_meas : Measurable reindex2 := by fun_prop
    have hk_meas : Measurable (Function.uncurry k : α × γ → ENNReal) :=
      hf.comp h_reindex2_meas
    let g2 : α × γ → ENNReal := Function.uncurry k
    have h_eq1 : ∫⁻ (a : α), ∫⁻ (c : γ), g2 (a, c) ∂ρ ∂μ =
        ∫⁻ (p : α × γ), g2 p ∂(μ.prod ρ) := by
      rw [lintegral_prod g2 hk_meas.aemeasurable] <;> rfl
    have h_eq2 : ∫⁻ (p : α × γ), g2 p ∂(μ.prod ρ) =
        ∫⁻ (p : γ × α), g2 (p.2, p.1) ∂(ρ.prod μ) := by
      have h_swap := lintegral_prod_swap (μ := μ) (ν := ρ) g2
      simpa [Prod.swap] using h_swap.symm
    have h_eq3 : ∫⁻ (p : γ × α), g2 (p.2, p.1) ∂(ρ.prod μ) =
        ∫⁻ (c : γ), ∫⁻ (a : α), g2 (a, c) ∂μ ∂ρ := by
      rw [lintegral_prod (fun p : γ × α => g2 (p.2, p.1)) (by fun_prop)] <;> rfl
    calc
      ∫⁻ (a : α), ∫⁻ (c : γ), g2 (a, c) ∂ρ ∂μ
        = ∫⁻ (p : α × γ), g2 p ∂(μ.prod ρ) := h_eq1
      _ = ∫⁻ (p : γ × α), g2 (p.2, p.1) ∂(ρ.prod μ) := h_eq2
      _ = ∫⁻ (c : γ), ∫⁻ (a : α), g2 (a, c) ∂μ ∂ρ := h_eq3
  calc
    ∫⁻ (a : α), ∫⁻ (b : β), h a b ∂ν ∂μ
      = ∫⁻ (b : β), ∫⁻ (a : α), h a b ∂μ ∂ν := h_step1
    _ = ∫⁻ (b : β), ∫⁻ (c : γ), ∫⁻ (a : α), f a b c ∂μ ∂ρ ∂ν := by
      congr with b
      exact h_step2 b

/-! ## Energy integrand -/

def energyIntegrand (δ κ : ℝ) (y : ℝ)
    (x z : EuclideanSpace ℝ (Fin 2)) : ENNReal :=
  ENNReal.ofReal ((max (|(x 0 - z 0) * y + (x 1 - z 1)|) δ) ^ (-(2 * κ)))

lemma energyIntegrand_measurable {δ κ : ℝ} (hδ_pos : 0 < δ) (hκ_pos : 0 < κ) :
    Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
      energyIntegrand δ κ p.1 p.2.1 p.2.2) := by
  let E2 := EuclideanSpace ℝ (Fin 2)
  have h_proj0 : Measurable (fun x : E2 => x 0) := by
    have h : Continuous (fun x : E2 => x 0) := by exact PiLp.continuous_apply 2 (fun x => ℝ) 0
    exact h.measurable
  have h_proj1 : Measurable (fun x : E2 => x 1) := by
    have h : Continuous (fun x : E2 => x 1) := by exact PiLp.continuous_apply 2 (fun x => ℝ) 1
    exact h.measurable
  have h_fst : Measurable (fun p : ℝ × E2 × E2 => p.1) := measurable_fst
  have h_snd1 : Measurable (fun p : ℝ × E2 × E2 => p.2.1) := by
    have h : Measurable (fun p : ℝ × E2 × E2 => (p.2).1) :=
      measurable_fst.comp measurable_snd
    simpa using h
  have h_snd2 : Measurable (fun p : ℝ × E2 × E2 => p.2.2) := by
    have h : Measurable (fun p : ℝ × E2 × E2 => (p.2).2) :=
      measurable_snd.comp measurable_snd
    simpa using h
  have h_x0 : Measurable (fun p : ℝ × E2 × E2 => p.2.1 0) := h_proj0.comp h_snd1
  have h_x1 : Measurable (fun p : ℝ × E2 × E2 => p.2.1 1) := h_proj1.comp h_snd1
  have h_z0 : Measurable (fun p : ℝ × E2 × E2 => p.2.2 0) := h_proj0.comp h_snd2
  have h_z1 : Measurable (fun p : ℝ × E2 × E2 => p.2.2 1) := h_proj1.comp h_snd2
  have h_diff0 : Measurable (fun p : ℝ × E2 × E2 => p.2.1 0 - p.2.2 0) := h_x0.sub h_z0
  have h_diff1 : Measurable (fun p : ℝ × E2 × E2 => p.2.1 1 - p.2.2 1) := h_x1.sub h_z1
  have h_inner : Measurable (fun p : ℝ × E2 × E2 => (p.2.1 0 - p.2.2 0) * p.1 + (p.2.1 1 - p.2.2 1)) :=
    (h_diff0.mul h_fst).add h_diff1
  have h_base : Measurable (fun p : ℝ × E2 × E2 => max (|(p.2.1 0 - p.2.2 0) * p.1 + (p.2.1 1 - p.2.2 1)|) δ) :=
    h_inner.abs.max measurable_const
  have h_rpow : Measurable (fun x : ℝ => x ^ (-(2 * κ))) :=
    measurable_id.pow measurable_const
  have h_main : Measurable (fun p : ℝ × E2 × E2 =>
      ENNReal.ofReal ((max (|(p.2.1 0 - p.2.2 0) * p.1 + (p.2.1 1 - p.2.2 1)|) δ) ^ (-(2 * κ)))) :=
    (h_rpow.comp h_base).ennreal_ofReal
  exact h_main

/-! ## Pushforward energy expansion -/

lemma projection_energy_to_double_integral
    {δ κ : ℝ} (hδ_pos : 0 < δ) (hκ_pos : 0 < κ)
    {ν : Measure (EuclideanSpace ℝ (Fin 2))}
    [SFinite ν]
    {y : ℝ} :
    ∫⁻ (a : ℝ), ∫⁻ (b : ℝ),
        ENNReal.ofReal ((max (dist a b) δ) ^ (-(2 * κ)))
        ∂(Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) ν)
        ∂(Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) ν) =
    ∫⁻ (x : EuclideanSpace ℝ (Fin 2)),
      ∫⁻ (z : EuclideanSpace ℝ (Fin 2)),
        energyIntegrand δ κ y x z ∂ν ∂ν := by
  let π_y : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0 * y + p 1
  have hπy_meas : Measurable π_y := by fun_prop
  have h_main1 : ∫⁻ (a : ℝ), ∫⁻ (b : ℝ),
        ENNReal.ofReal ((max (dist a b) δ) ^ (-(2 * κ)))
        ∂(Measure.map π_y ν) ∂(Measure.map π_y ν) =
      ∫⁻ (x : EuclideanSpace ℝ (Fin 2)),
        ∫⁻ (b : ℝ),
          ENNReal.ofReal ((max (dist (π_y x) b) δ) ^ (-(2 * κ)))
          ∂(Measure.map π_y ν) ∂ν := by
    rw [lintegral_map' (by fun_prop) hπy_meas.aemeasurable]
    <;> rfl
  rw [h_main1]
  have h_main2 : ∀ (x : EuclideanSpace ℝ (Fin 2)),
      ∫⁻ (b : ℝ),
        ENNReal.ofReal ((max (dist (π_y x) b) δ) ^ (-(2 * κ)))
        ∂(Measure.map π_y ν) =
      ∫⁻ (z : EuclideanSpace ℝ (Fin 2)),
        ENNReal.ofReal ((max (dist (π_y x) (π_y z)) δ) ^ (-(2 * κ))) ∂ν := by
    intro x
    rw [lintegral_map' (by fun_prop) hπy_meas.aemeasurable]
    <;> rfl
  congr with x
  rw [h_main2 x]
  congr with z
  have h_eq : dist (π_y x) (π_y z) = |(x 0 - z 0) * y + (x 1 - z 1)| := by
    simp [π_y, dist_eq_norm] <;> ring_nf
  rw [h_eq]
  <;> rfl

/-! ## Integral evaluation helpers -/

/-- Integrability of `t^(s-1)` on `Ioc 0 1` for `s > 0`. -/
private lemma integrable_rpow_Ioc01 {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t ^ (s - 1)) (Set.Ioc (0 : ℝ) 1) := by
  have h1 : -1 < s - 1 := by linarith
  have h2 : IntegrableOn (fun t : ℝ => t ^ (s - 1)) (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (ht := by norm_num)).mpr h1
  have h3 : Set.Ioc (0 : ℝ) 1 =ᵐ[volume] Set.Ioo (0 : ℝ) 1 := by
    have h4 : ∀ᵐ (t : ℝ) ∂volume, t ≠ 1 := by exact Measure.ae_ne volume 1
    filter_upwards [h4] with t ht
    have h5 : (t ∈ Set.Ioc (0 : ℝ) 1) = (t ∈ Set.Ioo (0 : ℝ) 1) := by
      simp only [Set.mem_Ioc, Set.mem_Ioo]
      apply propext
      constructor
      · rintro ⟨h1, h2⟩
        have h3 : t < 1 := by
          by_contra h4
          have h5 : t = 1 := by linarith
          exact ht h5
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by linarith⟩
    exact h5
  exact h2.congr_set_ae h3

/-- `∫⁻ t in Ioc 0 1, ENNReal.ofReal (t^(s-1)) = ENNReal.ofReal (1/s)` for `s > 0`. -/
private lemma lintegral_rpow_Ioc01 {s : ℝ} (hs : 0 < s) :
    ∫⁻ (t : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1)) ∂volume =
    ENNReal.ofReal (1 / s) := by
  have h_integrable : IntegrableOn (fun t : ℝ => t ^ (s - 1)) (Set.Ioc (0 : ℝ) 1) :=
    integrable_rpow_Ioc01 hs
  have h_nonneg_ae : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) 1), 0 ≤ t ^ (s - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have h_eq1 : ∫⁻ (t : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1)) ∂volume =
      ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) 1, t ^ (s - 1)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg_ae] <;> rfl
  rw [h_eq1]
  have h_int_Ioc : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (s - 1) = ∫ t in (0 : ℝ)..1, t ^ (s - 1) :=
    (intervalIntegral.integral_of_le (by norm_num)).symm
  have h_int_val : ∫ t in (0 : ℝ)..1, t ^ (s - 1) = 1 / s := by
    rw [integral_rpow (Or.inl (by linarith))]
    have h0 : (0 : ℝ) ^ s = 0 := Real.zero_rpow (by linarith)
    simp [h0, hs.ne'] <;> ring
  have h_final : ∫ t in Set.Ioc (0 : ℝ) 1, t ^ (s - 1) = 1 / s := by
    rw [h_int_Ioc, h_int_val]
  rw [h_final]

/-- `∫⁻ t in Ioc 1 (1/ε), ENNReal.ofReal (C * t^(s-τ-1)) = ENNReal.ofReal (C/(τ-s) * (1 - ε^(τ-s)))`. -/
private lemma lintegral_rpow_Ioc1 {s τ C ε : ℝ}
    (hs : 0 < s) (hst : s < τ) (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1) (hC_nonneg : 0 ≤ C) :
    ∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1)) ∂volume =
    ENNReal.ofReal (C / (τ - s) * (1 - ε ^ (τ - s))) := by
  have hτ_sub_pos : 0 < τ - s := by linarith
  have h1_le_1ε : 1 ≤ 1 / ε := by
    have h2 : 0 < ε := hε_pos
    have h3 : ε ≤ 1 := hε_le_one
    calc 1 / ε ≥ 1 / 1 := by gcongr
         _ = 1 := by norm_num
  have h_cont : ContinuousOn (fun t : ℝ => C * t ^ (s - τ - 1)) (Set.Icc (1 : ℝ) (1 / ε)) := by
    intro t ht
    have h_t_pos : 0 < t := by linarith [ht.1]
    have h1 : ContinuousAt (fun t : ℝ => t ^ (s - τ - 1)) t :=
      Real.continuousAt_rpow_const t (s - τ - 1) (Or.inl h_t_pos.ne')
    exact h1.const_mul C |>.continuousWithinAt
  have h_ic : IntegrableOn (fun t : ℝ => C * t ^ (s - τ - 1)) (Set.Icc (1 : ℝ) (1 / ε)) :=
    h_cont.integrableOn_Icc
  have h_integrable : IntegrableOn (fun t : ℝ => C * t ^ (s - τ - 1)) (Set.Ioc (1 : ℝ) (1 / ε)) :=
    h_ic.mono_set Set.Ioc_subset_Icc_self
  have h_nonneg_ae : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (1 : ℝ) (1 / ε)),
      0 ≤ C * t ^ (s - τ - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have h_t_pos : 0 < t := by linarith [ht.1]
    exact mul_nonneg hC_nonneg (Real.rpow_nonneg h_t_pos.le _)
  have h_eq1 : ∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1)) ∂volume =
      ENNReal.ofReal (∫ t in Set.Ioc (1 : ℝ) (1 / ε), C * t ^ (s - τ - 1)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg_ae] <;> rfl
  rw [h_eq1]
  have h_int_Ioc : ∫ t in Set.Ioc (1 : ℝ) (1 / ε), C * t ^ (s - τ - 1) =
      ∫ t in (1 : ℝ)..(1 / ε), C * t ^ (s - τ - 1) :=
    (intervalIntegral.integral_of_le h1_le_1ε).symm
  have h_int_val : ∫ t in (1 : ℝ)..(1 / ε), C * t ^ (s - τ - 1) =
      C / (τ - s) * (1 - ε ^ (τ - s)) := by
    have h_factor : ∫ t in (1 : ℝ)..(1 / ε), C * t ^ (s - τ - 1) =
        C * ∫ t in (1 : ℝ)..(1 / ε), t ^ (s - τ - 1) := by
      rw [intervalIntegral.integral_const_mul]
    rw [h_factor]
    have h_uIcc_eq : Set.uIcc (1 : ℝ) (1 / ε) = Set.Icc 1 (1 / ε) := by
      rw [Set.uIcc_of_le h1_le_1ε]
    have h0_not_in : (0 : ℝ) ∉ Set.uIcc 1 (1 / ε) := by
      rw [h_uIcc_eq]; simp
    rw [integral_rpow (Or.inr ⟨by linarith, h0_not_in⟩)]
    have h_exp : s - τ - 1 + 1 = s - τ := by ring
    rw [h_exp]
    have h3 : (1 / ε) ^ (s - τ) = ε ^ (τ - s) := by
      have h4 : 0 < ε := hε_pos
      have h5 : (1 / ε) = ε ^ (-1 : ℝ) := by
        simp [Real.rpow_neg_one] <;> field_simp
      rw [h5, ← Real.rpow_mul h4.le] <;> ring_nf
    have h4 : (1 : ℝ) ^ (s - τ) = 1 := Real.one_rpow (s - τ)
    rw [h3, h4]
    have h5 : C * ((ε ^ (τ - s) - 1) / (s - τ)) = C / (τ - s) * (1 - ε ^ (τ - s)) := by
      have h6 : s - τ = -(τ - s) := by ring
      rw [h6]
      field_simp [hτ_sub_pos.ne'] <;> ring
    exact h5
  have h_final : ∫ t in Set.Ioc (1 : ℝ) (1 / ε), C * t ^ (s - τ - 1) =
      C / (τ - s) * (1 - ε ^ (τ - s)) := by
    rw [h_int_Ioc, h_int_val]
  rw [h_final]

/-! ## Frostman negative power integral -/

/-- Layer-cake + Frostman estimate:
  `∫ max(dist(y,y0), ε)^{-s} dμ ≤ 1 + C * s / (τ - s)`
  for `0 < s < τ`, `δ ≤ ε`, `ε > 0`. -/
lemma frostman_negative_power_integral
    {δ τ s C : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hτ : 0 < τ) (hs : 0 < s) (hst : s < τ)
    {μ : Measure ℝ} (hμ : IsDirectionFrostman δ τ C μ)
    (y0 : ℝ) (ε : ℝ) (hε_pos : 0 < ε) (hδ_le_ε : δ ≤ ε) :
    ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ ≤
      ENNReal.ofReal (1 + C * s / (τ - s)) := by
  -- Derive 0 ≤ C from Frostman (at r=1, interval contains support)
  have hC_nonneg : 0 ≤ C := by
    let I := Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)
    have h_support_in_I : μ.support ⊆ I := by
      intro x hx
      have h_x_in : x ∈ Set.Icc (0 : ℝ) 1 := hμ.2.1 hx
      simp only [I, Set.mem_Icc] at h_x_in ⊢
      constructor <;> linarith
    have h1 : μ I ≤ ENNReal.ofReal (C * (1 : ℝ) ^ τ) :=
      hμ.2.2 (1 / 2) 1 (by linarith [hδ_le_one]) (by norm_num)
    have h2 : μ I = 1 := by
      have h3 : μ (μ.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
      have h4 : Iᶜ ⊆ μ.supportᶜ := compl_subset_compl.mpr h_support_in_I
      have h5 : μ Iᶜ = 0 := measure_mono_null h4 h3
      have hI_meas : MeasurableSet I := measurableSet_Icc
      have hIc_meas : MeasurableSet Iᶜ := hI_meas.compl
      have h6 : μ (I ∪ Iᶜ) = μ I + μ Iᶜ := measure_union disjoint_compl_right hIc_meas
      have h7 : I ∪ Iᶜ = Set.univ := by simp
      have h8 : μ Set.univ = μ I + μ Iᶜ := by rw [← h7, h6]
      have h9 : μ I = μ Set.univ := by rw [h8, h5] <;> simp
      rw [h9, hμ.1]
    rw [h2] at h1
    have h4 : (1 : ENNReal) ≤ ENNReal.ofReal (C * (1 : ℝ) ^ τ) := h1
    have h5 : 0 ≤ C * (1 : ℝ) ^ τ := by
      by_contra h6
      have h7 : C * (1 : ℝ) ^ τ < 0 := lt_of_not_ge h6
      have h8 : ENNReal.ofReal (C * (1 : ℝ) ^ τ) = 0 := ENNReal.ofReal_of_nonpos h7.le
      rw [h8] at h4
      simpa using h4
    have h9 : (1 : ℝ) ≤ C * (1 : ℝ) ^ τ := by
      have h10 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C * (1 : ℝ) ^ τ) := by simpa using h4
      exact (ENNReal.ofReal_le_ofReal_iff h5).mp h10
    have h12 : (1 : ℝ) ^ τ = 1 := Real.one_rpow τ
    have h13 : 1 ≤ C := by
      rw [h12] at h9
      simpa using h9
    have h14 : 0 ≤ C := by linarith [h13]
    exact h14
  have hτ_sub_pos : 0 < τ - s := by linarith
  set h : ℝ → ℝ := fun y => (max (dist y y0) ε)⁻¹ with h_def
  have h_base_pos : ∀ y, 0 < max (dist y y0) ε := by intro y; positivity
  have h_pos : ∀ y, 0 < h y := by intro y; dsimp only [h]; positivity
  have h_nn : 0 ≤ᵐ[μ] h := by filter_upwards with y; exact (h_pos y).le
  have h_meas : Measurable h := by fun_prop
  have h_rpow : ∀ y, (h y) ^ s = (max (dist y y0) ε) ^ (-s) := by
    intro y
    have hb : 0 < max (dist y y0) ε := h_base_pos y
    have h1 : h y = (max (dist y y0) ε)⁻¹ := by simpa [h_def] using rfl
    rw [h1]
    have h2 : ((max (dist y y0) ε)⁻¹) ^ s = (max (dist y y0) ε) ^ (-s) := by
      have h_inv : (max (dist y y0) ε)⁻¹ = (max (dist y y0) ε) ^ (-1 : ℝ) := by
        exact (Real.rpow_neg_one (x := max (dist y y0) ε)).symm
      rw [h_inv, ← Real.rpow_mul hb.le] <;> ring_nf
    exact h2
  -- If ε > 1, trivial bound
  by_cases hε_gt_one : ε > 1
  · have h_triv : ∀ y, (max (dist y y0) ε) ^ (-s) ≤ 1 := by
      intro y
      have h3 : max (dist y y0) ε ≥ ε := le_max_right _ _
      have h4 : max (dist y y0) ε > 1 := by linarith
      have h5 : (max (dist y y0) ε) ^ (-s) ≤ 1 := by
        have h6 : -s < 0 := by linarith
        have h7 : (max (dist y y0) ε) ^ (-s) ≤ (max (dist y y0) ε) ^ (0 : ℝ) := by
          gcongr <;> linarith
        simpa using h7
      exact h5
    have h8 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ ≤
        ENNReal.ofReal (1 : ℝ) := by
      have h9 : ∀ y, ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ≤ ENNReal.ofReal (1 : ℝ) := by
        intro y; exact ENNReal.ofReal_le_ofReal (h_triv y)
      have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ ≤
          ∫⁻ (y : ℝ), ENNReal.ofReal (1 : ℝ) ∂μ := lintegral_mono h9
      have h11 : ∫⁻ (y : ℝ), ENNReal.ofReal (1 : ℝ) ∂μ = ENNReal.ofReal (1 : ℝ) := by
        rw [lintegral_const, hμ.1] <;> simp
      rw [h11] at h10
      exact h10
    have h12 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (1 + C * s / (τ - s)) := by
      apply ENNReal.ofReal_le_ofReal
      have h13 : 0 ≤ C * s / (τ - s) := by
        apply div_nonneg
        · exact mul_nonneg hC_nonneg hs.le
        · linarith
      linarith
    exact le_trans h8 h12
  · -- ε ≤ 1
    have hε_le_one : ε ≤ 1 := by linarith
    have h_main : ∫⁻ (y : ℝ), ENNReal.ofReal ((h y) ^ s) ∂μ =
        ENNReal.ofReal s * ∫⁻ (t : ℝ) in Set.Ioi 0,
          μ {y : ℝ | t < h y} * ENNReal.ofReal (t ^ (s - 1)) ∂volume :=
      MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul μ h_nn h_meas.aemeasurable hs
    have h_goal : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ =
        ∫⁻ (y : ℝ), ENNReal.ofReal ((h y) ^ s) ∂μ := by
      congr with y; rw [h_rpow y]
    rw [h_goal, h_main]
    -- Characterize sets
    have h_set_lt : ∀ (t : ℝ), 0 < t → t < 1 / ε →
        {y : ℝ | t < h y} = {y : ℝ | dist y y0 < 1 / t} := by
      intro t ht hti
      ext y
      have hb : 0 < max (dist y y0) ε := h_base_pos y
      simp only [h_def, Set.mem_setOf_eq]
      have h9 : t < (max (dist y y0) ε)⁻¹ ↔ max (dist y y0) ε < 1 / t := by
        have h10 : 0 < t := ht
        have h11 : 0 < max (dist y y0) ε := hb
        constructor
        · intro h
          have h12 : t * max (dist y y0) ε < 1 := by
            calc t * max (dist y y0) ε
              < (max (dist y y0) ε)⁻¹ * max (dist y y0) ε := by gcongr <;> exact h
            _ = 1 := by field_simp [h11.ne'] <;> ring
          calc max (dist y y0) ε
            = (t * max (dist y y0) ε) / t := by field_simp [h10.ne'] <;> ring
          _ < 1 / t := by gcongr
        · intro h
          have h12 : t * max (dist y y0) ε < 1 := by
            calc t * max (dist y y0) ε
              < t * (1 / t) := by gcongr
            _ = 1 := by field_simp [h10.ne'] <;> ring
          calc t
            = (t * max (dist y y0) ε) / max (dist y y0) ε := by field_simp [h11.ne'] <;> ring
          _ < 1 / max (dist y y0) ε := by gcongr
          _ = (max (dist y y0) ε)⁻¹ := by simp
      rw [h9]
      have h10 : 1 / t > ε := by
        have h11 : t < 1 / ε := hti
        have h12 : 0 < ε := hε_pos
        calc 1 / t > 1 / (1 / ε) := by gcongr <;> exact one_div_pos.mpr h12
             _ = ε := by field_simp [h12.ne'] <;> ring
      have h14 : max (dist y y0) ε < 1 / t ↔ dist y y0 < 1 / t := by
        rw [max_lt_iff]
        constructor
        · intro h; exact h.1
        · intro h; exact ⟨h, by linarith⟩
      exact h14
    have h_set_empty : ∀ (t : ℝ), t ≥ 1 / ε → μ {y : ℝ | t < h y} = 0 := by
      intro t ht
      have h1 : ∀ y, ¬(t < h y) := by
        intro y
        have h2 : h y ≤ 1 / ε := by
          dsimp only [h]
          have h3 : max (dist y y0) ε ≥ ε := le_max_right _ _
          have h4 : (max (dist y y0) ε)⁻¹ ≤ ε⁻¹ := by gcongr
          simpa using h4
        linarith
      have h5 : {y : ℝ | t < h y} = ∅ := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
        exact ⟨fun h6 => False.elim (h1 y h6), fun h6 => False.elim h6⟩
      rw [h5]; simp
    -- Bounds
    have h_bound1 : ∀ (t : ℝ), 0 < t → t ≤ 1 →
        μ {y : ℝ | t < h y} ≤ 1 := by
      intro t ht hti
      have h4 : μ {y : ℝ | t < h y} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      have h5 : μ Set.univ = 1 := hμ.1
      rw [h5] at h4
      exact h4
    have h_bound2 : ∀ (t : ℝ), 1 < t → t < 1 / ε →
        μ {y : ℝ | t < h y} ≤ ENNReal.ofReal (C * (1 / t) ^ τ) := by
      intro t ht1 ht2
      have h_r_pos : 0 < 1 / t := by positivity
      have h_r_geδ : δ ≤ 1 / t := by
        have h4 : 1 / t > ε := by
          have h5 : t < 1 / ε := ht2
          have h6 : 0 < ε := hε_pos
          calc 1 / t > 1 / (1 / ε) := by gcongr <;> exact one_div_pos.mpr h6
               _ = ε := by field_simp [h6.ne'] <;> ring
        linarith [hδ_le_ε]
      have h_r_le1 : 1 / t ≤ 1 := by
        have h5 : 1 < t := ht1
        have h6 : 0 < t := by linarith
        have h7 : 1 / t ≤ 1 / 1 := by gcongr
        simpa using h7
      rw [h_set_lt t (by linarith) ht2]
      have h_set : {y : ℝ | dist y y0 < 1 / t} ⊆ Set.Icc (y0 - 1 / t) (y0 + 1 / t) := by
        intro y hy
        have h7 : |y - y0| < 1 / t := by simpa [dist_eq_norm] using hy
        have h8 : -(1 / t) < y - y0 := (abs_lt.mp h7).1
        have h9 : y - y0 < 1 / t := (abs_lt.mp h7).2
        simp only [Set.mem_Icc] <;> constructor <;> linarith
      have h9 : μ {y : ℝ | dist y y0 < 1 / t} ≤ μ (Set.Icc (y0 - 1 / t) (y0 + 1 / t)) :=
        measure_mono h_set
      have h10 : μ (Set.Icc (y0 - 1 / t) (y0 + 1 / t)) ≤ ENNReal.ofReal (C * (1 / t) ^ τ) :=
        hμ.2.2 y0 (1 / t) h_r_geδ h_r_le1
      exact le_trans h9 h10
    -- Split integral
    let g : ℝ → ENNReal := fun t => μ {y : ℝ | t < h y} * ENNReal.ofReal (t ^ (s - 1))
    have h1_le_1ε : 1 ≤ 1 / ε := by
      have h2 : 0 < ε := hε_pos
      have h3 : ε ≤ 1 := hε_le_one
      calc 1 / ε ≥ 1 / 1 := by gcongr
           _ = 1 := by norm_num
    have h_cover : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 1 ∪ Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε) := by
      intro t ht
      have h_t_pos : 0 < t := ht
      by_cases h : t ≤ 1
      · exact Or.inl (Or.inl ⟨h_t_pos, h⟩)
      · have h' : 1 < t := by linarith
        by_cases h2 : t < 1 / ε
        · exact Or.inl (Or.inr ⟨h', by linarith⟩)
        · exact Or.inr (show t ≥ 1 / ε from by linarith)
    have h_set_assoc : (Set.Ioc 0 1 ∪ Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε)) =
        (Set.Ioc 0 1 ∪ (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε))) := by
      ext x; simp [Set.mem_union] <;> tauto
    have h_union_le : ∫⁻ (t : ℝ) in Set.Ioi 0, g t ∂volume ≤
        (∫⁻ (t : ℝ) in Set.Ioc 0 1, g t ∂volume) +
        ((∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), g t ∂volume) +
        (∫⁻ (t : ℝ) in Set.Ici (1 / ε), g t ∂volume)) := by
      have h1 : ∫⁻ t in Set.Ioi 0, g t ≤ ∫⁻ t in (Set.Ioc 0 1 ∪ Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε)), g t :=
        lintegral_mono_set h_cover
      rw [h_set_assoc] at h1
      have h2 : ∫⁻ (t : ℝ) in (Set.Ioc 0 1 ∪ (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε))), g t ∂volume ≤
          (∫⁻ (t : ℝ) in Set.Ioc 0 1, g t ∂volume) +
          ∫⁻ (t : ℝ) in (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε)), g t ∂volume :=
        lintegral_union_le g (Set.Ioc 0 1) (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε))
      have h3 : ∫⁻ (t : ℝ) in (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε)), g t ∂volume ≤
          (∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), g t ∂volume) +
          (∫⁻ (t : ℝ) in Set.Ici (1 / ε), g t ∂volume) :=
        lintegral_union_le g (Set.Ioc 1 (1 / ε)) (Set.Ici (1 / ε))
      calc
        ∫⁻ t in Set.Ioi 0, g t
          ≤ ∫⁻ t in (Set.Ioc 0 1 ∪ (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε))), g t := h1
        _ ≤ (∫⁻ t in Set.Ioc 0 1, g t) + ∫⁻ t in (Set.Ioc 1 (1 / ε) ∪ Set.Ici (1 / ε)), g t := h2
        _ ≤ (∫⁻ t in Set.Ioc 0 1, g t) + ((∫⁻ t in Set.Ioc 1 (1 / ε), g t) + (∫⁻ t in Set.Ici (1 / ε), g t)) := by
          gcongr
    -- Piece 3 is zero
    have h_piece3 : ∫⁻ (t : ℝ) in Set.Ici (1 / ε), g t ∂volume = 0 := by
      have h4 : ∀ t ∈ Set.Ici (1 / ε), g t = 0 := by
        intro t ht
        have h5 : μ {y : ℝ | t < h y} = 0 := h_set_empty t ht
        have h6 : g t = μ {y : ℝ | t < h y} * ENNReal.ofReal (t ^ (s - 1)) := by rfl
        rw [h6, h5]; simp
      have h_ms : MeasurableSet (Set.Ici (1 / ε)) := measurableSet_Ici
      have h6 : g =ᵐ[volume.restrict (Set.Ici (1 / ε))] 0 := by
        filter_upwards [self_mem_ae_restrict h_ms] with t ht
        exact h4 t ht
      rw [lintegral_congr_ae h6]; simp
    -- Bound piece 1
    have h_piece1 : ∫⁻ (t : ℝ) in Set.Ioc 0 1, g t ∂volume ≤
        ∫⁻ (t : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1)) ∂volume := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      have h_t_pos : 0 < t := ht.1
      have h_t_le1 : t ≤ 1 := ht.2
      have h_b : μ {y : ℝ | t < h y} ≤ 1 := h_bound1 t h_t_pos h_t_le1
      have h_tpow_nonneg : 0 ≤ t ^ (s - 1) := Real.rpow_nonneg h_t_pos.le _
      calc
        g t = μ {y : ℝ | t < h y} * ENNReal.ofReal (t ^ (s - 1)) := by rfl
        _ ≤ (1 : ENNReal) * ENNReal.ofReal (t ^ (s - 1)) := by gcongr <;> exact_mod_cast h_b
        _ = ENNReal.ofReal (t ^ (s - 1)) := by simp
    -- Bound piece 2
    have h_piece2 : ∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), g t ∂volume ≤
        ∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1)) ∂volume := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      have h_t_gt1 : 1 < t := ht.1
      have h_t_le : t ≤ 1 / ε := ht.2
      have h_t_pos : 0 < t := by linarith
      by_cases h_t_lt : t < 1 / ε
      · have h_b : μ {y : ℝ | t < h y} ≤ ENNReal.ofReal (C * (1 / t) ^ τ) :=
          h_bound2 t h_t_gt1 h_t_lt
        have h1 : (1 / t) ^ τ = t ^ (-τ) := by
          have h11 : 1 / t = t ^ (-1 : ℝ) := by
            simp [Real.rpow_neg_one] <;> field_simp
          rw [h11, ← Real.rpow_mul h_t_pos.le] <;> ring_nf
        have h2 : t ^ (-τ) * t ^ (s - 1) = t ^ (s - τ - 1) := by
          have h21 : t ^ ((-τ) + (s - 1)) = t ^ (-τ) * t ^ (s - 1) :=
            Real.rpow_add h_t_pos (-τ) (s - 1)
          have h22 : t ^ (-τ) * t ^ (s - 1) = t ^ ((-τ) + (s - 1)) := h21.symm
          rw [h22]
          have h23 : (-τ) + (s - 1) = s - τ - 1 := by ring
          rw [h23]
        have h_alg : C * (1 / t) ^ τ * t ^ (s - 1) = C * t ^ (s - τ - 1) := by
          rw [h1]
          have h_assoc : C * t ^ (-τ) * t ^ (s - 1) = C * (t ^ (-τ) * t ^ (s - 1)) := by ring
          rw [h_assoc, h2]
        have h_nonneg : 0 ≤ C * t ^ (s - τ - 1) := by
          apply mul_nonneg hC_nonneg
          exact Real.rpow_nonneg (by linarith) _
        have h_pos : 0 ≤ C * (1 / t) ^ τ * t ^ (s - 1) := by
          rw [h_alg]; exact h_nonneg
        have h_pos1 : 0 ≤ C * (1 / t) ^ τ := by positivity
        have h_mul : ENNReal.ofReal (C * (1 / t) ^ τ) * ENNReal.ofReal (t ^ (s - 1)) =
            ENNReal.ofReal (C * (1 / t) ^ τ * t ^ (s - 1)) := by
          exact Eq.symm (ofReal_mul h_pos1)
        calc
          g t = μ {y : ℝ | t < h y} * ENNReal.ofReal (t ^ (s - 1)) := by rfl
          _ ≤ ENNReal.ofReal (C * (1 / t) ^ τ) * ENNReal.ofReal (t ^ (s - 1)) := by gcongr <;> exact h_b
          _ = ENNReal.ofReal (C * (1 / t) ^ τ * t ^ (s - 1)) := h_mul
          _ = ENNReal.ofReal (C * t ^ (s - τ - 1)) := by rw [h_alg]
      · have h_eq : t = 1 / ε := by linarith
        have h_empty : μ {y : ℝ | t < h y} = 0 := h_set_empty t (by linarith)
        have h_gt : g t = 0 := by
          rw [show g t = μ {y : ℝ | t < h y} * ENNReal.ofReal (t ^ (s - 1)) from rfl, h_empty]
          <;> simp
        rw [h_gt]
        simp
    have h_main_bound : ENNReal.ofReal s * ∫⁻ (t : ℝ) in Set.Ioi 0, g t ∂volume ≤
        ENNReal.ofReal s *
        ((∫⁻ (t : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1)) ∂volume) +
        (∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1)) ∂volume)) := by
      have h_inner : ∫⁻ (t : ℝ) in Set.Ioi 0, g t ∂volume ≤
          (∫⁻ (t : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1)) ∂volume) +
          (∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1)) ∂volume) := by
        calc
          ∫⁻ t in Set.Ioi 0, g t
            ≤ (∫⁻ t in Set.Ioc 0 1, g t) + ((∫⁻ t in Set.Ioc 1 (1 / ε), g t) + (∫⁻ t in Set.Ici (1 / ε), g t)) := h_union_le
          _ = (∫⁻ t in Set.Ioc 0 1, g t) + (∫⁻ t in Set.Ioc 1 (1 / ε), g t) := by rw [h_piece3]; simp
          _ ≤ (∫⁻ t in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1))) + (∫⁻ t in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1))) := by
            exact add_le_add h_piece1 h_piece2
      exact mul_le_mul_of_nonneg_left h_inner (by positivity)
    have h_final : ENNReal.ofReal s *
        ((∫⁻ (t : ℝ) in Set.Ioc 0 1, ENNReal.ofReal (t ^ (s - 1)) ∂volume) +
        (∫⁻ (t : ℝ) in Set.Ioc 1 (1 / ε), ENNReal.ofReal (C * t ^ (s - τ - 1)) ∂volume)) ≤
      ENNReal.ofReal (1 + C * s / (τ - s)) := by
      rw [lintegral_rpow_Ioc01 hs, lintegral_rpow_Ioc1 hs hst hε_pos hε_le_one hC_nonneg]
      have h_nonneg1 : 0 ≤ 1 / s := by positivity
      have h5 : 0 ≤ ε ^ (τ - s) := by positivity
      have h6 : ε ^ (τ - s) ≤ 1 := by
        have h7 : 0 ≤ τ - s := by linarith
        exact Real.rpow_le_one hε_pos.le hε_le_one h7
      have h_nonneg2 : 0 ≤ C / (τ - s) * (1 - ε ^ (τ - s)) := by
        apply mul_nonneg
        · apply div_nonneg hC_nonneg; linarith
        · linarith
      have h_mul : ENNReal.ofReal s *
          (ENNReal.ofReal (1 / s) + ENNReal.ofReal (C / (τ - s) * (1 - ε ^ (τ - s)))) =
        ENNReal.ofReal (s * (1 / s + C / (τ - s) * (1 - ε ^ (τ - s)))) := by
        rw [← ENNReal.ofReal_add h_nonneg1 h_nonneg2, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
      rw [h_mul]
      have h_ineq : s * (1 / s + C / (τ - s) * (1 - ε ^ (τ - s))) ≤ 1 + C * s / (τ - s) := by
        have h7 : s * (1 / s + C / (τ - s) * (1 - ε ^ (τ - s))) =
            1 + C * s / (τ - s) * (1 - ε ^ (τ - s)) := by
          field_simp [hs.ne', hτ_sub_pos.ne'] <;> ring
        rw [h7]
        have h8 : 0 ≤ C * s / (τ - s) := by
          apply div_nonneg
          · exact mul_nonneg hC_nonneg hs.le
          · linarith
        nlinarith
      exact ENNReal.ofReal_le_ofReal h_ineq
    exact le_trans h_main_bound h_final

/-- Helper inequality: `(√5)^s * (1 + C_μ * s/(τ-s)) ≤ C_Frost`. -/
lemma sqrt5_C_Frost_bound (s τ C_μ : ℝ) (hs_pos : 0 < s) (hst : s < τ)
    (hCμ_pos : 0 < C_μ) (h_sqrt5_le : Real.sqrt 5 ≤ 6 * Real.sqrt 2)
    (C_Frost : ℝ)
    (hC_Frost_def : C_Frost = (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s))) :
    (Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s)) ≤ C_Frost := by
  rw [hC_Frost_def]
  have h_pos1 : 0 ≤ Real.sqrt 5 := by positivity
  have h_pos2 : 0 ≤ 6 * Real.sqrt 2 := by positivity
  have h16 : (Real.sqrt 5) ^ s ≤ (6 * Real.sqrt 2) ^ s :=
    Real.rpow_le_rpow h_pos1 h_sqrt5_le hs_pos.le
  have h17 : 0 ≤ (Real.sqrt 5) ^ s := by positivity
  have h18 : 0 ≤ 1 + C_μ * s / (τ - s) := by positivity
  have h20 : 0 ≤ s / (τ - s) := by positivity
  have h21 : 0 ≤ C_μ := by linarith
  have h19 : 1 + C_μ * s / (τ - s) ≤ (C_μ + 1) * (1 + s / (τ - s)) := by
    have h : (C_μ + 1) * (1 + s / (τ - s)) - (1 + C_μ * s / (τ - s)) = s / (τ - s) + C_μ := by ring
    have h' : 0 ≤ s / (τ - s) + C_μ := by linarith
    linarith [h, h']
  have h22 : (Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s)) ≤
      (6 * Real.sqrt 2) ^ s * ((C_μ + 1) * (1 + s / (τ - s))) := by
    nlinarith [h16, h19, h17, h18]
  have h23 : (6 * Real.sqrt 2) ^ s * ((C_μ + 1) * (1 + s / (τ - s))) =
      (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s)) := by ring
  rw [h23] at h22
  exact h22

/-- Helper inequality: `1 + C_μ * s/(τ-s) ≤ C_Frost * v^(-s)` when `0 < v ≤ 4√2`. -/
lemma C_Frost_large_v0_bound (s τ C_μ v : ℝ) (hs_pos : 0 < s) (hst : s < τ)
    (hCμ_pos : 0 < C_μ) (hv_pos : 0 < v) (hv_bound : v ≤ 6 * Real.sqrt 2)
    (C_Frost : ℝ)
    (hC_Frost_def : C_Frost = (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s))) :
    1 + C_μ * s / (τ - s) ≤ C_Frost * v ^ (-s) := by
  have h_v_nonneg : 0 ≤ v := hv_pos.le
  have h14 : v ^ (-s) ≥ (6 * Real.sqrt 2) ^ (-s) := by
    have h141 : v ^ s ≤ (6 * Real.sqrt 2) ^ s :=
      Real.rpow_le_rpow h_v_nonneg hv_bound hs_pos.le
    have h142 : 0 < v ^ s := by positivity
    have h143 : 0 < (6 * Real.sqrt 2) ^ s := by positivity
    have h144 : ((6 * Real.sqrt 2) ^ s)⁻¹ ≤ (v ^ s)⁻¹ := by gcongr
    have h145 : v ^ (-s) = (v ^ s)⁻¹ := by
      rw [Real.rpow_neg] <;> linarith
    have h146 : (6 * Real.sqrt 2) ^ (-s) = ((6 * Real.sqrt 2) ^ s)⁻¹ := by
      rw [Real.rpow_neg] <;> linarith
    rw [h145, h146]; exact h144
  have hC_Frost_pos : 0 < C_Frost := by
    rw [hC_Frost_def] <;> positivity
  have h17 : C_Frost * v ^ (-s) ≥ C_Frost * (6 * Real.sqrt 2) ^ (-s) :=
    mul_le_mul_of_nonneg_left h14 hC_Frost_pos.le
  have h18 : C_Frost * (6 * Real.sqrt 2) ^ (-s) = (C_μ + 1) * (1 + s / (τ - s)) := by
    have h19 : 0 < 6 * Real.sqrt 2 := by positivity
    have h20 : (6 * Real.sqrt 2) ^ s * (6 * Real.sqrt 2) ^ (-s) = 1 := by
      have h_pos : 0 < (6 * Real.sqrt 2) ^ s := by positivity
      have h_neg : (6 * Real.sqrt 2) ^ (-s) = ((6 * Real.sqrt 2) ^ s)⁻¹ := by
        rw [Real.rpow_neg] <;> linarith
      rw [h_neg]
      field_simp [h_pos.ne']
    calc
      C_Frost * (6 * Real.sqrt 2) ^ (-s)
        = ((C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s))) * (6 * Real.sqrt 2) ^ (-s) := by rw [hC_Frost_def]
      _ = (C_μ + 1) * ((6 * Real.sqrt 2) ^ s * (6 * Real.sqrt 2) ^ (-s)) * (1 + s / (τ - s)) := by ring
      _ = (C_μ + 1) * (1 + s / (τ - s)) := by rw [h20] <;> ring
  have h20 : 0 ≤ s / (τ - s) := by positivity
  have h21 : 0 ≤ C_μ := by linarith
  have h22 : 1 + C_μ * s / (τ - s) ≤ (C_μ + 1) * (1 + s / (τ - s)) := by
    have h : (C_μ + 1) * (1 + s / (τ - s)) - (1 + C_μ * s / (τ - s)) = s / (τ - s) + C_μ := by ring
    have h' : 0 ≤ s / (τ - s) + C_μ := by linarith
    linarith [h, h']
  calc 1 + C_μ * s / (τ - s)
      ≤ (C_μ + 1) * (1 + s / (τ - s)) := h22
    _ = C_Frost * (6 * Real.sqrt 2) ^ (-s) := h18.symm
    _ ≤ C_Frost * v ^ (-s) := h17

/-- Helper: `(v / √5) ^ (-s) = (√5) ^ s * v ^ (-s)` for `v > 0`. -/
lemma rpow_div_sqrt5_identity (v s : ℝ) (hv_pos : 0 < v) (hs_pos : 0 < s) :
    (v / Real.sqrt 5) ^ (-s) = (Real.sqrt 5) ^ s * v ^ (-s) := by
  have h_sqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have h_sqrt5_nonneg : 0 ≤ Real.sqrt 5 := by positivity
  have h_v_nonneg : 0 ≤ v := hv_pos.le
  have h1 : (v / Real.sqrt 5) ^ (-s) = (v * (Real.sqrt 5)⁻¹) ^ (-s) := by
    have h_eq : v / Real.sqrt 5 = v * (Real.sqrt 5)⁻¹ := by rw [div_eq_mul_inv]
    rw [h_eq]
  rw [h1]
  have h2 : (v * (Real.sqrt 5)⁻¹) ^ (-s) = v ^ (-s) * (Real.sqrt 5)⁻¹ ^ (-s) := by
    rw [Real.mul_rpow h_v_nonneg (by positivity)]
  rw [h2]
  have h3 : (Real.sqrt 5)⁻¹ ^ (-s) = (Real.sqrt 5) ^ s := by
    have h4 : (Real.sqrt 5)⁻¹ ^ (-s) = ((Real.sqrt 5) ^ (-s))⁻¹ :=
      Real.inv_rpow h_sqrt5_nonneg (-s)
    have h5 : (Real.sqrt 5) ^ (-s) = ((Real.sqrt 5) ^ s)⁻¹ :=
      Real.rpow_neg h_sqrt5_nonneg s
    rw [h4, h5]
    have h_pos : 0 < (Real.sqrt 5) ^ s := by positivity
    have h6 : (((Real.sqrt 5) ^ s)⁻¹)⁻¹ = (Real.sqrt 5) ^ s := by
      field_simp [h_pos.ne']
    exact h6
  rw [h3] <;> ring

/-! ## Directional energy integral -/

set_option maxHeartbeats 500000 in
/-- Frostman strip estimate with bounded vector.

For `v ≤ 4√2` (differences in `[-2,2]²`), the directional integral is bounded
by `C_Frost · max(v, δ)^{-s}` where `s = 2κ`. -/
lemma directional_energy_integral
    {δ τ κ C_μ : ℝ} {μ : Measure ℝ}
    (hτ_pos : 0 < τ) (hκ_pos : 0 < κ) (hτ_gt_2κ : τ > 2 * κ)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hCμ_pos : 0 < C_μ)
    (hμ_frost : IsDirectionFrostman δ τ C_μ μ)
    (hμ_support_bdd : μ.support ⊆ Set.Icc 0 1)
    {v0 v1 : ℝ} (hv_ne_zero : (v0, v1) ≠ (0, 0))
    (hv_bound : Real.sqrt (v0^2 + v1^2) ≤ 6 * Real.sqrt 2) :
    ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-2 * κ)) ∂μ ≤
      ENNReal.ofReal ((C_μ + 1) * (6 * Real.sqrt 2) ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ))) *
      ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-2 * κ)) := by
  set s : ℝ := 2 * κ with hs_def
  have hs_pos : 0 < s := by positivity
  have hst : s < τ := by linarith
  set v : ℝ := Real.sqrt (v0^2 + v1^2) with hv_def
  have h_v_nonneg : 0 ≤ v := Real.sqrt_nonneg _
  have h_v2 : v^2 = v0^2 + v1^2 := by
    rw [hv_def, Real.sq_sqrt (by positivity)]
  have hτ_sub_pos : 0 < τ - s := by linarith
  let C_Frost : ℝ := (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s))
  have hC_Frost_pos : 0 < C_Frost := by positivity
  have h4sqrt2_ge1 : 1 ≤ 6 * Real.sqrt 2 := by
    have h1 : 1 ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have h2 : 1 ≤ 6 * Real.sqrt 2 := by
      have h3 : 0 < Real.sqrt 2 := by positivity
      nlinarith [h1]
    exact h2
  have hC_Frost_ge_one : 1 ≤ C_Frost := by
    dsimp only [C_Frost]
    have h1 : 1 ≤ C_μ + 1 := by linarith
    have h2 : 1 ≤ (6 * Real.sqrt 2) ^ s := Real.one_le_rpow h4sqrt2_ge1 hs_pos.le
    have h3 : 0 ≤ s / (τ - s) := by positivity
    have h4 : 1 ≤ 1 + s / (τ - s) := by linarith
    have h5 : 0 ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s := by positivity
    have h6 : 1 ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s := by
      have h_pos2 : 0 ≤ (6 * Real.sqrt 2) ^ s := by positivity
      have h61 : 1 * 1 ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s := mul_le_mul h1 h2 (by norm_num) (by linarith)
      simpa using h61
    have h7 : (C_μ + 1) * (6 * Real.sqrt 2) ^ s ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s)) := by
      exact le_mul_of_one_le_right h5 h4
    exact le_trans h6 h7
  have h_sqrt5_le : Real.sqrt 5 ≤ 6 * Real.sqrt 2 := by
    have h1 : Real.sqrt 5 ≤ Real.sqrt 72 := Real.sqrt_le_sqrt (by norm_num)
    have h2 : Real.sqrt 72 = 6 * Real.sqrt 2 := by
      rw [show (72 : ℝ) = 36 * 2 by norm_num, Real.sqrt_mul (by norm_num)] <;> norm_num
    linarith
  have h_goal : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
      ENNReal.ofReal C_Frost * ENNReal.ofReal ((max v δ) ^ (-s)) := by
    -- Case 1: v ≤ δ
    by_cases h_v_leδ : v ≤ δ
    · have h_max : max v δ = δ := by rw [max_eq_right] <;> linarith
      have h_bound : ∀ y, (max (|v0 * y + v1|) δ) ^ (-s) ≤ δ ^ (-s) := by
        intro y
        have h5 : δ ≤ max (|v0 * y + v1|) δ := le_max_right _ _
        have h6 : 0 < δ := hδ_pos
        have h7 : 0 ≤ max (|v0 * y + v1|) δ := by positivity
        have h8 : δ ^ s ≤ (max (|v0 * y + v1|) δ) ^ s :=
          Real.rpow_le_rpow h6.le h5 (by linarith)
        have h9 : 0 < δ ^ s := by positivity
        have h10 : ((max (|v0 * y + v1|) δ) ^ s)⁻¹ ≤ (δ ^ s)⁻¹ := by gcongr
        have h11 : (max (|v0 * y + v1|) δ) ^ (-s) = ((max (|v0 * y + v1|) δ) ^ s)⁻¹ := by
          rw [Real.rpow_neg] <;> linarith
        have h12 : δ ^ (-s) = (δ ^ s)⁻¹ := by
          rw [Real.rpow_neg] <;> linarith
        rw [h11, h12]
        exact h10
      have h7 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
          ENNReal.ofReal (δ ^ (-s)) := by
        have h8 : ∀ y, ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ≤
            ENNReal.ofReal (δ ^ (-s)) := by
          intro y; exact ENNReal.ofReal_le_ofReal (h_bound y)
        have h9 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
            ∫⁻ (y : ℝ), ENNReal.ofReal (δ ^ (-s)) ∂μ := lintegral_mono h8
        have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal (δ ^ (-s)) ∂μ = ENNReal.ofReal (δ ^ (-s)) := by
          rw [lintegral_const, hμ_frost.1] <;> simp
        rw [h10] at h9
        exact h9
      rw [h_max]
      have h9 : ENNReal.ofReal (δ ^ (-s)) ≤
          ENNReal.ofReal C_Frost * ENNReal.ofReal (δ ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by
          have h10 : 0 < δ ^ (-s) := by positivity
          nlinarith [hC_Frost_ge_one])
      exact le_trans h7 h9
    -- Case 2: v > δ
    have h_v_gtδ : δ < v := by linarith
    have h_v_pos : 0 < v := by linarith
    have h_max : max v δ = v := by rw [max_eq_left] <;> linarith
    rw [h_max]
    by_cases h_v0 : v0 = 0
    · have h_v1_ne_zero : v1 ≠ 0 := by
        intro h; simp [h_v0, h] at hv_ne_zero <;> tauto
      have h_v_eq : v = |v1| := by
        rw [hv_def, h_v0]; simp [Real.sqrt_sq_eq_abs] <;> ring
      have h_abs : ∀ y, |v0 * y + v1| = |v1| := by
        intro y; rw [h_v0]; ring_nf
      have h_gtδ : |v1| > δ := by linarith [h_v_eq]
      have h_max2 : ∀ y, max (|v0 * y + v1|) δ = |v1| := by
        intro y; rw [h_abs y, max_eq_left] <;> linarith
      have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ =
          ENNReal.ofReal (|v1| ^ (-s)) := by
        simp_rw [h_max2]
        rw [lintegral_const, hμ_frost.1] <;> simp
      rw [h10]
      have h11 : |v1| = v := by linarith [h_v_eq]
      rw [h11]
      have h12 : ENNReal.ofReal (v ^ (-s)) ≤
          ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by
          have h13 : 0 < v ^ (-s) := by positivity
          nlinarith [hC_Frost_ge_one])
      exact h12
    · -- v0 ≠ 0
      have h_v0_ne_zero : v0 ≠ 0 := h_v0
      set y0 : ℝ := -v1 / v0 with hy0_def
      have h_abs2 : ∀ y : ℝ, |v0 * y + v1| = |v0| * dist y y0 := by
        intro y
        have h6 : v0 * y + v1 = v0 * (y - y0) := by
          dsimp only [y0]; field_simp [h_v0_ne_zero] <;> ring
        rw [h6, abs_mul] <;> rfl
      by_cases h_small_v0 : |v0| < v / Real.sqrt 5
      · -- Sub-case A: |v0| < v/√5
        have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        have h1 : v1^2 > 4 * v^2 / 5 := by
          have h2 : v0^2 < v^2 / 5 := by
            have h3 : |v0| < v / Real.sqrt 5 := h_small_v0
            have h4 : |v0| ^ 2 < (v / Real.sqrt 5) ^ 2 := by gcongr
            have h5 : |v0| ^ 2 = v0^2 := by simp
            have h6 : (v / Real.sqrt 5) ^ 2 = v^2 / 5 := by
              calc (v / Real.sqrt 5) ^ 2
                  = v^2 / (Real.sqrt 5)^2 := by ring
                _ = v^2 / 5 := by rw [h_sqrt5_sq]
            rw [h5, h6] at h4; exact h4
          nlinarith [h_v2]
        have h_v1_gt : |v1| > 2 * v / Real.sqrt 5 := by
          have h_pos : 0 < 2 * v / Real.sqrt 5 := by positivity
          have h9 : |v1| ^ 2 > (2 * v / Real.sqrt 5) ^ 2 := by
            have h10 : |v1| ^ 2 = v1^2 := by simp
            have h11 : (2 * v / Real.sqrt 5) ^ 2 = 4 * v^2 / 5 := by
              calc (2 * v / Real.sqrt 5) ^ 2
                  = 4 * v^2 / (Real.sqrt 5)^2 := by ring
                _ = 4 * v^2 / 5 := by rw [h_sqrt5_sq]
            rw [h10, h11]; exact h1
          nlinarith [abs_nonneg v1]
        have h_ge : ∀ y ∈ Set.Icc (0 : ℝ) 1, |v0 * y + v1| ≥ v / Real.sqrt 5 := by
          intro y hy
          have h_y1 : 0 ≤ y := hy.1
          have h_y2 : y ≤ 1 := hy.2
          have h_tri : |v1| ≤ |v0 * y + v1| + |v0 * y| := by
            calc |v1| = |(v0 * y + v1) - v0 * y| := by ring_nf
                 _ ≤ |v0 * y + v1| + |v0 * y| := by exact abs_sub _ _
          have h_absy : |v0 * y| = |v0| * y := by
            rw [abs_mul, abs_of_nonneg h_y1] <;> ring
          have h_main : |v0 * y + v1| ≥ |v1| - |v0| * y := by linarith
          have h13 : |v0| * y ≤ |v0| := by
            calc |v0| * y ≤ |v0| * 1 := by gcongr
                 _ = |v0| := by ring
          have h14 : |v1| - |v0| * y ≥ |v1| - |v0| := by linarith
          set q : ℝ := v / Real.sqrt 5 with hq
          have h15 : |v1| > 2 * q := by
            have h151 : |v1| > 2 * v / Real.sqrt 5 := h_v1_gt
            have h152 : 2 * v / Real.sqrt 5 = 2 * q := by
              simp [hq] <;> ring
            rw [h152] at h151
            exact h151
          have h16 : |v0| < q := h_small_v0
          have h17 : |v1| - |v0| > q := by linarith
          have h18 : |v1| - |v0| * y ≥ q := by linarith
          linarith
        have h_support_ae : ∀ᵐ y ∂μ, y ∈ μ.support := by
          have h : μ (μ.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
          have h' : μ {y | y ∉ μ.support} = 0 := by
            have h_eq : {y | y ∉ μ.support} = μ.supportᶜ := by ext y; simp
            rw [h_eq]; exact h
          rw [ae_iff]; exact h'
        have h_support : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1 := by
          filter_upwards [h_support_ae] with y hy
          exact hμ_frost.2.1 hy
        have h_bound3 : ∀ᵐ y ∂μ,
            ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ≤
            ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) := by
          filter_upwards [h_support] with y hy
          have h4 : |v0 * y + v1| ≥ v / Real.sqrt 5 := h_ge y hy
          have h6 : max (|v0 * y + v1|) δ ≥ v / Real.sqrt 5 := by
            have h7 : max (|v0 * y + v1|) δ ≥ |v0 * y + v1| := le_max_left _ _
            linarith
          have h_v_sqrt5_pos : 0 < v / Real.sqrt 5 := by positivity
          have h_max_nonneg : 0 ≤ max (|v0 * y + v1|) δ := by positivity
          have h9 : (v / Real.sqrt 5) ^ s ≤ (max (|v0 * y + v1|) δ) ^ s :=
            Real.rpow_le_rpow h_v_sqrt5_pos.le h6 (by linarith)
          have h10 : 0 < (v / Real.sqrt 5) ^ s := by positivity
          have h11 : ((max (|v0 * y + v1|) δ) ^ s)⁻¹ ≤ ((v / Real.sqrt 5) ^ s)⁻¹ := by
            gcongr
          have h12 : (max (|v0 * y + v1|) δ) ^ (-s) = ((max (|v0 * y + v1|) δ) ^ s)⁻¹ := by
            rw [Real.rpow_neg] <;> linarith
          have h13 : (v / Real.sqrt 5) ^ (-s) = ((v / Real.sqrt 5) ^ s)⁻¹ := by
            rw [Real.rpow_neg] <;> linarith
          have h14 : (max (|v0 * y + v1|) δ) ^ (-s) ≤ (v / Real.sqrt 5) ^ (-s) := by
            rw [h12, h13]; exact h11
          have h15 : (v / Real.sqrt 5) ^ (-s) = (Real.sqrt 5 / v) ^ s := by
            have h16 : v / Real.sqrt 5 = (Real.sqrt 5 / v)⁻¹ := by
              field_simp [h_v_pos.ne'] <;> ring
            rw [h16]
            have h17 : 0 < Real.sqrt 5 / v := by positivity
            have h18 : (Real.sqrt 5 / v)⁻¹ ^ (-s) = ((Real.sqrt 5 / v) ^ (-s))⁻¹ := by
              rw [Real.inv_rpow] <;> linarith
            rw [h18]
            have h19 : (Real.sqrt 5 / v) ^ (-s) = ((Real.sqrt 5 / v) ^ s)⁻¹ := by
              rw [Real.rpow_neg] <;> linarith
            rw [h19] <;> field_simp
          rw [h15] at h14
          exact ENNReal.ofReal_le_ofReal h14
        have h9_int : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
            ∫⁻ (y : ℝ), ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) ∂μ :=
          lintegral_mono_ae h_bound3
        have h9_const : ∫⁻ (y : ℝ), ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) ∂μ =
            ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) := by
          rw [lintegral_const, hμ_frost.1] <;> simp
        have h9 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
            ENNReal.ofReal ((Real.sqrt 5 / v) ^ s) := by
          rw [h9_const] at h9_int; exact h9_int
        have h10 : (Real.sqrt 5 / v) ^ s = (Real.sqrt 5) ^ s * v ^ (-s) := by
          have h_sqrt5_pos : 0 < Real.sqrt 5 := by positivity
          have h1 : (Real.sqrt 5 / v) ^ s = (Real.sqrt 5 * v⁻¹) ^ s := by
            have h_eq : Real.sqrt 5 / v = Real.sqrt 5 * v⁻¹ := by
              rw [div_eq_mul_inv]
            rw [h_eq]
          rw [h1]
          have h2 : (Real.sqrt 5 * v⁻¹) ^ s = (Real.sqrt 5) ^ s * v⁻¹ ^ s := by
            have h_v_inv_nonneg : 0 ≤ v⁻¹ := by positivity
            rw [Real.mul_rpow (by positivity) h_v_inv_nonneg]
          rw [h2]
          have h3 : v⁻¹ ^ s = v ^ (-s) := by
            have h31 : v⁻¹ ^ s = (v ^ s)⁻¹ := by
              rw [Real.inv_rpow] <;> linarith
            have h32 : v ^ (-s) = (v ^ s)⁻¹ := by
              rw [Real.rpow_neg] <;> linarith
            rw [h31, ←h32]
          rw [h3]
        rw [h10] at h9
        have h11 : (Real.sqrt 5) ^ s ≤ C_Frost := by
          dsimp only [C_Frost]
          have h12 : (Real.sqrt 5) ^ s ≤ (6 * Real.sqrt 2) ^ s := by
            gcongr <;> exact h_sqrt5_le
          have h13 : 0 ≤ (6 * Real.sqrt 2) ^ s := by positivity
          have h14 : 1 ≤ C_μ + 1 := by linarith
          have h15 : 0 ≤ s / (τ - s) := by positivity
          have h16 : 1 ≤ 1 + s / (τ - s) := le_add_of_nonneg_right h15
          have h17 : (6 * Real.sqrt 2) ^ s ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s := by
            have h_pos : 0 ≤ (6 * Real.sqrt 2) ^ s := by positivity
            nlinarith
          have h20 : 0 ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s := by positivity
          have h19 : (C_μ + 1) * (6 * Real.sqrt 2) ^ s ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s)) :=
            le_mul_of_one_le_right h20 h16
          calc (Real.sqrt 5) ^ s
              ≤ (6 * Real.sqrt 2) ^ s := h12
            _ ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s := h17
            _ ≤ (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s)) := h19
        have h14 : ENNReal.ofReal ((Real.sqrt 5) ^ s * v ^ (-s)) ≤
            ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          have h15 : 0 ≤ v ^ (-s) := by positivity
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h11 h15)
        exact le_trans h9 h14
      · -- Sub-case B: |v0| ≥ v/√5
        have h_large_v0 : |v0| ≥ v / Real.sqrt 5 := by linarith
        by_cases h_v0_le1 : |v0| ≤ 1
        · -- |v0| ≤ 1: factor out |v0|, use frostman with ε = δ/|v0|
          set ε : ℝ := δ / |v0| with hε_def
          have hε_pos : 0 < ε := by positivity
          have hδ_le_ε : δ ≤ ε := by
            dsimp only [ε]
            have h4 : 0 < |v0| := abs_pos.mpr h_v0_ne_zero
            have h5 : |v0| ≤ 1 := h_v0_le1
            have h6 : δ / |v0| ≥ δ / 1 := by gcongr
            simpa using h6
          have h_factor : ∀ y, max (|v0 * y + v1|) δ = |v0| * max (dist y y0) ε := by
            intro y
            rw [h_abs2 y]
            have h4 : 0 < |v0| := abs_pos.mpr h_v0_ne_zero
            by_cases h7 : dist y y0 ≤ δ / |v0|
            · have h8 : |v0| * dist y y0 ≤ δ := by
                calc |v0| * dist y y0 ≤ |v0| * (δ / |v0|) := by gcongr
                     _ = δ := by field_simp [h4.ne'] <;> ring
              have h9 : max (|v0| * dist y y0) δ = δ := by
                rw [max_eq_right h8]
              have h10 : max (dist y y0) (δ / |v0|) = δ / |v0| := by
                rw [max_eq_right h7]
              rw [h9, h10] <;> field_simp [h4.ne'] <;> ring
            · have h7' : dist y y0 > δ / |v0| := by exact lt_of_not_ge h7
              have h8 : |v0| * dist y y0 > δ := by
                calc |v0| * dist y y0 > |v0| * (δ / |v0|) := by gcongr
                     _ = δ := by field_simp [h4.ne'] <;> ring
              have h9 : max (|v0| * dist y y0) δ = |v0| * dist y y0 := by
                rw [max_eq_left (by linarith)]
              have h10 : max (dist y y0) (δ / |v0|) = dist y y0 := by
                rw [max_eq_left (by linarith)]
              rw [h9, h10] <;> ring
          have h5 : ∀ y, ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) =
              ENNReal.ofReal (|v0| ^ (-s)) * ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) := by
            intro y
            rw [h_factor y]
            have h6 : 0 < |v0| := abs_pos.mpr h_v0_ne_zero
            have h7 : 0 ≤ max (dist y y0) ε := by positivity
            have h8 : (|v0| * max (dist y y0) ε) ^ (-s) =
                |v0| ^ (-s) * (max (dist y y0) ε) ^ (-s) := by
              rw [Real.mul_rpow h6.le h7]
            rw [h8, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
          have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ =
              ENNReal.ofReal (|v0| ^ (-s)) *
              ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ := by
            simp_rw [h5]
            rw [lintegral_const_mul]
            <;> fun_prop
          rw [h10]
          have h_frost := frostman_negative_power_integral hδ_pos hδ_le_one hτ_pos hs_pos hst hμ_frost y0 ε hε_pos hδ_le_ε
          have h11 : |v0| ^ (-s) ≤ (Real.sqrt 5) ^ s * v ^ (-s) := by
            have h12 : 0 < v / Real.sqrt 5 := by positivity
            have h13 : v / Real.sqrt 5 ≤ |v0| := h_large_v0
            have h14 : (v / Real.sqrt 5) ^ s ≤ |v0| ^ s :=
              Real.rpow_le_rpow h12.le h13 (by linarith)
            have h15 : 0 < (v / Real.sqrt 5) ^ s := by positivity
            have h16 : 0 < |v0| ^ s := by positivity
            have h17 : (|v0| ^ s)⁻¹ ≤ ((v / Real.sqrt 5) ^ s)⁻¹ := by gcongr
            have h18 : |v0| ^ (-s) = (|v0| ^ s)⁻¹ := by
              rw [Real.rpow_neg] <;> linarith
            have h19 : (v / Real.sqrt 5) ^ (-s) = ((v / Real.sqrt 5) ^ s)⁻¹ := by
              rw [Real.rpow_neg] <;> linarith
            have h20 : |v0| ^ (-s) ≤ (v / Real.sqrt 5) ^ (-s) := by
              rw [h18, h19]; exact h17
            have h21 : (v / Real.sqrt 5) ^ (-s) = (Real.sqrt 5) ^ s * v ^ (-s) :=
              rpow_div_sqrt5_identity v s (by linarith) hs_pos
            rw [h21] at h20
            exact h20
          have h15 : (Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s)) ≤ C_Frost :=
            sqrt5_C_Frost_bound s τ C_μ hs_pos hst hCμ_pos h_sqrt5_le C_Frost rfl
          have h_final_ineq : |v0| ^ (-s) * (1 + C_μ * s / (τ - s)) ≤ C_Frost * v ^ (-s) := by
            have h24 : |v0| ^ (-s) * (1 + C_μ * s / (τ - s)) ≤
                (Real.sqrt 5) ^ s * v ^ (-s) * (1 + C_μ * s / (τ - s)) := by
              gcongr
              <;> exact h11
            have h25 : (Real.sqrt 5) ^ s * v ^ (-s) * (1 + C_μ * s / (τ - s)) =
                v ^ (-s) * ((Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s))) := by ring
            rw [h25] at h24
            have h26 : v ^ (-s) * ((Real.sqrt 5) ^ s * (1 + C_μ * s / (τ - s))) ≤
                v ^ (-s) * C_Frost := by
              gcongr <;> exact h15
            have h27 : v ^ (-s) * C_Frost = C_Frost * v ^ (-s) := by ring
            rw [h27] at h26
            exact le_trans h24 h26
          calc
            ENNReal.ofReal (|v0| ^ (-s)) * ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) ε) ^ (-s)) ∂μ
              ≤ ENNReal.ofReal (|v0| ^ (-s)) * ENNReal.ofReal (1 + C_μ * s / (τ - s)) := by gcongr <;> exact h_frost
            _ = ENNReal.ofReal (|v0| ^ (-s) * (1 + C_μ * s / (τ - s))) := by
                rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
            _ ≤ ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                exact ENNReal.ofReal_le_ofReal h_final_ineq
        · -- |v0| > 1: use frostman with ε = δ, absorb via v ≤ 4√2
          have h_v0_gt1 : 1 < |v0| := by linarith
          have h_ge : ∀ y, max (|v0 * y + v1|) δ ≥ max (dist y y0) δ := by
            intro y
            rw [h_abs2 y]
            have h4 : |v0| * dist y y0 ≥ dist y y0 := by
              have h5 : 1 ≤ |v0| := by linarith
              have h6 : 0 ≤ dist y y0 := dist_nonneg
              nlinarith
            have h6 : max (|v0| * dist y y0) δ ≥ max (dist y y0) δ := by
              exact max_le_max h4 (by linarith)
            exact h6
          have h10 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
              ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) δ) ^ (-s)) ∂μ := by
            have h11 : ∀ y, (max (|v0 * y + v1|) δ) ^ (-s) ≤ (max (dist y y0) δ) ^ (-s) := by
              intro y
              have h12 : 0 ≤ max (dist y y0) δ := by positivity
              have h13 : max (dist y y0) δ ≤ max (|v0 * y + v1|) δ := h_ge y
              have h14 : (max (dist y y0) δ) ^ s ≤ (max (|v0 * y + v1|) δ) ^ s :=
                Real.rpow_le_rpow h12 h13 hs_pos.le
              have h15 : 0 < (max (dist y y0) δ) ^ s := by positivity
              have h16 : 0 < (max (|v0 * y + v1|) δ) ^ s := by positivity
              have h17 : ((max (|v0 * y + v1|) δ) ^ s)⁻¹ ≤ ((max (dist y y0) δ) ^ s)⁻¹ := by gcongr
              have h18 : (max (|v0 * y + v1|) δ) ^ (-s) = ((max (|v0 * y + v1|) δ) ^ s)⁻¹ := by
                rw [Real.rpow_neg] <;> linarith
              have h19 : (max (dist y y0) δ) ^ (-s) = ((max (dist y y0) δ) ^ s)⁻¹ := by
                rw [Real.rpow_neg] <;> linarith
              rw [h18, h19]; exact h17
            have h11' : ∀ y, ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ≤
                ENNReal.ofReal ((max (dist y y0) δ) ^ (-s)) := by
              intro y
              exact ENNReal.ofReal_le_ofReal (h11 y)
            exact lintegral_mono h11'
          have h_frost := frostman_negative_power_integral hδ_pos hδ_le_one hτ_pos hs_pos hst hμ_frost y0 δ hδ_pos (by linarith)
          have h13 : 1 + C_μ * s / (τ - s) ≤ C_Frost * v ^ (-s) :=
            C_Frost_large_v0_bound s τ C_μ v hs_pos hst hCμ_pos (by linarith) hv_bound C_Frost rfl
          calc
            ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ
              ≤ ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist y y0) δ) ^ (-s)) ∂μ := h10
            _ ≤ ENNReal.ofReal (1 + C_μ * s / (τ - s)) := h_frost
            _ ≤ ENNReal.ofReal (C_Frost * v ^ (-s)) := by
                exact ENNReal.ofReal_le_ofReal h13
            _ = ENNReal.ofReal C_Frost * ENNReal.ofReal (v ^ (-s)) := by
                rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
  simpa [hs_def] using h_goal

/-! ## Main theorem -/

/-- Average projection energy bound.

Given a Frostman measure μ on directions and a measure ν supported on `[-2,2]²`,
the average over y of the Riesz energy of the projection π_{y*}ν is bounded by
a constant times the energy of ν. -/
theorem average_projection_energy_bound
    {δ τ κ C_μ : ℝ} {μ : Measure ℝ}
    {ν : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hτ_pos : 0 < τ) (hκ_pos : 0 < κ) (hτ_gt_2κ : τ > 2 * κ)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hCμ_pos : 0 < C_μ)
    (hμ_frost : IsDirectionFrostman δ τ C_μ μ)
    (hμ_support_bdd : μ.support ⊆ Set.Icc 0 1)
    (hν_support_bdd : ν.support ⊆ {p | ∀ i, p i ∈ Set.Icc (-3 : ℝ) 3}) :
    ∫⁻ (y : ℝ), rieszEnergy (2 * κ) (hδ := hδ_pos)
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) ν) ∂μ ≤
      ENNReal.ofReal (1 + (C_μ + 1) * (6 * Real.sqrt 2) ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ))) *
      rieszEnergy (2 * κ) (hδ := hδ_pos) ν := by
  let s : ℝ := 2 * κ
  let C_dir : ℝ := (C_μ + 1) * (6 * Real.sqrt 2) ^ s * (1 + s / (τ - s))
  let C_total : ℝ := 1 + C_dir
  have hτ_sub_pos : 0 < τ - s := by linarith
  have hC_dir_pos : 0 < C_dir := by positivity
  have hC_total_pos : 0 < C_total := by linarith
  have hC_total_ge_one : 1 ≤ C_total := by linarith
  let E2 := EuclideanSpace ℝ (Fin 2)
  let proj : ℝ → E2 → ℝ := fun y p => p 0 * y + p 1
  let F : ℝ → E2 → E2 → ENNReal := fun y x z =>
    ENNReal.ofReal ((max (|proj y x - proj y z|) δ) ^ (-s))
  let S : Set E2 := {p | ∀ i, p i ∈ Set.Icc (-3 : ℝ) 3}
  have hF_eq : ∀ y x z, F y x z = energyIntegrand δ κ y x z := by
    intro y x z
    have h : proj y x - proj y z = (x 0 - z 0) * y + (x 1 - z 1) := by
      dsimp only [proj] <;> ring
    simp only [F, energyIntegrand, h] <;> rfl
  -- Support bound gives a.e. membership
  have h1 : ∀ᵐ (x : E2) ∂ν, x ∈ S := by
    have h_support : ∀ᵐ (x : E2) ∂ν, x ∈ ν.support := by
      have h : ν (ν.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
      have h' : ν {x | x ∉ ν.support} = 0 := by
        have h_eq : {x | x ∉ ν.support} = ν.supportᶜ := by ext x; simp
        rw [h_eq]; exact h
      rw [ae_iff]; exact h'
    filter_upwards [h_support] with x hx
    exact hν_support_bdd hx
  -- Pointwise directional bound (a.e.)
  have h_pointwise_ae : ∀ᵐ (x : E2) ∂ν, ∀ᵐ (z : E2) ∂ν,
      ∫⁻ (y : ℝ), F y x z ∂μ ≤
        ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) := by
    filter_upwards [h1] with x hx
    have h2 : ∀ᵐ (z : E2) ∂ν, z ∈ S := by
      have h_support : ∀ᵐ (z : E2) ∂ν, z ∈ ν.support := by
        have h : ν (ν.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
        have h' : ν {z | z ∉ ν.support} = 0 := by
          have h_eq : {z | z ∉ ν.support} = ν.supportᶜ := by ext z; simp
          rw [h_eq]; exact h
        rw [ae_iff]; exact h'
      filter_upwards [h_support] with z hz
      exact hν_support_bdd hz
    filter_upwards [h2] with z hz
    let v0 := x 0 - z 0
    let v1 := x 1 - z 1
    have h_x01 : -3 ≤ x 0 := by linarith [(hx 0).1]
    have h_x02 : x 0 ≤ 3 := by linarith [(hx 0).2]
    have h_x11 : -3 ≤ x 1 := by linarith [(hx 1).1]
    have h_x12 : x 1 ≤ 3 := by linarith [(hx 1).2]
    have h_z01 : -3 ≤ z 0 := (hz 0).1
    have h_z02 : z 0 ≤ 3 := (hz 0).2
    have h_z11 : -3 ≤ z 1 := (hz 1).1
    have h_z12 : z 1 ≤ 3 := (hz 1).2
    have h_v02 : v0^2 ≤ 36 := by dsimp only [v0]; nlinarith
    have h_v12 : v1^2 ≤ 36 := by dsimp only [v1]; nlinarith
    have hv_bound : Real.sqrt (v0^2 + v1^2) ≤ 6 * Real.sqrt 2 := by
      have h : v0^2 + v1^2 ≤ 72 := by nlinarith
      have h' : Real.sqrt (v0^2 + v1^2) ≤ Real.sqrt 72 := Real.sqrt_le_sqrt h
      have h'' : Real.sqrt 72 = 6 * Real.sqrt 2 := by
        rw [show (72 : ℝ) = 36 * 2 by norm_num]
        rw [Real.sqrt_mul (by norm_num)] <;> norm_num
      rw [h''] at h'
      exact h'
    have h_abs : ∀ y, |proj y x - proj y z| = |v0 * y + v1| := by
      intro y; dsimp only [v0, v1, proj]; ring_nf
    have h_dist : dist x z = Real.sqrt (v0^2 + v1^2) := by
      have h1 : dist x z = ‖x - z‖ := by exact dist_eq_norm x z
      rw [h1]
      have h_norm_sq : ∀ (v : E2), ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        intro v
        have h3 : ‖v‖ ^ 2 = ∑ i : Fin 2, (v i)^2 := by exact EuclideanSpace.real_norm_sq_eq v
        rw [h3, Fin.sum_univ_two] <;> ring
      have h4 : ‖x - z‖ ^ 2 = (x - z) 0 ^ 2 + (x - z) 1 ^ 2 := h_norm_sq (x - z)
      have h5 : (x - z) 0 = x 0 - z 0 := by exact PiLp.sub_apply (fun x => ℝ) x z 0
      have h6 : (x - z) 1 = x 1 - z 1 := by exact PiLp.sub_apply (fun x => ℝ) x z 1
      have h7 : 0 ≤ ‖x - z‖ := by positivity
      rw [← Real.sqrt_sq h7, h4, h5, h6]
    by_cases h_v : (v0, v1) = (0, 0)
    · -- diagonal case
      have h_v0 : v0 = 0 := by simp [Prod.ext_iff] at h_v <;> tauto
      have h_v1 : v1 = 0 := by simp [Prod.ext_iff] at h_v <;> tauto
      have hF_eq2 : ∀ y, F y x z = ENNReal.ofReal (δ ^ (-s)) := by
        intro y
        have h4 : |proj y x - proj y z| = 0 := by
          rw [h_abs y, h_v0, h_v1] <;> simp
        have h5 : max (|proj y x - proj y z|) δ = δ := by
          rw [h4]
          have h6 : max (0 : ℝ) δ = δ := by
            rw [max_eq_right] <;> linarith [hδ_pos]
          exact h6
        simp only [F, h5] <;> rfl
      have h_int : ∫⁻ (y : ℝ), F y x z ∂μ = ENNReal.ofReal (δ ^ (-s)) := by
        simp_rw [hF_eq2]
        rw [lintegral_const, measure_univ] <;> simp
      have h_dist_zero : dist x z = 0 := by
        rw [h_dist, h_v0, h_v1] <;> ring
      rw [h_int, h_dist_zero]
      have h_max0 : max (0 : ℝ) δ = δ := by
        rw [max_eq_right] <;> linarith [hδ_pos]
      simp only [h_max0]
      have h6 : ENNReal.ofReal (δ ^ (-s)) ≤
          ENNReal.ofReal C_total * ENNReal.ofReal (δ ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by
          have h7 : 0 < δ ^ (-s) := by positivity
          nlinarith [hC_total_ge_one])
      exact h6
    · -- off-diagonal
      have h4 : ∫⁻ (y : ℝ), F y x z ∂μ =
          ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ := by
        congr with y; simp [F, h_abs y]
      rw [h4]
      have h5_raw := directional_energy_integral hτ_pos hκ_pos hτ_gt_2κ hδ_pos hδ_le_one hCμ_pos hμ_frost hμ_support_bdd h_v hv_bound
      have h_s_eq : s = 2 * κ := by rfl
      have h_Cdir_eq : C_dir = (C_μ + 1) * (6 * Real.sqrt 2) ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ)) := by
        dsimp only [C_dir, s] <;> rfl
      have h5 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
          ENNReal.ofReal C_dir * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) := by
        have h5' : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-2 * κ)) ∂μ ≤
            ENNReal.ofReal ((C_μ + 1) * (6 * Real.sqrt 2) ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ))) *
            ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-2 * κ)) := h5_raw
        have h_neg_eq : (-s : ℝ) = -2 * κ := by
          dsimp only [s]; ring
        have h_Cdir_eq2 : C_dir = (C_μ + 1) * (6 * Real.sqrt 2) ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ)) := by
          dsimp only [C_dir, s] <;> rfl
        simpa [h_neg_eq, h_Cdir_eq2] using h5'
      have h6 : ENNReal.ofReal C_dir * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) ≤
          ENNReal.ofReal C_total * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) := by
        have h7 : C_dir ≤ C_total := by linarith
        exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h7) (by positivity)
      have h7 : ∫⁻ (y : ℝ), ENNReal.ofReal ((max (|v0 * y + v1|) δ) ^ (-s)) ∂μ ≤
          ENNReal.ofReal C_total * ENNReal.ofReal ((max (Real.sqrt (v0^2 + v1^2)) δ) ^ (-s)) :=
        le_trans h5 h6
      rw [h_dist] at *
      exact h7
  -- Pushforward expansion
  have h_expand : ∀ (y : ℝ),
      rieszEnergy s (hδ := hδ_pos) (Measure.map (proj y) ν) =
      ∫⁻ (x : E2), ∫⁻ (z : E2), F y x z ∂ν ∂ν := by
    intro y
    simp only [rieszEnergy]
    have h := @projection_energy_to_double_integral δ κ hδ_pos hκ_pos ν _ y
    simpa [hF_eq] using h
  -- Fubini swap
  have h_fubini :
      ∫⁻ (y : ℝ), ∫⁻ (x : E2), ∫⁻ (z : E2), F y x z ∂ν ∂ν ∂μ =
      ∫⁻ (x : E2), ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ∂ν := by
    have h_meas : Measurable (fun p : ℝ × E2 × E2 => F p.1 p.2.1 p.2.2) := by
      simpa [hF_eq] using energyIntegrand_measurable hδ_pos hκ_pos
    exact general_fubini3_swap h_meas
  -- A.E. monotonicity
  have h_inner_ae : ∀ᵐ (x : E2) ∂ν,
      ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ≤
      ∫⁻ (z : E2), ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν := by
    filter_upwards [h_pointwise_ae] with x hx
    exact lintegral_mono_ae hx
  have h_main_ineq : ∫⁻ (x : E2), ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ∂ν ≤
      ∫⁻ (x : E2), ∫⁻ (z : E2), ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν :=
    lintegral_mono_ae h_inner_ae
  -- Main calculation
  calc
    ∫⁻ (y : ℝ), rieszEnergy s (hδ := hδ_pos) (Measure.map (proj y) ν) ∂μ
      = ∫⁻ (y : ℝ), ∫⁻ (x : E2), ∫⁻ (z : E2), F y x z ∂ν ∂ν ∂μ := by
        congr with y; exact h_expand y
    _ = ∫⁻ (x : E2), ∫⁻ (z : E2), ∫⁻ (y : ℝ), F y x z ∂μ ∂ν ∂ν := h_fubini
    _ ≤ ∫⁻ (x : E2), ∫⁻ (z : E2),
          ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν := h_main_ineq
    _ = ENNReal.ofReal C_total * rieszEnergy s (hδ := hδ_pos) ν := by
        have h_inner : ∀ (x : E2),
            ∫⁻ (z : E2), ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν =
            ENNReal.ofReal C_total * ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν := by
          intro x
          have h_meas_z : Measurable (fun z : E2 => ENNReal.ofReal ((max (dist x z) δ) ^ (-s))) := by fun_prop
          rw [lintegral_const_mul (ENNReal.ofReal C_total) h_meas_z]
        have h_step1 : ∫⁻ (x : E2), ∫⁻ (z : E2),
              ENNReal.ofReal C_total * ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν =
            ∫⁻ (x : E2), ENNReal.ofReal C_total *
              ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν := by
          congr with x; exact h_inner x
        rw [h_step1]
        have h_meas_x : Measurable (fun x : E2 => ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν) := by fun_prop
        rw [lintegral_const_mul (ENNReal.ofReal C_total) h_meas_x]
        have h_riesz : rieszEnergy s (hδ := hδ_pos) ν =
            ∫⁻ (x : E2), ∫⁻ (z : E2), ENNReal.ofReal ((max (dist x z) δ) ^ (-s)) ∂ν ∂ν := by
          simp [rieszEnergy] <;> rfl
        exact congr_arg (fun x => ENNReal.ofReal C_total * x) h_riesz.symm

end robust_projection_main
