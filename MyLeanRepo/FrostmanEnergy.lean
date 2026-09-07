module

/-
# Frostman Measure → Bounded Riesz Energy

If a probability measure ν on a metric space satisfies the Frostman bound
ν(B(x,r)) ≤ C' · r^s for all x, r > 0, with s > 1, then its δ-regularized
1-Riesz energy is bounded by 1 + C'/(s-1), independent of δ.

Applied to the product measure μ^×n on EuclideanSpace ℝ (Fin n), where μ is
all-scale (κ,C)-Frostman and nκ > 1, giving C' = C^n and s = nκ.

## Proof route

Layer-cake formula: for fixed x,
  ∫ max(dist(x,y), δ)^{-1} dν(y)
  = ∫_0^{δ^{-1}} ν(B(x, 1/t)) dt
  ≤ ∫_0^1 1 dt + ∫_1^{δ^{-1}} C' t^{-s} dt
  = 1 + C' (1 - δ^{s-1}) / (s-1)
  ≤ 1 + C'/(s-1).

Integrate over x (ν is probability) to get the energy bound.

## Whiteprint node
frostman_energy
-/

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric Classical BigOperators

namespace WeakTwoEndsSumProduct

/-- Integral of t^{-s} from 1 to b: (1 - b^{1-s})/(s-1). -/
private lemma integral_t_neg_s {s b : ℝ} (hs : 1 < s) (hb : 1 ≤ b) :
    ∫ t in (1 : ℝ)..b, t ^ (-s) = (1 - b ^ (1 - s)) / (s - 1) := by
  have h1 : (-s : ℝ) ≠ -1 := by linarith
  have h2 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) b := by
    rw [Set.uIcc_of_le hb]
    intro h3; linarith [h3.1]
  have h3 := integral_rpow (h := Or.inr ⟨h1, h2⟩)
  have h4 : (-s : ℝ) + 1 = 1 - s := by ring
  have h_main : (b ^ ((-s : ℝ) + 1) - (1 : ℝ) ^ ((-s : ℝ) + 1)) / ((-s : ℝ) + 1) =
      (1 - b ^ (1 - s)) / (s - 1) := by
    rw [h4]
    have h7 : (1 : ℝ) ^ (1 - s) = 1 := by simp
    have h8 : 1 - s ≠ 0 := by linarith
    have h9 : s - 1 ≠ 0 := by linarith
    rw [h7]
    field_simp [h8, h9] <;> ring
  rw [h3]
  exact h_main

/-- Inner energy bound at a single point: for a probability measure ν with
    Frostman exponent s > 1, the regularized 1-energy integral at x is
    bounded by 1 + C'/(s-1). -/
lemma frostman_energy_inner_bound
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [OpensMeasurableSpace X]
    {ν : Measure X} (hν_prob : ν Set.univ = 1)
    {s C' : ℝ} (hs : 1 < s) (hC'_pos : 0 < C')
    (hFrost : ∀ (x : X) (r : ℝ), 0 < r → ν (Metric.ball x r) ≤ ENNReal.ofReal (C' * r ^ s))
    {δ : ℝ} (hδ : 0 < δ) (x : X) :
    ∫⁻ (y : X), ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ≤
    ENNReal.ofReal (1 + C' / (s - 1)) := by
  let f : X → ℝ := fun y => (max (dist x y) δ) ^ (-1 : ℝ)
  have hf_nonneg : ∀ y, 0 ≤ f y := by intro y; positivity
  have hf_meas : Measurable f := by fun_prop
  have hsm1_pos : 0 < s - 1 := by linarith
  have hC'_div_pos : 0 < C' / (s - 1) := by positivity
  -- Layer cake
  have h1 : ∫⁻ (y : X), ENNReal.ofReal (f y) ∂ν =
      ∫⁻ (t : ℝ) in Set.Ioi (0 : ℝ), ν {y | t < f y} :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt ν
      (by filter_upwards with y; exact hf_nonneg y) hf_meas.aemeasurable
  rw [h1]
  let g : ℝ → ENNReal := fun t => ν {y | t < f y}
  -- Characterize g
  have hg_eq : ∀ (t : ℝ), 0 < t → t < δ⁻¹ → g t = ν (Metric.ball x (1 / t)) := by
    intro t ht htl
    have hδ_lt : δ < 1 / t := by
      have h_t_pos : 0 < t := ht
      have hδ_pos : 0 < δ := hδ
      have h : t < 1 / δ := by
        have h9 : t < δ⁻¹ := htl
        have h10 : (δ⁻¹ : ℝ) = 1 / δ := by exact inv_eq_one_div δ
        rw [h10] at h9
        exact h9
      have h2 : t * δ < 1 := by
        calc t * δ < (1 / δ) * δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne'] <;> ring
      calc δ
        = (t * δ) / t := by field_simp [h_t_pos.ne'] <;> ring
      _ < 1 / t := by gcongr
    have h4 : ∀ (y : X), t < f y ↔ dist x y < 1 / t := by
      intro y
      let M := max (dist x y) δ
      have hM_pos : 0 < M := by positivity
      have h_fy : f y = M⁻¹ := by
        simp only [f]
        have h10 : M ^ (-1 : ℝ) = M⁻¹ := by
          rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hM_pos.le] <;> simp
        exact h10
      have h_iff : t < f y ↔ M < 1 / t := by
        rw [h_fy]
        constructor
        · intro h
          have h9 : t * M < 1 := by
            calc t * M < M⁻¹ * M := by gcongr
            _ = 1 := by field_simp [hM_pos.ne'] <;> ring
          calc M = (t * M) / t := by field_simp [ht.ne'] <;> ring
            _ < 1 / t := by gcongr
        · intro h
          have h9 : t * M < 1 := by
            calc t * M < t * (1 / t) := by gcongr
            _ = 1 := by field_simp [ht.ne'] <;> ring
          calc t = (t * M) / M := by field_simp [hM_pos.ne'] <;> ring
            _ < M⁻¹ := by
              have h10 : (t * M) / M < 1 / M := by gcongr
              have h11 : (1 / M : ℝ) = M⁻¹ := by exact one_div M
              rw [h11] at h10; exact h10
      have h7 : M < 1 / t ↔ dist x y < 1 / t := by
        constructor
        · intro h; exact (le_max_left _ _).trans_lt h
        · intro h; exact max_lt h hδ_lt
      rw [h_iff, h7]
    have h_set : {y : X | t < f y} = Metric.ball x (1 / t) := by
      ext y
      have h10 : y ∈ {y : X | t < f y} ↔ t < f y := by simp
      have h11 : y ∈ Metric.ball x (1 / t) ↔ dist y x < 1 / t := by
        simp [Metric.mem_ball]
      have h12 : dist y x = dist x y := dist_comm y x
      rw [h10, h11, h12]
      exact h4 y
    simpa [g] using congr_arg ν h_set
  have hg_zero : ∀ (t : ℝ), δ⁻¹ ≤ t → g t = 0 := by
    intro t hle
    have h5 : ∀ (y : X), ¬(t < f y) := by
      intro y
      have h6 : f y ≤ δ⁻¹ := by
        simp only [f]
        let M := max (dist x y) δ
        have hM_pos : 0 < M := by positivity
        have h_eq : M ^ (-1 : ℝ) = M⁻¹ := by
          rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hM_pos.le] <;> simp
        rw [h_eq]
        have h7 : δ ≤ M := le_max_right _ _
        have h8 : M⁻¹ ≤ δ⁻¹ := by gcongr <;> positivity
        exact h8
      have h7 : f y ≤ t := le_trans h6 hle
      exact not_lt.mpr h7
    have h9 : {y : X | t < f y} = ∅ := by
      ext y
      simpa using h5 y
    simpa [g] using congr_arg ν h9
  -- Integral over Ioi 0 equals integral over Ioo 0 δ⁻¹
  have h_disj : Disjoint (Set.Ioo (0 : ℝ) δ⁻¹) (Set.Ici δ⁻¹) := by
    simp [Set.disjoint_left] <;> linarith
  have h_union : Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) δ⁻¹ ∪ Set.Ici δ⁻¹ := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Ici]
    constructor
    · intro h
      by_cases h2 : t < δ⁻¹
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact h.1
      · have hpos : 0 < δ⁻¹ := by positivity
        linarith
  have h_meas1 : MeasurableSet (Set.Ioo (0 : ℝ) δ⁻¹) := measurableSet_Ioo
  have h_meas2 : MeasurableSet (Set.Ici δ⁻¹) := measurableSet_Ici
  have h_int2 : ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, g t = 0 := by
    have h_le : ∀ t ∈ Set.Ici δ⁻¹, g t ≤ (0 : ENNReal) := by
      intro t ht
      have h' : g t = 0 := hg_zero t ht
      rw [h'] <;> simp
    have h' : ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, g t ≤ ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, (0 : ENNReal) :=
      MeasureTheory.setLIntegral_mono' h_meas2 h_le
    have h0 : ∫⁻ (t : ℝ) in Set.Ici δ⁻¹, (0 : ENNReal) = 0 := by simp
    rw [h0] at h'
    exact le_zero_iff.mp h'
  have h_reduce : ∫⁻ (t : ℝ) in Set.Ioi (0 : ℝ), g t =
      ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) δ⁻¹, g t := by
    rw [h_union]
    rw [MeasureTheory.lintegral_union h_meas2 h_disj]
    rw [h_int2, add_zero]
  rw [h_reduce]
  -- Now bound integral over Ioo 0 δ⁻¹
  by_cases hδge : δ ≥ 1
  · -- Case δ ≥ 1: δ⁻¹ ≤ 1, everything is bounded by 1
    have hδinv_le_one : δ⁻¹ ≤ 1 := by
      have h : δ⁻¹ ≤ 1⁻¹ := by gcongr <;> linarith
      simpa using h
    have h_ball_le_one : ∀ t ∈ Set.Ioo (0 : ℝ) δ⁻¹, g t ≤ 1 := by
      intro t ht
      have h_t_pos : 0 < t := ht.1
      have h_t_lt : t < δ⁻¹ := ht.2
      rw [hg_eq t h_t_pos h_t_lt]
      have h : ν (Metric.ball x (1 / t)) ≤ ν Set.univ := measure_mono (subset_univ _)
      rw [hν_prob] at h
      exact h
    calc ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) δ⁻¹, g t
      ≤ ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) δ⁻¹, (1 : ENNReal) := MeasureTheory.setLIntegral_mono' h_meas1 h_ball_le_one
    _ = ENNReal.ofReal δ⁻¹ := by
      rw [MeasureTheory.setLIntegral_one, Real.volume_Ioo] <;> simp [hδ.ne'] <;> norm_cast <;> linarith
    _ ≤ ENNReal.ofReal (1 + C' / (s - 1)) := by
      gcongr <;> linarith
  · -- Case δ < 1: δ⁻¹ > 1
    have hδ_lt_one : δ < 1 := by linarith
    have hδinv_gt_one : 1 < δ⁻¹ := by
      have h2 : 0 < δ := hδ
      have h3 : δ < 1 := hδ_lt_one
      have h4 : (1 : ℝ) / δ > 1 := by
        calc (1 : ℝ) / δ > 1 / 1 := by gcongr
        _ = 1 := by norm_num
      have h5 : (1 : ℝ) / δ = δ⁻¹ := by
        exact one_div δ
      rw [h5] at h4
      exact h4
    have h_disj2 : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ico (1 : ℝ) δ⁻¹) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h1 : x < 1 := hx1.2
      have h2 : 1 ≤ x := hx2.1
      linarith
    have h_union2 : Set.Ioo (0 : ℝ) δ⁻¹ = Set.Ioo (0 : ℝ) 1 ∪ Set.Ico (1 : ℝ) δ⁻¹ := by
      ext t
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ico]
      constructor
      · intro h
        have h_pos : 0 < t := h.1
        have h_lt : t < δ⁻¹ := h.2
        by_cases h2 : t < 1
        · exact Or.inl ⟨h_pos, h2⟩
        · have h3 : 1 ≤ t := by
            by_contra h4
            exact h2 (by linarith)
          exact Or.inr ⟨h3, h_lt⟩
      · rintro (h | h)
        · exact ⟨h.1, by linarith⟩
        · have h_pos2 : 0 < t := by linarith
          exact ⟨h_pos2, h.2⟩
    have h_meas3 : MeasurableSet (Set.Ioo (0 : ℝ) 1) := measurableSet_Ioo
    have h_meas4 : MeasurableSet (Set.Ico (1 : ℝ) δ⁻¹) := measurableSet_Ico
    rw [h_union2]
    rw [MeasureTheory.lintegral_union h_meas4 h_disj2]
    -- Bound first part: t ∈ (0,1), ν(ball x (1/t)) ≤ 1
    have h_first : ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, g t ≤ 1 := by
      have h_ball_le_one : ∀ t ∈ Set.Ioo (0 : ℝ) 1, g t ≤ 1 := by
        intro t ht
        have h_t_pos : 0 < t := ht.1
        have h_t_lt : t < 1 := ht.2
        have h_t_lt2 : t < δ⁻¹ := by linarith
        rw [hg_eq t h_t_pos h_t_lt2]
        have h : ν (Metric.ball x (1 / t)) ≤ ν Set.univ := measure_mono (subset_univ _)
        rw [hν_prob] at h; exact h
      calc ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, g t
        ≤ ∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, (1 : ENNReal) := MeasureTheory.setLIntegral_mono' h_meas3 h_ball_le_one
      _ = 1 := by
        rw [MeasureTheory.setLIntegral_one, Real.volume_Ioo] <;> simp
    -- Bound second part: t ∈ [1, δ⁻¹), ν(ball x (1/t)) ≤ C' * t^{-s}
    have h_second : ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, g t ≤
        ENNReal.ofReal (C' / (s - 1)) := by
      have h_ball_le : ∀ t ∈ Set.Ico (1 : ℝ) δ⁻¹, g t ≤ ENNReal.ofReal (C' * t ^ (-s)) := by
        intro t ht
        have h_t_pos : 0 < t := zero_lt_one.trans_le ht.1
        have h_t_ge_one : 1 ≤ t := ht.1
        have h_t_lt : t < δ⁻¹ := ht.2
        rw [hg_eq t h_t_pos h_t_lt]
        have h1 : 0 < 1 / t := by positivity
        have h2 : 1 / t ≤ 1 := by
          apply (div_le_one (by linarith)).mpr; linarith
        have h3 : ν (Metric.ball x (1 / t)) ≤ ENNReal.ofReal (C' * (1 / t) ^ s) :=
          hFrost x (1 / t) h1
        have h4 : C' * (1 / t) ^ s = C' * t ^ (-s) := by
          have h5 : (1 / t) ^ s = (t ^ s)⁻¹ := by
            have h6 : (1 / t) = t⁻¹ := by field_simp [h_t_pos.ne']
            rw [h6]
            exact Real.inv_rpow h_t_pos.le s
          have h7 : t ^ (-s) = (t ^ s)⁻¹ := Real.rpow_neg h_t_pos.le s
          rw [h5, h7]
        rw [h4] at h3; exact h3
      calc ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, g t
        ≤ ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, ENNReal.ofReal (C' * t ^ (-s)) :=
          MeasureTheory.setLIntegral_mono' h_meas4 h_ball_le
      _ = ENNReal.ofReal (∫ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, C' * t ^ (-s)) := by
        have h_cont : ContinuousOn (fun t : ℝ => C' * t ^ (-s)) (Set.Icc (1 : ℝ) δ⁻¹) := by
          apply ContinuousOn.const_mul
          have h : ContinuousOn (fun t : ℝ => t ^ (-s)) (Set.Icc (1 : ℝ) δ⁻¹) := by
            intro t ht
            have h_t_pos : 0 < t := zero_lt_one.trans_le ht.1
            exact (Real.continuousAt_rpow_const t (-s) (Or.inl h_t_pos.ne')).continuousWithinAt
          exact h
        have h_le_one' : 1 ≤ δ⁻¹ := by linarith
        have h_int : IntervalIntegrable (fun t : ℝ => C' * t ^ (-s)) volume 1 δ⁻¹ := by
          have h_cont2 : ContinuousOn (fun t : ℝ => C' * t ^ (-s)) (Set.uIcc (1 : ℝ) δ⁻¹) := by
            rw [Set.uIcc_of_le h_le_one']
            exact h_cont
          exact h_cont2.intervalIntegrable
        have h_iOn_Icc : IntegrableOn (fun t : ℝ => C' * t ^ (-s)) (Set.Icc (1 : ℝ) δ⁻¹) volume :=
          h_cont.integrableOn_Icc
        have h_iOn : IntegrableOn (fun t : ℝ => C' * t ^ (-s)) (Set.Ico (1 : ℝ) δ⁻¹) volume :=
          h_iOn_Icc.mono_set (show Set.Ico (1 : ℝ) δ⁻¹ ⊆ Set.Icc (1 : ℝ) δ⁻¹ from by
            intro x hx; exact ⟨hx.1, le_of_lt hx.2⟩)
        have h_nn : 0 ≤ᵐ[volume.restrict (Set.Ico (1 : ℝ) δ⁻¹)] (fun t : ℝ => C' * t ^ (-s)) := by
          have h_mem : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ico (1 : ℝ) δ⁻¹), t ∈ Set.Ico (1 : ℝ) δ⁻¹ :=
            ae_restrict_mem h_meas4
          filter_upwards [h_mem] with t ht
          have h_t_pos : 0 < t := zero_lt_one.trans_le ht.1
          exact mul_nonneg hC'_pos.le (Real.rpow_nonneg h_t_pos.le _)
        have h_main_eq : ENNReal.ofReal (∫ (t : ℝ), C' * t ^ (-s) ∂(volume.restrict (Set.Ico (1 : ℝ) δ⁻¹))) =
            ∫⁻ (t : ℝ), ENNReal.ofReal (C' * t ^ (-s)) ∂(volume.restrict (Set.Ico (1 : ℝ) δ⁻¹)) :=
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_iOn h_nn
        simpa using h_main_eq.symm
      _ ≤ ENNReal.ofReal (C' / (s - 1)) := by
        have h_le_one : 1 ≤ δ⁻¹ := by linarith
        have h_eq1 : ∫ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, C' * t ^ (-s) =
            ∫ (t : ℝ) in Set.Ioc (1 : ℝ) δ⁻¹, C' * t ^ (-s) := by
          exact integral_Ico_eq_integral_Ioc
        have h_int_Ioc : ∫ (t : ℝ) in Set.Ioc (1 : ℝ) δ⁻¹, C' * t ^ (-s) =
            ∫ t in (1 : ℝ)..δ⁻¹, C' * t ^ (-s) := by
          exact (intervalIntegral.integral_of_le h_le_one).symm
        have h_bound : ∫ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, C' * t ^ (-s) ≤ C' / (s - 1) := by
          rw [h_eq1, h_int_Ioc]
          have h_mul : ∫ t in (1 : ℝ)..δ⁻¹, C' * t ^ (-s) =
              C' * ∫ t in (1 : ℝ)..δ⁻¹, t ^ (-s) := by
            rw [intervalIntegral.integral_const_mul]
          rw [h_mul, integral_t_neg_s hs h_le_one]
          have h10 : C' * ((1 - (δ⁻¹) ^ (1 - s)) / (s - 1)) ≤ C' / (s - 1) := by
            have h11 : C' * ((1 - (δ⁻¹) ^ (1 - s)) / (s - 1)) =
                (C' * (1 - (δ⁻¹) ^ (1 - s))) / (s - 1) := by
              rw [mul_div_assoc]
            rw [h11]
            have h12 : 0 ≤ (δ⁻¹) ^ (1 - s) := Real.rpow_nonneg (by positivity) _
            have h13 : 1 - (δ⁻¹) ^ (1 - s) ≤ 1 := by linarith
            have h14 : C' * (1 - (δ⁻¹) ^ (1 - s)) ≤ C' := mul_le_of_le_one_right hC'_pos.le h13
            exact div_le_div_of_nonneg_right h14 (by linarith)
          exact h10
        exact ofReal_le_ofReal h_bound
    -- Combine
    calc (∫⁻ (t : ℝ) in Set.Ioo (0 : ℝ) 1, g t) + ∫⁻ (t : ℝ) in Set.Ico (1 : ℝ) δ⁻¹, g t
      ≤ (1 : ENNReal) + ENNReal.ofReal (C' / (s - 1)) := by gcongr
    _ = ENNReal.ofReal (1 + C' / (s - 1)) := by
      have h_one : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h_one]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      <;> norm_cast

/-- If μ is all-scale (κ,C)-Frostman and nκ > 1, then μ^×n has bounded 1-energy. -/
lemma IsAllScaleFrostman.product_riesz_energy_bound
    {κ C : ℝ} {μ : Measure ℝ} (h : IsAllScaleFrostman κ C μ)
    {n : ℕ} (hnκ : 1 < (n : ℝ) * κ)
    {δ : ℝ} (hδ : 0 < δ) :
    robust_projection_main.rieszEnergy (α := 1) (hδ := hδ)
      (ProductMeasureEnergy.productMeasure (n := n) μ) ≤
    ENNReal.ofReal (1 + C ^ n / ((n : ℝ) * κ - 1)) := by
  let ν : Measure (EuclideanSpace ℝ (Fin n)) := ProductMeasureEnergy.productMeasure μ
  let s : ℝ := (n : ℝ) * κ
  let C' : ℝ := C ^ n
  have hκ_pos : 0 < κ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hs : 1 < s := hnκ
  have hC'_pos : 0 < C' := by positivity
  have hν_prob : ν Set.univ = 1 :=
    ProductMeasureEnergy.product_measure_univ h.1
  have hFrost : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (C' * r ^ s) := by
    intro x r hr
    exact h.product_ball_bound (n := n) (x := x) (r := r) (hr := hr)
  have h_main : ∀ (x : EuclideanSpace ℝ (Fin n)),
      ∫⁻ (y : EuclideanSpace ℝ (Fin n)),
        ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ≤
      ENNReal.ofReal (1 + C' / (s - 1)) := by
    intro x
    exact frostman_energy_inner_bound (X := EuclideanSpace ℝ (Fin n)) (ν := ν) (s := s) (C' := C')
      hν_prob hs hC'_pos hFrost hδ x
  dsimp only [robust_projection_main.rieszEnergy]
  have h_swap : ∫⁻ (x : EuclideanSpace ℝ (Fin n)),
      ∫⁻ (y : EuclideanSpace ℝ (Fin n)),
        ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ∂ν ≤
      ENNReal.ofReal (1 + C' / (s - 1)) := by
    have h_ae : ∀ᵐ (x : EuclideanSpace ℝ (Fin n)) ∂ν,
        (∫⁻ (y : EuclideanSpace ℝ (Fin n)),
          ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν) ≤
        ENNReal.ofReal (1 + C' / (s - 1)) :=
      Filter.Eventually.of_forall h_main
    have h_mono : ∫⁻ (x : EuclideanSpace ℝ (Fin n)),
        ∫⁻ (y : EuclideanSpace ℝ (Fin n)),
          ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ∂ν ≤
      ∫⁻ (x : EuclideanSpace ℝ (Fin n)),
        ENNReal.ofReal (1 + C' / (s - 1)) ∂ν :=
      MeasureTheory.lintegral_mono_ae h_ae
    have h_const : ∫⁻ (x : EuclideanSpace ℝ (Fin n)),
        ENNReal.ofReal (1 + C' / (s - 1)) ∂ν =
      ENNReal.ofReal (1 + C' / (s - 1)) := by
      rw [MeasureTheory.lintegral_const, hν_prob] <;> simp
    calc ∫⁻ (x : EuclideanSpace ℝ (Fin n)),
        ∫⁻ (y : EuclideanSpace ℝ (Fin n)),
          ENNReal.ofReal ((max (dist x y) δ) ^ (-1 : ℝ)) ∂ν ∂ν
      ≤ ∫⁻ (x : EuclideanSpace ℝ (Fin n)),
          ENNReal.ofReal (1 + C' / (s - 1)) ∂ν := h_mono
    _ = ENNReal.ofReal (1 + C' / (s - 1)) := h_const
  have h_final : ENNReal.ofReal (1 + C' / (s - 1)) = ENNReal.ofReal (1 + C ^ n / ((n : ℝ) * κ - 1)) := by
    congr 1
    <;> simp [show C' = C ^ n from rfl, show s = (n : ℝ) * κ from rfl] <;> ring
  rw [h_final] at h_swap
  exact h_swap
