import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.PrekopaLeindler

open scoped Pointwise

/-!
# Brunn–Minkowski Inequality

The `n`-dimensional Brunn–Minkowski inequality and its consequence:
a lower bound on the volume of the outer parallel body `E + t · B₁`.

## Main results

- `brunnMinkowski`: For nonempty measurable `A, B ⊆ ℝⁿ`,
  `volume(A + B)^(1/n) ≥ volume(A)^(1/n) + volume(B)^(1/n)`.
- `parallelVolume_lowerBound`: For measurable `E` and `t > 0`,
  `volume(E + t·B₁) ≥ volume(E) + n·t·volume(E)^((n-1)/n)·volume(B₁)^(1/n)`.

## Proof sketch

The Brunn–Minkowski inequality follows from Prékopa–Leindler by
taking `f = 1_A`, `g = 1_B`, and `h = 1_{(1-t)A+tB}`.

The parallel volume lower bound follows by setting `B = t · B₁` in BM
and applying the binomial lower bound
`(a + b)^n ≥ a^n + n·a^(n-1)·b` for `a, b ≥ 0`.

## Whiteprint

This module corresponds to the `brunn_minkowski` whiteprint node.
-/

namespace Geometry

open MeasureTheory ENNReal Metric Set

/-!
## Brunn–Minkowski inequality
-/

/-- **Brunn–Minkowski inequality.** For nonempty measurable sets
`A, B ⊆ ℝⁿ`, the volume of the Minkowski sum satisfies
`volume(A + B)^(1/n) ≥ volume(A)^(1/n) + volume(B)^(1/n)`.

NOTE: The `Nonempty` hypotheses are necessary: if `A = ∅` and `B ≠ ∅`,
then `A + B = ∅`, so LHS = 0 while RHS = `volume(B)^(1/n) > 0`. -/
theorem brunnMinkowski (n : ℕ) (hn : 2 ≤ n)
    (A B : Set (E n)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    (h_sum : MeasurableSet (A + B)) :
    volume (A + B) ^ (1 / (n : ℝ)) ≥
    volume A ^ (1 / (n : ℝ)) + volume B ^ (1 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by linarith
  -- Multiplicative BM from PL
  have h_mult : ∀ (t : ℝ), 0 < t → t < 1 →
      ∀ (X Y : Set (E n)), MeasurableSet X → MeasurableSet Y →
      MeasurableSet ((1 - t) • X + t • Y) →
      volume ((1 - t) • X + t • Y) ≥ (volume X) ^ (1 - t) * (volume Y) ^ t := by
    intro t ht1 ht2 X Y hX hY hXY
    let f : E n → ENNReal := Set.indicator X (fun _ => (1 : ENNReal))
    let g : E n → ENNReal := Set.indicator Y (fun _ => (1 : ENNReal))
    let h : E n → ENNReal := Set.indicator ((1 - t) • X + t • Y) (fun _ => (1 : ENNReal))
    have hf : Measurable f := measurable_one.indicator hX
    have hg : Measurable g := measurable_one.indicator hY
    have hh : Measurable h := measurable_one.indicator hXY
    have h1mt_pos : 0 < 1 - t := by linarith
    have hcond : ∀ (x y : E n), h ((1 - t) • x + t • y) ≥ f x ^ (1 - t) * g y ^ t := by
      intro x y
      by_cases hx : x ∈ X <;> by_cases hy : y ∈ Y
      · have h_in : (1 - t) • x + t • y ∈ (1 - t) • X + t • Y := by
          exact Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
        simp [h, f, g, hx, hy, h_in] <;> norm_num
      · have hgy : g y = 0 := by simp [g, hy, Set.indicator_apply]
        rw [hgy]; rw [ENNReal.zero_rpow_of_pos ht1] <;> simp
      · have hfx : f x = 0 := by simp [f, hx, Set.indicator_apply]
        rw [hfx]; rw [ENNReal.zero_rpow_of_pos h1mt_pos] <;> simp
      · have hfx : f x = 0 := by simp [f, hx, Set.indicator_apply]
        rw [hfx]; rw [ENNReal.zero_rpow_of_pos h1mt_pos] <;> simp
    have hpl := prekopaLeindler n t ht1 ht2 f g h hf hg hh hcond
    have hif : ∫⁻ x, f x = volume X := by
      simpa [f] using MeasureTheory.lintegral_indicator_const₀ hX.nullMeasurableSet 1
    have hig : ∫⁻ x, g x = volume Y := by
      simpa [g] using MeasureTheory.lintegral_indicator_const₀ hY.nullMeasurableSet 1
    have hih : ∫⁻ x, h x = volume ((1 - t) • X + t • Y) := by
      simpa [h] using MeasureTheory.lintegral_indicator_const₀ hXY.nullMeasurableSet 1
    rw [hih, hif, hig] at hpl
    exact hpl

  -- Translation invariance
  have htrans : ∀ (a : E n) (S : Set (E n)),
      volume ((fun x : E n => a + x) '' S) = volume S := by
    intro a S
    have h_eq : (fun x : E n => a + x) '' S = (fun x : E n => -a + x) ⁻¹' S := by
      ext y; simp [add_comm]
    rw [h_eq]
    exact MeasureTheory.measure_preimage_add volume (-a) S

  -- Volume scaling
  have hvol_scale : ∀ (c : ℝ), 0 < c → ∀ (S : Set (E n)),
      volume (c • S) = ENNReal.ofReal (c ^ n) * volume S := by
    intro c hc S
    let f : E n →L[ℝ] E n := c • ContinuousLinearMap.id ℝ (E n)
    have hdet : LinearMap.det (f : E n →ₗ[ℝ] E n) = c ^ n := by simp [f] <;> rfl
    have h_eq : (c • S) = f '' S := by ext x; simp [Set.mem_smul_set] <;> rfl
    rw [h_eq]
    rw [MeasureTheory.Measure.addHaar_image_continuousLinearMap volume f S, hdet]
    have habs : |c ^ n| = c ^ n := abs_of_pos (pow_pos hc n)
    rw [habs] <;> rfl

  -- Measurability of dilation
  have hmeas_scale : ∀ (c : ℝ), c ≠ 0 → ∀ {S : Set (E n)}, MeasurableSet S → MeasurableSet (c • S) := by
    intro c hc S hS
    exact hS.const_smul_of_ne_zero (a := c) hc

  -- c • (S + T) = c • S + c • T
  have hsmul_distrib : ∀ (c : ℝ) (S T : Set (E n)), c • (S + T) = c • S + c • T := by
    intro c S T
    ext x
    simp only [Set.mem_smul_set, Set.mem_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨s, hs, t, ht, rfl⟩
      exact ⟨c • s, ⟨s, hs, rfl⟩, c • t, ⟨t, ht, rfl⟩, by simp [smul_add]⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨s + t, ⟨s, hs, t, ht, rfl⟩, by simp [smul_add]⟩

  -- a • (b • S) = (a * b) • S
  have hsmul_smul : ∀ (a b : ℝ) (S : Set (E n)), a • (b • S) = (a * b) • S := by
    intro a b S
    ext x
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, by simp [smul_smul]⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨b • z, ⟨z, hz, rfl⟩, by simp [smul_smul]⟩

  -- Case 1: volume A = 0
  by_cases hA0 : volume A = 0
  · rcases hA_nonempty with ⟨a, ha⟩
    let f : E n → E n := fun x => a + x
    have h1 : f '' B ⊆ A + B := by
      intro x hx
      rcases hx with ⟨b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    have h2 : volume (f '' B) = volume B := htrans a B
    have h3 : volume (A + B) ≥ volume B := by
      calc volume (A + B) ≥ volume (f '' B) := measure_mono h1
           _ = volume B := h2
    have h4 : (volume (A + B)) ^ (1 / (n : ℝ)) ≥ (volume B) ^ (1 / (n : ℝ)) :=
      ENNReal.rpow_le_rpow h3 (by positivity)
    have h5 : (volume A) ^ (1 / (n : ℝ)) = 0 := by
      rw [hA0]; exact ENNReal.zero_rpow_of_pos (by positivity)
    rw [h5]
    simpa using h4
  -- Case 2: volume B = 0
  by_cases hB0 : volume B = 0
  · rcases hB_nonempty with ⟨b, hb⟩
    let f : E n → E n := fun x => b + x
    have h1 : f '' A ⊆ A + B := by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      have h_eq : a + b = b + a := by simp [add_comm]
      exact ⟨a, ha, b, hb, h_eq⟩
    have h2 : volume (f '' A) = volume A := htrans b A
    have h3 : volume (A + B) ≥ volume A := by
      calc volume (A + B) ≥ volume (f '' A) := measure_mono h1
           _ = volume A := h2
    have h4 : (volume (A + B)) ^ (1 / (n : ℝ)) ≥ (volume A) ^ (1 / (n : ℝ)) :=
      ENNReal.rpow_le_rpow h3 (by positivity)
    have h5 : (volume B) ^ (1 / (n : ℝ)) = 0 := by
      rw [hB0]; exact ENNReal.zero_rpow_of_pos (by positivity)
    rw [h5]
    simpa using h4
  -- Case 3: volume A = ⊤
  by_cases hA_top : volume A = ⊤
  · rcases hB_nonempty with ⟨b, hb⟩
    let f : E n → E n := fun x => b + x
    have h1 : f '' A ⊆ A + B := by
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      have h_eq : a + b = b + a := by simp [add_comm]
      exact ⟨a, ha, b, hb, h_eq⟩
    have h2 : volume (A + B) = ⊤ := by
      have h3 : volume (A + B) ≥ volume A := by
        calc volume (A + B) ≥ volume (f '' A) := measure_mono h1
             _ = volume A := htrans b A
      rw [hA_top] at h3
      exact top_le_iff.mp h3
    rw [h2]
    have h_top : (⊤ : ENNReal) ^ (1 / (n : ℝ)) = ⊤ :=
      ENNReal.top_rpow_of_pos (by positivity)
    rw [h_top]
    exact le_top
  -- Case 4: volume B = ⊤
  by_cases hB_top : volume B = ⊤
  · rcases hA_nonempty with ⟨a, ha⟩
    let f : E n → E n := fun x => a + x
    have h1 : f '' B ⊆ A + B := by
      intro x hx
      rcases hx with ⟨b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    have h2 : volume (A + B) = ⊤ := by
      have h3 : volume (A + B) ≥ volume B := by
        calc volume (A + B) ≥ volume (f '' B) := measure_mono h1
             _ = volume B := htrans a B
      rw [hB_top] at h3
      exact top_le_iff.mp h3
    rw [h2]
    have h_top : (⊤ : ENNReal) ^ (1 / (n : ℝ)) = ⊤ :=
      ENNReal.top_rpow_of_pos (by positivity)
    rw [h_top]
    exact le_top
  -- Main case: 0 < volume A < ⊤ and 0 < volume B < ⊤
  have hA_pos : 0 < volume A := bot_lt_iff_ne_bot.mpr hA0
  have hB_pos : 0 < volume B := bot_lt_iff_ne_bot.mpr hB0
  have hA_lt_top : volume A < ⊤ := lt_top_iff_ne_top.mpr hA_top
  have hB_lt_top : volume B < ⊤ := lt_top_iff_ne_top.mpr hB_top
  set α : ENNReal := volume A ^ (1 / (n : ℝ)) with hα_def
  set β : ENNReal := volume B ^ (1 / (n : ℝ)) with hβ_def
  have hα_ne_zero : α ≠ 0 := by
    rw [hα_def]
    have h : (volume A) ^ (1 / (n : ℝ)) = 0 ↔ volume A = 0 :=
      ENNReal.rpow_eq_zero_iff_of_pos (by positivity)
    exact h.not.mpr hA0
  have hβ_ne_zero : β ≠ 0 := by
    rw [hβ_def]
    have h : (volume B) ^ (1 / (n : ℝ)) = 0 ↔ volume B = 0 :=
      ENNReal.rpow_eq_zero_iff_of_pos (by positivity)
    exact h.not.mpr hB0
  have hα_ne_top : α ≠ ⊤ := by
    rw [hα_def]
    exact ENNReal.rpow_ne_top_of_nonneg (hy0 := by positivity) (h := hA_lt_top.ne)
  have hβ_ne_top : β ≠ ⊤ := by
    rw [hβ_def]
    exact ENNReal.rpow_ne_top_of_nonneg (hy0 := by positivity) (h := hB_lt_top.ne)
  have hαβ_pos : α + β ≠ 0 := by
    have h : 0 < α := bot_lt_iff_ne_bot.mpr hα_ne_zero
    have h' : 0 < α + β := by positivity
    exact h'.ne'
  have hαβ_top : α + β ≠ ⊤ := by
    have hα_lt : α < ⊤ := lt_top_iff_ne_top.mpr hα_ne_top
    have hβ_lt : β < ⊤ := lt_top_iff_ne_top.mpr hβ_ne_top
    have h : α + β < ⊤ := ENNReal.add_lt_top.mpr ⟨hα_lt, hβ_lt⟩
    exact h.ne
  have hα_n : α ^ (n : ℝ) = volume A := by
    have h : (volume A) ^ ((1 / (n : ℝ)) * (n : ℝ)) = ((volume A) ^ (1 / (n : ℝ))) ^ (n : ℝ) :=
      ENNReal.rpow_mul (volume A) (1 / (n : ℝ)) (n : ℝ)
    have h2 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn1] <;> linarith
    rw [h2] at h
    simpa [hα_def] using h.symm
  have hβ_n : β ^ (n : ℝ) = volume B := by
    have h : (volume B) ^ ((1 / (n : ℝ)) * (n : ℝ)) = ((volume B) ^ (1 / (n : ℝ))) ^ (n : ℝ) :=
      ENNReal.rpow_mul (volume B) (1 / (n : ℝ)) (n : ℝ)
    have h2 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn1] <;> linarith
    rw [h2] at h
    simpa [hβ_def] using h.symm
  have hα_toReal_pos : 0 < α.toReal := ENNReal.toReal_pos hα_ne_zero hα_ne_top
  have hβ_toReal_pos : 0 < β.toReal := ENNReal.toReal_pos hβ_ne_zero hβ_ne_top
  let a_real : ℝ := α.toReal⁻¹
  let b_real : ℝ := β.toReal⁻¹
  have ha_real_pos : 0 < a_real := by
    simp only [a_real, inv_pos] <;> exact hα_toReal_pos
  have hb_real_pos : 0 < b_real := by
    simp only [b_real, inv_pos] <;> exact hβ_toReal_pos
  let t : ℝ := a_real / (a_real + b_real)
  have ht1 : 0 < t := by positivity
  have ht2 : t < 1 := by
    apply (div_lt_one (by positivity)).mpr <;> linarith
  have h_eq_coeff : (1 - t) * a_real = t * b_real := by
    simp only [t]
    field_simp [ha_real_pos.ne', hb_real_pos.ne'] <;> ring
  let c_real : ℝ := (1 - t) * a_real
  have hc_real_pos : 0 < c_real := by positivity
  set X : Set (E n) := a_real • A with hX_def
  set Y : Set (E n) := b_real • B with hY_def
  have hX_meas : MeasurableSet X := hmeas_scale a_real ha_real_pos.ne' hA
  have hY_meas : MeasurableSet Y := hmeas_scale b_real hb_real_pos.ne' hB
  have hvolX : volume X = 1 := by
    rw [hX_def, hvol_scale a_real ha_real_pos A]
    have h21 : (α ^ (n : ℝ)).toReal = α.toReal ^ n := by
      have h := ENNReal.toReal_rpow α (n : ℝ)
      norm_cast at h ⊢ <;> exact h.symm
    have h22 : (α ^ (n : ℝ)).toReal = (volume A).toReal := by rw [hα_n]
    have h23 : a_real ^ n = (volume A).toReal⁻¹ := by
      simp only [a_real]
      have h24 : (α.toReal⁻¹) ^ n = (α.toReal ^ n)⁻¹ := by rw [inv_pow]
      rw [h24]
      have h25 : α.toReal ^ n = (volume A).toReal := by rw [← h21, h22]
      rw [h25]
    rw [h23]
    have h4 : 0 < (volume A).toReal := ENNReal.toReal_pos hA0 hA_top
    have h5 : ENNReal.ofReal ((volume A).toReal⁻¹) = (volume A)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos h4, ENNReal.ofReal_toReal hA_top]
    rw [h5]
    exact ENNReal.inv_mul_cancel hA0 hA_top
  have hvolY : volume Y = 1 := by
    rw [hY_def, hvol_scale b_real hb_real_pos B]
    have h21 : (β ^ (n : ℝ)).toReal = β.toReal ^ n := by
      have h := ENNReal.toReal_rpow β (n : ℝ)
      norm_cast at h ⊢ <;> exact h.symm
    have h22 : (β ^ (n : ℝ)).toReal = (volume B).toReal := by rw [hβ_n]
    have h23 : b_real ^ n = (volume B).toReal⁻¹ := by
      simp only [b_real]
      have h24 : (β.toReal⁻¹) ^ n = (β.toReal ^ n)⁻¹ := by rw [inv_pow]
      rw [h24]
      have h25 : β.toReal ^ n = (volume B).toReal := by rw [← h21, h22]
      rw [h25]
    rw [h23]
    have h4 : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hB_top
    have h5 : ENNReal.ofReal ((volume B).toReal⁻¹) = (volume B)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos h4, ENNReal.ofReal_toReal hB_top]
    rw [h5]
    exact ENNReal.inv_mul_cancel hB0 hB_top
  have h_set_eq : (1 - t : ℝ) • X + (t : ℝ) • Y = c_real • (A + B) := by
    calc
      (1 - t : ℝ) • X + (t : ℝ) • Y
        = (1 - t : ℝ) • (a_real • A) + (t : ℝ) • (b_real • B) := by rfl
      _ = ((1 - t) * a_real) • A + (t * b_real) • B := by
        rw [hsmul_smul (1 - t) a_real A, hsmul_smul t b_real B]
      _ = c_real • A + c_real • B := by
        have h : (t * b_real) = c_real := by linarith
        rw [h_eq_coeff, h]
      _ = c_real • (A + B) := by rw [hsmul_distrib c_real A B]
  have h_sum' : MeasurableSet ((1 - t : ℝ) • X + (t : ℝ) • Y) := by
    rw [h_set_eq]
    exact hmeas_scale c_real hc_real_pos.ne' h_sum
  have hbm := h_mult t ht1 ht2 X Y hX_meas hY_meas h_sum'
  rw [hvolX, hvolY] at hbm
  have h1 : volume ((1 - t : ℝ) • X + (t : ℝ) • Y) ≥ 1 := by simpa using hbm
  rw [h_set_eq] at h1
  have h2 : volume (c_real • (A + B)) = ENNReal.ofReal (c_real ^ n) * volume (A + B) :=
    hvol_scale c_real hc_real_pos (A + B)
  rw [h2] at h1
  set c_enn : ENNReal := ENNReal.ofReal (c_real ^ n) with hc_enn_def
  have hc_enn_pos : c_enn ≠ 0 := by
    rw [hc_enn_def]
    have h : 0 < ENNReal.ofReal (c_real ^ n) := by positivity
    exact h.ne'
  have hc_enn_ne_top : c_enn ≠ ⊤ := by
    rw [hc_enn_def]
    exact ENNReal.ofReal_ne_top
  have h3 : c_enn * volume (A + B) ≥ 1 := h1
  have h_eq : c_enn⁻¹ * (c_enn * volume (A + B)) = volume (A + B) :=
    ENNReal.inv_mul_cancel_left hc_enn_pos hc_enn_ne_top
  have h4 : volume (A + B) ≥ c_enn⁻¹ := by
    calc volume (A + B)
      = c_enn⁻¹ * (c_enn * volume (A + B)) := h_eq.symm
    _ ≥ c_enn⁻¹ * 1 := by gcongr
    _ = c_enn⁻¹ := by simp
  have h5 : c_real = (α.toReal + β.toReal)⁻¹ := by
    have h6 : c_real = a_real * b_real / (a_real + b_real) := by
      simp only [c_real, t]
      field_simp [ha_real_pos.ne', hb_real_pos.ne'] <;> ring
    rw [h6]
    have h7 : a_real = α.toReal⁻¹ := by rfl
    have h8 : b_real = β.toReal⁻¹ := by rfl
    rw [h7, h8]
    field_simp [hα_toReal_pos.ne', hβ_toReal_pos.ne'] <;> ring
  have h9 : c_enn⁻¹ = (α + β) ^ n := by
    have h_pos_sum : 0 < α.toReal + β.toReal := by positivity
    have h10 : c_real ^ n = ((α.toReal + β.toReal) ^ n)⁻¹ := by
      rw [h5, inv_pow]
    have h11 : c_enn = ENNReal.ofReal (((α.toReal + β.toReal) ^ n)⁻¹) := by
      rw [hc_enn_def, h10]
    have h12 : 0 < (α.toReal + β.toReal) ^ n := by positivity
    have h13 : ENNReal.ofReal (((α.toReal + β.toReal) ^ n)⁻¹)
             = (ENNReal.ofReal ((α.toReal + β.toReal) ^ n))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos h12]
    have h14 : ENNReal.ofReal ((α.toReal + β.toReal) ^ n) = (α + β) ^ n := by
      rw [ENNReal.ofReal_pow h_pos_sum.le]
      have h15 : ENNReal.ofReal (α.toReal + β.toReal) = α + β := by
        rw [ENNReal.ofReal_add hα_toReal_pos.le hβ_toReal_pos.le]
        rw [ENNReal.ofReal_toReal hα_ne_top, ENNReal.ofReal_toReal hβ_ne_top]
      rw [h15] <;> norm_cast
    have h15 : c_enn = ((α + β) ^ n)⁻¹ := by
      rw [h11, h13, h14]
    rw [h15]
    have h16 : (α + β) ^ n ≠ 0 := pow_ne_zero n hαβ_pos
    have h17 : (α + β) ^ n ≠ ⊤ := by
      have h18 : α + β < ⊤ := lt_top_iff_ne_top.mpr hαβ_top
      have h19 : (α + β) ^ n < ⊤ := pow_lt_top h18
      exact h19.ne
    set y : ENNReal := ((α + β) ^ n)⁻¹ with hy_def
    have hy0 : y ≠ 0 := by
      simp [hy_def, ENNReal.inv_eq_zero, h17] <;> tauto
    have hyt : y ≠ ⊤ := by
      simp [hy_def, ENNReal.inv_eq_top, h16] <;> tauto
    have hyt_inv : y⁻¹ ≠ ⊤ := by
      simp [hy_def, ENNReal.inv_eq_top, hy0] <;> tauto
    have h1 : y⁻¹ = ENNReal.ofReal (y⁻¹.toReal) := (ENNReal.ofReal_toReal hyt_inv).symm
    have h2 : y⁻¹.toReal = y.toReal⁻¹ := ENNReal.toReal_inv y
    have h3 : y.toReal = (((α + β) ^ n).toReal)⁻¹ := by
      rw [← ENNReal.toReal_inv ((α + β) ^ n)] <;> rfl
    have h4 : y⁻¹.toReal = ((α + β) ^ n).toReal := by
      rw [h2, h3]
      have hpos : 0 < ((α + β) ^ n).toReal := ENNReal.toReal_pos h16 h17
      field_simp [hpos.ne']
    have h5 : y⁻¹ = ENNReal.ofReal (((α + β) ^ n).toReal) := by
      rw [h1, h4]
    have h6 : ENNReal.ofReal (((α + β) ^ n).toReal) = (α + β) ^ n := ENNReal.ofReal_toReal h17
    have h_inv_inv : y⁻¹ = (α + β) ^ n := by
      rw [h5, h6]
    simpa [hy_def] using h_inv_inv
  rw [h9] at h4
  have h_rpow_nat : ∀ (x : ENNReal), x ≠ 0 → x ≠ ⊤ → ∀ (m : ℕ), x ^ m = x ^ (m : ℝ) := by
    intro x hx0 hxt m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih]
      have h_add : x ^ ((m : ℝ) + 1) = x ^ (m : ℝ) * x := by
        rw [ENNReal.rpow_add (m : ℝ) 1 hx0 hxt, ENNReal.rpow_one] <;> ring
      simpa using h_add.symm
  have h10 : (volume (A + B)) ^ (1 / (n : ℝ)) ≥ ((α + β) ^ n) ^ (1 / (n : ℝ)) :=
    ENNReal.rpow_le_rpow h4 (by positivity)
  have h11 : ((α + β) ^ n) ^ (1 / (n : ℝ)) = α + β := by
    have h_pow : (α + β) ^ n = (α + β) ^ (n : ℝ) := h_rpow_nat (α + β) hαβ_pos hαβ_top n
    rw [h_pow]
    have h12 : ((α + β) ^ (n : ℝ)) ^ (1 / (n : ℝ)) = (α + β) ^ ((n : ℝ) * (1 / (n : ℝ))) :=
      (ENNReal.rpow_mul (α + β) (n : ℝ) (1 / (n : ℝ))).symm
    rw [h12]
    have h13 : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hn1] <;> linarith
    rw [h13] <;> simp
  rw [h11] at h10
  have h12 : α = (volume A) ^ (1 / (n : ℝ)) := by rfl
  have h13 : β = (volume B) ^ (1 / (n : ℝ)) := by rfl
  rw [h12, h13] at h10
  exact h10

/-!
## Parallel volume lower bound
-/

/-- Binomial lower bound in ENNReal: `(a+b)^n ≥ a^n + n*a^(n-1)*b`. -/
private lemma binomial_lower_bound_ennreal {a b : ℝ≥0∞} {n : ℕ} (hn : 1 ≤ n) :
    a ^ n + (n : ℝ≥0∞) * a ^ (n - 1) * b ≤ (a + b) ^ n := by
  have h_main : (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * a ^ k * b ^ (n - k) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h_main]
  let S := Finset.range (n + 1)
  have h3 : ({n, n - 1} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl) <;> simp [S] <;> omega
  have h4 : ∑ k ∈ S, (n.choose k : ℝ≥0∞) * a ^ k * b ^ (n - k) ≥
      ∑ k ∈ ({n, n - 1} : Finset ℕ), (n.choose k : ℝ≥0∞) * a ^ k * b ^ (n - k) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h3
    intro i _ _
    positivity
  have h_disj : n ≠ n - 1 := by omega
  have h5 : ∑ k ∈ ({n, n - 1} : Finset ℕ), (n.choose k : ℝ≥0∞) * a ^ k * b ^ (n - k) =
      a ^ n + (n : ℝ≥0∞) * a ^ (n - 1) * b := by
    rw [Finset.sum_pair h_disj]
    have h6 : n.choose n = 1 := Nat.choose_self n
    have h7 : n.choose (n - 1) = n := by
      cases n with
      | zero => omega
      | succ n' => simp [Nat.choose_one_right]
    rw [h6, h7]
    <;> cases n with
      | zero => omega
      | succ n' => simp [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  rw [h5] at h4
  exact h4

/-- Volume scaling: `volume (t • B) = (ofReal t)^n * volume B` for `t ≥ 0`. -/
private lemma volume_dilation_nonneg {n : ℕ} (t : ℝ) (ht : 0 ≤ t) (B : Set (E n)) :
    volume (t • B) = (ENNReal.ofReal t) ^ n * volume B := by
  rw [MeasureTheory.Measure.addHaar_smul volume t B]
  have hfinrank : Module.finrank ℝ (E n) = n := finrank_euclideanSpace_fin
  rw [hfinrank]
  have h_abs : |t ^ n| = t ^ n := by
    rw [abs_of_nonneg (pow_nonneg ht n)]
  rw [h_abs]
  have h_ofReal_pow : ENNReal.ofReal (t ^ n) = (ENNReal.ofReal t) ^ n :=
    ENNReal.ofReal_pow ht n
  rw [h_ofReal_pow]

/-- Auxiliary: `((ofReal t)^n * volume B₁)^(1/n) = ofReal t * (volume B₁)^(1/n)`. -/
private lemma rpow_dilation_volume {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t)
    (B₁ : Set (E n)) :
    ((ENNReal.ofReal t) ^ n * volume B₁) ^ (1 / (n : ℝ)) =
      (ENNReal.ofReal t) * (volume B₁) ^ (1 / (n : ℝ)) := by
  have h_pos : 0 ≤ (1 / (n : ℝ)) := by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ h_pos]
  have h2 : ((ENNReal.ofReal t) ^ n) ^ (1 / (n : ℝ)) = ENNReal.ofReal t := by
    have h3 : ((ENNReal.ofReal t) ^ n) ^ (1 / (n : ℝ)) =
        (ENNReal.ofReal t) ^ ((n : ℝ) * (1 / (n : ℝ))) :=
      (ENNReal.rpow_natCast_mul (ENNReal.ofReal t) n (1 / (n : ℝ))).symm
    rw [h3]
    have h4 : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp [hn] <;> ring
    rw [h4, ENNReal.rpow_one]
  rw [h2]

/-- Auxiliary: raise both sides of `X^(1/n) ≥ Y` to nth power. -/
private lemma rpow_nth_cancel {n : ℕ} (hn : 1 ≤ n) {X Y : ENNReal}
    (h : X ^ (1 / (n : ℝ)) ≥ Y) : X ≥ Y ^ n := by
  have h_pos : 0 ≤ (n : ℝ) := by positivity
  have h1 : Y ^ (n : ℝ) ≤ (X ^ (1 / (n : ℝ))) ^ (n : ℝ) :=
    ENNReal.rpow_le_rpow h h_pos
  have h2 : (X ^ (1 / (n : ℝ))) ^ (n : ℝ) = X := by
    rw [← ENNReal.rpow_mul]
    have h3 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn] <;> ring
    rw [h3, ENNReal.rpow_one]
  have h4 : Y ^ (n : ℝ) = Y ^ n := by norm_cast
  rw [h2, h4] at h1
  exact h1

/-- **Lower bound on outer parallel volume.** From Brunn–Minkowski with
`B = t · B₁` and the binomial expansion:
`volume(E + t·B₁) ≥ volume(E) + n·t·volume(E)^((n-1)/n)·volume(B₁)^(1/n)`. -/
theorem parallelVolume_lowerBound (n : ℕ) (hn : 2 ≤ n)
    (E : Set (E n)) (hE : MeasurableSet E) (t : ℝ) (ht : 0 < t)
    (h_sum : MeasurableSet (E + t • unitBall n)) :
    volume (E + t • unitBall n) ≥
    volume E + (n : ENNReal) * ENNReal.ofReal t *
      volume E ^ ((n - 1 : ℝ) / n) *
      volume (unitBall n) ^ (1 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by linarith
  let A : Set (EuclideanSpace ℝ (Fin n)) := E
  have hA : MeasurableSet A := hE
  have h_sumA : MeasurableSet (A + t • unitBall n) := by
    simpa [show A = E from rfl] using h_sum
  set B₁ : Set (EuclideanSpace ℝ (Fin n)) := unitBall n with hB₁_def
  have hB₁_nonempty : B₁.Nonempty := by
    refine ⟨0, ?_⟩
    simp [hB₁_def, unitBall, dist_zero_right] <;> norm_num
  have hB₁_meas : MeasurableSet B₁ := isClosed_closedBall.measurableSet
  have h_tB₁_meas : MeasurableSet (t • B₁) := hB₁_meas.const_smul₀ t
  have h_tB₁_nonempty : (t • B₁).Nonempty := hB₁_nonempty.image _
  have h_vol_tB₁ : volume (t • B₁) = (ENNReal.ofReal t) ^ n * volume B₁ :=
    volume_dilation_nonneg t (by linarith) B₁
  have h_rpow_tB₁ : (volume (t • B₁)) ^ (1 / (n : ℝ)) =
      (ENNReal.ofReal t) * (volume B₁) ^ (1 / (n : ℝ)) := by
    rw [h_vol_tB₁, rpow_dilation_volume hn1 t (by linarith) B₁]

  -- If E is empty, both sides are 0
  by_cases hE_empty : E = ∅
  · have h_goal : volume (E + t • B₁) = 0 := by
      rw [hE_empty] <;> simp
    rw [h_goal]
    have h_vol_E : volume E = 0 := by simp [hE_empty]
    rw [h_vol_E]
    have h_pos_exp : 0 < ((n - 1 : ℝ) / n) := by
      have h1 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from by linarith)
      have h2 : 0 < (n - 1 : ℝ) := by exact_mod_cast (show 0 < n - 1 from by omega)
      exact div_pos h2 h1
    have h : (0 : ENNReal) ^ ((n - 1 : ℝ) / n) = 0 := ENNReal.zero_rpow_of_pos h_pos_exp
    rw [h] <;> simp
  · -- E is nonempty
    have hE_nonempty : E.Nonempty := Set.nonempty_iff_ne_empty.mpr hE_empty
    have hA_nonempty : A.Nonempty := by
      simpa [show A = E from rfl] using hE_nonempty
    have h_bm := brunnMinkowski n hn A (t • B₁) hA h_tB₁_meas hA_nonempty h_tB₁_nonempty h_sumA
    rw [h_rpow_tB₁] at h_bm
    set a : ENNReal := (volume A) ^ (1 / (n : ℝ)) with ha_def
    set b : ENNReal := (ENNReal.ofReal t) * (volume B₁) ^ (1 / (n : ℝ)) with hb_def
    have h_main1 : (volume (A + t • B₁)) ^ (1 / (n : ℝ)) ≥ a + b := h_bm
    have h_main2 : volume (A + t • B₁) ≥ (a + b) ^ n := rpow_nth_cancel hn1 h_main1
    have h_binom : (a + b) ^ n ≥ a ^ n + (n : ℝ≥0∞) * a ^ (n - 1) * b :=
      binomial_lower_bound_ennreal hn1
    have h_final : volume (A + t • B₁) ≥ a ^ n + (n : ℝ≥0∞) * a ^ (n - 1) * b := by
      calc volume (A + t • B₁) ≥ (a + b) ^ n := h_main2
           _ ≥ a ^ n + (n : ℝ≥0∞) * a ^ (n - 1) * b := h_binom
    have h_an : a ^ n = volume A := by
      rw [ha_def]
      have h : ((volume A) ^ (1 / (n : ℝ))) ^ n = volume A := by
        rw [← ENNReal.rpow_mul_natCast]
        have h3 : (1 / (n : ℝ)) * (↑n : ℝ) = 1 := by field_simp [hn1] <;> ring
        rw [h3, ENNReal.rpow_one]
      exact h
    have h_an1 : a ^ (n - 1) = (volume A) ^ ((n - 1 : ℝ) / (n : ℝ)) := by
      rw [ha_def]
      have h_cast : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1 := by
        cases n with
        | zero => omega
        | succ n' => simp [Nat.cast_add, Nat.cast_one] <;> ring
      have h : ((volume A) ^ (1 / (n : ℝ))) ^ (n - 1) =
          (volume A) ^ ((1 / (n : ℝ)) * (↑(n - 1) : ℝ)) := by
        rw [← ENNReal.rpow_mul_natCast]
      rw [h]
      have h3 : (1 / (n : ℝ)) * (↑(n - 1) : ℝ) = ((n - 1 : ℝ) / (n : ℝ)) := by
        rw [h_cast]
        field_simp [hn1] <;> ring
      rw [h3]
    rw [h_an, h_an1] at h_final
    have h_mul_perm : ∀ (a b c d : ENNReal),
        a * b * (c * d) = a * c * b * d := by
      intro a b c d
      simp [mul_assoc, mul_comm, mul_left_comm]
      <;> ac_rfl
    have h_mul_eq := h_mul_perm (n : ENNReal)
        ((volume A) ^ ((n - 1 : ℝ) / (n : ℝ)))
        (ENNReal.ofReal t)
        ((volume B₁) ^ (1 / (n : ℝ)))
    rw [h_mul_eq] at h_final
    have hA_eq : volume A = volume E := by rfl
    have hB1_eq : volume B₁ = volume (unitBall n) := by simp [hB₁_def]
    have h_sum_eq : volume (A + t • B₁) = volume (E + t • unitBall n) := by
      congr <;> simp [hB₁_def] <;> rfl
    rw [hA_eq, hB1_eq, h_sum_eq] at h_final
    exact h_final

end Geometry
