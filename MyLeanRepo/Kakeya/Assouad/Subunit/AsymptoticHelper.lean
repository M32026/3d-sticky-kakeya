import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.Estimates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Helper for asymptotic δ-power inequalities

Given `c > 0` and `e > 0`, there exists `delta₀ > 0` such that
for all `0 < δ ≤ delta₀`, `c ≤ δ^{-e}` (equivalently `c * δ^e ≤ 1`).
-/

noncomputable section

namespace Kakeya.Assouad.Subunit

/-- For `c > 0`, `e > 0`, there exists `delta₀ ≤ 1` such that
    `c * δ^e ≤ 1` for all `0 < δ ≤ delta₀`. -/
lemma exists_delta₀_mul_pow_le_one (c : ℝ) (hc : 0 < c) (e : ℝ) (he : 0 < e) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ → c * Real.rpow δ e ≤ 1 := by
  by_cases hc' : c ≤ 1
  · -- c ≤ 1, then delta₀ = 1 works since δ^e ≤ 1 for δ ≤ 1
    refine ⟨1, by norm_num, by norm_num, fun δ hδ hδ1 => ?_⟩
    have h1 : Real.rpow δ e ≤ 1 := Real.rpow_le_one hδ.le hδ1 he.le
    have h_rpow_nonneg : 0 ≤ Real.rpow δ e := (Real.rpow_pos_of_pos hδ e).le
    have h4 : c * Real.rpow δ e ≤ 1 := by
      calc c * Real.rpow δ e
        ≤ 1 * Real.rpow δ e := mul_le_mul_of_nonneg_right hc' h_rpow_nonneg
      _ ≤ 1 := by simpa using h1
    exact h4
  · -- c > 1, set delta₀ = (1/c)^(1/e)
    have hc_gt_one : 1 < c := by linarith
    set x : ℝ := 1 / c with hx_def
    have hx_pos : 0 < x := by positivity
    have hx_lt_one : x < 1 := by
      rw [hx_def]
      apply (div_lt_one (by positivity)).mpr
      linarith
    set delta₀ : ℝ := x ^ (1 / e) with hdelta₀_def
    have hdelta₀_pos : 0 < delta₀ := Real.rpow_pos_of_pos hx_pos (1 / e)
    have hdelta₀_le_one : delta₀ ≤ 1 := by
      rw [hdelta₀_def]
      have h2 : 0 < 1 / e := by positivity
      exact Real.rpow_le_one hx_pos.le hx_lt_one.le h2.le
    have h3 : x ^ ((1 / e) * e) = (x ^ (1 / e)) ^ e := Real.rpow_mul hx_pos.le (1 / e) e
    have h4 : (1 / e : ℝ) * e = 1 := by field_simp [he.ne']
    have h5 : delta₀ ^ e = x := by
      rw [hdelta₀_def]
      have h6 : (x ^ (1 / e)) ^ e = x ^ ((1 / e) * e) := h3.symm
      rw [h6, h4]
      <;> simp
    refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, fun δ hδ hδ1 => ?_⟩
    have h7 : Real.rpow δ e ≤ Real.rpow delta₀ e :=
      Real.rpow_le_rpow hδ.le hδ1 he.le
    have h5' : Real.rpow delta₀ e = x := h5
    rw [h5'] at h7
    have h8 : c * Real.rpow δ e ≤ c * x := by gcongr
    have h9 : c * x = 1 := by
      simp only [hx_def]
      field_simp [hc_gt_one.ne']
    rw [h9] at h8
    exact h8

/-- If `c * δ^e ≤ 1` with `e > 0`, then `c * δ^a ≤ δ^(a-e)`. -/
lemma mul_rpow_le_rpow_sub {δ c a e : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (he : 0 < e)
    (h : c * Real.rpow δ e ≤ 1) :
    c * Real.rpow δ a ≤ Real.rpow δ (a - e) := by
  have hde_pos : 0 < Real.rpow δ e := Real.rpow_pos_of_pos hδ e
  have hda_nonneg : 0 ≤ Real.rpow δ a := (Real.rpow_pos_of_pos hδ a).le
  have hc' : c ≤ (Real.rpow δ e)⁻¹ := by
    have h5 : c * Real.rpow δ e ≤ 1 := h
    have h6 : c ≤ 1 / Real.rpow δ e := by
      calc c
        = c * Real.rpow δ e / Real.rpow δ e := by field_simp [hde_pos.ne'] <;> ring
      _ ≤ 1 / Real.rpow δ e := by gcongr
    simpa [one_div] using h6
  have h7 : Real.rpow δ (a - e) = Real.rpow δ a / Real.rpow δ e := Real.rpow_sub hδ a e
  rw [h7]
  have h8 : c * Real.rpow δ a ≤ (Real.rpow δ e)⁻¹ * Real.rpow δ a := by gcongr
  have h9 : (Real.rpow δ e)⁻¹ * Real.rpow δ a = Real.rpow δ a / Real.rpow δ e := by
    field_simp [hde_pos.ne'] <;> ring
  rw [h9] at h8
  exact h8

/-- If `c * δ^e ≤ 1` with `e > 0`, then `c * δ^(a+e) ≤ δ^a`. -/
lemma mul_rpow_le_rpow_add {δ c a e : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (he : 0 < e)
    (h : c * Real.rpow δ e ≤ 1) :
    c * Real.rpow δ (a + e) ≤ Real.rpow δ a := by
  have h1 : Real.rpow δ (a + e) = Real.rpow δ a * Real.rpow δ e := Real.rpow_add hδ a e
  rw [h1]
  have h2 : 0 ≤ Real.rpow δ a := (Real.rpow_pos_of_pos hδ a).le
  calc c * (Real.rpow δ a * Real.rpow δ e)
    = Real.rpow δ a * (c * Real.rpow δ e) := by ring
  _ ≤ Real.rpow δ a * 1 := by gcongr
  _ = Real.rpow δ a := by ring

/-- `δ^a / δ^b = δ^(a-b)` in ENNReal. -/
lemma realRpowENN_div {δ a b : ℝ} (hδ : 0 < δ) :
    Kakeya.realRpowENN δ a / Kakeya.realRpowENN δ b = Kakeya.realRpowENN δ (a - b) := by
  simp only [Kakeya.realRpowENN]
  have hpos_b : 0 < Real.rpow δ b := Real.rpow_pos_of_pos hδ b
  have hpos_a : 0 ≤ Real.rpow δ a := (Real.rpow_pos_of_pos hδ a).le
  have h1 : (ENNReal.ofReal (Real.rpow δ b))⁻¹ = ENNReal.ofReal ((Real.rpow δ b)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hpos_b]
  have h2 : ENNReal.ofReal (Real.rpow δ a) / ENNReal.ofReal (Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ a / Real.rpow δ b) := by
    rw [div_eq_mul_inv, h1, ← ENNReal.ofReal_mul hpos_a]
    <;> rfl
  rw [h2]
  congr 1
  exact (Real.rpow_sub hδ a b).symm

/-- Core ENNReal cancellation for high deltaMax case:
    `(A / D) * (B * (D * V1 / (C * Vδ)) * Vδ) = A * B * (V1 / C)`. -/
lemma enreal_high_case_cancel (A B V1 Vδ C D : ENNReal)
    (hD0 : D ≠ 0) (hDtop : D ≠ ⊤)
    (hVδ0 : Vδ ≠ 0) (hVδtop : Vδ ≠ ⊤)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) :
    (A / D) * (B * (D * V1 / (C * Vδ)) * Vδ) = A * B * (V1 / C) := by
  have h1 : (A / D) * D = A := ENNReal.div_mul_cancel hD0 hDtop
  have h2 : (V1 / (C * Vδ)) * Vδ = V1 / C := by
    rw [div_eq_mul_inv]
    have h3 : (C * Vδ)⁻¹ = C⁻¹ * Vδ⁻¹ :=
      ENNReal.mul_inv (Or.inl hC0) (Or.inl hCtop)
    rw [h3]
    have h4 : V1 * (C⁻¹ * Vδ⁻¹) * Vδ = V1 * C⁻¹ := by
      calc
        V1 * (C⁻¹ * Vδ⁻¹) * Vδ
          = V1 * C⁻¹ * (Vδ⁻¹ * Vδ) := by
            simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
        _ = V1 * C⁻¹ * 1 := by rw [ENNReal.inv_mul_cancel hVδ0 hVδtop]
        _ = V1 * C⁻¹ := by simp
    rw [h4] <;> rfl
  have h_expand : D * V1 / (C * Vδ) = D * (V1 / (C * Vδ)) := by
    simp only [div_eq_mul_inv, mul_assoc] <;> rfl
  calc
    (A / D) * (B * (D * V1 / (C * Vδ)) * Vδ)
      = (A / D) * (B * (D * (V1 / (C * Vδ))) * Vδ) := by rw [h_expand]
    _ = (A / D) * D * (B * ((V1 / (C * Vδ)) * Vδ)) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
    _ = A * (B * (V1 / C)) := by rw [h1, h2] <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
    _ = A * B * (V1 / C) := by simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl

/-- `realRpowENN δ a * realRpowENN δ b = realRpowENN δ (a + b)`. -/
lemma realRpowENN_mul {δ a b : ℝ} (hδ : 0 < δ) :
    Kakeya.realRpowENN δ a * Kakeya.realRpowENN δ b =
    Kakeya.realRpowENN δ (a + b) := by
  simp only [Kakeya.realRpowENN]
  have ha : 0 ≤ Real.rpow δ a := (Real.rpow_pos_of_pos hδ a).le
  have hb : 0 ≤ Real.rpow δ b := (Real.rpow_pos_of_pos hδ b).le
  have h1 : ENNReal.ofReal (Real.rpow δ a) * ENNReal.ofReal (Real.rpow δ b) =
      ENNReal.ofReal (Real.rpow δ a * Real.rpow δ b) :=
    (ENNReal.ofReal_mul ha).symm
  rw [h1]
  have h2 : Real.rpow δ a * Real.rpow δ b = Real.rpow δ (a + b) :=
    (Real.rpow_add hδ a b).symm
  rw [h2]

/-- `(c : ENNReal) * realRpowENN δ a = ofReal (c * δ^a)` for `c ≥ 0`. -/
lemma coe_realRpowENN_eq_ofReal {c : ℝ} (hc : 0 ≤ c) {δ a : ℝ} (hδ : 0 < δ) :
    (ENNReal.ofReal c) * Kakeya.realRpowENN δ a =
    ENNReal.ofReal (c * Real.rpow δ a) := by
  simp only [Kakeya.realRpowENN]
  have ha : 0 ≤ Real.rpow δ a := (Real.rpow_pos_of_pos hδ a).le
  exact (ENNReal.ofReal_mul hc).symm

/-- `realRpowENN δ a ≤ realRpowENN δ b ↔ δ^a ≤ δ^b`. -/
lemma realRpowENN_le_iff {δ a b : ℝ} (hδ : 0 < δ) :
    Kakeya.realRpowENN δ a ≤ Kakeya.realRpowENN δ b ↔
    Real.rpow δ a ≤ Real.rpow δ b := by
  simp only [Kakeya.realRpowENN]
  have hb : 0 ≤ Real.rpow δ b := (Real.rpow_pos_of_pos hδ b).le
  rw [ENNReal.ofReal_le_ofReal_iff hb]

/-- `(realRpowENN δ a).toReal = δ^a`. -/
lemma realRpowENN_toReal {δ a : ℝ} (hδ : 0 < δ) :
    (Kakeya.realRpowENN δ a).toReal = Real.rpow δ a := by
  simp only [Kakeya.realRpowENN]
  have ha : 0 ≤ Real.rpow δ a := (Real.rpow_pos_of_pos hδ a).le
  rw [ENNReal.toReal_ofReal ha]

/-- `ofReal (c * δ^a) ≤ realRpowENN δ b` from `c * δ^a ≤ δ^b`. -/
lemma ofReal_realRpow_le_realRpow {c : ℝ} (_hc : 0 ≤ c) {δ a b : ℝ} (hδ : 0 < δ)
    (h : c * Real.rpow δ a ≤ Real.rpow δ b) :
    ENNReal.ofReal (c * Real.rpow δ a) ≤ Kakeya.realRpowENN δ b := by
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono h

/-- Convert `(c : ENNReal) * realRpowENN δ a ≤ realRpowENN δ b` from Real inequality. -/
lemma coe_realRpow_le_realRpow {c : ℝ} (hc : 0 ≤ c) {δ a b : ℝ} (hδ : 0 < δ)
    (h : c * Real.rpow δ a ≤ Real.rpow δ b) :
    (ENNReal.ofReal c) * Kakeya.realRpowENN δ a ≤ Kakeya.realRpowENN δ b := by
  rw [coe_realRpowENN_eq_ofReal hc hδ]
  exact ofReal_realRpow_le_realRpow hc hδ h

/-- Version for `(n : ENNReal)` from `Nat`/`Int` cast. -/
lemma natCoe_realRpow_le_realRpow {n : ℕ} {δ a b : ℝ} (hδ : 0 < δ)
    (h : (n : ℝ) * Real.rpow δ a ≤ Real.rpow δ b) :
    (n : ENNReal) * Kakeya.realRpowENN δ a ≤ Kakeya.realRpowENN δ b := by
  have h_cast : (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by
    simp <;> norm_cast
  rw [h_cast]
  exact coe_realRpow_le_realRpow (by positivity) hδ h

end Kakeya.Assouad.Subunit
