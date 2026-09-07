import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exponent arithmetic and volume scaling helpers
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- Volume is invariant under translation. -/
lemma volume_translation (v : Point3) {S : Set Point3} (hS : MeasurableSet S) :
    volume ((fun x => x + v) '' S) = volume S := by
  have h_eq : (fun x : Point3 => x + v) '' S = (fun x : Point3 => x + (-v)) ⁻¹' S := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨y + (-v), hy, by simp⟩
  rw [h_eq]
  exact MeasureTheory.measure_preimage_add_right volume (-v) S

/--
For `C > 0` and `a > 0`, there exists `delta₀ > 0` such that for all
`0 < δ ≤ delta₀`, we have `C ≤ δ^(-a)` (in ENNReal).
-/
lemma exists_delta₀_rpow_le_const (C : ℝ) (hC : 0 < C) (a : ℝ) (ha : 0 < a) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
        ENNReal.ofReal C ≤ Kakeya.realRpowENN δ (-a) := by
  let raw : ℝ := Real.rpow (1 / C) (1 / a)
  let delta₀ : ℝ := min 1 raw
  have hraw_pos : 0 < raw := Real.rpow_pos_of_pos (by positivity) _
  have hdelta₀_pos : 0 < delta₀ := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    exact lt_min h1 hraw_pos
  have hdelta₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  have hdelta₀_le_raw : delta₀ ≤ raw := min_le_right _ _
  exact ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, fun δ hδ_pos hδ_le => by
    have h1 : δ ≤ raw := hδ_le.trans hdelta₀_le_raw
    have h2 : Real.rpow δ a ≤ 1 / C := by
      have h3 : Real.rpow δ a ≤ Real.rpow raw a :=
        Real.rpow_le_rpow hδ_pos.le h1 (by positivity)
      have h4 : Real.rpow raw a = 1 / C := by
        have h_pos : 0 ≤ (1 / C) := by positivity
        have h_eq : Real.rpow raw a = Real.rpow (1 / C) ((1 / a) * a) := by
          simp only [raw]
          exact (Real.rpow_mul h_pos (1 / a) a).symm
        rw [h_eq]
        have h5 : (1 / a) * a = 1 := by field_simp [ha.ne'] <;> ring
        rw [h5]
        exact Real.rpow_one (1 / C)
      rw [h4] at h3
      exact h3
    have h5 : 0 < Real.rpow δ a := Real.rpow_pos_of_pos hδ_pos _
    have h6 : C * Real.rpow δ a ≤ 1 := by
      calc
        C * Real.rpow δ a ≤ C * (1 / C) := by gcongr
        _ = 1 := by field_simp [hC.ne'] <;> ring
    have h7 : C ≤ (Real.rpow δ a)⁻¹ := by
      have h8 : 0 < Real.rpow δ a := h5
      have h9 : C * Real.rpow δ a ≤ 1 := h6
      calc
        C = (C * Real.rpow δ a) / Real.rpow δ a := by field_simp [h8.ne'] <;> ring
        _ ≤ 1 / Real.rpow δ a := by gcongr
        _ = (Real.rpow δ a)⁻¹ := by ring
    have h10 : Real.rpow δ (-a) = (Real.rpow δ a)⁻¹ :=
      Real.rpow_neg hδ_pos.le a
    rw [Kakeya.realRpowENN, h10]
    exact ENNReal.ofReal_mono h7⟩

/--
For `C > 0` and `a < b`, there exists `delta₀ > 0` such that for all
`0 < δ ≤ delta₀`, we have `C * δ^b ≤ δ^a` (in ENNReal).
-/
lemma exists_delta₀_const_mul_rpow_le
    (C : ℝ) (hC : 0 < C) (a b : ℝ) (hab : a < b) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
        ENNReal.ofReal C * Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  let d : ℝ := b - a
  have hd_pos : 0 < d := by linarith
  let raw : ℝ := Real.rpow (1 / C) (1 / d)
  let delta₀ : ℝ := min 1 raw
  have hraw_pos : 0 < raw := Real.rpow_pos_of_pos (by positivity) _
  have hdelta₀_pos : 0 < delta₀ := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    exact lt_min h1 hraw_pos
  have hdelta₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  have hdelta₀_le_raw : delta₀ ≤ raw := min_le_right _ _
  exact ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, fun δ hδ_pos hδ_le => by
    have h1 : δ ≤ raw := hδ_le.trans hdelta₀_le_raw
    have h2 : Real.rpow δ d ≤ 1 / C := by
      have h3 : Real.rpow δ d ≤ Real.rpow raw d :=
        Real.rpow_le_rpow hδ_pos.le h1 (by positivity)
      have h4 : Real.rpow raw d = 1 / C := by
        have h_pos : 0 ≤ (1 / C) := by positivity
        have h_eq : Real.rpow raw d = Real.rpow (1 / C) ((1 / d) * d) := by
          simp only [raw]
          exact (Real.rpow_mul h_pos (1 / d) d).symm
        rw [h_eq]
        have h5 : (1 / d) * d = 1 := by field_simp [hd_pos.ne'] <;> ring
        rw [h5]
        exact Real.rpow_one (1 / C)
      rw [h4] at h3
      exact h3
    have h4 : C * Real.rpow δ d ≤ 1 := by
      calc
        C * Real.rpow δ d ≤ C * (1 / C) := by gcongr
        _ = 1 := by field_simp [hC.ne'] <;> ring
    have h5 : C * Real.rpow δ b ≤ Real.rpow δ a := by
      have h6 : Real.rpow δ b = Real.rpow δ a * Real.rpow δ d := by
        have h_sum : b = a + d := by linarith
        rw [h_sum]
        exact Real.rpow_add hδ_pos a d
      rw [h6]
      have h7 : 0 ≤ Real.rpow δ a := Real.rpow_nonneg hδ_pos.le _
      nlinarith
    have h8 : ENNReal.ofReal C * ENNReal.ofReal (Real.rpow δ b) ≤
        ENNReal.ofReal (Real.rpow δ a) := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ C by linarith)]
      exact ENNReal.ofReal_mono h5
    simpa [Kakeya.realRpowENN] using h8⟩

/--
For `0 < δ < 1`, if `a ≤ b` then `δ^b ≤ δ^a`.
-/
lemma rpow_monotonic_exp {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {a b : ℝ} (hab : a ≤ b) :
    Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  have h : Real.rpow δ b ≤ Real.rpow δ a :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le hab
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono h

/--
For `0 < δ ≤ 1`, `δ^a ≤ 1` when `a ≥ 0`.
-/
lemma realRpowENN_le_one {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) :
    Kakeya.realRpowENN δ a ≤ 1 := by
  have h : Real.rpow δ a ≤ 1 := Real.rpow_le_one hδ_pos.le hδ_le_one ha
  have h9 : ENNReal.ofReal (Real.rpow δ a) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_mono h
  have h10 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
  rw [h10] at h9
  simpa [Kakeya.realRpowENN] using h9

end Kakeya.Assouad
