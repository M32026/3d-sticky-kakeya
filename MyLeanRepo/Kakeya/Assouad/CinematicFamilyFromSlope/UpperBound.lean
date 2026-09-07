import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Assouad.CinematicBridge
import MyLeanRepo.Kakeya.Cinematic.Definitions

/-!
# Upper bound on C² distance for slope curve family

Proves that the C² distance between two slope curves is bounded by a constant
times the ℓ¹ distance of their parameter triples.

Whiteprint node: `slope_curve_upper_bound`.
-/

noncomputable section

open Kakeya.Cinematic Kakeya.Assouad

namespace Kakeya.Assouad

/--
Upper bound: the C² distance between two slope curves is controlled by
the ℓ¹ distance of their parameter triples.
-/
theorem slopeCurve_c2Distance_le (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ) :
    c2Distance (slopeCurve f a₁ b₁ d₁) (slopeCurve f a₂ b₂ d₂) ≤
    5 * (|a₁ - a₂| + |b₁ - b₂| + |d₁ - d₂|) := by
  set Δa := a₁ - a₂ with hΔa
  set Δb := b₁ - b₂ with hΔb
  set Δd := d₁ - d₂ with hΔd
  set C := 5 * (|Δa| + |Δb| + |Δd|) with hC
  let g₁ := slopeCurve f a₁ b₁ d₁
  let g₂ := slopeCurve f a₂ b₂ d₂

  have h_f_bound : ∀ (x : UnitPoint), |f x| ≤ 2 := by
    intro x
    exact abs_fx_le_two f h_ns h0 x.prop

  have h_f'_bound : ∀ (x : UnitPoint), |deriv f x| ≤ 2 := by
    intro x
    have hx : (x : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
      have hx2 : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.prop
      exact ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
    exact (h_ns x hx).2.1

  have h_f''_bound : ∀ (x : UnitPoint), |deriv (deriv f) x| ≤ 1 / 100 := by
    intro x
    have hx : (x : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
      have hx2 : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := x.prop
      exact ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
    exact (h_ns x hx).2.2

  have h_x_le_one : ∀ (x : UnitPoint), (x : ℝ) ≤ 1 := fun x => x.prop.2
  have h_x_nonneg : ∀ (x : UnitPoint), 0 ≤ (x : ℝ) := fun x => x.prop.1

  have h_abs_x_le_one : ∀ (x : UnitPoint), |(x : ℝ)| ≤ 1 := by
    intro x
    have h9 : 0 ≤ (x : ℝ) := h_x_nonneg x
    rw [abs_of_nonneg h9] <;> linarith [h_x_le_one x]

  have h_rep1 := slopeCurve_represents f a₁ b₁ d₁
  have h_rep2 := slopeCurve_represents f a₂ b₂ d₂

  have h1 : ∀ (x : UnitPoint), |g₁.value x - g₂.value x| ≤ C := by
    intro x
    have h11 : g₁.value x = slopeCurveFunction f a₁ b₁ d₁ x := (h_rep1 x).1
    have h12 : g₂.value x = slopeCurveFunction f a₂ b₂ d₂ x := (h_rep2 x).1
    have h_eq : g₁.value x - g₂.value x = Δa + Δb * f x + Δd * ((x : ℝ) * f x) := by
      rw [h11, h12]
      simp only [slopeCurveFunction, hΔa, hΔb, hΔd] <;> ring
    rw [h_eq]
    have h_tri : |Δa + Δb * f x + Δd * ((x : ℝ) * f x)| ≤
        |Δa| + |Δb * f x| + |Δd * ((x : ℝ) * f x)| := by
      exact abs_add_three Δa (Δb * f x) (Δd * ((x : ℝ) * f x))
    have h4 : |Δb * f x| ≤ |Δb| * 2 := by
      have h5 : |Δb * f x| = |Δb| * |f x| := by rw [abs_mul]
      rw [h5]
      exact mul_le_mul_of_nonneg_left (h_f_bound x) (abs_nonneg Δb)
    have h6 : |Δd * ((x : ℝ) * f x)| ≤ |Δd| * 2 := by
      have h7 : |Δd * ((x : ℝ) * f x)| = |Δd| * (|(x : ℝ)| * |f x|) := by
        rw [abs_mul, abs_mul] <;> ring
      rw [h7]
      have h8 : |(x : ℝ)| * |f x| ≤ 2 := by
        calc |(x : ℝ)| * |f x| ≤ 1 * |f x| := by gcongr <;> linarith [h_abs_x_le_one x]
          _ = |f x| := by ring
          _ ≤ 2 := h_f_bound x
      exact mul_le_mul_of_nonneg_left h8 (abs_nonneg Δd)
    have h_total : |Δa| + |Δb * f x| + |Δd * ((x : ℝ) * f x)| ≤ C := by
      have h_step : |Δa| + |Δb * f x| + |Δd * ((x : ℝ) * f x)| ≤
          |Δa| + |Δb| * 2 + |Δd| * 2 := by gcongr <;> linarith
      have h_final : |Δa| + |Δb| * 2 + |Δd| * 2 ≤ C := by
        simp only [hC]
        have ha : 0 ≤ |Δa| := abs_nonneg Δa
        have hb : 0 ≤ |Δb| := abs_nonneg Δb
        have hd : 0 ≤ |Δd| := abs_nonneg Δd
        linarith
      linarith
    exact le_trans h_tri h_total

  have h2 : ∀ (x : UnitPoint), |g₁.firstDeriv x - g₂.firstDeriv x| ≤ C := by
    intro x
    have h21 : g₁.firstDeriv x = deriv (slopeCurveFunction f a₁ b₁ d₁) x := (h_rep1 x).2.1
    have h22 : g₂.firstDeriv x = deriv (slopeCurveFunction f a₂ b₂ d₂) x := (h_rep2 x).2.1
    have h_eq : g₁.firstDeriv x - g₂.firstDeriv x =
        Δb * deriv f x + Δd * (f x + (x : ℝ) * deriv f x) := by
      rw [h21, h22, deriv_slopeCurveFunction f a₁ b₁ d₁ x,
        deriv_slopeCurveFunction f a₂ b₂ d₂ x, hΔb, hΔd] <;> ring
    rw [h_eq]
    have h_tri : |Δb * deriv f x + Δd * (f x + (x : ℝ) * deriv f x)| ≤
        |Δb * deriv f x| + |Δd * (f x + (x : ℝ) * deriv f x)| := by
      exact abs_add_le (Δb * deriv f x) (Δd * (f x + (x : ℝ) * deriv f x))
    have h4 : |Δb * deriv f x| ≤ |Δb| * 2 := by
      have h5 : |Δb * deriv f x| = |Δb| * |deriv f x| := by rw [abs_mul]
      rw [h5]
      exact mul_le_mul_of_nonneg_left (h_f'_bound x) (abs_nonneg Δb)
    have h_sum : |f x + (x : ℝ) * deriv f x| ≤ 4 := by
      have h9 : |f x + (x : ℝ) * deriv f x| ≤ |f x| + |(x : ℝ) * deriv f x| := by
        exact abs_add_le (f x) ((x : ℝ) * deriv f x)
      have h10 : |(x : ℝ) * deriv f x| = |(x : ℝ)| * |deriv f x| := by rw [abs_mul]
      rw [h10] at h9
      have h11 : |(x : ℝ)| * |deriv f x| ≤ 2 := by
        calc |(x : ℝ)| * |deriv f x| ≤ 1 * |deriv f x| := by gcongr <;> linarith [h_abs_x_le_one x]
          _ = |deriv f x| := by ring
          _ ≤ 2 := h_f'_bound x
      linarith [h_f_bound x, h9, h11]
    have h6 : |Δd * (f x + (x : ℝ) * deriv f x)| ≤ |Δd| * 4 := by
      have h7 : |Δd * (f x + (x : ℝ) * deriv f x)| =
          |Δd| * |f x + (x : ℝ) * deriv f x| := by rw [abs_mul]
      rw [h7]
      exact mul_le_mul_of_nonneg_left h_sum (abs_nonneg Δd)
    have h_total : |Δb * deriv f x| + |Δd * (f x + (x : ℝ) * deriv f x)| ≤ C := by
      have h_step : |Δb * deriv f x| + |Δd * (f x + (x : ℝ) * deriv f x)| ≤
          |Δb| * 2 + |Δd| * 4 := by gcongr <;> linarith
      have h_final : |Δb| * 2 + |Δd| * 4 ≤ C := by
        simp only [hC]
        have ha : 0 ≤ |Δa| := abs_nonneg Δa
        have hb : 0 ≤ |Δb| := abs_nonneg Δb
        have hd : 0 ≤ |Δd| := abs_nonneg Δd
        linarith
      linarith
    exact le_trans h_tri h_total

  have h3 : ∀ (x : UnitPoint), |g₁.secondDeriv x - g₂.secondDeriv x| ≤ C := by
    intro x
    have h31 : g₁.secondDeriv x = deriv (deriv (slopeCurveFunction f a₁ b₁ d₁)) x := (h_rep1 x).2.2
    have h32 : g₂.secondDeriv x = deriv (deriv (slopeCurveFunction f a₂ b₂ d₂)) x := (h_rep2 x).2.2
    have h_eq : g₁.secondDeriv x - g₂.secondDeriv x =
        Δb * deriv (deriv f) x +
        Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x) := by
      rw [h31, h32, deriv2_slopeCurveFunction f a₁ b₁ d₁ x,
        deriv2_slopeCurveFunction f a₂ b₂ d₂ x, hΔb, hΔd] <;> ring
    rw [h_eq]
    have h_tri : |Δb * deriv (deriv f) x + Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| ≤
        |Δb * deriv (deriv f) x| +
        |Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| := by
      exact abs_add_le (Δb * deriv (deriv f) x)
        (Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x))
    have h4 : |Δb * deriv (deriv f) x| ≤ |Δb| * (1 / 100) := by
      have h5 : |Δb * deriv (deriv f) x| = |Δb| * |deriv (deriv f) x| := by rw [abs_mul]
      rw [h5]
      exact mul_le_mul_of_nonneg_left (h_f''_bound x) (abs_nonneg Δb)
    have h_sum2 : |2 * deriv f x + (x : ℝ) * deriv (deriv f) x| ≤ 5 := by
      have h9 : |2 * deriv f x + (x : ℝ) * deriv (deriv f) x| ≤
          |2 * deriv f x| + |(x : ℝ) * deriv (deriv f) x| := by
        exact abs_add_le (2 * deriv f x) ((x : ℝ) * deriv (deriv f) x)
      have h10 : |2 * deriv f x| = 2 * |deriv f x| := by
        rw [abs_mul] <;> ring
      have h11 : |(x : ℝ) * deriv (deriv f) x| = |(x : ℝ)| * |deriv (deriv f) x| := by rw [abs_mul]
      rw [h10, h11] at h9
      have h12 : |(x : ℝ)| * |deriv (deriv f) x| ≤ 1 := by
        calc |(x : ℝ)| * |deriv (deriv f) x| ≤ 1 * |deriv (deriv f) x| := by gcongr <;> linarith [h_abs_x_le_one x]
          _ = |deriv (deriv f) x| := by ring
          _ ≤ 1 / 100 := h_f''_bound x
          _ ≤ 1 := by norm_num
      linarith [h_f'_bound x, h9, h12]
    have h6 : |Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| ≤ |Δd| * 5 := by
      have h7 : |Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| =
          |Δd| * |2 * deriv f x + (x : ℝ) * deriv (deriv f) x| := by rw [abs_mul]
      rw [h7]
      exact mul_le_mul_of_nonneg_left h_sum2 (abs_nonneg Δd)
    have h_total : |Δb * deriv (deriv f) x| +
        |Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| ≤ C := by
      have h_step : |Δb * deriv (deriv f) x| +
          |Δd * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x)| ≤
          |Δb| * (1 / 100) + |Δd| * 5 := by gcongr <;> linarith
      have h_final : |Δb| * (1 / 100) + |Δd| * 5 ≤ C := by
        simp only [hC]
        have ha : 0 ≤ |Δa| := abs_nonneg Δa
        have hb : 0 ≤ |Δb| := abs_nonneg Δb
        have hd : 0 ≤ |Δd| := abs_nonneg Δd
        linarith
      linarith
    exact le_trans h_tri h_total

  have hC_nonneg : 0 ≤ C := by
    simp only [hC]
    have ha : 0 ≤ |Δa| := abs_nonneg Δa
    have hb : 0 ≤ |Δb| := abs_nonneg Δb
    have hd : 0 ≤ |Δd| := abs_nonneg Δd
    linarith

  have hdist1 : dist g₁.value g₂.value ≤ C := by
    rw [ContinuousMap.dist_le hC_nonneg]
    intro x
    simpa [Real.dist_eq] using h1 x
  have hdist2 : dist g₁.firstDeriv g₂.firstDeriv ≤ C := by
    rw [ContinuousMap.dist_le hC_nonneg]
    intro x
    simpa [Real.dist_eq] using h2 x
  have hdist3 : dist g₁.secondDeriv g₂.secondDeriv ≤ C := by
    rw [ContinuousMap.dist_le hC_nonneg]
    intro x
    simpa [Real.dist_eq] using h3 x

  have h_jet : dist (C2Function.toJet g₁) (C2Function.toJet g₂) ≤ C := by
    have h_eq : dist (C2Function.toJet g₁) (C2Function.toJet g₂) =
        max (dist g₁.value g₂.value)
          (max (dist g₁.firstDeriv g₂.firstDeriv) (dist g₁.secondDeriv g₂.secondDeriv)) := by
      simp [C2Function.toJet, Prod.dist_eq]
      <;> rfl
    rw [h_eq]
    rw [max_le_iff]
    constructor
    · exact hdist1
    · rw [max_le_iff] <;> constructor <;> assumption
  exact h_jet

end Kakeya.Assouad
