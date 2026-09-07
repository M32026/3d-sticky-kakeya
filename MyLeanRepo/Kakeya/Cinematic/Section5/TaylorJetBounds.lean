import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Absolute bounds for quadratic Taylor jets

These scalar estimates give a family-independent absolute bound for the
quadratic tails used in centered Taylor extension.
-/

namespace Kakeya.Cinematic

lemma abs_add_three (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| := by
  calc
    |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| := by linarith [abs_add_le a b]

lemma quadraticTaylorValue_abs_le_two_mul
    {M v₀ v₁ v₂ t : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ 1 / 2)
    (hv₀ : |v₀| ≤ M) (hv₁ : |v₁| ≤ M) (hv₂ : |v₂| ≤ M) :
    |v₀ + v₁ * t + (v₂ / 2) * t ^ 2| ≤ 2 * M := by
  have ht_nonneg : 0 ≤ |t| := abs_nonneg t
  have ht_sq : |t| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [mul_self_le_mul_self ht_nonneg ht]
  have hlinear : |v₁| * |t| ≤ M * (1 / 2) :=
    mul_le_mul hv₁ ht (abs_nonneg t) hM
  have hquadratic :
      (|v₂| / 2) * |t| ^ 2 ≤ (M / 2) * (1 / 2 : ℝ) ^ 2 := by
    have hhalf : |v₂| / 2 ≤ M / 2 := by linarith
    exact mul_le_mul hhalf ht_sq (sq_nonneg _) (by positivity)
  calc
    |v₀ + v₁ * t + (v₂ / 2) * t ^ 2|
        ≤ |v₀| + |v₁ * t| + |(v₂ / 2) * t ^ 2| := abs_add_three _ _ _
    _ = |v₀| + |v₁| * |t| + (|v₂| / 2) * |t| ^ 2 := by
      simp only [abs_mul, abs_div, abs_pow,
        abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    _ ≤ M + M * (1 / 2) + (M / 2) * (1 / 2 : ℝ) ^ 2 := by
      linarith
    _ ≤ 2 * M := by nlinarith

lemma quadraticTaylorFirstDeriv_abs_le_two_mul
    {M v₁ v₂ t : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ 1 / 2)
    (hv₁ : |v₁| ≤ M) (hv₂ : |v₂| ≤ M) :
    |v₁ + v₂ * t| ≤ 2 * M := by
  have hlinear : |v₂| * |t| ≤ M * (1 / 2) :=
    mul_le_mul hv₂ ht (abs_nonneg t) hM
  calc
    |v₁ + v₂ * t| ≤ |v₁| + |v₂ * t| := abs_add_le _ _
    _ = |v₁| + |v₂| * |t| := by rw [abs_mul]
    _ ≤ M + M * (1 / 2) := by linarith
    _ ≤ 2 * M := by linarith

lemma quadraticTaylorSecondDeriv_abs_le_two_mul
    {M v₂ : ℝ} (hM : 0 ≤ M) (hv₂ : |v₂| ≤ M) :
    |v₂| ≤ 2 * M := by
  linarith

theorem quadraticTaylorJet_abs_le_two_mul
    {M v₀ v₁ v₂ t : ℝ}
    (hM : 0 ≤ M) (ht : |t| ≤ 1 / 2)
    (hv₀ : |v₀| ≤ M) (hv₁ : |v₁| ≤ M) (hv₂ : |v₂| ≤ M) :
    |v₀ + v₁ * t + (v₂ / 2) * t ^ 2| ≤ 2 * M ∧
      |v₁ + v₂ * t| ≤ 2 * M ∧
        |v₂| ≤ 2 * M := by
  exact ⟨quadraticTaylorValue_abs_le_two_mul hM ht hv₀ hv₁ hv₂,
    quadraticTaylorFirstDeriv_abs_le_two_mul hM ht hv₁ hv₂,
    quadraticTaylorSecondDeriv_abs_le_two_mul hM hv₂⟩

end Kakeya.Cinematic
