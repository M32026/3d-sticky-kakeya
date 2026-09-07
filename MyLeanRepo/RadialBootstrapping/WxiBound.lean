module

/-
  WxiBound.lean

  Helper lemma: prove W * ξ₀ ≤ C₁ * r for the direction extraction width.

  W = r + (D + r) * δ / 8, δ = r / ξ₀
  W * ξ₀ = r * ξ₀ + (D + r) * r / 8
         ≤ r + (D + 1) * r / 8    (since ξ₀ < 1 and r < 1)
         = C₁ * r
  where C₁ = 1 + (D + 1) / 8.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- Prove W * ξ₀ ≤ C₁ * r where W = r + (D+r)*δ/8 and δ = r/ξ₀.

    Requires ξ₀ ≤ 1 (which follows from ξ₀ ≤ r^κ < 1) and r < 1.
    C₁ = 1 + (D + 1) / 8.
-/
lemma width_times_xi_bound
    (r ξ₀ D : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hξ₀_pos : 0 < ξ₀) (hξ₀_le_one : ξ₀ ≤ 1)
    (hD_nonneg : 0 ≤ D)
    (δ : ℝ) (hδ : δ = r / ξ₀)
    (W : ℝ) (hW : W = r + (D + r) * δ / 8)
    (C₁ : ℝ) (hC₁ : C₁ = 1 + (D + 1) / 8) :
    W * ξ₀ ≤ C₁ * r := by
  have h1 : W * ξ₀ = r * ξ₀ + (D + r) * r / 8 := by
    rw [hW, hδ]
    field_simp [hξ₀_pos.ne'] <;> ring
  rw [h1]
  have h2 : r * ξ₀ ≤ r := by
    have h3 : 0 ≤ ξ₀ := by linarith
    have h4 : ξ₀ ≤ 1 := hξ₀_le_one
    nlinarith
  have h5 : D + r ≤ D + 1 := by linarith
  have h6 : (D + r) * r / 8 ≤ (D + 1) * r / 8 := by
    have h7 : 0 ≤ r / 8 := by positivity
    gcongr
  have h8 : r * ξ₀ + (D + r) * r / 8 ≤ r + (D + 1) * r / 8 := by linarith
  have h9 : r + (D + 1) * r / 8 = C₁ * r := by
    rw [hC₁] <;> ring
  linarith [h8, h9]

end RadialBootstrapping
