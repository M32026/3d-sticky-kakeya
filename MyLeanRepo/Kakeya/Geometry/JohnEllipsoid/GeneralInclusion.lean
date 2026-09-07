import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic

noncomputable section

open JohnEllipsoid MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

/-- Core lemma: given Fritz John contact conditions for a convex body K contained in the
unit ball, prove that the 1/n-ball is contained in K. -/
lemma general_inclusion_of_fritz_john {n : ℕ} {K : Set (E n)}
    (hn : 0 < n)
    (hK_conv : Convex ℝ K)
    {ι : Type*} [Fintype ι]
    (u : ι → E n)
    (c : ι → ℝ)
    (hu_in_K : ∀ i, u i ∈ K)
    (hu_norm : ∀ i, ‖u i‖ = 1)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hc_sum : ∑ i : ι, c i = (n : ℝ))
    (h_sum_u : ∑ i : ι, c i • u i = 0)
    (h_sum_tensor : ∀ (x : E n), ∑ i : ι, (c i * inner ℝ x (u i)) • u i = x)
    : ((n : ℝ)⁻¹ • Metric.closedBall (0 : E n) 1) ⊆ K := by
  have h_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  intro x hx
  have h_norm : ‖x‖ ≤ (n : ℝ)⁻¹ := by
    rcases hx with ⟨y, hy, rfl⟩
    have h_y_norm : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy
    have h5 : ‖(n : ℝ)⁻¹ • y‖ = (n : ℝ)⁻¹ * ‖y‖ := by
      rw [norm_smul]
      <;> have h6 : ‖(n : ℝ)⁻¹‖ = (n : ℝ)⁻¹ := by
        simp [abs_of_nonneg (show 0 ≤ (n : ℝ)⁻¹ by positivity)]
      rw [h6]
    rw [h5]
    have h7 : (n : ℝ)⁻¹ * ‖y‖ ≤ (n : ℝ)⁻¹ := by
      have h8 : 0 ≤ (n : ℝ)⁻¹ := by positivity
      have h9 : (n : ℝ)⁻¹ * ‖y‖ ≤ (n : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left h_y_norm h8
      have h10 : (n : ℝ)⁻¹ * 1 = (n : ℝ)⁻¹ := by ring
      rw [h10] at h9
      exact h9
    exact h7
  let a : ι → ℝ := fun i => c i * ((n : ℝ)⁻¹ + inner ℝ x (u i))
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    have h1 : 0 ≤ c i := hc_nonneg i
    have h2 : -((n : ℝ)⁻¹) ≤ inner ℝ x (u i) := by
      have h3 : |inner ℝ x (u i)| ≤ ‖x‖ * ‖u i‖ := abs_real_inner_le_norm x (u i)
      have h4 : ‖u i‖ = 1 := hu_norm i
      rw [h4] at h3
      have h5 : |inner ℝ x (u i)| ≤ (n : ℝ)⁻¹ := by
        calc
          |inner ℝ x (u i)| ≤ ‖x‖ * 1 := h3
          _ = ‖x‖ := by ring
          _ ≤ (n : ℝ)⁻¹ := h_norm
      linarith [abs_le.mp h5]
    have h6 : 0 ≤ (n : ℝ)⁻¹ + inner ℝ x (u i) := by linarith
    exact mul_nonneg h1 h6
  have ha_sum : ∑ i : ι, a i = 1 := by
    have h : ∑ i : ι, a i = ∑ i : ι, c i * (n : ℝ)⁻¹ + ∑ i : ι, c i * inner ℝ x (u i) := by
      simp only [a, mul_add]
      rw [Finset.sum_add_distrib]
    rw [h]
    have h1 : ∑ i : ι, c i * (n : ℝ)⁻¹ = (∑ i : ι, c i) * (n : ℝ)⁻¹ := by
      rw [Finset.sum_mul] <;> ring
    rw [h1, hc_sum]
    have h2 : ∑ i : ι, c i * inner ℝ x (u i) = inner ℝ x (∑ i : ι, c i • u i) := by
      have h3 : ∑ i : ι, c i * inner ℝ x (u i) = ∑ i : ι, inner ℝ x (c i • u i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_smul_right] <;> ring
      rw [h3, inner_sum]
    rw [h2, h_sum_u, inner_zero_right]
    <;> field_simp [h_pos.ne'] <;> ring
  have h_x_eq : ∑ i : ι, a i • u i = x := by
    have h4 : ∀ i, a i • u i = (c i * (n : ℝ)⁻¹) • u i + (c i * inner ℝ x (u i)) • u i := by
      intro i
      simp only [a, mul_add]
      rw [add_smul]
    have h : ∑ i : ι, a i • u i =
        ∑ i : ι, (c i * (n : ℝ)⁻¹) • u i + ∑ i : ι, (c i * inner ℝ x (u i)) • u i := by
      calc
        ∑ i : ι, a i • u i
          = ∑ i : ι, ((c i * (n : ℝ)⁻¹) • u i + (c i * inner ℝ x (u i)) • u i) := by
            apply Finset.sum_congr rfl; intro i _; exact h4 i
        _ = ∑ i : ι, (c i * (n : ℝ)⁻¹) • u i + ∑ i : ι, (c i * inner ℝ x (u i)) • u i := by
          rw [Finset.sum_add_distrib]
    rw [h]
    have h1 : ∑ i : ι, (c i * (n : ℝ)⁻¹) • u i = (n : ℝ)⁻¹ • (∑ i : ι, c i • u i) := by
      have h2 : ∀ i, (c i * (n : ℝ)⁻¹) • u i = (n : ℝ)⁻¹ • (c i • u i) := by
        intro i
        rw [smul_smul] <;> ring_nf
      have h3 : ∑ i : ι, (c i * (n : ℝ)⁻¹) • u i = ∑ i : ι, (n : ℝ)⁻¹ • (c i • u i) := by
        apply Finset.sum_congr rfl; intro i _; exact h2 i
      rw [h3]
      exact Eq.symm Finset.smul_sum
    rw [h1, h_sum_u, smul_zero]
    have h3 : ∑ i : ι, (c i * inner ℝ x (u i)) • u i = x := h_sum_tensor x
    rw [h3, zero_add]
  have ha_nonneg' : ∀ i ∈ Finset.univ, 0 ≤ a i := fun i _ => ha_nonneg i
  have hu_in_K' : ∀ i ∈ Finset.univ, u i ∈ K := fun i _ => hu_in_K i
  have h_main : ∑ i : ι, a i • u i ∈ K := Convex.sum_mem hK_conv ha_nonneg' ha_sum hu_in_K'
  rw [h_x_eq] at h_main
  exact h_main

end JohnEllipsoid
