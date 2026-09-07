import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.GCongr


/-!
# Convex body from a continuous seminorm

Given a continuous seminorm `p` on a real normed space,
with a linear bound `p u ≤ B * ‖u‖`, this file proves that
`unitBall ∩ {u | p u ≤ 1}` is a John-eligible centrally symmetric convex body.
-/

noncomputable section

open Metric Set

namespace Kakeya.CV

/-- A continuous seminorm with a linear bound produces a centrally symmetric
convex body with nonempty interior. -/
lemma seminorm_convexBody
    {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (p : E → ℝ)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (h_p_hom : ∀ (c : ℝ) u, 0 ≤ c → p (c • u) = c * p u)
    (h_p_sub : ∀ u v, p (u + v) ≤ p u + p v)
    (h_p_even : ∀ u, p (-u) = p u)
    (h_p_cont : Continuous p)
    (h_p_bound : ∀ u, p u ≤ B * ‖u‖) :
    Convex ℝ (Metric.closedBall (0 : E) 1 ∩ {u | p u ≤ 1}) ∧
    IsCompact (Metric.closedBall (0 : E) 1 ∩ {u | p u ≤ 1}) ∧
    (interior (Metric.closedBall (0 : E) 1 ∩ {u | p u ≤ 1})).Nonempty ∧
    ∀ u, u ∈ (Metric.closedBall (0 : E) 1 ∩ {u | p u ≤ 1}) →
      -u ∈ (Metric.closedBall (0 : E) 1 ∩ {u | p u ≤ 1}) := by
  let body : Set E := Metric.closedBall (0 : E) 1 ∩ {u | p u ≤ 1}
  -- Convexity
  have h_convex_sublevel : Convex ℝ {u : E | p u ≤ 1} := by
    intro u hu v hv a b ha hb hab
    have h1 : p (a • u + b • v) ≤ p (a • u) + p (b • v) := h_p_sub (a • u) (b • v)
    have h2 : p (a • u) = a * p u := h_p_hom a u ha
    have h3 : p (b • v) = b * p v := h_p_hom b v hb
    rw [h2, h3] at h1
    have h41 : a * p u ≤ a * (1 : ℝ) := mul_le_mul_of_nonneg_left hu ha
    have h42 : b * p v ≤ b * (1 : ℝ) := mul_le_mul_of_nonneg_left hv hb
    have h4 : a * p u + b * p v ≤ a * (1 : ℝ) + b * (1 : ℝ) := add_le_add h41 h42
    have h5 : a * (1 : ℝ) + b * (1 : ℝ) = 1 := by
      have h6 : a + b = 1 := hab
      simpa using h6
    rw [h5] at h4
    exact le_trans h1 h4
  have h_convex_ball : Convex ℝ (Metric.closedBall (0 : E) 1) :=
    convex_closedBall 0 1
  have h_convex : Convex ℝ body := Convex.inter h_convex_ball h_convex_sublevel
  -- Symmetry
  have h_sym_body : ∀ u, u ∈ body → -u ∈ body := by
    intro u hu
    have h1 : -u ∈ Metric.closedBall (0 : E) 1 := by
      simp only [Metric.mem_closedBall] at hu ⊢
      have h_dist : dist (-u) 0 = dist u 0 := by
        simp [dist_zero_right, norm_neg]
      rw [h_dist]
      exact hu.1
    have h2 : p (-u) = p u := h_p_even u
    have h3 : p (-u) ≤ 1 := by rw [h2]; exact hu.2
    exact ⟨h1, h3⟩
  -- Closedness
  have h_closed1 : IsClosed {u : E | p u ≤ 1} := isClosed_le h_p_cont continuous_const
  have h_closed : IsClosed body := by
    have h1 : IsClosed (Metric.closedBall (0 : E) 1) := Metric.isClosed_closedBall
    exact h1.inter h_closed1
  -- Boundedness
  have h_bounded : Bornology.IsBounded body := by
    have h : body ⊆ Metric.closedBall (0 : E) 1 := fun x hx => hx.1
    exact Metric.isBounded_closedBall.subset h
  -- Compactness
  have h_compact : IsCompact body := Metric.isCompact_of_isClosed_isBounded h_closed h_bounded
  -- Nonempty interior
  let r : ℝ := 1 / max B 1
  have hr_pos : 0 < r := by
    dsimp only [r]
    positivity
  have hB_mul_r : B * r ≤ 1 := by
    dsimp only [r]
    have h9 : 0 < max B 1 := by positivity
    have h10 : B ≤ max B 1 := le_max_left _ _
    have h11 : B * (1 / max B 1) ≤ 1 := by
      calc B * (1 / max B 1)
        = B / max B 1 := by ring
      _ ≤ (max B 1) / max B 1 := by gcongr
      _ = 1 := by field_simp [h9.ne']
    exact h11
  have h_r_le_one : r ≤ 1 := by
    dsimp only [r]
    have h9 : 1 ≤ max B 1 := le_max_right _ _
    have h10 : 0 < max B 1 := by positivity
    exact (div_le_one h10).mpr h9
  have h_ball_subset : Metric.ball (0 : E) r ⊆ body := by
    intro u hu
    have h_norm_lt : ‖u‖ < r := by simpa [Metric.mem_ball] using hu
    have h_norm_le1 : ‖u‖ ≤ 1 := by linarith [h_r_le_one]
    have h_ball : u ∈ Metric.closedBall (0 : E) 1 := by
      simpa [Metric.mem_closedBall] using h_norm_le1
    have h_p_le1 : p u ≤ 1 := by
      calc p u
        ≤ B * ‖u‖ := h_p_bound u
      _ ≤ B * r := by gcongr
      _ ≤ 1 := hB_mul_r
    exact ⟨h_ball, h_p_le1⟩
  have h_interior : (interior body).Nonempty := by
    have h_open : IsOpen (Metric.ball (0 : E) r) := Metric.isOpen_ball
    have h : Metric.ball (0 : E) r ⊆ interior body := (h_open.subset_interior_iff).mpr h_ball_subset
    exact ⟨0, h (Metric.mem_ball_self hr_pos)⟩
  exact ⟨h_convex, h_compact, h_interior, h_sym_body⟩

end Kakeya.CV
