import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

/-!
# Basic properties of ellipsoids

This file proves fundamental properties of `ellipsoid`:
nonemptiness, compactness, convexity, membership characterization,
and behavior under translation and homothety.
-/

section General

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma ellipsoid_nonempty (c : X) (A : X ≃ₗ[ℝ] X) :
    (ellipsoid c A).Nonempty := by
  have h0 : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by
    rw [Metric.mem_closedBall] <;> simp
  have hA0 : A 0 = 0 := by simp
  have h1 : (0 : X) ∈ A '' Metric.closedBall (0 : X) 1 := ⟨0, h0, hA0⟩
  exact ⟨c, ⟨0, h1, by simp⟩⟩

lemma ellipsoid_image (c : X) (A : X ≃ₗ[ℝ] X) :
    ellipsoid c A = c +ᵥ A '' Metric.closedBall 0 1 := by
  rfl

lemma ellipsoid_mem_iff (c : X) (A : X ≃ₗ[ℝ] X) (x : X) :
    x ∈ ellipsoid c A ↔ ‖A.symm (x - c)‖ ≤ 1 := by
  have h1 : x ∈ ellipsoid c A ↔
      ∃ (y : X), y ∈ Metric.closedBall (0 : X) 1 ∧ c + A y = x := by
    simp [ellipsoid, Set.mem_vadd_set, Set.mem_image]
    <;> aesop
  rw [h1]
  constructor
  · rintro ⟨y, hy, h_eq⟩
    have h_norm : ‖y‖ ≤ 1 := by
      rw [Metric.mem_closedBall] at hy
      simpa [dist_zero_right] using hy
    have h2 : A.symm (x - c) = y := by
      have h3 : x = c + A y := h_eq.symm
      rw [h3]
      simp [A.apply_symm_apply] <;> abel
    rw [h2]
    exact h_norm
  · intro h
    set y : X := A.symm (x - c) with hy_def
    have hy_norm : ‖y‖ ≤ 1 := h
    have hy_in : y ∈ Metric.closedBall (0 : X) 1 := by
      rw [Metric.mem_closedBall]
      simpa [dist_zero_right] using hy_norm
    refine' ⟨y, hy_in, _⟩
    have h4 : c + A y = x := by
      simp [hy_def, A.apply_symm_apply] <;> abel
    exact h4

lemma ellipsoid_convex (c : X) (A : X ≃ₗ[ℝ] X) :
    Convex ℝ (ellipsoid c A) := by
  have h1 : Convex ℝ (Metric.closedBall (0 : X) 1) := convex_closedBall 0 1
  have h2 : Convex ℝ (A '' Metric.closedBall (0 : X) 1) :=
    h1.linear_image A.toLinearMap
  exact h2.vadd c

lemma ellipsoid_translation (c : X) (A : X ≃ₗ[ℝ] X) (y : X) :
    y +ᵥ ellipsoid c A = ellipsoid (y + c) A := by
  ext z
  simp [ellipsoid, Set.mem_vadd_set]
  <;> constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, by abel⟩

end General

section FiniteDimensional

variable {n : ℕ} {c : E n} {A : E n ≃ₗ[ℝ] E n}

lemma ellipsoid_compact : IsCompact (ellipsoid c A) := by
  have h1 : IsCompact (Metric.closedBall (0 : E n) 1) := isCompact_closedBall 0 1
  have h2 : Continuous A := A.toLinearMap.continuous_of_finiteDimensional
  have h3 : IsCompact (A '' Metric.closedBall (0 : E n) 1) := h1.image h2
  have h4 : IsCompact (c +ᵥ A '' Metric.closedBall (0 : E n) 1) := h3.vadd c
  simpa [ellipsoid] using h4

lemma ball_is_ellipsoid {R : ℝ} (hR : 0 < R) :
    Metric.closedBall c R = ellipsoid c (Units.mk0 R hR.ne' • LinearEquiv.refl ℝ (E n)) := by
  let B : E n ≃ₗ[ℝ] E n := Units.mk0 R hR.ne' • LinearEquiv.refl ℝ (E n)
  have hB : ∀ (x : E n), B x = R • x := by
    intro x
    simp [B, LinearEquiv.smul_apply]
  ext x
  have h_iff : x ∈ Metric.closedBall c R ↔
      ∃ (v : E n), (‖v‖ ≤ 1) ∧ c + B v = x := by
    constructor
    · intro h
      set v : E n := R⁻¹ • (x - c) with hv_def
      have h_norm : ‖x - c‖ ≤ R := by simpa [dist_eq_norm, Metric.mem_closedBall] using h
      have hv_norm : ‖v‖ ≤ 1 := by
        have h : ‖v‖ = R⁻¹ * ‖x - c‖ := by
          simp [hv_def, norm_smul, Real.norm_eq_abs, abs_of_pos hR] <;> ring
        rw [h]
        have h5 : R⁻¹ * ‖x - c‖ ≤ 1 := by
          calc
            R⁻¹ * ‖x - c‖ ≤ R⁻¹ * R := by gcongr
            _ = 1 := by field_simp [hR.ne'] <;> ring
        exact h5
      have h6 : c + B v = x := by
        rw [hB v]
        simp [hv_def, smul_smul, hR.ne'] <;> abel
      exact ⟨v, hv_norm, h6⟩
    · rintro ⟨v, hv_norm, h_eq⟩
      have h9 : B v = R • v := hB v
      have h10 : x - c = R • v := by
        have h11 : c + B v = x := h_eq
        rw [h9] at h11
        exact (eq_sub_of_add_eq' h11).symm
      have h12 : ‖x - c‖ = R * ‖v‖ := by
        rw [h10, norm_smul, Real.norm_eq_abs, abs_of_pos hR] <;> ring
      rw [Metric.mem_closedBall, dist_eq_norm, h12]
      have h13 : R * ‖v‖ ≤ R := by
        calc
          R * ‖v‖ ≤ R * 1 := by gcongr
          _ = R := by ring
      exact h13
  have h_rhs : x ∈ ellipsoid c B ↔ ∃ (v : E n), (‖v‖ ≤ 1) ∧ c + B v = x := by
    simp [ellipsoid, Set.mem_vadd_set, Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    <;> rfl
  rw [h_rhs]
  exact h_iff

lemma ellipsoid_homothety {z : E n} {r : ℝ} (hr : 0 < r) :
    AffineMap.homothety z r '' ellipsoid c A =
    ellipsoid (z + r • (c - z)) (Units.mk0 r hr.ne' • A) := by
  let B : E n ≃ₗ[ℝ] E n := Units.mk0 r hr.ne' • A
  have hB : ∀ (x : E n), B x = r • A x := by
    intro x
    simp [B, LinearEquiv.smul_apply]
  ext x
  have h_lhs : x ∈ AffineMap.homothety z r '' ellipsoid c A ↔
      ∃ (v : E n), (‖v‖ ≤ 1) ∧ z + r • (c + A v - z) = x := by
    simp [ellipsoid, Set.mem_vadd_set, Set.mem_image, Metric.mem_closedBall, dist_zero_right,
      AffineMap.homothety_apply]
    <;> apply exists_congr <;> intro v <;> apply and_congr_right <;> intro _
    <;> simp [add_comm]
  have h_rhs : x ∈ ellipsoid (z + r • (c - z)) B ↔
      ∃ (v : E n), (‖v‖ ≤ 1) ∧ (z + r • (c - z)) + B v = x := by
    simp [ellipsoid, Set.mem_vadd_set, Set.mem_image, Metric.mem_closedBall, dist_zero_right]
    <;> rfl
  rw [h_lhs, h_rhs]
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  have h_eq : z + r • (c + A v - z) = (z + r • (c - z)) + B v := by
    rw [hB v]
    have h5 : r • (c + A v - z) = r • (c - z) + r • (A v) := by
      rw [show c + A v - z = (c - z) + A v by abel]
      rw [smul_add]
      <;> rfl
    rw [h5]
    <;> abel
  rw [h_eq]

end FiniteDimensional

section ZeroDimension

/-- In the zero-dimensional space, every ellipsoid is the singleton. -/
lemma ellipsoid_eq_singleton (c : E 0) (A : E 0 ≃ₗ[ℝ] E 0) :
    ellipsoid c A = {c} := by
  apply Set.Subset.antisymm
  · intro x _
    exact Subsingleton.elim x c
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have h : c ∈ ellipsoid c A := by
      have h0 : (0 : E 0) ∈ Metric.closedBall (0 : E 0) 1 := by
        rw [Metric.mem_closedBall] <;> simp
      have hA0 : A 0 = (0 : E 0) := by simp
      have h1 : (0 : E 0) ∈ A '' Metric.closedBall (0 : E 0) 1 := ⟨0, h0, hA0⟩
      exact ⟨0, h1, by simp⟩
    exact h

/-- In the zero-dimensional space, every nonempty closed ball is the singleton. -/
lemma closedBall_eq_singleton (c : E 0) {R : ℝ} (hR : 0 ≤ R) :
    Metric.closedBall c R = {c} := by
  apply Set.Subset.antisymm
  · intro x _
    exact Subsingleton.elim x c
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    rw [Metric.mem_closedBall]
    simpa using hR

end ZeroDimension

end JohnEllipsoid
