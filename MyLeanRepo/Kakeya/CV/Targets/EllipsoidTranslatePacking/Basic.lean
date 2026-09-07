import MyLeanRepo.Kakeya.CV.Statements

/-!
# Basic geometric lemmas for ellipsoid translate packing

This file proves two foundational lemmas:

1. `center_containment`: a translate of the `η`-ellipsoid with center in
   `closedBall 0 (1/2)` lies inside the unit ball, provided the doubled
   ellipsoid is contained in the unit ball.

2. `disjointness_criterion`: two `η`-ellipsoid translates are disjoint iff
   their centers are not within a `2η`-ellipsoid of each other.

## Whiteprint node

- `EllipsoidTranslatePacking.center_containment`
- `EllipsoidTranslatePacking.disjointness_criterion`
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

/-- Unfold membership in a scaled ellipsoid. -/
lemma mem_scaledEllipsoid_iff (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z x : Point 3) :
    x ∈ scaledEllipsoid A η z ↔ ∃ (y : Point 3), ‖y‖ ≤ η ∧ z + A y = x := by
  constructor
  · intro h
    have h' : ∃ (w : Point 3), w ∈ A '' Metric.closedBall 0 η ∧ z + w = x := by
      simpa [scaledEllipsoid, Set.mem_vadd_set] using h
    rcases h' with ⟨w, ⟨y, hy, rfl⟩, hx⟩
    exact ⟨y, by simpa [Metric.mem_closedBall] using hy, hx⟩
  · rintro ⟨y, hy, hx⟩
    have h' : ∃ (w : Point 3), w ∈ A '' Metric.closedBall 0 η ∧ z + w = x :=
      ⟨A y, ⟨y, by simpa [Metric.mem_closedBall] using hy, rfl⟩, hx⟩
    simpa [scaledEllipsoid, Set.mem_vadd_set] using h'

/--
If the doubled ellipsoid `scaledEllipsoid A (2*η) 0` is contained in the unit
ball and `‖z‖ ≤ 1/2`, then `scaledEllipsoid A η z ⊆ unitBall 3`.
-/
lemma center_containment (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (z : Point 3) (h : scaledEllipsoid A (2 * η) 0 ⊆ unitBall 3)
    (hz : ‖z‖ ≤ 1 / 2) :
    scaledEllipsoid A η z ⊆ unitBall 3 := by
  intro x hx
  rcases (mem_scaledEllipsoid_iff A η z x).mp hx with ⟨y, hy1, rfl⟩
  have h2 : ‖(2 : ℝ) • y‖ ≤ 2 * η := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    <;> linarith
  have h3 : A ((2 : ℝ) • y) ∈ scaledEllipsoid A (2 * η) 0 := by
    rw [mem_scaledEllipsoid_iff A (2 * η) 0 (A ((2 : ℝ) • y))]
    refine' ⟨(2 : ℝ) • y, h2, by simp⟩
  have h4 : A ((2 : ℝ) • y) ∈ unitBall 3 := h h3
  have h5 : ‖A ((2 : ℝ) • y)‖ ≤ 1 := by
    simpa [unitBall, Metric.mem_closedBall] using h4
  have h6 : A ((2 : ℝ) • y) = (2 : ℝ) • A y := map_smul A (2 : ℝ) y
  rw [h6] at h5
  have h7 : ‖A y‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at h5
    <;> linarith
  have h8 : ‖z + A y‖ ≤ 1 := by
    calc ‖z + A y‖ ≤ ‖z‖ + ‖A y‖ := norm_add_le z (A y)
      _ ≤ 1 / 2 + 1 / 2 := by linarith
      _ = 1 := by norm_num
  simpa [unitBall, Metric.mem_closedBall] using h8

/--
Two `η`-ellipsoid translates are disjoint iff their centers are not within
a `2η`-ellipsoid of each other.
-/
lemma disjointness_criterion (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (z1 z2 : Point 3) :
    Disjoint (scaledEllipsoid A η z1) (scaledEllipsoid A η z2) ↔
      z1 ∉ scaledEllipsoid A (2 * η) z2 := by
  have h_main : (∃ x, x ∈ scaledEllipsoid A η z1 ∧ x ∈ scaledEllipsoid A η z2) ↔
      z1 ∈ scaledEllipsoid A (2 * η) z2 := by
    constructor
    · -- Forward: intersection implies z1 ∈ scaledEllipsoid A (2*η) z2
      rintro ⟨x, hx1, hx2⟩
      rcases (mem_scaledEllipsoid_iff A η z1 x).mp hx1 with ⟨y1, hy1, h_eq1⟩
      rcases (mem_scaledEllipsoid_iff A η z2 x).mp hx2 with ⟨y2, hy2, h_eq2⟩
      have h_eq : z1 + A y1 = z2 + A y2 := by
        rw [h_eq1, h_eq2]
      have h1 : z1 - z2 = A (y2 - y1) := by
        have h : z1 + A y1 = z2 + A y2 := h_eq
        have h' : z1 - z2 = A y2 - A y1 := by
          calc z1 - z2 = z1 + A y1 - (z2 + A y1) := by abel
            _ = z2 + A y2 - (z2 + A y1) := by rw [h]
            _ = A y2 - A y1 := by abel
        rw [h', map_sub]
      have h2 : ‖y2 - y1‖ ≤ 2 * η := by
        calc ‖y2 - y1‖ ≤ ‖y2‖ + ‖y1‖ := norm_sub_le y2 y1
          _ ≤ η + η := by gcongr
          _ = 2 * η := by ring
      have h4 : z1 ∈ scaledEllipsoid A (2 * η) z2 := by
        rw [mem_scaledEllipsoid_iff A (2 * η) z2 z1]
        refine' ⟨y2 - y1, h2, _⟩
        have h5 : z2 + A (y2 - y1) = z1 := by
          have h7 : A (y2 - y1) = A y2 - A y1 := map_sub A y2 y1
          calc z2 + A (y2 - y1) = z2 + (A y2 - A y1) := by rw [h7]
            _ = z2 + A y2 - A y1 := by abel
            _ = z1 + A y1 - A y1 := by rw [h_eq]
            _ = z1 := by abel
        exact h5
      exact h4
    · -- Reverse: z1 ∈ scaledEllipsoid A (2*η) z2 implies intersection
      intro h
      rcases (mem_scaledEllipsoid_iff A (2 * η) z2 z1).mp h with ⟨y, hynorm, h_eq⟩
      -- h_eq : z2 + A y = z1
      -- Decompose y = y2 - y1 using midpoint: y2 = y/2, y1 = -y/2
      set y2 : Point 3 := (1 / 2 : ℝ) • y with hy2_def
      set y1 : Point 3 := -y2 with hy1_def
      have h_y2_norm : ‖y2‖ ≤ η := by
        rw [hy2_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
        <;> linarith
      have h_y1_norm : ‖y1‖ ≤ η := by
        rw [hy1_def, norm_neg]
        exact h_y2_norm
      have h4 : y2 - y1 = y := by
        have h41 : y2 - y1 = y2 - (-y2) := by rw [hy1_def]
        rw [h41]
        have h42 : y2 - (-y2) = y2 + y2 := by simp
        rw [h42]
        have h43 : y2 + y2 = (2 : ℝ) • y2 := by
          simp [two_smul]
          <;> abel
        rw [h43, hy2_def]
        have h44 : (2 : ℝ) • ((1 / 2 : ℝ) • y) = y := by
          rw [smul_smul]
          <;> norm_num
        exact h44
      have h5 : z1 + A y1 = z2 + A y2 := by
        have h6 : z2 + A y = z1 := h_eq
        have h7 : A y = A (y2 - y1) := by rw [h4]
        rw [h7] at h6
        have h8 : z2 + (A y2 - A y1) = z1 := by
          have h9 : A (y2 - y1) = A y2 - A y1 := map_sub A y2 y1
          rw [h9] at h6 <;> exact h6
        calc z1 + A y1 = (z2 + (A y2 - A y1)) + A y1 := by rw [h8]
          _ = z2 + A y2 := by abel
      let x : Point 3 := z1 + A y1
      have hx1 : x ∈ scaledEllipsoid A η z1 := by
        rw [mem_scaledEllipsoid_iff A η z1 x]
        exact ⟨y1, h_y1_norm, rfl⟩
      have hx2 : x ∈ scaledEllipsoid A η z2 := by
        rw [show x = z2 + A y2 from h5]
        rw [mem_scaledEllipsoid_iff A η z2 (z2 + A y2)]
        exact ⟨y2, h_y2_norm, rfl⟩
      exact ⟨x, hx1, hx2⟩
  have h_disjoint : Disjoint (scaledEllipsoid A η z1) (scaledEllipsoid A η z2) ↔
      ¬ (∃ x, x ∈ scaledEllipsoid A η z1 ∧ x ∈ scaledEllipsoid A η z2) := by
    simp [Set.disjoint_left]
    <;> tauto
  rw [h_disjoint]
  rw [h_main]
  <;> rfl

/-- The center `z` belongs to the doubled ellipsoid about `z`, since `0` is in
the closed ball of radius `2*η` and `A 0 = 0`. -/
lemma ellipsoid_mem_self (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (z : Point 3) : z ∈ scaledEllipsoid A (2 * η) z := by
  have h_nonneg : 0 ≤ 2 * η := by linarith
  have h1 : (0 : Point 3) ∈ Metric.closedBall (0 : Point 3) (2 * η) := by
    simpa [Metric.mem_closedBall] using h_nonneg
  rw [mem_scaledEllipsoid_iff A (2 * η) z z]
  refine' ⟨0, by simpa [Metric.mem_closedBall] using h1, _⟩
  simp

end Kakeya.CV
