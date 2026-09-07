module

/-
# Dyadic Tubes and Point-Line Duality

This module defines the point-line duality map, dyadic δ-tubes, and establishes
key incidence properties used in the discretised Furstenberg estimate.

## Main definitions
- `NonVerticalLine`: a line y = a*x + b
- `duality`: point-line duality D(a,b) = { (x,y) | y = a*x + b }
- `DyadicTube n`: a dyadic tube at scale δ = 2^-n
- `DyadicSquare n`: a dyadic square of side δ = 2^-n

## Main results
- `tubesSlopes`: the slope map is at most 9-to-1 on tubes intersecting a fixed square
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate

/-- Triangle inequality for real absolute values. -/
lemma real_abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| :=
  abs_add_le x y

/-- Reverse triangle inequality for real absolute values. -/
lemma real_abs_sub (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have h : |x - y| = |x + (-y)| := by ring_nf
  rw [h]
  have h2 := real_abs_add x (-y)
  rw [abs_neg] at h2
  exact h2

-- ============================================================================
-- Non-vertical lines and point-line duality
-- ============================================================================

/-- A non-vertical line in the plane, given by y = a*x + b. -/
structure NonVerticalLine : Type where
  a : ℝ  -- slope
  b : ℝ  -- intercept

namespace NonVerticalLine

/-- The set of points on the line. -/
def toSet (l : NonVerticalLine) : Set EuclideanPlane :=
  {p | p 1 = l.a * p 0 + l.b}

/-- Construct from a point in parameter space (a,b). -/
def ofPoint (p : EuclideanPlane) : NonVerticalLine :=
  ⟨p 0, p 1⟩

lemma mem_toSet_iff (l : NonVerticalLine) (p : EuclideanPlane) :
    p ∈ l.toSet ↔ p 1 = l.a * p 0 + l.b := by
  rfl

end NonVerticalLine

/-- Point-line duality: D(a,b) is the line y = a*x + b. -/
def duality (p : EuclideanPlane) : NonVerticalLine :=
  NonVerticalLine.ofPoint p

-- ============================================================================
-- Dyadic scale
-- ============================================================================

/-- The dyadic scale δ = 2^-n. -/
def dyadicDelta (n : ℕ) : ℝ := 1 / (2 : ℝ)^n

lemma dyadicDelta_pos (n : ℕ) : 0 < dyadicDelta n := by
  rw [dyadicDelta]
  apply div_pos
  · norm_num
  · positivity

lemma dyadicDelta_le_one (n : ℕ) : dyadicDelta n ≤ 1 := by
  rw [dyadicDelta]
  have h : (1 : ℝ) ≤ (2 : ℝ)^n := by
    have h2 : ∀ m : ℕ, (1 : ℝ) ≤ (2 : ℝ)^m := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih => simp [pow_succ] at * <;> linarith
    exact h2 n
  exact (div_le_one (by positivity)).mpr h

lemma dyadicDelta_le_half (n : ℕ) (hn : n ≥ 1) : dyadicDelta n ≤ 1 / 2 := by
  have h2 : ∀ k : ℕ, k ≥ 1 → (2 : ℝ)^k ≥ 2 := by
    intro k hk
    induction' hk with k hk ih
    · norm_num
    · simp [pow_succ] at * <;> linarith
  have h3 : (2 : ℝ) ≤ (2 : ℝ)^n := h2 n hn
  have h4 : (1 : ℝ) / (2 : ℝ)^n ≤ (1 : ℝ) / (2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) h3
  simpa [dyadicDelta] using h4

-- ============================================================================
-- Dyadic squares
-- ============================================================================

/-- A dyadic square of side δ = 2^-n, with lower-left corner (i*δ, j*δ). -/
structure DyadicSquare (n : ℕ) : Type where
  i : ℤ
  j : ℤ

namespace DyadicSquare

variable {n : ℕ}

/-- The set of points in the half-open square [iδ, (i+1)δ) × [jδ, (j+1)δ). -/
def toSet (p : DyadicSquare n) : Set EuclideanPlane :=
  let δ := dyadicDelta n
  {x | (p.i : ℝ) * δ ≤ x 0 ∧ x 0 < ((p.i : ℝ) + 1) * δ ∧
       (p.j : ℝ) * δ ≤ x 1 ∧ x 1 < ((p.j : ℝ) + 1) * δ}

lemma toSet_nonempty (p : DyadicSquare n) : (p.toSet : Set EuclideanPlane).Nonempty := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let x : EuclideanPlane := WithLp.toLp (2 : ENNReal)
    ![((p.i : ℝ) + 1 / 2) * δ, ((p.j : ℝ) + 1 / 2) * δ]
  have h1 : (p.i : ℝ) * δ ≤ x 0 := by
    simp [x] <;> linarith
  have h2 : x 0 < ((p.i : ℝ) + 1) * δ := by
    simp [x] <;> linarith
  have h3 : (p.j : ℝ) * δ ≤ x 1 := by
    simp [x] <;> linarith
  have h4 : x 1 < ((p.j : ℝ) + 1) * δ := by
    simp [x] <;> linarith
  exact ⟨x, h1, h2, h3, h4⟩

lemma side_length {p : DyadicSquare n} {x y : EuclideanPlane}
    (hx : x ∈ p.toSet) (hy : y ∈ p.toSet) :
    |x 0 - y 0| ≤ dyadicDelta n ∧ |x 1 - y 1| ≤ dyadicDelta n := by
  set δ := dyadicDelta n with hδ
  have hxi1 : (p.i : ℝ) * δ ≤ x 0 := hx.1
  have hxi2 : x 0 < ((p.i : ℝ) + 1) * δ := hx.2.1
  have hyi1 : (p.i : ℝ) * δ ≤ y 0 := hy.1
  have hyi2 : y 0 < ((p.i : ℝ) + 1) * δ := hy.2.1
  have hxj1 : (p.j : ℝ) * δ ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((p.j : ℝ) + 1) * δ := hx.2.2.2
  have hyj1 : (p.j : ℝ) * δ ≤ y 1 := hy.2.2.1
  have hyj2 : y 1 < ((p.j : ℝ) + 1) * δ := hy.2.2.2
  constructor
  · rw [abs_sub_le_iff]; constructor <;> linarith
  · rw [abs_sub_le_iff]; constructor <;> linarith

/-- Every dyadic square is a bounded set. -/
lemma toSet_isBounded {n : ℕ} (p : DyadicSquare n) :
    Bornology.IsBounded (p.toSet : Set EuclideanPlane) := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let c : EuclideanPlane := WithLp.toLp (2 : ENNReal)
      (fun k : Fin 2 => if k = 0 then (p.i : ℝ) * δ else (p.j : ℝ) * δ)
  have hc0 : c 0 = (p.i : ℝ) * δ := by
    simp [c]
  have hc1 : c 1 = (p.j : ℝ) * δ := by
    simp [c]
  have h_main : p.toSet ⊆ Metric.closedBall c (2 * δ) := by
    intro x hx
    have h0 : |x 0 - c 0| ≤ δ := by
      rw [hc0]
      have h_i1 : (p.i : ℝ) * δ ≤ x 0 := hx.1
      have h_i2 : x 0 < ((p.i : ℝ) + 1) * δ := hx.2.1
      rw [abs_sub_le_iff] <;> constructor <;> linarith
    have h1 : |x 1 - c 1| ≤ δ := by
      rw [hc1]
      have h_j1 : (p.j : ℝ) * δ ≤ x 1 := hx.2.2.1
      have h_j2 : x 1 < ((p.j : ℝ) + 1) * δ := hx.2.2.2
      rw [abs_sub_le_iff] <;> constructor <;> linarith
    have hdist : dist x c ≤ 2 * δ := by
      have h2 : dist x c = ‖x - c‖ := by exact dist_eq_norm x c
      rw [h2]
      set z := x - c with hz
      have h_norm : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      have h3 : ‖z‖ ≤ |z 0| + |z 1| := by
        rw [h_norm]
        have h4 : 0 ≤ (z 0)^2 + (z 1)^2 := by positivity
        have h5 : Real.sqrt ((z 0)^2 + (z 1)^2) ≤ |z 0| + |z 1| := by
          rw [Real.sqrt_le_left (by positivity)]
          have h6 : (z 0)^2 + (z 1)^2 ≤ (|z 0| + |z 1|)^2 := by
            have h71 : |z 0|^2 = (z 0)^2 := by simp [sq_abs]
            have h72 : |z 1|^2 = (z 1)^2 := by simp [sq_abs]
            have h7 : (|z 0| + |z 1|)^2 = (z 0)^2 + (z 1)^2 + 2 * |z 0| * |z 1| := by
              calc
                (|z 0| + |z 1|)^2 = |z 0|^2 + |z 1|^2 + 2 * |z 0| * |z 1| := by ring
                _ = (z 0)^2 + (z 1)^2 + 2 * |z 0| * |z 1| := by rw [h71, h72]
            rw [h7]
            have h8 : 0 ≤ 2 * |z 0| * |z 1| := by positivity
            linarith
          exact h6
        exact h5
      have h10 : |z 0| = |x 0 - c 0| := by simp [hz]
      have h11 : |z 1| = |x 1 - c 1| := by simp [hz]
      rw [h10, h11] at h3
      linarith
    exact hdist
  have h_ball : Bornology.IsBounded (Metric.closedBall c (2 * δ)) :=
    Metric.isBounded_closedBall
  exact h_ball.subset h_main

/-- The center of the dyadic square. -/
def center (p : DyadicSquare n) : EuclideanPlane :=
  let δ := dyadicDelta n
  WithLp.toLp (2 : ENNReal)
    ![((p.i : ℝ) + 1 / 2) * δ, ((p.j : ℝ) + 1 / 2) * δ]

/-- Every point in the dyadic square is within distance δ_n of its center.
    (The actual maximum distance is δ_n/√2, so δ_n is a safe upper bound.) -/
lemma centered_ball {p : DyadicSquare n} {x : EuclideanPlane} (hx : x ∈ p.toSet) :
    x ∈ Metric.closedBall (p.center) (dyadicDelta n) := by
  set δ : ℝ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set c : EuclideanPlane := p.center with hc
  have hc0 : c 0 = ((p.i : ℝ) + 1 / 2) * δ := by
    simp [hc, DyadicSquare.center, hδ] <;> norm_num
  have hc1 : c 1 = ((p.j : ℝ) + 1 / 2) * δ := by
    simp [hc, DyadicSquare.center, hδ] <;> norm_num
  have h0 : |x 0 - c 0| ≤ δ / 2 := by
    rw [hc0]
    have h_i1 : (p.i : ℝ) * δ ≤ x 0 := hx.1
    have h_i2 : x 0 < ((p.i : ℝ) + 1) * δ := hx.2.1
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h1 : |x 1 - c 1| ≤ δ / 2 := by
    rw [hc1]
    have h_j1 : (p.j : ℝ) * δ ≤ x 1 := hx.2.2.1
    have h_j2 : x 1 < ((p.j : ℝ) + 1) * δ := hx.2.2.2
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have hdist : dist x c ≤ δ := by
    have h2 : dist x c = ‖x - c‖ := by
      exact dist_eq_norm x c
    rw [h2]
    set z := x - c with hz
    have h_norm : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    rw [h_norm]
    have h3 : (z 0)^2 ≤ (δ / 2)^2 := by
      have h4 : |z 0| ≤ δ / 2 := by simpa [hz] using h0
      have h5 : (z 0)^2 = |z 0|^2 := by simp [sq_abs]
      rw [h5]; gcongr <;> linarith
    have h4 : (z 1)^2 ≤ (δ / 2)^2 := by
      have h5 : |z 1| ≤ δ / 2 := by simpa [hz] using h1
      have h6 : (z 1)^2 = |z 1|^2 := by simp [sq_abs]
      rw [h6]; gcongr <;> linarith
    have h7 : Real.sqrt ((z 0)^2 + (z 1)^2) ≤ δ := by
      have h8 : (z 0)^2 + (z 1)^2 ≤ δ^2 := by
        have h9 : (z 0)^2 + (z 1)^2 ≤ (δ / 2)^2 + (δ / 2)^2 := by gcongr
        have h10 : (δ / 2)^2 + (δ / 2)^2 = δ^2 / 2 := by ring
        rw [h10] at h9
        have h11 : δ^2 / 2 ≤ δ^2 := by
          have h12 : 0 ≤ δ^2 := by positivity
          linarith
        exact h9.trans h11
      have h13 : 0 ≤ δ := by positivity
      rw [Real.sqrt_le_left h13]
      exact h8
    exact h7
  exact hdist

end DyadicSquare

-- ============================================================================
-- Dyadic tubes
-- ============================================================================

/-- A dyadic δ-tube at scale n, indexed by integer slope and intercept.
The tube is the vertical strip of width 2δ around the line y = a*δ*x + b*δ. -/
structure DyadicTube (n : ℕ) : Type where
  a : ℤ
  b : ℤ

namespace DyadicTube

variable {n : ℕ}

/-- Slope of the representative line. -/
def slope (T : DyadicTube n) : ℝ := (T.a : ℝ) * dyadicDelta n

/-- Intercept of the representative line. -/
def intercept (T : DyadicTube n) : ℝ := (T.b : ℝ) * dyadicDelta n

/-- The representative non-vertical line. -/
def line (T : DyadicTube n) : NonVerticalLine :=
  ⟨T.slope, T.intercept⟩

/-- The tube as a vertical strip: |y - slope*x - intercept| ≤ δ. -/
def toSet (T : DyadicTube n) : Set EuclideanPlane :=
  {p | |p 1 - T.slope * p 0 - T.intercept| ≤ dyadicDelta n}

/-- Distance between two dyadic tubes: L1 distance in parameter space. -/
def dist (T₁ T₂ : DyadicTube n) : ℝ :=
  |T₁.slope - T₂.slope| + |T₁.intercept - T₂.intercept|

lemma dist_eq (T₁ T₂ : DyadicTube n) :
    T₁.dist T₂ = dyadicDelta n * ((|(T₁.a - T₂.a : ℤ)| : ℝ) + (|(T₁.b - T₂.b : ℤ)| : ℝ)) := by
  set δ := dyadicDelta n with hδ
  have hpos : 0 < δ := dyadicDelta_pos n
  have h1 : T₁.slope - T₂.slope = δ * ((T₁.a : ℝ) - (T₂.a : ℝ)) := by
    simp [slope] <;> ring
  have h2 : T₁.intercept - T₂.intercept = δ * ((T₁.b : ℝ) - (T₂.b : ℝ)) := by
    simp [intercept] <;> ring
  have h3 : |δ * ((T₁.a : ℝ) - (T₂.a : ℝ))| = δ * |((T₁.a : ℝ) - (T₂.a : ℝ))| := by
    have habs : |δ * ((T₁.a : ℝ) - (T₂.a : ℝ))| = |δ| * |((T₁.a : ℝ) - (T₂.a : ℝ))| := abs_mul _ _
    rw [habs, abs_of_pos hpos]
  have h3' : |((T₁.a : ℝ) - (T₂.a : ℝ))| = (|(T₁.a - T₂.a : ℤ)| : ℝ) := by
    norm_cast
  have h4 : |δ * ((T₁.b : ℝ) - (T₂.b : ℝ))| = δ * |((T₁.b : ℝ) - (T₂.b : ℝ))| := by
    have habs : |δ * ((T₁.b : ℝ) - (T₂.b : ℝ))| = |δ| * |((T₁.b : ℝ) - (T₂.b : ℝ))| := abs_mul _ _
    rw [habs, abs_of_pos hpos]
  have h4' : |((T₁.b : ℝ) - (T₂.b : ℝ))| = (|(T₁.b - T₂.b : ℤ)| : ℝ) := by
    norm_cast
  rw [dist, h1, h2, h3, h4, h3', h4'] <;> ring

lemma dist_self (T : DyadicTube n) : T.dist T = 0 := by
  simp [dist]

lemma dist_comm (T₁ T₂ : DyadicTube n) : T₁.dist T₂ = T₂.dist T₁ := by
  simp [dist, abs_sub_comm]

lemma dist_triangle (T₁ T₂ T₃ : DyadicTube n) :
    T₁.dist T₃ ≤ T₁.dist T₂ + T₂.dist T₃ := by
  have h1 : |T₁.slope - T₃.slope| ≤ |T₁.slope - T₂.slope| + |T₂.slope - T₃.slope| :=
    abs_sub_le _ _ _
  have h2 : |T₁.intercept - T₃.intercept| ≤ |T₁.intercept - T₂.intercept| + |T₂.intercept - T₃.intercept| :=
    abs_sub_le _ _ _
  have hgoal : |T₁.slope - T₃.slope| + |T₁.intercept - T₃.intercept| ≤
      (|T₁.slope - T₂.slope| + |T₁.intercept - T₂.intercept|) +
      (|T₂.slope - T₃.slope| + |T₂.intercept - T₃.intercept|) := by
    linarith
  simpa [dist] using hgoal

lemma eq_of_dist_eq_zero (T₁ T₂ : DyadicTube n) (h : T₁.dist T₂ = 0) : T₁ = T₂ := by
  have hsum : |T₁.slope - T₂.slope| + |T₁.intercept - T₂.intercept| = 0 := h
  have hnonneg1 : 0 ≤ |T₁.slope - T₂.slope| := abs_nonneg _
  have hnonneg2 : 0 ≤ |T₁.intercept - T₂.intercept| := abs_nonneg _
  have h1 : |T₁.slope - T₂.slope| = 0 := by linarith
  have h2 : |T₁.intercept - T₂.intercept| = 0 := by linarith
  have hs : T₁.slope = T₂.slope := by
    have h4 : T₁.slope - T₂.slope = 0 := abs_eq_zero.mp h1
    exact sub_eq_zero.mp h4
  have hi : T₁.intercept = T₂.intercept := by
    have h4 : T₁.intercept - T₂.intercept = 0 := abs_eq_zero.mp h2
    exact sub_eq_zero.mp h4
  have ha : T₁.a = T₂.a := by
    have hδ : 0 < dyadicDelta n := dyadicDelta_pos n
    have : (T₁.a : ℝ) = (T₂.a : ℝ) := by
      apply (mul_right_inj' hδ.ne').mp
      simpa [slope] using hs
    exact_mod_cast this
  have hb : T₁.b = T₂.b := by
    have hδ : 0 < dyadicDelta n := dyadicDelta_pos n
    have : (T₁.b : ℝ) = (T₂.b : ℝ) := by
      apply (mul_right_inj' hδ.ne').mp
      simpa [intercept] using hi
    exact_mod_cast this
  cases T₁ with | mk a1 b1 =>
  cases T₂ with | mk a2 b2 =>
  have ha' : a1 = a2 := ha
  have hb' : b1 = b2 := hb
  congr

instance : MetricSpace (DyadicTube n) where
  dist := dist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero {T₁ T₂} h := eq_of_dist_eq_zero T₁ T₂ h

/-- Dyadic tubes are δ-separated. -/
lemma separated (T₁ T₂ : DyadicTube n) (h : T₁ ≠ T₂) :
    dyadicDelta n ≤ dist T₁ T₂ := by
  set δ := dyadicDelta n with hδ_def
  have hpos : 0 < δ := dyadicDelta_pos n
  have h1 : T₁.a ≠ T₂.a ∨ T₁.b ≠ T₂.b := by
    by_contra h2
    have h2' : T₁.a = T₂.a ∧ T₁.b = T₂.b := by
      simpa [not_or] using h2
    have h_eq : T₁ = T₂ := by
      cases T₁ with | mk a1 b1 =>
      cases T₂ with | mk a2 b2 =>
      have ha' : a1 = a2 := h2'.1
      have hb' : b1 = b2 := h2'.2
      congr
    exact h h_eq
  rcases h1 with (h1 | h1)
  · have h2 : T₁.a - T₂.a ≠ 0 := sub_ne_zero.mpr h1
    have h3 : (1 : ℝ) ≤ (|(T₁.a - T₂.a : ℤ)| : ℝ) := by
      exact_mod_cast Int.one_le_abs h2
    have h4 : (0 : ℝ) ≤ (|(T₁.b - T₂.b : ℤ)| : ℝ) := by positivity
    have h6 : (1 : ℝ) ≤ (|(T₁.a - T₂.a : ℤ)| : ℝ) + (|(T₁.b - T₂.b : ℤ)| : ℝ) := by
      linarith
    rw [dist_eq]
    have h7 : δ * 1 ≤ δ * ((|(T₁.a - T₂.a : ℤ)| : ℝ) + (|(T₁.b - T₂.b : ℤ)| : ℝ)) :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    simpa [mul_one] using h7
  · have h2 : T₁.b - T₂.b ≠ 0 := sub_ne_zero.mpr h1
    have h3 : (1 : ℝ) ≤ (|(T₁.b - T₂.b : ℤ)| : ℝ) := by
      exact_mod_cast Int.one_le_abs h2
    have h4 : (0 : ℝ) ≤ (|(T₁.a - T₂.a : ℤ)| : ℝ) := by positivity
    have h6 : (1 : ℝ) ≤ (|(T₁.a - T₂.a : ℤ)| : ℝ) + (|(T₁.b - T₂.b : ℤ)| : ℝ) := by
      linarith
    rw [dist_eq]
    have h7 : δ * 1 ≤ δ * ((|(T₁.a - T₂.a : ℤ)| : ℝ) + (|(T₁.b - T₂.b : ℤ)| : ℝ)) :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    simpa [mul_one] using h7

end DyadicTube

-- ============================================================================
-- tubesSlopes: slope map is at most 9-to-1 on tubes through a fixed square
-- ============================================================================

namespace DyadicTube

variable {n : ℕ}

/-- If two dyadic tubes with the same slope both intersect a dyadic square,
and slopes are bounded by 1, their intercept indices differ by at most 4. -/
lemma intercept_diff_bound {T₁ T₂ : DyadicTube n} {p : DyadicSquare n}
    (h_slope : T₁.a = T₂.a)
    (h1 : (T₁.toSet ∩ p.toSet).Nonempty)
    (h2 : (T₂.toSet ∩ p.toSet).Nonempty)
    (h_slope_bound : |T₁.slope| ≤ 1) :
    |(T₁.b - T₂.b : ℤ)| ≤ 4 := by
  set δ := dyadicDelta n with hδ_def
  rcases h1 with ⟨x, hxT, hxS⟩
  rcases h2 with ⟨y, hyT, hyS⟩
  have hx3 : |x 1 - T₁.slope * x 0 - T₁.intercept| ≤ δ := hxT
  have hy3 : |y 1 - T₂.slope * y 0 - T₂.intercept| ≤ δ := hyT
  have h_side : |x 0 - y 0| ≤ δ ∧ |x 1 - y 1| ≤ δ := DyadicSquare.side_length hxS hyS
  have h_slope' : T₁.slope = T₂.slope := by
    simp [slope, h_slope]
  set e1 := x 1 - T₁.slope * x 0 - T₁.intercept with he1
  set e2 := y 1 - T₂.slope * y 0 - T₂.intercept with he2
  have he1b : |e1| ≤ δ := hx3
  have he2b : |e2| ≤ δ := hy3
  have h_eq : T₁.intercept - T₂.intercept =
      (x 1 - y 1) - T₁.slope * (x 0 - y 0) - (e1 - e2) := by
    simp [he1, he2, h_slope'] <;> ring
  have h4 : |T₁.intercept - T₂.intercept| ≤
      |x 1 - y 1| + |T₁.slope| * |x 0 - y 0| + |e1| + |e2| := by
    rw [h_eq]
    let a := x 1 - y 1
    let b := T₁.slope * (x 0 - y 0)
    let c := e1 - e2
    have h_abs1 : |a - b - c| ≤ |a| + |b + c| := by
      have h : |a - (b + c)| ≤ |a| + |b + c| := real_abs_sub a (b + c)
      simpa [sub_sub] using h
    have h_abs2 : |b + c| ≤ |b| + |c| := real_abs_add b c
    have h_abs3 : |c| ≤ |e1| + |e2| := real_abs_sub e1 e2
    have h_abs4 : |b| = |T₁.slope| * |x 0 - y 0| := by rw [abs_mul]
    calc |a - b - c|
      ≤ |a| + |b + c| := h_abs1
    _ ≤ |a| + (|b| + |c|) := by linarith [h_abs2]
    _ = |a| + |b| + |c| := by ring
    _ ≤ |a| + |b| + (|e1| + |e2|) := by
      exact add_le_add (le_refl (|a| + |b|)) h_abs3
    _ = |x 1 - y 1| + |T₁.slope| * |x 0 - y 0| + |e1| + |e2| := by
        simp [a, b, h_abs4] <;> ring
  have h_x1 : |x 1 - y 1| ≤ δ := h_side.2
  have h_x0 : |x 0 - y 0| ≤ δ := h_side.1
  have h_sl : |T₁.slope| ≤ 1 := h_slope_bound
  have h_e1 : |e1| ≤ δ := he1b
  have h_e2 : |e2| ≤ δ := he2b
  have h5 : |T₁.intercept - T₂.intercept| ≤ 4 * δ := by
    calc |T₁.intercept - T₂.intercept|
      ≤ |x 1 - y 1| + |T₁.slope| * |x 0 - y 0| + |e1| + |e2| := h4
    _ ≤ δ + 1 * δ + δ + δ := by
        have h1 : |x 1 - y 1| ≤ δ := h_x1
        have h2 : |T₁.slope| * |x 0 - y 0| ≤ 1 * δ := by
          calc |T₁.slope| * |x 0 - y 0| ≤ 1 * |x 0 - y 0| := by gcongr <;> linarith
            _ ≤ 1 * δ := by gcongr
        have h3 : |e1| ≤ δ := h_e1
        have h4 : |e2| ≤ δ := h_e2
        linarith
    _ = 4 * δ := by ring
  have h7 : T₁.intercept - T₂.intercept = δ * ((T₁.b - T₂.b : ℤ) : ℝ) := by
    simp [intercept] <;> ring
  rw [h7] at h5
  have h8 : 0 < δ := dyadicDelta_pos n
  have h91 : |δ * ((T₁.b - T₂.b : ℤ) : ℝ)| = δ * |((T₁.b - T₂.b : ℤ) : ℝ)| := by
    rw [abs_mul, abs_of_pos h8]
  rw [h91] at h5
  have h10 : |((T₁.b - T₂.b : ℤ) : ℝ)| ≤ 4 := by
    nlinarith [h5, h8]
  have h14 : |(T₁.b - T₂.b : ℤ)| ≤ 4 := by
    by_cases h15 : 0 ≤ T₁.b - T₂.b
    · have h16 : |((T₁.b - T₂.b : ℤ) : ℝ)| = ((T₁.b - T₂.b : ℤ) : ℝ) := by
        rw [abs_of_nonneg] <;> exact_mod_cast h15
      have h17 : ((T₁.b - T₂.b : ℤ) : ℝ) ≤ 4 := by rw [← h16]; exact h10
      have h18 : |(T₁.b - T₂.b : ℤ)| = T₁.b - T₂.b := abs_of_nonneg h15
      rw [h18]
      exact_mod_cast h17
    · have h15' : T₁.b - T₂.b < 0 := by omega
      have h16 : |((T₁.b - T₂.b : ℤ) : ℝ)| = -((T₁.b - T₂.b : ℤ) : ℝ) := by
        rw [abs_of_neg] <;> exact_mod_cast h15'
      have h17 : (-((T₁.b - T₂.b : ℤ) : ℝ)) ≤ 4 := by rw [← h16]; exact h10
      have h18 : |(T₁.b - T₂.b : ℤ)| = -(T₁.b - T₂.b) := abs_of_neg h15'
      rw [h18]
      exact_mod_cast h17
  exact h14

/-- **tubesSlopes**: For a fixed dyadic square p, among tubes intersecting p
with bounded slope (|slope| ≤ 1), the slope map is at most 9-to-1. -/
lemma tubesSlopes {p : DyadicSquare n} {Ts : Finset (DyadicTube n)}
    (hTs : ∀ T ∈ Ts, (T.toSet ∩ p.toSet).Nonempty)
    (h_bound : ∀ T ∈ Ts, |T.slope| ≤ 1)
    (a : ℤ) :
    (Ts.filter (fun T => T.a = a)).card ≤ 9 := by
  let S := Ts.filter (fun T => T.a = a)
  by_cases h_empty : S = ∅
  · have h : (Ts.filter (fun T => T.a = a)).card = 0 := by
      simpa [S] using h_empty
    rw [h] <;> norm_num
  · have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let T0 : DyadicTube n := Classical.choose hS_ne
    have hT0_in : T0 ∈ S := Classical.choose_spec hS_ne
    have hT0_a : T0.a = a := (Finset.mem_filter.mp hT0_in).2
    have h_bounds : ∀ T ∈ S, T.b ∈ Finset.Icc (T0.b - 4) (T0.b + 4) := by
      intro T hT
      have hT_a : T.a = a := (Finset.mem_filter.mp hT).2
      have hT_in_Ts : T ∈ Ts := (Finset.mem_filter.mp hT).1
      have hT0_in_Ts : T0 ∈ Ts := (Finset.mem_filter.mp hT0_in).1
      have h_diff : |(T.b - T0.b : ℤ)| ≤ 4 := intercept_diff_bound
        (by simp [hT_a, hT0_a])
        (hTs T hT_in_Ts) (hTs T0 hT0_in_Ts) (h_bound T hT_in_Ts)
      have h10 : -(4 : ℤ) ≤ T.b - T0.b := (abs_le.mp h_diff).1
      have h11 : T.b - T0.b ≤ (4 : ℤ) := (abs_le.mp h_diff).2
      exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h_inj : Set.InjOn (fun (T : DyadicTube n) => T.b) (↑S : Set (DyadicTube n)) := by
      intro T1 hT1 T2 hT2 h
      have ha1 : T1.a = a := (Finset.mem_filter.mp hT1).2
      have ha2 : T2.a = a := (Finset.mem_filter.mp hT2).2
      have h_a : T1.a = T2.a := by linarith
      have h_b : T1.b = T2.b := h
      cases T1 with | mk a1 b1 =>
      cases T2 with | mk a2 b2 =>
      have ha' : a1 = a2 := h_a
      have hb' : b1 = b2 := h_b
      congr
    have h_card : (S.image (fun T => T.b)).card = S.card :=
      Finset.card_image_of_injOn h_inj
    have h_le : (S.image (fun T => T.b)) ⊆ Finset.Icc (T0.b - 4) (T0.b + 4) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
      exact h_bounds T hT
    have h_final : (S.image (fun T => T.b)).card ≤ (Finset.Icc (T0.b - 4) (T0.b + 4)).card :=
      Finset.card_le_card h_le
    have h_Icc : (Finset.Icc (T0.b - 4) (T0.b + 4)).card = 9 := by
      rw [Int.card_Icc]
      have h_eq : (T0.b + 4 + 1 - (T0.b - 4)) = (9 : ℤ) := by ring
      rw [h_eq]
      <;> decide
    rw [h_card] at h_final
    rw [h_Icc] at h_final
    exact h_final

end DyadicTube

/-- InStandardChart instance for DyadicTube.

    `inChart T` holds iff the slope index satisfies -2^n ≤ T.a ≤ 2^n,
    i.e. |T.slope| ≤ 1. -/
noncomputable instance {n : ℕ} :
    DirecretisedFurstenbergEstimate.InStandardChart (DyadicTube n) where
  inChart T := -(2 : ℝ)^n ≤ (T.a : ℝ) ∧ (T.a : ℝ) ≤ (2 : ℝ)^n
  slope T _ := T.slope
  intercept T _ := T.intercept
  lineOfSlopeIntercept m b :=
    let δ := dyadicDelta n
    ⟨⌊m / δ⌋, ⌊b / δ⌋⟩
  line_eq T h := by
    have h1 : T.slope / dyadicDelta n = (T.a : ℝ) := by
      simp [DyadicTube.slope, dyadicDelta] <;> field_simp <;> ring
    have h2 : T.intercept / dyadicDelta n = (T.b : ℝ) := by
      simp [DyadicTube.intercept, dyadicDelta] <;> field_simp <;> ring
    have ha : ⌊(T.a : ℝ)⌋ = T.a := by
      simp
    have hb : ⌊(T.b : ℝ)⌋ = T.b := by
      simp
    have ha' : ⌊T.slope / dyadicDelta n⌋ = T.a := by
      rw [h1] <;> exact ha
    have hb' : ⌊T.intercept / dyadicDelta n⌋ = T.b := by
      rw [h2] <;> exact hb
    have h_eq : (⟨⌊T.slope / dyadicDelta n⌋, ⌊T.intercept / dyadicDelta n⌋⟩ : DyadicTube n) = T := by
      congr <;> simp [ha', hb'] <;> omega
    exact h_eq

/-- `|T.slope| ≤ 1` implies `T` is in the standard chart. -/
lemma DyadicTube.inChart_of_slope_bound {n : ℕ} {T : DyadicTube n}
    (h : |T.slope| ≤ 1) : InStandardChart.inChart T := by
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδ_inv : dyadicDelta n = 1 / (2 : ℝ)^n := by
    simp [dyadicDelta]
    <;> field_simp
  have h_slope_eq : T.slope = (T.a : ℝ) * dyadicDelta n := by
    rfl
  have h2 : |(T.a : ℝ)| * dyadicDelta n ≤ 1 := by
    have h3 : |T.slope| = |(T.a : ℝ)| * dyadicDelta n := by
      rw [h_slope_eq, abs_mul, abs_of_pos hδ_pos]
    rw [h3] at h
    exact h
  rw [hδ_inv] at h2
  have h7 : (0 : ℝ) < (2 : ℝ)^n := by positivity
  have h4 : |(T.a : ℝ)| ≤ (2 : ℝ)^n := by
    have h9 : |(T.a : ℝ)| * (1 / (2 : ℝ)^n) ≤ 1 := h2
    have h10 : |(T.a : ℝ)| ≤ (2 : ℝ)^n := by
      by_contra h11
      have h12 : |(T.a : ℝ)| > (2 : ℝ)^n := by linarith
      have h13 : |(T.a : ℝ)| * (1 / (2 : ℝ)^n) > 1 := by
        have h14 : (0 : ℝ) < 1 / (2 : ℝ)^n := by positivity
        calc |(T.a : ℝ)| * (1 / (2 : ℝ)^n)
          > (2 : ℝ)^n * (1 / (2 : ℝ)^n) := by gcongr
        _ = 1 := by
          field_simp [h7.ne'] <;> ring
      linarith
    exact h10
  have h9 : -(2 : ℝ)^n ≤ (T.a : ℝ) := by linarith [abs_le.mp h4]
  have h10 : (T.a : ℝ) ≤ (2 : ℝ)^n := by linarith [abs_le.mp h4]
  exact ⟨h9, h10⟩

end DiscretisedFurstenbergEstimate

end
