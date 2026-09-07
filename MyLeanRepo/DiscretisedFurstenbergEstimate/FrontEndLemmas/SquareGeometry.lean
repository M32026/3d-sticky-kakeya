module

/-
  Elementary square geometry lemmas for Team A (FrontEnd).

  Provides:
  - `squareCenter`: center of a dyadic square
  - `fine_square_subset_coarse`: fine square contained in its coarse containing square
  - `dyadicSquare_covered_by_center`: square covered by radius-δ ball around its center

  Restated from CombiningTheoremRework/Prop73/CoarseSsetConversion to avoid
  Team A importing C1 internals. Only depends on InductionConfigurations and
  elementary coordinate geometry.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.SquareGeometry

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionOnScales

attribute [local instance] Classical.propDecidable

/-- Construct a EuclideanPlane point from coordinates. -/
def ep (x y : ℝ) : EuclideanPlane := WithLp.toLp (2 : ENNReal) ![x, y]

/-- Center of a dyadic square as a EuclideanPlane point. -/
def squareCenter {m : ℕ} (δ : ℝ) (Q : DyadicSquare m) : EuclideanPlane :=
  ep (((Q.i : ℝ) + 1 / 2) * δ) (((Q.j : ℝ) + 1 / 2) * δ)

/-- A fine dyadic square is contained in its coarse containing square. -/
lemma fine_square_subset_coarse {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) :
    (p.toSet : Set EuclideanPlane) ⊆
      ((InductionConfigurations.containingSquare hnm p).toSet : Set EuclideanPlane) := by
  let Q := InductionConfigurations.containingSquare hnm p
  have h_cont : InductionConfigurations.squareContained hnm p Q :=
    (squareContained_iff_containingSquare hnm p Q).mpr rfl
  exact squareContained_toSet_subset (h := h_cont)

/-- A dyadic square of side δ is contained in a Euclidean closed ball of radius δ. -/
lemma dyadicSquare_covered_by_center {m : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_eq : δ = dyadicDelta m) (Q : DyadicSquare m) :
    (Q.toSet : Set EuclideanPlane) ⊆ Metric.closedBall (squareCenter δ Q) δ := by
  let c := squareCenter δ Q
  intro x hx
  have hxi1 : (Q.i : ℝ) * dyadicDelta m ≤ x 0 := hx.1
  have hxi2 : x 0 < ((Q.i : ℝ) + 1) * dyadicDelta m := hx.2.1
  have hxj1 : (Q.j : ℝ) * dyadicDelta m ≤ x 1 := hx.2.2.1
  have hxj2 : x 1 < ((Q.j : ℝ) + 1) * dyadicDelta m := hx.2.2.2
  have h1 : |x 0 - c 0| ≤ δ / 2 := by
    have h4 : c 0 = ((Q.i : ℝ) + 1 / 2) * δ := by simp [c, squareCenter] <;> rfl
    have h7 : (Q.i : ℝ) * δ ≤ x 0 := by
      have h8 : (Q.i : ℝ) * dyadicDelta m = (Q.i : ℝ) * δ := by rw [hδ_eq]
      rw [h8] at hxi1; exact hxi1
    have h9 : x 0 < ((Q.i : ℝ) + 1) * δ := by
      have h10 : ((Q.i : ℝ) + 1) * dyadicDelta m = ((Q.i : ℝ) + 1) * δ := by rw [hδ_eq]
      rw [h10] at hxi2; exact hxi2
    rw [h4]
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h2 : |x 1 - c 1| ≤ δ / 2 := by
    have h4 : c 1 = ((Q.j : ℝ) + 1 / 2) * δ := by simp [c, squareCenter] <;> rfl
    have h7 : (Q.j : ℝ) * δ ≤ x 1 := by
      have h8 : (Q.j : ℝ) * dyadicDelta m = (Q.j : ℝ) * δ := by rw [hδ_eq]
      rw [h8] at hxj1; exact hxj1
    have h9 : x 1 < ((Q.j : ℝ) + 1) * δ := by
      have h10 : ((Q.j : ℝ) + 1) * dyadicDelta m = ((Q.j : ℝ) + 1) * δ := by rw [hδ_eq]
      rw [h10] at hxj2; exact hxj2
    rw [h4]
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h3 : dist x c ≤ δ := by
    have h4 : dist x c ^ 2 = ∑ i : Fin 2, dist (x i) (c i) ^ 2 := EuclideanSpace.dist_sq_eq x c
    have h5 : (∑ i : Fin 2, dist (x i) (c i) ^ 2) = (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 := by
      simp [Fin.sum_univ_two, Real.dist_eq] <;> ring
    have h6 : (x 0 - c 0) ^ 2 ≤ (δ / 2) ^ 2 := by
      have h7 : |x 0 - c 0| ≤ δ / 2 := h1
      calc (x 0 - c 0) ^ 2 = |x 0 - c 0| ^ 2 := by rw [sq_abs]
        _ ≤ (δ / 2) ^ 2 := by gcongr
    have h8 : (x 1 - c 1) ^ 2 ≤ (δ / 2) ^ 2 := by
      have h9 : |x 1 - c 1| ≤ δ / 2 := h2
      calc (x 1 - c 1) ^ 2 = |x 1 - c 1| ^ 2 := by rw [sq_abs]
        _ ≤ (δ / 2) ^ 2 := by gcongr
    have h10 : (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 ≤ δ ^ 2 := by nlinarith
    have h11 : 0 ≤ dist x c := by positivity
    nlinarith
  exact h3

/-- Two distinct dyadic squares have disjoint point sets. -/
lemma dyadicSquare_toSet_disjoint {m : ℕ} {Q1 Q2 : DyadicSquare m} (h : Q1 ≠ Q2) :
    Disjoint (Q1.toSet : Set EuclideanPlane) (Q2.toSet : Set EuclideanPlane) := by
  have h_idx : Q1.i ≠ Q2.i ∨ Q1.j ≠ Q2.j := by
    by_contra h'; push Not at h'
    have h_eq : Q1 = Q2 := by
      cases Q1 <;> cases Q2 <;> simp_all
    exact h h_eq
  rcases h_idx with (h_i | h_j)
  · simp only [Set.disjoint_left, DyadicSquare.toSet, Set.mem_setOf_eq]
    intro x h1 h2
    have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
    by_cases h_lt : Q1.i < Q2.i
    · have h' : Q1.i + 1 ≤ Q2.i := by linarith
      have h1' : x 0 < ((Q1.i : ℝ) + 1) * dyadicDelta m := h1.2.1
      have h2' : (Q2.i : ℝ) * dyadicDelta m ≤ x 0 := h2.1
      have h3 : ((Q1.i : ℝ) + 1) * dyadicDelta m ≤ (Q2.i : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith
    · have h_lt2 : Q2.i < Q1.i := by
        by_contra h2; exact h_i (by omega)
      have h' : Q2.i + 1 ≤ Q1.i := by linarith
      have h2' : x 0 < ((Q2.i : ℝ) + 1) * dyadicDelta m := h2.2.1
      have h1' : (Q1.i : ℝ) * dyadicDelta m ≤ x 0 := h1.1
      have h3 : ((Q2.i : ℝ) + 1) * dyadicDelta m ≤ (Q1.i : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith
  · simp only [Set.disjoint_left, DyadicSquare.toSet, Set.mem_setOf_eq]
    intro x h1 h2
    have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
    by_cases h_lt : Q1.j < Q2.j
    · have h' : Q1.j + 1 ≤ Q2.j := by linarith
      have h1' : x 1 < ((Q1.j : ℝ) + 1) * dyadicDelta m := h1.2.2.2
      have h2' : (Q2.j : ℝ) * dyadicDelta m ≤ x 1 := h2.2.2.1
      have h3 : ((Q1.j : ℝ) + 1) * dyadicDelta m ≤ (Q2.j : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith
    · have h_lt2 : Q2.j < Q1.j := by
        by_contra h2; exact h_j (by omega)
      have h' : Q2.j + 1 ≤ Q1.j := by linarith
      have h2' : x 1 < ((Q2.j : ℝ) + 1) * dyadicDelta m := h2.2.2.2
      have h1' : (Q1.j : ℝ) * dyadicDelta m ≤ x 1 := h1.2.2.1
      have h3 : ((Q2.j : ℝ) + 1) * dyadicDelta m ≤ (Q1.j : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith

end DirecretisedFurstenbergEstimate.FrontEndLemmas.SquareGeometry
