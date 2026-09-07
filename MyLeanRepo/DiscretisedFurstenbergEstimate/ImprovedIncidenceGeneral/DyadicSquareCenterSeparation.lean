module

/-
  Phase 1 utility: DyadicSquare centers are δ-separated.

  Proves that the centers of distinct dyadic squares at scale n are at
  least dyadicDelta n apart in Euclidean distance. This enables extracting
  a δ-separated finite point set from the P₀ field of a NiceConfiguration.

  Dependencies: DyadicTubes (DyadicSquare, dyadicDelta), DyadicBridge
  (dyadicSquareCenter), BallGrowth (SeparatedAt).
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate

variable {n : ℕ}

/-- Centers of distinct dyadic squares are at least δ apart. -/
lemma dyadicSquareCenter_distinct_separated (q1 q2 : DyadicSquare n) (hne : q1 ≠ q2) :
    dyadicDelta n ≤ dist (dyadicSquareCenter q1) (dyadicSquareCenter q2) := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set c1 := dyadicSquareCenter q1 with hc1
  set c2 := dyadicSquareCenter q2 with hc2
  set v := c1 - c2 with hv
  have hc10 : c1 0 = ((q1.i : ℝ) + 1 / 2) * δ := by
    have h : c1 0 = ((q1.i : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [c1, dyadicSquareCenter] <;> rfl
    rw [h, hδ]
  have hc11 : c1 1 = ((q1.j : ℝ) + 1 / 2) * δ := by
    have h : c1 1 = ((q1.j : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [c1, dyadicSquareCenter] <;> rfl
    rw [h, hδ]
  have hc20 : c2 0 = ((q2.i : ℝ) + 1 / 2) * δ := by
    have h : c2 0 = ((q2.i : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [c2, dyadicSquareCenter] <;> rfl
    rw [h, hδ]
  have hc21 : c2 1 = ((q2.j : ℝ) + 1 / 2) * δ := by
    have h : c2 1 = ((q2.j : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [c2, dyadicSquareCenter] <;> rfl
    rw [h, hδ]
  have h_norm_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    have h_pos : 0 ≤ (v 0) ^ 2 + (v 1) ^ 2 := by positivity
    have h : ‖v‖ = Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
    rw [h]
    rw [Real.sq_sqrt h_pos]
  have h_abs_le_norm0 : |v 0| ≤ ‖v‖ := by
    have h : (v 0) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [h_norm_sq] <;> nlinarith [sq_nonneg (v 1)]
    have h2 : 0 ≤ |v 0| := by positivity
    have h3 : 0 ≤ ‖v‖ := by positivity
    nlinarith [sq_abs (v 0)]
  have h_abs_le_norm1 : |v 1| ≤ ‖v‖ := by
    have h : (v 1) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [h_norm_sq] <;> nlinarith [sq_nonneg (v 0)]
    have h2 : 0 ≤ |v 1| := by positivity
    have h3 : 0 ≤ ‖v‖ := by positivity
    nlinarith [sq_abs (v 1)]
  have h_coord : (q1.i ≠ q2.i) ∨ (q1.j ≠ q2.j) := by
    by_contra h
    push Not at h
    have h_i : q1.i = q2.i := h.1
    have h_j : q1.j = q2.j := h.2
    have h_eq : q1 = q2 := by
      cases q1 <;> cases q2 <;> simp_all <;> tauto
    exact hne h_eq
  rcases h_coord with (h_i | h_j)
  · -- q1.i ≠ q2.i
    have h_int : (1 : ℝ) ≤ |(q1.i : ℝ) - (q2.i : ℝ)| := by
      have h1 : q1.i - q2.i ≠ 0 := by omega
      have h2 : (1 : ℤ) ≤ |q1.i - q2.i| := Int.one_le_abs h1
      exact_mod_cast h2
    have h_diff0 : v 0 = δ * ((q1.i : ℝ) - (q2.i : ℝ)) := by
      have hv0 : v 0 = c1 0 - c2 0 := by simp [v]
      rw [hv0, hc10, hc20] <;> ring
    have h_abs0 : δ ≤ |v 0| := by
      rw [h_diff0, abs_mul, abs_of_pos hδ_pos]
      have h3 : δ * |(q1.i : ℝ) - (q2.i : ℝ)| ≥ δ * 1 := by gcongr
      linarith
    have h5 : δ ≤ ‖v‖ := by
      calc δ ≤ |v 0| := h_abs0
           _ ≤ ‖v‖ := h_abs_le_norm0
    have h_goal : dist c1 c2 = ‖v‖ := by
      rw [dist_eq_norm, hv]
    rw [h_goal]
    exact h5
  · -- q1.j ≠ q2.j
    have h_int : (1 : ℝ) ≤ |(q1.j : ℝ) - (q2.j : ℝ)| := by
      have h1 : q1.j - q2.j ≠ 0 := by omega
      have h2 : (1 : ℤ) ≤ |q1.j - q2.j| := Int.one_le_abs h1
      exact_mod_cast h2
    have h_diff1 : v 1 = δ * ((q1.j : ℝ) - (q2.j : ℝ)) := by
      have hv1 : v 1 = c1 1 - c2 1 := by simp [v]
      rw [hv1, hc11, hc21] <;> ring
    have h_abs1 : δ ≤ |v 1| := by
      rw [h_diff1, abs_mul, abs_of_pos hδ_pos]
      have h3 : δ * |(q1.j : ℝ) - (q2.j : ℝ)| ≥ δ * 1 := by gcongr
      linarith
    have h5 : δ ≤ ‖v‖ := by
      calc δ ≤ |v 1| := h_abs1
           _ ≤ ‖v‖ := h_abs_le_norm1
    have h_goal : dist c1 c2 = ‖v‖ := by
      rw [dist_eq_norm, hv]
    rw [h_goal]
    exact h5

/-- `dyadicSquareCenter` is injective. -/
lemma dyadicSquareCenter_injective :
    Function.Injective (dyadicSquareCenter (n := n)) := by
  intro q1 q2 h
  have h0 : (dyadicSquareCenter q1) 0 = (dyadicSquareCenter q2) 0 := by rw [h]
  have h1 : (dyadicSquareCenter q1) 1 = (dyadicSquareCenter q2) 1 := by rw [h]
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  set δ := dyadicDelta n with hδ
  have h_eq0 : ((q1.i : ℝ) + 1 / 2) * δ = ((q2.i : ℝ) + 1 / 2) * δ := by
    have h_a : (dyadicSquareCenter q1) 0 = ((q1.i : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [dyadicSquareCenter] <;> rfl
    have h_b : (dyadicSquareCenter q2) 0 = ((q2.i : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [dyadicSquareCenter] <;> rfl
    rw [h_a, h_b] at h0
    simpa [hδ] using h0
  have h_eq1 : ((q1.j : ℝ) + 1 / 2) * δ = ((q2.j : ℝ) + 1 / 2) * δ := by
    have h_a : (dyadicSquareCenter q1) 1 = ((q1.j : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [dyadicSquareCenter] <;> rfl
    have h_b : (dyadicSquareCenter q2) 1 = ((q2.j : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [dyadicSquareCenter] <;> rfl
    rw [h_a, h_b] at h1
    simpa [hδ] using h1
  have hi : (q1.i : ℝ) = (q2.i : ℝ) := by
    apply (mul_right_inj' hδ_pos.ne').mp
    linarith
  have hj : (q1.j : ℝ) = (q2.j : ℝ) := by
    apply (mul_right_inj' hδ_pos.ne').mp
    linarith
  have hi' : q1.i = q2.i := by exact_mod_cast hi
  have hj' : q1.j = q2.j := by exact_mod_cast hj
  cases q1 <;> cases q2 <;> simp_all <;> tauto

/-- The image of a Finset of DyadicSquares under dyadicSquareCenter is
    a SeparatedAt δ set. -/
lemma dyadicSquareCenters_separated (P₀ : Finset (DyadicSquare n)) :
    SSetBridges.SeparatedAt (dyadicDelta n)
      (↑(P₀.image dyadicSquareCenter) : Set Plane) := by
  have h_main : Set.Pairwise (↑(P₀.image dyadicSquareCenter) : Set Plane)
      (fun p p' => dyadicDelta n ≤ dist p p') := by
    intro p hp p' hp' hne
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hp' with ⟨q', hq', rfl⟩
    have hqne : q ≠ q' := by
      intro h
      apply hne
      rw [h]
    exact dyadicSquareCenter_distinct_separated q q' hqne
  exact h_main

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
