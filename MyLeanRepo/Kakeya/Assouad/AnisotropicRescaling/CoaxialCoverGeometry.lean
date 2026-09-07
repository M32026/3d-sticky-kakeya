import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoveringConstruction

/-!
# Geometry for bounded coaxial image covers

Coordinate distance control and the exact three-segment cover used by the
WZ Lemma 8 coaxial rediscretization.
-/

namespace Kakeya.Assouad

/-- The second coordinate difference is bounded by Euclidean distance. -/
lemma coord2_dist_le {x y : Point3} : |x 2 - y 2| ≤ dist x y := by
  let v := x - y
  have h1 : (v 2) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h2 : ‖v‖ ^ 2 = ∑ i : Fin 3, (v i) ^ 2 := by
      simpa using EuclideanSpace.real_norm_sq_eq v
    rw [h2]
    have h3 : (2 : Fin 3) ∈ Finset.univ := by simp
    exact Finset.single_le_sum (fun i _ => sq_nonneg (v i)) h3
  have h4 : |v 2| ≤ ‖v‖ := by
    have h5 : |v 2| ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [sq_abs]
      exact h1
    have h6 : 0 ≤ |v 2| := abs_nonneg (v 2)
    have h7 : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith
  have h8 : |x 2 - y 2| = |v 2| := by
    have h9 : v 2 = x 2 - y 2 := by simp [v]
    rw [h9]
  rw [h8]
  simpa [dist_eq_norm, v] using h4

/--
Three unit segments with bases `P`, `P + v`, and `Q - v` cover `[P,Q]`
when its signed length is nonnegative and strictly less than three.
-/
lemma three_segment_coverage {P Q : Point3} {v : Point3}
    (L : ℝ) (hL_nonneg : 0 ≤ L) (hL_lt_3 : L < 3)
    (hQP : Q - P = L • v) :
    Kakeya.unitSegment P v ∪ Kakeya.unitSegment (P + v) v ∪
      Kakeya.unitSegment (Q - v) v ⊇
    {z : Point3 | ∃ u : ℝ, 0 ≤ u ∧ u ≤ L ∧ z = P + u • v} := by
  have hQ : Q = P + L • v := by
    have h : Q - P = L • v := hQP
    have h' : Q = P + (Q - P) := by simp
    rw [h', h]
  have h_eq2 : Q - v = P + (L - 1) • v := by
    rw [hQ]
    have h2 : L • v - v = (L - 1) • v := by
      have h3 : v = (1 : ℝ) • v := (one_smul ℝ v).symm
      have h4 : L • v - v = L • v - (1 : ℝ) • v := by
        exact congr_arg (fun x : Point3 => L • v - x) h3
      rw [h4, sub_smul]
    have h4 : (P + L • v) - v = P + (L • v - v) := by
      calc
        (P + L • v) - v = P + L • v + (-v) := by rfl
        _ = P + (L • v + (-v)) := by rw [add_assoc]
        _ = P + (L • v - v) := by rfl
    rw [h4, h2]
  intro z hz
  rcases hz with ⟨u, hu_nonneg, hu_le_L, rfl⟩
  by_cases h_case1 : u ≤ 1
  · exact Or.inl (Or.inl ⟨u, ⟨hu_nonneg, h_case1⟩, by simp⟩)
  · have h_gt1 : 1 < u := by linarith
    by_cases h_case2 : u ≤ 2
    · have h_goal :
          P + u • v ∈ Kakeya.unitSegment (P + v) v := by
        refine ⟨u - 1, ⟨by linarith, by linarith⟩, ?_⟩
        have h_sum : v + (u - 1) • v = u • v := by
          have h4 :
              (1 : ℝ) • v + (u - 1) • v =
                ((1 : ℝ) + (u - 1)) • v :=
            (add_smul (1 : ℝ) (u - 1) v).symm
          have h5 : (1 : ℝ) + (u - 1) = u := by ring
          have h6 : (1 : ℝ) • v + (u - 1) • v = u • v := by
            rw [h4, h5]
          have h7 :
              v + (u - 1) • v =
                (1 : ℝ) • v + (u - 1) • v := by
            exact congr_arg
              (fun x : Point3 => x + (u - 1) • v)
              (one_smul ℝ v).symm
          rw [h7, h6]
        have h :
            (P + v) + (u - 1) • v = P + u • v := by
          rw [add_assoc, h_sum]
        exact h
      exact Or.inl (Or.inr h_goal)
    · have h_gt2 : 2 < u := by linarith
      have h_lem : L - 1 ≤ u := by linarith [hL_lt_3]
      have h_goal :
          P + u • v ∈ Kakeya.unitSegment (Q - v) v := by
        rw [h_eq2]
        refine ⟨u - (L - 1), ⟨by linarith, by linarith⟩, ?_⟩
        have h_sum :
            (L - 1) • v + (u - (L - 1)) • v = u • v := by
          have h :
              (L - 1) • v + (u - (L - 1)) • v =
                ((L - 1) + (u - (L - 1))) • v :=
            (add_smul (L - 1) (u - (L - 1)) v).symm
          rw [h]
          have h4 : (L - 1) + (u - (L - 1)) = u := by ring
          rw [h4]
        have h :
            (P + (L - 1) • v) + (u - (L - 1)) • v =
              P + u • v := by
          rw [add_assoc, h_sum]
        exact h
      exact Or.inr h_goal

end Kakeya.Assouad
