import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Direction closeness from tube containment

If a `rho`-tube T is contained in a `tau`-tube U, then their unoriented
directions are close: after choosing a sign ±1,
`‖T.direction - sign • U.direction‖ ≤ 4 * tau`.

This is a key geometric lemma for the common-container parameter cluster.
-/

noncomputable section

open Kakeya Metric Set

namespace Kakeya.Assouad

/--
If a `rho`-tube T is contained in a `tau`-tube U, then there exists a sign
`sign ∈ {1, -1}` such that `‖T.direction - sign • U.direction‖ ≤ 4 * tau`.
-/
lemma direction_closeness_from_containment {rho tau : ℝ}
    (hrho_nonneg : 0 ≤ rho) (htau_nonneg : 0 ≤ tau)
    (T : Kakeya.DeltaTube rho) (U : Kakeya.DeltaTube tau)
    (h_cont : T.carrier ⊆ U.carrier) :
    ∃ (sign : ℝ), (sign = 1 ∨ sign = -1) ∧
      ‖T.direction - sign • U.direction‖ ≤ 4 * tau := by
  let axisU := Kakeya.unitSegment U.base U.direction
  have h_compactU : IsCompact axisU := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hU_eq : U.carrier = ⋃ y ∈ axisU, Metric.closedBall y tau :=
    h_compactU.cthickening_eq_biUnion_closedBall htau_nonneg

  -- T.base is in T.carrier (at t=0 on the unit segment)
  have h_base_in_T : T.base ∈ T.carrier := by
    have h1 : T.base ∈ Kakeya.unitSegment T.base T.direction := by
      refine ⟨0, by norm_num, ?_⟩
      simp
    exact Metric.mem_cthickening_of_dist_le T.base T.base rho _ h1 (by simp [hrho_nonneg])

  -- T.base + T.direction is in T.carrier (at t=1)
  have h_end_in_T : T.base + T.direction ∈ T.carrier := by
    have h1 : T.base + T.direction ∈ Kakeya.unitSegment T.base T.direction := by
      refine ⟨1, by norm_num, ?_⟩
      simp
    exact Metric.mem_cthickening_of_dist_le (T.base + T.direction) (T.base + T.direction) rho _ h1 (by simp [hrho_nonneg])

  -- Both are in U.carrier by containment
  have h_base_in_U : T.base ∈ U.carrier := h_cont h_base_in_T
  have h_end_in_U : T.base + T.direction ∈ U.carrier := h_cont h_end_in_T

  -- Extract q0 on U's segment close to T.base
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact h_base_in_U) with ⟨q0, hq0_seg, hq0_ball⟩
  have hq0_dist : dist T.base q0 ≤ tau := by simpa [Metric.mem_closedBall] using hq0_ball

  -- Extract q1 on U's segment close to T.base + T.direction
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact h_end_in_U) with ⟨q1, hq1_seg, hq1_ball⟩
  have hq1_dist : dist (T.base + T.direction) q1 ≤ tau := by simpa [Metric.mem_closedBall] using hq1_ball

  -- Write q0 = U.base + t0 • U.direction, q1 = U.base + t1 • U.direction
  rcases hq0_seg with ⟨t0, ht0, hq0_eq⟩
  rcases hq1_seg with ⟨t1, ht1, hq1_eq⟩
  have ht0_nonneg : 0 ≤ t0 := ht0.1
  have ht0_le_one : t0 ≤ 1 := ht0.2
  have ht1_nonneg : 0 ≤ t1 := ht1.1
  have ht1_le_one : t1 ≤ 1 := ht1.2

  set s : ℝ := t1 - t0 with hs_def
  have hs_ge_neg_one : -1 ≤ s := by linarith
  have hs_le_one : s ≤ 1 := by linarith

  have h_qdiff : q1 - q0 = s • U.direction := by
    have hq0_eq' : q0 = U.base + t0 • U.direction := by exact hq0_eq.symm
    have hq1_eq' : q1 = U.base + t1 • U.direction := by exact hq1_eq.symm
    rw [hq1_eq', hq0_eq']
    have h : (U.base + t1 • U.direction) - (U.base + t0 • U.direction) = (t1 - t0) • U.direction := by
      simp [sub_smul]
    rw [h, hs_def]

  have hq0_dist' : ‖T.base - q0‖ ≤ tau := by
    simpa [dist_eq_norm] using hq0_dist
  have hq1_dist' : ‖(T.base + T.direction) - q1‖ ≤ tau := by
    simpa [dist_eq_norm] using hq1_dist

  -- Key estimate: ‖T.direction - s • U.direction‖ ≤ 2 * tau
  have h_main : ‖T.direction - s • U.direction‖ ≤ 2 * tau := by
    have h_eq1 : (T.base + T.direction) - q1 - (T.base - q0) = T.direction - (q1 - q0) := by
      abel
    have h_eq2 : T.direction - (q1 - q0) = T.direction - s • U.direction := by
      rw [h_qdiff]
    have h : ‖T.direction - s • U.direction‖ = ‖(T.base + T.direction) - q1 - (T.base - q0)‖ := by
      rw [←h_eq2, ←h_eq1]
    rw [h]
    have h_tri : ‖(T.base + T.direction) - q1 - (T.base - q0)‖ ≤
        ‖(T.base + T.direction) - q1‖ + ‖T.base - q0‖ := by
      exact norm_sub_le _ _
    calc _ ≤ ‖(T.base + T.direction) - q1‖ + ‖T.base - q0‖ := h_tri
         _ ≤ tau + tau := by gcongr
         _ = 2 * tau := by ring

  -- Lower bound on |s|: |s| ≥ 1 - 2 * tau
  have h_abs_s_lower : |s| ≥ 1 - 2 * tau := by
    have h1 : ‖s • U.direction‖ = |s| := by
      rw [norm_smul, U.direction_unit]
      ; simp
    have h2 : ‖T.direction‖ ≤ ‖s • U.direction‖ + ‖T.direction - s • U.direction‖ := by
      calc ‖T.direction‖
          = ‖s • U.direction + (T.direction - s • U.direction)‖ := by congr 1; abel
        _ ≤ ‖s • U.direction‖ + ‖T.direction - s • U.direction‖ := norm_add_le _ _
    have h4 : ‖T.direction‖ - ‖T.direction - s • U.direction‖ ≤ ‖s • U.direction‖ := by linarith
    rw [h1] at h4
    rw [T.direction_unit] at h4
    linarith [h_main]

  by_cases h_s_nonneg : 0 ≤ s
  · -- Case s ≥ 0: sign = 1
    have h_s_lower : s ≥ 1 - 2 * tau := by
      have h_abs : |s| = s := abs_of_nonneg h_s_nonneg
      rw [h_abs] at h_abs_s_lower
      exact h_abs_s_lower
    have h_one_minus_s : 1 - s ≤ 2 * tau := by linarith
    refine ⟨1, Or.inl rfl, ?_⟩
    let a := T.direction - s • U.direction
    let b := (s - 1 : ℝ) • U.direction
    have h_ab : a + b = T.direction - (1 : ℝ) • U.direction := by
      have h3 : T.direction - s • U.direction = T.direction + (-s : ℝ) • U.direction := by
        simp [sub_eq_add_neg, neg_smul]
      have h4 : (-s : ℝ) • U.direction + (s - 1 : ℝ) • U.direction = ((-s + (s - 1 : ℝ)) • U.direction) := by
        rw [←add_smul]
      have h : a + b = T.direction + ((-s + (s - 1 : ℝ)) • U.direction) := by
        simp only [a, b]
        rw [h3]
        have h5 : (T.direction + (-s : ℝ) • U.direction) + (s - 1 : ℝ) • U.direction =
            T.direction + ((-s : ℝ) • U.direction + (s - 1 : ℝ) • U.direction) := by
          rw [add_assoc]
        rw [h5]
        rw [h4]
      rw [h]
      have h2 : (-s + (s - 1 : ℝ)) = -1 := by ring
      rw [h2]
      simp [sub_eq_add_neg]
    have h6 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    have h7 : ‖b‖ = |s - 1| := by
      simp only [b, norm_smul, U.direction_unit]
      ; simp
    have h8 : ‖a + b‖ ≤ ‖a‖ + |s - 1| := by
      rw [h7] at h6
      exact h6
    have h9 : |s - 1| = 1 - s := by
      rw [abs_of_nonpos] <;> linarith
    have h10 : ‖T.direction - (1 : ℝ) • U.direction‖ ≤ ‖a‖ + (1 - s) := by
      have h11 : ‖T.direction - (1 : ℝ) • U.direction‖ = ‖a + b‖ := by rw [←h_ab]
      rw [h11]
      rw [h9] at h8
      exact h8
    have h12 : ‖a‖ = ‖T.direction - s • U.direction‖ := by rfl
    rw [h12] at h10
    linarith [h_main, h_one_minus_s]
  · -- Case s < 0: sign = -1
    have h_s_neg : s < 0 := by linarith
    have h_s_lower : s ≤ -1 + 2 * tau := by
      have h_abs : |s| = -s := abs_of_neg h_s_neg
      rw [h_abs] at h_abs_s_lower
      linarith
    have h_one_plus_s : 1 + s ≤ 2 * tau := by linarith
    refine ⟨-1, Or.inr rfl, ?_⟩
    let a := T.direction - s • U.direction
    let b := (s + 1 : ℝ) • U.direction
    have h_ab : a + b = T.direction - (-1 : ℝ) • U.direction := by
      have h3 : T.direction - s • U.direction = T.direction + (-s : ℝ) • U.direction := by
        simp [sub_eq_add_neg, neg_smul]
      have h4 : (-s : ℝ) • U.direction + (s + 1 : ℝ) • U.direction = ((-s + (s + 1 : ℝ)) • U.direction) := by
        rw [←add_smul]
      have h : a + b = T.direction + ((-s + (s + 1 : ℝ)) • U.direction) := by
        simp only [a, b]
        rw [h3]
        have h5 : (T.direction + (-s : ℝ) • U.direction) + (s + 1 : ℝ) • U.direction =
            T.direction + ((-s : ℝ) • U.direction + (s + 1 : ℝ) • U.direction) := by
          rw [add_assoc]
        rw [h5]
        rw [h4]
      rw [h]
      have h2 : (-s + (s + 1 : ℝ)) = 1 := by ring
      rw [h2]
      simp [sub_eq_add_neg]
    have h6 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    have h7 : ‖b‖ = |s + 1| := by
      simp only [b, norm_smul, U.direction_unit]
      ; simp
    have h8 : ‖a + b‖ ≤ ‖a‖ + |s + 1| := by
      rw [h7] at h6
      exact h6
    have h9 : |s + 1| = s + 1 := by
      rw [abs_of_nonneg] ; linarith
    have h10 : ‖T.direction - (-1 : ℝ) • U.direction‖ ≤ ‖a‖ + (s + 1) := by
      have h11 : ‖T.direction - (-1 : ℝ) • U.direction‖ = ‖a + b‖ := by rw [←h_ab]
      rw [h11]
      rw [h9] at h8
      exact h8
    have h12 : ‖a‖ = ‖T.direction - s • U.direction‖ := by rfl
    rw [h12] at h10
    linarith [h_main, h_one_plus_s]

end Kakeya.Assouad
