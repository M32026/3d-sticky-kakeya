module

/-
  A1 Stage Assembly: Heavy-square refinement → canonical A1_Output.

  Pipeline:
  1. Targeted selection: Pfin → Qset (heavy coarse squares)
  2. S-set conversion: Qset center ball-growth → IsDeltaSSet Δ t (Δ^{-20ε})
  3. Point selection: per-square δ-separated subsets with cardinality bounds
  4. Assemble canonical A1_Output (using input tube families directly)

  Additional hypotheses (established upstream):
  - hTp_sep: input tube families are already δ-separated
  - h_tube_uniform: raw tube families have cardinality within factor 2

  Whiteprint node: appendix_a_alternative / A1_heavy_square_refinement
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SeparatedSubset
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_TargetedSelection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_Stub4
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

set_option maxHeartbeats 500000

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.A1_Assembly

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Cobalt
open DirecretisedFurstenbergEstimate.Lagoon (squareSet squareCenter)
open DirecretisedFurstenbergEstimate.Phase2 (squareIndex)

abbrev Plane := EuclideanPlane
abbrev FineTube := AffineLine

/-- Helper: extract a δ-separated subset from a finite set, given a bound K
    on points in any open δ-ball. Output size ≥ |P|/K. -/
lemma extract_separated_subset_fin
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (δ : ℝ) (hδ_pos : 0 < δ)
    (P : Finset X) (K : ℕ) (hK_pos : 0 < K)
    (h_local : ∀ x ∈ P, (P.filter (fun y => dist x y < δ)).card ≤ K) :
    ∃ (S : Finset X), S ⊆ P ∧
      SSetBridges.SeparatedAt δ (S : Set X) ∧
      (S.card : ℝ) ≥ (P.card : ℝ) / (K : ℝ) := by
  let R : X → X → Prop := fun x y => dist x y < δ
  have hR_sym : ∀ x ∈ P, ∀ y ∈ P, R x y → R y x := by
    intro x _ y _ h
    have h' : dist y x < δ := by rw [dist_comm]; exact h
    exact h'
  have hR_refl : ∀ x ∈ P, R x x := by
    intro x _; simp [R, dist_self, hδ_pos]
  have h_main :=
    DiscretisedFurstenbergEstimate.InductionOnScales.Separated.exists_separated_subset
      P R hR_sym hR_refl K hK_pos h_local
  rcases h_main with ⟨S, hS_sub, hS_sep, hS_card⟩
  have hS_sep' : SSetBridges.SeparatedAt δ (S : Set X) := by
    dsimp only [SSetBridges.SeparatedAt]
    intro x hx y hy hne
    have h : ¬ R x y := hS_sep x hx y hy hne
    have h' : ¬ (dist x y < δ) := by simpa [R] using h
    have h'' : δ ≤ dist x y := by linarith
    exact h''
  exact ⟨S, hS_sub, hS_sep', hS_card⟩

/-! ========================================================================
   A1 Stage Main Definition
   ======================================================================== -/

/-- **A1 stage: heavy-square refinement with point and tube extraction.**

    Additional hypotheses:
    - `hTp_sep`: input tube families are already δ-separated
    - `h_tube_uniform`: raw tube cardinalities within factor 2 globally
-/
def a1_stage
    {Δ δ t s ε : ℝ}
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ)
    (hδ_le_D : δ ≤ Δ)
    (ht : 0 < t)
    (ht_lt_two : t < 2)
    (hs : 0 < s)
    (hs_lt_one : s < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    -- Point set
    (Pfin : Finset Plane)
    (hP_in_ball : (Pfin : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2))
    (hP_y_bound : ∀ p ∈ Pfin, |p 1| ≤ Real.sqrt 2)
    (hP_sep : SSetBridges.SeparatedAt δ (Pfin : Set Plane))
    (hP_card_lower : Real.rpow Δ (-2 * t + ε / 4) ≤ (Pfin.card : ℝ))
    (hP_card_upper : (Pfin.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4))
    (hP_ball_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin.card : ℝ))
    (hN_cover : ∀ (Q_all : Finset (ℤ × ℤ)),
      Q_all = Pfin.image (fun p => squareIndex Δ p) →
      (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2))
    -- Tube families
    (Tp : Plane → Finset FineTube)
    (hTp_sset : ∀ p ∈ Pfin,
      IsDeltaSSet δ s (Real.rpow δ (-ε)) (Tp p : Set FineTube))
    (hTp_sep : ∀ p ∈ Pfin,
      SSetBridges.SeparatedAt (δ / 2) (Tp p : Set FineTube))
    (h_tube_card_lower : ∀ p ∈ Pfin,
      Real.rpow Δ (-2 * s + 2 * ε) ≤ (Tp p).card)
    (h_tube_card_upper : ∀ p ∈ Pfin,
      (Tp p).card ≤ Real.rpow Δ (-2 * s - ε))
    (M_in : ℕ)
    (hM_in_pos : 0 < M_in)
    (hM_in_even : M_in % 2 = 0)
    (h_tube_uniform : ∀ p ∈ Pfin, M_in / 2 ≤ (Tp p).card ∧ (Tp p).card ≤ M_in)
    (h_slope_bound : ∀ p ∈ Pfin, ∀ T ∈ Tp p,
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3)
    (h_inc : ∀ p ∈ Pfin, ∀ T ∈ Tp p,
      p ∈ Metric.cthickening (2 * δ) T.1)
    (hP_sset : IsDeltaSSet δ t (Real.rpow δ (-2 * ε)) (Pfin : Set Plane)) :
    A1_Output Δ δ t s ε := by
  have hΔ_lt_one : Δ < 1 := by linarith

  -- Step 1: Targeted heavy-square selection
  have h_small' : Real.rpow Δ (ε / 4) ≤ 1 / 2 :=
    le_trans h_small (by norm_num)
  have h1 : ∃ (Qset : Finset (ℤ × ℤ)),
      (Real.rpow Δ (-t + 3 * ε) ≤ (Qset.card : ℝ)) ∧
      ((Qset.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)) ∧
      (∀ Q ∈ Qset,
        Real.rpow Δ (-t + 3 * ε) ≤ ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ∧
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)) :=
    a1_targeted_selection hΔ_pos hΔ_lt_half ht hε_pos Pfin
      hP_card_lower hP_card_upper hP_ball_growth hN_cover h_small'
  let Qset : Finset (ℤ × ℤ) := Classical.choose h1
  have hQ_spec := Classical.choose_spec h1
  have hQ_card_lower : Real.rpow Δ (-t + 3 * ε) ≤ (Qset.card : ℝ) := hQ_spec.1
  have hQ_card_upper_3ε : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := hQ_spec.2.1
  have hQ_heavy : ∀ Q ∈ Qset,
      Real.rpow Δ (-t + 3 * ε) ≤ ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ∧
      ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := hQ_spec.2.2
  -- Stronger -ε bound from covering number: Qset ⊆ Q_all and Q_all.card ≤ Δ^{-t-ε/2} < Δ^{-t-ε}
  have hQ_all : Qset ⊆ Pfin.image (fun p => squareIndex Δ p) := by
    intro Q hQ
    have h_heavy : Real.rpow Δ (-t + 3 * ε) ≤ ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) :=
      (hQ_heavy Q hQ).1
    have h_nonempty : (Pfin.filter (fun p => p ∈ squareSet Δ Q)).Nonempty := by
      have h_pos : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h_card : 0 < (Pfin.filter (fun p => p ∈ squareSet Δ Q)).card := by
        exact_mod_cast lt_of_lt_of_le h_pos h_heavy
      exact Finset.card_pos.mp h_card
    rcases h_nonempty with ⟨p, hp⟩
    have h_p_in : p ∈ squareSet Δ Q := (Finset.mem_filter.mp hp).2
    have h_idx1 : (Q.1 : ℝ) ≤ p 0 / Δ ∧ p 0 / Δ < (Q.1 : ℝ) + 1 := by
      have h1 : Δ * (Q.1 : ℝ) ≤ p 0 := h_p_in.1.1
      have h2 : p 0 < Δ * ((Q.1 : ℝ) + 1) := h_p_in.1.2
      have h1' : (Q.1 : ℝ) ≤ p 0 / Δ := by
        calc (Q.1 : ℝ) = (Δ * (Q.1 : ℝ)) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
          _ ≤ (p 0) / Δ := by gcongr
      have h2' : p 0 / Δ < (Q.1 : ℝ) + 1 := by
        calc p 0 / Δ < (Δ * ((Q.1 : ℝ) + 1)) / Δ := by gcongr
          _ = (Q.1 : ℝ) + 1 := by field_simp [hΔ_pos.ne'] <;> ring
      exact ⟨h1', h2'⟩
    have h_idx2 : (Q.2 : ℝ) ≤ p 1 / Δ ∧ p 1 / Δ < (Q.2 : ℝ) + 1 := by
      have h1 : Δ * (Q.2 : ℝ) ≤ p 1 := h_p_in.2.1
      have h2 : p 1 < Δ * ((Q.2 : ℝ) + 1) := h_p_in.2.2
      have h1' : (Q.2 : ℝ) ≤ p 1 / Δ := by
        calc (Q.2 : ℝ) = (Δ * (Q.2 : ℝ)) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
          _ ≤ (p 1) / Δ := by gcongr
      have h2' : p 1 / Δ < (Q.2 : ℝ) + 1 := by
        calc p 1 / Δ < (Δ * ((Q.2 : ℝ) + 1)) / Δ := by gcongr
          _ = (Q.2 : ℝ) + 1 := by field_simp [hΔ_pos.ne'] <;> ring
      exact ⟨h1', h2'⟩
    have h_floor1 : ⌊p 0 / Δ⌋ = Q.1 := by
      rw [Int.floor_eq_iff] <;> exact ⟨by linarith, by linarith⟩
    have h_floor2 : ⌊p 1 / Δ⌋ = Q.2 := by
      rw [Int.floor_eq_iff] <;> exact ⟨by linarith, by linarith⟩
    have h_idx : squareIndex Δ p = Q := by
      simp [squareIndex, h_floor1, h_floor2] <;> rfl
    exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, h_idx⟩
  have hQ_card_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := by
    let Q_all := Pfin.image (fun p => squareIndex Δ p)
    have h1 : (Qset.card : ℝ) ≤ (Q_all.card : ℝ) := by exact_mod_cast Finset.card_le_card hQ_all
    have h2 : (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := hN_cover Q_all rfl
    have h3 : Real.rpow Δ (-t - ε / 2) ≤ Real.rpow Δ (-t - ε) := by
      apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos <;> linarith
    exact le_trans (le_trans h1 h2) h3

  have hQset_nonempty : Qset.Nonempty := by
    have h_pos : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_card_pos : 0 < (Qset.card : ℝ) := lt_of_lt_of_le h_pos hQ_card_lower
    have h_nat_pos : 0 < Qset.card := by exact_mod_cast h_card_pos
    exact Finset.card_pos.mp h_nat_pos

  -- Step 2: Qset center ball-growth via geometric enlargement
  -- Constant Δ^{-17ε/2} from |Pfin|/|Qset| ratio with ±3ε bounds
  have hQset_center_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) := by
    intro c r hr
    let S := Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)
    let R := (1 + Real.sqrt 2 / 2) * r
    have hR_ge_D : Δ ≤ R := by
      dsimp only [R]
      have h9 : 1 + Real.sqrt 2 / 2 ≥ 1 := by linarith [Real.sqrt_nonneg 2]
      nlinarith
    have hr_nonneg : 0 ≤ r := by linarith
    have h_geom : ∀ Q ∈ S, (Pfin.filter (fun p => p ∈ squareSet Δ Q)) ⊆
        Pfin.filter (fun y => dist c y ≤ R) := by
      intro Q hQ p hp
      have h_p_in_square : p ∈ squareSet Δ Q := (Finset.mem_filter.mp hp).2
      have h_p_in_Pfin : p ∈ Pfin := (Finset.mem_filter.mp hp).1
      have h_center_dist : dist (squareCenter Δ Q) c ≤ r := (Finset.mem_filter.mp hQ).2
      have h_square_diam : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
        Lagoon.point_in_square_close_to_center hΔ_pos Q p h_p_in_square
      have h10 : Real.sqrt 2 * Δ / 2 ≤ Real.sqrt 2 / 2 * r := by
        have h11 : (Real.sqrt 2 / 2) * Δ ≤ (Real.sqrt 2 / 2) * r := by gcongr
        ring_nf at h11 ⊢; exact h11
      have h_final : dist c p ≤ R := by
        calc dist c p
          ≤ dist c (squareCenter Δ Q) + dist (squareCenter Δ Q) p := dist_triangle _ _ _
        _ = dist (squareCenter Δ Q) c + dist p (squareCenter Δ Q) := by
          rw [dist_comm c (squareCenter Δ Q), dist_comm (squareCenter Δ Q) p]
        _ ≤ r + Real.sqrt 2 * Δ / 2 := by gcongr
        _ ≤ (1 + Real.sqrt 2 / 2) * r := by linarith [Real.sqrt_nonneg 2, h10]
      exact Finset.mem_filter.mpr ⟨h_p_in_Pfin, h_final⟩
    have h_disj : ∀ Q1 ∈ S, ∀ Q2 ∈ S, Q1 ≠ Q2 →
        Disjoint (Pfin.filter (fun p => p ∈ squareSet Δ Q1))
          (Pfin.filter (fun p => p ∈ squareSet Δ Q2)) := by
      intro Q1 _ Q2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p ∈ squareSet Δ Q1 := (Finset.mem_filter.mp hp1).2
      have h2 : p ∈ squareSet Δ Q2 := (Finset.mem_filter.mp hp2).2
      have h_eq1 : squareIndex Δ p = Q1 := Phase2.squareIndex_unique hΔ_pos p Q1 h1
      have h_eq2 : squareIndex Δ p = Q2 := Phase2.squareIndex_unique hΔ_pos p Q2 h2
      have h_eq : Q1 = Q2 := by
        exact h_eq1.symm.trans h_eq2
      exact False.elim (hne h_eq)
    have h_sum : ∑ Q ∈ S, (Pfin.filter (fun p => p ∈ squareSet Δ Q)).card ≤
        (Pfin.filter (fun y => dist c y ≤ R)).card := by
      have h_bunion : (S.biUnion (fun Q => Pfin.filter (fun p => p ∈ squareSet Δ Q))) ⊆
          Pfin.filter (fun y => dist c y ≤ R) := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨Q, hQ, hxQ⟩
        exact h_geom Q hQ hxQ
      have h_card : (S.biUnion (fun Q => Pfin.filter (fun p => p ∈ squareSet Δ Q))).card =
          ∑ Q ∈ S, (Pfin.filter (fun p => p ∈ squareSet Δ Q)).card := by
        rw [Finset.card_biUnion]
        · exact h_disj
      rw [←h_card]
      exact Finset.card_le_card h_bunion
    have h_each_lower : ∀ Q ∈ S, Real.rpow Δ (-t + 3 * ε) ≤
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
      intro Q hQ
      have hQ' : Q ∈ Qset := (Finset.mem_filter.mp hQ).1
      exact (hQ_heavy Q hQ').1
    have h_lower : (S.card : ℝ) * Real.rpow Δ (-t + 3 * ε) ≤
        ∑ Q ∈ S, ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
      have h : ∑ Q ∈ S, ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ≥
          ∑ Q ∈ S, Real.rpow Δ (-t + 3 * ε) := by
        apply Finset.sum_le_sum
        intro Q hQ
        exact h_each_lower Q hQ
      have h2 : ∑ Q ∈ S, Real.rpow Δ (-t + 3 * ε) = (S.card : ℝ) * Real.rpow Δ (-t + 3 * ε) := by
        simp [Finset.sum_const] <;> ring
      rw [h2] at h
      exact h
    have h_lower' : (S.card : ℝ) * Real.rpow Δ (-t + 3 * ε) ≤
        ((Pfin.filter (fun y => dist c y ≤ R)).card : ℝ) := by
      exact h_lower.trans (by exact_mod_cast h_sum)
    have hR_expand : R^t = (1 + Real.sqrt 2 / 2)^t * r^t := by
      dsimp only [R]
      have h_nonneg1 : 0 ≤ 1 + Real.sqrt 2 / 2 := by positivity
      rw [Real.mul_rpow h_nonneg1 hr_nonneg] <;> ring
    have h_upper : ((Pfin.filter (fun y => dist c y ≤ R)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * (1 + Real.sqrt 2 / 2)^t * r^t * (Pfin.card : ℝ) := by
      have h := hP_ball_growth c R hR_ge_D
      rw [hR_expand] at h
      have h_eq : Real.rpow Δ (-9 * ε / 4) * ((1 + Real.sqrt 2 / 2)^t * r^t) * (Pfin.card : ℝ) =
          Real.rpow Δ (-9 * ε / 4) * (1 + Real.sqrt 2 / 2)^t * r^t * (Pfin.card : ℝ) := by ring
      rw [h_eq] at h
      exact h
    have h_pos1 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos_eps4 : 0 < Real.rpow Δ (-9 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos_geom : 0 < (1 + Real.sqrt 2 / 2)^t := by positivity
    have h_pos_rt : 0 ≤ r^t := by positivity
    let X := Real.rpow Δ (-9 * ε / 4) * (1 + Real.sqrt 2 / 2)^t * r^t * (Pfin.card : ℝ)
    let Y := Real.rpow Δ (-t + 3 * ε)
    -- h9: |S| ≤ X / Y
    have h_combined : (S.card : ℝ) * Y ≤ X := by
      calc (S.card : ℝ) * Y
        ≤ ((Pfin.filter (fun y => dist c y ≤ R)).card : ℝ) := h_lower'
      _ ≤ Real.rpow Δ (-9 * ε / 4) * (1 + Real.sqrt 2 / 2)^t * r^t * (Pfin.card : ℝ) := h_upper
    have h9 : (S.card : ℝ) ≤ X / Y := by
      have h91 : ((S.card : ℝ) * Y) / Y = (S.card : ℝ) := by
        rw [mul_div_cancel_right₀ (S.card : ℝ) h_pos1.ne']
      have h92 : ((S.card : ℝ) * Y) / Y ≤ X / Y := div_le_div_of_nonneg_right h_combined h_pos1.le
      rw [h91] at h92
      exact h92
    -- Key ratio bound: |Pfin| ≤ Δ^{-t-13ε/4} * |Qset| (from ±3ε card bounds)
    have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
      intro a b; exact (Real.rpow_add hΔ_pos a b).symm
    have h14 : Real.rpow Δ (-t - 13 * ε / 4) * Real.rpow Δ (-t + 3 * ε) = Real.rpow Δ (-2 * t - ε / 4) := by
      have h := h_rpow_mul (-t - 13 * ε / 4) (-t + 3 * ε)
      have h2 : (-t - 13 * ε / 4) + (-t + 3 * ε) = -2 * t - ε / 4 := by ring
      rw [h2] at h; exact h
    have h_pos_big : 0 < Real.rpow Δ (-t - 13 * ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h10 : (Pfin.card : ℝ) ≤ Real.rpow Δ (-t - 13 * ε / 4) * (Qset.card : ℝ) := by
      calc (Pfin.card : ℝ)
        ≤ Real.rpow Δ (-2 * t - ε / 4) := hP_card_upper
      _ = Real.rpow Δ (-t - 13 * ε / 4) * Real.rpow Δ (-t + 3 * ε) := h14.symm
      _ ≤ Real.rpow Δ (-t - 13 * ε / 4) * (Qset.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left hQ_card_lower h_pos_big.le
    -- Multiply by Δ^{-9ε/4}: Δ^{-9ε/4} * |Pfin| ≤ Δ^{-17ε/2} * Δ^{-t+3ε} * |Qset|
    have h16 : Real.rpow Δ (-9 * ε / 4) * Real.rpow Δ (-t - 13 * ε / 4) = Real.rpow Δ (-t - 11 * ε / 2) := by
      have h := h_rpow_mul (-9 * ε / 4) (-t - 13 * ε / 4)
      have h2 : (-9 * ε / 4) + (-t - 13 * ε / 4) = -t - 11 * ε / 2 := by ring
      rw [h2] at h; exact h
    have h17 : Real.rpow Δ (-t - 11 * ε / 2) = Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-t + 3 * ε) := by
      have h := h_rpow_mul (-17 * ε / 2) (-t + 3 * ε)
      have h2 : (-17 * ε / 2) + (-t + 3 * ε) = -t - 11 * ε / 2 := by ring
      rw [h2] at h; exact h.symm
    have h15 : Real.rpow Δ (-9 * ε / 4) * (Pfin.card : ℝ) ≤
        Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-t + 3 * ε) * (Qset.card : ℝ) := by
      calc Real.rpow Δ (-9 * ε / 4) * (Pfin.card : ℝ)
        ≤ Real.rpow Δ (-9 * ε / 4) * (Real.rpow Δ (-t - 13 * ε / 4) * (Qset.card : ℝ)) :=
          mul_le_mul_of_nonneg_left h10 h_pos_eps4.le
      _ = (Real.rpow Δ (-9 * ε / 4) * Real.rpow Δ (-t - 13 * ε / 4)) * (Qset.card : ℝ) := by ring
      _ = Real.rpow Δ (-t - 11 * ε / 2) * (Qset.card : ℝ) := by rw [h16]
      _ = (Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-t + 3 * ε)) * (Qset.card : ℝ) := by rw [h17]
      _ = Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-t + 3 * ε) * (Qset.card : ℝ) := by ring
    -- h18: X / Y ≤ Δ^{-17ε/2} * geom * r^t * |Qset|
    let Z := Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ)
    have h18 : X / Y ≤ Z := by
      have h_mult : X ≤ Z * Y := by
        dsimp only [X, Y, Z]
        have h : Real.rpow Δ (-9 * ε / 4) * (Pfin.card : ℝ) ≤
            Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-t + 3 * ε) * (Qset.card : ℝ) := h15
        have h_geom_nonneg : 0 ≤ (1 + Real.sqrt 2 / 2)^t * r^t := by positivity
        have h' : Real.rpow Δ (-9 * ε / 4) * (Pfin.card : ℝ) * ((1 + Real.sqrt 2 / 2)^t * r^t) ≤
            (Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-t + 3 * ε) * (Qset.card : ℝ)) * ((1 + Real.sqrt 2 / 2)^t * r^t) :=
          mul_le_mul_of_nonneg_right h h_geom_nonneg
        have h_final : Real.rpow Δ (-9 * ε / 4) * (1 + Real.sqrt 2 / 2)^t * r^t * (Pfin.card : ℝ) ≤
            Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Real.rpow Δ (-t + 3 * ε) * (Qset.card : ℝ)) := by
          ring_nf at h' ⊢; exact h'
        have h'' : Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Real.rpow Δ (-t + 3 * ε) * (Qset.card : ℝ)) =
            (Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ)) * Real.rpow Δ (-t + 3 * ε) := by ring
        rw [h''] at h_final
        exact h_final
      have h_div : X / Y ≤ (Z * Y) / Y := by gcongr
      have h_cancel : (Z * Y) / Y = Z := by
        rw [mul_div_cancel_right₀ Z h_pos1.ne']
      rw [h_cancel] at h_div
      exact h_div
    exact le_trans h9 h18

  -- Step 3: Weak absorption lemmas for a1_ball_growth_to_sset_weak
  have hrpow_add : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm

  have h_small_absorb_weak : (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-13 * ε / 2) := by
    have h_const : (1 + Real.sqrt 2 / 2)^t ≤ 4 := by
      have h_sqrt2_le2 : Real.sqrt 2 ≤ 2 := by
        have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h2 : Real.sqrt 4 = 2 := by norm_num
        linarith
      have h_base_le : 1 + Real.sqrt 2 / 2 ≤ 2 := by linarith [h_sqrt2_le2]
      have h1 : (1 + Real.sqrt 2 / 2)^t ≤ (1 + Real.sqrt 2 / 2)^2 := by
        have h2 : (1 + Real.sqrt 2 / 2)^t ≤ (1 + Real.sqrt 2 / 2)^(2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.sqrt_nonneg 2]) (by linarith)
        have h3 : (1 + Real.sqrt 2 / 2)^(2:ℝ) = (1 + Real.sqrt 2 / 2)^2 := by
          simp [Real.rpow_two]
        rw [h3] at h2; exact h2
      have h4 : (1 + Real.sqrt 2 / 2)^2 ≤ 4 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    have h13eps2 : 13 * ε / 2 = (ε / 4) * 26 := by ring
    have hΔ13eps2_pos : Real.rpow Δ (13 * ε / 2) = (Real.rpow Δ (ε / 4)) ^ 26 := by
      rw [h13eps2]
      simpa using Real.rpow_mul_natCast hΔ_pos.le (ε / 4) 26
    have hΔ13eps2 : Real.rpow Δ (-13 * ε / 2) = (Real.rpow Δ (13 * ε / 2))⁻¹ := by
      rw [show -13 * ε / 2 = -(13 * ε / 2) by ring]; exact Real.rpow_neg hΔ_pos.le (13 * ε / 2)
    rw [hΔ13eps2, hΔ13eps2_pos]
    have h_eps4_pos : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h5 : (Real.rpow Δ (ε / 4)) ^ 26 ≤ (1 / 100 : ℝ) ^ 26 := by
      have h51 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
      have h52 : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
      exact pow_le_pow_left₀ h52 h_small 26
    have h6 : 0 < (Real.rpow Δ (ε / 4)) ^ 26 := pow_pos h_eps4_pos 26
    have h7 : ((Real.rpow Δ (ε / 4)) ^ 26)⁻¹ ≥ ((1 / 100 : ℝ) ^ 26)⁻¹ := by
      have h71 : (Real.rpow Δ (ε / 4)) ^ 26 ≤ (1 / 100 : ℝ) ^ 26 := h5
      have h72 : 0 < (Real.rpow Δ (ε / 4)) ^ 26 := h6
      gcongr
    have h8 : ((1 / 100 : ℝ) ^ 26)⁻¹ ≥ 4 := by norm_num
    linarith

  have h_geom_absorb_weak :
      (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t * Real.rpow Δ (t - 17 * ε / 2) ≤ Real.rpow Δ (-15 * ε) := by
    have h_mul : (1 + Real.sqrt 2 / 2) * (2 * Real.sqrt 2) = 2 * (1 + Real.sqrt 2) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h_nonneg1 : 0 ≤ 1 + Real.sqrt 2 / 2 := by positivity
    have h_nonneg2 : 0 ≤ 2 * Real.sqrt 2 := by positivity
    have h_product : (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t = (2 * (1 + Real.sqrt 2))^t := by
      have h : (1 + Real.sqrt 2 / 2)^t * (2 * Real.sqrt 2)^t = ((1 + Real.sqrt 2 / 2) * (2 * Real.sqrt 2))^t := by
        rw [←Real.mul_rpow h_nonneg1 h_nonneg2]
      rw [h, h_mul]
    have h_const : (2 * (1 + Real.sqrt 2))^t ≤ 1000 := by
      have h_base1 : 1 ≤ 2 * (1 + Real.sqrt 2) := by linarith [Real.sqrt_nonneg 2]
      have h_pow : (2 * (1 + Real.sqrt 2))^t ≤ (2 * (1 + Real.sqrt 2))^2 := by
        have h1 : (2 * (1 + Real.sqrt 2))^t ≤ (2 * (1 + Real.sqrt 2))^(2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.sqrt_nonneg 2]) (by linarith)
        have h2 : (2 * (1 + Real.sqrt 2))^(2:ℝ) = (2 * (1 + Real.sqrt 2))^2 := by
          simp [Real.rpow_two]
        rw [h2] at h1; exact h1
      have h_sq : (2 * (1 + Real.sqrt 2))^2 ≤ 1000 := by
        have h_sqrt2_le : Real.sqrt 2 ≤ 2 := by
          have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
          have h2 : Real.sqrt 4 = 2 := by norm_num
          linarith
        nlinarith [Real.sqrt_nonneg 2]
      linarith
    -- 1000 ≤ Δ^{-13ε/2} since Δ^{ε/4} ≤ 1/100
    have h13eps2 : 13 * ε / 2 = (ε / 4) * 26 := by ring
    have hΔ13eps2_pos : Real.rpow Δ (13 * ε / 2) = (Real.rpow Δ (ε / 4)) ^ 26 := by
      rw [h13eps2]
      simpa using Real.rpow_mul_natCast hΔ_pos.le (ε / 4) 26
    have hΔ13eps2 : Real.rpow Δ (-13 * ε / 2) = (Real.rpow Δ (13 * ε / 2))⁻¹ := by
      rw [show -13 * ε / 2 = -(13 * ε / 2) by ring]; exact Real.rpow_neg hΔ_pos.le (13 * ε / 2)
    have h_1000_le : (1000 : ℝ) ≤ Real.rpow Δ (-13 * ε / 2) := by
      rw [hΔ13eps2, hΔ13eps2_pos]
      have h3 : (Real.rpow Δ (ε / 4)) ^ 26 ≤ (1 / 100 : ℝ) ^ 26 := by
        have h31 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
        have h32 : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
        exact pow_le_pow_left₀ h32 h_small 26
      have h4 : 0 < (Real.rpow Δ (ε / 4)) ^ 26 := pow_pos (Real.rpow_pos_of_pos hΔ_pos _) 26
      have h5 : ((Real.rpow Δ (ε / 4)) ^ 26)⁻¹ ≥ ((1 / 100 : ℝ) ^ 26)⁻¹ := by gcongr
      have h6 : ((1 / 100 : ℝ) ^ 26)⁻¹ ≥ 1000 := by norm_num
      linarith
    have h_product_le : (2 * (1 + Real.sqrt 2))^t ≤ Real.rpow Δ (-13 * ε / 2) := by
      calc (2 * (1 + Real.sqrt 2))^t ≤ 1000 := h_const
        _ ≤ Real.rpow Δ (-13 * ε / 2) := h_1000_le
    have h_t_le : Real.rpow Δ (t - 17 * ε / 2) ≤ Real.rpow Δ (-17 * ε / 2) := by
      apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos <;> linarith
    have h_final : (2 * (1 + Real.sqrt 2))^t * Real.rpow Δ (t - 17 * ε / 2) ≤
        Real.rpow Δ (-13 * ε / 2) * Real.rpow Δ (-17 * ε / 2) := by
      have h_nonneg1 : 0 ≤ (2 * (1 + Real.sqrt 2))^t := by positivity
      have h_nonneg2 : 0 ≤ Real.rpow Δ (t - 17 * ε / 2) := Real.rpow_nonneg hΔ_pos.le _
      gcongr
    have h_add : (-13 * ε / 2) + (-17 * ε / 2) = -15 * ε := by ring
    have h_rpow : Real.rpow Δ (-13 * ε / 2) * Real.rpow Δ (-17 * ε / 2) = Real.rpow Δ (-15 * ε) := by
      have h := hrpow_add (-13 * ε / 2) (-17 * ε / 2)
      rw [h_add] at h; exact h
    rw [h_product] at *
    have h_final' : (2 * (1 + Real.sqrt 2))^t * Real.rpow Δ (t - 17 * ε / 2) ≤ Real.rpow Δ (-15 * ε) := by
      rw [←h_rpow]
      exact h_final
    exact h_final'

  -- Step 4: S-set conversion (Stub4 expects -17ε/2 input, gives -15ε output)
  have hQset_sset : IsDeltaSSet Δ t (Real.rpow Δ (-15 * ε))
      (Qset : Set (CoarseSquare Δ)) :=
    a1_ball_growth_to_sset_weak hΔ_pos hΔ_lt_half ht hε_pos Qset hQset_nonempty
      hQset_center_growth h_geom_absorb_weak h_small_absorb_weak

  -- Physical ball-growth with τ-free constant Δ^{-9ε}
  -- Absorb (1+√2/2)^t into Δ^{-13ε/2} to get Δ^{-5ε/2} * Δ^{-13ε/2} = Δ^{-9ε}.
  -- The stronger constant (vs Δ^{-10ε}) leaves room for the energy bound factor K_total ≥ 1.
  have h_small_absorb_strong : (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-5 * ε / 2) := by
    have h_const : (1 + Real.sqrt 2 / 2)^t ≤ 4 := by
      have h_sqrt2_le2 : Real.sqrt 2 ≤ 2 := by
        have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h2 : Real.sqrt 4 = 2 := by norm_num
        linarith
      have h_base_le : 1 + Real.sqrt 2 / 2 ≤ 2 := by linarith [h_sqrt2_le2]
      have h1 : (1 + Real.sqrt 2 / 2)^t ≤ (1 + Real.sqrt 2 / 2)^(2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [Real.sqrt_nonneg 2]) (by linarith)
      have h3 : (1 + Real.sqrt 2 / 2)^(2:ℝ) = (1 + Real.sqrt 2 / 2)^2 := by
        simp [Real.rpow_two]
      rw [h3] at h1
      have h4 : (1 + Real.sqrt 2 / 2)^2 ≤ 4 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith
    have h5eps2 : 5 * ε / 2 = (ε / 4) * 10 := by ring
    have hΔ5eps2_pos : Real.rpow Δ (5 * ε / 2) = (Real.rpow Δ (ε / 4)) ^ 10 := by
      rw [h5eps2]
      simpa using Real.rpow_mul_natCast hΔ_pos.le (ε / 4) 10
    have hΔ5eps2 : Real.rpow Δ (-5 * ε / 2) = (Real.rpow Δ (5 * ε / 2))⁻¹ := by
      rw [show -5 * ε / 2 = -(5 * ε / 2) by ring]; exact Real.rpow_neg hΔ_pos.le (5 * ε / 2)
    rw [hΔ5eps2, hΔ5eps2_pos]
    have h_eps4_pos : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h5 : (Real.rpow Δ (ε / 4)) ^ 10 ≤ (1 / 100 : ℝ) ^ 10 := by
      have h51 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
      have h52 : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
      exact pow_le_pow_left₀ h52 h_small 10
    have h6 : 0 < (Real.rpow Δ (ε / 4)) ^ 10 := pow_pos h_eps4_pos 10
    have h7 : ((Real.rpow Δ (ε / 4)) ^ 10)⁻¹ ≥ ((1 / 100 : ℝ) ^ 10)⁻¹ := by
      have h71 : (Real.rpow Δ (ε / 4)) ^ 10 ≤ (1 / 100 : ℝ) ^ 10 := h5
      have h72 : 0 < (Real.rpow Δ (ε / 4)) ^ 10 := h6
      gcongr
    have h8 : ((1 / 100 : ℝ) ^ 10)⁻¹ ≥ 4 := by norm_num
    linarith

  have hQset_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-11 * ε) * r^t * (Qset.card : ℝ) := by
    intro c r hr
    have h := hQset_center_growth c r hr
    have h_const : Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t ≤
        Real.rpow Δ (-11 * ε) := by
      have h1 : (1 + Real.sqrt 2 / 2)^t ≤ Real.rpow Δ (-5 * ε / 2) := h_small_absorb_strong
      have h_pos : 0 < Real.rpow Δ (-17 * ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
      have h2 : Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t ≤
          Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-5 * ε / 2) := by gcongr
      have h_add : (-17 * ε / 2) + (-5 * ε / 2) = -11 * ε := by ring
      have h3 : Real.rpow Δ (-17 * ε / 2) * Real.rpow Δ (-5 * ε / 2) =
          Real.rpow Δ ((-17 * ε / 2) + (-5 * ε / 2)) := (Real.rpow_add hΔ_pos _ _).symm
      rw [h3, h_add] at h2
      exact h2
    have h_r_nonneg : 0 ≤ r := by linarith
    have h_rt_nonneg : 0 ≤ r^t := by positivity
    have hQcard_nonneg : 0 ≤ (Qset.card : ℝ) := by positivity
    calc ((Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ)
      ≤ Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t * r^t * (Qset.card : ℝ) := h
    _ = (Real.rpow Δ (-17 * ε / 2) * (1 + Real.sqrt 2 / 2)^t) * r^t * (Qset.card : ℝ) := by ring
    _ ≤ Real.rpow Δ (-11 * ε) * r^t * (Qset.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_const h_rt_nonneg) hQcard_nonneg

  -- Step 5: Select δ-separated points per square
  have h_local_one : ∀ x ∈ Pfin, (Pfin.filter (fun y => dist x y < δ)).card ≤ 1 := by
    intro x hx
    have h1 : ∀ y ∈ Pfin.filter (fun y => dist x y < δ), y = x := by
      intro y hy
      have h_y_in_P : y ∈ Pfin := (Finset.mem_filter.mp hy).1
      have h_xy : dist x y < δ := (Finset.mem_filter.mp hy).2
      by_cases h : y ≠ x
      · have h_sep : δ ≤ dist y x := hP_sep h_y_in_P hx h
        have h_comm : dist y x = dist x y := dist_comm y x
        rw [h_comm] at h_sep
        linarith
      · simpa using h
    rw [Finset.card_le_one]
    intro y hy z hz
    exact (h1 y hy).trans (h1 z hz).symm

  choose points_raw hpoints_sub hpoints_sep hpoints_card_lower using
    fun (Q : CoarseSquare Δ) (hQ : Q ∈ Qset) =>
      let P_Q := Pfin.filter (fun p => p ∈ squareSet Δ Q)
      have h_local_Q : ∀ x ∈ P_Q, (P_Q.filter (fun y => dist x y < δ)).card ≤ 1 := by
        intro x hx
        have h_x_in_P : x ∈ Pfin := (Finset.mem_filter.mp hx).1
        have h1 : P_Q.filter (fun y => dist x y < δ) ⊆ Pfin.filter (fun y => dist x y < δ) := by
          intro y hy
          have h_y_in_PQ : y ∈ P_Q := (Finset.mem_filter.mp hy).1
          have h_y_in_P : y ∈ Pfin := (Finset.mem_filter.mp h_y_in_PQ).1
          exact Finset.mem_filter.mpr ⟨h_y_in_P, (Finset.mem_filter.mp hy).2⟩
        exact Finset.card_le_card h1 |>.trans (h_local_one x h_x_in_P)
      extract_separated_subset_fin δ hδ_pos P_Q 1 (by norm_num) h_local_Q

  let points : (Q : CoarseSquare Δ) → Q ∈ Qset → Finset Plane := points_raw

  have h_points_in_square : ∀ Q hQ p, p ∈ points Q hQ → p ∈ squareSet Δ Q := by
    intro Q hQ p hp
    have h4 : p ∈ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ hp
    exact (Finset.mem_filter.mp h4).2

  have h_points_in_ball : ∀ Q hQ, (points Q hQ : Set Plane) ⊆ Metric.closedBall 0 (Real.sqrt 2) := by
    intro Q hQ
    have h1 : (points Q hQ : Set Plane) ⊆ (Pfin : Set Plane) := by
      intro p hp
      have h2 : p ∈ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ hp
      exact (Finset.mem_filter.mp h2).1
    exact Set.Subset.trans h1 hP_in_ball

  have h_points_y_bound : ∀ Q hQ p, p ∈ points Q hQ → |p 1| ≤ Real.sqrt 2 := by
    intro Q hQ p hp
    have h1 : p ∈ Pfin := by
      have h2 : p ∈ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ hp
      exact (Finset.mem_filter.mp h2).1
    exact hP_y_bound p h1

  have h_points_card_lower' : ∀ Q hQ,
      Real.rpow Δ (-t + 3 * ε) ≤ (points Q hQ).card := by
    intro Q hQ
    have h5 : ((points Q hQ).card : ℝ) ≥
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
      have h51 := hpoints_card_lower Q hQ
      simpa using h51
    have h6 : Real.rpow Δ (-t + 3 * ε) ≤
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) :=
      (hQ_heavy Q hQ).1
    exact le_trans h6 h5

  have h_points_card_lower_strong' : ∀ Q hQ,
      Real.rpow Δ (-t + 3 * ε) ≤ (points Q hQ).card := by
    intro Q hQ
    have h5 : ((points Q hQ).card : ℝ) ≥
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
      have h51 := hpoints_card_lower Q hQ
      simpa using h51
    have h6 : Real.rpow Δ (-t + 3 * ε) ≤
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) :=
      (hQ_heavy Q hQ).1
    exact le_trans h6 h5

  have h_points_card_upper' : ∀ Q hQ,
      (points Q hQ).card ≤ Real.rpow Δ (-t - 3 * ε) := by
    intro Q hQ
    have h5 : (points Q hQ) ⊆ Pfin.filter (fun p => p ∈ squareSet Δ Q) :=
      hpoints_sub Q hQ
    have h6 : (points Q hQ).card ≤ (Pfin.filter (fun p => p ∈ squareSet Δ Q)).card :=
      Finset.card_le_card h5
    have h7 : ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ≤
        Real.rpow Δ (-t - 3 * ε) := (hQ_heavy Q hQ).2
    exact le_trans (by exact_mod_cast h6) h7

  -- Step 6: Assemble output using input tube families directly
  let K_pack : ℝ := (MainAppendix.affineLine_packing_constant : ℝ) + 1
  let M : ℝ := (M_in : ℝ)

  have hK_pack_pos : 0 < K_pack := by
    dsimp only [K_pack]; linarith

  have hM_pos : 0 < M := by
    dsimp only [M]
    exact Nat.cast_pos.mpr hM_in_pos

  have hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack := by
    dsimp only [M]
    have h1 : ∀ p ∈ Pfin, (M_in : ℝ) ≥ (Tp p).card := by
      intro p hp
      exact_mod_cast (h_tube_uniform p hp).2
    rcases hQset_nonempty with ⟨Q, hQ⟩
    have h9 : 0 < (points Q hQ).card := by
      have h10 : Real.rpow Δ (-t + 3 * ε) ≤ (points Q hQ).card := h_points_card_lower' Q hQ
      have h11 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact_mod_cast lt_of_lt_of_le h11 h10
    rcases Finset.card_pos.mp h9 with ⟨p, hp⟩
    have h_p_in_Pfin : p ∈ Pfin := by
      have h4 : p ∈ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ hp
      exact (Finset.mem_filter.mp h4).1
    have h2 : (Tp p).card ≥ Real.rpow Δ (-2 * s + 2 * ε) := h_tube_card_lower p h_p_in_Pfin
    have h3 : (M_in : ℝ) ≥ (Tp p).card := h1 p h_p_in_Pfin
    have h4 : (M_in : ℝ) ≥ Real.rpow Δ (-2 * s + 2 * ε) := by linarith
    have h5 : K_pack ≥ 1 := by
      dsimp only [K_pack]; linarith
    have h6 : Real.rpow Δ (-2 * s + 2 * ε) / K_pack ≤ Real.rpow Δ (-2 * s + 2 * ε) := by
      have h7 : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact (div_le_self h7.le h5)
    linarith

  have hM_upper : M ≤ 2 * Real.rpow Δ (-2 * s - ε) := by
    dsimp only [M]
    rcases hQset_nonempty with ⟨Q, hQ⟩
    have h9 : 0 < (points Q hQ).card := by
      have h10 : Real.rpow Δ (-t + 3 * ε) ≤ (points Q hQ).card := h_points_card_lower' Q hQ
      have h11 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact_mod_cast lt_of_lt_of_le h11 h10
    rcases Finset.card_pos.mp h9 with ⟨p, hp⟩
    have h_p_in_Pfin : p ∈ Pfin := by
      have h4 : p ∈ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ hp
      exact (Finset.mem_filter.mp h4).1
    have h1 : M_in / 2 ≤ (Tp p).card := (h_tube_uniform p h_p_in_Pfin).1
    have h2 : (Tp p).card ≤ Real.rpow Δ (-2 * s - ε) := h_tube_card_upper p h_p_in_Pfin
    have h3 : M_in ≤ 2 * (Tp p).card := by
      have h4 : M_in = 2 * (M_in / 2) := by
        have h5 : M_in % 2 = 0 := hM_in_even
        omega
      rw [h4]
      <;> omega
    have h4 : (M_in : ℝ) ≤ 2 * ((Tp p).card : ℝ) := by exact_mod_cast h3
    have h5 : (M_in : ℝ) ≤ 2 * Real.rpow Δ (-2 * s - ε) := by
      calc (M_in : ℝ) ≤ 2 * ((Tp p).card : ℝ) := h4
           _ ≤ 2 * Real.rpow Δ (-2 * s - ε) := by gcongr
    exact h5

  have h_p_in_Pfin : ∀ Q hQ p, p ∈ points Q hQ → p ∈ Pfin := by
    intro Q hQ p hp
    have h5 : p ∈ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ hp
    exact (Finset.mem_filter.mp h5).1

  have h_tubes_card : ∀ Q hQ p, p ∈ points Q hQ →
      (M / 2 : ℝ) ≤ (Tp p).card ∧ (Tp p).card ≤ M := by
    intro Q hQ p hp
    have h_p_in : p ∈ Pfin := h_p_in_Pfin Q hQ p hp
    have h := h_tube_uniform p h_p_in
    have h1 : (M / 2 : ℝ) ≤ (Tp p).card := by
      dsimp only [M]
      have h_nat : M_in / 2 ≤ (Tp p).card := h.1
      have h_div2 : (M_in : ℝ) / 2 = ↑(M_in / 2) := by
        have h4 : M_in = 2 * (M_in / 2) := by
          have h5 : M_in % 2 = 0 := hM_in_even
          omega
        have h5 : (M_in : ℝ) = 2 * ↑(M_in / 2) := by exact_mod_cast h4
        rw [h5] <;> ring
      rw [h_div2]
      exact_mod_cast h_nat
    have h2 : ((Tp p).card : ℝ) ≤ M := by
      dsimp only [M]
      exact_mod_cast h.2
    exact ⟨h1, h2⟩

  have h_tubes_sset' : ∀ Q hQ p, p ∈ points Q hQ →
      IsDeltaSSet δ s (max 1 (K_pack * Real.rpow δ (-ε))) (Tp p : Set FineTube) := by
    intro Q hQ p hp
    have h_p_in : p ∈ Pfin := h_p_in_Pfin Q hQ p hp
    let C_new := max 1 (K_pack * Real.rpow δ (-ε))
    have hC_old_le_new : Real.rpow δ (-ε) ≤ C_new := by
      dsimp only [C_new, K_pack]
      have h1 : 0 < Real.rpow δ (-ε) := Real.rpow_pos_of_pos hδ_pos _
      have h2 : 1 ≤ (MainAppendix.affineLine_packing_constant : ℝ) + 1 := by linarith
      have h3 : Real.rpow δ (-ε) ≤ ((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow δ (-ε) := by
        have h31 : Real.rpow δ (-ε) ≤ Real.rpow δ (-ε) * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) :=
          le_mul_of_one_le_right h1.le h2
        have h32 : Real.rpow δ (-ε) * ((MainAppendix.affineLine_packing_constant : ℝ) + 1) =
            ((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow δ (-ε) := by ring
        rw [h32] at h31
        exact h31
      have h4 : ((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow δ (-ε) ≤ max 1 (((MainAppendix.affineLine_packing_constant : ℝ) + 1) * Real.rpow δ (-ε)) := by
        exact le_max_right _ _
      exact le_trans h3 h4
    rcases hTp_sset p h_p_in with ⟨hne, hδ, hC, hs, hg⟩
    refine ⟨hne, hδ, by positivity, hs, fun x r hr => ?_⟩
    have h13 := hg x r hr
    have h14 : ENNReal.ofReal (Real.rpow δ (-ε)) ≤ ENNReal.ofReal C_new := ENNReal.ofReal_le_ofReal hC_old_le_new
    calc (Metric.externalCoveringNumber δ.toNNReal ((Tp p : Set FineTube) ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal (Real.rpow δ (-ε)) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal (Tp p : Set FineTube) : ENNReal) := h13
    _ ≤ ENNReal.ofReal C_new * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal (Tp p : Set FineTube) : ENNReal) := by
      gcongr

  have h_tubes_sep' : ∀ Q hQ p, p ∈ points Q hQ →
      SSetBridges.SeparatedAt (δ / 2) (Tp p : Set FineTube) := by
    intro Q hQ p hp
    have h_p_in : p ∈ Pfin := h_p_in_Pfin Q hQ p hp
    exact hTp_sep p h_p_in

  have h_inc' : ∀ Q hQ p, p ∈ points Q hQ → ∀ T ∈ Tp p,
      p ∈ Metric.cthickening (2 * δ) T.1 := by
    intro Q hQ p hp T hT
    have h_p_in : p ∈ Pfin := h_p_in_Pfin Q hQ p hp
    exact h_inc p h_p_in T hT

  have h_slope_bound' : ∀ Q hQ p, p ∈ points Q hQ → ∀ T ∈ Tp p,
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3 := by
    intro Q hQ p hp T hT
    have h_p_in : p ∈ Pfin := h_p_in_Pfin Q hQ p hp
    exact h_slope_bound p h_p_in T hT

  exact {
    Qset := Qset,
    points := points,
    tubes := Tp,
    M := M,
    K_pack := K_pack,
    hK_pack_pos := hK_pack_pos,
    hQset_sset := hQset_sset,
    hQset_phys_growth := hQset_phys_growth,
    hQset_card_lower := hQ_card_lower,
    hQset_card_upper := hQ_card_upper,
    h_points_in_square := h_points_in_square,
    h_points_in_ball := h_points_in_ball,
    h_points_y_bound := h_points_y_bound,
    h_points_card_lower := h_points_card_lower',
    h_points_card_lower_strong := h_points_card_lower_strong',
    h_points_card_upper := h_points_card_upper',
    hM_pos := hM_pos,
    hM_lower := hM_lower,
    hM_upper := hM_upper,
    h_tubes_card := h_tubes_card,
    h_slope_bound := h_slope_bound',
    h_tubes_sset := h_tubes_sset',
    h_separated := hpoints_sep,
    P_all := Pfin,
    hP_all_card_upper := hP_card_upper,
    hP_all_sset := hP_sset,
    h_points_sub_all := by
      intro Q hQ
      have h_sub : points Q hQ ⊆ Pfin.filter (fun p => p ∈ squareSet Δ Q) := hpoints_sub Q hQ
      have h_filter_sub : (Pfin.filter (fun p => p ∈ squareSet Δ Q) : Set Plane) ⊆ (Pfin : Set Plane) := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      exact Set.Subset.trans (show (points Q hQ : Set Plane) ⊆ _ from h_sub) h_filter_sub,
    h_tubes_separated := h_tubes_sep',
    h_inc := h_inc'
  }

/-- Projection: points selected by `a1_stage` are subset of input `Pfin`. -/
lemma a1_stage_points_subset_Pfin
    {Δ δ t s ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hδ_pos : 0 < δ) (hδ_le_D : δ ≤ Δ)
    (ht : 0 < t) (ht_lt_two : t < 2) (hs : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε) (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (Pfin : Finset Plane)
    (hP_in_ball hP_y_bound hP_sep hP_card_lower hP_card_upper hP_ball_growth hN_cover)
    (Tp : Plane → Finset FineTube)
    (hTp_sset hTp_sep h_tube_card_lower h_tube_card_upper)
    (M_in : ℕ) (hM_in_pos hM_in_even h_tube_uniform h_slope_bound h_inc hP_sset) :
    ∀ (Q : CoarseSquare Δ)
      (hQ : Q ∈ (a1_stage hΔ_pos hΔ_lt_half hδ_pos hδ_le_D ht ht_lt_two hs hs_lt_one hε_pos h_small
        Pfin hP_in_ball hP_y_bound hP_sep hP_card_lower hP_card_upper hP_ball_growth hN_cover
        Tp hTp_sset hTp_sep h_tube_card_lower h_tube_card_upper
        M_in hM_in_pos hM_in_even h_tube_uniform h_slope_bound h_inc hP_sset).Qset),
      ((a1_stage hΔ_pos hΔ_lt_half hδ_pos hδ_le_D ht ht_lt_two hs hs_lt_one hε_pos h_small
        Pfin hP_in_ball hP_y_bound hP_sep hP_card_lower hP_card_upper hP_ball_growth hN_cover
        Tp hTp_sset hTp_sep h_tube_card_lower h_tube_card_upper
        M_in hM_in_pos hM_in_even h_tube_uniform h_slope_bound h_inc hP_sset).points Q hQ : Set Plane)
      ⊆ (Pfin : Set Plane) := by
  let a1 := a1_stage hΔ_pos hΔ_lt_half hδ_pos hδ_le_D ht ht_lt_two hs hs_lt_one hε_pos h_small
    Pfin hP_in_ball hP_y_bound hP_sep hP_card_lower hP_card_upper hP_ball_growth hN_cover
    Tp hTp_sset hTp_sep h_tube_card_lower h_tube_card_upper
    M_in hM_in_pos hM_in_even h_tube_uniform h_slope_bound h_inc hP_sset
  have h_sub : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ (a1.P_all : Set Plane) := a1.h_points_sub_all
  have h_eq : a1.P_all = Pfin := by rfl
  intro Q hQ
  have h := h_sub Q hQ
  rw [h_eq] at h
  exact h

end DirecretisedFurstenbergEstimate.AppendixA.A1_Assembly
