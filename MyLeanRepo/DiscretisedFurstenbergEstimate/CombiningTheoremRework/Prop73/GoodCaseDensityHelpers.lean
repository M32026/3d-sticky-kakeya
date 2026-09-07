module

/-
  GoodCaseDensityHelpers — Covering number bounds for the good-case
  point-set density transfer.

  Three lemmas establish the density ratio 1/(9K) needed to transfer
  IsRegularBetweenScales from the full point set to the selected subset:

  1. coarse_squares_intersecting_ball_at_most_9: grid packing
  2. cover_config_pointSet_upper: upper bound for full point set
  3. cover_P_selected_lower: lower bound for selected point set

  Whiteprint node: combining_theorem_rework / good_case_density_helpers
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open InductionConfigurations

/-! ========================================================================
   Grid packing: a δ-ball intersects at most 9 δ-dyadic squares
   ======================================================================== -/

/-- At most 9 dyadic squares of side δ can intersect a closed ball of radius δ. -/
lemma coarse_squares_intersecting_ball_at_most_9
    {m : ℕ} (c : EuclideanPlane) (Qs : Finset (DyadicSquare m)) :
    (Qs.filter (fun Q => (Q.toSet ∩ Metric.closedBall c (dyadicDelta m)).Nonempty)).card ≤ 9 := by
  let δ := dyadicDelta m
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  let k0 : ℤ := Int.floor (c 0 / δ)
  let l0 : ℤ := Int.floor (c 1 / δ)
  have h1 : (k0 : ℝ) ≤ c 0 / δ := Int.floor_le (c 0 / δ)
  have h2 : c 0 / δ < (k0 : ℝ) + 1 := Int.lt_floor_add_one (c 0 / δ)
  have h3 : (l0 : ℝ) ≤ c 1 / δ := Int.floor_le (c 1 / δ)
  have h4 : c 1 / δ < (l0 : ℝ) + 1 := Int.lt_floor_add_one (c 1 / δ)
  let grid : Finset (DyadicSquare m) :=
    (Finset.Icc (k0 - 1) (k0 + 1)).biUnion fun i =>
      (Finset.Icc (l0 - 1) (l0 + 1)).image (fun j => (⟨i, j⟩ : DyadicSquare m))
  have h_grid_card : grid.card ≤ 9 := by
    have h : grid.card ≤ 3 * 3 := by
      calc grid.card
        ≤ ∑ i ∈ Finset.Icc (k0 - 1) (k0 + 1),
            ((Finset.Icc (l0 - 1) (l0 + 1)).image (fun j : ℤ => (⟨i, j⟩ : DyadicSquare m))).card
          := Finset.card_biUnion_le
      _ = ∑ i ∈ Finset.Icc (k0 - 1) (k0 + 1), 3 := by
          apply Finset.sum_congr rfl; intro i _
          have h_inj : Function.Injective (fun j : ℤ => (⟨i, j⟩ : DyadicSquare m)) := by
            intro j1 j2 h; simpa using h
          rw [Finset.card_image_of_injective _ h_inj]
          simp [Finset.Icc_self] <;> omega
      _ = 3 * 3 := by
          have h5 : (Finset.Icc (k0 - 1) (k0 + 1)).card = 3 := by simp <;> omega
          rw [Finset.sum_const, h5] <;> ring
      _ = 9 := by norm_num
    exact h
  have h_sub : Qs.filter (fun Q => (Q.toSet ∩ Metric.closedBall c δ).Nonempty) ⊆ grid := by
    intro Q hQ
    have h5 : (Q.toSet ∩ Metric.closedBall c δ).Nonempty := (Finset.mem_filter.mp hQ).2
    rcases h5 with ⟨x, hxQ, hxball⟩
    have hdist : dist x c ≤ δ := by exact Metric.mem_closedBall.mp hxball
    have h6 : |x 0 - c 0| ≤ δ := by
      have h : |x 0 - c 0| ≤ dist x c := euclidean_dist_ge_component (k := 0)
      exact le_trans h hdist
    have h7 : |x 1 - c 1| ≤ δ := by
      have h : |x 1 - c 1| ≤ dist x c := euclidean_dist_ge_component (k := 1)
      exact le_trans h hdist
    have hxi1 : (Q.i : ℝ) * δ ≤ x 0 := hxQ.1
    have hxi2 : x 0 < ((Q.i : ℝ) + 1) * δ := hxQ.2.1
    have hxj1 : (Q.j : ℝ) * δ ≤ x 1 := hxQ.2.2.1
    have hxj2 : x 1 < ((Q.j : ℝ) + 1) * δ := hxQ.2.2.2
    have h_abs6 : -δ ≤ x 0 - c 0 ∧ x 0 - c 0 ≤ δ := abs_le.mp h6
    have h_abs7 : -δ ≤ x 1 - c 1 ∧ x 1 - c 1 ≤ δ := abs_le.mp h7
    have h61 : c 0 - δ ≤ x 0 := by linarith
    have h62 : x 0 ≤ c 0 + δ := by linarith
    have h71 : c 1 - δ ≤ x 1 := by linarith
    have h72 : x 1 ≤ c 1 + δ := by linarith
    have h_i1 : (Q.i : ℝ) ≤ c 0 / δ + 1 := by
      have h : (Q.i : ℝ) * δ ≤ c 0 + δ := by linarith
      have hdiv : ((Q.i : ℝ) * δ) / δ ≤ (c 0 + δ) / δ := by gcongr
      have hq : ((Q.i : ℝ) * δ) / δ = (Q.i : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      have hr : (c 0 + δ) / δ = c 0 / δ + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [hq, hr] at hdiv; exact hdiv
    have h_i2 : c 0 / δ - 2 < (Q.i : ℝ) := by
      have h : c 0 - δ < ((Q.i : ℝ) + 1) * δ := by linarith
      have hdiv : (c 0 - δ) / δ < (((Q.i : ℝ) + 1) * δ) / δ := by gcongr
      have hl : (c 0 - δ) / δ = c 0 / δ - 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      have hr : (((Q.i : ℝ) + 1) * δ) / δ = (Q.i : ℝ) + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [hl, hr] at hdiv; linarith
    have h_i_lt : (Q.i : ℝ) < (k0 : ℝ) + 2 := by linarith
    have h_i_le : Q.i ≤ k0 + 1 := by
      by_contra h
      have h' : k0 + 1 < Q.i := by simpa using h
      have h'' : k0 + 2 ≤ Q.i := by omega
      have : (Q.i : ℝ) ≥ (k0 : ℝ) + 2 := by exact_mod_cast h''
      linarith
    have h_i_gt : (k0 : ℝ) - 2 < (Q.i : ℝ) := by linarith [h1]
    have h_i_ge : k0 - 1 ≤ Q.i := by
      by_contra h
      have h'' : Q.i ≤ k0 - 2 := by omega
      have : (Q.i : ℝ) ≤ (k0 : ℝ) - 2 := by exact_mod_cast h''
      linarith
    have h_j1 : (Q.j : ℝ) ≤ c 1 / δ + 1 := by
      have h : (Q.j : ℝ) * δ ≤ c 1 + δ := by linarith
      have hdiv : ((Q.j : ℝ) * δ) / δ ≤ (c 1 + δ) / δ := by gcongr
      have hq : ((Q.j : ℝ) * δ) / δ = (Q.j : ℝ) := by
        field_simp [hδ_pos.ne'] <;> ring
      have hr : (c 1 + δ) / δ = c 1 / δ + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [hq, hr] at hdiv; exact hdiv
    have h_j2 : c 1 / δ - 2 < (Q.j : ℝ) := by
      have h : c 1 - δ < ((Q.j : ℝ) + 1) * δ := by linarith
      have hdiv : (c 1 - δ) / δ < (((Q.j : ℝ) + 1) * δ) / δ := by gcongr
      have hl : (c 1 - δ) / δ = c 1 / δ - 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      have hr : (((Q.j : ℝ) + 1) * δ) / δ = (Q.j : ℝ) + 1 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [hl, hr] at hdiv; linarith
    have h_j_lt : (Q.j : ℝ) < (l0 : ℝ) + 2 := by linarith
    have h_j_le : Q.j ≤ l0 + 1 := by
      by_contra h
      have h' : l0 + 1 < Q.j := by simpa using h
      have h'' : l0 + 2 ≤ Q.j := by omega
      have : (Q.j : ℝ) ≥ (l0 : ℝ) + 2 := by exact_mod_cast h''
      linarith
    have h_j_gt : (l0 : ℝ) - 2 < (Q.j : ℝ) := by linarith [h3]
    have h_j_ge : l0 - 1 ≤ Q.j := by
      by_contra h
      have h'' : Q.j ≤ l0 - 2 := by omega
      have : (Q.j : ℝ) ≤ (l0 : ℝ) - 2 := by exact_mod_cast h''
      linarith
    have h_i_in : Q.i ∈ Finset.Icc (k0 - 1) (k0 + 1) := by
      simp only [Finset.mem_Icc]; exact ⟨h_i_ge, h_i_le⟩
    have h_j_in : Q.j ∈ Finset.Icc (l0 - 1) (l0 + 1) := by
      simp only [Finset.mem_Icc]; exact ⟨h_j_ge, h_j_le⟩
    exact Finset.mem_biUnion.mpr ⟨Q.i, h_i_in, Finset.mem_image.mpr ⟨Q.j, h_j_in, by cases Q <;> simp <;> rfl⟩⟩
  exact le_trans (Finset.card_le_card h_sub) h_grid_card

/-! ========================================================================
   Covering upper bound: union of fine squares covered by coarse square centers
   ======================================================================== -/

/-- Covering number at coarse scale of config.pointSet is at most the number
    of coarse squares it occupies. -/
lemma cover_config_pointSet_upper
    {k m : ℕ} {s C_cfg : ℝ} {M : ℕ}
    (hnm : m ≤ k)
    (config : CTNiceConfiguration k s C_cfg M) :
    Metric.externalCoveringNumber (dyadicDelta m).toNNReal config.pointSet ≤
      ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ENNReal) := by
  let δ := dyadicDelta m
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  let S_full := config.P₀.image (InductionConfigurations.containingSquare hnm)
  let centers : Finset EuclideanPlane := S_full.image dyadicSquareCenter
  have hcover : Metric.IsCover δ.toNNReal config.pointSet (centers : Set EuclideanPlane) := by
    intro x hx
    have h1 : ∃ (p : DyadicSquare k), p ∈ config.P₀ ∧ x ∈ (p.toSet : Set EuclideanPlane) := by
      simpa [NiceConfiguration.pointSet, Set.mem_iUnion] using hx
    rcases h1 with ⟨p, hp, hxp⟩
    let Q : DyadicSquare m := InductionConfigurations.containingSquare hnm p
    have hQ_in : Q ∈ S_full := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_contain : InductionConfigurations.squareContained hnm p Q := by
      exact (InductionConfigurations.containingSquare_iff hnm p Q).mp rfl
    have h_p_sub_Q : (p.toSet : Set EuclideanPlane) ⊆ (Q.toSet : Set EuclideanPlane) :=
      DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h_contain
    have hxQ : x ∈ Q.toSet := h_p_sub_Q hxp
    have h_center_in : dyadicSquareCenter Q ∈ centers :=
      Finset.mem_image.mpr ⟨Q, hQ_in, rfl⟩
    have h_dist : dist x (dyadicSquareCenter Q) ≤ δ :=
      dyadicSquare_center_ball_cover Q hxQ
    have h_edist : edist x (dyadicSquareCenter Q) ≤ ↑δ.toNNReal := by
      rw [edist_dist]
      have h_eq : (↑δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
      rw [h_eq]
      exact ENNReal.ofReal_le_ofReal h_dist
    exact ⟨dyadicSquareCenter Q, h_center_in, h_edist⟩
  have h1 : Metric.externalCoveringNumber δ.toNNReal config.pointSet ≤ (centers : Set EuclideanPlane).encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hcover
  have h3 : centers.card ≤ S_full.card := Finset.card_image_le
  have h4 : (centers : Set EuclideanPlane).encard = ↑centers.card := by simp
  have h5 : (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal) ≤ (↑centers.card : ENNReal) := by
    exact_mod_cast h1.trans_eq h4
  have h6 : (↑centers.card : ENNReal) ≤ (↑S_full.card : ENNReal) := by exact_mod_cast h3
  exact le_trans h5 h6

/-! ========================================================================
   Covering lower bound: selected point set needs ≥ N/9 coarse-scale balls
   ======================================================================== -/

/-- Helper: distinct DyadicSquares have disjoint toSets. -/
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
    by_cases h : Q1.i < Q2.i
    · have h' : Q1.i + 1 ≤ Q2.i := by linarith
      have h1' : x 0 < ((Q1.i : ℝ) + 1) * dyadicDelta m := h1.2.1
      have h2' : (Q2.i : ℝ) * dyadicDelta m ≤ x 0 := h2.1
      have h3 : ((Q1.i : ℝ) + 1) * dyadicDelta m ≤ (Q2.i : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith
    · have h_lt : Q2.i < Q1.i := by
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
    by_cases h : Q1.j < Q2.j
    · have h' : Q1.j + 1 ≤ Q2.j := by linarith
      have h1' : x 1 < ((Q1.j : ℝ) + 1) * dyadicDelta m := h1.2.2.2
      have h2' : (Q2.j : ℝ) * dyadicDelta m ≤ x 1 := h2.2.2.1
      have h3 : ((Q1.j : ℝ) + 1) * dyadicDelta m ≤ (Q2.j : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith
    · have h_lt : Q2.j < Q1.j := by
        by_contra h2; exact h_j (by omega)
      have h' : Q2.j + 1 ≤ Q1.j := by linarith
      have h2' : x 1 < ((Q2.j : ℝ) + 1) * dyadicDelta m := h2.2.2.2
      have h1' : (Q1.j : ℝ) * dyadicDelta m ≤ x 1 := h1.2.2.1
      have h3 : ((Q2.j : ℝ) + 1) * dyadicDelta m ≤ (Q1.j : ℝ) * dyadicDelta m := by
        gcongr <;> norm_cast <;> linarith
      linarith

/-- Covering number at coarse scale of P_selected is at least |coarseConfig.P₀| / 9. -/
lemma cover_P_selected_lower
    {k m M MΔ : ℕ} {s C_cfg CΔ : ℝ}
    (hnm : m ≤ k)
    (config : CTNiceConfiguration k s C_cfg M)
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (hP_nonempty : P.Nonempty) :
    (coarseConfig.P₀.card : ENNReal) / 9 ≤
      Metric.externalCoveringNumber (dyadicDelta m).toNNReal
        (⋃ p ∈ P, (p.toSet : Set EuclideanPlane)) := by
  let δ := dyadicDelta m
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  have h_exists : ∀ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ →
      ∃ (p : DyadicSquare k), p ∈ P ∧ InductionConfigurations.containingSquare hnm p = Q := by
    intro Q hQ
    rw [hcoarse_P_eq] at hQ
    rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  choose p hp1 hp2 using h_exists
  let selectPoint (Q : DyadicSquare m) : EuclideanPlane :=
    dite (Q ∈ coarseConfig.P₀) (fun hQ => dyadicSquareCenter (p Q hQ)) (fun _ => 0)
  let X : Finset EuclideanPlane := coarseConfig.P₀.image selectPoint
  have h_select_eq : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.P₀),
      selectPoint Q = dyadicSquareCenter (p Q hQ) := by
    intro Q hQ
    exact dif_pos hQ
  have hX_sub : (X : Set EuclideanPlane) ⊆ (⋃ p ∈ P, (p.toSet : Set EuclideanPlane)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨Q, hQ, rfl⟩
    have h_p_in_P : p Q hQ ∈ P := hp1 Q hQ
    have h_center_in : dyadicSquareCenter (p Q hQ) ∈ (p Q hQ).toSet := dyadicSquareCenter_mem (p Q hQ)
    have h_eq : selectPoint Q = dyadicSquareCenter (p Q hQ) := h_select_eq Q hQ
    rw [h_eq]
    exact Set.mem_iUnion₂.mpr ⟨p Q hQ, h_p_in_P, h_center_in⟩
  have h_inj : Set.InjOn selectPoint (coarseConfig.P₀ : Set (DyadicSquare m)) := by
    intro Q1 hQ1 Q2 hQ2 h_eq
    have h1 : selectPoint Q1 ∈ (Q1.toSet : Set EuclideanPlane) := by
      rw [h_select_eq Q1 hQ1]
      let p1 := p Q1 hQ1
      have h_contain : InductionConfigurations.squareContained hnm p1 Q1 :=
        (InductionConfigurations.containingSquare_iff hnm p1 Q1).mp (hp2 Q1 hQ1)
      exact DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h_contain
        (dyadicSquareCenter_mem p1)
    have h2 : selectPoint Q2 ∈ (Q2.toSet : Set EuclideanPlane) := by
      rw [h_select_eq Q2 hQ2]
      let p2 := p Q2 hQ2
      have h_contain : InductionConfigurations.squareContained hnm p2 Q2 :=
        (InductionConfigurations.containingSquare_iff hnm p2 Q2).mp (hp2 Q2 hQ2)
      exact DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h_contain
        (dyadicSquareCenter_mem p2)
    rw [h_eq] at h1
    by_cases h : Q1 = Q2
    · exact h
    · have h_disj : Disjoint (Q1.toSet : Set EuclideanPlane) (Q2.toSet : Set EuclideanPlane) :=
        dyadicSquare_toSet_disjoint h
      have h_contra : selectPoint Q2 ≠ selectPoint Q2 :=
        Set.disjoint_iff_forall_ne.mp h_disj h1 h2
      exact False.elim (h_contra rfl)
  have hX_card : X.card = coarseConfig.P₀.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_cover_mono : Metric.externalCoveringNumber δ.toNNReal (X : Set EuclideanPlane) ≤
      Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ P, (p.toSet : Set EuclideanPlane)) :=
    Metric.externalCoveringNumber_mono_set hX_sub
  have h_main : ∀ (C : Set EuclideanPlane), Metric.IsCover δ.toNNReal (X : Set EuclideanPlane) C →
      (X.card : ENNReal) / 9 ≤ C.encard := by
    intro C hC
    by_cases hCfin : Set.Finite C
    · let Cfin := hCfin.toFinset
      have h2 : (Cfin : Set EuclideanPlane) = C := Set.Finite.coe_toFinset _
      have h3 : (X : Set EuclideanPlane) ⊆ ⋃ c ∈ Cfin, Metric.closedBall c δ := by
        have h4 : (X : Set EuclideanPlane) ⊆ ⋃ c ∈ C, Metric.closedBall c δ := by
          have h5 := hC.subset_iUnion_closedBall
          have h_rad : (δ.toNNReal : ℝ) = δ := by
            have h9 : 0 ≤ δ := hδ_pos.le
            have h10 : (Real.toNNReal δ : ℝ) = δ := by
              rw [Real.toNNReal_of_nonneg h9] <;> simp
            exact h10
          have h10 : (⋃ c ∈ C, Metric.closedBall c (δ.toNNReal : ℝ)) = (⋃ c ∈ C, Metric.closedBall c δ) := by
            apply Set.ext
            intro x
            simp only [Set.mem_iUnion₂]
            constructor
            · rintro ⟨c, hc, hball⟩
              have h11 : Metric.closedBall c (δ.toNNReal : ℝ) = Metric.closedBall c δ := by rw [h_rad]
              rw [h11] at hball
              exact ⟨c, hc, hball⟩
            · rintro ⟨c, hc, hball⟩
              have h11 : Metric.closedBall c (δ.toNNReal : ℝ) = Metric.closedBall c δ := by rw [h_rad]
              have hball' : x ∈ Metric.closedBall c (δ.toNNReal : ℝ) := by
                rw [h11]
                exact hball
              exact ⟨c, hc, hball'⟩
          rw [h10] at h5
          exact h5
        have h6 : (⋃ c ∈ C, Metric.closedBall c δ) = (⋃ c ∈ Cfin, Metric.closedBall c δ) := by
          apply Set.ext
          intro x
          simp only [Set.mem_iUnion₂]
          constructor
          · rintro ⟨c, hc, hball⟩
            have hc' : c ∈ Cfin := by
              have h : c ∈ (Cfin : Set EuclideanPlane) := h2.symm ▸ hc
              simpa using h
            exact ⟨c, hc', hball⟩
          · rintro ⟨c, hc, hball⟩
            have hc' : c ∈ C := by
              have h : c ∈ (Cfin : Set EuclideanPlane) := hc
              exact h2 ▸ h
            exact ⟨c, hc', hball⟩
        rw [h6] at h4
        exact h4
      have h4 : ∀ c ∈ Cfin, (X.filter (fun x => x ∈ Metric.closedBall c δ)).card ≤ 9 := by
        intro c _
        let Qs_in_ball := coarseConfig.P₀.filter (fun Q =>
            (Q.toSet ∩ Metric.closedBall c δ).Nonempty)
        have h5 : X.filter (fun x => x ∈ Metric.closedBall c δ) ⊆
            Qs_in_ball.image selectPoint := by
          intro x hx
          have h_x_in_X : x ∈ X := (Finset.mem_filter.mp hx).1
          rcases Finset.mem_image.mp h_x_in_X with ⟨Q, hQ, rfl⟩
          have h_in_ball : selectPoint Q ∈ Metric.closedBall c δ := (Finset.mem_filter.mp hx).2
          have h_pt_in_Q : selectPoint Q ∈ Q.toSet := by
            rw [h_select_eq Q hQ]
            let pQ := p Q hQ
            have h_contain : InductionConfigurations.squareContained hnm pQ Q :=
              (InductionConfigurations.containingSquare_iff hnm pQ Q).mp (hp2 Q hQ)
            exact DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h_contain
              (dyadicSquareCenter_mem pQ)
          have h_Q_intersect : (Q.toSet ∩ Metric.closedBall c δ).Nonempty :=
            ⟨selectPoint Q, h_pt_in_Q, h_in_ball⟩
          have hQ_in_filter : Q ∈ Qs_in_ball := Finset.mem_filter.mpr ⟨hQ, h_Q_intersect⟩
          exact Finset.mem_image.mpr ⟨Q, hQ_in_filter, rfl⟩
        have h6 : (X.filter (fun x => x ∈ Metric.closedBall c δ)).card ≤
            (Qs_in_ball.image selectPoint).card := Finset.card_le_card h5
        have h7 : (Qs_in_ball.image selectPoint).card ≤ Qs_in_ball.card := Finset.card_image_le
        have h8 : Qs_in_ball.card ≤ 9 := coarse_squares_intersecting_ball_at_most_9 c coarseConfig.P₀
        exact le_trans (le_trans h6 h7) h8
      have h5 : X ⊆ Cfin.biUnion (fun c => X.filter (fun x => x ∈ Metric.closedBall c δ)) := by
        intro x hx
        have h7 : x ∈ ⋃ c ∈ Cfin, Metric.closedBall c δ := h3 hx
        rcases Set.mem_iUnion₂.mp h7 with ⟨c, hc, hball⟩
        have h8 : x ∈ X.filter (fun x => x ∈ Metric.closedBall c δ) :=
          Finset.mem_filter.mpr ⟨hx, hball⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc, h8⟩
      have h9 : X.card ≤ ∑ c ∈ Cfin, (X.filter (fun x => x ∈ Metric.closedBall c δ)).card := by
        calc X.card
          ≤ (Cfin.biUnion (fun c => X.filter (fun x => x ∈ Metric.closedBall c δ))).card := Finset.card_le_card h5
        _ ≤ ∑ c ∈ Cfin, (X.filter (fun x => x ∈ Metric.closedBall c δ)).card := Finset.card_biUnion_le
      have h10 : ∑ c ∈ Cfin, (X.filter (fun x => x ∈ Metric.closedBall c δ)).card ≤ ∑ c ∈ Cfin, 9 :=
        Finset.sum_le_sum h4
      have h11 : X.card ≤ 9 * Cfin.card := by
        calc X.card
          ≤ ∑ c ∈ Cfin, (X.filter (fun x => x ∈ Metric.closedBall c δ)).card := h9
        _ ≤ ∑ c ∈ Cfin, 9 := h10
        _ = 9 * Cfin.card := by simp [Finset.sum_const] <;> ring
      have h12 : (X.card : ENNReal) / 9 ≤ (Cfin.card : ENNReal) := by
        have h13 : (X.card : ENNReal) ≤ (9 : ENNReal) * (Cfin.card : ENNReal) := by exact_mod_cast h11
        calc (X.card : ENNReal) / 9
          ≤ ((9 : ENNReal) * (Cfin.card : ENNReal)) / 9 := by gcongr
        _ = (Cfin.card : ENNReal) := by
          have h_comm : (9 : ENNReal) * (Cfin.card : ENNReal) = (Cfin.card : ENNReal) * (9 : ENNReal) := by ring
          rw [h_comm]
          exact ENNReal.mul_div_cancel_right (by norm_num) (by simp)
      have h14 : C.encard = ↑Cfin.card := by
        have h15 : C.encard = (Cfin : Set EuclideanPlane).encard := by rw [h2]
        rw [h15]
        simp
      rw [h14]
      exact_mod_cast h12
    · have h6 : C.encard = ⊤ := by rw [Set.encard_eq_top_iff]; exact hCfin
      rw [h6] <;> simp
  let n := Metric.externalCoveringNumber δ.toNNReal (X : Set EuclideanPlane)
  have h_pack : (X.card : ENNReal) / 9 ≤ (n : ENNReal) := by
    by_cases hn : n = ⊤
    · rw [hn] <;> simp
    · let S : Type _ := {s : Set EuclideanPlane // Metric.IsCover δ.toNNReal (X : Set EuclideanPlane) s}
      letI : Nonempty S := ⟨⟨(X : Set EuclideanPlane), Metric.IsCover.refl _ _⟩⟩
      let f : S → ℕ∞ := fun s => (s : Set EuclideanPlane).encard
      have h2 : ∃ (s : S), f s = iInf f := ENat.exists_eq_iInf f
      rcases h2 with ⟨s, hs_eq⟩
      have h4 : n = iInf f := by
        unfold n Metric.externalCoveringNumber
        exact iInf_subtype'
      have h3 : f s = n := by
        rw [hs_eq, h4]
      have h5 : (s : Set EuclideanPlane).encard ≠ ⊤ := by
        have h51 : (s : Set EuclideanPlane).encard = f s := by rfl
        rw [h51, h3] <;> exact hn
      have h4fin : Set.Finite (s : Set EuclideanPlane) := Set.encard_lt_top_iff.mp (lt_top_iff_ne_top.mpr h5)
      have h6 : (X.card : ENNReal) / 9 ≤ ((s : Set EuclideanPlane).encard : ENNReal) := h_main (s : Set EuclideanPlane) s.2
      have h7 : ((s : Set EuclideanPlane).encard : ENNReal) = (n : ENNReal) := by
        have h8 : (s : Set EuclideanPlane).encard = f s := by rfl
        rw [h8, h3]
      rw [h7] at h6
      exact h6
  have h_final : (X.card : ENNReal) / 9 ≤ (Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ P, (p.toSet : Set EuclideanPlane)) : ENNReal) := by
    have h7 : (n : ENNReal) ≤ (Metric.externalCoveringNumber δ.toNNReal (⋃ p ∈ P, (p.toSet : Set EuclideanPlane)) : ENNReal) := by
      exact_mod_cast h_cover_mono
    exact le_trans h_pack h7
  rw [hX_card] at h_final
  exact h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
