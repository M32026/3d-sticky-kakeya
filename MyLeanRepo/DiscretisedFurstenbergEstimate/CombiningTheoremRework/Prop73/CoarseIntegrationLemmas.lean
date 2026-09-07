module

/-
  Coarse Integration Lemmas

  Wiring lemmas connecting B1 bridge output to the coarse incidence estimate.

  Provides:
  1. b1_bridge_to_per_square_density: extract per-square density from B1 bridge
  2. (pending) coarse_point_set_regularity: IsSquareRootRegular construction
  3. (pending) incidence_output_to_goal: output conversion

  Whiteprint: combining_theorem_genuine / coarse_integration
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseIncidenceWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FinePointsetGlue
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Helper: two integers whose half-open intervals `[i*δ, (i+1)*δ)` and
    `[j*δ, (j+1)*δ)` both contain `x` must be equal. -/
lemma int_interval_unique {i j : ℤ} {x δ : ℝ} (hδ : 0 < δ)
    (h1 : (i : ℝ) * δ ≤ x) (h2 : x < ((i : ℝ) + 1) * δ)
    (h3 : (j : ℝ) * δ ≤ x) (h4 : x < ((j : ℝ) + 1) * δ) : i = j := by
  by_cases h : i < j
  · have h5 : i + 1 ≤ j := Int.add_one_le_of_lt h
    have h6' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h5
    have h6 : ((i : ℝ) + 1) * δ ≤ (j : ℝ) * δ := by gcongr
    linarith
  · by_cases h2 : j < i
    · have h5 : j + 1 ≤ i := Int.add_one_le_of_lt h2
      have h6' : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h5
      have h6 : ((j : ℝ) + 1) * δ ≤ (i : ℝ) * δ := by gcongr
      linarith
    · omega

/-- If a point is in both a fine dyadic square and a coarse dyadic square,
    then the fine square is contained in the coarse square. -/
lemma fine_point_in_coarse_square_implies_contained
    {k m : ℕ} (hnm : m ≤ k) {p : DyadicSquare k} {Q : DyadicSquare m}
    {x : EuclideanPlane} (hxp : x ∈ p.toSet) (hxQ : x ∈ Q.toSet) :
    InductionConfigurations.squareContained hnm p Q := by
  let Q' := InductionConfigurations.containingSquare hnm p
  have h1 : InductionConfigurations.squareContained hnm p Q' := by
    have h_eq : InductionConfigurations.containingSquare hnm p = Q' := by rfl
    exact (InductionConfigurations.containingSquare_iff hnm p Q').mp h_eq
  have h2 : (p.toSet : Set Plane) ⊆ (Q'.toSet : Set Plane) :=
    DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h1
  have h3 : x ∈ Q'.toSet := h2 hxp
  have hδ_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have hi : Q'.i = Q.i := int_interval_unique hδ_pos
    h3.1 h3.2.1 hxQ.1 hxQ.2.1
  have hj : Q'.j = Q.j := int_interval_unique hδ_pos
    h3.2.2.1 h3.2.2.2 hxQ.2.2.1 hxQ.2.2.2
  have h4 : Q' = Q := by
    have h_inj : Function.Injective (fun p : DyadicSquare m => (p.i, p.j)) := by
      intro p q h
      cases p <;> cases q <;> simpa [Prod.ext_iff] using h
    exact h_inj (Prod.ext hi hj)
  have h5 : InductionConfigurations.containingSquare hnm p = Q := h4
  exact (InductionConfigurations.containingSquare_iff hnm p Q).mp h5

/-! ========================================================================
   Lemma 1: B1 bridge → per-square covering density
   ======================================================================== -/

/-- Extract per-square covering density from B1 bridge cardinality bounds.

    Given the full point set (restricted to coarse squares that have thin
    counterparts) and the thin point set, produce the `hdensity` function
    required by `between_scales_transfer_with_density`. -/
lemma b1_bridge_to_per_square_density
    {k m M MΔ : ℕ} {s C_cfg CΔ : ℝ}
    (hnm : m ≤ k)
    (config : CTNiceConfiguration k s C_cfg M)
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (P : Finset (DyadicSquare k))
    {K : ℝ} (hK_pos : 0 < K)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_ineq : ∀ Q ∈ coarseConfig.P₀,
      ((config.P₀.filter fun p => InductionConfigurations.squareContained hnm p Q).card : ℝ) ≤
      K * ((P.filter fun p => InductionConfigurations.squareContained hnm p Q).card : ℝ))
    (P_full_set P_thin_set : Set Plane)
    (hP_full_def : P_full_set =
      ⋃ p ∈ (config.P₀.filter fun p => InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀),
        (p.toSet : Set Plane))
    (hP_thin_def : P_thin_set = ⋃ p ∈ P, (p.toSet : Set Plane)) :
    ∀ (i j : ℤ), (P_full_set ∩ dyadicSquare (dyadicDelta m) i j).Nonempty →
      ENNReal.ofReal (1 / (9 * K)) *
        Metric.externalCoveringNumber ((dyadicDelta k) / (dyadicDelta m)).toNNReal
          (homothetyS (dyadicDelta m) i j '' (P_full_set ∩ dyadicSquare (dyadicDelta m) i j)) ≤
      Metric.externalCoveringNumber ((dyadicDelta k) / (dyadicDelta m)).toNNReal
          (homothetyS (dyadicDelta m) i j '' (P_thin_set ∩ dyadicSquare (dyadicDelta m) i j)) := by
  classical
  intro i j h_nonempty
  let Q : DyadicSquare m := ⟨i, j⟩
  have hQ_set : (Q.toSet : Set Plane) = dyadicSquare (dyadicDelta m) i j :=
    dyadicSquare_toSet_eq Q
  have hQ_in : Q ∈ coarseConfig.P₀ := by
    rcases h_nonempty with ⟨x, hx⟩
    have hx_full : x ∈ P_full_set := hx.1
    have hx_Qsq : x ∈ Q.toSet := by
      rw [hQ_set]
      exact hx.2
    rw [hP_full_def] at hx_full
    have h_exists : ∃ (p : DyadicSquare k), p ∈ (config.P₀.filter fun p => InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀) ∧ x ∈ (p.toSet : Set Plane) := by
      simpa [Set.mem_iUnion] using hx_full
    rcases h_exists with ⟨p, hp, hxp⟩
    have h2 : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀ :=
      (Finset.mem_filter.mp hp).2
    have h3 : InductionConfigurations.squareContained hnm p Q :=
      fine_point_in_coarse_square_implies_contained hnm hxp hx_Qsq
    have h4 : InductionConfigurations.containingSquare hnm p = Q :=
      (InductionConfigurations.containingSquare_iff hnm p Q).mpr h3
    rw [h4] at h2
    exact h2
  let P_full_Q := config.P₀.filter fun p => InductionConfigurations.squareContained hnm p Q
  let P_thin_Q := P.filter fun p => InductionConfigurations.squareContained hnm p Q
  have h_full_cont : ∀ p ∈ P_full_Q, InductionConfigurations.squareContained hnm p Q := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h_thin_cont : ∀ p ∈ P_thin_Q, InductionConfigurations.squareContained hnm p Q := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have h_card : (P_full_Q.card : ℝ) ≤ K * (P_thin_Q.card : ℝ) :=
    h_card_ineq Q hQ_in
  have h_main := per_square_covering_density hnm Q P_full_Q P_thin_Q
    h_full_cont h_thin_cont K hK_pos h_card
  have h_intersection_full : P_full_set ∩ dyadicSquare (dyadicDelta m) i j =
      ⋃ p ∈ P_full_Q, (p.toSet : Set Plane) := by
    rw [hP_full_def]
    ext x
    constructor
    · intro hx
      have h_x_iUnion : x ∈ (⋃ p ∈ (config.P₀.filter fun p => InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀), (p.toSet : Set Plane)) := hx.1
      have h_x_Q : x ∈ dyadicSquare (dyadicDelta m) i j := hx.2
      have h_xQ_set : x ∈ Q.toSet := by
        rw [hQ_set]; exact h_x_Q
      have h_exists : ∃ (p : DyadicSquare k), p ∈ (config.P₀.filter fun p => InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀) ∧ x ∈ (p.toSet : Set Plane) := by
        simpa using h_x_iUnion
      rcases h_exists with ⟨p, hp, hxp⟩
      have h6 : p ∈ config.P₀ := (Finset.mem_filter.mp hp).1
      have h8 : InductionConfigurations.squareContained hnm p Q :=
        fine_point_in_coarse_square_implies_contained hnm hxp h_xQ_set
      have h5 : p ∈ P_full_Q := Finset.mem_filter.mpr ⟨h6, h8⟩
      simpa using ⟨p, h5, hxp⟩
    · intro hx
      have h_exists : ∃ (p : DyadicSquare k), p ∈ P_full_Q ∧ x ∈ (p.toSet : Set Plane) := by
        simpa using hx
      rcases h_exists with ⟨p, hp, hxp⟩
      have h5 : p ∈ config.P₀ := (Finset.mem_filter.mp hp).1
      have h7 : InductionConfigurations.squareContained hnm p Q := (Finset.mem_filter.mp hp).2
      have h8 : InductionConfigurations.containingSquare hnm p = Q :=
        (InductionConfigurations.containingSquare_iff hnm p Q).mpr h7
      have h6 : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀ := by
        rw [h8]; exact hQ_in
      have h9 : p ∈ (config.P₀.filter fun p => InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀) :=
        Finset.mem_filter.mpr ⟨h5, h6⟩
      have h10 : x ∈ dyadicSquare (dyadicDelta m) i j := by
        have h11 : x ∈ p.toSet := hxp
        have h12 : p.toSet ⊆ Q.toSet :=
          DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h7
        have h13 : x ∈ Q.toSet := h12 h11
        rw [hQ_set] at h13
        exact h13
      have h14 : x ∈ (⋃ p ∈ (config.P₀.filter fun p => InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀), (p.toSet : Set Plane)) := by
        have h9' : p ∈ config.P₀ ∧ InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀ := Finset.mem_filter.mp h9
        simpa using ⟨p, h9', hxp⟩
      exact ⟨h14, h10⟩
  have h_intersection_thin : P_thin_set ∩ dyadicSquare (dyadicDelta m) i j =
      ⋃ p ∈ P_thin_Q, (p.toSet : Set Plane) := by
    rw [hP_thin_def]
    ext x
    constructor
    · intro hx
      have h_x_iUnion : x ∈ (⋃ p ∈ P, (p.toSet : Set Plane)) := hx.1
      have h_x_Q : x ∈ dyadicSquare (dyadicDelta m) i j := hx.2
      have h_xQ_set : x ∈ Q.toSet := by
        rw [hQ_set]; exact h_x_Q
      have h_exists : ∃ (p : DyadicSquare k), p ∈ P ∧ x ∈ (p.toSet : Set Plane) := by
        simpa using h_x_iUnion
      rcases h_exists with ⟨p, hp, hxp⟩
      have h7 : InductionConfigurations.squareContained hnm p Q :=
        fine_point_in_coarse_square_implies_contained hnm hxp h_xQ_set
      have h5 : p ∈ P_thin_Q := Finset.mem_filter.mpr ⟨hp, h7⟩
      simpa using ⟨p, h5, hxp⟩
    · intro hx
      have h_exists : ∃ (p : DyadicSquare k), p ∈ P_thin_Q ∧ x ∈ (p.toSet : Set Plane) := by
        simpa using hx
      rcases h_exists with ⟨p, hp, hxp⟩
      have h5 : p ∈ P := (Finset.mem_filter.mp hp).1
      have h7 : InductionConfigurations.squareContained hnm p Q := (Finset.mem_filter.mp hp).2
      have h6 : x ∈ dyadicSquare (dyadicDelta m) i j := by
        have h8 : p.toSet ⊆ Q.toSet :=
          DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h7
        have h9 : x ∈ Q.toSet := h8 hxp
        rw [hQ_set] at h9
        exact h9
      have h10 : x ∈ (⋃ p ∈ P, (p.toSet : Set Plane)) := by
        simpa using ⟨p, h5, hxp⟩
      exact ⟨h10, h6⟩
  rw [h_intersection_full, h_intersection_thin]
  exact h_main

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
