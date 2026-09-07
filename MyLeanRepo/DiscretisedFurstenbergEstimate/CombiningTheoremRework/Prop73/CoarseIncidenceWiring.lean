module

/-
  Coarse Incidence Wiring — Helper lemmas

  Provides:
  - IsSquareRootRegular.weaken_CK: weaken both C and K constants
  - coarseSquareOf: map point in selected union to its coarse square in P₀
  - coarse_constant_bound: constant bound for incidence regularity

  Whiteprint: combining_theorem_genuine / coarse_incidence_wiring
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq

noncomputable section

namespace DirecretisedFurstenbergEstimate.RegularIncidence

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Weaken both constants C and K of IsSquareRootRegular. -/
lemma IsSquareRootRegular.weaken_CK
    {δ t C K C' K' : ℝ} {P : Set EuclideanPlane}
    (h : IsSquareRootRegular δ t C K P)
    (hC : C ≤ C') (hK : K ≤ K') (hC'_pos : 0 < C') (hK'_pos : 0 < K') :
    IsSquareRootRegular δ t C' K' P := by
  rcases h with ⟨hsset, hcover⟩
  have hδ_pos : 0 < δ := hsset.2.1
  have hsset' : IsDeltaSSet δ t C' P := IsDeltaSSet.weaken_C hsset hC
  have h_nonneg : 0 ≤ Real.rpow δ (-t / 2) := Real.rpow_nonneg hδ_pos.le _
  have hcover' : Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (K' * Real.rpow δ (-t / 2)) := by
    have h6 : K * Real.rpow δ (-t / 2) ≤ K' * Real.rpow δ (-t / 2) := by
      gcongr <;> linarith
    have h7 : ENNReal.ofReal (K * Real.rpow δ (-t / 2)) ≤
        ENNReal.ofReal (K' * Real.rpow δ (-t / 2)) :=
      ENNReal.ofReal_le_ofReal h6
    exact le_trans hcover h7
  exact ⟨hsset', hcover'⟩

end DirecretisedFurstenbergEstimate.RegularIncidence

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DirecretisedFurstenbergEstimate.RegularIncidence
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-! ========================================================================
   squareOf construction

   Given a point p in the union of selected fine squares P_orig,
   produce the coarse square containing p and prove it is in P₀.
   ======================================================================== -/

/-- Given p ∈ ⋃_{Q ∈ P} Q.toSet, return the coarse square containing p.
    Uses Classical.choose to find a fine square in P containing p. -/
noncomputable def coarseSquareOf
    {k m : ℕ} (hnm : m ≤ k)
    {P : Finset (DyadicSquare k)}
    (p : EuclideanPlane)
    (hp : p ∈ ⋃ q ∈ P, (q.toSet : Set EuclideanPlane)) :
    DyadicSquare m :=
  let h_exists : ∃ (q : DyadicSquare k), q ∈ P ∧ p ∈ (q.toSet : Set EuclideanPlane) := by
    simpa [Finset.mem_biUnion] using hp
  let Q_fine : DyadicSquare k := Classical.choose h_exists
  InductionConfigurations.containingSquare hnm Q_fine

/-- The chosen coarse square contains p. -/
lemma coarseSquareOf_contains
    {k m : ℕ} (hnm : m ≤ k)
    {P : Finset (DyadicSquare k)}
    {p : EuclideanPlane}
    (hp : p ∈ ⋃ q ∈ P, (q.toSet : Set EuclideanPlane)) :
    p ∈ (coarseSquareOf hnm p hp).toSet := by
  let h_exists : ∃ (q : DyadicSquare k), q ∈ P ∧ p ∈ (q.toSet : Set EuclideanPlane) := by
    simpa [Finset.mem_biUnion] using hp
  let Q_fine : DyadicSquare k := Classical.choose h_exists
  have hQ_fine_in_P : Q_fine ∈ P := (Classical.choose_spec h_exists).1
  have hQ_fine_contains : p ∈ (Q_fine.toSet : Set EuclideanPlane) :=
    (Classical.choose_spec h_exists).2
  let Q_coarse : DyadicSquare m := coarseSquareOf hnm p hp
  have h_eq : Q_coarse = InductionConfigurations.containingSquare hnm Q_fine := by rfl
  have h_contained : InductionConfigurations.squareContained hnm Q_fine Q_coarse := by
    have h_eq' : InductionConfigurations.containingSquare hnm Q_fine = Q_coarse :=
      Eq.symm h_eq
    exact (InductionConfigurations.containingSquare_iff hnm Q_fine Q_coarse).mp h_eq'
  have h_sub : (Q_fine.toSet : Set EuclideanPlane) ⊆ (Q_coarse.toSet : Set EuclideanPlane) :=
    DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h_contained
  exact h_sub hQ_fine_contains

/-- The chosen coarse square is in P₀. -/
lemma coarseSquareOf_in_P₀
    {k m MΔ : ℕ} {s CΔ : ℝ}
    (hnm : m ≤ k)
    {P : Finset (DyadicSquare k)}
    (hcoarse_P_eq : ∀ (Q : DyadicSquare k), Q ∈ P →
      InductionConfigurations.containingSquare hnm Q ∈ (P.image (InductionConfigurations.containingSquare hnm)))
    {p : EuclideanPlane}
    (hp : p ∈ ⋃ q ∈ P, (q.toSet : Set EuclideanPlane)) :
    coarseSquareOf hnm p hp ∈ P.image (InductionConfigurations.containingSquare hnm) := by
  let h_exists : ∃ (q : DyadicSquare k), q ∈ P ∧ p ∈ (q.toSet : Set EuclideanPlane) := by
    simpa [Finset.mem_biUnion] using hp
  let Q_fine : DyadicSquare k := Classical.choose h_exists
  have hQ_fine_in_P : Q_fine ∈ P := (Classical.choose_spec h_exists).1
  have h_eq : coarseSquareOf hnm p hp = InductionConfigurations.containingSquare hnm Q_fine := by
    rfl
  rw [h_eq]
  exact Finset.mem_image.mpr ⟨Q_fine, hQ_fine_in_P, rfl⟩

/-! ========================================================================
   Constant bound for incidence regularity

   We need: 9 * K * C_between ≤ (dyadicDelta m)^{-ε_inc}

   This is stated as a hypothesis since it depends on the scale
   arrangement and smallness conditions chosen in the outer theorem.
   ======================================================================== -/

/-- Constant bound hypothesis for coarse incidence regularity.
    The outer theorem must ensure this holds by choosing scales
    small enough relative to ε_inc. -/
abbrev CoarseConstantBound (K C_between ε_inc : ℝ) (m : ℕ) : Prop :=
  9 * K * C_between ≤ Real.rpow (dyadicDelta m) (-ε_inc)

/-! ========================================================================
   Per-square covering density from B1 bridge cardinality

   For each coarse square Q, B1 bridge gives:
     |full_squares_in_Q| ≤ K * |thin_squares_in_Q|
   Using covering bounds (upper ≤ card, lower ≥ card/9), we derive:
     (1/(9K)) * EC(homothety '' full) ≤ EC(homothety '' thin)
   This is exactly the per-square density needed by
   `between_scales_transfer_with_density`.
   ======================================================================== -/

/-- Per-square covering density from cardinality ratio.

    Given full and thin finsets of fine squares all contained in the same
    coarse square Q, with `card_full ≤ K * card_thin`, derive the covering
    density bound after normalization by the homothety mapping Q to the
    unit square. -/
lemma per_square_covering_density
    {k m : ℕ} (hnm : m ≤ k)
    (Q : DyadicSquare m)
    (P_full P_thin : Finset (DyadicSquare k))
    (h_full : ∀ p ∈ P_full, InductionConfigurations.squareContained hnm p Q)
    (h_thin : ∀ p ∈ P_thin, InductionConfigurations.squareContained hnm p Q)
    (K : ℝ) (hK_pos : 0 < K)
    (h_card : (P_full.card : ℝ) ≤ K * (P_thin.card : ℝ)) :
    ENNReal.ofReal (1 / (9 * K)) *
      Metric.externalCoveringNumber (dyadicDelta k / dyadicDelta m).toNNReal
        (homothetyS (dyadicDelta m) Q.i Q.j ''
          (⋃ p ∈ P_full, (p.toSet : Set Plane))) ≤
    Metric.externalCoveringNumber (dyadicDelta k / dyadicDelta m).toNNReal
        (homothetyS (dyadicDelta m) Q.i Q.j ''
          (⋃ p ∈ P_thin, (p.toSet : Set Plane))) := by
  let rf : ℕ := InductionConfigurations.refinementFactor k m
  let δ' : ℝ := dyadicDelta k / dyadicDelta m
  have hδk_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  have hδm_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have hδ'_pos : 0 < δ' := div_pos hδk_pos hδm_pos
  have hrf_pos : 0 < rf := by
    dsimp only [rf, InductionConfigurations.refinementFactor] <;> positivity
  have hδ'_eq : δ' = dyadicDelta (k - m) := by
    dsimp only [δ', dyadicDelta]
    have h_sum : m + (k - m) = k := by omega
    have h_pow : (2 : ℝ)^k = (2 : ℝ)^m * (2 : ℝ)^(k - m) := by
      rw [← pow_add, h_sum]
    have h_pos1 : (0 : ℝ) < (2 : ℝ)^m := by positivity
    have h_pos2 : (0 : ℝ) < (2 : ℝ)^(k - m) := by positivity
    rw [h_pow]
    field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  let Q_full := P_full.image (InductionConfigurations.squareHomothety hnm Q)
  let Q_thin := P_thin.image (InductionConfigurations.squareHomothety hnm Q)
  have h_union_full : (⋃ p ∈ P_full, (InductionConfigurations.squareHomothety hnm Q p).toSet) =
      ⋃ q ∈ Q_full, (q.toSet : Set Plane) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp, hx⟩
      have hq : InductionConfigurations.squareHomothety hnm Q p ∈ Q_full :=
        Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact ⟨InductionConfigurations.squareHomothety hnm Q p, hq, hx⟩
    · rintro ⟨q, hq, hx⟩
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      exact ⟨p, hp, hx⟩
  have h_union_thin : (⋃ p ∈ P_thin, (InductionConfigurations.squareHomothety hnm Q p).toSet) =
      ⋃ q ∈ Q_thin, (q.toSet : Set Plane) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨p, hp, hx⟩
      have hq : InductionConfigurations.squareHomothety hnm Q p ∈ Q_thin :=
        Finset.mem_image.mpr ⟨p, hp, rfl⟩
      exact ⟨InductionConfigurations.squareHomothety hnm Q p, hq, hx⟩
    · rintro ⟨q, hq, hx⟩
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      exact ⟨p, hp, hx⟩
  have h_img_full : homothetyS (dyadicDelta m) Q.i Q.j ''
        (⋃ p ∈ P_full, (p.toSet : Set Plane)) =
      ⋃ q ∈ Q_full, (q.toSet : Set Plane) := by
    rw [← h_union_full]
    exact (fine_point_set_homothety_image hnm Q P_full h_full).symm
  have h_img_thin : homothetyS (dyadicDelta m) Q.i Q.j ''
        (⋃ p ∈ P_thin, (p.toSet : Set Plane)) =
      ⋃ q ∈ Q_thin, (q.toSet : Set Plane) := by
    rw [← h_union_thin]
    exact (fine_point_set_homothety_image hnm Q P_thin h_thin).symm
  rw [h_img_full, h_img_thin]
  have h_inj : Function.Injective (InductionConfigurations.squareHomothety hnm Q) := by
    intro p1 p2 h
    have hi : (InductionConfigurations.squareHomothety hnm Q p1).i =
        (InductionConfigurations.squareHomothety hnm Q p2).i := by rw [h]
    have hj : (InductionConfigurations.squareHomothety hnm Q p1).j =
        (InductionConfigurations.squareHomothety hnm Q p2).j := by rw [h]
    simp [InductionConfigurations.squareHomothety] at hi hj
    have h_i : p1.i = p2.i := by linarith
    have h_j : p1.j = p2.j := by linarith
    cases p1 <;> cases p2 <;> simp_all
  have h_card_Q : (Q_full.card : ℝ) ≤ K * (Q_thin.card : ℝ) := by
    have h1 : Q_full.card = P_full.card := Finset.card_image_of_injective _ h_inj
    have h2 : Q_thin.card = P_thin.card := Finset.card_image_of_injective _ h_inj
    rw [h1, h2]
    exact h_card
  have h_main := global_covering_density_from_cardinality Q_full Q_thin K hK_pos h_card_Q
  have h_scale : (dyadicDelta k / dyadicDelta m).toNNReal = (dyadicDelta (k - m)).toNNReal := by
    rw [show dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) from hδ'_eq]
  rw [h_scale] at *
  exact h_main

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
