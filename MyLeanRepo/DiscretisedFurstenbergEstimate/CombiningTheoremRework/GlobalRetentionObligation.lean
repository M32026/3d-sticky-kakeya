module

/-
  Global Retention Obligation — CLOSED

  Derives global point retention `|config.P₀| ≤ K_global * |P|` from B1
  decomposition output plus uniform fiber-size bounds.

  Proof: split original points into retained coarse squares (Q) and
  non-retained ones (Q0 \\ Q). Use per-square retention on Q, uniform
  fiber upper bound on Q0 \\ Q, and lower bound on retained fibers to
  absorb the non-retained contribution into a global constant.

  Whiteprint node: combining_theorem_rework / global_retention_obligation
  Status: CLOSED — proved
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations

/-! ### General summation lemma -/

/-- Global retention from uniform fiber bounds.

    Given `Q ⊆ Q0`, fiber counts `F0` (original) and `F` (retained), with:
    - `|Q0| ≤ Kq * |Q|`
    - `A ≤ F0 i ≤ R * A` for all `i ∈ Q0`
    - `F0 i ≤ Kf * F i` for `i ∈ Q`

    Then `Σ_{Q0} F0 ≤ Kf * (1 + (Kq - 1) * R) * Σ_Q F`. -/
lemma global_retention_from_fiber_bounds
    {α : Type*} (Q0 Q : Finset α)
    (F0 F : α → ℕ)
    (Kq Kf R A : ℝ)
    (hA_pos : 0 < A) (hKf_pos : 0 < Kf) (hR_pos : 0 < R) (hKq_ge1 : 1 ≤ Kq)
    (hQ_sub : Q ⊆ Q0)
    (hQ_count : (Q0.card : ℝ) ≤ Kq * (Q.card : ℝ))
    (hF0_lower : ∀ i ∈ Q0, A ≤ (F0 i : ℝ))
    (hF0_upper : ∀ i ∈ Q0, (F0 i : ℝ) ≤ R * A)
    (hF_retention : ∀ i ∈ Q, (F0 i : ℝ) ≤ Kf * (F i : ℝ)) :
    (∑ i ∈ Q0, (F0 i : ℝ)) ≤ (Kf * (1 + (Kq - 1) * R)) * (∑ i ∈ Q, (F i : ℝ)) := by
  let Qdiff := Q0 \ Q
  have hQdiff_sub : Qdiff ⊆ Q0 := by
    simp [Qdiff]
    <;> tauto
  have h_disj : Disjoint Q Qdiff := Finset.disjoint_sdiff
  have h_union : Q ∪ Qdiff = Q0 := Finset.union_sdiff_of_subset hQ_sub
  set S_F := (∑ i ∈ Q, (F i : ℝ)) with hS_F_def
  -- Step 1: bound sum over Q
  have h_sum_Q : (∑ i ∈ Q, (F0 i : ℝ)) ≤ Kf * S_F := by
    have h3 : ∀ i ∈ Q, (F0 i : ℝ) ≤ Kf * (F i : ℝ) := hF_retention
    calc (∑ i ∈ Q, (F0 i : ℝ))
      ≤ ∑ i ∈ Q, (Kf * (F i : ℝ)) := Finset.sum_le_sum h3
    _ = Kf * S_F := by rw [Finset.mul_sum]
  -- Step 2: lower bound S_F ≥ |Q| * A / Kf
  have h_lower_F : ∀ i ∈ Q, (F i : ℝ) ≥ A / Kf := by
    intro i hi
    have h11 : A ≤ (F0 i : ℝ) := hF0_lower i (hQ_sub hi)
    have h12 : (F0 i : ℝ) ≤ Kf * (F i : ℝ) := hF_retention i hi
    have h13 : (F0 i : ℝ) / Kf ≤ (F i : ℝ) := by
      calc (F0 i : ℝ) / Kf
        ≤ (Kf * (F i : ℝ)) / Kf := by gcongr
      _ = (F i : ℝ) := by
        field_simp [hKf_pos.ne'] <;> ring
    have h14 : A / Kf ≤ (F0 i : ℝ) / Kf := by gcongr
    linarith
  have h_SF_lower : S_F ≥ (Q.card : ℝ) * (A / Kf) := by
    calc S_F
      ≥ ∑ i ∈ Q, (A / Kf) := Finset.sum_le_sum h_lower_F
    _ = (Q.card : ℝ) * (A / Kf) := by rw [Finset.sum_const] <;> ring
  -- Step 3: |Q| * A ≤ Kf * S_F
  have h_QA : (Q.card : ℝ) * A ≤ Kf * S_F := by
    have h : (Q.card : ℝ) * (A / Kf) ≤ S_F := h_SF_lower
    have h' : (Q.card : ℝ) * A ≤ Kf * S_F := by
      have h_eq : Kf * ((Q.card : ℝ) * (A / Kf)) = (Q.card : ℝ) * A := by
        field_simp [hKf_pos.ne'] <;> ring
      have h_ineq : Kf * ((Q.card : ℝ) * (A / Kf)) ≤ Kf * S_F := by gcongr
      rw [h_eq] at h_ineq
      exact h_ineq
    exact h'
  -- Step 4: bound |Qdiff|
  have h_card_diff : (Qdiff.card : ℝ) ≤ (Kq - 1) * (Q.card : ℝ) := by
    have h5 : Qdiff.card = Q0.card - Q.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hQ_sub] <;> omega
    have hQ_le : Q.card ≤ Q0.card := Finset.card_le_card hQ_sub
    have h6 : (Qdiff.card : ℝ) = (Q0.card : ℝ) - (Q.card : ℝ) := by
      rw [h5, Nat.cast_sub hQ_le] <;> simp
    rw [h6]
    linarith
  -- Step 5: bound sum over Qdiff
  have h_sum_diff : (∑ i ∈ Qdiff, (F0 i : ℝ)) ≤ (Qdiff.card : ℝ) * (R * A) := by
    have h8 : ∀ i ∈ Qdiff, (F0 i : ℝ) ≤ R * A := by
      intro i hi
      exact hF0_upper i (hQdiff_sub hi)
    calc (∑ i ∈ Qdiff, (F0 i : ℝ))
      ≤ ∑ i ∈ Qdiff, (R * A) := Finset.sum_le_sum h8
    _ = (Qdiff.card : ℝ) * (R * A) := by rw [Finset.sum_const] <;> ring
  -- Step 6: combine
  have h14 : (∑ i ∈ Qdiff, (F0 i : ℝ)) ≤ (Kq - 1) * Kf * R * S_F := by
    calc (∑ i ∈ Qdiff, (F0 i : ℝ))
      ≤ (Qdiff.card : ℝ) * (R * A) := h_sum_diff
    _ ≤ ((Kq - 1) * (Q.card : ℝ)) * (R * A) := by gcongr
    _ = (Kq - 1) * R * ((Q.card : ℝ) * A) := by ring
    _ ≤ (Kq - 1) * R * (Kf * S_F) := by gcongr
    _ = (Kq - 1) * Kf * R * S_F := by ring
  -- Final
  have h1 : (∑ i ∈ Q0, (F0 i : ℝ)) =
      (∑ i ∈ Q, (F0 i : ℝ)) + ∑ i ∈ Qdiff, (F0 i : ℝ) := by
    rw [← Finset.sum_union h_disj, h_union]
  rw [h1]
  have h_final : (∑ i ∈ Q, (F0 i : ℝ)) + ∑ i ∈ Qdiff, (F0 i : ℝ) ≤
      Kf * S_F + (Kq - 1) * Kf * R * S_F := by
    exact add_le_add h_sum_Q h14
  have h_ring : Kf * S_F + (Kq - 1) * Kf * R * S_F =
      (Kf * (1 + (Kq - 1) * R)) * S_F := by ring
  rw [h_ring] at h_final
  exact h_final

/-! ### Instantiation for B1 context -/

/-- Global retention from B1 decomposition plus uniform fiber bounds.

    Given the B1 bridge decomposition output and uniform bounds on the
    fine-fiber sizes in every coarse square hit by P₀, derive global
    point retention `|config.P₀| ≤ K_global * |P|`.

    Constant: `K_global = Kf * (1 + (K - 1) * R)`. -/
theorem b1_global_retention_from_heavy_fibers
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    {K Kf R A : ℝ} {P : Finset (DyadicSquare n)}
    {CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CombiningTheorem.NiceConfiguration m s CΔ MΔ}
    (hP_sub : P ⊆ config.P₀)
    (h_coarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_coarse_count : ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
        K * (coarseConfig.P₀.card : ℝ))
    (h_per_Q_ret : ∀ Q ∈ coarseConfig.P₀,
        ((config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) ≤
        Kf * ((P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ))
    -- Uniform fiber-size bounds
    (hA_pos : 0 < A) (hKf_pos : 0 < Kf) (hR_pos : 0 < R) (hK_ge1 : 1 ≤ K)
    (hF0_lower : ∀ Q ∈ config.P₀.image (InductionConfigurations.containingSquare hnm),
        A ≤ ((config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ))
    (hF0_upper : ∀ Q ∈ config.P₀.image (InductionConfigurations.containingSquare hnm),
        ((config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) ≤ R * A) :
    ∃ (K_global : ℝ), 0 < K_global ∧
      (config.P₀.card : ℝ) ≤ K_global * (P.card : ℝ) := by
  let Q0 := config.P₀.image (InductionConfigurations.containingSquare hnm)
  let Q := coarseConfig.P₀
  let F0 (Q : DyadicSquare m) : ℕ :=
    (config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card
  let F (Q : DyadicSquare m) : ℕ :=
    (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card
  have hQ_sub : Q ⊆ Q0 := by
    intro x hx
    have h1 : x ∈ P.image (InductionConfigurations.containingSquare hnm) := by
      rw [←h_coarse_P_eq]; exact hx
    have h2 : P.image (InductionConfigurations.containingSquare hnm) ⊆ Q0 := by
      apply Finset.image_subset_image
      exact hP_sub
    exact h2 h1
  have h_sum_F0 : (∑ Q ∈ Q0, (F0 Q : ℝ)) = (config.P₀.card : ℝ) := by
    have h_mapsTo : (config.P₀ : Set (DyadicSquare n)).MapsTo
        (InductionConfigurations.containingSquare hnm) (Q0 : Set (DyadicSquare m)) := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h := Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h' : config.P₀.card = ∑ Q ∈ Q0,
        (config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card := h
    have h_eq : ∀ q ∈ Q0,
        (config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card =
        (config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p q)).card := by
      intro q _
      have h_filter_eq : config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = q) =
          config.P₀.filter (fun p => InductionConfigurations.squareContained hnm p q) := by
        apply Finset.ext
        intro p
        simp only [Finset.mem_filter]
        <;> rw [InductionConfigurations.containingSquare_iff hnm p q]
      rw [h_filter_eq]
    have h_sum : ∑ Q ∈ Q0, (F0 Q : ℝ) = ∑ Q ∈ Q0,
        ((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [h_eq Q hQ]
    rw [h_sum]
    exact_mod_cast h'.symm
  have h_sum_F : (∑ q ∈ Q, (F q : ℝ)) = (P.card : ℝ) := by
    have h_mapsTo : (P : Set (DyadicSquare n)).MapsTo
        (InductionConfigurations.containingSquare hnm) (Q : Set (DyadicSquare m)) := by
      intro p hp
      have h1 : InductionConfigurations.containingSquare hnm p ∈ P.image (InductionConfigurations.containingSquare hnm) :=
        Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have h_eq1 : Q = P.image (InductionConfigurations.containingSquare hnm) := by
        simpa [Q] using h_coarse_P_eq
      rw [h_eq1] at *
      exact h1
    have h := Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h' : P.card = ∑ q ∈ Q,
        (P.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card := h
    have h_eq2 : ∀ q ∈ Q,
        (P.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card =
        (P.filter (fun p => InductionConfigurations.squareContained hnm p q)).card := by
      intro q _
      have h_filter_eq : P.filter (fun p => InductionConfigurations.containingSquare hnm p = q) =
          P.filter (fun p => InductionConfigurations.squareContained hnm p q) := by
        apply Finset.ext
        intro p
        simp only [Finset.mem_filter]
        <;> rw [InductionConfigurations.containingSquare_iff hnm p q]
      rw [h_filter_eq]
    have h_sum : ∑ q ∈ Q, (F q : ℝ) = ∑ q ∈ Q,
        ((P.filter (fun p => InductionConfigurations.containingSquare hnm p = q)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [h_eq2 q hq]
    rw [h_sum]
    exact_mod_cast h'.symm
  have h_main := global_retention_from_fiber_bounds
    Q0 Q F0 F K Kf R A
    hA_pos hKf_pos hR_pos hK_ge1
    hQ_sub h_coarse_count
    hF0_lower hF0_upper
    h_per_Q_ret
  refine' ⟨Kf * (1 + (K - 1) * R), by positivity, _⟩
  have h_final : (∑ i ∈ Q0, (F0 i : ℝ)) ≤ (Kf * (1 + (K - 1) * R)) * (∑ i ∈ Q, (F i : ℝ)) := h_main
  rw [h_sum_F0, h_sum_F] at h_final
  exact h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
