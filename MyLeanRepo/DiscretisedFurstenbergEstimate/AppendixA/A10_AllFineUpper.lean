module

/-
  h_allFine_upper: bound the δ-covering number of allFineParamsEuclidean.

  Provides the final step: from |allFineParams| ≤ Δ^{-(2s+2ε)}, derive
  2000 * Ncover_δ(allFineParams) < Δ^{-(2s+η_upper)}.

  The cardinality bound itself comes from the counter-assumption via A5/A6
  and is the caller's responsibility.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Canonical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_Fixed
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open A10 (allFineParamsEuclidean)

/-- allFineParamsEuclidean is finite: finite union of finite images. -/
lemma allFineParams_finite {Δ δ s t ε : ℝ} (a9 : A9_Output Δ δ s t ε) :
    (allFineParamsEuclidean a9).Finite := by
  let f (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0) : Set EuclideanPlane :=
    ⋃ (p : EuclideanPlane) (hp : p ∈ (a9.perSquare Q hQ).P_norm_Q),
      (A10.toPlane' ∘ (paramsOfDyadicCell δ)) ''
        ((a9.perSquare Q hQ).fineTubes_norm p : Set (DyadicTubeCell δ))
  let g (Q : CoarseSquare Δ) : Set EuclideanPlane :=
    if hQ : Q ∈ a9.Q0 then f Q hQ else ∅
  have h_main : ∀ (Q : CoarseSquare Δ), Q ∈ a9.Q0 → (g Q).Finite := by
    intro Q hQ
    dsimp only [g]
    rw [dif_pos hQ]
    apply Set.Finite.biUnion (Finset.finite_toSet (a9.perSquare Q hQ).P_norm_Q)
    intro p _
    exact Set.Finite.image _ (Finset.finite_toSet _)
  have h_eq : allFineParamsEuclidean a9 = ⋃ Q ∈ (a9.Q0 : Set (CoarseSquare Δ)), g Q := by
    ext x
    simp [allFineParamsEuclidean, g, f, Set.mem_iUnion]
    <;> aesop
  rw [h_eq]
  exact Set.Finite.biUnion (Finset.finite_toSet a9.Q0) h_main

/-- Final step of h_allFine_upper: from a cardinality bound on allFineParams,
    derive the ENNReal inequality needed by A10. Generalized version:
    from |allFineParams| ≤ C * Δ^{-(2s+k)}, derive
    2000 * Ncover_δ(allFineParams) < Δ^{-(2s+η_upper)}
    when η_upper > k and Δ is sufficiently small. -/
lemma allFineUpper_general
    {Δ δ s t ε η_upper k C : ℝ}
    (a9 : A9_Output Δ δ s t ε)
    (hε_pos : 0 < ε)
    (hη_upper_pos : 0 < η_upper)
    (hk_pos : 0 < k)
    (hη_upper_gt_k : k < η_upper)
    (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hfin : (allFineParamsEuclidean a9).Finite)
    (h_card_bound : (hfin.toFinset.card : ℝ) ≤ C * Real.rpow Δ (-(2 * s + k)))
    (hC_nonneg : 0 ≤ C)
    (hΔ_small : (2000 : ℝ) * C < Real.rpow Δ (-(η_upper - k))) :
    (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal
        (allFineParamsEuclidean a9) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
  let S : Finset EuclideanPlane := hfin.toFinset
  have hS_eq : (S : Set EuclideanPlane) = allFineParamsEuclidean a9 := by
    exact Set.Finite.coe_toFinset _
  have h_card : (S.card : ℝ) ≤ C * Real.rpow Δ (-(2 * s + k)) := by
    simpa [S] using h_card_bound
  have hS_fin : (S : Set EuclideanPlane).Finite := by exact_mod_cast S.finite_toSet
  have h_enc : (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane)) ≤
      (S : Set EuclideanPlane).encard :=
    Metric.externalCoveringNumber_le_encard_self (ε := δ.toNNReal) (A := (S : Set EuclideanPlane))
  have h_encard : (S : Set EuclideanPlane).encard = ↑S.card := by
    rw [Set.Finite.encard_eq_coe hS_fin] <;> simp
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (allFineParamsEuclidean a9) : ENNReal) ≤
      (S.card : ENNReal) := by
    rw [← hS_eq]
    have h' : (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) : ENNReal) ≤
        ((S : Set EuclideanPlane).encard : ENNReal) := by exact_mod_cast h_enc
    have h'' : ((S : Set EuclideanPlane).encard : ENNReal) = (S.card : ENNReal) := by
      rw [h_encard] <;> rfl
    rw [h''] at h'
    exact h'
  have h2 : (S.card : ENNReal) ≤ ENNReal.ofReal (C * Real.rpow Δ (-(2 * s + k))) := by
    have h2b : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by simp
    rw [h2b]
    exact ENNReal.ofReal_le_ofReal h_card
  have h3 : (2000 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal
        (allFineParamsEuclidean a9) : ENNReal) ≤
      (2000 : ENNReal) * ENNReal.ofReal (C * Real.rpow Δ (-(2 * s + k))) := by
    gcongr <;> exact h1.trans h2
  have hpos1 : 0 < Real.rpow Δ (-(2 * s + k)) := Real.rpow_pos_of_pos hΔ_pos _
  have h7 : 0 < η_upper - k := by linarith
  have h_rpow_add : Real.rpow Δ (-(2 * s + η_upper)) =
      Real.rpow Δ (-(2 * s + k)) * Real.rpow Δ (-(η_upper - k)) := by
    have h_eq1 : (-(2 * s + η_upper)) = (-(2 * s + k)) + (-(η_upper - k)) := by ring
    rw [h_eq1]
    exact Real.rpow_add hΔ_pos _ _
  have h_pos_prod : 0 ≤ (2000 : ℝ) * C * Real.rpow Δ (-(2 * s + k)) := by positivity
  have h_nonneg2 : 0 ≤ C * Real.rpow Δ (-(2 * s + k)) := by positivity
  have h10 : (2000 : ENNReal) * ENNReal.ofReal (C * Real.rpow Δ (-(2 * s + k))) =
      ENNReal.ofReal ((2000 : ℝ) * C * Real.rpow Δ (-(2 * s + k))) := by
    have h11 : (2000 : ENNReal) = ENNReal.ofReal (2000 : ℝ) := by simp
    have h12 : ENNReal.ofReal ((2000 : ℝ) * (C * Real.rpow Δ (-(2 * s + k)))) =
        ENNReal.ofReal (2000 : ℝ) * ENNReal.ofReal (C * Real.rpow Δ (-(2 * s + k))) :=
      ENNReal.ofReal_mul (by positivity)
    have h13 : (2000 : ℝ) * (C * Real.rpow Δ (-(2 * s + k))) =
        (2000 : ℝ) * C * Real.rpow Δ (-(2 * s + k)) := by ring
    rw [h11, ← h12, h13]
  rw [h10] at h3
  have h6 : (2000 : ℝ) * C * Real.rpow Δ (-(2 * s + k)) <
      Real.rpow Δ (-(2 * s + η_upper)) := by
    rw [h_rpow_add]
    have h8 : (2000 : ℝ) * C < Real.rpow Δ (-(η_upper - k)) := hΔ_small
    have h9 : (2000 : ℝ) * C * Real.rpow Δ (-(2 * s + k)) <
        Real.rpow Δ (-(η_upper - k)) * Real.rpow Δ (-(2 * s + k)) := by
      exact mul_lt_mul_of_pos_right h8 hpos1
    linarith
  have h13 : 0 < Real.rpow Δ (-(2 * s + η_upper)) := Real.rpow_pos_of_pos hΔ_pos _
  have h11 : ENNReal.ofReal ((2000 : ℝ) * C * Real.rpow Δ (-(2 * s + k))) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
    rw [ENNReal.ofReal_lt_ofReal_iff h13]
    exact h6
  exact lt_of_le_of_lt h3 h11

/-- Final step of h_allFine_upper: from |allFineParams| ≤ Δ^{-(2s+2ε)}, derive
    2000 * Ncover_δ(allFineParams) < Δ^{-(2s+η_upper)}. -/
lemma allFineUpper_from_card_bound
    {Δ δ s t ε η_upper : ℝ}
    (a9 : A9_Output Δ δ s t ε)
    (hs : 0 < s)
    (hε_pos : 0 < ε)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_2ε : 2 * ε < η_upper)
    (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hfin : (allFineParamsEuclidean a9).Finite)
    (h_card_bound : hfin.toFinset.card ≤ Real.rpow Δ (-(2 * s + 2 * ε)))
    (hΔ_small : (2000 : ℝ) < Real.rpow Δ (-(η_upper - 2 * ε))) :
    (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal
        (allFineParamsEuclidean a9) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
  let S : Finset EuclideanPlane := hfin.toFinset
  have hS_eq : (S : Set EuclideanPlane) = allFineParamsEuclidean a9 := by
    exact Set.Finite.coe_toFinset _
  have h_card : (S.card : ℝ) ≤ Real.rpow Δ (-(2 * s + 2 * ε)) := by
    simpa [S] using h_card_bound
  -- Ncover_δ(S) ≤ |S|
  have hS_fin : (S : Set EuclideanPlane).Finite := by exact_mod_cast S.finite_toSet
  have h_enc : (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane)) ≤
      (S : Set EuclideanPlane).encard :=
    Metric.externalCoveringNumber_le_encard_self (ε := δ.toNNReal) (A := (S : Set EuclideanPlane))
  have h_encard : (S : Set EuclideanPlane).encard = ↑S.card := by
    rw [Set.Finite.encard_eq_coe hS_fin]
    <;> simp
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (allFineParamsEuclidean a9) : ENNReal) ≤
      (S.card : ENNReal) := by
    rw [← hS_eq]
    have h' : (Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) : ENNReal) ≤
        ((S : Set EuclideanPlane).encard : ENNReal) := by exact_mod_cast h_enc
    have h'' : ((S : Set EuclideanPlane).encard : ENNReal) = (S.card : ENNReal) := by
      rw [h_encard] <;> rfl
    rw [h''] at h'
    exact h'
  have h2 : (S.card : ENNReal) ≤ ENNReal.ofReal (Real.rpow Δ (-(2 * s + 2 * ε))) := by
    have h2a : (S.card : ℝ) ≤ Real.rpow Δ (-(2 * s + 2 * ε)) := h_card
    have h2b : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by simp
    rw [h2b]
    exact ENNReal.ofReal_le_ofReal h2a
  have h3 : (2000 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal
        (allFineParamsEuclidean a9) : ENNReal) ≤
      (2000 : ENNReal) * ENNReal.ofReal (Real.rpow Δ (-(2 * s + 2 * ε))) := by
    gcongr
    <;> exact h1.trans h2
  have hpos1 : 0 < Real.rpow Δ (-(2 * s + 2 * ε)) := Real.rpow_pos_of_pos hΔ_pos _
  have h7 : 0 < η_upper - 2 * ε := by linarith
  have h_rpow_add : Real.rpow Δ (-(2 * s + η_upper)) =
      Real.rpow Δ (-(2 * s + 2 * ε)) * Real.rpow Δ (-(η_upper - 2 * ε)) := by
    have h_eq1 : (-(2 * s + η_upper)) = (-(2 * s + 2 * ε)) + (-(η_upper - 2 * ε)) := by ring
    rw [h_eq1]
    exact Real.rpow_add hΔ_pos _ _
  have h6 : (2000 : ℝ) * Real.rpow Δ (-(2 * s + 2 * ε)) <
      Real.rpow Δ (-(2 * s + η_upper)) := by
    rw [h_rpow_add]
    have h8 : (2000 : ℝ) < Real.rpow Δ (-(η_upper - 2 * ε)) := hΔ_small
    have h9 : (2000 : ℝ) * Real.rpow Δ (-(2 * s + 2 * ε)) <
        Real.rpow Δ (-(η_upper - 2 * ε)) * Real.rpow Δ (-(2 * s + 2 * ε)) := by
      exact mul_lt_mul_of_pos_right h8 hpos1
    linarith
  have h_pos2 : 0 ≤ (2000 : ℝ) * Real.rpow Δ (-(2 * s + 2 * ε)) := by positivity
  have h10 : (2000 : ENNReal) * ENNReal.ofReal (Real.rpow Δ (-(2 * s + 2 * ε))) =
      ENNReal.ofReal ((2000 : ℝ) * Real.rpow Δ (-(2 * s + 2 * ε))) := by
    simp [h_pos2, ENNReal.ofReal_mul]
    <;> norm_cast
  rw [h10] at h3
  have h11 : ENNReal.ofReal ((2000 : ℝ) * Real.rpow Δ (-(2 * s + 2 * ε))) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
    have h13 : 0 < Real.rpow Δ (-(2 * s + η_upper)) := Real.rpow_pos_of_pos hΔ_pos _
    rw [ENNReal.ofReal_lt_ofReal_iff h13]
    exact h6
  exact lt_of_le_of_lt h3 h11

/-- Cardinal of allFineParamsEuclidean is bounded by the sum of fineTubes_norm
    cardinals across all squares and points.

    This is the bridge from the A9 normalized parameter set to the per-point
    fine tube counts, which can then be bounded via A5 incidence counting. -/
lemma allFineParams_card_le_sum {Δ δ s t ε : ℝ} (a9 : A9_Output Δ δ s t ε) :
    ∃ (hfin : (allFineParamsEuclidean a9).Finite),
      hfin.toFinset.card ≤
      ∑ Q' ∈ a9.Q0.attach,
        ∑ p ∈ (a9.perSquare Q'.val Q'.property).P_norm_Q,
          ((a9.perSquare Q'.val Q'.property).fineTubes_norm p).card := by
  let f_cell : DyadicTubeCell δ → EuclideanPlane :=
    fun cell => A10.toPlane' (paramsOfDyadicCell δ cell)

  -- Construct the finset explicitly as a biUnion of images
  let S_total : Finset EuclideanPlane :=
    a9.Q0.attach.biUnion fun Q' =>
      let sq := a9.perSquare Q'.val Q'.property
      sq.P_norm_Q.biUnion fun p =>
        Finset.image f_cell (sq.fineTubes_norm p)

  -- S_total as a set equals allFineParamsEuclidean a9
  have hS_eq : (S_total : Set EuclideanPlane) = allFineParamsEuclidean a9 := by
    ext x
    simp only [S_total, Finset.mem_coe, Finset.mem_biUnion, allFineParamsEuclidean,
      Set.mem_iUnion, Finset.mem_image, Subtype.exists]
    <;> aesop

  -- S_total is finite
  have hS_finite : (allFineParamsEuclidean a9).Finite := by
    rw [← hS_eq]
    exact S_total.finite_toSet

  refine ⟨hS_finite, ?_⟩

  -- The toFinset of allFineParams equals S_total
  have h_toFinset_eq : hS_finite.toFinset = S_total := by
    apply Finset.ext
    intro x
    have h1 : x ∈ hS_finite.toFinset ↔ x ∈ allFineParamsEuclidean a9 := by
      simp [hS_finite]
    have h2 : x ∈ S_total ↔ x ∈ (S_total : Set EuclideanPlane) := Iff.rfl
    rw [h1, h2, hS_eq]

  -- Cardinal bound: |S_total| ≤ sum
  have h_card : S_total.card ≤
      ∑ Q' ∈ a9.Q0.attach,
        ∑ p ∈ (a9.perSquare Q'.val Q'.property).P_norm_Q,
          ((a9.perSquare Q'.val Q'.property).fineTubes_norm p).card := by
    calc S_total.card
      ≤ ∑ Q' ∈ a9.Q0.attach,
          ((a9.perSquare Q'.val Q'.property).P_norm_Q.biUnion fun p =>
            Finset.image f_cell ((a9.perSquare Q'.val Q'.property).fineTubes_norm p)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ Q' ∈ a9.Q0.attach,
          ∑ p ∈ (a9.perSquare Q'.val Q'.property).P_norm_Q,
            (Finset.image f_cell ((a9.perSquare Q'.val Q'.property).fineTubes_norm p)).card := by
        apply Finset.sum_le_sum
        intro Q' _
        exact Finset.card_biUnion_le
    _ ≤ ∑ Q' ∈ a9.Q0.attach,
          ∑ p ∈ (a9.perSquare Q'.val Q'.property).P_norm_Q,
            ((a9.perSquare Q'.val Q'.property).fineTubes_norm p).card := by
        apply Finset.sum_le_sum
        intro Q' _
        apply Finset.sum_le_sum
        intro p _
        have h_img : (Finset.image f_cell ((a9.perSquare Q'.val Q'.property).fineTubes_norm p)).card ≤
            ((a9.perSquare Q'.val Q'.property).fineTubes_norm p).card :=
          Finset.card_image_le
        exact h_img

  rw [h_toFinset_eq]
  exact h_card

/-- Cardinal of allFineParamsEuclidean ≤ |allCells| ≤ 2·Δ^{-2s-214ε}.

    Uses the new h_allCells_card_upper field of A9_Output, which is proved
    via A5 incidence counting (hG4_upper + hN_upper). -/
lemma allFineParams_card_upper {Δ δ s t ε : ℝ} (a9 : A9_Output Δ δ s t ε) :
    ∃ (hfin : (allFineParamsEuclidean a9).Finite),
      (hfin.toFinset.card : ℝ) ≤ 2 * Real.rpow Δ (-(2 * s + 214 * ε)) := by
  let f_cell : DyadicTubeCell δ → EuclideanPlane :=
    fun cell => A10.toPlane' (paramsOfDyadicCell δ cell)
  let allCells : Finset (DyadicTubeCell δ) :=
    a9.Q0.attach.biUnion fun Q' =>
      let sq := a9.perSquare Q'.val Q'.property
      sq.P_norm_Q.biUnion fun p => sq.fineTubes_norm p
  let S_total : Finset EuclideanPlane := allCells.image f_cell

  have hS_eq : (S_total : Set EuclideanPlane) = allFineParamsEuclidean a9 := by
    ext x
    simp only [S_total, allCells, Finset.mem_coe, Finset.mem_image, Finset.mem_biUnion,
      allFineParamsEuclidean, Set.mem_iUnion, Subtype.exists]
    <;> aesop

  have hS_finite : (allFineParamsEuclidean a9).Finite := by
    rw [← hS_eq]; exact S_total.finite_toSet

  have h_toFinset_eq : hS_finite.toFinset = S_total := by
    apply Finset.ext; intro x
    have h1 : x ∈ hS_finite.toFinset ↔ x ∈ allFineParamsEuclidean a9 := by simp [hS_finite]
    have h2 : x ∈ S_total ↔ x ∈ (S_total : Set EuclideanPlane) := Iff.rfl
    rw [h1, h2, hS_eq]

  have h_card1 : (S_total.card : ℝ) ≤ (allCells.card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have h_card2 : (allCells.card : ℝ) ≤ 2 * Real.rpow Δ (-(2 * s + 214 * ε)) := by
    exact_mod_cast a9.h_allCells_card_upper

  refine ⟨hS_finite, ?_⟩
  rw [h_toFinset_eq]
  exact le_trans h_card1 h_card2

/-- Derive h_allFine_upper from h_allCells_card_upper.

    Uses k = 214ε, C = 2. Requires η_upper > 214ε and Δ small enough
    to absorb 4000 = 2000·2. -/
lemma allFineUpper_from_cells {Δ δ s t ε η_upper : ℝ}
    (a9 : A9_Output Δ δ s t ε)
    (hε_pos : 0 < ε)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_214ε : 214 * ε < η_upper)
    (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hΔ_small : (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε))) :
    (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal
        (allFineParamsEuclidean a9) <
      ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) := by
  rcases allFineParams_card_upper a9 with ⟨hfin, h_card⟩
  exact allFineUpper_general (k := 214 * ε) (C := 2) a9
    (hε_pos := hε_pos)
    (hη_upper_pos := hη_upper_pos)
    (hk_pos := by positivity)
    (hη_upper_gt_k := hη_upper_gt_214ε)
    (hδ_eq := hδ_eq)
    (hΔ_pos := hΔ_pos)
    (hΔ_lt_one := hΔ_lt_one)
    (hfin := hfin)
    (h_card_bound := h_card)
    (hC_nonneg := by positivity)
    (hΔ_small := hΔ_small)

end DirecretisedFurstenbergEstimate.AppendixA
