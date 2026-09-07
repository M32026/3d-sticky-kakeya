module

/-
  Fine Branch Transfer for Theorem 6.1 — cross-type via cardinality.

  Chain (explicit dyadic → affine crossing):
    Appendix fine lower bound (at 9δ_n on affine image)
      ≤ Ncover(9δ_n, f '' retainedDyadic)         [hypothesis]
      ≤ encard(f '' retainedDyadic)                [cover-by-self, same AffineLine type]
      ≤ card(retainedDyadic)                       [finite image cardinality ≤ domain]
      ≤ δ_n^{-ρ_T} * Ncover(δ, originalAffine)     [h_card_bound]
    Multiply by δ_n^{ρ_T}, absorb constants, compare exponents.

  The cross-type step is purely finite image cardinality; no Ncover
  monotonicity across metric spaces is used.

  Whiteprint node: theorem61 / fine_branch_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.SourceFacingTheorem61

open DiscretisedFurstenbergEstimate
open RegularIncidence

/-- Fine branch: transfer Appendix A fine bound to original affine covering.

    The fine bound lives on the affine image `f '' retainedDyadic` at scale `9δ_n`.
    We cross from dyadic tubes to affine lines via finite image cardinality:
    `encard(f '' S) ≤ card(S)`. No packing or cross-type Ncover monotonicity is used.

    Instantiate `f` with `toAffineLine` (or `wideToAffineLine`) as appropriate. -/
lemma fine_branch_transfer
    {n : ℕ} {δ δ_n : ℝ}
    (hδn_pos : 0 < δ_n) (hδn_one : δ_n ≤ 1)
    (hδ_pos : 0 < δ) (hδn_leδ : δ_n ≤ δ)
    {s : ℝ} (hs_pos : 0 < s)
    {εA εInc ρ_T : ℝ}
    (hεA_pos : 0 < εA) (hεInc_pos : 0 < εInc)
    (hρ_T_nonneg : 0 ≤ ρ_T)
    {originalTubes : Set AffineLine}
    -- Finite dyadic tube family and its affine embedding
    (retainedDyadic : Finset (DyadicTube n))
    (f : DyadicTube n → AffineLine)
    -- Appendix A fine bound at 9δ_n on the affine image
    (h_fine_bound :
      ENNReal.ofReal ((9 * δ_n) ^ (-(2 * s + εA))) ≤
      Ncover (9 * δ_n) (f '' (retainedDyadic : Set (DyadicTube n))))
    -- Cardinality bound: card(retainedDyadic) ≤ δ_n^{-ρ_T} * Ncover(δ, original)
    (h_card_bound : (retainedDyadic.card : ENNReal) ≤
        ENNReal.ofReal (δ_n ^ (-ρ_T)) * Ncover δ originalTubes)
    -- Loss budget
    (loss_fine : ℝ) (hloss_fine_nonneg : 0 ≤ loss_fine)
    (h_budget : εInc ≤ εA - ρ_T - loss_fine)
    -- Scale-smallness to absorb 9^{-(2s+εA)}
    (h_scale_small : δ_n ^ (-loss_fine) ≥ (9 : ℝ)^(2 * s + εA)) :
    ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤
      Ncover δ originalTubes := by
  set N : ENNReal := Ncover δ originalTubes with hN_def
  set δ9 : ℝ := 9 * δ_n with hδ9_def
  set affineImage : Set AffineLine := f '' (retainedDyadic : Set (DyadicTube n)) with hImg_def
  have hδ9_pos : 0 < δ9 := by positivity

  -- Step 1: Cover-by-self at 9δ_n (same AffineLine type, no monotonicity)
  have h_cover_le_card : Ncover δ9 affineImage ≤ (affineImage.encard : ENNReal) := by
    have h' : Metric.externalCoveringNumber δ9.toNNReal affineImage ≤ affineImage.encard :=
      Metric.externalCoveringNumber_le_encard_self affineImage
    have h4 : Ncover δ9 affineImage = ↑(Metric.externalCoveringNumber δ9.toNNReal affineImage) := by rfl
    rw [h4]
    have h5 : (↑(Metric.externalCoveringNumber δ9.toNNReal affineImage) : ENNReal) ≤ (affineImage.encard : ENNReal) := by
      exact ENat.toENNReal_le.mpr h'
    exact h5

  -- Step 2: Finite image cardinality ≤ domain cardinality
  have h_image_fin : affineImage.Finite := by
    exact Set.Finite.image f (Finset.finite_toSet retainedDyadic)
  have h_image_card : (affineImage.encard : ENNReal) ≤ (retainedDyadic.card : ENNReal) := by
    have h1 : affineImage.encard ≤ (retainedDyadic.card : ENat) := by
      simpa [hImg_def] using Set.encard_image_le f (retainedDyadic : Set (DyadicTube n))
    exact_mod_cast h1

  -- Step 3: Chain → card(retainedDyadic) ≥ fine_bound
  have h_card_lower : (retainedDyadic.card : ENNReal) ≥
      ENNReal.ofReal (δ9 ^ (-(2 * s + εA))) := by
    calc (retainedDyadic.card : ENNReal)
      ≥ (affineImage.encard : ENNReal) := h_image_card
    _ ≥ Ncover δ9 affineImage := h_cover_le_card
    _ ≥ ENNReal.ofReal (δ9 ^ (-(2 * s + εA))) := h_fine_bound

  -- Step 4: h_card_bound → N ≥ card * δ_n^{ρ_T}
  have h_mult : ENNReal.ofReal (δ_n ^ ρ_T) * (retainedDyadic.card : ENNReal) ≤ N := by
    have h1 : ENNReal.ofReal (δ_n ^ ρ_T) * (retainedDyadic.card : ENNReal) ≤
        ENNReal.ofReal (δ_n ^ ρ_T) * (ENNReal.ofReal (δ_n ^ (-ρ_T)) * N) := by
      gcongr <;> exact h_card_bound
    have h2 : ENNReal.ofReal (δ_n ^ ρ_T) * (ENNReal.ofReal (δ_n ^ (-ρ_T)) * N) = N := by
      have h3 : ENNReal.ofReal (δ_n ^ ρ_T) * ENNReal.ofReal (δ_n ^ (-ρ_T)) = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have h4 : δ_n ^ ρ_T * δ_n ^ (-ρ_T) = 1 := by
          have h5 : δ_n ^ ρ_T * δ_n ^ (-ρ_T) = δ_n ^ (ρ_T + (-ρ_T)) := by
            rw [← Real.rpow_add hδn_pos]
          rw [h5]
          have h6 : ρ_T + (-ρ_T) = 0 := by ring
          rw [h6, Real.rpow_zero]
        rw [h4] <;> simp
      rw [← mul_assoc, h3, one_mul]
    rw [h2] at h1
    exact h1

  -- Step 5: Combine → N ≥ ofReal(9^{-(2s+εA)} * δ_n^{ρ_T-(2s+εA)})
  have h5 : ENNReal.ofReal (δ_n ^ ρ_T) * ENNReal.ofReal (δ9 ^ (-(2 * s + εA))) =
      ENNReal.ofReal (δ_n ^ ρ_T * δ9 ^ (-(2 * s + εA))) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
  have h6 : N ≥ ENNReal.ofReal (δ_n ^ ρ_T * δ9 ^ (-(2 * s + εA))) := by
    calc N
      ≥ ENNReal.ofReal (δ_n ^ ρ_T) * (retainedDyadic.card : ENNReal) := h_mult
    _ ≥ ENNReal.ofReal (δ_n ^ ρ_T) * ENNReal.ofReal (δ9 ^ (-(2 * s + εA))) := by gcongr
    _ = ENNReal.ofReal (δ_n ^ ρ_T * δ9 ^ (-(2 * s + εA))) := h5

  -- Simplify: δ_n^{ρ_T} * (9δ_n)^{-(2s+εA)} = 9^{-(2s+εA)} * δ_n^{ρ_T-(2s+εA)}
  have h7 : δ_n ^ ρ_T * δ9 ^ (-(2 * s + εA)) =
      (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (ρ_T - (2 * s + εA)) := by
    simp only [hδ9_def]
    have h8 : (9 * δ_n) ^ (-(2 * s + εA)) =
        (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-(2 * s + εA)) := by
      rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
    rw [h8]
    have h91 : δ_n ^ ρ_T * ((9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-(2 * s + εA))) =
        (9 : ℝ)^(-(2 * s + εA)) * (δ_n ^ ρ_T * δ_n ^ (-(2 * s + εA))) := by ring
    rw [h91]
    have h92 : δ_n ^ ρ_T * δ_n ^ (-(2 * s + εA)) =
        δ_n ^ (ρ_T + (-(2 * s + εA))) := by
      rw [← Real.rpow_add hδn_pos]
    rw [h92]
    have h93 : ρ_T + (-(2 * s + εA)) = ρ_T - (2 * s + εA) := by ring
    rw [h93]
  rw [h7] at h6

  -- Step 6: Real exponent comparison
  -- 6a: ρ_T - (2s+εA) ≤ -(2s+εInc) - loss_fine
  have h_exp_le : ρ_T - (2 * s + εA) ≤ -(2 * s + εInc) - loss_fine := by linarith

  -- 6b: Since δ_n ≤ 1, smaller exponent → larger rpow
  have h_rpow1 : δ_n ^ (ρ_T - (2 * s + εA)) ≥ δ_n ^ (-(2 * s + εInc) - loss_fine) :=
    Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_one h_exp_le

  -- 6c: Multiply by 9^{-(2s+εA)}
  have h_prod1 : (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (ρ_T - (2 * s + εA)) ≥
      (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-(2 * s + εInc) - loss_fine) := by
    gcongr

  -- 6d: Split exponent
  have h_split : δ_n ^ (-(2 * s + εInc) - loss_fine) =
      δ_n ^ (-(2 * s + εInc)) * δ_n ^ (-loss_fine) := by
    have h : -(2 * s + εInc) - loss_fine = (-(2 * s + εInc)) + (-loss_fine) := by ring
    rw [h, ← Real.rpow_add hδn_pos]

  -- 6e: 9^{-(2s+εA)} * δ_n^{-loss_fine} ≥ 1
  have h_scale_absorb : (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-loss_fine) ≥ 1 := by
    have h1 : (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-loss_fine) ≥
        (9 : ℝ)^(-(2 * s + εA)) * (9 : ℝ)^(2 * s + εA) := by
      gcongr <;> exact h_scale_small
    have h2 : (9 : ℝ)^(-(2 * s + εA)) * (9 : ℝ)^(2 * s + εA) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 9)]
      rw [show (-(2 * s + εA)) + (2 * s + εA) = 0 by ring, Real.rpow_zero]
    rw [h2] at h1
    exact h1

  -- 6f: Combine → product ≥ δ_n^{-(2s+εInc)}
  have h_final : (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (ρ_T - (2 * s + εA)) ≥
      δ_n ^ (-(2 * s + εInc)) := by
    calc (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (ρ_T - (2 * s + εA))
      ≥ (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-(2 * s + εInc) - loss_fine) := h_prod1
    _ = (9 : ℝ)^(-(2 * s + εA)) * (δ_n ^ (-(2 * s + εInc)) * δ_n ^ (-loss_fine)) := by rw [h_split]
    _ = δ_n ^ (-(2 * s + εInc)) * ((9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (-loss_fine)) := by ring
    _ ≥ δ_n ^ (-(2 * s + εInc)) * 1 := by gcongr
    _ = δ_n ^ (-(2 * s + εInc)) := by ring

  -- 6g: δ_n^{-(2s+εInc)} ≥ δ^{-(2s+εInc)} since δ_n ≤ δ and exponent negative
  have h_pos_exp : 0 < 2 * s + εInc := by positivity
  have h_δ_compare : δ_n ^ (-(2 * s + εInc)) ≥ δ ^ (-(2 * s + εInc)) := by
    have h1 : δ_n ^ (2 * s + εInc) ≤ δ ^ (2 * s + εInc) :=
      Real.rpow_le_rpow hδn_pos.le hδn_leδ h_pos_exp.le
    have h2 : 0 < δ_n ^ (2 * s + εInc) := Real.rpow_pos_of_pos hδn_pos _
    have h3 : δ_n ^ (-(2 * s + εInc)) = 1 / δ_n ^ (2 * s + εInc) := by
      rw [Real.rpow_neg hδn_pos.le] <;> ring
    have h4 : δ ^ (-(2 * s + εInc)) = 1 / δ ^ (2 * s + εInc) := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h3, h4]
    exact one_div_le_one_div_of_le h2 h1

  have h_goal : (9 : ℝ)^(-(2 * s + εA)) * δ_n ^ (ρ_T - (2 * s + εA)) ≥
      δ ^ (-(2 * s + εInc)) :=
    le_trans h_δ_compare h_final

  exact le_trans (ENNReal.ofReal_le_ofReal h_goal) h6

end DirecretisedFurstenbergEstimate.SourceFacingTheorem61

end
