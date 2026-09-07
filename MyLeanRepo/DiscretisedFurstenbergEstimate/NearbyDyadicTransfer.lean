module

/-
  Nearby-dyadic scale transfer for the discretised Furstenberg estimate.

  Provides input S-set transfer and output covering transfer between
  an arbitrary real scale δ and a nearby dyadic scale δ_d.

  ## Two transfer directions

  ### Coarser dyadic (δ < δ_d ≤ 2δ) — RECOMMENDED
  - Input: (δ,s,C)-set → (δ_d,s,C·K)-set (easy, no hard S-set transfer)
  - Output: Ncover(δ_d,T) ≥ δ_d^{-(2s+ε)} ⟹ Ncover(δ,T) ≥ δ^{-(2s+ε/2)}
  - Full package: `full_nearby_dyadic_transfer`

  ### Finer dyadic (δ_d ≤ δ < 2δ_d)
  - Output: Ncover(δ_d,T) ≥ δ_d^{-(2s+ε)} ⟹ Ncover(δ,T) ≥ δ^{-(2s+ε/2)}
  - Requires doubling for the output lower bound transfer
  - Lemma: `nearby_dyadic_transfer_conclusion`

  ## Key lemmas

  - `covering_doubling_of_packing`: general metric space
  - `affineLine_covering_doubling`: K = affineLine_packing_constant
  - `plane_covering_doubling`: K = 9 for EuclideanPlane
  - `sset_transfer_coarser`: input S-set transfer to coarser scale
  - `choose_coarser_dyadic_scale`: finds δ < dyadicDelta n ≤ 2δ
  - `output_transfer_coarser`: output bound transfer from coarser dyadic
  - `full_nearby_dyadic_transfer`: complete package

  Whiteprint node: section9 / nearby_dyadic
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.NearbyDyadicTransfer

open DirecretisedFurstenbergEstimate

/-! ============================================================================
   Part 1: General covering doubling from packing bound
   ============================================================================ -/

/-- If every r-separated subset of a 2r-ball has cardinality at most K,
    then the r-covering number is at most K times the 2r-covering number. -/
lemma covering_doubling_of_packing
    {X : Type*} [MetricSpace X] {r : ℝ} (hr_pos : 0 < r)
    (K : ℕ) (hK_pos : 0 < K)
    (hK : ∀ (z : X) (S : Set X),
      Set.Pairwise S (fun x y => r ≤ dist x y) →
      S ⊆ Metric.closedBall z (2 * r) →
      S.Finite ∧ S.encard ≤ (K : ENat)) :
    ∀ (A : Set X),
      Metric.externalCoveringNumber r.toNNReal A ≤
        (K : ENNReal) * Metric.externalCoveringNumber (2 * r).toNNReal A := by
  have hK_ne_zero : (K : ENNReal) ≠ 0 := by exact_mod_cast hK_pos.ne'
  intro A
  by_cases h_top : Metric.externalCoveringNumber (2 * r).toNNReal A = ⊤
  · -- If 2r-covering number is infinite and K > 0, RHS is infinite
    have h : (K : ENNReal) * Metric.externalCoveringNumber (2 * r).toNNReal A = ⊤ := by
      rw [h_top]
      exact ENNReal.mul_top hK_ne_zero
    rw [h]
    exact le_top
  · -- Ncover(2r, A) ≠ ⊤
    have hN_lt_top : Metric.externalCoveringNumber (2 * r).toNNReal A < ⊤ := by
      exact Ne.lt_top' fun a => h_top (id (Eq.symm a))
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq hN_lt_top
      with ⟨D, hD_cover, hD_eq⟩
    have hD_fin : D.Finite := by
      have h : D.encard < ⊤ := by rw [hD_eq]; exact hN_lt_top
      exact Set.encard_lt_top_iff.mp h
    let D' : Finset X := hD_fin.toFinset
    have hD'_eq : (D' : Set X) = D := hD_fin.coe_toFinset
    have hr_nonneg : 0 ≤ r := by linarith
    have h2r_nonneg : 0 ≤ 2 * r := by linarith

    -- Helper: convert IsSeparated to Pairwise (r ≤ dist)
    have h_sep_convert : ∀ (S : Set X), Metric.IsSeparated r.toNNReal S →
        Set.Pairwise S (fun x y => r ≤ dist x y) := by
      intro S hS
      intro x hx y hy hxy
      have h : (r.toNNReal : ℝ≥0∞) < edist x y := hS hx hy hxy
      have h' : r < dist x y := by
        have h9 : (r.toNNReal : ℝ≥0∞) = ENNReal.ofReal r := by
          exact ENNReal.ofNNReal_toNNReal r
        rw [h9] at h
        have h10 : ENNReal.ofReal r < ENNReal.ofReal (dist x y) := by
          simpa [edist_dist] using h
        have h11 : r < dist x y := by
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nonneg).mp h10
        exact h11
      linarith

    -- For each d ∈ D', get a maximal r-separated subset that covers B_d
    have h_each : ∀ (d : X), d ∈ D' → ∃ (S_d : Finset X),
        (S_d : Set X) ⊆ A ∩ Metric.closedBall d (2 * r) ∧
        Metric.IsCover r.toNNReal (A ∩ Metric.closedBall d (2 * r)) (S_d : Set X) ∧
        S_d.card ≤ K := by
      intro d _
      let B_d := A ∩ Metric.closedBall d (2 * r)
      -- Bound packingNumber(r, B_d) ≤ K
      have h_pack_le : Metric.packingNumber r.toNNReal B_d ≤ (K : ENat) := by
        have h_all : ∀ (S : Set X), S ⊆ B_d →
            Metric.IsSeparated r.toNNReal S → S.encard ≤ (K : ENat) := by
          intro S hS_sub hS_sep
          have hS_sep' := h_sep_convert S hS_sep
          have hS_sub2 : S ⊆ Metric.closedBall d (2 * r) := by
            intro x hx; exact (hS_sub hx).2
          exact (hK d S hS_sep' hS_sub2).2
        simpa [Metric.packingNumber] using iSup_le fun C => iSup_le fun hC_sub =>
          iSup_le fun hC_sep => h_all C hC_sub hC_sep
      have h_pack_ne_top : Metric.packingNumber r.toNNReal B_d ≠ ⊤ := by
        have h : (K : ENat) < ⊤ := by simp
        exact ne_top_of_le_ne_top h.ne h_pack_le
      let S_d_set := Metric.maximalSeparatedSet r.toNNReal B_d
      have hS_sub : S_d_set ⊆ B_d := Metric.maximalSeparatedSet_subset
      have hS_cover : Metric.IsCover r.toNNReal B_d S_d_set :=
        Metric.isCover_maximalSeparatedSet h_pack_ne_top
      have hS_encard : S_d_set.encard = Metric.packingNumber r.toNNReal B_d :=
        Metric.encard_maximalSeparatedSet h_pack_ne_top
      have hS_fin : S_d_set.Finite := by
        have h : S_d_set.encard ≤ (K : ENat) := by
          rw [hS_encard]; exact h_pack_le
        exact Set.encard_lt_top_iff.mp (lt_of_le_of_lt h (by simp))
      let S_d : Finset X := hS_fin.toFinset
      have hS_d_eq : (S_d : Set X) = S_d_set := hS_fin.coe_toFinset
      have h_card : S_d.card ≤ K := by
        have h : (S_d : Set X).encard ≤ (K : ENat) := by
          rw [hS_d_eq, hS_encard]; exact h_pack_le
        exact_mod_cast h
      exact ⟨S_d, by rw [hS_d_eq] <;> exact hS_sub,
        by rw [hS_d_eq] <;> exact hS_cover, h_card⟩

    choose S_d hS_sub hS_cover hS_card using h_each
    -- S_d : (d : X) → d ∈ D' → Finset X

    -- Curry to X → Finset X
    let S_d' (d : X) : Finset X :=
      if h : d ∈ D' then S_d d h else ∅

    let D_all : Finset X := D'.biUnion S_d'

    -- D_all is an r-cover of A
    have hD_all_cover : Metric.IsCover r.toNNReal A (D_all : Set X) := by
      intro a ha
      have h1 : ∃ (d : X), d ∈ D ∧ edist a d ≤ ↑(2 * r).toNNReal := hD_cover ha
      rcases h1 with ⟨d, hd, hed⟩
      have hd' : d ∈ (D' : Set X) := by rw [hD'_eq] <;> exact hd
      have hdist : dist a d ≤ 2 * r := by
        have h4 : ENNReal.ofReal (dist a d) ≤ ENNReal.ofReal (2 * r) := by
          have h5 : edist a d = ENNReal.ofReal (dist a d) := edist_dist a d
          rw [h5] at hed
          exact hed
        exact (edist_le_ofReal h2r_nonneg).mp hed

      have h_a_in_Bd : a ∈ A ∩ Metric.closedBall d (2 * r) := ⟨ha, hdist⟩
      have hSd_eq : S_d' d = S_d d hd' := by
        unfold S_d'
        have h : d ∈ D' := hd'
        rw [dif_pos h]
      have h5 : ∃ (y : X), y ∈ (S_d d hd' : Set X) ∧ edist a y ≤ ↑r.toNNReal :=
        hS_cover d hd' h_a_in_Bd
      rcases h5 with ⟨y, hy, hball⟩
      have h_yin_Dall : y ∈ (D_all : Set X) := by
        exact Finset.mem_biUnion.mpr ⟨d, hd', by rw [hSd_eq] <;> exact hy⟩
      exact ⟨y, h_yin_Dall, hball⟩

    -- Bound cardinality
    have hD_all_card : D_all.card ≤ K * D'.card := by
      calc D_all.card
        ≤ ∑ d ∈ D', (S_d' d).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ D', K := by
        apply Finset.sum_le_sum
        intro d hd
        have h : S_d' d = S_d d hd := by simp [S_d', hd]
        rw [h]
        exact hS_card d hd
      _ = K * D'.card := by simp [Finset.sum_const, mul_comm]

    have h1 : Metric.externalCoveringNumber r.toNNReal A ≤
        (D_all.card : ENNReal) := by
      exact_mod_cast Metric.IsCover.externalCoveringNumber_le_encard hD_all_cover
    have h2 : (D_all.card : ENNReal) ≤ ((K * D'.card : ℕ) : ENNReal) := by
      exact_mod_cast hD_all_card
    have h3 : ((K * D'.card : ℕ) : ENNReal) =
        (K : ENNReal) * (D'.card : ENNReal) := by
      simp [Nat.cast_mul] <;> ring
    have h4 : (D'.card : ENNReal) = D.encard := by
      simp [← hD'_eq] <;> rfl
    have h5 : D.encard = Metric.externalCoveringNumber (2 * r).toNNReal A := hD_eq
    exact le_trans h1 (le_trans h2 (by rw [h3, h4, h5]))

/-! ============================================================================
     Part 2: Covering doubling for AffineLine
     ============================================================================ -/

/-- Covering number doubling for AffineLine:
      `Ncover(r, A) ≤ affineLine_packing_constant * Ncover(2r, A)`. -/
lemma affineLine_covering_doubling {r : ℝ} (hr_pos : 0 < r)
      (A : Set AffineLine) :
    Metric.externalCoveringNumber r.toNNReal A ≤
      (MainAppendix.affineLine_packing_constant : ENNReal) *
        Metric.externalCoveringNumber (2 * r).toNNReal A := by
  let hK' : ∀ (z : AffineLine) (S : Set AffineLine),
      Set.Pairwise S (fun x y => r ≤ dist x y) →
      S ⊆ Metric.closedBall z (2 * r) →
      S.Finite ∧ S.encard ≤ (MainAppendix.affineLine_packing_constant : ENat) :=
    fun z S h_sep h_sub =>
      MainAppendix.affineLine_packing_bound r hr_pos h_sep z h_sub
  exact covering_doubling_of_packing hr_pos
    MainAppendix.affineLine_packing_constant
    MainAppendix.affineLine_packing_constant_pos
    hK' A

/-! ============================================================================
   Part 3: Nearby-dyadic conclusion transfer
   ============================================================================ -/

/-- Transfer a covering lower bound from a nearby dyadic scale to the original scale.

    Given:
    - δ > 0, s > 0, ε > 0
    - δ_d is dyadic with δ_d ≤ δ < 2δ_d
    - `Ncover(δ_d, T) ≥ δ_d^{-(2s+ε)}`

    Then for sufficiently small δ:
    - `Ncover(δ, T) ≥ δ^{-(2s+ε/2)}`

    The constant factor from doubling is absorbed by halving ε.
-/
lemma nearby_dyadic_transfer_conclusion
    (δ s ε : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hε_pos : 0 < ε)
    (δ_d : ℝ) (hδ_d_dyadic : ∃ n : ℕ, δ_d = dyadicDelta n)
    (hδ_d_le : δ_d ≤ δ) (hδ_lt_2δ_d : δ < 2 * δ_d)
    (T : Set AffineLine)
    (h_bound : Metric.externalCoveringNumber δ_d.toNNReal T ≥
        ENNReal.ofReal (Real.rpow δ_d (-(2 * s + ε))))
    (h_small : δ ≤ (MainAppendix.affineLine_packing_constant : ℝ) ^ (-(2 / ε))) :
    Metric.externalCoveringNumber δ.toNNReal T ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε / 2))) := by
  set K : ℕ := MainAppendix.affineLine_packing_constant with hK_def
  have hK_pos : 0 < K := MainAppendix.affineLine_packing_constant_pos
  have hK_one : 1 ≤ (K : ℝ) := by exact_mod_cast hK_pos
  have hδ_d_pos : 0 < δ_d := by
    rcases hδ_d_dyadic with ⟨n, rfl⟩
    exact dyadicDelta_pos n
  have h_half_pos : 0 < δ / 2 := by linarith
  have hK_ne_zero : (K : ENNReal) ≠ 0 := by exact_mod_cast hK_pos.ne'

  -- Step 1: Ncover(δ_d, T) ≤ Ncover(δ/2, T) since δ/2 < δ_d
  have h_toNNReal_le : (δ / 2).toNNReal ≤ δ_d.toNNReal := by
    have h3 : δ / 2 ≤ δ_d := by linarith
    have h_nonneg1 : 0 ≤ δ / 2 := by linarith
    have h_nonneg2 : 0 ≤ δ_d := by linarith
    have h4 : ((δ / 2).toNNReal : ℝ) = δ / 2 := by simp [h_nonneg1]
    have h5 : (δ_d.toNNReal : ℝ) = δ_d := by simp [h_nonneg2]
    have h6 : ((δ / 2).toNNReal : ℝ) ≤ (δ_d.toNNReal : ℝ) := by
      rw [h4, h5] <;> linarith
    exact NNReal.coe_le_coe.mp h6
  have h1 : (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≤
      (Metric.externalCoveringNumber (δ / 2).toNNReal T : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_anti h_toNNReal_le

  -- Step 2: Ncover(δ/2, T) ≤ K * Ncover(δ, T) by doubling
  have h21 : (2 * (δ / 2)).toNNReal = δ.toNNReal := by
    apply NNReal.coe_injective
    have h : 2 * (δ / 2) = δ := by ring
    rw [h]
  have h2 : (Metric.externalCoveringNumber (δ / 2).toNNReal T : ENNReal) ≤
      (K : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
    have h := affineLine_covering_doubling h_half_pos T
    rw [h21] at h
    exact_mod_cast h

  -- Step 3: Ncover(δ, T) ≥ (1/K) * Ncover(δ_d, T)
  have h4 : (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≤
      (K : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) :=
    le_trans h1 h2
  have h3 : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≥
      (1 : ENNReal) / (K : ENNReal) *
        (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) := by
    have h5 : (1 : ENNReal) / (K : ENNReal) *
        (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≤
      (1 : ENNReal) / (K : ENNReal) *
        ((K : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal)) := by gcongr
    have h6 : (1 : ENNReal) / (K : ENNReal) *
        ((K : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal)) =
        (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
      have h7 : (K : ENNReal)⁻¹ * (K : ENNReal) = 1 :=
        ENNReal.inv_mul_cancel (by exact_mod_cast hK_pos.ne') (by simp)
      have hdiv : (1 : ENNReal) / (K : ENNReal) = (K : ENNReal)⁻¹ := by
        simp [one_div]
      rw [hdiv]
      rw [← mul_assoc, h7, one_mul]
    rw [h6] at h5
    exact h5

  -- Step 4: δ_d^{-(2s+ε)} ≥ δ^{-(2s+ε)} (since δ_d ≤ δ, exponent negative)
  have h7 : Real.rpow δ (-(2 * s + ε)) ≤ Real.rpow δ_d (-(2 * s + ε)) := by
    have h_exp_neg : -(2 * s + ε) < 0 := by linarith
    have h_iff : Real.rpow δ (-(2 * s + ε)) ≤ Real.rpow δ_d (-(2 * s + ε)) ↔ δ_d ≤ δ :=
      Real.rpow_le_rpow_iff_of_neg hδ_pos hδ_d_pos h_exp_neg
    exact h_iff.mpr hδ_d_le
  have h9 : (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) :=
    le_trans (ENNReal.ofReal_le_ofReal h7) (by exact_mod_cast h_bound)

  -- Step 5: Ncover(δ, T) ≥ (1/K) * δ^{-(2s+ε)}
  have h10 : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≥
      (1 : ENNReal) / (K : ENNReal) *
        ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by
    calc (Metric.externalCoveringNumber δ.toNNReal T : ENNReal)
      ≥ (1 : ENNReal) / (K : ENNReal) *
          (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) := h3
    _ ≥ (1 : ENNReal) / (K : ENNReal) *
          ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by gcongr

  -- Step 6: (1/K) * δ^{-(2s+ε)} ≥ δ^{-(2s+ε/2)}
  -- Equivalent to δ^{-ε/2} ≥ K, which follows from δ ≤ K^{-2/ε}
  have hK_real_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have h_exp_half_neg : -(ε / 2) ≤ 0 := by linarith
  have h12 : Real.rpow δ (-(ε / 2)) ≥ (K : ℝ) := by
    -- From δ ≤ K^{-2/ε}, raising to nonpositive power flips inequality
    have hK_rpow_pos : 0 < Real.rpow (K : ℝ) (-(2 / ε)) := Real.rpow_pos_of_pos hK_real_pos _
    have h_a : Real.rpow (Real.rpow (K : ℝ) (-(2 / ε))) (-(ε / 2)) ≤ Real.rpow δ (-(ε / 2)) :=
      Real.rpow_le_rpow_of_nonpos hδ_pos h_small h_exp_half_neg
    have h_b : Real.rpow (Real.rpow (K : ℝ) (-(2 / ε))) (-(ε / 2)) =
        Real.rpow (K : ℝ) ((-(2 / ε)) * (-(ε / 2))) := by
      exact Eq.symm (Real.rpow_mul (by positivity) _ _)
    have h_c : (-(2 / ε)) * (-(ε / 2)) = 1 := by
      field_simp [hε_pos.ne'] <;> ring
    rw [h_b, h_c] at h_a
    simpa using h_a
  have h13 : Real.rpow δ (-(2 * s + ε)) =
      Real.rpow δ (-(2 * s + ε / 2)) * Real.rpow δ (-(ε / 2)) := by
    have h_sum : -(2 * s + ε) = -(2 * s + ε / 2) + (-(ε / 2)) := by ring
    rw [h_sum]
    exact Real.rpow_add hδ_pos _ _
  have h14 : (1 : ℝ) / (K : ℝ) * Real.rpow δ (-(2 * s + ε)) ≥
      Real.rpow δ (-(2 * s + ε / 2)) := by
    rw [h13]
    have h15 : 0 < Real.rpow δ (-(2 * s + ε / 2)) := Real.rpow_pos_of_pos hδ_pos _
    have h16 : (1 : ℝ) / (K : ℝ) * Real.rpow δ (-(ε / 2)) ≥ 1 := by
      have h17 : (1 : ℝ) / (K : ℝ) * Real.rpow δ (-(ε / 2)) ≥ (1 : ℝ) / (K : ℝ) * (K : ℝ) := by
        gcongr <;> linarith
      have h18 : (1 : ℝ) / (K : ℝ) * (K : ℝ) = 1 := by
        field_simp [hK_real_pos.ne'] <;> ring
      linarith
    have h19 : (1 : ℝ) / (K : ℝ) *
        (Real.rpow δ (-(2 * s + ε / 2)) * Real.rpow δ (-(ε / 2))) =
        Real.rpow δ (-(2 * s + ε / 2)) *
          ((1 : ℝ) / (K : ℝ) * Real.rpow δ (-(ε / 2))) := by ring
    rw [h19]
    have h20 : Real.rpow δ (-(2 * s + ε / 2)) *
        ((1 : ℝ) / (K : ℝ) * Real.rpow δ (-(ε / 2))) ≥
        Real.rpow δ (-(2 * s + ε / 2)) * 1 := by gcongr
    linarith
  have h_pos_rpow : 0 ≤ Real.rpow δ (-(2 * s + ε)) :=
    le_of_lt (Real.rpow_pos_of_pos hδ_pos _)
  have h21 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε / 2))) ≤
      (1 : ENNReal) / (K : ENNReal) * ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by
    have h_ofReal_mul : ENNReal.ofReal ((1 : ℝ) / (K : ℝ) * Real.rpow δ (-(2 * s + ε))) =
        ENNReal.ofReal ((1 : ℝ) / (K : ℝ)) * ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    have h_ofReal_inv : ENNReal.ofReal ((1 : ℝ) / (K : ℝ)) = (1 : ENNReal) / (K : ENNReal) := by
      have h_pos' : 0 < (K : ℝ) := by exact_mod_cast hK_pos
      have h_div : (1 : ℝ) / (K : ℝ) = (K : ℝ)⁻¹ := by
        field_simp [h_pos'.ne']
      rw [h_div]
      have h : ENNReal.ofReal ((K : ℝ)⁻¹) = (ENNReal.ofReal (K : ℝ))⁻¹ :=
        ENNReal.ofReal_inv_of_pos h_pos'
      have h2 : ENNReal.ofReal (K : ℝ) = (K : ENNReal) := by simp
      rw [h, h2]
      <;> simp [one_div]
    have h22 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε / 2))) ≤
        ENNReal.ofReal ((1 : ℝ) / (K : ℝ) * Real.rpow δ (-(2 * s + ε))) :=
      ENNReal.ofReal_le_ofReal h14
    rw [h_ofReal_mul, h_ofReal_inv] at h22
    exact h22
  exact le_trans h21 h10

/-! ============================================================================
   Part 4: Input S-set transfer to coarser scale
   ============================================================================ -/

/-- General S-set transfer from a finer scale δ to a coarser scale δ_d.

    If `P` is a `(δ, s, C)`-set, `δ ≤ δ_d ≤ 2δ`, and the metric space has
    covering doubling constant `K`, then `P` is a `(δ_d, s, C*K)`-set. -/
lemma sset_transfer_coarser
    {X : Type*} [MetricSpace X]
    {δ δ_d : ℝ} (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_le_d : δ ≤ δ_d) (hδ_d_le_2δ : δ_d ≤ 2 * δ)
    (K : ℕ) (hK_pos : 0 < K)
    (h_doubling : ∀ (r : ℝ), 0 < r → ∀ (A : Set X),
      (Metric.externalCoveringNumber r.toNNReal A : ENNReal) ≤
        (K : ENNReal) * (Metric.externalCoveringNumber (2 * r).toNNReal A : ENNReal))
    {s C : ℝ} (hs : 0 ≤ s) (hC_pos : 0 < C)
    {P : Set X} (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ_d s (C * (K : ℝ)) P := by
  rcases hP with ⟨hP_nonempty, _, _, hs_nonneg, h_main⟩
  have hCK_pos : 0 < C * (K : ℝ) := by positivity
  have h_half_leδ : δ_d / 2 ≤ δ := by linarith
  have h_half_pos : 0 < δ_d / 2 := by linarith
  -- Ncover(δ, P) ≤ Ncover(δ_d/2, P) since δ_d/2 ≤ δ
  have hN1 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (Metric.externalCoveringNumber (δ_d / 2).toNNReal P : ENNReal) := by
    have h_le : (δ_d / 2).toNNReal ≤ δ.toNNReal := by
      have h1 : 0 ≤ δ_d / 2 := by linarith
      have h2 : 0 ≤ δ := by linarith
      have h3 : ((δ_d / 2).toNNReal : ℝ) ≤ (δ.toNNReal : ℝ) := by
        simp [h1, h2, h_half_leδ] <;> linarith
      exact NNReal.coe_le_coe.mp h3
    have h : Metric.externalCoveringNumber δ.toNNReal P ≤
        Metric.externalCoveringNumber (δ_d / 2).toNNReal P :=
      Metric.externalCoveringNumber_anti h_le
    exact_mod_cast h
  -- Ncover(δ_d/2, P) ≤ K * Ncover(δ_d, P) by doubling
  have hN2 : (Metric.externalCoveringNumber (δ_d / 2).toNNReal P : ENNReal) ≤
      (K : ENNReal) * (Metric.externalCoveringNumber δ_d.toNNReal P : ENNReal) := by
    have h := h_doubling (δ_d / 2) h_half_pos P
    have h2 : (2 * (δ_d / 2)).toNNReal = δ_d.toNNReal := by
      apply NNReal.coe_injective
      have h3 : 2 * (δ_d / 2) = δ_d := by ring
      rw [h3]
    rw [h2] at h
    exact h
  have hNcover : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      (K : ENNReal) * (Metric.externalCoveringNumber δ_d.toNNReal P : ENNReal) :=
    le_trans hN1 hN2
  refine' ⟨hP_nonempty, hδ_d_pos, hCK_pos, hs_nonneg, _⟩
  intro x r hr
  have hδ_le_r : δ ≤ r := by linarith
  have h1 : (Metric.externalCoveringNumber δ_d.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
    have h_le : δ.toNNReal ≤ δ_d.toNNReal := by
      have h1 : 0 ≤ δ := by linarith
      have h2 : 0 ≤ δ_d := by linarith
      have h3 : (δ.toNNReal : ℝ) ≤ (δ_d.toNNReal : ℝ) := by
        simp [h1, h2, hδ_le_d] <;> linarith
      exact NNReal.coe_le_coe.mp h3
    have h : Metric.externalCoveringNumber δ_d.toNNReal (P ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_anti h_le
    exact_mod_cast h
  have h2 := h_main x r hδ_le_r
  calc (Metric.externalCoveringNumber δ_d.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          ((K : ENNReal) * (Metric.externalCoveringNumber δ_d.toNNReal P : ENNReal)) := by gcongr
    _ = ENNReal.ofReal (C * (K : ℝ)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ_d.toNNReal P : ENNReal) := by
      have h3 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            ((K : ENNReal) * (Metric.externalCoveringNumber δ_d.toNNReal P : ENNReal)) =
          (K : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ_d.toNNReal P : ENNReal) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
      rw [h3]
      have h4 : (K : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal ((K : ℝ) * C) := by
        have h41 : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
        rw [h41]
        have h5 : 0 ≤ (K : ℝ) := by positivity
        have h6 : ENNReal.ofReal (K : ℝ) * ENNReal.ofReal C = ENNReal.ofReal ((K : ℝ) * C) := by
          rw [← ENNReal.ofReal_mul h5]
        exact h6
      rw [h4] <;> ring_nf

/-- Covering doubling for EuclideanPlane with constant 9. -/
lemma plane_covering_doubling {r : ℝ} (hr_pos : 0 < r)
    (A : Set EuclideanPlane) :
    (Metric.externalCoveringNumber r.toNNReal A : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber (2 * r).toNNReal A : ENNReal) := by
  have h := externalCoveringNumber_half_le_plane A (2 * r).toNNReal
  have h2 : (2 * r).toNNReal / 2 = r.toNNReal := by
    apply NNReal.coe_injective
    simp [NNReal.coe_div, hr_pos.le] <;> ring
  rw [h2] at h
  exact_mod_cast h

/-- S-set transfer for EuclideanPlane: (δ,s,C)-set → (δ_d,s,9*C)-set
    when δ ≤ δ_d ≤ 2δ. -/
lemma sset_transfer_coarser_plane
    {δ δ_d s C : ℝ} {P : Set EuclideanPlane}
    (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_le_d : δ ≤ δ_d) (hδ_d_le_2δ : δ_d ≤ 2 * δ)
    (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ_d s (C * 9) P :=
  sset_transfer_coarser hδ_pos hδ_d_pos hδ_le_d hδ_d_le_2δ
    9 (by norm_num) (fun r hr A => @plane_covering_doubling r hr A)
    hs hC_pos hP

/-- S-set transfer for AffineLine: (δ,s,C)-set → (δ_d,s,K*C)-set
    when δ ≤ δ_d ≤ 2δ, where K = affineLine_packing_constant. -/
lemma sset_transfer_coarser_affineLine
    {δ δ_d s C : ℝ} {P : Set AffineLine}
    (hδ_pos : 0 < δ) (hδ_d_pos : 0 < δ_d)
    (hδ_le_d : δ ≤ δ_d) (hδ_d_le_2δ : δ_d ≤ 2 * δ)
    (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ_d s (C * (MainAppendix.affineLine_packing_constant : ℝ)) P :=
  let K := MainAppendix.affineLine_packing_constant
  sset_transfer_coarser hδ_pos hδ_d_pos hδ_le_d hδ_d_le_2δ
    K MainAppendix.affineLine_packing_constant_pos
    (fun r hr A => affineLine_covering_doubling hr A)
    hs hC_pos hP

/-! ============================================================================
   Part 5: Coarser dyadic scale selection and output transfer
   ============================================================================ -/

/-- Given 0 < δ < 1, find a dyadic scale δ_d with δ < δ_d ≤ 2δ. -/
lemma choose_coarser_dyadic_scale (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    ∃ (n : ℕ), δ < dyadicDelta n ∧ dyadicDelta n ≤ 2 * δ := by
  let x : ℝ := 1 / δ
  have hx_gt_one : 1 < x := by
    have h : 1 / δ > 1 := by
      apply one_lt_one_div
      <;> linarith
    exact h
  let P : ℕ → Prop := fun n => (2 : ℝ)^n ≥ x
  have h_exists : ∃ n, P n := by
    have h_arch : ∃ n : ℕ, (n : ℝ) ≥ x := exists_nat_ge x
    rcases h_arch with ⟨n, hn⟩
    have h_pow2 : (n : ℝ) ≤ (2 : ℝ)^n := by
      have h : ∀ m : ℕ, (m : ℝ) ≤ (2 : ℝ)^m := by
        intro m
        induction m with
        | zero => norm_num
        | succ m ih =>
          have h5 : (2 : ℝ)^m ≥ 1 := by
            have h6 : ∀ k : ℕ, (2 : ℝ)^k ≥ 1 := by
              intro k; induction k <;> simp [*, pow_succ] <;> linarith
            exact h6 m
          simp [pow_succ] at * <;> linarith
      exact h n
    exact ⟨n, by linarith⟩
  let n := Nat.find h_exists
  have hn : P n := Nat.find_spec h_exists
  have h_n_pos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hn
    simp [P] at hn <;> linarith
  let m : ℕ := n - 1
  have hnm : n = m + 1 := by omega
  have h_lt : ¬ P m := Nat.find_min h_exists (by omega)
  have h1 : (2 : ℝ)^m < x := by
    simpa [P] using h_lt
  have h2 : dyadicDelta m > δ := by
    have h21 : (2 : ℝ)^m < x := h1
    have h_pos2m : 0 < (2 : ℝ)^m := by positivity
    have h : 1 / (2 : ℝ)^m > 1 / x := one_div_lt_one_div_of_lt (by positivity) h21
    have hx : 1 / x = δ := by
      simp [x, hδ_pos.ne'] <;> field_simp
    rw [hx] at h
    simpa [dyadicDelta] using h
  have h3 : dyadicDelta m ≤ 2 * δ := by
    have h31 : (2 : ℝ)^n ≥ x := hn
    have h32 : (2 : ℝ)^(m + 1) ≥ x := by
      rw [show n = m + 1 from hnm] at h31
      exact h31
    have h33 : (2 : ℝ)^(m + 1) = 2 * (2 : ℝ)^m := by
      simp [pow_succ] <;> ring
    rw [h33] at h32
    have h_pos2m : 0 < (2 : ℝ)^m := by positivity
    have h4 : 2 * (2 : ℝ)^m ≥ 1 / δ := by simpa [x] using h32
    have h5 : 1 / (2 : ℝ)^m ≤ 2 * δ := by
      have h6 : 2 * (2 : ℝ)^m * δ ≥ 1 := by
        calc 2 * (2 : ℝ)^m * δ
          ≥ (1 / δ) * δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne']
      calc 1 / (2 : ℝ)^m
        ≤ (2 * (2 : ℝ)^m * δ) / (2 : ℝ)^m := by gcongr
      _ = 2 * δ := by field_simp [h_pos2m.ne'] <;> ring
    simpa [dyadicDelta] using h5
  exact ⟨m, h2, h3⟩

/-- Output covering transfer from coarser dyadic δ_d to finer real δ.

    If Ncover(δ_d, T) ≥ δ_d^{-(2s+ε)} and δ < δ_d ≤ 2δ, then
    Ncover(δ, T) ≥ δ^{-(2s+ε/2)} for sufficiently small δ. -/
lemma output_transfer_coarser
    (δ s ε : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hε_pos : 0 < ε)
    (δ_d : ℝ) (hδ_d_pos : 0 < δ_d)
    (hδ_lt_d : δ < δ_d) (hδ_d_le_2δ : δ_d ≤ 2 * δ)
    (T : Set AffineLine)
    (h_bound : (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ_d (-(2 * s + ε))))
    (h_small : δ ≤ (2 : ℝ) ^ (-2 * (2 * s + ε) / ε)) :
    (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε / 2))) := by
  set z : ℝ := -(2 * s + ε) with hz_def
  have hz_neg : z < 0 := by linarith
  -- Step 1: Ncover(δ, T) ≥ Ncover(δ_d, T) since δ ≤ δ_d
  have hδ_le_d : δ ≤ δ_d := by linarith
  have h1 : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≥
      (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) := by
    have h_le : δ.toNNReal ≤ δ_d.toNNReal := by
      have h1 : 0 ≤ δ := by linarith
      have h2 : 0 ≤ δ_d := by linarith
      have h3 : (δ.toNNReal : ℝ) ≤ (δ_d.toNNReal : ℝ) := by
        simp [h1, h2, hδ_le_d] <;> linarith
      exact NNReal.coe_le_coe.mp h3
    have h : Metric.externalCoveringNumber δ_d.toNNReal T ≤
        Metric.externalCoveringNumber δ.toNNReal T :=
      Metric.externalCoveringNumber_anti h_le
    exact_mod_cast h
  -- Step 2: δ_d^z ≥ (2δ)^z since δ_d ≤ 2δ and z < 0
  have h2δ_pos : 0 < 2 * δ := by positivity
  have h4 : Real.rpow (2 * δ) z ≤ Real.rpow δ_d z := by
    have h_iff : Real.rpow (2 * δ) z ≤ Real.rpow δ_d z ↔ δ_d ≤ 2 * δ :=
      Real.rpow_le_rpow_iff_of_neg h2δ_pos hδ_d_pos hz_neg
    exact h_iff.mpr hδ_d_le_2δ
  -- Step 3: (2δ)^z = 2^z * δ^z
  have h5 : Real.rpow (2 * δ) z = Real.rpow 2 z * Real.rpow δ z := by
    have h : Real.rpow (2 * δ) z = Real.rpow (2 * δ) z := rfl
    have h6 : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z :=
      fun x y hx hy => Real.mul_rpow hx hy
    exact h6 2 δ (by norm_num) (by linarith)
  -- Step 4: 2^z ≥ δ^(ε/2) from h_small
  have h_half_pos2 : 0 ≤ ε / 2 := by linarith
  let a := -2 * (2 * s + ε) / ε
  have h6 : Real.rpow δ (ε / 2) ≤ Real.rpow 2 z := by
    have h71 : Real.rpow δ (ε / 2) ≤ Real.rpow (Real.rpow 2 a) (ε / 2) :=
      Real.rpow_le_rpow (by linarith) h_small h_half_pos2
    have h72 : Real.rpow (Real.rpow 2 a) (ε / 2) = Real.rpow 2 (a * (ε / 2)) := by
      have h := Real.rpow_mul (show (0 : ℝ) ≤ 2 from by norm_num) a (ε / 2)
      exact h.symm
    have h73 : a * (ε / 2) = z := by
      simp [a, z, hε_pos.ne'] <;> field_simp [hε_pos.ne'] <;> ring
    rw [h72, h73] at h71
    exact h71
  -- Step 5: 2^z * δ^z ≥ δ^(z + ε/2) = δ^(-(2s+ε/2))
  have h10 : z + ε / 2 = -(2 * s + ε / 2) := by
    simp [z] <;> ring
  have h11 : Real.rpow 2 z * Real.rpow δ z ≥ Real.rpow δ (z + ε / 2) := by
    have h12 : Real.rpow δ (ε / 2) * Real.rpow δ z = Real.rpow δ (ε / 2 + z) := by
      exact (Real.rpow_add hδ_pos (ε / 2) z).symm
    have h13 : Real.rpow 2 z * Real.rpow δ z ≥ Real.rpow δ (ε / 2) * Real.rpow δ z := by
      have h_pos_z : 0 ≤ Real.rpow δ z := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul_of_nonneg_right h6 h_pos_z
    rw [h12] at h13
    have h14 : ε / 2 + z = z + ε / 2 := by ring
    rw [h14] at h13
    exact h13
  have h15 : Real.rpow δ_d z ≥ Real.rpow δ (z + ε / 2) := by
    calc Real.rpow δ_d z
      ≥ Real.rpow (2 * δ) z := h4
    _ = Real.rpow 2 z * Real.rpow δ z := h5
    _ ≥ Real.rpow δ (z + ε / 2) := h11
  rw [h10] at h15
  have h16 : (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε / 2))) :=
    le_trans (ENNReal.ofReal_le_ofReal h15) h_bound
  exact le_trans h16 h1

/-! ============================================================================
   Part 6: Full nearby-dyadic transfer package
   ============================================================================ -/

/-- Full nearby-dyadic transfer package.

    Given arbitrary real δ and input S-sets at scale δ:
    1. Finds a coarser dyadic scale δ_d with δ < δ_d ≤ 2δ
    2. Transfers point set X from (δ,t,C)-set to (δ_d,t,9*C)-set
    3. Transfers tube families from (δ,s,C)-set to (δ_d,s,K*C)-set
    4. Transfers output covering lower bound from δ_d back to δ

    This bridges the gap between the target theorem (arbitrary real δ) and
    the incidence axiom (dyadic δ only). -/
theorem full_nearby_dyadic_transfer
    (δ s t ε C : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (ht_nonneg : 0 ≤ t) (hε_pos : 0 < ε) (hC_pos : 0 < C)
    (X : Set EuclideanPlane) (hX : IsDeltaSSet δ t C X)
    (𝓣 : ∀ (x : EuclideanPlane), x ∈ X → Set AffineLine)
    (h𝓣 : ∀ x hx, IsDeltaSSet δ s C (𝓣 x hx))
    (h_small : δ ≤ (2 : ℝ) ^ (-2 * (2 * s + ε) / ε)) :
    ∃ (δ_d : ℝ), (∃ n : ℕ, δ_d = dyadicDelta n) ∧ δ < δ_d ∧ δ_d ≤ 2 * δ ∧
      IsDeltaSSet δ_d t (C * 9) X ∧
      (∀ x hx, IsDeltaSSet δ_d s (C * (MainAppendix.affineLine_packing_constant : ℝ)) (𝓣 x hx)) ∧
      ∀ (T : Set AffineLine),
        (Metric.externalCoveringNumber δ_d.toNNReal T : ENNReal) ≥
          ENNReal.ofReal (Real.rpow δ_d (-(2 * s + ε))) →
        (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≥
          ENNReal.ofReal (Real.rpow δ (-(2 * s + ε / 2))) := by
  rcases choose_coarser_dyadic_scale δ hδ_pos hδ_lt_one with ⟨n, hlt, hle⟩
  let δ_d : ℝ := dyadicDelta n
  have hδ_d_pos : 0 < δ_d := dyadicDelta_pos n
  have hδ_lt_d : δ < δ_d := hlt
  have hδ_d_le_2δ : δ_d ≤ 2 * δ := hle
  have hδ_le_d : δ ≤ δ_d := by linarith
  have hX' : IsDeltaSSet δ_d t (C * 9) X :=
    sset_transfer_coarser_plane hδ_pos hδ_d_pos hδ_le_d hδ_d_le_2δ ht_nonneg hC_pos hX
  have h𝓣' : ∀ x hx, IsDeltaSSet δ_d s (C * (MainAppendix.affineLine_packing_constant : ℝ)) (𝓣 x hx) :=
    fun x hx => sset_transfer_coarser_affineLine hδ_pos hδ_d_pos hδ_le_d hδ_d_le_2δ (by linarith) hC_pos (h𝓣 x hx)
  refine' ⟨δ_d, ⟨n, rfl⟩, hδ_lt_d, hδ_d_le_2δ, hX', h𝓣', _⟩
  intro T h_bound
  exact output_transfer_coarser δ s ε hδ_pos hδ_lt_one hs_pos hε_pos δ_d hδ_d_pos
    hδ_lt_d hδ_d_le_2δ T h_bound h_small

end DiscretisedFurstenbergEstimate.NearbyDyadicTransfer
