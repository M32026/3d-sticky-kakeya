module

/-
  Standalone fibre-cardinality uniformization step.

  Extracts the fibre uniformization from BridgeInner.lean into a standalone
  lemma that operates on squares and tube families, NOT on a point set.

  Wraps `finalize_tubes_and_global_bound` and adds the M lower bound proof
  from the S-set property.

  Outputs:
  - squares' : retained subset of squares (card ≥ original / (K+1))
  - tubeFam : exact common cardinality M, S-set constant δ_n^{-lam}
  - T₀ : ambient tube family
  - M : exact common cardinality
  - K_ambient : tube count bound factor
  - hM_lower : M ≥ δ_n^(-s+lam+ρ_M)
  - hT0_bound : T₀.card ≤ K_ambient * Ncover(T_oriented)
  - htube_sset : S-set property for each retained square

  Whiteprint node: section9 / fibre_uniformization_step
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Lemma7Repair
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CardinalityLowerBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open ImprovedIncidenceAssembly (sset_ncover_lower_bound)
open DyadicCardToNcover (toAffineLine)

/-- Standalone fibre-cardinality uniformization step.

    Takes raw tube families per square and produces uniformized families
    with exact common cardinality M and S-set constant δ_n^{-lam}.

    This is a thin wrapper around `finalize_tubes_and_global_bound` plus
    the M lower bound derivation from the S-set property. -/
lemma fibre_uniformization_step
    {n : ℕ} {δ s lam : ℝ}
    (hδ_pos : 0 < δ)
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (hδ_lt2δn : δ < 2 * dyadicDelta n)
    (squares : Finset (DyadicSquare n))
    (rawTubes : ∀ (q : DyadicSquare n), q ∈ squares → Finset (DyadicTube n))
    (C_raw : ℝ) (hC_raw_pos : 0 < C_raw)
    (h_raw_sset : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C_raw (rawTubes q hq : Set (DyadicTube n)))
    (K : ℕ) (hK : ∀ q hq, (rawTubes q hq).card ≤ 2^K)
    (hlam_pos : 0 < lam)
    (h_absorb : 18 * C_raw ≤ (dyadicDelta n) ^ (-lam))
    (h_intersect : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      (U.toSet ∩ (q.toSet : Set EuclideanPlane)).Nonempty)
    (T_oriented : Set AffineLine)
    (B : ℝ) (hB_nonneg : 0 ≤ B) (hB_le_three_halves : B ≤ 3 / 2)
    (h_slope_bound : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.slope| ≤ B)
    (h_intercept_bound : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.intercept| ≤ 3)
    (h_provenance : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧ dist (toAffineLine U) ℓ ≤ 7 * δ)
    (h_raw_strip : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ))
    (hsquares_nonempty : squares.Nonempty)
    (ρ_M : ℝ) (hρ_M_nonneg : 0 ≤ ρ_M) :
    ∃ (squares_all : Finset (DyadicSquare n))
      (K_band : ℕ)
      (squares' : Finset (DyadicSquare n))
      (tubeFam : ∀ (q : DyadicSquare n), q ∈ squares' → Finset (DyadicTube n))
      (T₀ : Finset (DyadicTube n))
      (M : ℕ)
      (K_ambient : ℕ),
      squares_all = squares ∧
      K_band = K ∧
      squares' ⊆ squares_all ∧
      (squares'.card : ℝ) ≥ (squares_all.card : ℝ) / (K_band + 1 : ℝ) ∧
      0 < M ∧
      (∀ q hq, (tubeFam q hq).card = M) ∧
      (∀ q hq, IsDeltaSSet (dyadicDelta n) s ((dyadicDelta n) ^ (-lam))
          (tubeFam q hq : Set (DyadicTube n))) ∧
      (∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
          (U.toSet ∩ (q.toSet : Set EuclideanPlane)).Nonempty) ∧
      (∀ q hq, tubeFam q hq ⊆ T₀) ∧
      0 < K_ambient ∧
      (T₀.card : ENNReal) ≤
        (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) ∧
      K_ambient ≤ 1000000 ∧
      (M : ℝ) ≥ (dyadicDelta n) ^ (-s + lam + ρ_M) ∧
      ((T₀ : Set (DyadicTube n)) = ⋃ (q : DyadicSquare n) (hq : q ∈ squares'), (tubeFam q hq : Set (DyadicTube n))) ∧
      (∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
        -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ)) ∧
      (∀ q hq, ∃ (hqs : q ∈ squares), tubeFam q hq ⊆ rawTubes q hqs) := by
  let δ_n := dyadicDelta n
  have hδn_le_one : δ_n ≤ 1 := dyadicDelta_le_one n

  rcases finalize_tubes_and_global_bound
      hδ_pos hδn_pos hδn_leδ hδ_lt2δn
      squares rawTubes C_raw hC_raw_pos h_raw_sset K hK
      lam hlam_pos h_absorb h_intersect
      T_oriented B hB_nonneg hB_le_three_halves
      h_slope_bound h_intercept_bound h_provenance h_raw_strip
    with ⟨squares', tubeFam, T₀, M, K_ambient,
      hsquares'_sub, hretention, hM_pos, _, huniform, htube_sset, htube_intersect,
      htube_in_T0, _, _, hK_ambient_pos, hT0_bound, _, hKamb_bound, hT0_eq_union,
      h_tube_strip, htube_subset_raw⟩

  -- M lower bound from S-set property
  have hM_lower : (M : ℝ) ≥ δ_n ^ (-s + lam + ρ_M) := by
    have hq_nonempty : squares'.Nonempty := by
      have h7 : (squares'.card : ℝ) ≥ (squares.card : ℝ) / (K + 1 : ℝ) := hretention
      have h8 : 0 < (squares.card : ℝ) := by exact_mod_cast hsquares_nonempty.card_pos
      have h9 : (0 : ℝ) < (K + 1 : ℝ) := by positivity
      have h10 : 0 < (squares.card : ℝ) / (K + 1 : ℝ) := by positivity
      have h11 : 0 < (squares'.card : ℝ) := by linarith
      have h12 : 0 < squares'.card := by exact_mod_cast h11
      exact Finset.card_pos.mp h12
    rcases hq_nonempty with ⟨q, hq⟩
    have h_sset : IsDeltaSSet δ_n s (δ_n ^ (-lam)) (tubeFam q hq : Set (DyadicTube n)) :=
      htube_sset q hq
    have h_lower1 : ENNReal.ofReal ((δ_n ^ (-lam) * δ_n ^ s)⁻¹) ≤
        (Metric.externalCoveringNumber δ_n.toNNReal (tubeFam q hq : Set (DyadicTube n)) : ENNReal) :=
      sset_ncover_lower_bound h_sset
    have hcover : (Metric.externalCoveringNumber δ_n.toNNReal (tubeFam q hq : Set (DyadicTube n)) : ENNReal) ≤
        (tubeFam q hq).card := by
      have hcover_self : Metric.IsCover δ_n.toNNReal (tubeFam q hq : Set (DyadicTube n)) (tubeFam q hq : Set (DyadicTube n)) := by
        intro x hx; exact ⟨x, hx, by simp [hδn_pos.le]⟩
      exact_mod_cast hcover_self.externalCoveringNumber_le_encard
    have h_eq : (tubeFam q hq).card = M := huniform q hq
    have h9 : ENNReal.ofReal ((δ_n ^ (-lam) * δ_n ^ s)⁻¹) ≤ (M : ENNReal) := by
      rw [h_eq] at hcover
      exact le_trans h_lower1 hcover
    have h10 : 0 ≤ (δ_n ^ (-lam) * δ_n ^ s)⁻¹ := by positivity
    have h11 : (M : ℝ) ≥ (δ_n ^ (-lam) * δ_n ^ s)⁻¹ := by exact_mod_cast h9
    have h12 : (δ_n ^ (-lam) * δ_n ^ s)⁻¹ = δ_n ^ (lam - s) := by
      have h_exp1 : (-lam) + s = -lam + s := by ring
      have h13 : δ_n ^ (-lam) * δ_n ^ s = δ_n ^ (-lam + s) := by
        rw [← Real.rpow_add hδn_pos, h_exp1]
      rw [h13]
      have h14 : (δ_n ^ (-lam + s))⁻¹ = δ_n ^ (-(-lam + s)) := by
        rw [← Real.rpow_neg hδn_pos.le]
      have h15 : -(-lam + s) = lam - s := by ring
      rw [h14, h15]
    rw [h12] at h11
    have h14 : -s + lam + ρ_M ≥ lam - s := by linarith [hρ_M_nonneg]
    have h15 : δ_n ≤ 1 := hδn_le_one
    have h16 : δ_n ^ (lam - s) ≥ δ_n ^ (-s + lam + ρ_M) :=
      Real.rpow_le_rpow_of_exponent_ge hδn_pos h15 h14
    exact le_trans h16 h11

  exact ⟨squares, K, squares', tubeFam, T₀, M, K_ambient,
    rfl, rfl, hsquares'_sub, hretention,
    hM_pos, huniform, htube_sset, htube_intersect, htube_in_T0,
    hK_ambient_pos, hT0_bound, hKamb_bound, hM_lower, hT0_eq_union, h_tube_strip, htube_subset_raw⟩

end DirecretisedFurstenbergEstimate.Section9
