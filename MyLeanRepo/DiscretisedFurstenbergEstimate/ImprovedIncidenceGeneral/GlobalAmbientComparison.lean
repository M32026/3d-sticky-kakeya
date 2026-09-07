module

/-
  Global ambient comparison for Lemma 7.

  Thin wrapper around `covering_movement_global`: given a family of DyadicTubes
  with provenance to an oriented AffineLine family (dist ≤ 7δ), bound the total
  number of tubes by K_ambient * Ncover(δ, T_oriented).

  For B=3/2 (snapped tubes), K_ambient = (2 * Nat.ceil (49 * 8) + 1)^2 = 785^2.

  Also provides Lemma 7 (`finalize_tubes_and_global_bound`): covering mass
  with exact common cardinality M AND global ambient bound.

  Whiteprint node: improved_incidence_general / global_ambient_comparison
  Dependencies: CoveringMovement, B1_Sublemmas
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringMovement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CoveringMovementGeneralized
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DyadicCardToNcover

/-- Global ambient bound: if every tube U in T₀ has provenance to T_oriented
    (dist(ℓ, toAffineLine(U)) ≤ 6δ), and tubes have bounded slopes/intercepts,
    then |T₀| ≤ K_ambient * Ncover(δ, T_oriented).

    This is a direct application of `covering_movement_global` with C_move = 7.
    K_ambient = (2 * Nat.ceil (32 * 8) + 1)^2 = 513^2. -/
lemma global_ambient_bound {n : ℕ} {δ : ℝ}
    (hδ_pos : 0 < δ) (hδn_leδ : dyadicDelta n ≤ δ) (hδ_lt2δn : δ < 2 * dyadicDelta n)
    (T₀ : Finset (DyadicTube n))
    (T_oriented : Set AffineLine)
    (h_slope_bound : ∀ U ∈ T₀, |U.slope| ≤ 1)
    (h_intercept_bound : ∀ U ∈ T₀, |U.intercept| ≤ 3)
    (h_provenance : ∀ U ∈ T₀, ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
      AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ) :
    (T₀.card : ENNReal) ≤
      (2 * Nat.ceil (32 * (8 : ℝ)) + 1)^2 *
        Metric.externalCoveringNumber δ.toNNReal T_oriented := by
  have h_prov' : ∀ U ∈ T₀, ∃ ℓ ∈ T_oriented,
      dist (toAffineLine U) ℓ ≤ (7 : ℝ) * δ := by
    intro U hU
    rcases h_provenance U hU with ⟨ℓ, hℓ, hdist⟩
    refine ⟨ℓ, hℓ, ?_⟩
    have h : dist ℓ (toAffineLine U) ≤ 7 * δ := by exact_mod_cast hdist
    have h_comm : dist ℓ (toAffineLine U) = dist (toAffineLine U) ℓ := dist_comm _ _
    rw [h_comm] at h
    exact h
  have h_main : (T₀.card : ENNReal) ≤
      (2 * Nat.ceil (32 * ((7 : ℝ) + 1)) + 1)^2 *
        Metric.externalCoveringNumber δ.toNNReal T_oriented :=
    covering_movement_global
      (hδ_pos := hδ_pos)
      (hC_move_nonneg := by norm_num)
      (h_scale := hδ_lt2δn)
      (T_oriented := T_oriented)
      (T₀ := T₀)
      (hm := h_slope_bound)
      (hb := h_intercept_bound)
      (h_prov := h_prov')
  have h_norm : (32 * ((7 : ℝ) + 1)) = (32 * (8 : ℝ)) := by norm_num
  rw [h_norm] at h_main
  exact h_main

/-- Generalized global ambient bound with arbitrary slope bound B.

    Uses `covering_movement_global_generalized` with C_move = 7.
    K_ambient(B) = (2 * Nat.ceil (4 * (4 + B + 3*B^2) * 8) + 1)^2.

    For B=1: K = 513^2 (matches `global_ambient_bound`).
    For B=3/2: K = 785^2. -/
lemma global_ambient_bound_generalized {n : ℕ} {δ B : ℝ}
    (hδ_pos : 0 < δ) (hδn_leδ : dyadicDelta n ≤ δ) (hδ_lt2δn : δ < 2 * dyadicDelta n)
    (hB_nonneg : 0 ≤ B)
    (T₀ : Finset (DyadicTube n))
    (T_oriented : Set AffineLine)
    (h_slope_bound : ∀ U ∈ T₀, |U.slope| ≤ B)
    (h_intercept_bound : ∀ U ∈ T₀, |U.intercept| ≤ 3)
    (h_provenance : ∀ U ∈ T₀, ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
      AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ) :
    (T₀.card : ENNReal) ≤
      (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1)^2 *
        Metric.externalCoveringNumber δ.toNNReal T_oriented := by
  have h_prov' : ∀ U ∈ T₀, ∃ ℓ ∈ T_oriented,
      dist (toAffineLine U) ℓ ≤ (7 : ℝ) * δ := by
    intro U hU
    rcases h_provenance U hU with ⟨ℓ, hℓ, hdist⟩
    refine ⟨ℓ, hℓ, ?_⟩
    have h : dist ℓ (toAffineLine U) ≤ 7 * δ := by exact_mod_cast hdist
    have h_comm : dist ℓ (toAffineLine U) = dist (toAffineLine U) ℓ := dist_comm _ _
    rw [h_comm] at h
    exact h
  have h_main : (T₀.card : ENNReal) ≤
      (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * ((7 : ℝ) + 1)) + 1)^2 *
        Metric.externalCoveringNumber δ.toNNReal T_oriented :=
    covering_movement_global_generalized
      (hδ_pos := hδ_pos)
      (hC_move_nonneg := by norm_num)
      (hB_nonneg := hB_nonneg)
      (h_scale := hδ_lt2δn)
      (T_oriented := T_oriented)
      (T₀ := T₀)
      (hm := h_slope_bound)
      (hb := h_intercept_bound)
      (h_prov := h_prov')
  have h_norm : (4 * (4 + B + 3 * B^2) * ((7 : ℝ) + 1)) =
      (4 * (4 + B + 3 * B^2) * (8 : ℝ)) := by ring
  rw [h_norm] at h_main
  exact h_main

/- COMMENTED OUT: broken second half, not currently needed
/-- Subset S-set transfer for DyadicTubes: if B ⊆ A, |A| < 2|B|, and A is a
    (δ_n, s, C)-S-set, then B is a (δ_n, s, 18*C)-S-set.

    Key: distinct DyadicTubes are δ_n-separated, so |B| ≤ 9 * Ncover(δ_n, B).
    Then Ncover(δ_n, A) ≤ |A| < 2|B| ≤ 18 * Ncover(δ_n, B). -/
lemma dyadic_subset_sset_transfer {n : ℕ} {s C : ℝ}
    {A B : Finset (DyadicTube n)}
    (hB_sub : B ⊆ A)
    (h_card : A.card < 2 * B.card)
    (hA_sset : IsDeltaSSet (dyadicDelta n) s C (A : Set (DyadicTube n))) :
    IsDeltaSSet (dyadicDelta n) s (18 * C) (B : Set (DyadicTube n)) := by
  set δ_n := dyadicDelta n with hδn_def
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hB_pos : 0 < B.card := by
    by_contra h
    have h0 : B.card = 0 := by omega
    have h1 : B = ∅ := by simpa [Finset.card_eq_zero] using h0
    rw [h1] at h_card
    exact False.elim (not_lt.mpr (Nat.zero_le A.card) h_card)
  have hB_nonempty : (B : Set (DyadicTube n)).Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty] using hB_pos
  -- Distinct DyadicTubes are δ_n-separated
  have h_sep : SeparatedAt δ_n (B : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 hne
    have h_dist_eq : dist T1 T2 = T1.dist T2 := by rfl
    rw [h_dist_eq, DyadicTube.dist_eq T1 T2]
    have h_ne_coord : T1.a ≠ T2.a ∨ T1.b ≠ T2.b := by
      by_contra h
      push Not at h
      have h' : T1 = T2 := by
        exact DyadicTube.eq_iff.mpr h
      exact hne h'
    have h_pos : 0 < (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      rcases h_ne_coord with (h | h)
      · have h' : 0 < |(T1.a - T2.a : ℤ)| := by
          apply Int.abs_pos.mpr
          exact sub_ne_zero.mpr h
        exact_mod_cast h'
      · have h' : 0 < |(T1.b - T2.b : ℤ)| := by
          apply Int.abs_pos.mpr
          exact sub_ne_zero.mpr h
        exact_mod_cast h'
    have h9 : (1 : ℝ) ≤ (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      exact_mod_cast h_pos
    have h_ge : δ_n * ((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)) ≥ δ_n := by
      nlinarith
    exact h_ge
  -- Packing bound: |B| ≤ 9 * Ncover(δ_n, B)
  have h_pack : (B.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) :=
    DirecretisedFurstenbergEstimate.SSetBridges.packing_cover_generic
      (hδ_pos := hδn_pos) (hsep := h_sep) (hK_pos := by norm_num)
      (fun x => DiscretisedFurstenbergEstimate.InductionOnScales.max_points_in_delta_ball_DyadicTube hδn_pos B h_sep x)
  -- Ncover(δ_n, A) ≤ |A| < 2|B| ≤ 18 * Ncover(δ_n, B)
  have h1 : (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal) ≤
      (A.card : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (A : Set (DyadicTube n))
  have h2 : (A.card : ENNReal) < 2 * (B.card : ENNReal) := by
    exact_mod_cast h_card
  have h3 : (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal) ≤
      (18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by
    calc (Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) : ENNReal)
      ≤ (A.card : ENNReal) := h1
    _ ≤ 2 * (B.card : ENNReal) := le_of_lt h2
    _ ≤ 2 * ((9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))) := by gcongr
    _ = (18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by ring
  -- Transfer S-set property
  rcases hA_sset with ⟨hne_A, hδ, hC_pos, hs, hmain⟩
  have hC18_pos : 0 < 18 * C := by positivity
  refine ⟨hB_nonempty, hδ, hC18_pos, hs, fun x r hr => ?_⟩
  have h4 : (Metric.externalCoveringNumber δ_n.toNNReal ((B : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal) ≤
      Metric.externalCoveringNumber δ_n.toNNReal ((A : Set (DyadicTube n)) ∩ Metric.closedBall x r) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (show (B : Set (DyadicTube n)) ∩ Metric.closedBall x r ⊆ (A : Set (DyadicTube n)) ∩ Metric.closedBall x r from by gcongr)
  have h5 := hmain x r hr
  calc (Metric.externalCoveringNumber δ_n.toNNReal ((B : Set (DyadicTube n)) ∩ Metric.closedBall x r) : ENNReal)
    ≤ Metric.externalCoveringNumber δ_n.toNNReal ((A : Set (DyadicTube n)) ∩ Metric.closedBall x r) := h4
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber δ_n.toNNReal (A : Set (DyadicTube n)) := h5
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        ((18 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))) := by gcongr
  _ = ENNReal.ofReal (18 * C) * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) := by
    have h6 : ENNReal.ofReal (18 * C) = (18 : ENNReal) * ENNReal.ofReal C := by
      have h7 : ENNReal.ofReal (18 * C) = ENNReal.ofReal 18 * ENNReal.ofReal C := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)]
      rw [h7]
      have h8 : ENNReal.ofReal 18 = (18 : ENNReal) := by simp
      rw [h8]
    rw [h6]
    <;> ring

/-- Lemma 7: Finalize tubes — covering mass with exact common cardinality M
    AND global ambient bound.

    Uses weighted_uniformize_cardinalities to thin to a common M = 2^k,
    then transfers S-set property with constant 18*C_raw, which is absorbed
    into δ_n^{-lam} by hypothesis. -/
lemma finalize_tubes_and_global_bound
    {n : ℕ} {δ s : ℝ}
    (hδ_pos : 0 < δ)
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (hδ_lt2δn : δ < 2 * dyadicDelta n)
    (squares : Finset (DyadicSquare n))
    (rawTubes : ∀ (q : DyadicSquare n), q ∈ squares → Finset (DyadicTube n))
    (C_raw : ℝ) (hC_raw_pos : 0 < C_raw)
    (h_raw_sset : ∀ q hq, IsDeltaSSet (dyadicDelta n) s C_raw (rawTubes q hq : Set (DyadicTube n)))
    (K : ℕ) (hK : ∀ q hq, (rawTubes q hq).card ≤ 2^K)
    (lam : ℝ) (hlam_pos : 0 < lam)
    (h_absorb : 18 * C_raw ≤ (dyadicDelta n) ^ (-lam))
    (h_intersect : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      (U.toSet ∩ (q.toSet : Set Plane)).Nonempty)
    (T_oriented : Set AffineLine)
    (B : ℝ) (hB_nonneg : 0 ≤ B)
    (h_slope_bound : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.slope| ≤ B)
    (h_intercept_bound : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.intercept| ≤ 3)
    (h_provenance : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
        AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ) :
    ∃ (squares' : Finset (DyadicSquare n))
      (tubeFam : ∀ (q : DyadicSquare n), q ∈ squares' → Finset (DyadicTube n))
      (T₀ : Finset (DyadicTube n))
      (M : ℕ)
      (K_ambient : ℕ),
      squares' ⊆ squares ∧
      (squares'.card : ℝ) ≥ (squares.card : ℝ) / (K + 1 : ℝ) ∧
      0 < M ∧
      (∀ q hq, (tubeFam q hq).card = M) ∧
      (∀ q hq, IsDeltaSSet (dyadicDelta n) s ((dyadicDelta n) ^ (-lam))
          (tubeFam q hq : Set (DyadicTube n))) ∧
      (∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
          (U.toSet ∩ (q.toSet : Set Plane)).Nonempty) ∧
      (∀ q hq, tubeFam q hq ⊆ T₀) ∧
      0 < K_ambient ∧
      (T₀.card : ENNReal) ≤
        (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) := by
  -- Step 1: Uniformize cardinalities using weighted pigeonhole with unit weights
  let w : DyadicSquare n → ℝ := fun _ => 1
  let rawTubesSimple (q : DyadicSquare n) : Finset (DyadicTube n) :=
    if hq : q ∈ squares then rawTubes q hq else ∅
  have hK_simple : ∀ q ∈ squares, (rawTubesSimple q).card ≤ 2^K := by
    intro q hq
    have h_eq : rawTubesSimple q = rawTubes q hq := by
      simp [rawTubesSimple, hq]
    rw [h_eq]
    exact hK q hq
  have h_nonempty : ∀ q ∈ squares, (rawTubesSimple q).Nonempty := by
    intro q hq
    have h_eq : rawTubesSimple q = rawTubes q hq := by
      simp [rawTubesSimple, hq]
    rw [h_eq]
    have h_sset : IsDeltaSSet (dyadicDelta n) s C_raw (rawTubes q hq : Set (DyadicTube n)) :=
      h_raw_sset q hq
    exact h_sset.1
  rcases DiscretisedFurstenbergEstimate.InductionOnScales.weighted_uniformize_cardinalities
      squares rawTubesSimple w K hK_simple h_nonempty (fun _ _ => by norm_num) with
    ⟨k, squares', M, C_trim, hk_le, hM_eq, h_squares'_sub, h_weight, h_trim⟩
  have hM_pos : 0 < M := by
    rw [hM_eq] <;> positivity
  -- Step 2: Define tubeFam from C_trim restricted to squares'
  let tubeFam : ∀ (q : DyadicSquare n), q ∈ squares' → Finset (DyadicTube n) :=
    fun q hq => C_trim q
  let rawTubes' (q : DyadicSquare n) : Finset (DyadicTube n) :=
    if hq : q ∈ squares' then C_trim q else ∅
  let T₀ : Finset (DyadicTube n) := squares'.biUnion rawTubes'
  let K_ambient : ℕ := (2 * Nat.ceil (32 * (7 : ℝ)) + 1)^2

  have hK_pos : 0 < K_ambient := by positivity
  have h_squares'_card : (squares'.card : ℝ) ≥ (squares.card : ℝ) / (K + 1 : ℝ) := by
    simpa [w, Finset.sum_const] using h_weight

  -- Properties of trimmed families
  have h1 : ∀ q hq, tubeFam q hq ⊆ rawTubesSimple q := by
    intro q hq
    exact (h_trim q hq).1
  have h1' : ∀ q hq, tubeFam q hq ⊆ rawTubes q (h_squares'_sub hq) := by
    intro q hq
    have h_sub : tubeFam q hq ⊆ rawTubesSimple q := h1 q hq
    have h_eq : rawTubesSimple q = rawTubes q (h_squares'_sub hq) := by
      simp [rawTubesSimple, h_squares'_sub hq]
    rw [h_eq] at h_sub
    exact h_sub
  have h2 : ∀ q hq, (tubeFam q hq).card = M := by
    intro q hq
    exact (h_trim q hq).2.1
  have h3_card : ∀ (q : DyadicSquare n) (hq : q ∈ squares'), (rawTubesSimple q).card < 2 * M := by
    intro q hq
    exact (h_trim q hq).2.2.2
  have h3_card' : ∀ (q : DyadicSquare n) (hq : q ∈ squares'), (rawTubes q (h_squares'_sub hq)).card < 2 * M := by
    intro q hq
    have h_eq : rawTubesSimple q = rawTubes q (h_squares'_sub hq) := by
      simp [rawTubesSimple, h_squares'_sub hq]
    rw [h_eq]
    exact h3_card q hq
  -- S-set transfer: trimmed family is (δ_n, s, 18*C_raw)-S-set
  have h3_sset18 : ∀ q hq, IsDeltaSSet (dyadicDelta n) s (18 * C_raw)
      (tubeFam q hq : Set (DyadicTube n)) := by
    intro q hq
    exact dyadic_subset_sset_transfer
      (h1' q hq)
      (h3_card' q hq)
      (h_raw_sset q (h_squares'_sub hq))
  -- Absorb 18*C_raw into δ_n^{-lam}
  have h3 : ∀ q hq, IsDeltaSSet (dyadicDelta n) s ((dyadicDelta n) ^ (-lam))
      (tubeFam q hq : Set (DyadicTube n)) := by
    intro q hq
    have hC_lam_pos : 0 < (dyadicDelta n) ^ (-lam) := by positivity
    rcases h3_sset18 q hq with ⟨hne, hδ, hC18_pos, hs, hmain⟩
    refine ⟨hne, hδ, hC_lam_pos, hs, fun x r hr => ?_⟩
    have h6 := hmain x r hr
    calc (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (_ ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal (18 * C_raw) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (tubeFam q hq : Set (DyadicTube n)) : ENNReal) := h6
    _ ≤ ENNReal.ofReal ((dyadicDelta n) ^ (-lam)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber (dyadicDelta n).toNNReal (tubeFam q hq : Set (DyadicTube n)) : ENNReal) := by
      gcongr <;> exact ENNReal.ofReal_le_ofReal h_absorb
  have h4 : ∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
      (U.toSet ∩ (q.toSet : Set Plane)).Nonempty := by
    intro q hq U hU
    exact h_intersect q (h_squares'_sub hq) U (h1' q hq hU)
  have h5 : ∀ q hq, tubeFam q hq ⊆ T₀ := by
    intro q hq
    intro U hU
    have h_raw_eq : rawTubes' q = C_trim q := by
      simp [rawTubes', hq]
    have hU' : U ∈ rawTubes' q := by
      rw [h_raw_eq] <;> exact hU
    exact Finset.mem_biUnion.mpr ⟨q, hq, hU'⟩

  -- Global ambient bound
  have h_slope : ∀ U ∈ T₀, |U.slope| ≤ 1 := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨q, hq, hU_raw⟩
    have h_raw_eq : rawTubes' q = C_trim q := by simp [rawTubes', hq]
    rw [h_raw_eq] at hU_raw
    exact h_slope_bound q (h_squares'_sub hq) U (h1' q hq hU_raw)
  have h_intercept : ∀ U ∈ T₀, |U.intercept| ≤ 3 := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨q, hq, hU_raw⟩
    have h_raw_eq : rawTubes' q = C_trim q := by simp [rawTubes', hq]
    rw [h_raw_eq] at hU_raw
    exact h_intercept_bound q (h_squares'_sub hq) U (h1' q hq hU_raw)
  have h_prov : ∀ U ∈ T₀, ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
      AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨q, hq, hU_raw⟩
    have h_raw_eq : rawTubes' q = C_trim q := by simp [rawTubes', hq]
    rw [h_raw_eq] at hU_raw
    exact h_provenance q (h_squares'_sub hq) U (h1' q hq hU_raw)

  have h_ambient : (T₀.card : ENNReal) ≤
      (K_ambient : ENNReal) * Metric.externalCoveringNumber δ.toNNReal T_oriented := by
    have h : (T₀.card : ENNReal) ≤
        ((2 * Nat.ceil (32 * (8 : ℝ)) + 1)^2 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal T_oriented :=
      global_ambient_bound
        (hδ_pos := hδ_pos)
        (hδn_leδ := hδn_leδ)
        (hδ_lt2δn := hδ_lt2δn)
        (T₀ := T₀)
        (T_oriented := T_oriented)
        (h_slope_bound := h_slope)
        (h_intercept_bound := h_intercept)
        (h_provenance := h_prov)
    have hK_def : (K_ambient : ENNReal) = ((2 * Nat.ceil (32 * (8 : ℝ)) + 1)^2 : ENNReal) := by rfl
    rw [hK_def]
    exact h

  exact ⟨squares', tubeFam, T₀, M, K_ambient,
    h_squares'_sub, h_squares'_card, hM_pos, h2, h3, h4, h5, hK_pos, h_ambient⟩

-/

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
