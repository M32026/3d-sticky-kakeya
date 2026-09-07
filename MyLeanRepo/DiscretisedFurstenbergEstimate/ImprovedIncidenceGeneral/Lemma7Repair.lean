module

/-
  Repaired Lemma 7: finalize_tubes_and_global_bound (exact M version).

  Fixes from commented-out version:
  1. Uses global_ambient_bound_generalized with parameter B (for B=3/2 snapped tubes)
  2. K_ambient computed from generalized formula
  3. All imports and namespaces verified

  Contains:
  - dyadic_subset_sset_transfer: subset S-set transfer with constant 18
  - finalize_tubes_and_global_bound: thinning to exact M + ambient bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringMovement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CoveringMovementGeneralized
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.GlobalAmbientComparison
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MainAppendix
open DirecretisedFurstenbergEstimate.SSetBridges (packing_cover_generic)
open DiscretisedFurstenbergEstimate.InductionOnScales
  (weighted_uniformize_cardinalities max_points_in_delta_ball_DyadicTube)
open DyadicCardToNcover (toAffineLine)

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
      have h' : T1 = T2 := by exact InductionOnScales.DyadicTube.eq_iff.mpr h
      exact hne h'
    have h_pos : 0 < (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      rcases h_ne_coord with (h | h)
      · have h' : (T1.a - T2.a : ℤ) ≠ 0 := by omega
        have h'' : 0 < |(T1.a - T2.a : ℤ)| := abs_pos.mpr h'
        have h3 : 0 ≤ (|(T1.b - T2.b : ℤ)| : ℝ) := by positivity
        have h4 : (0 : ℝ) < (|(T1.a - T2.a : ℤ)| : ℝ) := by exact_mod_cast h''
        exact add_pos_of_pos_of_nonneg h4 h3
      · have h' : (T1.b - T2.b : ℤ) ≠ 0 := by omega
        have h'' : 0 < |(T1.b - T2.b : ℤ)| := abs_pos.mpr h'
        have h3 : 0 ≤ (|(T1.a - T2.a : ℤ)| : ℝ) := by positivity
        have h4 : (0 : ℝ) < (|(T1.b - T2.b : ℤ)| : ℝ) := by exact_mod_cast h''
        exact add_pos_of_nonneg_of_pos h3 h4
    have h9 : (1 : ℝ) ≤ (|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ) := by
      exact_mod_cast h_pos
    have h_ge : δ_n * ((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)) ≥ δ_n := by
      nlinarith
    exact h_ge
  -- Packing bound: |B| ≤ 9 * Ncover(δ_n, B)
  have h_pack : (B.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n)) :=
    packing_cover_generic
      (hδ_pos := hδn_pos) (hsep := h_sep) (hK_pos := by norm_num)
      (fun x => max_points_in_delta_ball_DyadicTube hδn_pos B h_sep x)
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
    let a : ENNReal := ENNReal.ofReal C
    let b : ENNReal := (ENNReal.ofReal r) ^ s
    let c_enc := Metric.externalCoveringNumber δ_n.toNNReal (B : Set (DyadicTube n))
    let c : ENNReal := ↑c_enc
    have h_mul : a * b * ((18 : ENNReal) * c) = (18 : ENNReal) * a * b * c := by
      have h1 : a * b * ((18 : ENNReal) * c) = (18 : ENNReal) * (a * b * c) := by
        calc a * b * ((18 : ENNReal) * c)
          = (a * b) * ((18 : ENNReal) * c) := by rfl
        _ = ((18 : ENNReal) * c) * (a * b) := by exact mul_comm (a * b) ((18 : ENNReal) * c)
        _ = (18 : ENNReal) * (c * (a * b)) := by rw [mul_assoc]
        _ = (18 : ENNReal) * ((a * b) * c) := by rw [mul_comm c (a * b)]
        _ = (18 : ENNReal) * (a * b * c) := by rw [mul_assoc a b]
      rw [h1] <;> simp only [mul_assoc]
    have h6 : (18 : ENNReal) * a = ENNReal.ofReal (18 * C) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 18)] <;> norm_cast
    have h_final : a * b * ((18 : ENNReal) * c) = ENNReal.ofReal (18 * C) * b * c := by
      rw [h_mul, h6] <;> simp only [mul_assoc]
    exact h_final

/-- Lemma 7: Finalize tubes — covering mass with exact common cardinality M
    AND global ambient bound.

    Uses weighted_uniformize_cardinalities to thin to a common M = 2^k,
    then transfers S-set property with constant 18*C_raw, which is absorbed
    into δ_n^{-lam} by hypothesis.

    Uses generalized ambient bound with slope parameter B. -/
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
    (B : ℝ) (hB_nonneg : 0 ≤ B) (hB_le_three_halves : B ≤ 3 / 2)
    (h_slope_bound : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.slope| ≤ B)
    (h_intercept_bound : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq → |U.intercept| ≤ 3)
    (h_provenance : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
        dist (toAffineLine U) ℓ ≤ 7 * δ)
    (h_raw_strip : ∀ q hq (U : DyadicTube n), U ∈ rawTubes q hq →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ)) :
    ∃ (squares' : Finset (DyadicSquare n))
      (tubeFam : ∀ (q : DyadicSquare n), q ∈ squares' → Finset (DyadicTube n))
      (T₀ : Finset (DyadicTube n))
      (M : ℕ)
      (K_ambient : ℕ),
      squares' ⊆ squares ∧
      (squares'.card : ℝ) ≥ (squares.card : ℝ) / (K + 1 : ℝ) ∧
      0 < M ∧
      (∃ (k : ℕ), M = 2 ^ k) ∧
      (∀ q hq, (tubeFam q hq).card = M) ∧
      (∀ q hq, IsDeltaSSet (dyadicDelta n) s ((dyadicDelta n) ^ (-lam))
          (tubeFam q hq : Set (DyadicTube n))) ∧
      (∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
          (U.toSet ∩ (q.toSet : Set Plane)).Nonempty) ∧
      (∀ q hq, tubeFam q hq ⊆ T₀) ∧
      (∀ (U : DyadicTube n), U ∈ T₀ ↔
        ∃ (q : DyadicSquare n) (hq : q ∈ squares'), U ∈ tubeFam q hq) ∧
      (∀ (q : DyadicSquare n) (hq' : q ∈ squares') (hq : q ∈ squares),
        tubeFam q hq' ⊆ rawTubes q hq) ∧
      0 < K_ambient ∧
      (T₀.card : ENNReal) ≤
        (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) ∧
      (∀ (q : DyadicSquare n) (hq : q ∈ squares), q ∈ squares' → (rawTubes q hq).card < 2 * M) ∧
      K_ambient ≤ 1000000 ∧
      ((T₀ : Set (DyadicTube n)) = ⋃ (q : DyadicSquare n) (hq : q ∈ squares'), (tubeFam q hq : Set (DyadicTube n))) ∧
      (∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
        -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ)) ∧
      (∀ q hq, ∃ (hqs : q ∈ squares), tubeFam q hq ⊆ rawTubes q hqs) := by
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
  rcases weighted_uniformize_cardinalities
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
  let K_ambient : ℕ := (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1)^2

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
  have h1_output : ∀ q hq, ∃ (hqs : q ∈ squares), tubeFam q hq ⊆ rawTubes q hqs := by
    intro q hq
    exact ⟨h_squares'_sub hq, h1' q hq⟩
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
    have h := h3_card q hq
    rw [h_eq] at h
    exact h
  -- S-set transfer: trimmed family is (δ_n, s, 18*C_raw)-S-set
  have h3_sset18 : ∀ q hq, IsDeltaSSet (dyadicDelta n) s (18 * C_raw)
      (tubeFam q hq : Set (DyadicTube n)) := by
    intro q hq
    have h_card : (rawTubes q (h_squares'_sub hq)).card < 2 * (tubeFam q hq).card := by
      rw [h2 q hq]
      exact h3_card' q hq
    exact dyadic_subset_sset_transfer
      (h1' q hq)
      h_card
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

  -- Global ambient bound using generalized version with B
  have h_slope : ∀ U ∈ T₀, |U.slope| ≤ B := by
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
  have h_prov' : ∀ U ∈ T₀, ∃ ℓ ∈ T_oriented, dist (toAffineLine U) ℓ ≤ (7 : ℝ) * δ := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨q, hq, hU_raw⟩
    have h_raw_eq : rawTubes' q = C_trim q := by simp [rawTubes', hq]
    rw [h_raw_eq] at hU_raw
    exact h_provenance q (h_squares'_sub hq) U (h1' q hq hU_raw)
  have h_prov_wrapper : ∀ U ∈ T₀, ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
      AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ := by
    intro U hU
    rcases h_prov' U hU with ⟨ℓ, hℓ, hdist⟩
    refine ⟨ℓ, hℓ, ?_⟩
    have h1 : AffineLine.dist ℓ (toAffineLine U) = dist ℓ (toAffineLine U) := by rfl
    have h2 : dist ℓ (toAffineLine U) = dist (toAffineLine U) ℓ := dist_comm _ _
    rw [h1, h2]
    exact hdist
  have h_main : (T₀.card : ENNReal) ≤
      ((2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1)^2 : ENNReal) *
      Metric.externalCoveringNumber δ.toNNReal T_oriented :=
    global_ambient_bound_generalized
      (hδ_pos := hδ_pos)
      (hδn_leδ := hδn_leδ)
      (hδ_lt2δn := hδ_lt2δn)
      (hB_nonneg := hB_nonneg)
      (T₀ := T₀)
      (T_oriented := T_oriented)
      (h_slope_bound := h_slope)
      (h_intercept_bound := h_intercept)
      (h_provenance := h_prov_wrapper)
  have h_ambient : (T₀.card : ENNReal) ≤
      (K_ambient : ENNReal) * Metric.externalCoveringNumber δ.toNNReal T_oriented := by
    have hK_def : (K_ambient : ENNReal) =
        ((2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1)^2 : ENNReal) := by
      simp [K_ambient] <;> norm_cast
    rw [hK_def]
    exact h_main

  have h3_card'' : ∀ (q : DyadicSquare n) (hq : q ∈ squares), q ∈ squares' → (rawTubes q hq).card < 2 * M := by
    intro q hq hq'
    have h_eq : rawTubes q hq = rawTubes q (h_squares'_sub hq') := by rfl
    rw [h_eq]
    exact h3_card' q hq'

  have hKamb_bound : K_ambient ≤ 1000000 := by
    have h1 : 4 * (4 + B + 3 * B^2) * (8 : ℝ) ≤ 392 := by
      have h2 : B ≤ 3 / 2 := hB_le_three_halves
      have h3 : 0 ≤ B := hB_nonneg
      nlinarith [sq_nonneg (B - 3 / 2)]
    have h4 : Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) ≤ 392 := by
      rw [Nat.ceil_le]
      exact h1
    have h5 : 2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1 ≤ 785 := by
      omega
    have h6 : (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1)^2 ≤ 1000000 := by
      have h7 : 2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1 ≤ 785 := h5
      have h8 : (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (8 : ℝ)) + 1)^2 ≤ 785^2 := by
        gcongr
      have h9 : 785^2 ≤ 1000000 := by norm_num
      linarith
    simpa [K_ambient] using h6

  have hT0_eq_union : (T₀ : Set (DyadicTube n)) = ⋃ (q : DyadicSquare n) (hq : q ∈ squares'), (tubeFam q hq : Set (DyadicTube n)) := by
    ext U
    simp only [T₀, Finset.mem_coe, Finset.mem_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, hU⟩
      have h_raw_eq : rawTubes' q = C_trim q := by simp [rawTubes', hq]
      rw [h_raw_eq] at hU
      exact ⟨q, hq, hU⟩
    · rintro ⟨q, hq, hU⟩
      have h_raw_eq : rawTubes' q = C_trim q := by simp [rawTubes', hq]
      exact ⟨q, hq, by rw [h_raw_eq]; exact hU⟩

  have h_tube_strip : ∀ q hq (U : DyadicTube n), U ∈ tubeFam q hq →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ) := by
    intro q hq U hU
    have h_sub : U ∈ rawTubes q (h_squares'_sub hq) := h1' q hq hU
    exact h_raw_strip q (h_squares'_sub hq) U h_sub

  have hT0_mem_iff : ∀ (U : DyadicTube n), U ∈ T₀ ↔
      ∃ (q : DyadicSquare n) (hq : q ∈ squares'), U ∈ tubeFam q hq := by
    intro U
    change U ∈ (T₀ : Set (DyadicTube n)) ↔ _
    rw [hT0_eq_union]
    simp

  exact ⟨squares', tubeFam, T₀, M, K_ambient,
    h_squares'_sub, h_squares'_card, hM_pos, ⟨k, hM_eq⟩, h2, h3, h4, h5,
    hT0_mem_iff, fun q hq' hq => h1' q hq', hK_pos, h_ambient, h3_card'',
    hKamb_bound, hT0_eq_union, h_tube_strip, h1_output⟩

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
