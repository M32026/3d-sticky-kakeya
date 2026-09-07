module

/-
  Source-to-NiceConfiguration bridge — inner bridge lemma.

  Extracted from SourceToNiceConfiguration_hmass2.lean to reduce
  per-file compilation time.

  Contains `bridge_inner`: the core bridge for a fixed δ assumed
  sufficiently small. Produces a NiceConfiguration with retention,
  mass, multiplicity, and ambient bounds.

  Depends on BridgeHelpers for standalone utility lemmas.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CardinalityLowerBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.ContinuousExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.GlobalOrientationPartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.SnapTransferAll
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CoveringMovementGeneralized
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Lemma7Repair
public import MyLeanRepo.DiscretisedFurstenbergEstimate.NearbyDyadicTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.BridgeMassTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.GeometricAndExternal
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Section9.BridgeHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TubeCapacityPruningMain
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate (AffineLine)
open DirecretisedFurstenbergEstimate.MainAppendix (affineLine_packing_constant)
open DirecretisedFurstenbergEstimate.MainAppendix (affineLine_packing_constant_pos)
open CoordinatePartition
open DyadicCardToNcover (toAffineLine)
open DiscretisedFurstenbergEstimate.FrontEndLemmas (dyadicTube_capacity_pruning)

/-- Inner bridge for a fixed δ assumed sufficiently small. -/
lemma bridge_inner
    (δ s t : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1) (hst : s < t) (hδ_lt_one : δ < 1)
    (C_P C_T : ℝ) (hCP_pos : 0 < C_P) (hCT_pos : 0 < C_T)
    (P : Set BridgePlane) (hP_bdd : P ⊆ Metric.closedBall 0 1)
    (hP_sset : IsDeltaSSet δ t C_P P)
    (T : Set AffineLine) (hT_bdd : Bornology.IsBounded T)
    (Tp : ∀ (p : BridgePlane), p ∈ P → Set AffineLine)
    (hTp_sub : ∀ p hp, Tp p hp ⊆ T)
    (hTp_sset : ∀ p hp, IsDeltaSSet δ s C_T (Tp p hp))
    (hTp_near : ∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1)
    (hTp_bdd : ∀ p hp, ∀ ℓ ∈ Tp p hp, ℓ.offset ∈ Metric.closedBall 0 2)
    (reserved_budget : ℝ) (hbudget_pos : 0 < reserved_budget)
    (lam : ℝ) (hlam_pos : 0 < lam)
    (ε_tube : ℝ) (hε_tube_pos : 0 < ε_tube) (hε_tube_lt_lam : ε_tube < lam)
    (hCT_bound : C_T ≤ δ ^ (-ε_tube))
    (hδ_le_one : δ ≤ 1)
    (h_absorb_snap : ∀ (n : ℕ), dyadicDelta n ≤ δ → δ < 2 * dyadicDelta n →
      (3721 * (affineLine_packing_constant : ℝ)^5 * (58 : ℝ)^s * 2 *
        max 1 ((affineLine_packing_constant : ℝ) * C_T) * (affineLine_packing_constant : ℝ))
        ≤ (dyadicDelta n)^(-lam))
    (h_absorb_snap18 : ∀ (n : ℕ), dyadicDelta n ≤ δ → δ < 2 * dyadicDelta n →
      (9000 : ℝ) * (3721 * (affineLine_packing_constant : ℝ)^5 * (58 : ℝ)^s * 2 *
        max 1 ((affineLine_packing_constant : ℝ) * C_T) * (affineLine_packing_constant : ℝ))
        ≤ (dyadicDelta n)^(-lam))
    (h_absorb_ambient : ∀ (n : ℕ), dyadicDelta n ≤ δ → δ < 2 * dyadicDelta n →
      (1000000 : ℝ) ≤ (dyadicDelta n)^(-reserved_budget / 3))
    (h_K_log_absorb : ∀ (n : ℕ), dyadicDelta n ≤ δ → δ < 2 * dyadicDelta n →
      (2 * (n : ℝ) + 10) ≤ (dyadicDelta n)^(-reserved_budget / 24))
    (hδ_slope : δ ^ (reserved_budget / 6) ≤ 1 / 81) :
    ∃ (n : ℕ) (M : ℕ)
      (config : CombiningTheorem.NiceConfiguration n s ((dyadicDelta n) ^ (-lam)) M)
      (P_ret P_oriented : Set Plane)
      (T_oriented : Set AffineLine)
      (swapped : Bool)
      (ρ_mass ρ_M ρ_T : ℝ),
      dyadicDelta n ≤ δ ∧ δ < 2 * dyadicDelta n ∧
      0 ≤ ρ_mass ∧ 0 ≤ ρ_M ∧ 0 ≤ ρ_T ∧
      ρ_mass + ρ_M + ρ_T ≤ reserved_budget ∧
      0 < M ∧
      (∃ (k : ℕ), M = 2^k) ∧
      P_ret ⊆ P ∧
      (swapped = false → P_oriented ⊆ P_ret ∧ T_oriented = T) ∧
      (swapped = true → P_oriented ⊆ swapCoords '' P_ret ∧ T_oriented = swapLine '' T) ∧
      (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) =
        (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ∧
      (∀ q ∈ config.P₀, (q.toSet ∩ P_oriented).Nonempty) ∧
      P_oriented ⊆ config.pointSet ∧
      (Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet : ENNReal) ≥
        ENNReal.ofReal ((dyadicDelta n) ^ ρ_mass) *
          (Metric.externalCoveringNumber (dyadicDelta n).toNNReal P : ENNReal) ∧
      (M : ℝ) ≥ (dyadicDelta n) ^ (-s + lam + ρ_M) ∧
      (M : ℝ) ≤ 28 * (dyadicDelta n) ^ (-s) ∧
      (config.T₀.card : ENNReal) ≤
        ENNReal.ofReal ((dyadicDelta n) ^ (-ρ_T)) *
          (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ∧
      (∀ T ∈ config.T₀, -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) ∧
      (∀ q (hq : q ∈ config.P₀) (T : DyadicTube n), T ∈ config.tubeFamily q hq → |T.intercept| ≤ 3) ∧
      config.T₀.card ≤ 12 * 16 ^ n ∧
      (∀ (U : DyadicTube n), U ∈ config.T₀ →
        ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
          dist (toAffineLine U) ℓ ≤ 7 * δ) := by
  -- Choose loss exponents
  set ρ_mass := 5 * reserved_budget / 12 with hρ_mass_def
  set ρ_M := reserved_budget / 6 with hρ_M_def
  set ρ_T := reserved_budget / 3 with hρ_T_def
  have hbudget : ρ_mass + ρ_M + ρ_T ≤ reserved_budget := by
    simp [hρ_mass_def, hρ_M_def, hρ_T_def] <;> linarith
  have hρ_mass_nonneg : 0 ≤ ρ_mass := by positivity
  have hρ_M_nonneg : 0 ≤ ρ_M := by positivity
  have hρ_T_nonneg : 0 ≤ ρ_T := by positivity
  set ρ_slope := reserved_budget / 6 with hρ_slope_def
  have hρ_slope_nonneg : 0 ≤ ρ_slope := by positivity
  have hδ_pos : 0 < δ := hP_sset.2.1

  -- Step 1: Continuous extraction
  have hTp_finite_bdd : ∀ p hp, Bornology.IsBounded (Tp p hp) := by
    intro p hp
    exact Bornology.IsBounded.subset hT_bdd (hTp_sub p hp)
  rcases ContinuousExtraction.continuous_to_finite_extraction Tp hTp_sset hTp_finite_bdd hTp_near hTp_bdd
    with ⟨Fp, hF_sub_tp, hF_nonempty, hF_sep, hF_sset_raw, hF_card, hF_near, hF_offset⟩

  -- Fiber subsets of T (needed for global_slope_partition)
  have hF_sub : ∀ p hp, (Fp p hp : Set AffineLine) ⊆ T := by
    intro p hp
    have h1 : (Fp p hp : Set AffineLine) ⊆ Tp p hp := hF_sub_tp p hp
    have h2 : Tp p hp ⊆ T := hTp_sub p hp
    exact Set.Subset.trans h1 h2

  -- Define adjusted C_T' so that C_T' * Kpack = max 1 (Kpack * C_T)
  let Kpack : ℝ := (affineLine_packing_constant : ℝ)
  have hKpack_pos : 0 < Kpack := Nat.cast_pos.mpr affineLine_packing_constant_pos
  let C_F : ℝ := max 1 (Kpack * C_T)
  let C_T' : ℝ := C_F / Kpack
  have hC_T'_pos : 0 < C_T' := by
    have h1 : 0 < C_F := by
      have h2 : 0 < (1 : ℝ) := by norm_num
      exact lt_of_lt_of_le h2 (le_max_left 1 (Kpack * C_T))
    positivity
  have hC_F_eq : C_T' * Kpack = C_F := by
    simp [C_T'] <;> field_simp [hKpack_pos.ne'] <;> ring
  have hF_sset : ∀ p hp, IsDeltaSSet δ s (C_T' * Kpack) (Fp p hp : Set AffineLine) := by
    intro p hp
    rcases hF_sset_raw p hp with ⟨hne, hδ, hC1, hs, hmain⟩
    have hC_pos : 0 < C_T' * Kpack := by positivity
    refine ⟨hne, hδ, hC_pos, hs, fun x r hr => ?_⟩
    have h_eq : C_T' * Kpack = max 1 (Kpack * C_T) := by
      rw [hC_F_eq] <;> rfl
    rw [h_eq]
    exact hmain x r hr

  -- Step 2: Lemma 3 — global slope partition (using C_T' instead of C_T)
  have hδ_slope' : δ ^ ρ_slope ≤ 1 / 2 := by
    have h1 : ρ_slope ≥ reserved_budget / 6 := by
      dsimp only [ρ_slope, hρ_slope_def] <;> linarith
    have h2 : δ ^ ρ_slope ≤ δ ^ (reserved_budget / 6) := by
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one (by linarith)
    have h3 : δ ^ (reserved_budget / 6) ≤ 1 / 81 := hδ_slope
    have h4 : (1 / 81 : ℝ) ≤ (1 / 2 : ℝ) := by norm_num
    exact le_trans (le_trans h2 h3) h4
  rcases global_slope_partition δ s C_T' hs_pos hC_T'_pos hδ_pos P T Fp
      hF_sub hF_sset hF_sep hF_near ρ_slope hρ_slope_nonneg hδ_slope'
    with ⟨swapped, P_ret, P_oriented, T_oriented, F_oriented, c_slope,
      hc_slope_pos, _hc_slope_eq, hP_ret_sub, hswap_false, hswap_true, hT_oriented_ncover,
      hF_oriented_sub, hF_oriented_sset, hF_oriented_v0, hF_oriented_slope,
      hF_oriented_near, hc_slope_lower, hP_oriented_mass⟩

  -- Step 3: Choose dyadic scale n
  rcases choose_dyadic_scale δ hδ_pos hδ_le_one with ⟨n, hδn_leδ, hδ_lt2δn⟩
  let δ_n := dyadicDelta n
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδn_lt_one : δ_n < 1 := lt_of_le_of_lt hδn_leδ hδ_lt_one

  -- Step 4: Boundedness and nonemptiness of P_oriented
  have hP_ret_sub_ball : P_ret ⊆ Metric.closedBall 0 1 := Set.Subset.trans hP_ret_sub hP_bdd
  have hP_oriented_bdd : Bornology.IsBounded P_oriented := by
    by_cases hsw : swapped
    · have h : P_oriented = swapCoords '' P_ret := (hswap_true hsw).1
      rw [h]
      have h_img_sub : swapCoords '' P_ret ⊆ Metric.closedBall 0 1 := by
        intro z hz
        rcases hz with ⟨p, hp, rfl⟩
        have hpin : p ∈ Metric.closedBall 0 1 := hP_ret_sub_ball hp
        have hnorm : ‖swapCoords p‖ = ‖p‖ := swapCoordsLI.norm_map p
        simpa [Metric.mem_closedBall, hnorm] using hpin
      exact Bornology.IsBounded.subset Metric.isBounded_closedBall h_img_sub
    · have h : P_oriented = P_ret := (hswap_false (by simpa using hsw)).1
      rw [h]
      exact Bornology.IsBounded.subset (Metric.isBounded_closedBall) hP_ret_sub_ball
  have hP_oriented_nonempty : P_oriented.Nonempty := by
    have hP_nonempty : P.Nonempty := hP_sset.1
    have hcov_pos : 0 < (Metric.externalCoveringNumber δ.toNNReal P_oriented : ENNReal) := by
      have hpos : 0 < ENNReal.ofReal c_slope * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        apply ENNReal.mul_pos
        · exact ne_of_gt (ENNReal.ofReal_pos.mpr hc_slope_pos)
        · have hne : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≠ 0 := by
            have h : 0 < (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
              exact_mod_cast Metric.externalCoveringNumber_pos_iff.mpr hP_nonempty
            exact ne_of_gt h
          exact hne
      exact lt_of_lt_of_le hpos hP_oriented_mass
    have h : (Metric.externalCoveringNumber δ.toNNReal P_oriented : ENNReal) ≠ 0 := ne_of_gt hcov_pos
    have h' : P_oriented.Nonempty := by
      rw [← Metric.externalCoveringNumber_pos_iff]
      exact_mod_cast hcov_pos
    exact h'

  -- Cover P_oriented by dyadic squares
  rcases cover_by_dyadic_squares hP_oriented_bdd with ⟨squares_raw, hcover_raw⟩
  let squares : Finset (DyadicSquare n) :=
    squares_raw.filter (fun q => (P_oriented ∩ (q.toSet : Set Plane)).Nonempty)
  have hcover : P_oriented ⊆ ⋃ q ∈ (squares : Set (DyadicSquare n)), (q.toSet : Set Plane) := by
    intro p hp
    have h1 : p ∈ ⋃ q ∈ (squares_raw : Set (DyadicSquare n)), (q.toSet : Set Plane) := hcover_raw hp
    rcases Set.mem_iUnion₂.mp h1 with ⟨q, hq, hq2⟩
    have h_inter : (P_oriented ∩ (q.toSet : Set Plane)).Nonempty := ⟨p, hp, hq2⟩
    have hq' : q ∈ squares := by
      simp only [squares, Finset.mem_filter] <;> exact ⟨hq, h_inter⟩
    exact Set.mem_iUnion₂.mpr ⟨q, hq', hq2⟩
  have hsquares_nonempty : squares.Nonempty := by
    rcases hP_oriented_nonempty with ⟨p, hp⟩
    have h1 := hcover hp
    rcases Set.mem_iUnion₂.mp h1 with ⟨q, hq, _⟩
    exact ⟨q, hq⟩

  -- Choose representative points in each square
  choose rep hrep using fun (q : DyadicSquare n) (hq : q ∈ squares) =>
    show (P_oriented ∩ (q.toSet : Set Plane)).Nonempty from by
      simp only [squares, Finset.mem_filter] at hq <;> exact hq.2
  let rep' : (q : DyadicSquare n) → q ∈ squares → BridgePlane :=
    fun q hq => rep q hq
  have hrep' : ∀ q hq, rep' q hq ∈ P_oriented ∩ (q.toSet : Set Plane) := by
    intro q hq
    exact hrep q hq

  -- P_oriented ⊆ closedBall 0 1
  have hP_oriented_sub_ball : P_oriented ⊆ Metric.closedBall 0 1 := by
    by_cases hsw : swapped
    · have h : P_oriented = swapCoords '' P_ret := (hswap_true hsw).1
      rw [h]
      intro z hz
      rcases hz with ⟨p, hp, rfl⟩
      have hpin : p ∈ Metric.closedBall 0 1 := hP_ret_sub_ball hp
      have hnorm : ‖swapCoords p‖ = ‖p‖ :=
        swapCoordsLI.norm_map p
      have hdist : dist (swapCoords p) 0 = ‖swapCoords p‖ := by simp
      have hpin' : ‖p‖ ≤ 1 := by simpa [dist_eq_norm] using hpin
      rw [Metric.mem_closedBall]
      rw [hdist, hnorm]
      exact hpin'
    · have h : P_oriented = P_ret := (hswap_false (by simpa using hsw)).1
      rw [h] <;> exact hP_ret_sub_ball

  -- Step 5: Lemma 4 — snap oriented fibers to dyadic tubes (bacon's SnapTransferAll)
  let C_in : ℝ := 2 * C_T' * Kpack^2
  have hC_in_pos : 0 < C_in := by
    have hKpos : 0 < (affineLine_packing_constant : ℝ) := by exact_mod_cast affineLine_packing_constant_pos
    positivity
  have hs_nonneg : 0 ≤ s := by linarith [hs_pos]
  have hC_in_eq : C_in = C_T' * Kpack * 2 * Kpack := by
    simp [C_in] <;> ring
  have hF_oriented_sset' : ∀ p hp, IsDeltaSSet δ s C_in (F_oriented p hp : Set AffineLine) := by
    intro p hp
    have h := hF_oriented_sset p hp
    rw [hC_in_eq] at *
    exact h
  rcases snap_transfer_all
      (hδ_pos := hδ_pos) (hδ_le_one := hδ_le_one)
      (hδn_pos := hδn_pos) (hδn_leδ := hδn_leδ) (hδ_le2δn := by linarith)
      (hs_nonneg := hs_nonneg) (hC_in_pos := hC_in_pos)
      (P' := P_oriented) (F' := F_oriented)
      (hF'_sset := hF_oriented_sset') (hF'_v0 := hF_oriented_v0)
      (hF'_slope := hF_oriented_slope) (hF'_near := hF_oriented_near)
      (hP'_bdd := hP_oriented_sub_ball)
    with ⟨rawTubes_point, hraw_eq, hraw_sset, hraw_prov, hraw_intersect, hraw_slope,
      hraw_intercept, hraw_strip⟩

  -- Map point-indexed raw tubes to square-indexed
  let rawTubes_square (q : DyadicSquare n) (hq : q ∈ squares) : Finset (DyadicTube n) :=
    rawTubes_point (rep' q hq) (hrep' q hq).1
  let K_snap : ℝ := 3721 * (affineLine_packing_constant : ℝ)^5 * (58 : ℝ)^s
  let C_raw : ℝ := K_snap * C_in
  have hC_raw_pos : 0 < C_raw := by
    have hKpos : 0 < (affineLine_packing_constant : ℝ) := by exact_mod_cast affineLine_packing_constant_pos
    positivity
  have hraw_square_sset : ∀ q hq, IsDeltaSSet δ_n s C_raw (rawTubes_square q hq : Set (DyadicTube n)) := by
    intro q hq
    exact hraw_sset (rep' q hq) (hrep' q hq).1
  have hraw_square_prov : ∀ q hq (U : DyadicTube n), U ∈ rawTubes_square q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧ AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ := by
    intro q hq U hU
    rcases hraw_prov (rep' q hq) (hrep' q hq).1 U hU with ⟨ℓ, hℓ_in_F, hdist⟩
    exact ⟨ℓ, hF_oriented_sub (rep' q hq) (hrep' q hq).1 hℓ_in_F, hdist⟩
  have hraw_square_slope : ∀ q hq (U : DyadicTube n), U ∈ rawTubes_square q hq → |U.slope| ≤ 3 / 2 := by
    intro q hq U hU
    exact hraw_slope (rep' q hq) (hrep' q hq).1 U hU
  have hraw_square_intercept : ∀ q hq (U : DyadicTube n), U ∈ rawTubes_square q hq → |U.intercept| ≤ 3 := by
    intro q hq U hU
    exact hraw_intercept (rep' q hq) (hrep' q hq).1 U hU
  have hraw_square_strip : ∀ q hq (U : DyadicTube n), U ∈ rawTubes_square q hq →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ) := by
    intro q hq U hU
    exact hraw_strip (rep' q hq) (hrep' q hq).1 U hU
  have hraw_square_intersect : ∀ q hq (Ttube : DyadicTube n), Ttube ∈ rawTubes_square q hq →
      (Ttube.toSet ∩ (q.toSet : Set Plane)).Nonempty := by
    intro q hq Ttube hT
    let p := rep' q hq
    have hp_in_P : p ∈ P_oriented := (hrep' q hq).1
    have hp_in_Q : p ∈ (q.toSet : Set Plane) := (hrep' q hq).2
    have h_eq : (rawTubes_square q hq : Set (DyadicTube n)) =
        (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) ''
          (F_oriented p hp_in_P : Set AffineLine) := by
      exact hraw_eq p hp_in_P
    have hT' : Ttube ∈ (rawTubes_square q hq : Set (DyadicTube n)) := hT
    rw [h_eq] at hT'
    rcases hT' with ⟨ℓ, hℓ, rfl⟩
    have h1 : p ∈ (LegacyRound.snapToTubeThroughPoint n ℓ p).toSet :=
      LegacyRound.snapToTubeThroughPoint_incidence (n := n) (ℓ := ℓ) (p := p)
    exact ⟨p, h1, hp_in_Q⟩

  -- Step 6: Cardinality lower bound
  have h_card_lower : ∀ q hq, (rawTubes_square q hq).card ≥ (C_raw * δ_n^s)⁻¹ := by
    intro q hq
    have h1 : ENNReal.ofReal ((C_raw * δ_n^s)⁻¹) ≤
        (Metric.externalCoveringNumber δ_n.toNNReal (rawTubes_square q hq : Set (DyadicTube n)) : ENNReal) :=
      ImprovedIncidenceAssembly.sset_ncover_lower_bound (hraw_square_sset q hq)
    have hcover_self : Metric.IsCover δ_n.toNNReal (rawTubes_square q hq : Set (DyadicTube n)) (rawTubes_square q hq : Set (DyadicTube n)) := by
      intro x hx; exact ⟨x, hx, by simp [hδn_pos.le]⟩
    have h2 : (Metric.externalCoveringNumber δ_n.toNNReal (rawTubes_square q hq : Set (DyadicTube n)) : ENNReal) ≤
        (rawTubes_square q hq).card := by
      exact_mod_cast hcover_self.externalCoveringNumber_le_encard
    have h3 : ENNReal.ofReal ((C_raw * δ_n^s)⁻¹) ≤ (rawTubes_square q hq).card := le_trans h1 h2
    have h4 : 0 ≤ (C_raw * δ_n^s)⁻¹ := by positivity
    exact_mod_cast h3

  -- Step 6b: Capacity pruning — normalize each square's tube family to ≤ 28 * δ_n^{-s}
  let C_prune : ℝ := 125 * (2 : ℝ)^(s + 1) * C_raw
  have hC_prune_pos : 0 < C_prune := by positivity
  have h2pow_le : (2 : ℝ)^(s + 1) ≤ 4 := by
    have h : s + 1 ≤ 2 := by linarith
    have h' : (2 : ℝ)^(s + 1) ≤ (2 : ℝ)^(2 : ℝ) := by
      gcongr
      <;> norm_num <;> linarith
    norm_num at h' ⊢
    exact h'
  choose normalizedTubes hnorm_sub hnorm_upper hnorm_lower hnorm_sset using
    fun (q : DyadicSquare n) (hq : q ∈ squares) =>
      dyadicTube_capacity_pruning
        hs_pos hs_lt_one δ_n hδn_pos hδn_lt_one rfl
        (rawTubes_square q hq)
        (hraw_square_sset q hq)
        (hraw_square_slope q hq)
        (hraw_square_intercept q hq)
  let normalizedTubes_square (q : DyadicSquare n) (hq : q ∈ squares) : Finset (DyadicTube n) :=
    normalizedTubes q hq
  have hnorm_square_sub : ∀ q hq, normalizedTubes_square q hq ⊆ rawTubes_square q hq :=
    fun q hq => hnorm_sub q hq
  have hnorm_square_upper : ∀ q hq, ((normalizedTubes_square q hq).card : ℝ) ≤ 28 * δ_n^(-s) :=
    fun q hq => hnorm_upper q hq
  have hnorm_square_sset : ∀ q hq, IsDeltaSSet δ_n s C_prune (normalizedTubes_square q hq : Set (DyadicTube n)) :=
    fun q hq => hnorm_sset q hq
  have hnorm_square_intersect : ∀ q hq (U : DyadicTube n), U ∈ normalizedTubes_square q hq →
      (U.toSet ∩ (q.toSet : Set Plane)).Nonempty :=
    fun q hq U hU => hraw_square_intersect q hq U (hnorm_square_sub q hq hU)
  have hnorm_square_slope : ∀ q hq (U : DyadicTube n), U ∈ normalizedTubes_square q hq → |U.slope| ≤ 3 / 2 :=
    fun q hq U hU => hraw_square_slope q hq U (hnorm_square_sub q hq hU)
  have hnorm_square_intercept : ∀ q hq (U : DyadicTube n), U ∈ normalizedTubes_square q hq → |U.intercept| ≤ 3 :=
    fun q hq U hU => hraw_square_intercept q hq U (hnorm_square_sub q hq hU)
  have hnorm_square_strip : ∀ q hq (U : DyadicTube n), U ∈ normalizedTubes_square q hq →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ) :=
    fun q hq U hU => hraw_square_strip q hq U (hnorm_square_sub q hq hU)
  have hnorm_square_prov : ∀ q hq (U : DyadicTube n), U ∈ normalizedTubes_square q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧ dist (toAffineLine U) ℓ ≤ 7 * δ := by
    intro q hq U hU
    rcases hraw_square_prov q hq U (hnorm_square_sub q hq hU) with ⟨ℓ, hℓ, hdist⟩
    have h_eq : AffineLine.dist ℓ (toAffineLine U) = dist (toAffineLine U) ℓ := by
      have h1 : AffineLine.dist ℓ (toAffineLine U) = dist ℓ (toAffineLine U) := by rfl
      rw [h1, dist_comm]
    exact ⟨ℓ, hℓ, h_eq ▸ hdist⟩

  -- Step 7: Exact-M Lemma 7 (repo version with square trimming)
  -- Use logarithmic K bound: card ≤ 2^(2n+7), so K = 2*n + 7
  let K : ℕ := 2 * n + 7
  have hK : ∀ q hq, (normalizedTubes_square q hq).card ≤ 2^K := by
    intro q hq
    have h_sub : normalizedTubes_square q hq ⊆ rawTubes_square q hq := hnorm_square_sub q hq
    have h_bound : (rawTubes_square q hq).card ≤ 2 ^ (2 * n + 7) :=
      bounded_dyadic_tubes_card
        (fun U hU => hraw_square_slope q hq U hU)
        (fun U hU => hraw_square_intercept q hq U hU)
    have h_card_le : (normalizedTubes_square q hq).card ≤ (rawTubes_square q hq).card :=
      Finset.card_le_card h_sub
    simpa [K] using le_trans h_card_le h_bound
  -- Absorption for 18*C_prune (needed by dyadic_subset_sset_transfer)
  have hC_raw_eq : C_raw = 3721 * Kpack^5 * (58 : ℝ)^s * 2 * max 1 (Kpack * C_T) * Kpack := by
    dsimp only [C_raw, K_snap, C_in, C_T', C_F]
    field_simp [hKpack_pos.ne'] <;> ring
  have h_absorb18 : 18 * C_prune ≤ δ_n ^ (-lam) := by
    have h1 : 18 * C_prune ≤ 9000 * C_raw := by
      dsimp only [C_prune]
      have h2 : (2 : ℝ)^(s + 1) ≤ 4 := h2pow_le
      nlinarith
    have h3 : 9000 * C_raw ≤ δ_n ^ (-lam) := by
      rw [hC_raw_eq]
      exact h_absorb_snap18 n hδn_leδ hδ_lt2δn
    exact le_trans h1 h3
  rcases finalize_tubes_and_global_bound
      (hδ_pos := hδ_pos) (hδn_pos := hδn_pos) (hδn_leδ := hδn_leδ) (hδ_lt2δn := hδ_lt2δn)
      squares normalizedTubes_square C_prune hC_prune_pos hnorm_square_sset K hK
      lam hlam_pos h_absorb18
      hnorm_square_intersect T_oriented
      (3 / 2 : ℝ) (by norm_num) (by norm_num)
      hnorm_square_slope hnorm_square_intercept
      (fun q hq U hU => hnorm_square_prov q hq U hU)
      hnorm_square_strip
    with ⟨squares', tubeFam, T₀, M, K_ambient,
      hsquares'_sub, hretention, hM_pos', hM_dyadic, huniform, htube_sset,
      htube_intersect, htube_in_T0, hT0_mem_iff, htube_sub_raw, hK_pos', hT0_bound,
      hraw_card_lt, hKamb_bound, _, htube_strip, _⟩

  -- Define retained point set (points covered by trimmed squares)
  let P_retained : Set Plane := P_oriented ∩ ⋃ q ∈ (squares' : Set (DyadicSquare n)), (q.toSet : Set Plane)

  -- Assemble NiceConfiguration with exact M
  have hconfig_bounded : Bornology.IsBounded (⋃ q ∈ (squares' : Set (DyadicSquare n)), (q.toSet : Set Plane)) := by
    exact (Bornology.isBounded_biUnion_finset squares').mpr (fun q _ => DyadicSquare.toSet_isBounded q)
  let config : CombiningTheorem.NiceConfiguration n s ((dyadicDelta n) ^ (-lam)) M :=
    { P₀ := squares'
      T₀ := T₀
      tubeFamily := tubeFam
      h_subset := htube_in_T0
      h_size := huniform
      h_delta_s_set := htube_sset
      h_intersect := htube_intersect
      h_tube_parameters := by
        exact Finset.finite_toSet _ |>.isBounded
      h_bounded := hconfig_bounded }

  -- P_retained ⊆ config.pointSet is trivial
  have hmass1 : P_retained ⊆ config.pointSet := by
    intro p hp
    exact hp.2

  -- Every config square contains a point of P_retained
  have h_each_square : ∀ q ∈ config.P₀, (q.toSet ∩ P_retained).Nonempty := by
    intro q hq
    have hq' : q ∈ squares' := by simpa [config] using hq
    have hq_in_squares : q ∈ squares := hsquares'_sub hq'
    have h_inter : (P_oriented ∩ (q.toSet : Set Plane)).Nonempty := by
      simp only [squares, Finset.mem_filter] at hq_in_squares
      exact hq_in_squares.2
    rcases h_inter with ⟨p, hp_in_Poriented, hp_in_square⟩
    have hp_in_union : p ∈ ⋃ q' ∈ (squares' : Set (DyadicSquare n)), (q'.toSet : Set Plane) := by
      exact Set.mem_iUnion₂.mpr ⟨q, hq', hp_in_square⟩
    have hp_in_retained : p ∈ P_retained := by
      exact ⟨hp_in_Poriented, hp_in_union⟩
    exact ⟨p, hp_in_square, hp_in_retained⟩

  -- Mass bound: Ncover(config.pointSet) ≥ δ_n^{ρ_mass} * Ncover(P)
  -- Proof chain:
  -- 1. Factor-9: squares'.card ≤ 9 * Ncover(δ_n, config.pointSet)
  -- 2. Retention: squares.card ≤ (K+1) * squares'.card
  -- 3. Cover: Ncover(δ, P_oriented) ≤ squares.card
  -- 4. Slope: c_slope * Ncover(δ, P) ≤ Ncover(δ, P_oriented)
  -- 5. Doubling: Ncover(δ_n, P) ≤ 9 * Ncover(δ, P)
  -- Combine: c_slope * Ncover(δ_n, P) ≤ 81*(K+1) * Ncover(config.pointSet)
  -- Absorb: 81*(K+1) * δ_n^ρ_mass ≤ c_slope
  have hmass2 : Ncover' δ_n config.pointSet ≥
      ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P := by
    -- Step 1: Factor-9 packing for squares'
    have h1 : (squares'.card : ENNReal) ≤ (9 : ENNReal) * Ncover' δ_n config.pointSet :=
      local_finset_squares_ncover_lower squares'
    -- Step 2: Retention, rearranged
    have h2 : (squares.card : ENNReal) ≤ ((K + 1 : ENNReal) * (squares'.card : ENNReal)) := by
      have h21 : (squares'.card : ℝ) ≥ (squares.card : ℝ) / (K + 1 : ℝ) := hretention
      have hpos : 0 < (K + 1 : ℝ) := by positivity
      have h_eq : (K + 1 : ℝ) * ((squares.card : ℝ) / (K + 1 : ℝ)) = (squares.card : ℝ) := by
        field_simp [hpos.ne'] <;> ring
      have h22 : (squares.card : ℝ) ≤ (K + 1 : ℝ) * (squares'.card : ℝ) := by
        calc (squares.card : ℝ)
          = (K + 1 : ℝ) * ((squares.card : ℝ) / (K + 1 : ℝ)) := h_eq.symm
        _ ≤ (K + 1 : ℝ) * (squares'.card : ℝ) := by gcongr
      exact_mod_cast h22
    -- Step 3: Each square is covered by one δ-ball, so Ncover(δ, P_oriented) ≤ squares.card
    have h_square_cover : ∀ (q : DyadicSquare n), ∃ (c : Plane),
        (q.toSet : Set Plane) ⊆ Metric.closedBall c δ := by
      intro q
      let c : Plane := WithLp.toLp (2 : ENNReal) fun i : Fin 2 =>
        if i = 0 then ((q.i : ℝ) + 1 / 2) * δ_n else ((q.j : ℝ) + 1 / 2) * δ_n
      refine ⟨c, ?_⟩
      intro x hx
      have h0 : (q.i : ℝ) * δ_n ≤ x 0 := hx.1
      have h1 : x 0 < ((q.i : ℝ) + 1) * δ_n := hx.2.1
      have h2 : (q.j : ℝ) * δ_n ≤ x 1 := hx.2.2.1
      have h3 : x 1 < ((q.j : ℝ) + 1) * δ_n := hx.2.2.2
      have h4 : |x 0 - c 0| ≤ δ_n / 2 := by
        dsimp only [c]
        have h5 : x 0 - (((q.i : ℝ) + 1 / 2) * δ_n) ≤ δ_n / 2 := by linarith
        have h6 : -(δ_n / 2) ≤ x 0 - (((q.i : ℝ) + 1 / 2) * δ_n) := by linarith
        exact abs_le.mpr ⟨h6, h5⟩
      have h7 : |x 1 - c 1| ≤ δ_n / 2 := by
        dsimp only [c]
        have h8 : x 1 - (((q.j : ℝ) + 1 / 2) * δ_n) ≤ δ_n / 2 := by linarith
        have h9 : -(δ_n / 2) ≤ x 1 - (((q.j : ℝ) + 1 / 2) * δ_n) := by linarith
        exact abs_le.mpr ⟨h9, h8⟩
      have h10 : dist x c ≤ δ_n := by
        have h11 : dist x c = ‖x - c‖ := by rfl
        rw [h11]
        have h12 : ‖x - c‖ ^ 2 = (x 0 - c 0)^2 + (x 1 - c 1)^2 := by
          have h121 : ‖x - c‖ = Real.sqrt ((x 0 - c 0)^2 + (x 1 - c 1)^2) := by
            simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
          rw [h121]
          have h122 : 0 ≤ (x 0 - c 0)^2 + (x 1 - c 1)^2 := by positivity
          rw [Real.sq_sqrt h122]
        have h13 : (x 0 - c 0)^2 ≤ (δ_n / 2)^2 := by
          have h14 : (x 0 - c 0)^2 = |x 0 - c 0|^2 := by rw [sq_abs]
          rw [h14]
          have h15 : 0 ≤ δ_n / 2 := by positivity
          gcongr
        have h16 : (x 1 - c 1)^2 ≤ (δ_n / 2)^2 := by
          have h17 : (x 1 - c 1)^2 = |x 1 - c 1|^2 := by rw [sq_abs]
          rw [h17]
          have h18 : 0 ≤ δ_n / 2 := by positivity
          gcongr
        have h19 : ‖x - c‖ ^ 2 ≤ δ_n ^ 2 := by
          rw [h12]
          nlinarith
        have h20 : 0 ≤ ‖x - c‖ := by positivity
        nlinarith
      have h15 : δ_n ≤ δ := hδn_leδ
      exact le_trans h10 h15
    let centers : Finset Plane := squares.image (fun q => Classical.choose (h_square_cover q))
    have h_cover : P_oriented ⊆ ⋃ c ∈ (centers : Set Plane), Metric.closedBall c δ := by
      intro p hp
      have hcov : p ∈ ⋃ q ∈ (squares : Set (DyadicSquare n)), (q.toSet : Set Plane) := hcover hp
      rcases Set.mem_iUnion₂.mp hcov with ⟨q, hq, hq2⟩
      let c := Classical.choose (h_square_cover q)
      have hc_in : c ∈ (centers : Set Plane) := by
        exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
      have hsub : (q.toSet : Set Plane) ⊆ Metric.closedBall c δ :=
        Classical.choose_spec (h_square_cover q)
      have hpin : p ∈ Metric.closedBall c δ := hsub hq2
      exact Set.mem_iUnion₂.mpr ⟨c, hc_in, hpin⟩
    have hδ_toNNReal : (δ.toNNReal : ℝ) = δ := by
      have h : 0 ≤ δ := by linarith
      simp [Real.toNNReal, h]
    have h_cover' : P_oriented ⊆ ⋃ c ∈ (centers : Set Plane), Metric.closedBall c δ.toNNReal := by
      intro p hp
      have h := h_cover hp
      simpa [hδ_toNNReal] using h
    have h3 : Ncover' δ P_oriented ≤ (centers.card : ENNReal) := by
      have hcov' : Metric.IsCover δ.toNNReal P_oriented (centers : Set Plane) := by
        rw [Metric.isCover_iff_subset_iUnion_closedBall]
        exact h_cover'
      have h4 : Metric.externalCoveringNumber δ.toNNReal P_oriented ≤ (centers : Set Plane).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hcov'
      have h5 : (centers : Set Plane).encard = ↑centers.card := by simp
      rw [h5] at h4
      have h6 : Ncover' δ P_oriented = Metric.externalCoveringNumber δ.toNNReal P_oriented := by
        unfold Ncover' <;> rfl
      rw [h6]
      exact_mod_cast h4
    have h3' : centers.card ≤ squares.card := Finset.card_image_le
    have h3'' : Ncover' δ P_oriented ≤ (squares.card : ENNReal) := by
      calc Ncover' δ P_oriented
        ≤ (centers.card : ENNReal) := h3
      _ ≤ (squares.card : ENNReal) := by exact_mod_cast Finset.card_image_le
    -- Step 4: Slope partition mass bound
    have h4 : ENNReal.ofReal c_slope * Ncover' δ P ≤ Ncover' δ P_oriented := hP_oriented_mass
    -- Step 5: Doubling bound Ncover(δ_n, P) ≤ 9 * Ncover(δ, P)
    have h5 : Ncover' δ_n P ≤ (9 : ENNReal) * Ncover' δ P := by
      have h51 : (δ / 2).toNNReal ≤ δ_n.toNNReal := by
        have h : δ / 2 ≤ δ_n := by linarith
        exact Real.toNNReal_mono h
      have h52 : Ncover' δ_n P ≤ Ncover' (δ / 2) P := by
        have h := Metric.externalCoveringNumber_anti h51 (A := P)
        exact_mod_cast h
      have hhalf_eq : (δ / 2).toNNReal = δ.toNNReal / 2 := by
        apply NNReal.coe_injective
        have hpos1 : 0 ≤ δ / 2 := by linarith
        have hpos2 : 0 ≤ δ := by linarith
        simp [Real.toNNReal_of_nonneg hpos1, Real.toNNReal_of_nonneg hpos2] <;> ring
      have h525 : (Ncover' (δ / 2) P : ENNReal) = (Metric.externalCoveringNumber (δ.toNNReal / 2) P : ENNReal) := by
        unfold Ncover'
        rw [hhalf_eq]
      have h53 : Ncover' (δ / 2) P ≤ (9 : ENNReal) * Ncover' δ P := by
        rw [h525]
        have h := RobustKaufmanProjection.externalCoveringNumber_half_le_plane P δ.toNNReal
        have h_goal : Metric.externalCoveringNumber (δ.toNNReal / 2) P ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P := by
          exact_mod_cast h
        have h_final : (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P = (9 : ENNReal) * Ncover' δ P := by
          unfold Ncover' <;> rfl
        rw [h_final] at h_goal
        exact h_goal
      exact le_trans h52 h53
    -- Step 6: Combine all inequalities
    set a : ENNReal := (81 : ENNReal) * (K + 1 : ENNReal) with ha_def
    have ha_pos : a ≠ 0 := by simp [ha_def]
    have ha_fin : a ≠ ⊤ := by
      have h : a = (81 : ENNReal) * (K + 1 : ENNReal) := by simp [ha_def]
      rw [h]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    have h6 : ENNReal.ofReal c_slope * Ncover' δ_n P ≤ a * Ncover' δ_n config.pointSet := by
      calc ENNReal.ofReal c_slope * Ncover' δ_n P
        ≤ ENNReal.ofReal c_slope * ((9 : ENNReal) * Ncover' δ P) := by gcongr
      _ = (9 : ENNReal) * (ENNReal.ofReal c_slope * Ncover' δ P) := by ring
      _ ≤ (9 : ENNReal) * Ncover' δ P_oriented := by gcongr
      _ ≤ (9 : ENNReal) * (squares.card : ENNReal) := by gcongr
      _ ≤ (9 : ENNReal) * ((K + 1 : ENNReal) * (squares'.card : ENNReal)) := by gcongr
      _ ≤ (9 : ENNReal) * ((K + 1 : ENNReal) * ((9 : ENNReal) * Ncover' δ_n config.pointSet)) := by gcongr
      _ = a * Ncover' δ_n config.pointSet := by
        simp [ha_def] <;> ring
    -- Step 7: Absorption: 81*(K+1) * δ_n^ρ_mass ≤ c_slope
    have hK1 : (K + 1 : ℝ) ≤ 2 * (n : ℝ) + 10 := by
      have hK_def : K = 2 * n + 7 := by rfl
      rw [hK_def]
      <;> norm_cast <;> omega
    have h_K_abs : (K + 1 : ℝ) ≤ δ_n ^ (-reserved_budget / 24) := by
      calc (K + 1 : ℝ)
        ≤ 2 * (n : ℝ) + 10 := hK1
      _ ≤ δ_n ^ (-reserved_budget / 24) := h_K_log_absorb n hδn_leδ hδ_lt2δn
    have hδn_le_one : δ_n ≤ 1 := by linarith [hδn_leδ, hδ_le_one]
    have h81 : δ_n ^ (5 * reserved_budget / 24) ≤ 1 / 81 := by
      have h1 : 5 * reserved_budget / 24 ≥ reserved_budget / 6 := by linarith
      have h2 : δ_n ^ (5 * reserved_budget / 24) ≤ δ ^ (5 * reserved_budget / 24) := by
        gcongr <;> linarith
      have h3 : δ ^ (5 * reserved_budget / 24) ≤ δ ^ (reserved_budget / 6) :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h1
      have h4 : δ ^ (reserved_budget / 6) ≤ 1 / 81 := hδ_slope
      exact le_trans (le_trans h2 h3) h4
    have h_absorb : (81 : ℝ) * ((K + 1 : ℝ)) * (δ_n ^ ρ_mass) ≤ c_slope := by
      have h_c_slope_lower : c_slope ≥ δ_n ^ ρ_slope := by
        have h1 : c_slope ≥ δ ^ ρ_slope := hc_slope_lower
        have h2 : δ ^ ρ_slope ≥ δ_n ^ ρ_slope := by
          have h21 : δ_n ^ ρ_slope ≤ δ ^ ρ_slope := by gcongr <;> linarith
          exact h21
        exact le_trans h2 h1
      have h_exp : ρ_slope - ρ_mass = -reserved_budget / 4 := by
        simp [ρ_slope, ρ_mass, hρ_slope_def, hρ_mass_def] <;> ring
      have h9 : (81 : ℝ) * ((K + 1 : ℝ)) ≤ δ_n ^ (ρ_slope - ρ_mass) := by
        rw [h_exp]
        have h10 : (81 : ℝ) * ((K + 1 : ℝ)) ≤ 81 * δ_n ^ (-reserved_budget / 24) := by gcongr
        have h11 : 81 * δ_n ^ (-reserved_budget / 24) ≤ δ_n ^ (-reserved_budget / 4) := by
          have h12 : (81 : ℝ) ≤ δ_n ^ (-5 * reserved_budget / 24) := by
            have h13 : δ_n ^ (5 * reserved_budget / 24) ≤ 1 / 81 := h81
            have h14 : 0 < δ_n ^ (5 * reserved_budget / 24) := by positivity
            have h15 : (δ_n ^ (5 * reserved_budget / 24))⁻¹ ≥ 81 := by
              have h16 : (1 / 81 : ℝ)⁻¹ = 81 := by norm_num
              have h17 : 1 / (δ_n ^ (5 * reserved_budget / 24)) ≥ 1 / (1 / 81 : ℝ) := one_div_le_one_div_of_le h14 h13
              have h18 : (δ_n ^ (5 * reserved_budget / 24))⁻¹ = 1 / (δ_n ^ (5 * reserved_budget / 24)) := by simp
              have h19 : (1 / 81 : ℝ)⁻¹ = 1 / (1 / 81 : ℝ) := by simp
              have h20 : (δ_n ^ (5 * reserved_budget / 24))⁻¹ ≥ (1 / 81 : ℝ)⁻¹ := by
                calc (δ_n ^ (5 * reserved_budget / 24))⁻¹
                  = 1 / (δ_n ^ (5 * reserved_budget / 24)) := h18
                _ ≥ 1 / (1 / 81 : ℝ) := h17
                _ = (1 / 81 : ℝ)⁻¹ := h19.symm
              rw [h16] at h20
              exact h20
            have h17 : (δ_n ^ (5 * reserved_budget / 24))⁻¹ = δ_n ^ (-5 * reserved_budget / 24) := by
              have h_exp : -(5 * reserved_budget / 24) = -5 * reserved_budget / 24 := by ring
              rw [← Real.rpow_neg (by positivity), h_exp]
            rw [h17] at h15; exact h15
          have h18 : δ_n ^ (-5 * reserved_budget / 24) * δ_n ^ (-reserved_budget / 24) =
              δ_n ^ (-reserved_budget / 4) := by
            have h_exp : (-5 * reserved_budget / 24) + (-reserved_budget / 24) = -reserved_budget / 4 := by ring
            rw [← Real.rpow_add hδn_pos, h_exp]
          have h_pos2 : 0 ≤ δ_n ^ (-reserved_budget / 24) := by positivity
          have h13 : 81 * δ_n ^ (-reserved_budget / 24) ≤ δ_n ^ (-5 * reserved_budget / 24) * δ_n ^ (-reserved_budget / 24) :=
            mul_le_mul_of_nonneg_right h12 h_pos2
          calc 81 * δ_n ^ (-reserved_budget / 24)
            ≤ δ_n ^ (-5 * reserved_budget / 24) * δ_n ^ (-reserved_budget / 24) := h13
          _ = δ_n ^ (-reserved_budget / 4) := h18
        exact le_trans h10 h11
      have h10 : (81 : ℝ) * ((K + 1 : ℝ)) * (δ_n ^ ρ_mass) ≤ δ_n ^ (ρ_slope - ρ_mass) * (δ_n ^ ρ_mass) := by
        have h_pos : 0 ≤ δ_n ^ ρ_mass := by positivity
        exact mul_le_mul_of_nonneg_right h9 h_pos
      have h11 : δ_n ^ (ρ_slope - ρ_mass) * (δ_n ^ ρ_mass) = δ_n ^ ρ_slope := by
        have h_exp : (ρ_slope - ρ_mass) + ρ_mass = ρ_slope := by ring
        rw [← Real.rpow_add hδn_pos, h_exp]
      have h12 : (81 : ℝ) * ((K + 1 : ℝ)) * (δ_n ^ ρ_mass) ≤ δ_n ^ ρ_slope := by
        rw [h11] at h10
        exact h10
      exact le_trans h12 h_c_slope_lower
    have h7 : a * ENNReal.ofReal (δ_n ^ ρ_mass) ≤ ENNReal.ofReal c_slope := by
      have h71 : (81 : ℝ) * ((K + 1 : ℝ)) * (δ_n ^ ρ_mass) ≤ c_slope := h_absorb
      have h72 : a = ENNReal.ofReal ((81 : ℝ) * ((K + 1 : ℝ))) := by
        rw [ha_def]
        <;> norm_cast
      rw [h72]
      have h73 : ENNReal.ofReal ((81 : ℝ) * ((K + 1 : ℝ))) * ENNReal.ofReal (δ_n ^ ρ_mass) =
          ENNReal.ofReal (((81 : ℝ) * ((K + 1 : ℝ)) * (δ_n ^ ρ_mass))) := by
        have h_pos : 0 ≤ (81 : ℝ) * ((K + 1 : ℝ)) := by positivity
        rw [ENNReal.ofReal_mul h_pos]
        <;> ring
      rw [h73]
      exact ENNReal.ofReal_le_ofReal h71
    -- Step 8: Multiply h7 by Ncover(δ_n, P) and combine with h6
    have h8 : a * (ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P) ≤ a * Ncover' δ_n config.pointSet := by
      calc a * (ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P)
        = (a * ENNReal.ofReal (δ_n ^ ρ_mass)) * Ncover' δ_n P := by ring
      _ ≤ (ENNReal.ofReal c_slope) * Ncover' δ_n P := by gcongr
      _ ≤ a * Ncover' δ_n config.pointSet := h6
    have h9 : ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P ≤ Ncover' δ_n config.pointSet := by
      have h_div : a * (ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P) / a ≤ a * Ncover' δ_n config.pointSet / a := by
        gcongr
      have h_cancel1 : a * (ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P) / a = ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P := by
        set x := ENNReal.ofReal (δ_n ^ ρ_mass) * Ncover' δ_n P with hx
        have h1 : a * x / a = a * (x / a) := by
          simp only [div_eq_mul_inv, mul_assoc]
        rw [h1]
        exact ENNReal.mul_div_cancel ha_pos ha_fin
      have h_cancel2 : a * Ncover' δ_n config.pointSet / a = Ncover' δ_n config.pointSet := by
        set y := Ncover' δ_n config.pointSet with hy
        have h1 : a * y / a = a * (y / a) := by
          simp only [div_eq_mul_inv, mul_assoc]
        rw [h1]
        exact ENNReal.mul_div_cancel ha_pos ha_fin
      rw [h_cancel1, h_cancel2] at h_div
      exact h_div
    exact h9

  -- M lower bound: use S-set property of tubeFam directly
  -- tubeFam is (δ_n, s, δ_n^{-lam})-S-set, tubes are δ_n-separated, so Ncover = M
  -- sset_ncover_lower_bound gives M ≥ (δ_n^{-lam} * δ_n^s)^{-1} = δ_n^{lam-s}
  -- Since ρ_M ≥ 0 and δ_n ≤ 1, δ_n^{lam-s} ≥ δ_n^{lam-s+ρ_M}
  have hM_lower_final : (M : ℝ) ≥ δ_n ^ (-s + lam + ρ_M) := by
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
      ImprovedIncidenceAssembly.sset_ncover_lower_bound h_sset
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
    have h15 : δ_n ≤ 1 := by linarith [hδ_le_one]
    have h16 : δ_n ^ (lam - s) ≥ δ_n ^ (-s + lam + ρ_M) :=
      Real.rpow_le_rpow_of_exponent_ge hδn_pos h15 h14
    exact le_trans h16 h11

  -- M upper bound: tubeFam ⊆ normalizedTubes_square, which has ≤ 28 * δ_n^{-s}
  have hM_upper_final : (M : ℝ) ≤ 28 * δ_n ^ (-s) := by
    have hq_nonempty : squares'.Nonempty := by
      have h7 : (squares'.card : ℝ) ≥ (squares.card : ℝ) / (K + 1 : ℝ) := hretention
      have h8 : 0 < (squares.card : ℝ) := by exact_mod_cast hsquares_nonempty.card_pos
      have h9 : (0 : ℝ) < (K + 1 : ℝ) := by positivity
      have h10 : 0 < (squares.card : ℝ) / (K + 1 : ℝ) := by positivity
      have h11 : 0 < (squares'.card : ℝ) := by linarith
      have h12 : 0 < squares'.card := by exact_mod_cast h11
      exact Finset.card_pos.mp h12
    rcases hq_nonempty with ⟨q, hq⟩
    have hq_in_squares : q ∈ squares := hsquares'_sub hq
    have h1 : (tubeFam q hq).card = M := huniform q hq
    have h2 : tubeFam q hq ⊆ normalizedTubes_square q hq_in_squares :=
      htube_sub_raw q hq hq_in_squares
    have h3 : (tubeFam q hq).card ≤ (normalizedTubes_square q hq_in_squares).card :=
      Finset.card_le_card h2
    have h4 : ((normalizedTubes_square q hq_in_squares).card : ℝ) ≤ 28 * δ_n ^ (-s) :=
      hnorm_square_upper q hq_in_squares
    have h5 : (M : ℝ) ≤ ((normalizedTubes_square q hq_in_squares).card : ℝ) := by
      have h6 : (tubeFam q hq).card = M := h1
      rw [h6] at h3
      exact_mod_cast h3
    exact le_trans h5 h4

  -- Ambient bound
  have hambient1 : (T₀.card : ENNReal) ≤
      (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) := hT0_bound
  have hambient2 : (K_ambient : ℝ) ≤ δ_n ^ (-ρ_T) := by
    have h_eq1 : ρ_T = reserved_budget / 3 := by simp [ρ_T, hρ_T_def]
    have h_eq2 : (-ρ_T : ℝ) = -reserved_budget / 3 := by
      rw [h_eq1] <;> ring
    rw [h_eq2]
    have h1 : (K_ambient : ℝ) ≤ 1000000 := by exact_mod_cast hKamb_bound
    have h2 : (1000000 : ℝ) ≤ δ_n ^ (-reserved_budget / 3) := h_absorb_ambient n hδn_leδ hδ_lt2δn
    exact le_trans h1 h2
  have hambient3 : (T₀.card : ENNReal) ≤
      ENNReal.ofReal (δ_n ^ (-ρ_T)) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
    have h4 : (K_ambient : ENNReal) ≤ ENNReal.ofReal (δ_n ^ (-ρ_T)) := by
      have h41 : (K_ambient : ℝ) ≤ δ_n ^ (-ρ_T) := hambient2
      have h42 : (K_ambient : ENNReal) = ENNReal.ofReal (K_ambient : ℝ) := by simp
      rw [h42]
      exact ENNReal.ofReal_le_ofReal h41
    have h5 : (T₀.card : ENNReal) ≤
        (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) := hT0_bound
    have h6 : (T₀.card : ENNReal) ≤
        (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
      have h5' : (T₀.card : ENNReal) ≤
          (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) := hT0_bound
      have h_eq : (Metric.externalCoveringNumber δ.toNNReal T_oriented : ENNReal) =
          (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
        exact_mod_cast hT_oriented_ncover
      rw [h_eq] at h5'
      exact h5'
    have h7 : (K_ambient : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
        ENNReal.ofReal (δ_n ^ (-ρ_T)) * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
      exact mul_le_mul_right' h4 _
    exact le_trans h6 h7

  -- Weaken swapped conditions: P_retained ⊆ P_oriented
  have hretained_sub : P_retained ⊆ P_oriented := by
    intro p hp; exact hp.1
  have hswap_false' : swapped = false → P_retained ⊆ P_ret ∧ T_oriented = T := by
    intro hsw
    have h_eq : P_oriented = P_ret := (hswap_false hsw).1
    have hT : T_oriented = T := (hswap_false hsw).2
    have hsub : P_retained ⊆ P_ret := by
      rw [h_eq] at hretained_sub
      exact hretained_sub
    exact ⟨hsub, hT⟩
  have hswap_true' : swapped = true → P_retained ⊆ swapCoords '' P_ret ∧ T_oriented = swapLine '' T := by
    intro hsw
    have h_eq : P_oriented = swapCoords '' P_ret := (hswap_true hsw).1
    have hT : T_oriented = swapLine '' T := (hswap_true hsw).2
    have hsub : P_retained ⊆ swapCoords '' P_ret := by
      rw [h_eq] at hretained_sub
      exact hretained_sub
    exact ⟨hsub, hT⟩

  -- Geometric bounds for tubes
  have h_n_ge1 : n ≥ 1 := by
    by_contra h
    have h0 : n = 0 := by omega
    have hδn_eq : δ_n = 1 := by
      simp only [δ_n, dyadicDelta, h0] <;> norm_num
    rw [hδn_eq] at hδn_lt_one
    <;> norm_num at hδn_lt_one <;> linarith

  have h_tubes_strip : ∀ (T : DyadicTube n), T ∈ T₀ →
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) := by
    intro T hT
    have h_exists : ∃ (q : DyadicSquare n) (hq' : q ∈ squares'), T ∈ tubeFam q hq' :=
      (hT0_mem_iff T).mp hT
    rcases h_exists with ⟨q, hq', hT_fam⟩
    exact htube_strip q hq' T hT_fam

  have h_tubes_intercept : ∀ (q : DyadicSquare n) (hq' : q ∈ squares') (T : DyadicTube n),
      T ∈ tubeFam q hq' → |T.intercept| ≤ 3 := by
    intro q hq' T hT
    have hq : q ∈ squares := hsquares'_sub hq'
    have hT_norm : T ∈ normalizedTubes_square q hq := htube_sub_raw q hq' hq hT
    have hT_raw : T ∈ rawTubes_square q hq := hnorm_square_sub q hq hT_norm
    exact hraw_square_intercept q hq T hT_raw

  have h_tubes_intercept_T0 : ∀ (T : DyadicTube n), T ∈ T₀ → |T.intercept| ≤ 3 := by
    intro T hT
    have h_exists : ∃ (q : DyadicSquare n) (hq' : q ∈ squares'), T ∈ tubeFam q hq' :=
      (hT0_mem_iff T).mp hT
    rcases h_exists with ⟨q, hq', hT_fam⟩
    exact h_tubes_intercept q hq' T hT_fam

  have h_tubes_bounded : T₀.card ≤ 12 * 16 ^ n :=
    bounded_tubes_card_from_geometric h_n_ge1 h_tubes_strip h_tubes_intercept_T0

  -- Section 9 provenance: each tube in config.T₀ has an original oriented line within 7δ
  have h_section9_prov : ∀ (U : DyadicTube n), U ∈ config.T₀ →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧ dist (toAffineLine U) ℓ ≤ 7 * δ := by
    intro U hU
    have h_exists : ∃ (q : DyadicSquare n) (hq' : q ∈ squares'), U ∈ tubeFam q hq' :=
      (hT0_mem_iff U).mp hU
    rcases h_exists with ⟨q, hq', hT_fam⟩
    have hq : q ∈ squares := hsquares'_sub hq'
    have h_norm : U ∈ normalizedTubes_square q hq := htube_sub_raw q hq' hq hT_fam
    exact hnorm_square_prov q hq U h_norm

  exact ⟨n, M, config, P_ret, P_retained, T_oriented, swapped, ρ_mass, ρ_M, ρ_T,
    hδn_leδ, hδ_lt2δn, hρ_mass_nonneg, hρ_M_nonneg, hρ_T_nonneg, hbudget, hM_pos', hM_dyadic,
    hP_ret_sub, hswap_false', hswap_true', hT_oriented_ncover, h_each_square, hmass1,
    hmass2, hM_lower_final, hM_upper_final, hambient3,
    h_tubes_strip, h_tubes_intercept, h_tubes_bounded, h_section9_prov⟩


end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
