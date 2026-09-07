module

/-
  Source-to-NiceConfiguration bridge — main theorem.

  Extracted from SourceToNiceConfiguration_hmass2.lean to reduce
  per-file compilation time.

  Contains `source_to_nice_configuration`: the full bridge from continuous
  source data (point set, tube families) to a NiceConfiguration with
  explicit loss budget. Chooses δ₀ and verifies all absorption conditions.

  Depends on BridgeHelpers and BridgeInner.
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
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Section9.BridgeInner
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate (AffineLine)
open DirecretisedFurstenbergEstimate.MainAppendix (affineLine_packing_constant)
open DirecretisedFurstenbergEstimate.MainAppendix (affineLine_packing_constant_pos)
open CoordinatePartition
open DyadicCardToNcover (toAffineLine)

/-- Internal implementation: continuous source → NiceConfiguration with loss budget.
    Canonical public theorem is `DirecretisedFurstenbergEstimate.Section9.source_to_nice_configuration`. -/
theorem source_to_nice_configuration_impl
    (reserved_budget : ℝ) (hbudget_pos : 0 < reserved_budget)
    (lam : ℝ) (hlam_pos : 0 < lam)
    (ε_tube : ℝ) (hε_tube_pos : 0 < ε_tube) (hε_tube_lt_lam : ε_tube < lam) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        ∀ (s t : ℝ), 0 < s → s < 1 → s < t →
          ∀ (C_P C_T : ℝ), 0 < C_P → 0 < C_T →
            C_T ≤ δ ^ (-ε_tube) →
              ∀ (P : Set Plane), P ⊆ Metric.closedBall 0 1 →
                IsDeltaSSet δ t C_P P →
                  ∀ (T : Set AffineLine), Bornology.IsBounded T →
                    ∀ (Tp : ∀ (p : Plane), p ∈ P → Set AffineLine),
                      (∀ p hp, Tp p hp ⊆ T) →
                      (∀ p hp, IsDeltaSSet δ s C_T (Tp p hp)) →
                      (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
                      (∀ p hp, ∀ ℓ ∈ Tp p hp, ℓ.offset ∈ Metric.closedBall 0 2) →
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
  -- Step 1: Constants
  let Kpack : ℝ := (affineLine_packing_constant : ℝ)
  have hKpack_pos : 0 < Kpack := by
    have h : (0 : ℝ) < (affineLine_packing_constant : ℝ) := by exact_mod_cast affineLine_packing_constant_pos
    simpa [Kpack] using h
  let C_fixed : ℝ := 3721 * Kpack^5 * 58 * 2 * (1 + Kpack) * Kpack
  have hC_fixed_pos : 0 < C_fixed := by positivity
  let d : ℝ := lam - ε_tube
  have hd_pos : 0 < d := by linarith
  let ρ_T_loc := reserved_budget / 3
  have hρ_T_loc_pos : 0 < ρ_T_loc := by positivity
  let a : ℝ := (2 : ℝ) ^ (reserved_budget / 24)
  have ha_one : 1 < a := by
    have h1 : (0 : ℝ) < reserved_budget / 24 := by positivity
    exact Real.one_lt_rpow (by norm_num) h1
  rcases exp_dominates_linear a ha_one with ⟨N0, hN0⟩

  -- Step 2: Define δ bounds (without if-then-else for cleaner proofs)
  let δ1 : ℝ := (1 / C_fixed) ^ (1 / d)
  let C_fixed18 := 9000 * C_fixed
  let δ2 : ℝ := (1 / C_fixed18) ^ (1 / d)
  let δ3 : ℝ := (1 / 1000000 : ℝ) ^ (1 / ρ_T_loc)
  let δ4 : ℝ := (1 / 2 : ℝ) ^ N0
  let δ5 : ℝ := (1 / 81 : ℝ) ^ (6 / reserved_budget)
  let δ0 := min 1 (min δ1 (min δ2 (min δ3 (min δ4 δ5))))

  have hδ0_pos : 0 < δ0 := by positivity

  refine ⟨δ0, hδ0_pos, fun δ hδ_pos hδ_leδ0 => ?_⟩
  have hδ_le_one : δ ≤ 1 := by
    have h2 : δ0 ≤ 1 := min_le_left _ _
    linarith [hδ_leδ0, h2]
  have hδ_lt_one : δ < 1 := by
    have h2 : δ0 ≤ δ1 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h3 : δ1 < 1 := by
      dsimp only [δ1]
      have hK_nat_pos : 0 < affineLine_packing_constant := affineLine_packing_constant_pos
      have hK_nat_ge1 : 1 ≤ affineLine_packing_constant := by omega
      have hKpack_ge1 : (1 : ℝ) ≤ Kpack := by
        have h : (affineLine_packing_constant : ℝ) ≥ 1 := by exact_mod_cast hK_nat_ge1
        simpa [Kpack] using h
      have hK5 : Kpack ^ 5 ≥ 1 := by
        have h1 : Kpack ≥ 1 := hKpack_ge1
        have h2 : Kpack ^ 5 ≥ 1 ^ 5 := by gcongr
        simpa using h2
      have h4 : (1 : ℝ) < C_fixed := by
        dsimp only [C_fixed]
        have h_pos1 : 0 < Kpack := by linarith
        have h : 3721 * Kpack ^ 5 * 58 * 2 * (1 + Kpack) * Kpack ≥ 3721 * (1 : ℝ) * 58 * 2 * 2 * 1 := by
          gcongr <;> linarith
        linarith
      have h5 : (1 / C_fixed) < 1 := by
        apply (div_lt_one (show (0 : ℝ) < C_fixed by linarith)).mpr
        linarith
      have h6 : 0 < 1 / d := by positivity
      have h7 : 0 ≤ (1 / C_fixed) := by positivity
      exact Real.rpow_lt_one h7 h5 h6
    have h7 : δ ≤ δ0 := hδ_leδ0
    have h8 : δ0 ≤ δ1 := h2
    linarith
  have hδ_leδ1 : δ ≤ δ1 := by
    have h2 : δ0 ≤ δ1 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith [hδ_leδ0, h2]
  have hδ_leδ2 : δ ≤ δ2 := by
    have h2 : δ0 ≤ δ2 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    linarith [hδ_leδ0, h2]
  have hδ_leδ3 : δ ≤ δ3 := by
    have h2 : δ0 ≤ δ3 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    linarith [hδ_leδ0, h2]
  have hδ_leδ4 : δ ≤ δ4 := by
    have h2 : δ0 ≤ δ4 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    linarith [hδ_leδ0, h2]
  have hδ_leδ5 : δ ≤ δ5 := by
    have h2 : δ0 ≤ δ5 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
    linarith [hδ_leδ0, h2]

  intro s t hs_pos hs_lt_one hst C_P C_T hCP_pos hCT_pos hCT_bound P hP_bdd hP_sset T hT_bdd Tp hTp_sub hTp_sset hTp_near hTp_bdd

  -- Step 3: Choose finer dyadic scale
  rcases choose_finer_dyadic_scale δ hδ_pos hδ_le_one with ⟨n, hδn_leδ, hδ_lt2δn⟩
  let δ_n := dyadicDelta n
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n

  -- Step 4a: Bound the snap constant uniformly in s, C_T
  have h1_58 : (58 : ℝ)^s ≤ 58 := by
    have h2 : (58 : ℝ)^s ≤ (58 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using h2
  have h1_max : max 1 (Kpack * C_T) ≤ (1 + Kpack) * δ^(-ε_tube) := by
    have h5 : C_T ≤ δ^(-ε_tube) := hCT_bound
    have h6 : 1 ≤ δ^(-ε_tube) := by
      have h7 : -ε_tube ≤ 0 := by linarith
      have h8 : δ^(-ε_tube) ≥ δ^(0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h7
      simpa using h8
    have hδinv_pos : 0 < δ^(-ε_tube) := by positivity
    have h9 : max 1 (Kpack * C_T) ≤ 1 + Kpack * δ^(-ε_tube) := by
      apply max_le
      · have h_pos : 0 ≤ Kpack * δ^(-ε_tube) := by positivity
        linarith
      · have h10 : Kpack * C_T ≤ Kpack * δ^(-ε_tube) := by gcongr
        linarith
    have h10 : 1 + Kpack * δ^(-ε_tube) ≤ (1 + Kpack) * δ^(-ε_tube) := by
      have h11 : (1 + Kpack) * δ^(-ε_tube) = δ^(-ε_tube) + Kpack * δ^(-ε_tube) := by ring
      rw [h11]
      have h12 : 1 ≤ δ^(-ε_tube) := h6
      linarith
    exact le_trans h9 h10
  let snap_const := 3721 * Kpack^5 * (58 : ℝ)^s * 2 * max 1 (Kpack * C_T) * Kpack
  have h_snap_bound : snap_const ≤ C_fixed * δ^(-ε_tube) := by
    dsimp only [snap_const, C_fixed]
    have h_pos : 0 < 3721 * Kpack^5 * 2 * Kpack := by positivity
    have h_mul1 : (58 : ℝ)^s * max 1 (Kpack * C_T) ≤ 58 * ((1 + Kpack) * δ^(-ε_tube)) := by
      calc (58 : ℝ)^s * max 1 (Kpack * C_T)
        ≤ (58 : ℝ)^s * ((1 + Kpack) * δ^(-ε_tube)) := by gcongr
      _ ≤ 58 * ((1 + Kpack) * δ^(-ε_tube)) := by
          have h : (58 : ℝ)^s ≤ 58 := h1_58
          have hpos2 : 0 ≤ (1 + Kpack) * δ^(-ε_tube) := by positivity
          nlinarith
    calc 3721 * Kpack^5 * (58 : ℝ)^s * 2 * max 1 (Kpack * C_T) * Kpack
      = (3721 * Kpack^5 * 2 * Kpack) * ((58 : ℝ)^s * max 1 (Kpack * C_T)) := by ring
    _ ≤ (3721 * Kpack^5 * 2 * Kpack) * (58 * ((1 + Kpack) * δ^(-ε_tube))) := by gcongr
    _ = 3721 * Kpack^5 * 58 * 2 * (1 + Kpack) * Kpack * δ^(-ε_tube) := by ring

  -- Absorption: C_fixed ≤ δ^(-d) from δ ≤ δ1
  have h_abs1 : C_fixed ≤ δ^(-d) := absorb_const hC_fixed_pos hd_pos hδ_pos hδ_leδ1
  have h_abs18 : C_fixed18 ≤ δ^(-d) := absorb_const (by positivity) hd_pos hδ_pos hδ_leδ2

  -- h_absorb_snap
  have h_absorb_snap' : ∀ (m : ℕ), dyadicDelta m ≤ δ → δ < 2 * dyadicDelta m →
      snap_const ≤ (dyadicDelta m)^(-lam) := by
    intro m hdm_leδ _
    have h_posm : 0 < dyadicDelta m := dyadicDelta_pos m
    have h_anti : (dyadicDelta m)^(-lam) ≥ δ^(-lam) := rpow_neg_antitone h_posm hdm_leδ hlam_pos
    have h_mul : C_fixed * δ^(-ε_tube) ≤ δ^(-lam) := by
      have h : δ^(-d) * δ^(-ε_tube) = δ^(-lam) := by
        rw [← Real.rpow_add hδ_pos] <;> simp [d] <;> ring_nf
      have h' : C_fixed * δ^(-ε_tube) ≤ δ^(-d) * δ^(-ε_tube) := by gcongr
      rw [h] at h'; exact h'
    calc snap_const
      ≤ C_fixed * δ^(-ε_tube) := h_snap_bound
    _ ≤ δ^(-lam) := h_mul
    _ ≤ (dyadicDelta m)^(-lam) := h_anti

  -- h_absorb_snap18
  have h_snap18_bound : (9000 : ℝ) * snap_const ≤ C_fixed18 * δ^(-ε_tube) := by
    dsimp only [C_fixed18]
    have h : (9000 : ℝ) * snap_const ≤ (9000 : ℝ) * (C_fixed * δ^(-ε_tube)) := by gcongr
    have h2 : (9000 : ℝ) * (C_fixed * δ^(-ε_tube)) = C_fixed18 * δ^(-ε_tube) := by
      dsimp only [C_fixed18] <;> ring
    rw [h2] at h
    exact h
  have h_absorb_snap18' : ∀ (m : ℕ), dyadicDelta m ≤ δ → δ < 2 * dyadicDelta m →
      (9000 : ℝ) * snap_const ≤ (dyadicDelta m)^(-lam) := by
    intro m hdm_leδ _
    have h_posm : 0 < dyadicDelta m := dyadicDelta_pos m
    have h_anti : (dyadicDelta m)^(-lam) ≥ δ^(-lam) := rpow_neg_antitone h_posm hdm_leδ hlam_pos
    have h_mul : C_fixed18 * δ^(-ε_tube) ≤ δ^(-lam) := by
      have h : δ^(-d) * δ^(-ε_tube) = δ^(-lam) := by
        rw [← Real.rpow_add hδ_pos] <;> simp [d] <;> ring_nf
      have h' : C_fixed18 * δ^(-ε_tube) ≤ δ^(-d) * δ^(-ε_tube) := by gcongr
      rw [h] at h'; exact h'
    calc (9000 : ℝ) * snap_const
      ≤ C_fixed18 * δ^(-ε_tube) := h_snap18_bound
    _ ≤ δ^(-lam) := h_mul
    _ ≤ (dyadicDelta m)^(-lam) := h_anti

  -- h_absorb_ambient: 1000000 ≤ δ_n^{-ρ_T_loc}
  have h_absorb_ambient' : ∀ (m : ℕ), dyadicDelta m ≤ δ → δ < 2 * dyadicDelta m →
      (1000000 : ℝ) ≤ (dyadicDelta m)^(-ρ_T_loc) := by
    intro m hdm_leδ _
    have h_posm : 0 < dyadicDelta m := dyadicDelta_pos m
    have h_anti : (dyadicDelta m)^(-ρ_T_loc) ≥ δ^(-ρ_T_loc) := rpow_neg_antitone h_posm hdm_leδ hρ_T_loc_pos
    have h3 : δ^(ρ_T_loc) ≤ 1 / 1000000 := by
      have h4 : δ^(ρ_T_loc) ≤ δ3^(ρ_T_loc) := by gcongr
      have h5 : δ3^(ρ_T_loc) = 1 / 1000000 := by
        dsimp only [δ3]
        exact rpow_root_cancel (by positivity) hρ_T_loc_pos
      rw [h5] at h4; exact h4
    have h7 : (1000000 : ℝ) ≤ δ^(-ρ_T_loc) := by
      have h8 : δ^(-ρ_T_loc) = (δ^(ρ_T_loc))⁻¹ := by
        rw [← Real.rpow_neg (by linarith)] <;> ring
      rw [h8]
      have h9 : 0 < δ^(ρ_T_loc) := by positivity
      have h10 : (δ^(ρ_T_loc))⁻¹ ≥ (1 / 1000000 : ℝ)⁻¹ := by gcongr
      have h11 : (1 / 1000000 : ℝ)⁻¹ = 1000000 := by norm_num
      rw [h11] at h10; exact h10
    linarith

  -- h_K_log_absorb
  have h_n_ge_N0 : n ≥ N0 := by
    have h1 : δ_n ≤ δ4 := le_trans hδn_leδ hδ_leδ4
    have h_eq1 : δ_n = (2 : ℝ)^(-(n : ℝ)) := by simp [dyadicDelta, δ_n] <;> ring
    have h_eq2 : δ4 = (2 : ℝ)^(-(N0 : ℝ)) := by simp [δ4] <;> ring
    have h2 : (2 : ℝ)^(-(n : ℝ)) ≤ (2 : ℝ)^(-(N0 : ℝ)) := by
      rw [h_eq1, h_eq2] at h1; exact h1
    have h3 : Real.log ((2 : ℝ)^(-(n : ℝ))) ≤ Real.log ((2 : ℝ)^(-(N0 : ℝ))) := Real.log_le_log (by positivity) h2
    have h4 : -(n : ℝ) * Real.log 2 ≤ -(N0 : ℝ) * Real.log 2 := by
      simpa [Real.log_rpow] using h3
    have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h6 : -(n : ℝ) ≤ -(N0 : ℝ) := by
      calc -(n : ℝ)
        = (-(n : ℝ) * Real.log 2) / Real.log 2 := by field_simp [h5.ne'] <;> ring
      _ ≤ (-(N0 : ℝ) * Real.log 2) / Real.log 2 := by gcongr
      _ = -(N0 : ℝ) := by field_simp [h5.ne'] <;> ring
    have h7 : (N0 : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast h7
  have h_K_log_absorb' : ∀ (m : ℕ), dyadicDelta m ≤ δ → δ < 2 * dyadicDelta m →
      (2 * (m : ℝ) + 10) ≤ (dyadicDelta m)^(-reserved_budget / 24) := by
    intro m hdm_leδ _
    have h_m_ge_N0 : m ≥ N0 := by
      have h1 : dyadicDelta m ≤ δ4 := le_trans hdm_leδ hδ_leδ4
      have h_eq1 : dyadicDelta m = (2 : ℝ)^(-(m : ℝ)) := by simp [dyadicDelta] <;> ring
      have h_eq2 : δ4 = (2 : ℝ)^(-(N0 : ℝ)) := by simp [δ4] <;> ring
      have h2 : (2 : ℝ)^(-(m : ℝ)) ≤ (2 : ℝ)^(-(N0 : ℝ)) := by
        rw [h_eq1, h_eq2] at h1; exact h1
      have h3 : Real.log ((2 : ℝ)^(-(m : ℝ))) ≤ Real.log ((2 : ℝ)^(-(N0 : ℝ))) := Real.log_le_log (by positivity) h2
      have h4 : -(m : ℝ) * Real.log 2 ≤ -(N0 : ℝ) * Real.log 2 := by
        simpa [Real.log_rpow] using h3
      have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h6 : -(m : ℝ) ≤ -(N0 : ℝ) := by
        calc -(m : ℝ)
          = (-(m : ℝ) * Real.log 2) / Real.log 2 := by field_simp [h5.ne'] <;> ring
        _ ≤ (-(N0 : ℝ) * Real.log 2) / Real.log 2 := by gcongr
        _ = -(N0 : ℝ) := by field_simp [h5.ne'] <;> ring
      exact_mod_cast (by linarith : (N0 : ℝ) ≤ (m : ℝ))
    have h4 : (2 * (m : ℝ) + 10) ≤ a ^ m := hN0 m h_m_ge_N0
    have h5 : a ^ m = (dyadicDelta m)^(-reserved_budget / 24) := by
      dsimp only [a]
      have h6 : (a ^ m : ℝ) = (2 : ℝ)^(reserved_budget / 24 * (m : ℝ)) := by
        have h61 : (a ^ m : ℝ) = a ^ (m : ℝ) := by norm_cast
        rw [h61]
        have h62 : a = (2 : ℝ)^(reserved_budget / 24) := by simp [a]
        rw [h62]
        rw [Real.rpow_mul (by norm_num)] <;> ring
      have h7 : (dyadicDelta m)^(-reserved_budget / 24) = (2 : ℝ)^((m : ℝ) * (reserved_budget / 24)) := by
        have h8 : dyadicDelta m = (2 : ℝ)^(-(m : ℝ)) := by simp [dyadicDelta] <;> ring
        rw [h8]
        have h9 : ((2 : ℝ)^(-(m : ℝ))) ^ (-reserved_budget / 24) = (2 : ℝ)^((-(m : ℝ)) * (-reserved_budget / 24)) := by
          rw [Real.rpow_mul (by norm_num)]
        rw [h9]
        have h10 : (-(m : ℝ)) * (-reserved_budget / 24) = (m : ℝ) * (reserved_budget / 24) := by ring
        rw [h10]
      have h9 : reserved_budget / 24 * (m : ℝ) = (m : ℝ) * (reserved_budget / 24) := by ring
      rw [h6, h7, h9]
    have h_goal : 2 * (m : ℝ) + 10 ≤ (dyadicDelta m)^(-reserved_budget / 24) := by
      calc 2 * (m : ℝ) + 10
        ≤ (a ^ m : ℝ) := h4
      _ = (dyadicDelta m)^(-reserved_budget / 24) := h5
    exact h_goal

  -- hδ_slope
  have hδ_slope' : δ ^ (reserved_budget / 6) ≤ 1 / 81 := by
    have h2 : δ ^ (reserved_budget / 6) ≤ δ5 ^ (reserved_budget / 6) := by gcongr
    have h3 : δ5 ^ (reserved_budget / 6) = 1 / 81 := by
      dsimp only [δ5]
      have h_eq : 1 / (reserved_budget / 6) = 6 / reserved_budget := by
        field_simp [hbudget_pos.ne'] <;> ring
      have h_eq' : (6 / reserved_budget) = 1 / (reserved_budget / 6) := h_eq.symm
      rw [h_eq']
      exact rpow_root_cancel (by norm_num) (by positivity)
    rw [h3] at h2; exact h2

  -- Convert h_absorb_ambient' to expected type
  have h_absorb_ambient'' : ∀ (m : ℕ), dyadicDelta m ≤ δ → δ < 2 * dyadicDelta m →
      (1000000 : ℝ) ≤ (dyadicDelta m)^(-reserved_budget / 3) := by
    intro m h1 h2
    have h3 := h_absorb_ambient' m h1 h2
    have h4 : -ρ_T_loc = -reserved_budget / 3 := by
      have h5 : ρ_T_loc = reserved_budget / 3 := by simp [ρ_T_loc]
      rw [h5] <;> ring
    rw [h4] at h3
    exact h3

  -- Step 5: Apply bridge_inner
  exact bridge_inner δ s t hs_pos hs_lt_one hst hδ_lt_one C_P C_T hCP_pos hCT_pos P hP_bdd hP_sset T hT_bdd
    Tp hTp_sub hTp_sset hTp_near hTp_bdd
    reserved_budget hbudget_pos lam hlam_pos ε_tube hε_tube_pos hε_tube_lt_lam hCT_bound hδ_le_one
    h_absorb_snap' h_absorb_snap18' h_absorb_ambient'' h_K_log_absorb' hδ_slope'

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

end
