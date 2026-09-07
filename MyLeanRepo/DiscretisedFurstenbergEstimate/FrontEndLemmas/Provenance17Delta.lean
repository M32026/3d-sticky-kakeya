module

/-
  17Δ Provenance Lemma.

  Proves that each coarse parent in T_Delta_global_dyadic has an original
  oriented line within 17Δ, combining:
  - Parent movement: 10Δ (via InParent + antilipschitz)
  - Section 9 representative error: 7δ_n
  - Triangle: 10Δ + 7δ_n ≤ 17Δ (since δ_n ≤ Δ)

  Whiteprint node: appendix_a_alternative / provenance_17_delta
  Dependencies: TDeltaGlobalConstruction, SnapTubeProvenance, H2_Migration_Adapters
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.SnapTubeProvenance
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.H2_Migration_Adapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure
open DirecretisedFurstenbergEstimate.AppendixA.SnapTubeProvenance
open DirecretisedFurstenbergEstimate.AppendixA.H2Migration
open DirecretisedFurstenbergEstimate.AppendixA.TDeltaGlobal
open CoordinatePartition (swapLine swapLine_isometry swapLine_invol)
open DyadicCardToNcover (toAffineLine)

/-- Corrected 17Δ provenance: each coarse parent in T_Delta_global_dyadic
    has an original oriented line within 17Δ.

    Combines parent movement (10Δ via InParent) and Section 9 representative
    error (7δ_n), then triangle inequality.

    Hypotheses:
    - T₀: Section 9 fine dyadic tube family
    - T_source: A2 image of T₀ under dyadicTubeToA2
    - hT0_slope: each U ∈ T₀ has -1 ≤ U.slope < 1 (from dyadic strip bound)
    - hT0_intercept: each U ∈ T₀ has |U.intercept| ≤ 3
    - h_section9_prov: Section 9 gives each U_fine ∈ T₀ an ℓ_orig ∈ T_oriented
      within 7δ_n of toAffineLine U_fine
-/
lemma provenance_17_delta
    {n m : ℕ} {hnm : m ≤ n}
    {Δ δ_n : ℝ}
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_le_Δ : δ_n ≤ Δ)
    (hΔ_eq : Δ = dyadicDelta m)
    (T₀ : Finset (DyadicTube n))
    (T_source : Finset AffineLine)
    (T_oriented : Set AffineLine)
    (hT_source_eq : T_source = Finset.image (dyadicTubeToA2 (m := n)) T₀)
    (hT0_slope : ∀ U ∈ T₀, -1 ≤ U.slope ∧ U.slope < 1)
    (hT0_intercept : ∀ U ∈ T₀, |U.intercept| ≤ 3)
    (h_section9_prov : ∀ (U_fine : DyadicTube n), U_fine ∈ T₀ →
        ∃ (ℓ_orig : AffineLine), ℓ_orig ∈ T_oriented ∧
          dist (toAffineLine U_fine) ℓ_orig ≤ 7 * δ_n) :
    ∀ (U_coarse : DyadicTube m), U_coarse ∈ T_Delta_global_dyadic hnm T_source →
      ∃ (ℓ_orig : AffineLine), ℓ_orig ∈ T_oriented ∧
        dist (toAffineLine U_coarse) ℓ_orig ≤ 17 * Δ := by
  intro U_coarse hU_coarse

  -- Step 1: U_coarse comes from some ℓ ∈ T_source via sourceParent ∘ snapTube
  have h1 : ∃ (ℓ : AffineLine), ℓ ∈ T_source ∧
      sourceParent hnm (snapTube n ℓ) = U_coarse := by
    simpa [T_Delta_global_dyadic, Finset.mem_image] using hU_coarse
  rcases h1 with ⟨ℓ, hℓ_in_source, hU_eq⟩

  -- Step 2: ℓ = dyadicTubeToA2 U_fine for some U_fine ∈ T₀
  have h2 : ∃ (U_fine : DyadicTube n), U_fine ∈ T₀ ∧ ℓ = dyadicTubeToA2 U_fine := by
    rw [hT_source_eq] at hℓ_in_source
    rcases Finset.mem_image.mp hℓ_in_source with ⟨U_fine, hU_fine, rfl⟩
    exact ⟨U_fine, hU_fine, rfl⟩
  rcases h2 with ⟨U_fine, hU_fine_in_T0, rfl⟩

  set ℓ := dyadicTubeToA2 U_fine with hℓ_def

  -- Step 3: Bounds on ℓ (from U_fine)
  have h_slope_ℓ : tubeSlope ℓ = U_fine.slope := dyadicTubeToA2_slope U_fine
  have h_intercept_ℓ : tubeIntercept ℓ = U_fine.intercept := dyadicTubeToA2_intercept U_fine
  have h_slope_bounds : -1 ≤ tubeSlope ℓ ∧ tubeSlope ℓ < 1 := by
    rw [h_slope_ℓ] <;> exact hT0_slope U_fine hU_fine_in_T0
  have h_intercept_bound : |tubeIntercept ℓ| ≤ 3 := by
    rw [h_intercept_ℓ] <;> exact hT0_intercept U_fine hU_fine_in_T0

  -- Step 4: Bounds on snapTube n ℓ (fine dyadic tube)
  have h_fine_strip : -(2 ^ n : ℤ) ≤ (snapTube n ℓ).a ∧ (snapTube n ℓ).a < (2 ^ n : ℤ) :=
    snapTube_slope_strip_bound h_slope_bounds.1 h_slope_bounds.2
  have h_fine_intercept : |(snapTube n ℓ).intercept| ≤ 3 :=
    snapTube_intercept_bound h_intercept_bound

  -- Step 5: Bounds on U_coarse (coarse parent) via SnapTubeProvenance
  have h_coarse_slope : |U_coarse.slope| ≤ 1 :=
    sourceParent_slope_bound hnm (snapTube n ℓ) U_coarse hU_eq h_fine_strip
  have h_coarse_intercept : |U_coarse.intercept| ≤ 3 :=
    sourceParent_intercept_bound hnm (snapTube n ℓ) U_coarse hU_eq h_fine_intercept

  -- Step 6: InParent relation
  have hdm_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have hInParent0 : InParent (dyadicDelta m) hdm_pos ℓ (dyadicTubeToA2 U_coarse) := by
    have h_iff := sourceParent_snap_iff_inParent hnm ℓ U_coarse hdm_pos
    exact h_iff.mp hU_eq
  have hInParent : InParent Δ hΔ_pos ℓ (dyadicTubeToA2 U_coarse) := by
    subst hΔ_eq
    exact hInParent0

  -- Step 7: Direction bounds
  have h_dir_ℓ : (LemmaE.getDirV ℓ) 1 ≠ 0 :=
    A2TypedQTTCAdapter.dyadicTubeToA2_getDirV_ne_zero U_fine
  have h_dir_U : (LemmaE.getDirV (dyadicTubeToA2 U_coarse)) 1 ≠ 0 :=
    A2TypedQTTCAdapter.dyadicTubeToA2_getDirV_ne_zero U_coarse

  -- Step 8: Slope/intercept bounds for dyadicTubeToA2 forms
  have h_slope_ℓ' : |tubeSlope ℓ| ≤ 1 := by
    have h : |tubeSlope ℓ| = |U_fine.slope| := by rw [h_slope_ℓ]
    rw [h]
    have h' := h_slope_bounds
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_slope_U : |tubeSlope (dyadicTubeToA2 U_coarse)| ≤ 1 := by
    have h : tubeSlope (dyadicTubeToA2 U_coarse) = U_coarse.slope := dyadicTubeToA2_slope U_coarse
    rw [h] <;> exact h_coarse_slope
  have h_intercept_ℓ' : |tubeIntercept ℓ| ≤ 3 := h_intercept_bound
  have h_intercept_U : |tubeIntercept (dyadicTubeToA2 U_coarse)| ≤ 3 := by
    have h : tubeIntercept (dyadicTubeToA2 U_coarse) = U_coarse.intercept := dyadicTubeToA2_intercept U_coarse
    rw [h] <;> exact h_coarse_intercept

  -- Step 9: Parent movement via inParent_dist_lt_tenDelta
  have h_parent_move : dist ℓ (dyadicTubeToA2 U_coarse) < 10 * Δ :=
    inParent_dist_lt_tenDelta Δ hΔ_pos ℓ (dyadicTubeToA2 U_coarse) hInParent
      h_dir_ℓ h_dir_U h_slope_ℓ' h_slope_U h_intercept_ℓ' h_intercept_U

  -- Step 10: Convert to toAffineLine distance via swapLine isometry
  have h_swap_eq1 : ℓ = swapLine (toAffineLine U_fine) := by
    simp [ℓ, dyadicTubeToA2] <;> rfl
  have h_swap_eq2 : dyadicTubeToA2 U_coarse = swapLine (toAffineLine U_coarse) := by
    simp [dyadicTubeToA2] <;> rfl
  have h_parent_move' : dist (toAffineLine U_fine) (toAffineLine U_coarse) < 10 * Δ := by
    rw [h_swap_eq1, h_swap_eq2] at h_parent_move
    have h_iso : dist (swapLine (toAffineLine U_fine)) (swapLine (toAffineLine U_coarse)) =
        dist (toAffineLine U_fine) (toAffineLine U_coarse) :=
      swapLine_isometry.dist_eq (toAffineLine U_fine) (toAffineLine U_coarse)
    rw [h_iso] at h_parent_move
    exact h_parent_move

  -- Step 11: Section 9 provenance
  rcases h_section9_prov U_fine hU_fine_in_T0 with ⟨ℓ_orig, hℓ_orig_in, h_dist_fine⟩

  -- Step 12: Triangle inequality
  have h_triangle : dist (toAffineLine U_coarse) ℓ_orig ≤
      dist (toAffineLine U_coarse) (toAffineLine U_fine) +
      dist (toAffineLine U_fine) ℓ_orig := dist_triangle _ _ _
  have h_comm : dist (toAffineLine U_coarse) (toAffineLine U_fine) =
      dist (toAffineLine U_fine) (toAffineLine U_coarse) := dist_comm _ _
  have h7δ : 7 * δ_n ≤ 7 * Δ := by gcongr <;> linarith
  have h_final : dist (toAffineLine U_coarse) ℓ_orig < 17 * Δ := by
    calc dist (toAffineLine U_coarse) ℓ_orig
      ≤ dist (toAffineLine U_coarse) (toAffineLine U_fine) +
          dist (toAffineLine U_fine) ℓ_orig := h_triangle
    _ = dist (toAffineLine U_fine) (toAffineLine U_coarse) +
          dist (toAffineLine U_fine) ℓ_orig := by rw [h_comm]
    _ < 10 * Δ + 7 * δ_n := by linarith
    _ ≤ 10 * Δ + 7 * Δ := by gcongr
    _ = 17 * Δ := by ring
  exact ⟨ℓ_orig, hℓ_orig_in, by linarith⟩

end DirecretisedFurstenbergEstimate.FrontEndLemmas
