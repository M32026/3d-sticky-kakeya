module

/-
  Transfer lemma for A2 Typed QTTC Adapter.

  Provides `affine_sset_transfer`: transfer finite δ-S-set from dyadic tubes
  to affine lines via dyadicTubeToA2.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_TypedQTTC_Adapter.Basic

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept InParent parentCell pointFiber)
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
  (snapTube dyadicTubeToA2 dyadicTubeToA2_slope dyadicTubeToA2_intercept
   sourceParent_snap_iff_inParent ballGrowth_transfer_snap snap_fiber_bound)
open DirecretisedFurstenbergEstimate.AppendixA.A2Thinning (thin_coarse_tubes_affine_separated)
open DirecretisedFurstenbergEstimate.AppendixA.A2Helpers
  (perpendicular_to_algebraic_distance c2_bound_helper
   dyadicDelta_div_refinement floor_real_ediv
   coarse_slope_index_floor coarse_intercept_index_floor)
open DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
  (qttc_for_dyadicTubes globalCoarseG pointFiberG sp)
open LemmaE (affineLineParams)
open DiscretisedFurstenbergEstimate.InductionOnScales (tubeParamDistLinf dist_le_two_linf)
open DirecretisedFurstenbergEstimate.InductionOnScales (coarseTubeToM refinementFactor)
open DirecretisedFurstenbergEstimate.AppendixA.TypedDyadicInfrastructure (sourceParent)
open DyadicToAffineAdapters (toAffineLine_co_lipschitz)
open DyadicCardToNcover (tubeDirV lineOfSlopeIntercept_direction toAffineLine)
open CoordinatePartition (swapCoords swapCoordsLI)

/-- Transfer finite δ-S-set from dyadic tubes to affine lines via dyadicTubeToA2. -/
lemma affine_sset_transfer {m : ℕ} {Δ' Δ s C₂ C₂_typed : ℝ}
    {C_thin : Finset (DyadicTube m)} {C'_affine : Finset AffineLine}
    (h_sset_thin : IsFiniteDeltaSSet Δ' s (C₂_typed * 1936) C_thin)
    (h_image : C'_affine = C_thin.image dyadicTubeToA2)
    (h_slope : ∀ U ∈ C_thin, |U.slope| ≤ 1)
    (h_intercept : ∀ U ∈ C_thin, |U.intercept| ≤ 3)
    (hC2_one : 1 ≤ C₂_typed)
    (hΔ'_le_Δ : Δ' ≤ Δ)
    (hΔ_pos : 0 < Δ)
    (hs : 0 ≤ s)
    (hC2_def : C₂ = C₂_typed * 1936 * (88 : ℝ)^s)
    (h_sep_delta : SeparatedAt Δ (C'_affine : Set AffineLine))
    (hC_affine_nonempty : C'_affine.Nonempty)
    (hC_thin_nonempty : C_thin.Nonempty) :
    IsFiniteDeltaSSet Δ s C₂ C'_affine := by
  have hC2_one' : 1 ≤ C₂ := by
    rw [hC2_def]
    have h1 : 1 ≤ C₂_typed := hC2_one
    have h3 : 1 ≤ (88 : ℝ)^s := by
      have h : (1 : ℝ)^s ≤ (88 : ℝ)^s := Real.rpow_le_rpow (by linarith) (by norm_num) hs
      have h9 : (1 : ℝ)^s = 1 := Real.one_rpow s
      rw [h9] at h; exact h
    have h4 : 1 ≤ (1936 : ℝ) := by norm_num
    have h6 : 1 ≤ C₂_typed * 1936 := by
      have h7 : 1 * 1 ≤ C₂_typed * 1936 := mul_le_mul h1 h4 (by norm_num) (by linarith)
      simpa using h7
    have h8 : 1 ≤ C₂_typed * 1936 * (88 : ℝ)^s := by
      have h9 : 1 * 1 ≤ (C₂_typed * 1936) * (88 : ℝ)^s :=
        mul_le_mul h6 h3 (by positivity) (by linarith)
      simpa using h9
    simpa using h8
  refine' ⟨hC_affine_nonempty, hΔ_pos, hC2_one', hs, h_sep_delta, _⟩
  intro x r hr
  let F_filter := C'_affine.filter fun y => dist y x ≤ r
  by_cases h_empty : F_filter.Nonempty
  · rcases h_empty with ⟨c1, hc1⟩
    have hc1_in : c1 ∈ C'_affine := (Finset.mem_filter.mp hc1).1
    have hdist1 : dist c1 x ≤ r := (Finset.mem_filter.mp hc1).2
    rcases Finset.mem_image.mp (by rw [h_image] at hc1_in; exact hc1_in) with ⟨U1, hU1_thin, rfl⟩
    have hU1_s : |U1.slope| ≤ 1 := h_slope U1 hU1_thin
    have hU1_i : |U1.intercept| ≤ 3 := h_intercept U1 hU1_thin
    have h5 : ∀ c ∈ F_filter, ∃ (U : DyadicTube m), U ∈ C_thin ∧ dyadicTubeToA2 U = c ∧ U.dist U1 ≤ 88 * r := by
      intro c hc
      have hc_in : c ∈ C'_affine := (Finset.mem_filter.mp hc).1
      have hdist : dist c x ≤ r := (Finset.mem_filter.mp hc).2
      rcases Finset.mem_image.mp (by rw [h_image] at hc_in; exact hc_in) with ⟨U, hU_thin, rfl⟩
      have hU_s : |U.slope| ≤ 1 := h_slope U hU_thin
      have hU_i : |U.intercept| ≤ 3 := h_intercept U hU_thin
      have h_ldist : dist (dyadicTubeToA2 U) x ≤ r := hdist
      have h_rdist : dist x (dyadicTubeToA2 U1) ≤ r := by rw [dist_comm]; exact hdist1
      have h_sum : dist (dyadicTubeToA2 U) x + dist x (dyadicTubeToA2 U1) ≤ r + r := add_le_add h_ldist h_rdist
      have h_dist_c1 : dist (dyadicTubeToA2 U) (dyadicTubeToA2 U1) ≤ 2 * r := by
        calc dist (dyadicTubeToA2 U) (dyadicTubeToA2 U1)
          ≤ dist (dyadicTubeToA2 U) x + dist x (dyadicTubeToA2 U1) := dist_triangle _ _ _
        _ ≤ r + r := h_sum
        _ = 2 * r := by ring
      have h_dist_dyadic : U.dist U1 ≤ 44 * dist (dyadicTubeToA2 U) (dyadicTubeToA2 U1) :=
        dyadicTube_dist_le_44_affine U U1 hU_s hU1_s hU_i hU1_i
      have h_final : U.dist U1 ≤ 88 * r := by
        calc U.dist U1
          ≤ 44 * dist (dyadicTubeToA2 U) (dyadicTubeToA2 U1) := h_dist_dyadic
        _ ≤ 44 * (2 * r) := mul_le_mul_of_nonneg_left h_dist_c1 (by norm_num)
        _ = 88 * r := by ring
      exact ⟨U, hU_thin, rfl, h_final⟩
    let S_dyadic := C_thin.filter fun U => U.dist U1 ≤ 88 * r
    classical
    let default_tube : DyadicTube m := Classical.choose hC_thin_nonempty
    let f : AffineLine → DyadicTube m := fun c =>
      if h : c ∈ F_filter then (h5 c h).choose else default_tube
    have hf_spec : ∀ c ∈ F_filter, f c ∈ C_thin ∧ dyadicTubeToA2 (f c) = c ∧ (f c).dist U1 ≤ 88 * r := by
      intro c hc
      have h_let : f c = (h5 c hc).choose := by simp [f, hc]
      rw [h_let]
      exact (h5 c hc).choose_spec
    have hf1 : ∀ c ∈ F_filter, f c ∈ C_thin := fun c hc => (hf_spec c hc).1
    have hf2 : ∀ c ∈ F_filter, dyadicTubeToA2 (f c) = c := fun c hc => (hf_spec c hc).2.1
    have hf3 : ∀ c ∈ F_filter, (f c).dist U1 ≤ 88 * r := fun c hc => (hf_spec c hc).2.2
    have h_f_in_S : ∀ c ∈ F_filter, f c ∈ S_dyadic := by
      intro c hc
      have h1 : f c ∈ C_thin := hf1 c hc
      have h2 : (f c).dist U1 ≤ 88 * r := hf3 c hc
      simp only [S_dyadic, Finset.mem_filter] <;> exact ⟨h1, h2⟩
    have h_inj : Set.InjOn f (F_filter : Set AffineLine) := by
      intro c1 hc1 c2 hc2 h
      have h_eq1 : dyadicTubeToA2 (f c1) = c1 := hf2 c1 hc1
      have h_eq2 : dyadicTubeToA2 (f c2) = c2 := hf2 c2 hc2
      rw [h] at h_eq1
      exact h_eq1.symm.trans h_eq2
    have h_image_sub : F_filter.image f ⊆ S_dyadic := by
      intro U hU
      rcases Finset.mem_image.mp hU with ⟨c, hc, rfl⟩
      exact h_f_in_S c hc
    have h_card_img : (F_filter.image f).card = F_filter.card :=
      Finset.card_image_of_injOn h_inj
    have h_nat : F_filter.card ≤ S_dyadic.card := by
      rw [← h_card_img]
      exact Finset.card_le_card h_image_sub
    have h6 : (F_filter.card : ℝ) ≤ (S_dyadic.card : ℝ) := Nat.cast_le.mpr h_nat
    have h88r : Δ' ≤ 88 * r := by
      have h9 : Δ' ≤ Δ := hΔ'_le_Δ
      have h10 : Δ ≤ r := hr
      linarith
    have h7 : ((S_dyadic).card : ℝ) ≤ (C₂_typed * 1936) * (88 * r) ^ s * (C_thin.card : ℝ) :=
      h_sset_thin.2.2.2.2.2 U1 (88 * r) h88r
    have h_card_eq : (C'_affine.card : ℝ) = (C_thin.card : ℝ) := by
      rw [h_image]
      simp [Finset.card_image_of_injective _ dyadicTubeToA2_injective]
    calc (F_filter.card : ℝ)
      ≤ (S_dyadic.card : ℝ) := h6
    _ ≤ (C₂_typed * 1936) * (88 * r) ^ s * (C_thin.card : ℝ) := h7
    _ = C₂ * r ^ s * (C'_affine.card : ℝ) := by
      have hpow : (88 * r) ^ s = (88 : ℝ)^s * r ^ s := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
      rw [hpow, h_card_eq, hC2_def] <;> ring
  · have h9 : F_filter = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_empty
    have h_goal : (F_filter.card : ℝ) ≤ C₂ * r ^ s * (C'_affine.card : ℝ) := by
      rw [h9]
      have h_rpos : 0 < r := lt_of_lt_of_le hΔ_pos hr
      have h10 : 0 ≤ C₂ * r ^ s * (C'_affine.card : ℝ) := by positivity
      simpa using h10
    simpa [F_filter] using h_goal


end DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter
