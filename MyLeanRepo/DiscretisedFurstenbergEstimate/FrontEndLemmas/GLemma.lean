module

/-
  G lemma: Construct GOutput from B1 bridge data.

  Takes the B1 bridge output (config', b1) and all preceding numerical/geometric
  data, then constructs:
  - A1 output via NiceConfigToA1
  - Fixed source family T_source_dyadic / T_source
  - Global coarse parent T_Delta
  - 17Δ provenance
  - Dyadic cardinality bound h_dyadic
  - Slope/intercept bounds
  - All numerical hypotheses consumed by H

  Whiteprint node: front_end_lemmas / G_lemma
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.GOutput
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.HDyadicBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.Provenance17Delta
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TSubSource
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.FrontEndLemmas
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
open DirecretisedFurstenbergEstimate.Section9
open DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly
open DirecretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds
open DiscretisedFurstenbergEstimate.InductionConfigurations
open HeavyParentFiltering
open B1HardFields
open SquareGeometry
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter

/-- G lemma: construct GOutput from B1 bridge data and preceding hypotheses. -/
def front_end_G
    -- Scale parameters
    {n m : ℕ} (hnm : m ≤ n) (hm_pos : 1 ≤ m) (hn_even : n % 2 = 0)
    {s t u ε Δ δ_n δ A εA : ℝ}
    (hΔ_eq' : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (h_eq_n : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hΔ_lt_one : Δ < 1) (hΔ_lt_third : Δ < 1 / 3)
    (hδ_n_pos : 0 < δ_n) (hδ_le_D : δ_n ≤ Δ)
    (hδ_pos : 0 < δ) (hδ_le_δ_n' : δ ≤ δ_n) (hδ_n_le_4δ' : δ_n ≤ 4 * δ)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsu : s < u) (hu_pos : 0 < u) (h_run_lt_two : u < 2)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hA_one : 1 ≤ A)
    (hQTTC : ParameterSelectionQTTC s A)
    (hεA_eq : εA = ε / 50)
    -- B1 bridge output
    {C₁ : ℝ} {M : ℕ}
    (config_n : DiscretisedFurstenbergEstimate.CombiningTheorem.NiceConfiguration n s C₁ M)
    (config' : DiscretisedFurstenbergEstimate.CombiningTheorem.NiceConfiguration n s C₁ M)
    (b1 : B1BridgeDecomposition n m hnm s C₁ M config' Δ δ_n u ε)
    (hconfig'_subset : config'.P₀ ⊆ config_n.P₀)
    (hconfig'_T0_eq : config'.T₀ = config_n.T₀)
    -- Numerical data
    (h_small_A2 : AppendixA.A2.A2_Smallness Δ δ_n s u ε A
        ((MainAppendix.affineLine_packing_constant : ℝ) + 1) (M : ℝ))
    (h_uniform_num : ∀ (u : ℝ), t ≤ u → u ≤ 2 → AssemblyNumericalBounds Δ s u ε)
    (h_absorb_energy :
        (MainAppendix.plane_energy_constant s u 2) *
        (MainAppendix.plane_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_absorb_Kpack : (CGlobalCardBound.kPack 1 17 : ℝ) ≤
        Real.rpow Δ (ε / 20 - 3 * ε))
    -- Point bounds
    (h_points_in_ball_R :
        (config_n.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) ⊆
        Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2))
    -- Tube families
    (T_oriented : Set AffineLine)
    (h_section9_prov : ∀ (U : DiscretisedFurstenbergEstimate.DyadicTube n), U ∈ config'.T₀ →
        ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧ dist (DyadicCardToNcover.toAffineLine U) ℓ ≤ 7 * δ_n)
    (T_original : Set AffineLine)
    (allTubes : Set AffineLine)
    (hT_original_sub : T_original ⊆ allTubes)
    -- Swap/Section 9 setup
    (swapped : Bool)
    (h_swapped_true : swapped = true → T_oriented = CoordinatePartition.swapLine '' T_original)
    (h_swapped_false : swapped = false → T_oriented = T_original)
    -- Coarse failure
    (h_coarse_failure_HDyadic :
        Metric.externalCoveringNumber (Real.sqrt δ).toNNReal allTubes ≤
        ENNReal.ofReal (Real.rpow δ (-(s + εA))))
    -- RKP
    (δ₀_RKP : ℝ) (hΔ_le_RKP : Δ ≤ δ₀_RKP)
    (hRKP_uniform : ∀ (u : ℝ), t ≤ u → u ≤ 2 → RKPAtExponent s u ε δ₀_RKP)
    (h576ε_lt : 576 * ε < t - s)
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    -- δ_n ≤ Δ/4
    (hδ_le_quarter : δ_n ≤ Δ / 4) :
    GOutput n m hnm Δ δ_n s u ε T_oriented := by
  -- Step 1: A1 output from B1 bridge
  let a1 : A1_Output Δ δ_n u s ε :=
    AppendixA.NiceConfigToA1.niceConfig_to_a1_output
      (n := n) (m := m) (hnm := hnm)
      (s := s) (ε := ε) (Δ := Δ) (δ := δ_n) (t := u)
      (b1 := b1)
      hΔ_eq' h_eq_n
      hΔ_pos hΔ_lt_half hδ_n_pos
      hu_pos h_run_lt_two
      hs_pos hs_lt_one hε_pos h_small

  have h_points_in_ball' : ∀ Q hQ, (a1.points Q hQ : Set EuclideanPlane) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2) := by
    intro Q hQ
    have h1 : (a1.points Q hQ : Set EuclideanPlane) ⊆
        (config'.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) :=
      AppendixA.NiceConfigToA1.niceConfig_to_a1_output_points_subset
        (hnm := hnm) (b1 := b1)
        hΔ_eq' h_eq_n
        hΔ_pos hΔ_lt_half hδ_n_pos
        hu_pos h_run_lt_two hs_pos hs_lt_one hε_pos h_small Q hQ
    have h2 : (config'.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) ⊆
        (config_n.P₀.image (CoordinatePartition.swapCoords ∘ localSquareCenter) : Set EuclideanPlane) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨p, hp, rfl⟩
      have hp' : p ∈ config_n.P₀ := hconfig'_subset hp
      exact Finset.mem_image.mpr ⟨p, hp', rfl⟩
    exact Set.Subset.trans (Set.Subset.trans h1 h2) h_points_in_ball_R

  -- Step 2: T_source construction
  let T_source_dyadic : Finset (DiscretisedFurstenbergEstimate.DyadicTube n) :=
    config'.P₀.biUnion (fun p => tubeFamilyOpt config' p)
  let T_source : Finset AppendixA.FineTube :=
    T_source_dyadic.image (AppendixA.A2DyadicAdapter.dyadicTubeToA2 (m := n))
  let T_Delta : Finset AppendixA.CoarseTube :=
    AppendixA.TDeltaGlobal.T_Delta_global hnm T_source

  have hT_source_eq : T_source = T_source_dyadic.image (AppendixA.A2DyadicAdapter.dyadicTubeToA2 (m := n)) := by
    rfl

  -- Step 3: Fiber inclusion
  have hT_source_dyadic : ∀ (p : DiscretisedFurstenbergEstimate.DyadicSquare n) (hp : p ∈ config'.P₀),
      config'.tubeFamily p hp ⊆ T_source_dyadic := by
    intro p hp
    have h1 : tubeFamilyOpt config' p = config'.tubeFamily p hp := tubeFamilyOpt_eq config' hp
    have h2 : tubeFamilyOpt config' p ⊆ T_source_dyadic :=
      Finset.subset_biUnion_of_mem (fun p => tubeFamilyOpt config' p) hp
    rw [h1] at h2
    exact h2

  have hT_sub_source : ∀ (p : EuclideanPlane), a1.tubes p ⊆ T_source :=
    niceConfig_to_a1_output_tubes_subset_Tsource
      (hnm := hnm) (b1 := b1) (hΔ_eq := hΔ_eq') (hδ_eq := h_eq_n)
      hΔ_pos hΔ_lt_half hδ_n_pos hu_pos h_run_lt_two
      hs_pos hs_lt_one hε_pos h_small
      T_source_dyadic hT_source_dyadic

  have hKpack_le_ε : a1.K_pack ≤ Real.rpow Δ (-ε) := by
    have h1 : 6 * a1.K_pack ≤ Real.rpow Δ (-ε) := h_small_A2.hKpack_loss_strong
    have h2 : 0 ≤ Real.rpow Δ (-ε) := Real.rpow_nonneg hΔ_pos.le (-ε)
    linarith

  -- Step 4: Slope/intercept bounds on T_source
  have h_slope_T_source : ∀ ℓ ∈ T_source, |tubeSlope ℓ| ≤ 1 := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨T, hT, rfl⟩
    rcases Finset.mem_biUnion.mp hT with ⟨p, hp, hT'⟩
    have h_eq_tube : tubeFamilyOpt config' p = config'.tubeFamily p hp := tubeFamilyOpt_eq config' hp
    have hT_in : T ∈ config'.tubeFamily p hp := by
      rw [←h_eq_tube]; exact hT'
    have h_strip : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) :=
      b1.h_tubes_strip p hp T hT_in
    have h_slope_le_one : |T.slope| ≤ 1 := by
      have h1 : T.slope = (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n := by
        exact rfl
      rw [h1]
      have h2 : (T.a : ℝ) ≥ -((2 ^ n : ℝ)) := by exact_mod_cast h_strip.1
      have h3 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_strip.2
      have h4 : DiscretisedFurstenbergEstimate.dyadicDelta n = 1 / (2 ^ n : ℝ) := by
        simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> field_simp
      rw [h4]
      have h_pos : 0 ≤ 1 / (2 ^ n : ℝ) := by positivity
      have h_neg_eq : -((2 ^ n : ℝ)) * (1 / (2 ^ n : ℝ)) = -1 := by field_simp <;> ring
      have h5 : -1 ≤ (T.a : ℝ) * (1 / (2 ^ n : ℝ)) := by
        have h51 : -((2 ^ n : ℝ)) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
        have h : -((2 ^ n : ℝ)) * (1 / (2 ^ n : ℝ)) ≤ (T.a : ℝ) * (1 / (2 ^ n : ℝ)) :=
          mul_le_mul_of_nonneg_right h51 h_pos
        rw [h_neg_eq] at h
        exact h
      have h6 : (T.a : ℝ) * (1 / (2 ^ n : ℝ)) < 1 := by
        have h61 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_strip.2
        have h_pos2 : 0 < 1 / (2 ^ n : ℝ) := by positivity
        have h : (T.a : ℝ) * (1 / (2 ^ n : ℝ)) < (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) :=
          mul_lt_mul_of_pos_right h61 h_pos2
        have h2 : (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) = 1 := by field_simp <;> ring
        rw [h2] at h; exact h
      exact abs_le.mpr ⟨h5, by linarith⟩
    have h_eq : tubeSlope (AppendixA.A2DyadicAdapter.dyadicTubeToA2 T) = T.slope :=
      AppendixA.A2DyadicAdapter.dyadicTubeToA2_slope T
    rw [h_eq]; exact h_slope_le_one

  have h_intercept_T_source : ∀ ℓ ∈ T_source, |tubeIntercept ℓ| ≤ 3 := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨T, hT, rfl⟩
    rcases Finset.mem_biUnion.mp hT with ⟨p, hp, hT'⟩
    have h_eq_tube2 : tubeFamilyOpt config' p = config'.tubeFamily p hp := tubeFamilyOpt_eq config' hp
    have hT_in : T ∈ config'.tubeFamily p hp := by
      rw [←h_eq_tube2]; exact hT'
    have h_int : |T.intercept| ≤ 3 := b1.h_tubes_intercept p hp T hT_in
    have h_eq : tubeIntercept (AppendixA.A2DyadicAdapter.dyadicTubeToA2 T) = T.intercept :=
      AppendixA.A2DyadicAdapter.dyadicTubeToA2_intercept T
    rw [h_eq]; exact h_int

  -- Step 5: T0 slope/intercept for provenance
  have hT0_slope : ∀ U ∈ T_source_dyadic, -1 ≤ U.slope ∧ U.slope < 1 := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨p, hp, hUT⟩
    have h_eq_tube3 : tubeFamilyOpt config' p = config'.tubeFamily p hp := tubeFamilyOpt_eq config' hp
    have h_in : U ∈ config'.tubeFamily p hp := by
      rw [←h_eq_tube3]; exact hUT
    have h_strip : -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ) :=
      b1.h_tubes_strip p hp U h_in
    have h1 : -1 ≤ U.slope := by
      have h2 : U.slope = (U.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n := by exact rfl
      rw [h2]
      have h3 : -(2 ^ n : ℝ) ≤ (U.a : ℝ) := by exact_mod_cast h_strip.1
      have h4 : DiscretisedFurstenbergEstimate.dyadicDelta n = 1 / (2 ^ n : ℝ) := by
        simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> field_simp
      rw [h4]
      have h_pos : 0 ≤ 1 / (2 ^ n : ℝ) := by positivity
      have h_neg_eq : -((2 ^ n : ℝ)) * (1 / (2 ^ n : ℝ)) = -1 := by field_simp <;> ring
      have h : -((2 ^ n : ℝ)) * (1 / (2 ^ n : ℝ)) ≤ (U.a : ℝ) * (1 / (2 ^ n : ℝ)) :=
        mul_le_mul_of_nonneg_right h3 h_pos
      rw [h_neg_eq] at h
      exact h
    have h2 : U.slope < 1 := by
      have h3 : U.slope = (U.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n := by exact rfl
      rw [h3]
      have h4 : (U.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h_strip.2
      have h5 : DiscretisedFurstenbergEstimate.dyadicDelta n = 1 / (2 ^ n : ℝ) := by
        simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> field_simp
      rw [h5]
      have h_pos2 : 0 < 1 / (2 ^ n : ℝ) := by positivity
      have h : (U.a : ℝ) * (1 / (2 ^ n : ℝ)) < (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) :=
        mul_lt_mul_of_pos_right h4 h_pos2
      have h2 : (2 ^ n : ℝ) * (1 / (2 ^ n : ℝ)) = 1 := by field_simp <;> ring
      rw [h2] at h; exact h
    exact ⟨h1, h2⟩

  have hT0_intercept : ∀ U ∈ T_source_dyadic, |U.intercept| ≤ 3 := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨p, hp, hUT⟩
    have h_eq_tube4 : tubeFamilyOpt config' p = config'.tubeFamily p hp := tubeFamilyOpt_eq config' hp
    have h_in : U ∈ config'.tubeFamily p hp := by
      rw [←h_eq_tube4]; exact hUT
    exact b1.h_tubes_intercept p hp U h_in

  -- Restrict h_section9_prov to T_source_dyadic
  have hT_source_dyadic_sub_T0 : T_source_dyadic ⊆ config'.T₀ := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨p, hp, hT'⟩
    have h_eq_tube5 : tubeFamilyOpt config' p = config'.tubeFamily p hp := tubeFamilyOpt_eq config' hp
    have hT_in : T ∈ config'.tubeFamily p hp := by
      rw [←h_eq_tube5]; exact hT'
    exact config'.h_subset p hp hT_in

  have h_section9_prov_restricted : ∀ (U : DiscretisedFurstenbergEstimate.DyadicTube n), U ∈ T_source_dyadic →
      ∃ (ℓ : AffineLine), ℓ ∈ T_oriented ∧
        dist (DyadicCardToNcover.toAffineLine U) ℓ ≤ 7 * δ_n :=
    fun U hU => h_section9_prov U (hT_source_dyadic_sub_T0 hU)

  -- Step 6: 17Δ provenance
  have hδ_le_D2 : δ ≤ Δ ^ 2 := by
    rw [←hδ_n_eq2]; exact hδ_le_δ_n'

  have h_provenance_17Δ : ∀ (U : DiscretisedFurstenbergEstimate.DyadicTube m),
      U ∈ AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source →
      ∃ (ℓ_orig : AffineLine), ℓ_orig ∈ T_oriented ∧
        dist (DyadicCardToNcover.toAffineLine U) ℓ_orig ≤ 17 * Δ :=
    provenance_17_delta
      (hΔ_pos := hΔ_pos) (hΔ_lt_one := hΔ_lt_one)
      (hδ_n_pos := hδ_n_pos) (hδ_n_le_Δ := hδ_le_D)
      (hΔ_eq := hΔ_eq')
      (T₀ := T_source_dyadic) (T_source := T_source)
      (T_oriented := T_oriented)
      (by
        apply Finset.ext
        intro x
        simp [hT_source_eq, Finset.mem_image])
      hT0_slope hT0_intercept
      h_section9_prov_restricted

  have hT_Delta_provenance : (T_Delta : Set AppendixA.CoarseTube) ⊆
      Metric.cthickening (17 * Δ) (CoordinatePartition.swapLine '' T_oriented) := by
    intro T hT
    have h_img : T ∈ Finset.image (AppendixA.A2DyadicAdapter.dyadicTubeToA2 (m := m))
        (AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source) := by
      have h_set : (T_Delta : Set AffineLine) =
          Set.image (AppendixA.A2DyadicAdapter.dyadicTubeToA2 (m := m))
            (AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source) := by
        have h1 : (T_Delta : Set AffineLine) =
            (AppendixA.TDeltaGlobal.T_Delta_global hnm T_source : Set AffineLine) := by rfl
        rw [h1]
        have h2 := AppendixA.TDeltaGlobal.T_Delta_global_eq_image (hnm := hnm) (T_source := T_source)
        rw [h2]
        simp [Finset.coe_image]
      have hT' : T ∈ (T_Delta : Set AffineLine) := hT
      rw [h_set] at hT'
      simpa [Finset.mem_image] using hT'
    rcases Finset.mem_image.mp h_img with ⟨U_coarse, hU_coarse, rfl⟩
    rcases h_provenance_17Δ U_coarse hU_coarse with ⟨ℓ_orig, hℓ_orig, hdist⟩
    have h_toAffine : DyadicCardToNcover.toAffineLine U_coarse =
        CoordinatePartition.swapLine (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse) := by
      simp [DyadicCardToNcover.toAffineLine, AppendixA.A2DyadicAdapter.dyadicTubeToA2]
      <;> rw [CoordinatePartition.swapLine_invol]
    have h_iso : dist (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse)
        (CoordinatePartition.swapLine ℓ_orig) =
      dist (DyadicCardToNcover.toAffineLine U_coarse) ℓ_orig := by
      have h_swap2 : CoordinatePartition.swapLine (CoordinatePartition.swapLine ℓ_orig) = ℓ_orig := by
        rw [CoordinatePartition.swapLine_invol]
      have h_iso1 : dist (CoordinatePartition.swapLine (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse))
          (CoordinatePartition.swapLine (CoordinatePartition.swapLine ℓ_orig)) =
        dist (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse) (CoordinatePartition.swapLine ℓ_orig) :=
        CoordinatePartition.swapLine_isometry.dist_eq _ _
      rw [h_swap2] at h_iso1
      rw [←h_toAffine] at h_iso1
      exact h_iso1.symm
    have h_final : dist (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse)
        (CoordinatePartition.swapLine ℓ_orig) ≤ 17 * Δ := by
      rw [h_iso]
      exact hdist
    have h_member : AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse ∈
        Metric.cthickening (17 * Δ) (CoordinatePartition.swapLine '' T_oriented) := by
      have h_witness : CoordinatePartition.swapLine ℓ_orig ∈ CoordinatePartition.swapLine '' T_oriented :=
        ⟨ℓ_orig, hℓ_orig, rfl⟩
      have h_edist : edist (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse)
          (CoordinatePartition.swapLine ℓ_orig) ≤ ENNReal.ofReal (17 * Δ) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal h_final
      have h_inf : Metric.infEDist (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse)
          (CoordinatePartition.swapLine '' T_oriented) ≤
          edist (AppendixA.A2DyadicAdapter.dyadicTubeToA2 U_coarse)
            (CoordinatePartition.swapLine ℓ_orig) :=
        Metric.infEDist_le_edist_of_mem h_witness
      exact le_trans h_inf h_edist
    exact h_member

  -- Step 7: Dyadic T_Delta slope/intercept bounds
  have h_slope_T_Delta_dyadic : ∀ U ∈ AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source, |U.slope| ≤ 1 :=
    AppendixA.TDeltaGlobal.T_Delta_global_dyadic_slope_bound h_slope_T_source
  have h_intercept_T_Delta_dyadic : ∀ U ∈ AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source, |U.intercept| ≤ 3 :=
    AppendixA.TDeltaGlobal.T_Delta_global_dyadic_intercept_bound h_intercept_T_source

  -- Step 8: Numerical bounds
  have h_num_u : AssemblyNumericalBounds Δ s u ε := h_uniform_num u hu_t hu_two
  have hRKP_cond_u : 576 * ε < u - s := by
    have h1 : 576 * ε < t - s := h576ε_lt
    have h2 : t ≤ u := hu_t
    linarith
  have hRKP_u : RKPAtExponent s u ε δ₀_RKP := hRKP_uniform u hu_t hu_two
  have hRKP_at_Delta := hRKP_u.2.2 Δ hΔ_pos hΔ_lt_one hΔ_le_RKP

  have hΔ_lt_quarter : Δ < 1 / 4 := by
    have hε4_pos : 0 < ε / 4 := by positivity
    have hε4_lt_one : ε / 4 < 1 := by linarith [hε_lt_one]
    have h1 : Real.rpow Δ 1 < Real.rpow Δ (ε / 4) :=
      Real.rpow_lt_rpow_of_exponent_gt hΔ_pos hΔ_lt_one (by linarith [hε_lt_one])
    have h2 : Real.rpow Δ 1 = Δ := by simp
    have h3 : Δ < Real.rpow Δ (ε / 4) := by
      rw [h2] at h1
      exact h1
    have h4 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small_eps
    linarith
  have hΔ_le_quarter : Δ ≤ 1 / 4 := by linarith
  have h_center_bdd : ∀ Q ∈ a1.Qset, ‖Lagoon.squareCenter Δ Q‖ ≤ 2 :=
    center_norm_le_two_from_ball
      hΔ_pos hΔ_le_quarter hδ_n_eq2 a1 h_points_in_ball'

  have hQset_nonempty : a1.Qset.Nonempty := a1.hQset_sset.1

  -- Derive hNcover_eq from swapped setup
  have hNcover_eq : Metric.externalCoveringNumber Δ.toNNReal T_oriented =
      Metric.externalCoveringNumber Δ.toNNReal T_original := by
    by_cases h_swapped : swapped
    · have h : T_oriented = CoordinatePartition.swapLine '' T_original := h_swapped_true h_swapped
      rw [h]
      simpa [RegularIncidence.Ncover] using NcoverEqualities.ncover_swapLine_eq (δ := Δ) (T := T_original)
    · have h_swapped' : swapped = false := by
        by_cases h : swapped <;> simp [h] at h_swapped ⊢ <;> tauto
      have h : T_oriented = T_original := h_swapped_false h_swapped'
      rw [h]

  -- Derive h_absorb_4 with exponent s + εA
  have h_absorb_4' : Real.rpow 4 (s + εA) ≤ Real.rpow Δ (-ε / 100) := by
    have h1 : s + εA < 2 := by
      rw [hεA_eq]; linarith [hε_lt_one, hs_lt_one]
    have h2 : Real.rpow 4 (s + εA) ≤ (16 : ℝ) := by
      have h3 : s + εA ≤ 2 := by linarith
      have h4 : Real.rpow 4 (s + εA) ≤ Real.rpow 4 (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
      have h5 : Real.rpow 4 (2 : ℝ) = (16 : ℝ) := by norm_num
      rw [h5] at h4; exact h4
    have h6 : (16 : ℝ) ≤ Real.rpow Δ (-ε / 100) := h_num_u.h_absorb_4_dyadic
    exact le_trans h2 h6

  -- Step 9: h_dyadic bound
  have h_dyadic : (AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source).card ≤
      Real.rpow Δ (-(2 * s + 3 * ε)) :=
    HDyadicBound.h_dyadic_bound
      hnm Δ δ δ_n hΔ_eq' hδ_n_eq2 hδ_le_D2 hδ_n_le_4δ'
      hΔ_pos hΔ_lt_one hδ_pos
      s ε εA hs_pos hε_pos hεA_eq
      T_source T_oriented T_original allTubes
      h_slope_T_source h_intercept_T_source
      h_provenance_17Δ
      hNcover_eq
      hT_original_sub
      h_coarse_failure_HDyadic
      h_absorb_4'
      h_absorb_Kpack

  -- Assemble GOutput
  exact
    { a1 := a1
      T_source_dyadic := T_source_dyadic
      T_source := T_source
      T_Delta := T_Delta
      K_pack := a1.K_pack
      A := A
      hT_source_eq := hT_source_eq
      hK_pack_eq := by rfl
      hδ_n_eq := hδ_n_eq2
      hΔ_eq := hΔ_eq'
      hδ_eq := h_eq_n
      hm_pos := hm_pos
      hT_Delta_eq := by rfl
      hT_sub_source := hT_sub_source
      hT_Delta_provenance := hT_Delta_provenance
      h_dyadic := h_dyadic
      h_slope_T_source := h_slope_T_source
      h_intercept_T_source := h_intercept_T_source
      h_slope_T_Delta_dyadic := h_slope_T_Delta_dyadic
      h_intercept_T_Delta_dyadic := h_intercept_T_Delta_dyadic
      h_small_A2 := h_small_A2
      h_num_u := h_num_u
      h_small_eps := h_small_eps
      h_absorb_energy := h_absorb_energy
      hKpack_le_ε := hKpack_le_ε
      hRKP_cond_u := hRKP_cond_u
      δ₀_RKP := δ₀_RKP
      hRKP_u := hRKP_u
      hΔ_le_RKP := hΔ_le_RKP
      h_center_bdd := h_center_bdd
      hQset_nonempty := hQset_nonempty
      hΔ_pos := hΔ_pos
      hΔ_lt_half := hΔ_lt_half
      hδ_n_pos := hδ_n_pos
      hδ_le_D := hδ_le_D
      hε_pos := hε_pos
      hε_lt_one := hε_lt_one
      hs_pos := hs_pos
      hs_lt_one := hs_lt_one
      hsu := hsu
      hu_pos := hu_pos
      h_run_lt_two := h_run_lt_two
      hA_one := hA_one
      hQTTC := hQTTC
      hδ_le_quarter := hδ_le_quarter }

end DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

end
