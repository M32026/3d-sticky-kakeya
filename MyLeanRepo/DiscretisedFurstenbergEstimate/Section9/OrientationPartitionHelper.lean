module

/-
  Orientation-only partition helper for Section 9 Step 5.

  Takes normalized point/tube data at scale δ (Set fibers), extracts
  finite sub-fibers, applies the global slope partition, and outputs
  oriented data with bounded slopes.

  This is orientation ONLY — no config construction, no uniformization.
  The output P_orien is what gets uniformized next.

  Pipeline:
  1. continuous_to_finite_extraction: Set fibers → Finset fibers
  2. global_slope_partition: flat/steep partition + pigeonhole retention

  Whiteprint node: section9 / orientation_partition_helper
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.ContinuousExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.GlobalOrientationPartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.IncidenceOffsetBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.LemmaE_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SlopeUtilities
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Ncover
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral (offset_bound_from_incidence tube_family_bounded_from_incidence)
open CoordinatePartition
open LemmaE
open SlopeUtilities

/-- Orientation-only partition helper.

    Given normalized P, T, Tp at scale δ with S-set properties,
    extracts finite fibers, partitions into flat/steep, retains one
    branch via pigeonhole, and outputs oriented data with bounded slopes.

    Output S-set constant for fibers: (max 1 (Kpack * C_T)) * 2 * Kpack.
    Output point S-set constant: 2 * C_P.
-/
theorem orientation_partition_helper
    (δ s t C_T C_P : ℝ)
    (hs_pos : 0 < s)
    (hCT_pos : 0 < C_T)
    (hCP_pos : 0 < C_P)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (P : Set EuclideanPlane)
    (hP_bdd : P ⊆ Metric.closedBall 0 1)
    (hP_sset : IsDeltaSSet δ t C_P P)
    (hP_interior : P ⊆ {p : EuclideanPlane | p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)})
    (T : Set AffineLine)
    (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine)
    (hTp_sub : ∀ p hp, Tp p hp ⊆ T)
    (hTp_sset : ∀ p hp, IsDeltaSSet δ s C_T (Tp p hp))
    (hTp_near : ∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1)
    (ρ_slope : ℝ)
    (hρ_slope_nonneg : 0 ≤ ρ_slope)
    (hδ_slope : δ ^ ρ_slope ≤ 1 / 2) :
    ∃ (swapped : Bool)
      (P_orien : Set EuclideanPlane)
      (T_orien : Set AffineLine)
      (F_orien : ∀ (p : EuclideanPlane), p ∈ P_orien → Finset AffineLine)
      (c_slope : ℝ),
      0 < c_slope ∧
      c_slope = 1 / 2 ∧
      c_slope ≥ δ ^ ρ_slope ∧
      (Ncover δ P_orien : ENNReal) ≥ ENNReal.ofReal c_slope * (Ncover δ P : ENNReal) ∧
      IsDeltaSSet δ t (2 * C_P) P_orien ∧
      P_orien ⊆ {p : EuclideanPlane | p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)} ∧
      (swapped = false → P_orien ⊆ P ∧ T_orien = T) ∧
      (swapped = true →
        P_orien ⊆ swapCoords '' P ∧ T_orien = swapLine '' T) ∧
      (Ncover δ T_orien : ENNReal) = (Ncover δ T : ENNReal) ∧
      (∀ p hp, (F_orien p hp : Set AffineLine) ⊆ T_orien) ∧
      (∀ p hp, IsDeltaSSet δ s
        ((max 1 ((MainAppendix.affineLine_packing_constant : ℝ) * C_T)) * 2 *
          (MainAppendix.affineLine_packing_constant : ℝ))
        (F_orien p hp : Set AffineLine)) ∧
      (∀ p hp, ∀ ℓ ∈ F_orien p hp,
        (LemmaE.getDirV ℓ) 0 ≠ 0) ∧
      (∀ p hp, ∀ ℓ ∈ F_orien p hp,
        |(affineLineSlopeIntercept ℓ).1| ≤ 1) ∧
      (∀ p hp, ∀ ℓ ∈ F_orien p hp,
        p ∈ Metric.cthickening δ ℓ.1) := by
  let Kpack : ℝ := (MainAppendix.affineLine_packing_constant : ℝ)
  have hKpack_pos : 0 < Kpack := by
    have h : 0 < MainAppendix.affineLine_packing_constant :=
      MainAppendix.affineLine_packing_constant_pos
    have h' : (0 : ℝ) < (MainAppendix.affineLine_packing_constant : ℝ) := by
      exact_mod_cast h
    simpa [Kpack] using h'

  -- Derive offset bound from incidence (IncidenceOffsetBound)
  have hTp_offset : ∀ p hp, ∀ ℓ ∈ Tp p hp, ℓ.offset ∈ Metric.closedBall 0 2 := by
    intro p hp ℓ hℓ
    have hp_ball : p ∈ Metric.closedBall 0 1 := hP_bdd hp
    exact offset_bound_from_incidence hδ_pos hδ_le_one hp_ball (hTp_near p hp ℓ hℓ)

  -- Derive fibrewise boundedness from incidence
  have hTp_bdd : ∀ p hp, Bornology.IsBounded (Tp p hp) := by
    intro p hp
    by_cases hne : (Tp p hp).Nonempty
    · exact tube_family_bounded_from_incidence hδ_pos
        (by simpa [Metric.mem_closedBall] using hP_bdd hp) hne
        (fun ℓ hℓ => hTp_near p hp ℓ hℓ)
    · have h_empty : Tp p hp = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hne
      rw [h_empty]
      exact Bornology.isBounded_empty

  -- Step 1: Extract finite fibers
  rcases ContinuousExtraction.continuous_to_finite_extraction
      Tp hTp_sset hTp_bdd hTp_near hTp_offset
    with ⟨Fp, hF_sub, hF_nonempty, hF_sep, hF_sset, hF_card, hF_near, hF_offset⟩

  -- C_T_in * Kpack = max 1 (Kpack * C_T), matching extraction output
  let C_T_in : ℝ := max 1 (Kpack * C_T) / Kpack
  have hC_T_in_pos : 0 < C_T_in := by
    have h1 : 0 < max 1 (Kpack * C_T) := by positivity
    exact div_pos h1 hKpack_pos
  have hC_T_in_Kpack : C_T_in * Kpack = max 1 (Kpack * C_T) := by
    dsimp only [C_T_in]
    field_simp [hKpack_pos.ne'] <;> ring

  have hF_sset' : ∀ p hp, IsDeltaSSet δ s (C_T_in * Kpack) (Fp p hp : Set AffineLine) := by
    intro p hp
    have h1 : IsDeltaSSet δ s (max 1 (Kpack * C_T)) (Fp p hp : Set AffineLine) :=
      hF_sset p hp
    rw [hC_T_in_Kpack] at *
    exact h1

  -- Fp fibers are subsets of Tp, which are subsets of T
  have hF_sub_T : ∀ p hp, (Fp p hp : Set AffineLine) ⊆ T := by
    intro p hp
    exact Set.Subset.trans (hF_sub p hp) (hTp_sub p hp)

  -- Step 2: Global slope partition
  rcases DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.global_slope_partition
      δ s C_T_in hs_pos hC_T_in_pos hδ_pos P T Fp
      hF_sub_T hF_sset' hF_sep hF_near
      ρ_slope hρ_slope_nonneg hδ_slope
    with ⟨swapped, P', P_oriented, T_oriented, F_oriented, c_slope,
      hc_slope_pos, h_c_slope_eq, hP'_sub, h_swapped_false, h_swapped_true,
      h_ncover_T, hF_orien_sub, hF_orien_sset, hF_orien_v0, hF_orien_slope,
      hF_orien_near, h_c_slope_ge, h_ncover_P⟩

  -- Half covering bound: Ncover(P) ≤ 2 * Ncover(P')
  -- Since c_slope = 1/2 and Ncover(P_oriented) ≥ c_slope * Ncover(P),
  -- and Ncover(P_oriented) = Ncover(P') (isometry or equality),
  -- we get Ncover(P) ≤ 2 * Ncover(P').
  have hNcover_P'_eq : Ncover δ P_oriented = Ncover δ P' := by
    cases swapped with
    | false =>
      have h1 := h_swapped_false rfl
      rw [h1.1]
    | true =>
      have h1 := h_swapped_true rfl
      rw [h1.1]
      simpa [Ncover] using externalCoveringNumber_image_of_involutive_isometry
        swapCoords_isometry swapCoords_invol δ.toNNReal P'
  have h_half_P' : Ncover δ P ≤ 2 * Ncover δ P' := by
    have h1 : Ncover δ P_oriented ≥ ENNReal.ofReal (1 / 2 : ℝ) * Ncover δ P := by
      rw [h_c_slope_eq] at h_ncover_P <;> exact h_ncover_P
    rw [hNcover_P'_eq] at h1
    have h_mul2 : (2 : ENNReal) * (ENNReal.ofReal (1 / 2 : ℝ) * Ncover δ P) = Ncover δ P := by
      have h3 : (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
        have h4 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
        rw [h4]
        rw [← ENNReal.ofReal_mul (by norm_num)]
        <;> norm_num
      calc
        (2 : ENNReal) * (ENNReal.ofReal (1 / 2 : ℝ) * Ncover δ P)
          = ((2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ)) * Ncover δ P := by ring
        _ = (1 : ENNReal) * Ncover δ P := by rw [h3]
        _ = Ncover δ P := by rw [one_mul]
    have h5 : (2 : ENNReal) * Ncover δ P' ≥ Ncover δ P := by
      calc
        (2 : ENNReal) * Ncover δ P'
          ≥ (2 : ENNReal) * (ENNReal.ofReal (1 / 2 : ℝ) * Ncover δ P) := by gcongr
        _ = Ncover δ P := h_mul2
    exact h5

  -- Rewrite S-set constant to match statement
  have hF_orien_sset' : ∀ p hp, IsDeltaSSet δ s
      (max 1 (Kpack * C_T) * 2 * Kpack) (F_oriented p hp : Set AffineLine) := by
    intro p hp
    have h1 : IsDeltaSSet δ s (C_T_in * Kpack * 2 * Kpack) (F_oriented p hp : Set AffineLine) :=
      hF_orien_sset p hp
    have h_eq : C_T_in * Kpack * 2 * Kpack = max 1 (Kpack * C_T) * 2 * Kpack := by
      rw [hC_T_in_Kpack] <;> ring
    rw [h_eq] at h1
    exact h1

  -- Point S-set for P' with enlarged constant 2 * C_P
  have hP'_sset : IsDeltaSSet δ t (2 * C_P) P' :=
    IsDeltaSSet.half_subset hP_sset hP'_sub h_half_P'

  -- Transport to P_oriented
  have hP_orien_sset : IsDeltaSSet δ t (2 * C_P) P_oriented := by
    cases swapped with
    | false =>
      have h1 := h_swapped_false rfl
      have h2 : P_oriented = P' := h1.1
      rw [h2]
      exact hP'_sset
    | true =>
      have h1 := h_swapped_true rfl
      have h2 : P_oriented = swapCoords '' P' := h1.1
      rw [h2]
      exact hP'_sset.surjective_isometry_image swapCoords_isometry
        (Function.Involutive.surjective swapCoords_invol)

  -- Interior chart preservation for P_oriented
  have hP'_interior : P' ⊆ {p : EuclideanPlane | p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)} :=
    Set.Subset.trans hP'_sub hP_interior
  have h_swap_preserves_interior :
      ∀ (p : EuclideanPlane), (p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)) →
      ((swapCoords p) 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ (swapCoords p) 1 ∈ Set.Icc (1 / 4) (3 / 4)) := by
    intro p hp
    have h1 : (swapCoords p) 0 = p 1 := by
      simp [swapCoords] <;> aesop
    have h2 : (swapCoords p) 1 = p 0 := by
      simp [swapCoords] <;> aesop
    rw [h1, h2]
    exact ⟨hp.2, hp.1⟩
  have hP_orien_interior : P_oriented ⊆ {p : EuclideanPlane | p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)} := by
    cases swapped with
    | false =>
      have h1 := h_swapped_false rfl
      have h2 : P_oriented = P' := h1.1
      rw [h2]
      exact hP'_interior
    | true =>
      have h1 := h_swapped_true rfl
      have h2 : P_oriented = swapCoords '' P' := h1.1
      rw [h2]
      intro q hq
      rcases hq with ⟨p, hp, rfl⟩
      have h3 : p ∈ P' := hp
      have h4 : p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4) := hP'_interior h3
      exact h_swap_preserves_interior p h4

  refine' ⟨swapped, P_oriented, T_oriented, F_oriented, c_slope, _⟩
  exact ⟨
    hc_slope_pos,
    h_c_slope_eq,
    h_c_slope_ge,
    h_ncover_P,
    hP_orien_sset,
    hP_orien_interior,
    (by
      intro h
      have h1 := h_swapped_false h
      have h2 : P_oriented = P' := h1.1
      rw [h2]
      exact ⟨hP'_sub, h1.2⟩),
    (by
      intro h
      have h1 := h_swapped_true h
      have h2 : P_oriented = swapCoords '' P' := h1.1
      rw [h2]
      exact ⟨Set.image_mono hP'_sub, h1.2⟩),
    h_ncover_T,
    hF_orien_sub,
    hF_orien_sset',
    hF_orien_v0,
    hF_orien_slope,
    hF_orien_near
  ⟩

end DirecretisedFurstenbergEstimate.Section9

end
