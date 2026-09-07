module

/-
  A2 Typed QTTC Adapter v3: bridge typed dyadic QTTC to A2 AffineLine interface.

  Main theorem: `qttc_typed_parentCell`.

  Split into submodules:
  - Basic: helper lemmas
  - Transfer: `affine_sset_transfer`

  Whiteprint node: appendix_a_alternative / a2_typed_qttc_adapter
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_TypedQTTC_Adapter.Transfer

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

set_option maxHeartbeats 1000000

/-- Main adapter theorem v3.
    Takes exact dyadic levels n, m. Uses original preimages. -/
theorem qttc_typed_parentCell (s : ℝ) (hs : 0 < s) (hs_lt_two : s < 2) :
    ∃ (A : ℝ), 1 ≤ A ∧
      ∀ {n m : ℕ} {δ Δ C₁ : ℝ} {M : ℕ}
        {P : Finset Plane} {T : Plane → Finset AffineLine},
        (hδ_eq : δ = dyadicDelta n) →
        (hΔ_eq : Δ = dyadicDelta m) →
        (hnm : m ≤ n) → (hm_pos : 1 ≤ m) →
        1 ≤ C₁ → P.Nonempty → 0 < M →
        (∀ p ∈ P, M / 2 < (T p).card ∧ (T p).card ≤ M) →
        (∀ p ∈ P, _root_.BallGrowth δ s C₁ (T p)) →
        (∀ p ∈ P, SeparatedAt (δ / 2) ((T p) : Set AffineLine)) →
        (∀ p ∈ P, ∀ ℓ ∈ T p,
          (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3) →
        (R : ℝ) →
        (hR : R ≤ Real.sqrt 2) →
        (∀ p ∈ P, |p 1| ≤ R) →
        (hδ_le_quarter_Delta : δ ≤ Δ / 4) →
        (∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) →
        ∃ (P' : Finset Plane) (T' : Plane → Finset AffineLine)
          (C' : Finset AffineLine) (K C₂ : ℝ) (H : ℕ),
          1 ≤ K ∧ K ≤ A * Real.rpow (Real.log (2 / Δ)) A ∧
          1 ≤ C₂ ∧ 0 < H ∧
          P' ⊆ P ∧
          (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
          (∀ p ∈ P', T' p ⊆ T p) ∧
          (∀ p ∈ P', (M : ℝ) ≤ K * ((T' p).card : ℝ)) ∧
          _root_.IsFiniteDeltaSSet Δ s C₂ C' ∧
          IsDeltaSSet Δ s (max 1 (QTTC_Assembly.C_PACK * C₂)) (C' : Set AffineLine) ∧
          C₂ ≤ A * Real.rpow K A * C₁ ∧
          -- Coarse tube parameter bounds
          (∀ c ∈ C', |tubeSlope c| ≤ 1) ∧
          (∀ c ∈ C', (LemmaE.getDirV c) 1 ≠ 0) ∧
          (∀ c ∈ C', |tubeIntercept c| ≤ 3) ∧
          -- Near-point incidence for h_strip derivation (algebraic bound)
          (∀ c ∈ C', ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ) ∧
          -- Exact-parent provenance via composite:
          -- ell → snapTube n ell → sp hnm → dyadicTubeToA2 = c
          (∀ c ∈ C', ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
            (hell : ell ∈ T' p) (U : DyadicTube m),
            sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U) ∧
          -- H2 lower bound
          (∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C',
            (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T' p c).card) ∧
          -- PointFiber upper bound (geometric constant GEOM_CONST to be absorbed)
          (∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C',
            (pointFiber Δ hΔ_pos T' p c).card ≤
              C₁ * GEOM_CONST s * (T p).card * Δ^s) ∧
          (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'.card : ℝ) ∧
          (H : ℝ) * (C'.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ) := by
  rcases qttc_for_dyadicTubes s hs hs_lt_two with ⟨A_typed, hA_one, hQTTC_typed⟩

  let B_nat : ℕ := max 1 MainAppendix.affineLine_packing_constant_720
  let B : ℝ := (B_nat : ℝ)
  have hB_nat_one : 1 ≤ B_nat := by
    exact Nat.le_max_left 1 _
  have hB_one : 1 ≤ B := by
    have h : (1 : ℝ) ≤ (B_nat : ℝ) := by exact_mod_cast hB_nat_one
    simpa [B] using h
  let D_nat : ℕ := 2 * B_nat
  let D : ℝ := (D_nat : ℝ)
  have hD_nat_one : 1 ≤ D_nat := by
    dsimp only [D_nat]
    omega
  have hD_one : 1 ≤ D := by
    have h : (1 : ℝ) ≤ (D_nat : ℝ) := by exact_mod_cast hD_nat_one
    simpa [D] using h
  have hB_eq_max : B = max 1 (MainAppendix.affineLine_packing_constant_720 : ℝ) := by
    dsimp only [B, B_nat]
    norm_cast
    <;> simp [max_comm]
    <;> ring_nf
  let A : ℝ := A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s
  have hA_one' : 1 ≤ A := by
    have h2 : 0 ≤ s := by linarith
    have h3 : 1 ≤ (88 : ℝ)^s := by
      have h5 : (1 : ℝ) ≤ (88 : ℝ) := by norm_num
      have h6 : (1 : ℝ)^s ≤ (88 : ℝ)^s := Real.rpow_le_rpow (by linarith) h5 h2
      simpa using h6
    have h4 : 1 ≤ (40 : ℝ)^s := by
      have h5 : (1 : ℝ) ≤ (40 : ℝ) := by norm_num
      have h6 : (1 : ℝ)^s ≤ (40 : ℝ)^s := Real.rpow_le_rpow (by linarith) h5 h2
      simpa using h6
    have h5 : 1 ≤ A_typed := hA_one
    have h6 : 1 ≤ (1936 : ℝ) := by norm_num
    have h7 : 1 ≤ D := hD_one
    calc 1
      = 1 * 1 * 1 * 1 * 1 * 1 := by ring
    _ ≤ A_typed * D * 1936 * (88 : ℝ)^s * (40 : ℝ)^s := by
      gcongr <;> linarith
    _ = A := by rfl

  refine' ⟨A, hA_one', _⟩
  intro n m δ Δ C₁ M P T hδ_eq hΔ_eq hnm hm_pos hC1 hP_nonempty hM_pos h_size h_sset h_sep_family h_slope R hR h_ball hδ_le_quarter_Delta h_inc

  let δ' := dyadicDelta n
  let Δ' := dyadicDelta m
  have hΔ_pos' : 0 < Δ := by
    rw [hΔ_eq] <;> exact dyadicDelta_pos m

  -- Snap
  let T_dyadic (p : Plane) : Finset (DyadicTube n) := (T p).image (snapTube n)
  let C₁' : ℝ := C₁ * (40 : ℝ)^s * B
  have hC1'_one : 1 ≤ C₁' := by
    have h2 : 0 ≤ s := by linarith
    have h3 : 1 ≤ (40 : ℝ)^s := by
      have h4 : (1 : ℝ) ≤ (40 : ℝ) := by norm_num
      have h5 : (1 : ℝ)^s ≤ (40 : ℝ)^s := Real.rpow_le_rpow (by linarith) h4 h2
      simpa using h5
    have h4 : 1 ≤ C₁ := hC1
    have h5 : 1 ≤ B := hB_one
    have h61 : 1 ≤ C₁ := h4
    have h62 : 1 ≤ (40 : ℝ)^s := by
      have h : (1 : ℝ) ≤ (40 : ℝ) := by norm_num
      have h' : (1 : ℝ)^s ≤ (40 : ℝ)^s := Real.rpow_le_rpow (by linarith) h h2
      simpa using h'
    have h6 : 1 ≤ C₁ * (40 : ℝ)^s * B := by
      calc 1
        = 1 * 1 * 1 := by ring
      _ ≤ C₁ * ((40 : ℝ)^s) * B := by gcongr <;> linarith
    have h7 : C₁ * (40 : ℝ)^s * B = C₁' := by rfl
    rw [←h7]
    exact h6

  have h_bg_dyadic : ∀ p ∈ P, BallGrowth δ' s C₁' (T_dyadic p) := by
    intro p hp
    have h_sep : SeparatedAt (δ / 2) ((T p) : Set AffineLine) := h_sep_family p hp
    have h_bg_raw : BallGrowth δ s (C₁ * (40 : ℝ)^s * max 1 (MainAppendix.affineLine_packing_constant_720 : ℝ)) ((T p).image (snapTube n)) :=
      ballGrowth_transfer_snap hδ_eq (T p) (h_sset p hp) h_sep
        (fun ℓ hℓ => (h_slope p hp ℓ hℓ).1)
        (fun ℓ hℓ => (h_slope p hp ℓ hℓ).2.1)
        (fun ℓ hℓ => (h_slope p hp ℓ hℓ).2.2)
    have hB_eq : (max 1 (MainAppendix.affineLine_packing_constant_720 : ℝ)) = B := by
      exact hB_eq_max.symm
    have h_bg_raw2 : BallGrowth δ s (C₁ * (40 : ℝ)^s * B) ((T p).image (snapTube n)) := by
      rw [hB_eq] at h_bg_raw
      exact h_bg_raw
    have hδ_eq' : δ = δ' := by
      simp [δ', hδ_eq] <;> rfl
    have hC_eq : C₁ * (40 : ℝ)^s * B = C₁' := by rfl
    have hT_eq : (T p).image (snapTube n) = T_dyadic p := by rfl
    rw [hδ_eq', hC_eq, hT_eq] at h_bg_raw2
    exact h_bg_raw2

  -- Snap fiber lower bound: |T p| ≤ B_nat * |T_dyadic p|
  have h_snap_lower : ∀ p ∈ P, (T p).card ≤ B_nat * (T_dyadic p).card := by
    intro p hp
    have h_sep : SeparatedAt (δ / 2) ((T p) : Set AffineLine) := h_sep_family p hp
    have h_v : ∀ ℓ ∈ T p, (LemmaE.getDirV ℓ) 1 ≠ 0 :=
      fun ℓ hℓ => (h_slope p hp ℓ hℓ).1
    have h_a : ∀ ℓ ∈ T p, |tubeSlope ℓ| ≤ 1 :=
      fun ℓ hℓ => (h_slope p hp ℓ hℓ).2.1
    have h_b : ∀ ℓ ∈ T p, |tubeIntercept ℓ| ≤ 3 :=
      fun ℓ hℓ => (h_slope p hp ℓ hℓ).2.2
    have h_fiber : ∀ U ∈ T_dyadic p,
        ((T p).filter (fun ℓ => snapTube n ℓ = U)).card ≤ B_nat := by
      intro U hU
      have h : ((T p).filter (fun ℓ => snapTube n ℓ = U)).card ≤
          MainAppendix.affineLine_packing_constant_720 :=
        snap_fiber_bound hδ_eq (T p) U h_sep h_v h_a h_b
      have h' : MainAppendix.affineLine_packing_constant_720 ≤ B_nat := by
        exact Nat.le_max_right 1 _
      exact le_trans h h'
    exact Finset.card_le_mul_card_image (T p) B_nat h_fiber

  have h_slope_dyadic : ∀ U ∈ globalCoarseG hnm P T_dyadic, |U.slope| ≤ 1 := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨V, hV_in_biUnion, rfl⟩
    rcases Finset.mem_biUnion.mp hV_in_biUnion with ⟨p, hp, hV_in_Tdyadic⟩
    rcases Finset.mem_image.mp hV_in_Tdyadic with ⟨ℓ, hℓ, rfl⟩
    have h_orig_slope : |tubeSlope ℓ| ≤ 1 := (h_slope p hp ℓ hℓ).2.1
    -- Fine snapped tube slope bounded by 1
    have hV_slope : |(snapTube n ℓ).slope| ≤ 1 := by
      have h_eq : (snapTube n ℓ).slope = (⌊tubeSlope ℓ / δ'⌋ : ℝ) * δ' := by
        simp [snapTube, DyadicTube.slope, δ'] <;> rfl
      rw [h_eq]
      exact floor_dyadic_bound_one (tubeSlope ℓ) h_orig_slope
    -- Coarse parent slope bounded by 1
    have h_eq2 : (sp hnm (snapTube n ℓ)).slope =
        (⌊(snapTube n ℓ).slope / Δ'⌋ : ℝ) * Δ' := by
      let T := snapTube n ℓ
      let k : ℕ := refinementFactor n m
      have h1 : (sp hnm T).a = T.a / (k : ℤ) := by
        simp [sp, sourceParent, coarseTubeToM] <;> rfl
      have h_floor : ⌊T.slope / Δ'⌋ = (sp hnm T).a := by
        have h : ⌊T.slope / dyadicDelta m⌋ = T.a / (k : ℤ) :=
          coarse_slope_index_floor hnm T
        have hD : Δ' = dyadicDelta m := by rfl
        rw [hD] at *
        rw [h, h1]
      have h_slope_def : (sp hnm T).slope = ((sp hnm T).a : ℝ) * dyadicDelta m := by rfl
      have hD : Δ' = dyadicDelta m := by rfl
      rw [h_slope_def, h_floor, hD] <;> rfl
    rw [h_eq2]
    exact floor_dyadic_bound_one (snapTube n ℓ).slope hV_slope
  have h_intercept_dyadic : ∀ U ∈ globalCoarseG hnm P T_dyadic, |U.intercept| ≤ 3 := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨V, hV_in_biUnion, rfl⟩
    rcases Finset.mem_biUnion.mp hV_in_biUnion with ⟨p, hp, hV_in_Tdyadic⟩
    rcases Finset.mem_image.mp hV_in_Tdyadic with ⟨ℓ, hℓ, rfl⟩
    have h_orig_int : |tubeIntercept ℓ| ≤ 3 := (h_slope p hp ℓ hℓ).2.2
    -- Fine snapped tube intercept bounded by 3
    have hV_int : |(snapTube n ℓ).intercept| ≤ 3 := by
      have h_eq : (snapTube n ℓ).intercept = (⌊tubeIntercept ℓ / δ'⌋ : ℝ) * δ' := by
        simp [snapTube, DyadicTube.intercept, δ'] <;> rfl
      rw [h_eq]
      exact floor_dyadic_bound_three (tubeIntercept ℓ) h_orig_int
    -- Coarse parent intercept bounded by 3
    have h_eq2 : (sp hnm (snapTube n ℓ)).intercept =
        (⌊(snapTube n ℓ).intercept / Δ'⌋ : ℝ) * Δ' := by
      let T := snapTube n ℓ
      let k : ℕ := refinementFactor n m
      have h1 : (sp hnm T).b = T.b / (k : ℤ) := by
        simp [sp, sourceParent, coarseTubeToM] <;> rfl
      have h_floor : ⌊T.intercept / Δ'⌋ = (sp hnm T).b := by
        have h : ⌊T.intercept / dyadicDelta m⌋ = T.b / (k : ℤ) :=
          coarse_intercept_index_floor hnm T
        have hD : Δ' = dyadicDelta m := by rfl
        rw [hD] at *
        rw [h, h1]
      have h_int_def : (sp hnm T).intercept = ((sp hnm T).b : ℝ) * dyadicDelta m := by rfl
      have hD : Δ' = dyadicDelta m := by rfl
      rw [h_int_def, h_floor, hD] <;> rfl
    rw [h_eq2]
    exact floor_dyadic_bound_three (snapTube n ℓ).intercept hV_int

  -- M-adjustment: snap can lose up to B_nat x, QTTC needs M/2 < card
  -- Use M_QTTC = ceil(M / D_nat), where D_nat = 2 * B_nat, thin snapped family
  let M_QTTC : ℕ := (M + D_nat - 1) / D_nat
  have hD_nat_pos : 0 < D_nat := by
    dsimp only [D_nat]
    have h1 : 0 < B_nat := by linarith [hB_nat_one]
    exact mul_pos two_pos h1
  have hM_QTTC_pos : 0 < M_QTTC := by
    have h1 : 0 < M := hM_pos
    have h2 : 0 < D_nat := hD_nat_pos
    dsimp only [M_QTTC]
    have h3 : D_nat ≤ M + D_nat - 1 := by omega
    have h4 : 1 ≤ (M + D_nat - 1) / D_nat := by
      apply Nat.one_le_div_iff (by omega) |>.mpr
      exact h3
    exact h4
  have hM_le_D_nat : M ≤ D_nat * M_QTTC := by
    have hpos : 0 < D_nat := hD_nat_pos
    dsimp only [M_QTTC]
    exact ceil_div_mul_bound hpos
  have hM_le_D : (M : ℝ) ≤ D * (M_QTTC : ℝ) := by
    have h' : (M : ℝ) ≤ (D_nat : ℝ) * (M_QTTC : ℝ) := by exact_mod_cast hM_le_D_nat
    have hD_eq : D = (D_nat : ℝ) := by rfl
    rw [hD_eq]
    exact h'
  have hM_QTTC_le : ∀ p ∈ P, M_QTTC ≤ (T_dyadic p).card := by
    intro p hp
    have h1 : M / 2 < (T p).card := (h_size p hp).1
    have h2 : (T p).card ≤ B_nat * (T_dyadic p).card := h_snap_lower p hp
    have h1' : M < 2 * (T p).card := by omega
    have hD_eq : D_nat = 2 * B_nat := by simp [D_nat]
    have h2' : 2 * (T p).card ≤ D_nat * (T_dyadic p).card := by
      rw [hD_eq]
      have h : 2 * (T p).card ≤ 2 * (B_nat * (T_dyadic p).card) := by gcongr
      linarith
    have h3 : M < D_nat * (T_dyadic p).card := lt_of_lt_of_le h1' h2'
    dsimp only [M_QTTC]
    exact ceil_div_le hD_nat_pos h3
  -- Thin T_dyadic to T_QTTC with exactly M_QTTC elements
  let T_QTTC (p : Plane) : Finset (DyadicTube n) :=
    if hp : p ∈ P then
      Classical.choose (Finset.exists_subset_card_eq (hM_QTTC_le p hp))
    else ∅
  have hT_QTTC_sub : ∀ p ∈ P, T_QTTC p ⊆ T_dyadic p := by
    intro p hp
    have h := Classical.choose_spec (Finset.exists_subset_card_eq (hM_QTTC_le p hp))
    simpa [T_QTTC, hp] using h.1
  have hT_QTTC_card : ∀ p ∈ P, (T_QTTC p).card = M_QTTC := by
    intro p hp
    have h := Classical.choose_spec (Finset.exists_subset_card_eq (hM_QTTC_le p hp))
    simpa [T_QTTC, hp] using h.2
  -- Density-corrected BallGrowth for thinned family: C₁_QTTC = C₁' * D
  let C₁_QTTC : ℝ := C₁' * D
  have hC1_QTTC_one : 1 ≤ C₁_QTTC := by
    have h1 : 1 ≤ C₁' := hC1'_one
    have h2 : 1 ≤ D := hD_one
    have h3 : 1 ≤ C₁' * D := by
      calc 1 = 1 * 1 := by ring
      _ ≤ C₁' * D := by gcongr <;> linarith
    simpa [C₁_QTTC] using h3
  have h_bg_QTTC : ∀ p ∈ P, BallGrowth δ' s C₁_QTTC (T_QTTC p) := by
    intro p hp
    have h_bg : BallGrowth δ' s C₁' (T_dyadic p) := h_bg_dyadic p hp
    have h_card_dyadic_le : (T_dyadic p).card ≤ M := by
      have h1 : (T_dyadic p).card ≤ (T p).card := Finset.card_image_le
      have h2 : (T p).card ≤ M := (h_size p hp).2
      exact Nat.le_trans h1 h2
    have h_ratio : (T_dyadic p).card ≤ D_nat * (T_QTTC p).card := by
      have h3 : M ≤ D_nat * M_QTTC := hM_le_D_nat
      have h4 : (T_QTTC p).card = M_QTTC := hT_QTTC_card p hp
      rw [h4]
      exact Nat.le_trans h_card_dyadic_le h3
    have h_nonempty : (T_QTTC p).Nonempty := by
      have h5 : (T_QTTC p).card = M_QTTC := hT_QTTC_card p hp
      have h6 : 0 < (T_QTTC p).card := by
        rw [h5]
        exact hM_QTTC_pos
      exact Finset.card_pos.mp h6
    refine' {
      nonempty := h_nonempty,
      δ_pos := h_bg.δ_pos,
      C_one := hC1_QTTC_one,
      s_nonneg := h_bg.s_nonneg,
      growth := fun x r hr => by
        have h1 : ((T_QTTC p).filter fun y => dist y x ≤ r) ⊆
            (T_dyadic p).filter fun y => dist y x ≤ r := by
          apply Finset.filter_subset_filter
          exact hT_QTTC_sub p hp
        have h2 : ((T_QTTC p).filter fun y => dist y x ≤ r).card ≤
            ((T_dyadic p).filter fun y => dist y x ≤ r).card :=
          Finset.card_le_card h1
        have h2' : (((T_QTTC p).filter fun y => dist y x ≤ r).card : ℝ) ≤
            (((T_dyadic p).filter fun y => dist y x ≤ r).card : ℝ) := by
          exact_mod_cast h2
        have h3 : (((T_dyadic p).filter fun y => dist y x ≤ r).card : ℝ) ≤
            C₁' * r ^ s * (T_dyadic p).card := h_bg.growth x r hr
        have h4 : ((T_dyadic p).card : ℝ) ≤ D * ((T_QTTC p).card : ℝ) := by
          have h5 : ((T_dyadic p).card : ℝ) ≤ (D_nat : ℝ) * ((T_QTTC p).card : ℝ) := by
            exact_mod_cast h_ratio
          have h6 : D = (D_nat : ℝ) := by rfl
          rw [h6]
          exact h5
        have h_pos1 : 0 ≤ C₁' * r ^ s := by
          have hC1'_pos : 0 < C₁' := by linarith [hC1'_one]
          have hr_pos : 0 < r := by linarith [h_bg.δ_pos, hr]
          have hrs_pos : 0 ≤ r ^ s := by positivity
          positivity
        calc (((T_QTTC p).filter fun y => dist y x ≤ r).card : ℝ)
          ≤ (((T_dyadic p).filter fun y => dist y x ≤ r).card : ℝ) := h2'
        _ ≤ C₁' * r ^ s * (T_dyadic p).card := h3
        _ ≤ C₁' * r ^ s * (D * (T_QTTC p).card) := by
          exact mul_le_mul_of_nonneg_left h4 h_pos1
        _ = C₁_QTTC * r ^ s * (T_QTTC p).card := by
          dsimp only [C₁_QTTC] <;> ring
    }
  have h_size_QTTC : ∀ p ∈ P, M_QTTC / 2 < (T_QTTC p).card ∧ (T_QTTC p).card ≤ M_QTTC := by
    intro p hp
    have h_card : (T_QTTC p).card = M_QTTC := hT_QTTC_card p hp
    rw [h_card]
    have h_pos : 0 < M_QTTC := hM_QTTC_pos
    omega
  have h_biUnion_sub : P.biUnion T_QTTC ⊆ P.biUnion T_dyadic := by
    apply Finset.biUnion_mono
    intro p hp
    exact hT_QTTC_sub p hp
  have h_global_sub : globalCoarseG hnm P T_QTTC ⊆ globalCoarseG hnm P T_dyadic := by
    dsimp only [globalCoarseG]
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, h_biUnion_sub hy, rfl⟩
  have h_slope_QTTC : ∀ U ∈ globalCoarseG hnm P T_QTTC, |U.slope| ≤ 1 := by
    intro U hU
    exact h_slope_dyadic U (h_global_sub hU)
  have h_intercept_QTTC : ∀ U ∈ globalCoarseG hnm P T_QTTC, |U.intercept| ≤ 3 := by
    intro U hU
    exact h_intercept_dyadic U (h_global_sub hU)

  have h_main := hQTTC_typed hnm hm_pos
    (C₁ := C₁_QTTC) (M := M_QTTC) (P := P) (tubeFamily := T_QTTC)
    hC1_QTTC_one hP_nonempty hM_QTTC_pos
    h_size_QTTC
    h_bg_QTTC h_slope_QTTC
    h_intercept_QTTC

  rcases h_main with ⟨P', T'_dyadic, C'_dyadic, K_typed, C₂_typed, H,
    hK_one, hK_bound, hC2_one, hH_pos, hP'_sub, hP_card, hT'_sub, hT'_size,
    hC'_sset_typed, hC2_bound, h_pointFiberG, h_avg_lower, h_avg_upper, hC'_sub⟩

  -- Thin
  have hC_slope : ∀ U ∈ C'_dyadic, |U.slope| ≤ 1 := by
    intro U hU
    exact h_slope_dyadic U (h_global_sub (hC'_sub hU))
  have hC_intercept : ∀ U ∈ C'_dyadic, |U.intercept| ≤ 3 := by
    intro U hU
    exact h_intercept_dyadic U (h_global_sub (hC'_sub hU))

  rcases thin_coarse_tubes_affine_separated hm_pos C'_dyadic hC_slope hC_intercept
    with ⟨C_thin, h_thin_sub, h_card_thin, h_sep_affine⟩

  have h_sep_delta : SeparatedAt Δ (C_thin.image dyadicTubeToA2 : Set AffineLine) := by
    have h_eq : Δ = Δ' := by simp [hΔ_eq, Δ'] <;> rfl
    rw [h_eq]
    exact h_sep_affine

  let C'_affine : Finset AffineLine := C_thin.image dyadicTubeToA2

  -- ========================================================================
  -- Retain ORIGINAL preimages of selected dyadic fine tubes
  -- ========================================================================
  let T'_affine (p : Plane) : Finset AffineLine :=
    (T p).filter (fun ℓ => snapTube n ℓ ∈ T'_dyadic p)

  have hT'_sub' : ∀ p ∈ P', T'_affine p ⊆ T p := by
    intro p hp; exact Finset.filter_subset _ _

  have hT'_nonempty_card : ∀ p ∈ P', (T'_dyadic p).card ≤ (T'_affine p).card := by
    intro p hp
    -- Each selected dyadic tube has at least one preimage in T p
    have h1 : ∀ V ∈ T'_dyadic p, ∃ ℓ ∈ T p, snapTube n ℓ = V := by
      intro V hV
      have hV' : V ∈ T_dyadic p := hT_QTTC_sub p (hP'_sub hp) (hT'_sub p hp hV)
      rcases Finset.mem_image.mp hV' with ⟨ℓ, hℓ, rfl⟩
      exact ⟨ℓ, hℓ, rfl⟩
    -- Pick a default AffineLine for V outside T'_dyadic p (never used in image)
    have hT_nonempty : (T p).Nonempty := by
      have h : M / 2 < (T p).card := (h_size p (hP'_sub hp)).1
      have h' : 0 < (T p).card := by omega
      exact Finset.card_pos.mp h'
    let ℓ0 : AffineLine := Classical.choose hT_nonempty
    -- Map each V to a chosen preimage; injective because snaps differ
    let f (V : DyadicTube n) : AffineLine :=
      if hV : V ∈ T'_dyadic p then Classical.choose (h1 V hV) else ℓ0
    have hf_spec : ∀ V ∈ T'_dyadic p, f V ∈ T p ∧ snapTube n (f V) = V := by
      intro V hV
      have h_f_def : f V = Classical.choose (h1 V hV) := by
        simp [f, hV] <;> rfl
      rw [h_f_def]
      exact Classical.choose_spec (h1 V hV)
    have h_inj : Set.InjOn f (T'_dyadic p : Set (DyadicTube n)) := by
      intro V1 hV1 V2 hV2 h
      have h1 : snapTube n (f V1) = V1 := (hf_spec V1 hV1).2
      have h2 : snapTube n (f V2) = V2 := (hf_spec V2 hV2).2
      rw [h] at h1; rw [h1] at h2; exact h2
    have h_image_sub : (T'_dyadic p).image f ⊆ T'_affine p := by
      intro ℓ hℓ
      rcases Finset.mem_image.mp hℓ with ⟨V, hV, rfl⟩
      have hℓ_in_T : f V ∈ T p := (hf_spec V hV).1
      have h_snap : snapTube n (f V) = V := (hf_spec V hV).2
      exact Finset.mem_filter.mpr ⟨hℓ_in_T, by rw [h_snap]; exact hV⟩
    have h_card_image : ((T'_dyadic p).image f).card = (T'_dyadic p).card :=
      Finset.card_image_of_injOn h_inj
    have h : ((T'_dyadic p).image f).card ≤ (T'_affine p).card :=
      Finset.card_le_card h_image_sub
    rw [h_card_image] at h; exact h

  -- K adjustment for thinning + M-adjustment
  let K : ℝ := K_typed * D * 1936
  have hK_one' : 1 ≤ K := by
    have h1 : 1 ≤ K_typed := hK_one
    have h2 : 1 ≤ (1936 : ℝ) := by norm_num
    have h3 : 1 ≤ D := hD_one
    have h4 : 1 ≤ K_typed * D * 1936 := by
      calc 1 = 1 * 1 * 1 := by ring
      _ ≤ K_typed * D * 1936 := by gcongr <;> linarith
    exact h4
  have hΔ_lt_half' : Δ ≤ 1 / 2 := by
    rw [hΔ_eq]
    have h_pow : (2 : ℝ)^m ≥ 2 := by
      have h' : 1 ≤ m := hm_pos
      have h : ∀ n : ℕ, 1 ≤ n → (2 : ℝ)^n ≥ 2 := by
        intro n hn
        induction' hn with n hn IH
        · norm_num
        · simp [pow_succ] at * <;> linarith
      exact h m h'
    dsimp only [dyadicDelta]
    have h3 : 1 / (2 : ℝ)^m ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact h_pow
    exact h3
  have hK_boundΔ : K_typed ≤ A_typed * Real.rpow (Real.log (2 / Δ)) A_typed := by
    have h_eq : Real.log (2 / (dyadicDelta m)) = Real.log (2 / Δ) := by
      rw [hΔ_eq]
    rw [h_eq] at hK_bound
    exact hK_bound
  have hK_bound' : K ≤ A * Real.rpow (Real.log (2 / Δ)) A :=
    k_bound_helper A_typed K_typed D Δ s hA_one hK_one hD_one
      (by linarith) hΔ_pos' hΔ_lt_half' hK_boundΔ A K rfl rfl

  -- C₂ for S-set transfer
  let C₂ : ℝ := C₂_typed * 1936 * (88 : ℝ)^s
  have hC2_one' : 1 ≤ C₂ := by
    have h1 : 1 ≤ C₂_typed := hC2_one
    have h2 : 0 ≤ s := by linarith
    have h3 : 1 ≤ (88 : ℝ)^s := by
      have h : (1 : ℝ)^s ≤ (88 : ℝ)^s := Real.rpow_le_rpow (by linarith) (by norm_num) h2
      have h9 : (1 : ℝ)^s = 1 := Real.one_rpow s
      rw [h9] at h; exact h
    have h4 : 1 ≤ (1936 : ℝ) := by norm_num
    have h6 : 1 ≤ C₂_typed * 1936 := by
      have h7 : 1 * 1 ≤ C₂_typed * 1936 := mul_le_mul h1 h4 (by norm_num) (by linarith)
      simpa using h7
    have h5 : 1 ≤ C₂_typed * 1936 * (88 : ℝ)^s := by
      have h8 : 1 * 1 ≤ (C₂_typed * 1936) * (88 : ℝ)^s :=
        mul_le_mul h6 h3 (by positivity) (by linarith)
      simpa using h8
    simpa [C₂] using h5

  have hC_thin_nonempty : C_thin.Nonempty := by
    have hC'_nonempty : C'_dyadic.Nonempty := hC'_sset_typed.1
    by_contra h
    have h_empty : C_thin = ∅ := by simpa using h
    rw [h_empty] at h_card_thin
    have h4 : (C'_dyadic.card : ℝ) ≤ 0 := by simpa using h_card_thin
    have h4' : C'_dyadic.card ≤ 0 := by exact_mod_cast h4
    have h5 : C'_dyadic.card = 0 := Nat.eq_zero_of_le_zero h4'
    have h6 : C'_dyadic = ∅ := Finset.card_eq_zero.mp h5
    exact hC'_nonempty.ne_empty h6

  have hC_affine_nonempty : C'_affine.Nonempty :=
    Finset.Nonempty.image hC_thin_nonempty _

  -- ========================================================================
  -- S-set transfer
  -- ========================================================================
  have h_sset_thin : _root_.IsFiniteDeltaSSet Δ' s (C₂_typed * 1936) C_thin := by
    have h1 : C_thin ⊆ C'_dyadic := h_thin_sub
    have h2 : (C'_dyadic.card : ℝ) ≤ 1936 * (C_thin.card : ℝ) := h_card_thin
    have hC2_1936_one : 1 ≤ C₂_typed * 1936 := by
      have h1' : 1 ≤ C₂_typed := hC2_one
      have h2' : 1 ≤ (1936 : ℝ) := by norm_num
      have h3' : 1 * 1 ≤ C₂_typed * 1936 := mul_le_mul h1' h2' (by norm_num) (by linarith)
      simpa using h3'
    have h_sep_dyadic := hC'_sset_typed.2.2.2.2.1
    have h_sep_thin : SeparatedAt Δ' (C_thin : Set (DyadicTube m)) := by
      have h_eq : Δ' = dyadicDelta m := by simp [Δ']
      rw [h_eq]
      exact h_sep_dyadic.mono h1
    have h_growth : ∀ (x : DyadicTube m) (r : ℝ), Δ' ≤ r →
        ((C_thin.filter fun y => dist y x ≤ r).card : ℝ) ≤
          (C₂_typed * 1936) * r ^ s * (C_thin.card : ℝ) := by
      intro x r hr
      have h3 : ((C_thin.filter fun y => dist y x ≤ r).card : ℝ) ≤
          ((C'_dyadic.filter fun y => dist y x ≤ r).card : ℝ) := by
        simpa using Finset.card_le_card (Finset.filter_subset_filter _ h1)
      have h4 : ((C'_dyadic.filter fun y => dist y x ≤ r).card : ℝ) ≤
          C₂_typed * r ^ s * (C'_dyadic.card : ℝ) := hC'_sset_typed.2.2.2.2.2 x r hr
      have h5 : (C'_dyadic.card : ℝ) ≤ 1936 * (C_thin.card : ℝ) := h2
      have h_rpos : 0 < r := lt_of_lt_of_le hC'_sset_typed.2.1 hr
      have h6 : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
      have h7 : 0 ≤ C₂_typed := by linarith [hC2_one]
      calc ((C_thin.filter fun y => dist y x ≤ r).card : ℝ)
        ≤ ((C'_dyadic.filter fun y => dist y x ≤ r).card : ℝ) := h3
      _ ≤ C₂_typed * r ^ s * (C'_dyadic.card : ℝ) := h4
      _ ≤ C₂_typed * r ^ s * (1936 * (C_thin.card : ℝ)) := by gcongr
      _ = (C₂_typed * 1936) * r ^ s * (C_thin.card : ℝ) := by ring
    exact ⟨hC_thin_nonempty, hC'_sset_typed.2.1, hC2_1936_one, hC'_sset_typed.2.2.2.1, h_sep_thin, h_growth⟩

  have h_slope_thin : ∀ U ∈ C_thin, |U.slope| ≤ 1 :=
    fun U hU => hC_slope U (h_thin_sub hU)
  have h_intercept_thin : ∀ U ∈ C_thin, |U.intercept| ≤ 3 :=
    fun U hU => hC_intercept U (h_thin_sub hU)
  have hΔ'_eq : Δ' = Δ := by simp [Δ', hΔ_eq]
  have hC'_sset_affine : _root_.IsFiniteDeltaSSet Δ s C₂ C'_affine :=
    affine_sset_transfer h_sset_thin rfl h_slope_thin h_intercept_thin hC2_one
      (by linarith [hΔ'_eq]) hΔ_pos' (by linarith) rfl h_sep_delta hC_affine_nonempty hC_thin_nonempty

  have hC'_delta_sset : IsDeltaSSet Δ s (max 1 (QTTC_Assembly.C_PACK * C₂)) (C'_affine : Set AffineLine) :=
    QTTC_Assembly.IsFiniteDeltaSSet.to_delta_sset_affineLine hC'_sset_affine

  -- C₂ bound
  have hC1_QTTC_def : C₁_QTTC = C₁ * (40 : ℝ)^s * B * D := by
    dsimp only [C₁_QTTC, C₁'] <;> ring
  have hD_eq : D = 2 * B := by
    have h1 : D_nat = 2 * B_nat := by simp [D_nat]
    have h2 : (D_nat : ℝ) = 2 * (B_nat : ℝ) := by
      rw [h1] <;> simp
    exact h2
  have hC2_bound' : C₂ ≤ A * Real.rpow K A * C₁ :=
    c2_bound_helper s A_typed K_typed C₁ C₂_typed B D A K C₂ C₁_QTTC
      hA_one hK_one hB_one hD_one hC1 (by linarith) hD_eq rfl rfl rfl hC1_QTTC_def hC2_bound

  -- ========================================================================
  -- Coarse tube parameter bounds
  -- ========================================================================
  have hC'_slope : ∀ c ∈ C'_affine, |tubeSlope c| ≤ 1 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨U, hU, rfl⟩
    have h : |U.slope| ≤ 1 := hC_slope U (h_thin_sub hU)
    simpa [dyadicTubeToA2_slope] using h

  have hC'_v : ∀ c ∈ C'_affine, (LemmaE.getDirV c) 1 ≠ 0 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨U, hU, rfl⟩
    exact dyadicTubeToA2_getDirV_ne_zero U

  have hC'_b : ∀ c ∈ C'_affine, |tubeIntercept c| ≤ 3 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨U, hU, rfl⟩
    have h : |U.intercept| ≤ 3 := h_intercept_dyadic U (h_global_sub (hC'_sub (h_thin_sub hU)))
    simpa [dyadicTubeToA2_intercept] using h

  -- ========================================================================
  -- Near-point incidence
  -- ========================================================================
  have hC'_near : ∀ c ∈ C'_affine, ∃ p ∈ P', |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨U, hU_thin, hc_eq⟩
    have hU' : U ∈ C'_dyadic := h_thin_sub hU_thin
    -- H > 0 and incidence bound imply some p has nonempty pointFiberG
    have hH_pos' : 0 < H := hH_pos
    have h_h_sum : (H : ℝ) ≤ ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card :=
      h_pointFiberG U hU'
    have h_nonempty_sum : 0 < ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card := by
      have h_pos' : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
      have h_h_sum' : (H : ℝ) ≤ ∑ p ∈ P', ↑(pointFiberG hnm T'_dyadic p U).card := by
        simpa [Nat.cast_sum] using h_h_sum
      have h : (0 : ℝ) < ∑ p ∈ P', ↑(pointFiberG hnm T'_dyadic p U).card :=
        lt_of_lt_of_le h_pos' h_h_sum'
      exact_mod_cast h
    have h_exists_p : ∃ p ∈ P', (pointFiberG hnm T'_dyadic p U).Nonempty := by
      by_contra h
      push Not at h
      have h_all_empty : ∀ p ∈ P', (pointFiberG hnm T'_dyadic p U).card = 0 := by
        intro p hp
        have hne : (pointFiberG hnm T'_dyadic p U) = ∅ := by
          simpa [Finset.Nonempty] using h p hp
        rw [hne] <;> simp
      have h_sum_zero : ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card = 0 := by
        apply Finset.sum_eq_zero
        intro p hp; exact h_all_empty p hp
      rw [h_sum_zero] at h_nonempty_sum <;> simp at h_nonempty_sum
    rcases h_exists_p with ⟨p, hp, hfiber_nonempty⟩
    rcases hfiber_nonempty with ⟨V, hV⟩
    have hV_and : V ∈ T'_dyadic p ∧ sp hnm V = U := by simpa [pointFiberG] using hV
    have hV_in : V ∈ T'_dyadic p := hV_and.1
    have h_sp : sp hnm V = U := hV_and.2
    -- Pick original preimage ℓ of V
    have hV' : V ∈ T_dyadic p := hT_QTTC_sub p (hP'_sub hp) (hT'_sub p hp hV_in)
    rcases Finset.mem_image.mp hV' with ⟨ℓ, hℓ_in_T, h_snap_eq⟩
    have hℓ_in_T' : ℓ ∈ T'_affine p := by
      exact Finset.mem_filter.mpr ⟨hℓ_in_T, by rw [h_snap_eq]; exact hV_in⟩
    -- ℓ is in parent cell of c: |slope ℓ - slope c| < Δ, |intercept ℓ - intercept c| < Δ
    have h_sp' : sp hnm (snapTube n ℓ) = U := by
      rw [h_snap_eq]; exact h_sp
    have h_iff : sp hnm (snapTube n ℓ) = U ↔
        InParent Δ hΔ_pos' ℓ (dyadicTubeToA2 U) := by
      have h_tmp := sourceParent_snap_iff_inParent hnm ℓ U (dyadicDelta_pos m)
      have h_eq2 : Δ = dyadicDelta m := by simp [hΔ_eq]
      exact h_eq2 ▸ h_tmp
    have h_in_parent : InParent Δ hΔ_pos' ℓ (dyadicTubeToA2 U) := h_iff.mp h_sp'
    -- p is within 2δ of ℓ.1
    have h_p_near_ℓ : p ∈ Metric.cthickening (2 * δ) ℓ.1 := h_inc p (hP'_sub hp) ℓ hℓ_in_T
    have h_p1_bound : |p 1| ≤ R := h_ball p (hP'_sub hp)
    -- Tube parameter bounds for ℓ
    have h_ℓ_v1 : (LemmaE.getDirV ℓ) 1 ≠ 0 := (h_slope p (hP'_sub hp) ℓ hℓ_in_T).1
    have h_ℓ_slope : |tubeSlope ℓ| ≤ 1 := (h_slope p (hP'_sub hp) ℓ hℓ_in_T).2.1
    have hδ_pos' : 0 < δ := by rw [hδ_eq]; exact dyadicDelta_pos n
    -- Algebraic near bound for p relative to ℓ: |p0 - slope ℓ * p1 - intercept ℓ| ≤ 4δ
    have h_algebraic_ℓ : |p 0 - tubeSlope ℓ * p 1 - tubeIntercept ℓ| ≤ 4 * δ := by
      have h := perpendicular_to_algebraic_distance p ℓ (2 * δ) (by linarith) h_ℓ_v1 h_ℓ_slope h_p_near_ℓ
      have h_eq : (2 * (2 * δ) : ℝ) = 4 * δ := by ring
      rw [h_eq] at h
      exact h
    -- InParent gives parameter differences < Δ
    have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos'
    have h_cells : InParent Δ hΔ_pos' ℓ (dyadicTubeToA2 U) := h_in_parent
    have h_cell1 : ⌊tubeSlope ℓ / Δ⌋ = ⌊tubeSlope (dyadicTubeToA2 U) / Δ⌋ := by
      simpa [parentCell, InParent] using congr_arg Prod.fst h_cells
    have h_cell2 : ⌊tubeIntercept ℓ / Δ⌋ = ⌊tubeIntercept (dyadicTubeToA2 U) / Δ⌋ := by
      simpa [parentCell, InParent] using congr_arg Prod.snd h_cells
    have h_slope_diff : |tubeSlope ℓ - tubeSlope (dyadicTubeToA2 U)| < Δ := by
      have h : |tubeSlope ℓ / Δ - tubeSlope (dyadicTubeToA2 U) / Δ| < 1 := floor_eq_abs_lt_one h_cell1
      have h2 : |tubeSlope ℓ - tubeSlope (dyadicTubeToA2 U)| = Δ * |tubeSlope ℓ / Δ - tubeSlope (dyadicTubeToA2 U) / Δ| := by
        have h3 : tubeSlope ℓ - tubeSlope (dyadicTubeToA2 U) = Δ * (tubeSlope ℓ / Δ - tubeSlope (dyadicTubeToA2 U) / Δ) := by
          field_simp [hΔ_ne] <;> ring
        rw [h3, abs_mul, abs_of_pos hΔ_pos']
      rw [h2]; nlinarith
    have h_int_diff : |tubeIntercept ℓ - tubeIntercept (dyadicTubeToA2 U)| < Δ := by
      have h : |tubeIntercept ℓ / Δ - tubeIntercept (dyadicTubeToA2 U) / Δ| < 1 := floor_eq_abs_lt_one h_cell2
      have h2 : |tubeIntercept ℓ - tubeIntercept (dyadicTubeToA2 U)| = Δ * |tubeIntercept ℓ / Δ - tubeIntercept (dyadicTubeToA2 U) / Δ| := by
        have h3 : tubeIntercept ℓ - tubeIntercept (dyadicTubeToA2 U) = Δ * (tubeIntercept ℓ / Δ - tubeIntercept (dyadicTubeToA2 U) / Δ) := by
          field_simp [hΔ_ne] <;> ring
        rw [h3, abs_mul, abs_of_pos hΔ_pos']
      rw [h2]; nlinarith
    have hδ_le_Δ : δ ≤ Δ := by
      rw [hδ_eq, hΔ_eq]
      have h1 : m ≤ n := hnm
      have h_base : 1 ≤ (2 : ℝ) := by norm_num
      have h2 : (2 : ℝ)^n ≥ (2 : ℝ)^m := by
        gcongr <;> exact h_base
      have h3 : dyadicDelta n ≤ dyadicDelta m := by
        dsimp only [dyadicDelta] <;> gcongr
      exact h3
    -- Convert bounds from dyadicTubeToA2 U to c
    have h_slope_diff_c : |tubeSlope ℓ - tubeSlope c| < Δ := by
      have h_eq : tubeSlope (dyadicTubeToA2 U) = tubeSlope c := congr_arg tubeSlope hc_eq
      rw [h_eq] at h_slope_diff
      exact h_slope_diff
    have h_int_diff_c : |tubeIntercept ℓ - tubeIntercept c| < Δ := by
      have h_eq : tubeIntercept (dyadicTubeToA2 U) = tubeIntercept c := congr_arg tubeIntercept hc_eq
      rw [h_eq] at h_int_diff
      exact h_int_diff
    -- Algebraic bound: |p 0 - slope c * p 1 - intercept c| ≤ 4δ + Δ*|p 1| + Δ ≤ 4Δ
    set x := p 0 - tubeSlope ℓ * p 1 - tubeIntercept ℓ with hx_def
    set y := (tubeSlope ℓ - tubeSlope c) * p 1 with hy_def
    set z := tubeIntercept ℓ - tubeIntercept c with hz_def
    have h_step1 : |p 0 - tubeSlope c * p 1 - tubeIntercept c| ≤ |x| + |y| + |z| := by
      have h_eq1 : p 0 - tubeSlope c * p 1 - tubeIntercept c = x + y + z := by
        simp [hx_def, hy_def, hz_def] <;> ring
      rw [h_eq1]
      have h1 : |x + y + z| ≤ |x + y| + |z| := by
        exact real_abs_add (x + y) z
      have h2 : |x + y| ≤ |x| + |y| := by exact real_abs_add x y
      linarith
    have h_abs_mul : |y| = |tubeSlope ℓ - tubeSlope c| * |p 1| := by
      simp [hy_def, abs_mul]
    have h_bound2 : |x| + |y| + |z| ≤ 4 * δ + |tubeSlope ℓ - tubeSlope c| * |p 1| + |tubeIntercept ℓ - tubeIntercept c| := by
      rw [h_abs_mul]
      gcongr <;> linarith [h_algebraic_ℓ]
    have h_main_ineq : |p 0 - tubeSlope c * p 1 - tubeIntercept c| ≤ 4 * Δ := by
      calc |p 0 - tubeSlope c * p 1 - tubeIntercept c|
        ≤ |x| + |y| + |z| := h_step1
      _ ≤ 4 * δ + |tubeSlope ℓ - tubeSlope c| * |p 1| + |tubeIntercept ℓ - tubeIntercept c| := h_bound2
      _ ≤ 4 * δ + Δ * R + Δ := by
        have h1 : |tubeSlope ℓ - tubeSlope c| * |p 1| ≤ Δ * R := by
          have h1a : |tubeSlope ℓ - tubeSlope c| ≤ Δ := by linarith [h_slope_diff_c]
          have h1b : |p 1| ≤ R := h_p1_bound
          calc |tubeSlope ℓ - tubeSlope c| * |p 1|
            ≤ Δ * |p 1| := by gcongr <;> linarith
          _ ≤ Δ * R := by gcongr <;> linarith
        have h2 : |tubeIntercept ℓ - tubeIntercept c| ≤ Δ := by linarith [h_int_diff_c]
        linarith
      _ ≤ 4 * (Δ / 4) + Δ * Real.sqrt 2 + Δ := by
        gcongr <;> linarith [hR]
      _ = (2 + Real.sqrt 2) * Δ := by ring
      _ ≤ 4 * Δ := by
        have h_sqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_iff] <;> norm_num
        have hΔ_nonneg : 0 ≤ Δ := by linarith [hΔ_pos']
        have h : (2 + Real.sqrt 2) * Δ ≤ 4 * Δ := by
          calc (2 + Real.sqrt 2) * Δ
            ≤ (2 + 2) * Δ := by gcongr <;> linarith
          _ = 4 * Δ := by ring
        exact h
    have h_main_ineq' : |tubeIntercept c - (p 0 - tubeSlope c * p 1)| ≤ 4 * Δ := by
      have h_eq : tubeIntercept c - (p 0 - tubeSlope c * p 1) =
          -(p 0 - tubeSlope c * p 1 - tubeIntercept c) := by ring
      rw [h_eq, abs_neg]
      exact h_main_ineq
    exact ⟨p, hp, h_main_ineq'⟩

  -- ========================================================================
  -- Exact-parent provenance via composite:
  -- ell → snapTube n ell → sp hnm → dyadicTubeToA2 = c
  -- This is the structural witness needed for C_Q ⊆ T_Delta.
  -- ========================================================================
  have h_exact_parent : ∀ c ∈ C'_affine,
      ∃ (p : Plane) (hp : p ∈ P') (ell : AffineLine)
        (hell : ell ∈ T'_affine p) (U : DyadicTube m),
        sp hnm (snapTube n ell) = U ∧ c = dyadicTubeToA2 U := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨U, hU_thin, rfl⟩
    have hU' : U ∈ C'_dyadic := h_thin_sub hU_thin
    have hH_pos' : 0 < H := hH_pos
    have h_h_sum : (H : ℝ) ≤ ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card :=
      h_pointFiberG U hU'
    have h_nonempty_sum : 0 < ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card := by
      have h_pos' : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
      have h_h_sum' : (H : ℝ) ≤ ∑ p ∈ P', ↑(pointFiberG hnm T'_dyadic p U).card := by
        simpa [Nat.cast_sum] using h_h_sum
      have h : (0 : ℝ) < ∑ p ∈ P', ↑(pointFiberG hnm T'_dyadic p U).card :=
        lt_of_lt_of_le h_pos' h_h_sum'
      exact_mod_cast h
    have h_exists_p : ∃ p ∈ P', (pointFiberG hnm T'_dyadic p U).Nonempty := by
      by_contra h
      push Not at h
      have h_all_empty : ∀ p ∈ P', (pointFiberG hnm T'_dyadic p U).card = 0 := by
        intro p hp
        have hne : (pointFiberG hnm T'_dyadic p U) = ∅ := by
          simpa [Finset.Nonempty] using h p hp
        rw [hne] <;> simp
      have h_sum_zero : ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card = 0 := by
        apply Finset.sum_eq_zero
        intro p hp; exact h_all_empty p hp
      rw [h_sum_zero] at h_nonempty_sum <;> simp at h_nonempty_sum
    rcases h_exists_p with ⟨p, hp, hfiber_nonempty⟩
    rcases hfiber_nonempty with ⟨V, hV⟩
    have hV_and : V ∈ T'_dyadic p ∧ sp hnm V = U := by simpa [pointFiberG] using hV
    have hV_in : V ∈ T'_dyadic p := hV_and.1
    have h_sp : sp hnm V = U := hV_and.2
    have hV' : V ∈ T_dyadic p := hT_QTTC_sub p (hP'_sub hp) (hT'_sub p hp hV_in)
    rcases Finset.mem_image.mp hV' with ⟨ell, hell_in_T, h_snap_eq⟩
    have hell_in_T' : ell ∈ T'_affine p :=
      Finset.mem_filter.mpr ⟨hell_in_T, by rw [h_snap_eq]; exact hV_in⟩
    have h_sp' : sp hnm (snapTube n ell) = U := by
      rw [h_snap_eq]; exact h_sp
    exact ⟨p, hp, ell, hell_in_T', U, h_sp', rfl⟩

  -- ========================================================================
  -- PointFiber lower bound (H2): pointFiberG ⊆ image of pointFiber under snapTube
  -- ========================================================================
  have h_pointFiber_inc : ∀ (hΔ_pos : 0 < Δ), ∀ c ∈ C'_affine,
      (H : ℝ) ≤ ∑ p ∈ P', (pointFiber Δ hΔ_pos T'_affine p c).card := by
    intro hΔ_pos c hc
    rcases Finset.mem_image.mp hc with ⟨U, hU_thin, rfl⟩
    have hU' : U ∈ C'_dyadic := h_thin_sub hU_thin
    have h_main_inc : (H : ℝ) ≤
        ∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card := h_pointFiberG U hU'
    have h_ineq : ∀ p ∈ P', (pointFiberG hnm T'_dyadic p U).card ≤
        (pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).card := by
      intro p hp
      -- Show pointFiberG ⊆ (pointFiber).image (snapTube n)
      have h_sub : pointFiberG hnm T'_dyadic p U ⊆
          (pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).image (snapTube n) := by
        intro V hV
        have hV_and : V ∈ T'_dyadic p ∧ sp hnm V = U := by simpa [pointFiberG] using hV
        have hV_in : V ∈ T'_dyadic p := hV_and.1
        have h_sp : sp hnm V = U := hV_and.2
        have hV' : V ∈ T_dyadic p := hT_QTTC_sub p (hP'_sub hp) (hT'_sub p hp hV_in)
        rcases Finset.mem_image.mp hV' with ⟨ℓ, hℓ_in_T, h_snap_eq⟩
        have hℓ_in_T' : ℓ ∈ T'_affine p :=
          Finset.mem_filter.mpr ⟨hℓ_in_T, by rw [h_snap_eq]; exact hV_in⟩
        have h_sp' : sp hnm (snapTube n ℓ) = U := by
          rw [h_snap_eq]; exact h_sp
        have h_iff : sp hnm (snapTube n ℓ) = U ↔
            InParent Δ hΔ_pos ℓ (dyadicTubeToA2 U) := by
          have h_tmp := sourceParent_snap_iff_inParent hnm ℓ U (dyadicDelta_pos m)
          have h_eq2 : Δ = dyadicDelta m := by simp [hΔ_eq]
          exact h_eq2 ▸ h_tmp
        have h_in_parent : InParent Δ hΔ_pos ℓ (dyadicTubeToA2 U) := h_iff.mp h_sp'
        have hℓ_in_pf : ℓ ∈ pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U) :=
          Finset.mem_filter.mpr ⟨hℓ_in_T', h_in_parent⟩
        exact Finset.mem_image.mpr ⟨ℓ, hℓ_in_pf, h_snap_eq⟩
      calc (pointFiberG hnm T'_dyadic p U).card
        ≤ ((pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).image (snapTube n)).card :=
          Finset.card_le_card h_sub
      _ ≤ (pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).card :=
          Finset.card_image_le
    have h_sum_nat : (∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card) ≤
        (∑ p ∈ P', (pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).card) :=
      Finset.sum_le_sum h_ineq
    have h_sum_cast : (↑(∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card) : ℝ) ≤
        (↑(∑ p ∈ P', (pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).card) : ℝ) :=
      Nat.cast_le.mpr h_sum_nat
    calc (H : ℝ)
      ≤ ↑(∑ p ∈ P', (pointFiberG hnm T'_dyadic p U).card) := h_main_inc
    _ ≤ ↑(∑ p ∈ P', (pointFiber Δ hΔ_pos T'_affine p (dyadicTubeToA2 U)).card) := h_sum_cast

  -- ========================================================================
  -- PointFiber upper bound via ORIGINAL BallGrowth on AffineLine
  -- Center at an original tube ℓ0 in the pointFiber (all hypotheses satisfied).
  -- ========================================================================
  have h_pointFiber_upper : ∀ (hΔ_pos : 0 < Δ), ∀ p ∈ P', ∀ c ∈ C'_affine,
      (pointFiber Δ hΔ_pos T'_affine p c).card ≤
        C₁ * GEOM_CONST s * (T p).card * Δ^s := by
    intro hΔ_pos p hp c hc
    by_cases h_empty : (pointFiber Δ hΔ_pos T'_affine p c) = ∅
    · rw [h_empty]
      simp
      have hpos : 0 ≤ C₁ * GEOM_CONST s * (T p).card * Δ ^ s := by
        have hC1_pos : 0 < C₁ := by linarith [hC1]
        have hGEOM_pos : 0 < GEOM_CONST s := by
          dsimp only [GEOM_CONST]
          exact Real.rpow_pos_of_pos (by norm_num) s
        have hΔs_pos : 0 ≤ Δ ^ s := Real.rpow_nonneg (by linarith) s
        have hT_card : 0 ≤ (T p).card := by positivity
        have hT_card' : 0 ≤ ((T p).card : ℝ) := by exact_mod_cast hT_card
        exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hT_card') hΔs_pos
      exact hpos
    · let PF := pointFiber Δ hΔ_pos T'_affine p c
      have hPF_sub : PF ⊆ T p := by
        intro ℓ hℓ
        have h2 : ℓ ∈ T'_affine p := (Finset.mem_filter.mp hℓ).1
        exact Finset.mem_filter.mp h2 |>.1
      -- Pick ℓ0 ∈ PF as center
      have h_nonempty : PF.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
      let ℓ0 : AffineLine := Classical.choose h_nonempty
      have hℓ0 : ℓ0 ∈ PF := Classical.choose_spec h_nonempty
      have hℓ0_in_T : ℓ0 ∈ T p := by
        have h2 : ℓ0 ∈ T'_affine p := (Finset.mem_filter.mp hℓ0).1
        exact Finset.mem_filter.mp h2 |>.1
      have hℓ0_parent : InParent Δ hΔ_pos ℓ0 c := (Finset.mem_filter.mp hℓ0).2
      -- All ℓ ∈ PF are in same parent cell as ℓ0, so dist ℓ ℓ0 < 6Δ
      have h2 : ∀ ℓ ∈ PF, dist ℓ ℓ0 ≤ 6 * Δ := by
        intro ℓ hℓ
        have h_parent_ℓ : InParent Δ hΔ_pos ℓ c := (Finset.mem_filter.mp hℓ).2
        have h_parent_ℓ0 : InParent Δ hΔ_pos ℓ0 c := hℓ0_parent
        -- Both in same parent cell as c → InParent ℓ ℓ0
        have h_cell_eq : parentCell Δ hΔ_pos ℓ = parentCell Δ hΔ_pos ℓ0 :=
          h_parent_ℓ.trans h_parent_ℓ0.symm
        have h_in_parent : InParent Δ hΔ_pos ℓ ℓ0 := h_cell_eq
        have hΔ_ne : Δ ≠ 0 := hΔ_pos.ne'
        have h_cell1 : ⌊tubeSlope ℓ / Δ⌋ = ⌊tubeSlope ℓ0 / Δ⌋ := by
          simpa [parentCell, InParent] using congr_arg Prod.fst h_in_parent
        have h_cell2 : ⌊tubeIntercept ℓ / Δ⌋ = ⌊tubeIntercept ℓ0 / Δ⌋ := by
          simpa [parentCell, InParent] using congr_arg Prod.snd h_in_parent
        have h_slope_diff : |tubeSlope ℓ - tubeSlope ℓ0| < Δ := by
          have h : |tubeSlope ℓ / Δ - tubeSlope ℓ0 / Δ| < 1 := floor_eq_abs_lt_one h_cell1
          have h2 : |tubeSlope ℓ - tubeSlope ℓ0| = Δ * |tubeSlope ℓ / Δ - tubeSlope ℓ0 / Δ| := by
            have h3 : tubeSlope ℓ - tubeSlope ℓ0 = Δ * (tubeSlope ℓ / Δ - tubeSlope ℓ0 / Δ) := by
              field_simp [hΔ_ne] <;> ring
            rw [h3, abs_mul, abs_of_pos hΔ_pos]
          rw [h2]; nlinarith
        have h_int_diff : |tubeIntercept ℓ - tubeIntercept ℓ0| < Δ := by
          have h : |tubeIntercept ℓ / Δ - tubeIntercept ℓ0 / Δ| < 1 := floor_eq_abs_lt_one h_cell2
          have h2 : |tubeIntercept ℓ - tubeIntercept ℓ0| = Δ * |tubeIntercept ℓ / Δ - tubeIntercept ℓ0 / Δ| := by
            have h3 : tubeIntercept ℓ - tubeIntercept ℓ0 = Δ * (tubeIntercept ℓ / Δ - tubeIntercept ℓ0 / Δ) := by
              field_simp [hΔ_ne] <;> ring
            rw [h3, abs_mul, abs_of_pos hΔ_pos]
          rw [h2]; nlinarith
        -- L∞ param distance < Δ
        have h_param_linf : dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ0, tubeIntercept ℓ0) < Δ := by
          have h_main : dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ0, tubeIntercept ℓ0) =
              max (|tubeSlope ℓ - tubeSlope ℓ0|) (|tubeIntercept ℓ - tubeIntercept ℓ0|) := by
            simp [Prod.dist_eq] <;> rfl
          rw [h_main]
          exact max_lt h_slope_diff h_int_diff
        -- Antilipschitz: dist ≤ 6 * param_dist (B=3, constant 3+3=6)
        have hℓ_in_T : ℓ ∈ T p := by
          have h2' : ℓ ∈ T'_affine p := (Finset.mem_filter.mp hℓ).1
          exact Finset.mem_filter.mp h2' |>.1
        have h_v1 : (LemmaE.getDirV ℓ) 1 ≠ 0 := (h_slope p (hP'_sub hp) ℓ hℓ_in_T).1
        have h_v2 : (LemmaE.getDirV ℓ0) 1 ≠ 0 := (h_slope p (hP'_sub hp) ℓ0 hℓ0_in_T).1
        have h_a1 : |tubeSlope ℓ| ≤ 1 := (h_slope p (hP'_sub hp) ℓ hℓ_in_T).2.1
        have h_a2 : |tubeSlope ℓ0| ≤ 1 := (h_slope p (hP'_sub hp) ℓ0 hℓ0_in_T).2.1
        have h_b1 : |tubeIntercept ℓ| ≤ 3 := (h_slope p (hP'_sub hp) ℓ hℓ_in_T).2.2
        have h_b2 : |tubeIntercept ℓ0| ≤ 3 := (h_slope p (hP'_sub hp) ℓ0 hℓ0_in_T).2.2
        have h_lip : dist ℓ ℓ0 ≤ (3 + 3 : ℝ) * dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ0, tubeIntercept ℓ0) :=
          affineLine_antilipschitz_general (B := 3) (by norm_num) ℓ ℓ0 h_v1 h_v2 h_b2
        have h : dist ℓ ℓ0 < 6 * Δ := by
          calc dist ℓ ℓ0
            ≤ (3 + 3 : ℝ) * dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ0, tubeIntercept ℓ0) := h_lip
          _ = 6 * dist (tubeSlope ℓ, tubeIntercept ℓ) (tubeSlope ℓ0, tubeIntercept ℓ0) := by norm_num
          _ < 6 * Δ := by gcongr
        exact le_of_lt h
      have h3 : PF ⊆ (T p).filter (fun ℓ => dist ℓ ℓ0 ≤ 6 * Δ) := by
        intro ℓ hℓ
        have h_in_T : ℓ ∈ T p := by
          have h2' : ℓ ∈ T'_affine p := (Finset.mem_filter.mp hℓ).1
          exact Finset.mem_filter.mp h2' |>.1
        exact Finset.mem_filter.mpr ⟨h_in_T, h2 ℓ hℓ⟩
      have h4 : δ ≤ 6 * Δ := by
        have h5 : δ ≤ Δ := by
          rw [hδ_eq, hΔ_eq]
          dsimp only [dyadicDelta]
          have h6 : m ≤ n := hnm
          have h7 : (2 : ℝ)^m ≤ (2 : ℝ)^n := by
            gcongr
            <;> norm_num
          exact one_div_le_one_div_of_le (by positivity) h7
        linarith
      have h_bg := h_sset p (hP'_sub hp)
      have h_count := h_bg.growth ℓ0 (6 * Δ) h4
      have h10 : PF.card ≤ ((T p).filter (fun ℓ => dist ℓ ℓ0 ≤ 6 * Δ)).card :=
        Finset.card_le_card h3
      have h11 : (PF.card : ℝ) ≤ (((T p).filter (fun ℓ => dist ℓ ℓ0 ≤ 6 * Δ)).card : ℝ) :=
        Nat.cast_le.mpr h10
      calc (PF.card : ℝ)
        ≤ (((T p).filter (fun ℓ => dist ℓ ℓ0 ≤ 6 * Δ)).card : ℝ) := h11
      _ ≤ C₁ * (6 * Δ)^s * (T p).card := h_count
      _ = C₁ * (6 : ℝ)^s * (T p).card * Δ^s := by
        have hpow : (6 * Δ)^s = (6 : ℝ)^s * Δ^s := by
          rw [Real.mul_rpow (by norm_num) (by linarith)]
        rw [hpow] <;> ring
      _ = C₁ * GEOM_CONST s * (T p).card * Δ^s := by
        simp [GEOM_CONST] <;> ring

  -- ========================================================================
  -- Balance bounds
  -- ========================================================================
  have h_avg_lower' : (M : ℝ) * (P.card : ℝ) ≤ K * (H : ℝ) * (C'_affine.card : ℝ) := by
    have h1 : (C'_affine.card : ℝ) = (C_thin.card : ℝ) := by
      simp [C'_affine, Finset.card_image_of_injective _ dyadicTubeToA2_injective]
    rw [h1]
    have h2 : (C'_dyadic.card : ℝ) ≤ 1936 * (C_thin.card : ℝ) := h_card_thin
    have h3 : (M_QTTC : ℝ) * (P.card : ℝ) ≤ K_typed * (H : ℝ) * (C'_dyadic.card : ℝ) := h_avg_lower
    have h4 : (M : ℝ) ≤ D * (M_QTTC : ℝ) := hM_le_D
    calc (M : ℝ) * (P.card : ℝ)
      ≤ (D * (M_QTTC : ℝ)) * (P.card : ℝ) := by gcongr
    _ = D * ((M_QTTC : ℝ) * (P.card : ℝ)) := by ring
    _ ≤ D * (K_typed * (H : ℝ) * (C'_dyadic.card : ℝ)) := by gcongr
    _ ≤ D * K_typed * (H : ℝ) * (1936 * (C_thin.card : ℝ)) := by
      have h5 : (C'_dyadic.card : ℝ) ≤ 1936 * (C_thin.card : ℝ) := h_card_thin
      have hpos : 0 ≤ D * K_typed * (H : ℝ) := by positivity
      have h_eq : D * (K_typed * (H : ℝ) * (C'_dyadic.card : ℝ)) =
          D * K_typed * (H : ℝ) * (C'_dyadic.card : ℝ) := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_left h5 hpos
    _ = K * (H : ℝ) * (C_thin.card : ℝ) := by
      dsimp only [K] <;> ring

  have hK_ge_K : K_typed ≤ K := by
    dsimp only [K]
    have h1 : 0 ≤ K_typed := by linarith [hK_one]
    have h2 : 1 ≤ D := hD_one
    nlinarith
  have hDK_le_K : D * K_typed ≤ K := by
    dsimp only [K]
    have h_pos : 0 ≤ K_typed := by linarith [hK_one]
    have h2 : D * K_typed = K_typed * D := by ring
    rw [h2]
    have h3 : K_typed * D ≤ K_typed * D * 1936 := by
      have h4 : 0 ≤ K_typed * D := by positivity
      exact le_mul_of_one_le_right h4 (by norm_num)
    exact h3
  have h_avg_upper' : (H : ℝ) * (C'_affine.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ) := by
    have h1 : (C'_affine.card : ℝ) = (C_thin.card : ℝ) := by
      simp [C'_affine, Finset.card_image_of_injective _ dyadicTubeToA2_injective]
    rw [h1]
    have h2 : (C_thin.card : ℝ) ≤ (C'_dyadic.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_thin_sub
    have h3 : (H : ℝ) * (C'_dyadic.card : ℝ) ≤ K_typed * (M_QTTC : ℝ) * (P.card : ℝ) := h_avg_upper
    have hM_QTTC_le_M : M_QTTC ≤ M := by
      dsimp only [M_QTTC]
      exact ceil_div_le_self hM_pos hD_nat_pos
    have h4 : (M_QTTC : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_QTTC_le_M
    calc (H : ℝ) * (C_thin.card : ℝ)
      ≤ (H : ℝ) * (C'_dyadic.card : ℝ) := by gcongr
    _ ≤ K_typed * (M_QTTC : ℝ) * (P.card : ℝ) := h3
    _ ≤ K_typed * (M : ℝ) * (P.card : ℝ) := by
      have hpos : 0 ≤ K_typed * (P.card : ℝ) := by positivity
      have h5 : (M_QTTC : ℝ) * (K_typed * (P.card : ℝ)) ≤ (M : ℝ) * (K_typed * (P.card : ℝ)) :=
        mul_le_mul_of_nonneg_right h4 hpos
      have h6 : K_typed * (M_QTTC : ℝ) * (P.card : ℝ) = (M_QTTC : ℝ) * (K_typed * (P.card : ℝ)) := by ring
      have h7 : K_typed * (M : ℝ) * (P.card : ℝ) = (M : ℝ) * (K_typed * (P.card : ℝ)) := by ring
      rw [h6, h7]; exact h5
    _ ≤ K * (M : ℝ) * (P.card : ℝ) := by
      have hpos : 0 ≤ (M : ℝ) * (P.card : ℝ) := by positivity
      have h8 : K_typed * ((M : ℝ) * (P.card : ℝ)) ≤ K * ((M : ℝ) * (P.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hK_ge_K hpos
      have h9 : K_typed * (M : ℝ) * (P.card : ℝ) = K_typed * ((M : ℝ) * (P.card : ℝ)) := by ring
      have h10 : K * (M : ℝ) * (P.card : ℝ) = K * ((M : ℝ) * (P.card : ℝ)) := by ring
      rw [h9, h10]; exact h8

  have hP_card' : (P.card : ℝ) ≤ K * (P'.card : ℝ) := by
    have h : (P.card : ℝ) ≤ K_typed * (P'.card : ℝ) := hP_card
    calc (P.card : ℝ) ≤ K_typed * (P'.card : ℝ) := h
         _ ≤ K * (P'.card : ℝ) := by
           have hpos : 0 ≤ (P'.card : ℝ) := by positivity
           exact mul_le_mul_of_nonneg_right hK_ge_K hpos

  have hT'_size' : ∀ p ∈ P', (M : ℝ) ≤ K * ((T'_affine p).card : ℝ) := by
    intro p hp
    have h1 : (M_QTTC : ℝ) ≤ K_typed * ((T'_dyadic p).card : ℝ) := hT'_size p hp
    have h2 : (T'_dyadic p).card ≤ (T'_affine p).card := hT'_nonempty_card p hp
    have h4 : (M : ℝ) ≤ D * (M_QTTC : ℝ) := hM_le_D
    have h5 : (M : ℝ) ≤ D * K_typed * ((T'_dyadic p).card : ℝ) := by
      calc (M : ℝ) ≤ D * (M_QTTC : ℝ) := h4
           _ ≤ D * (K_typed * ((T'_dyadic p).card : ℝ)) := by
             exact mul_le_mul_of_nonneg_left h1 (by positivity)
           _ = D * K_typed * ((T'_dyadic p).card : ℝ) := by ring
    have h6 : D * K_typed * ((T'_dyadic p).card : ℝ) ≤ D * K_typed * ((T'_affine p).card : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (by positivity)
    have h7 : D * K_typed * ((T'_affine p).card : ℝ) ≤ K * ((T'_affine p).card : ℝ) := by
      have hpos : 0 ≤ ((T'_affine p).card : ℝ) := by positivity
      have h8 : D * K_typed * ((T'_affine p).card : ℝ) =
          ((T'_affine p).card : ℝ) * (D * K_typed) := by ring
      have h9 : ((T'_affine p).card : ℝ) * K = K * ((T'_affine p).card : ℝ) := by ring
      rw [h8]
      have h10 : ((T'_affine p).card : ℝ) * (D * K_typed) ≤ ((T'_affine p).card : ℝ) * K :=
        mul_le_mul_of_nonneg_left hDK_le_K hpos
      rw [h9] at h10
      exact h10
    exact le_trans (le_trans h5 h6) h7

  exact ⟨P', T'_affine, C'_affine, K, C₂, H, hK_one', hK_bound', hC2_one', hH_pos,
    hP'_sub, hP_card', hT'_sub', hT'_size',
    hC'_sset_affine, hC'_delta_sset, hC2_bound',
    hC'_slope, hC'_v, hC'_b, hC'_near,
    h_exact_parent,
    h_pointFiber_inc, h_pointFiber_upper,
    h_avg_lower', h_avg_upper'⟩


end DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter
