import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleSubfamily
import MyLeanRepo.Kakeya.Cinematic.Targets.ComparableRectangles
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangle
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement.DoublingLemma
import MyLeanRepo.Kakeya.Cinematic.Targets.GeneralizedPacking
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialRectangleRefinement.DoublingCover
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialRectangleRefinement.NeighborPackingBound

/-!
# Final assembly for polynomial rectangle refinement

This module assembles the proof of `polynomial_rectangle_refinement` from:
1. `uniform_doubling` — curvature implies cinematic family
2. `comparable_rectangles_have_close_graphs` — geometry of comparable rectangles
3. `rectangle_subfamily_selection` — maximal incomparable subfamily
4. `polynomial_doubling_cover` — localized ball cover
5. `neighbor_packing_bound` — per-ball packing bound
6. `generalized_packing_bound` — packing in arbitrary containing interval

The key difference from `rectangle_refinement_part2` is that the center-distance
bound is `comparison * t` rather than `3 * t`, so we use a doubling cover to
reduce to balls of radius `3 * t`, then pack inside each ball.
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

/-- Polynomial rectangle refinement (PYZ Lemma 24, quantitative form). -/
theorem polynomial_rectangle_refinement_assembly :
    PolynomialRectangleRefinementStatement := by
  intro K hK
  classical
  -- Step 1: Get uniform doubling constant
  rcases uniform_doubling K hK with ⟨D, hD, hDouble⟩
  -- Step 2: Get ComparableRectangles constant
  let hCommon : CommonTangentRectangleStatement :=
    common_tangent_rectangle_controls_parameter
  let hComparable : ComparableRectanglesStatement :=
    comparable_rectangles_have_close_graphs hCommon
  rcases hComparable K D hK hD with ⟨C₁, hC₁_pos, hComp_prop_raw⟩
  -- Increase C₁ to at least 1
  let C₁' : ℝ := max C₁ 1
  have hC₁'_pos : 0 < C₁' := by positivity
  have hC₁'_one : 1 ≤ C₁' := le_max_right _ _
  have hC₁'_ge_C₁ : C₁ ≤ C₁' := le_max_left _ _
  -- Strengthened comparable-rectangles property with C₁'
  have hComp_prop_full : ∀ (family : Set C2Function), IsCinematicFamily family K D →
      ∀ I : ParameterInterval, I.IsControlled K →
      ∀ delta t lambda : ℝ, 0 < delta → delta ≤ t → 1 ≤ lambda →
      ∀ R S : CurvilinearRectangle delta t,
        R.function ∈ family → S.function ∈ family →
        R.IsOverCentralQuarterOf I → S.IsOverCentralQuarterOf I →
        R.AreLambdaComparable S family lambda →
        max R.interval.right S.interval.right -
          min R.interval.left S.interval.left ≤
          Real.sqrt (lambda * delta / t) ∧
        ∀ x ∈ R.intervalHullCarrier S,
          |R.function x - S.function x| ≤ C₁' * Real.rpow lambda 3 * delta := by
    intro family hCinematic I hI delta t lambda hdelta hdt hlam R S hRfam hSfam hRq hSq hcomp
    have h := hComp_prop_raw family hCinematic I hI delta t lambda hdelta hdt
      hlam R S hRfam hSfam hRq hSq hcomp
    have hlam_nonneg : 0 ≤ lambda := by linarith
    have hrpow_nonneg : 0 ≤ Real.rpow lambda 3 := Real.rpow_nonneg hlam_nonneg 3
    have h3 : C₁ * Real.rpow lambda 3 * delta ≤ C₁' * Real.rpow lambda 3 * delta := by
      have h31 : C₁ * Real.rpow lambda 3 ≤ C₁' * Real.rpow lambda 3 := by gcongr
      have h32 : 0 ≤ delta := by linarith
      exact mul_le_mul_of_nonneg_right h31 h32
    constructor
    · exact h.1
    · intro x hx
      have h4 : |R.function x - S.function x| ≤ C₁ * Real.rpow lambda 3 * delta := h.2 x hx
      linarith
  -- Choose the global polynomial exponent and constant (independent of comparison)
  let alpha : ℝ := Real.log D / Real.log 2
  have halpha_nonneg : 0 ≤ alpha := by
    have h1 : 0 ≤ Real.log D := Real.log_nonneg hD
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h1 h2.le
  let M0 : ℝ := 84 * D * (C₁' + 1)^2
  let e : ℝ := alpha + 13 / 2
  have he_nonneg : 0 ≤ e := by
    dsimp only [e]
    exact add_nonneg halpha_nonneg (by norm_num)
  let C : ℝ := max (e + 1) (M0 + 1)
  have hC_one : 1 ≤ C := by
    have h1 : 1 ≤ e + 1 := by linarith [he_nonneg]
    exact le_max_of_le_left h1
  have hC_ge_e : e ≤ C := by
    have h1 : e + 1 ≤ C := le_max_left _ _
    linarith
  have hC_ge_M0 : M0 + 1 ≤ C := le_max_right _ _
  refine' ⟨C, hC_one, _⟩
  intro comparison hcomparison family hCurv I hI delta t hdelta hdt hAdm center R hCenters hOver hIncomp hdist
  let hCinematic : IsCinematicFamily family K D := hDouble family hCurv
  have ht_pos : 0 < t := by linarith
  -- Specialize hComp_prop to this family/I/delta/t
  have hComp_spec : ∀ (lambda : ℝ), 1 ≤ lambda →
      ∀ (R S : CurvilinearRectangle delta t),
        R.function ∈ family → S.function ∈ family →
        R.IsOverCentralQuarterOf I → S.IsOverCentralQuarterOf I →
        R.AreLambdaComparable S family lambda →
        max R.interval.right S.interval.right - min R.interval.left S.interval.left ≤
          Real.sqrt (lambda * delta / t) ∧
        ∀ x ∈ R.intervalHullCarrier S,
          |R.function x - S.function x| ≤ C₁' * Real.rpow lambda 3 * delta := by
    intro lambda hlam R S hRfam hSfam hRq hSq hcomp
    exact hComp_prop_full family hCinematic I hI delta t lambda hdelta hdt hlam R S hRfam hSfam hRq hSq hcomp
  -- Comparison-dependent quantities
  let lambda_pack : ℝ := C₁' * comparison^3 + 1
  let pack_bound : ℝ := 42 * lambda_pack^2 * (2 * Real.sqrt comparison)
  let cover_bound : ℝ := D * Real.rpow (2 * comparison / 3) alpha
  let M : ℝ := cover_bound * pack_bound
  have hM_nonneg : 0 ≤ M := by
    dsimp only [M, cover_bound, pack_bound, lambda_pack]
    have h1 : 0 ≤ D := by linarith
    have h2 : 0 ≤ Real.rpow (2 * comparison / 3) alpha := Real.rpow_nonneg (by linarith) alpha
    have h3 : 0 ≤ 42 * (C₁' * comparison ^ 3 + 1) ^ 2 * (2 * Real.sqrt comparison) := by positivity
    positivity
  have hcomparison_pos : 0 < comparison := by linarith
  have hcomparison_one : 1 ≤ comparison := by linarith
  -- Step 3: Get maximal comparison-incomparable subfamily
  rcases rectangle_subfamily_selection delta t family comparison hcomparison R hCenters with
    ⟨S, hSCenters, hSIncomp, hCover⟩
  -- Define neighbor sets
  let N (j : Fin S.card) : Finset (Fin R.card) :=
    Finset.univ.filter fun i : Fin R.card =>
      (R.rectangle i).AreLambdaComparable (S.family.rectangle j) family comparison
  -- Step 4: Bound neighbors of each S_j
  have h_neighbor_bound : ∀ (j : Fin S.card), (N j).card ≤ M := by
    intro j
    let S_j : CurvilinearRectangle delta t := S.family.rectangle j
    let N_j : Finset (Fin R.card) := N j
    have hS_j_family : S_j.function ∈ family := hSCenters j
    have hS_j_over : S_j.IsOverCentralQuarterOf I := hOver (S.embedding j)
    -- All neighbors are within comparison * t of center, and S_j is too,
    -- so they are within 2 * comparison * t of S_j.function
    have h_neighbor_dist : ∀ i ∈ N_j,
        c2Distance S_j.function (R.rectangle i).function ≤ 2 * comparison * t := by
      intro i hi
      have h1 : c2Distance center (R.rectangle i).function ≤ comparison * t := hdist i
      have h2 : c2Distance center S_j.function ≤ comparison * t := hdist (S.embedding j)
      have h3 : c2Distance S_j.function (R.rectangle i).function ≤
          c2Distance S_j.function center + c2Distance center (R.rectangle i).function := by
        simp only [c2Distance_eq_dist]
        exact dist_triangle _ _ _
      have h4 : c2Distance S_j.function center = c2Distance center S_j.function := by
        simp [c2Distance_eq_dist, dist_comm]
      rw [h4] at h3
      linarith
    -- Step 4a: Localized doubling cover
    set R_cover : ℝ := 2 * comparison * t with hR_cover_def
    set r_cover : ℝ := 3 * t with hr_cover_def
    have hR_cover_pos : 0 < R_cover := by
      dsimp only [R_cover]; positivity
    have hr_cover_pos : 0 < r_cover := by linarith
    have hrR : r_cover ≤ R_cover := by
      dsimp only [r_cover, R_cover]
      have h : 3 * t ≤ 2 * comparison * t := by
        have h2 : 3 ≤ 2 * comparison := by linarith [hcomparison]
        gcongr
      exact h
    rcases polynomial_doubling_cover hCinematic hD S_j.function hS_j_family
        R_cover r_cover hR_cover_pos hr_cover_pos hrR with
      ⟨centers, hcenters_sub, hcenters_card, hcenters_cover⟩
    -- Step 4b: For each center, construct RectangleFamily and apply packing bound
    let N_jh (h : C2Function) : Finset (Fin R.card) :=
      N_j.filter (fun i => c2Distance h (R.rectangle i).function ≤ 3 * t)
    have h_per_ball : ∀ (h : C2Function), h ∈ centers →
        (N_jh h).card ≤ pack_bound := by
      intro h hh
      have hh_family : h ∈ family := hcenters_sub hh
      -- Construct RectangleFamily from N_jh
      let e : Fin (N_jh h).card ↪ Fin R.card :=
        (Finset.orderEmbOfFin (N_jh h) rfl).toEmbedding
      let neighbors : RectangleFamily delta t :=
        { card := (N_jh h).card
          rectangle := fun k => R.rectangle (e k) }
      have h_neighbors_centers : neighbors.CentersIn family := by
        intro k; exact hCenters (e k)
      have h_neighbors_over : neighbors.IsOverCentralQuarterOf I := by
        intro k; exact hOver (e k)
      have h_neighbors_incomp : neighbors.IsPairwiseIncomparable family 100 := by
        intro k l hne
        exact hIncomp (e k) (e l) (e.inj'.ne hne)
      have h_neighbors_dist : ∀ k, c2Distance h (neighbors.rectangle k).function ≤ 3 * t := by
        intro k
        have h5 : e k ∈ N_jh h := Finset.orderEmbOfFin_mem (N_jh h) rfl k
        exact (Finset.mem_filter.mp h5).2
      have h_neighbors_comparable : ∀ k,
          (neighbors.rectangle k).AreLambdaComparable S_j family comparison := by
        intro k
        have h5 : e k ∈ N_jh h := Finset.orderEmbOfFin_mem (N_jh h) rfl k
        have h6 : e k ∈ N_j := (Finset.mem_filter.mp h5).1
        simpa [N_j, N, Finset.mem_filter, Finset.mem_univ] using h6
      have h_pack := neighbor_packing_bound
          hK hI hdelta hdt hcomparison hC₁'_one hComp_spec
          hS_j_family hS_j_over
          (center := h) (neighbors := neighbors)
          h_neighbors_centers h_neighbors_over h_neighbors_incomp
          h_neighbors_dist h_neighbors_comparable
      simpa [pack_bound, lambda_pack] using h_pack
    -- Every neighbor is covered by some ball center
    have h_covered : ∀ i ∈ N_j,
        ∃ h ∈ centers, c2Distance h (R.rectangle i).function ≤ 3 * t := by
      intro i hi
      have h_i_family : (R.rectangle i).function ∈ family := hCenters i
      have h_i_dist : c2Distance S_j.function (R.rectangle i).function ≤ R_cover :=
        h_neighbor_dist i hi
      rcases hcenters_cover (R.rectangle i).function h_i_family h_i_dist with
        ⟨h, hh, hdist⟩
      exact ⟨h, hh, hdist⟩
    -- N_j is covered by the union of N_jh over h ∈ centers
    have h_union_cover : N_j ⊆ Finset.biUnion centers N_jh := by
      intro i hi
      rcases h_covered i hi with ⟨h, hh, hdist⟩
      have h_i_in_Njh : i ∈ N_jh h := by
        simp only [N_jh, Finset.mem_filter]
        exact ⟨hi, hdist⟩
      exact Finset.mem_biUnion.mpr ⟨h, hh, h_i_in_Njh⟩
    -- Sum the bounds
    have h_card : (N_j.card : ℝ) ≤
        ∑ h ∈ centers, ((N_jh h).card : ℝ) := by
      have h1 : N_j.card ≤ (Finset.biUnion centers N_jh).card :=
        Finset.card_le_card h_union_cover
      have h2 : (Finset.biUnion centers N_jh).card ≤
          ∑ h ∈ centers, (N_jh h).card := Finset.card_biUnion_le
      exact_mod_cast (h1.trans h2)
    have h_sum : ∑ h ∈ centers, ((N_jh h).card : ℝ) ≤
        (centers.card : ℝ) * pack_bound := by
      have h3 : ∀ h ∈ centers, ((N_jh h).card : ℝ) ≤ pack_bound := by
        intro h hh
        exact h_per_ball h hh
      calc
        ∑ h ∈ centers, ((N_jh h).card : ℝ)
          ≤ ∑ h ∈ centers, pack_bound := Finset.sum_le_sum h3
        _ = (centers.card : ℝ) * pack_bound := by
          simp [Finset.sum_const]
    have h_centers_bound : (centers.card : ℝ) ≤ cover_bound := by
      have h1 : (centers.card : ℝ) ≤
          D * Real.rpow (R_cover / r_cover) alpha := hcenters_card
      have h2 : R_cover / r_cover = 2 * comparison / 3 := by
        simp [hR_cover_def, hr_cover_def]
        field_simp [ht_pos.ne'] <;> ring
      rw [h2] at h1
      exact h1
    calc
      (N_j.card : ℝ)
        ≤ ∑ h ∈ centers, ((N_jh h).card : ℝ) := h_card
      _ ≤ (centers.card : ℝ) * pack_bound := h_sum
      _ ≤ cover_bound * pack_bound := by gcongr
      _ = M := by rfl
  -- Step 5: Counting argument
  let S_set : Finset (Fin R.card) := Finset.image S.embedding Finset.univ
  have hS_card : S_set.card = S.card := by
    dsimp only [S_set]
    have h : (Finset.image S.embedding (Finset.univ : Finset (Fin S.card))).card =
        (Finset.univ : Finset (Fin S.card)).card := by
      apply Finset.card_image_of_injOn
      intro x _ y _ hxy
      exact S.embedding.inj' hxy
    rw [h] <;> simp
  let Filtered : Finset (Fin R.card) :=
    Finset.univ.filter fun i : Fin R.card =>
      ∃ (j : Fin S.card), (R.rectangle i).AreLambdaComparable
        (S.family.rectangle j) family comparison
  have h_cover : ∀ (i : Fin R.card), i ∈ S_set ∨ i ∈ Filtered := by
    intro i
    rcases hCover i with ⟨j, h | h⟩
    · exact Or.inl (by
        simp only [S_set, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨j, by simpa using h.symm⟩)
    · exact Or.inr (by
        simp only [Filtered, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨j, h⟩)
  have h_filtered_sub : Filtered ⊆ Finset.biUnion Finset.univ N := by
    intro i hi
    have h_exists : ∃ (j : Fin S.card),
        (R.rectangle i).AreLambdaComparable (S.family.rectangle j) family comparison :=
      (Finset.mem_filter.mp hi).2
    rcases h_exists with ⟨j, hj⟩
    have h_in_N_j : i ∈ N j := by
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, h_in_N_j⟩
  have h_card_filtered : (Filtered.card : ℝ) ≤ (S.card : ℝ) * M := by
    calc
      (Filtered.card : ℝ)
        ≤ ((Finset.biUnion Finset.univ N).card : ℝ) := by
          exact_mod_cast Finset.card_le_card h_filtered_sub
      _ ≤ ∑ j : Fin S.card, ((N j).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j : Fin S.card, M := by
          apply Finset.sum_le_sum
          intro j _
          exact h_neighbor_bound j
      _ = (S.card : ℝ) * M := by
          simp [Finset.sum_const]
  have h_count : (R.card : ℝ) ≤ (S.card : ℝ) * (1 + M) := by
    have h1 : (Finset.univ : Finset (Fin R.card)).card ≤
        (S_set ∪ Filtered).card := by
      apply Finset.card_le_card
      intro i _
      exact (h_cover i).elim (Finset.mem_union_left _) (Finset.mem_union_right _)
    have h2 : ((S_set ∪ Filtered).card : ℝ) ≤
        (S_set.card : ℝ) + (Filtered.card : ℝ) := by
      exact_mod_cast Finset.card_union_le _ _
    have h3 : (S_set.card : ℝ) = (S.card : ℝ) := by
      exact_mod_cast hS_card
    have h4 : (R.card : ℝ) = ((Finset.univ : Finset (Fin R.card)).card : ℝ) := by simp
    rw [h4]
    calc
      ((Finset.univ : Finset (Fin R.card)).card : ℝ)
        ≤ ((S_set ∪ Filtered).card : ℝ) := by exact_mod_cast h1
      _ ≤ (S_set.card : ℝ) + (Filtered.card : ℝ) := h2
      _ = (S.card : ℝ) + (Filtered.card : ℝ) := by rw [h3]
      _ ≤ (S.card : ℝ) + (S.card : ℝ) * M := by gcongr
      _ = (S.card : ℝ) * (1 + M) := by ring
  -- Step 6: Polynomial algebra
  -- cover_bound = D * (2*comparison/3)^alpha ≤ D * comparison^alpha
  -- pack_bound ≤ 42 * (C₁'+1)^2 * comparison^6 * 2 * comparison^(1/2)
  -- M ≤ 84 * D * (C₁'+1)^2 * comparison^(alpha + 13/2) = M0 * comparison^e
  have h1 : 2 * comparison / 3 ≤ comparison := by
    have h2 : 2 * comparison ≤ 3 * comparison := by linarith
    have h3 : 2 * comparison / 3 ≤ comparison := by
      calc
        2 * comparison / 3 ≤ 3 * comparison / 3 := by gcongr
        _ = comparison := by ring
    exact h3
  have h3 : C₁' * comparison^3 + 1 ≤ (C₁' + 1) * comparison^3 := by
    have h4 : 1 ≤ comparison^3 := by
      have h5 : 1 ≤ comparison := by linarith
      have h6 : (1 : ℝ) ≤ comparison^3 := by
        calc (1 : ℝ) ≤ comparison^1 := by linarith
             _ ≤ comparison^3 := by gcongr <;> linarith
      exact h6
    have h7 : C₁' * comparison^3 + 1 ≤ C₁' * comparison^3 + comparison^3 := by gcongr
    have h8 : C₁' * comparison^3 + comparison^3 = (C₁' + 1) * comparison^3 := by ring
    linarith
  have hsqrt : Real.sqrt comparison = comparison ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have hcover : cover_bound ≤ D * Real.rpow comparison alpha := by
    dsimp only [cover_bound]
    have h5 : 2 * comparison / 3 ≤ comparison := h1
    have h6 : Real.rpow (2 * comparison / 3) alpha ≤ Real.rpow comparison alpha :=
      Real.rpow_le_rpow (by linarith) h5 halpha_nonneg
    have hD_nonneg : 0 ≤ D := by linarith
    exact mul_le_mul_of_nonneg_left h6 hD_nonneg
  have hpack : pack_bound ≤
      42 * ((C₁' + 1) * comparison^3)^2 * (2 * comparison ^ (1 / 2 : ℝ)) := by
    dsimp only [pack_bound, lambda_pack]
    have h5 : C₁' * comparison^3 + 1 ≤ (C₁' + 1) * comparison^3 := h3
    have h6 : (C₁' * comparison^3 + 1)^2 ≤ ((C₁' + 1) * comparison^3)^2 := by gcongr
    have h7 : Real.sqrt comparison = comparison ^ (1 / 2 : ℝ) := hsqrt
    rw [h7]
    gcongr
  have h12 : comparison^6 * comparison^(1 / 2 : ℝ) = comparison^(13 / 2 : ℝ) := by
    have h13 : comparison^6 = comparison^(6 : ℝ) := by simp
    rw [h13]
    rw [←Real.rpow_add (by linarith)] <;> norm_num
  have hM : M ≤ M0 * Real.rpow comparison e := by
    dsimp only [M, M0, e]
    have hD_nonneg' : 0 ≤ D := by linarith
    have hrp_nonneg : 0 ≤ Real.rpow comparison alpha := Real.rpow_nonneg (by linarith) alpha
    have h_pos1 : 0 ≤ D * Real.rpow comparison alpha := mul_nonneg hD_nonneg' hrp_nonneg
    have h_pos2 : 0 ≤ pack_bound := by
      dsimp only [pack_bound, lambda_pack]
      positivity
    have h_step1 : cover_bound * pack_bound ≤
        (D * Real.rpow comparison alpha) *
          (42 * ((C₁' + 1) * comparison^3)^2 * (2 * comparison ^ (1 / 2 : ℝ))) :=
      mul_le_mul hcover hpack h_pos2 h_pos1
    have h9 : ((C₁' + 1) * comparison^3)^2 = (C₁' + 1)^2 * comparison^6 := by ring
    have h_half : (6 : ℝ) + (1 / 2 : ℝ) = (13 / 2 : ℝ) := by norm_num
    have h12 : comparison^6 * comparison^(1 / 2 : ℝ) = comparison^(13 / 2 : ℝ) := by
      have h13 : comparison^6 = comparison^(6 : ℝ) := by simp
      rw [h13]
      have h14 : comparison^(6 : ℝ) * comparison^(1 / 2 : ℝ) =
          comparison^((6 : ℝ) + (1 / 2 : ℝ)) := by
        rw [←Real.rpow_add (by linarith)]
      rw [h14, h_half]
    have h11 : Real.rpow comparison alpha * comparison^(13 / 2 : ℝ) =
        Real.rpow comparison (alpha + (13 / 2 : ℝ)) := by
      have h111 : comparison^(13 / 2 : ℝ) = Real.rpow comparison (13 / 2 : ℝ) := by rfl
      rw [h111]
      have hcomp_pos : 0 < comparison := by linarith [hcomparison]
      have h112 : Real.rpow comparison alpha * Real.rpow comparison (13 / 2 : ℝ) =
          Real.rpow comparison (alpha + (13 / 2 : ℝ)) := by
        exact (Real.rpow_add hcomp_pos alpha (13 / 2 : ℝ)).symm
      exact h112
    calc
      cover_bound * pack_bound
        ≤ (D * Real.rpow comparison alpha) *
              (42 * ((C₁' + 1) * comparison^3)^2 * (2 * comparison ^ (1 / 2 : ℝ))) := h_step1
      _ = 84 * D * (C₁' + 1)^2 * (Real.rpow comparison alpha * (comparison^6 * comparison^(1 / 2 : ℝ))) := by
            rw [h9] <;> ring
      _ = 84 * D * (C₁' + 1)^2 * (Real.rpow comparison alpha * comparison^(13 / 2 : ℝ)) := by
            rw [h12]
      _ = 84 * D * (C₁' + 1)^2 * Real.rpow comparison (alpha + (13 / 2 : ℝ)) := by
            rw [h11] <;> ring
      _ = M0 * Real.rpow comparison e := by
            dsimp only [M0, e] <;> ring
  have h_final : 1 + M ≤ C * Real.rpow comparison C := by
    have h9 : M ≤ M0 * Real.rpow comparison e := hM
    have h10 : 1 + M ≤ 1 + M0 * Real.rpow comparison e := by linarith
    have h11 : Real.rpow comparison e ≥ 1 := by
      have h12 : 1 ≤ comparison := by linarith
      exact Real.one_le_rpow h12 he_nonneg
    have h14 : 1 + M0 * Real.rpow comparison e ≤ (M0 + 1) * Real.rpow comparison e := by
      have h15 : 1 ≤ Real.rpow comparison e := h11
      have h16 : 1 + M0 * Real.rpow comparison e ≤
          Real.rpow comparison e + M0 * Real.rpow comparison e := by gcongr
      have h17 : Real.rpow comparison e + M0 * Real.rpow comparison e =
          (M0 + 1) * Real.rpow comparison e := by ring
      linarith
    have h18 : (M0 + 1) * Real.rpow comparison e ≤ C * Real.rpow comparison e := by
      have h19 : M0 + 1 ≤ C := hC_ge_M0
      have h20 : 0 ≤ Real.rpow comparison e := by positivity
      gcongr
    have h21 : C * Real.rpow comparison e ≤ C * Real.rpow comparison C := by
      have h22 : e ≤ C := hC_ge_e
      have h23 : Real.rpow comparison e ≤ Real.rpow comparison C :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) h22
      have h24 : 0 ≤ C := by linarith
      gcongr
    calc
      1 + M ≤ 1 + M0 * Real.rpow comparison e := h10
      _ ≤ (M0 + 1) * Real.rpow comparison e := h14
      _ ≤ C * Real.rpow comparison e := h18
      _ ≤ C * Real.rpow comparison C := h21
  have h_main : (R.card : ℝ) ≤ C * Real.rpow comparison C * (S.card : ℝ) := by
    have h26 : (R.card : ℝ) ≤ (S.card : ℝ) * (1 + M) := h_count
    have h27 : (S.card : ℝ) * (1 + M) ≤
        (S.card : ℝ) * (C * Real.rpow comparison C) := by
      have h28 : 0 ≤ (S.card : ℝ) := by positivity
      gcongr
    have h29 : (S.card : ℝ) * (C * Real.rpow comparison C) =
        C * Real.rpow comparison C * (S.card : ℝ) := by ring
    rw [h29] at h27
    exact h26.trans h27
  exact ⟨S, hSIncomp, h_main⟩

end Kakeya.Cinematic
