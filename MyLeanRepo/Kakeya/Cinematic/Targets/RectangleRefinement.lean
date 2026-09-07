import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement.ShrinkingPreservesIncomparability
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement.DoublingLemma
import MyLeanRepo.Kakeya.Cinematic.Targets.GeneralizedPacking

/-!
# PYZ rectangle refinement

This module assembles the proof of `rectangle_refinement` (PYZ Lemmas 22 and 24)
from three components:
1. `shrinking_preserves_incomparability` — Lemma 22
2. `uniform_doubling` — curvature implies cinematic family
3. `generalized_packing_bound` — packing in arbitrary containing interval
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

/-- Part 2: large incomparable refinement (PYZ Lemma 24). -/
theorem rectangle_refinement_part2
    (_hPacking : RectanglePackingStatement)
    (hSubfamily : RectangleSubfamilySelectionStatement)
    (hComparable : ComparableRectanglesStatement) :
    ∀ K : ℝ, 1 ≤ K →
      ∀ C : ℝ, 100 ≤ C →
        ∃ retention : ℝ, 0 < retention ∧ retention ≤ 1 ∧
          ∀ family : Set C2Function,
            HasCinematicCurvature family K →
            ∀ I : ParameterInterval, I.IsControlled K →
              ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
                IsAdmissibleComparisonScale delta t C →
                ∀ center : C2Function,
                  ∀ R : RectangleFamily delta t,
                    R.CentersIn family →
                    R.IsOverCentralQuarterOf I →
                    R.IsPairwiseIncomparable family 100 →
                    (∀ i, c2Distance center (R.rectangle i).function ≤ 3 * t) →
                      ∃ S : RectangleSubfamily R,
                        S.family.IsPairwiseIncomparable family C ∧
                        retention * (R.card : ℝ) ≤ (S.card : ℝ) := by
  intro K hK C hC
  classical
  -- Step 1: Get uniform doubling constant
  rcases uniform_doubling K hK with ⟨D, hD, hDouble⟩
  -- Step 2: Get ComparableRectangles constant
  rcases hComparable K D hK hD with ⟨C₁, hC₁_pos, hComp_prop⟩
  -- Increase C₁ to at least 1
  let C₁' : ℝ := max C₁ 1
  have hC₁'_pos : 0 < C₁' := by positivity
  have hC₁'_one : 1 ≤ C₁' := le_max_right _ _
  have hComp_prop' : ∀ (family : Set C2Function), IsCinematicFamily family K D →
      ∀ I : ParameterInterval, I.IsControlled K →
      ∀ delta t lambda : ℝ, 0 < delta → delta ≤ t → t ≤ 1 → 1 ≤ lambda →
      ∀ R S : CurvilinearRectangle delta t,
        R.function ∈ family → S.function ∈ family →
        R.IsOverCentralQuarterOf I → S.IsOverCentralQuarterOf I →
        R.AreLambdaComparable S family lambda →
        max R.interval.right S.interval.right - min R.interval.left S.interval.left ≤
          Real.sqrt (lambda * delta / t) ∧
        ∀ x ∈ R.intervalHullCarrier S,
          |R.function x - S.function x| ≤ C₁' * Real.rpow lambda 3 * delta := by
    intro family hCinematic I hI delta t lambda hdelta hdt ht hlam R S hRfam hSfam hRq hSq hcomp
    have h := hComp_prop family hCinematic I hI delta t lambda hdelta hdt hlam
      R S hRfam hSfam hRq hSq hcomp
    have h1 : C₁ ≤ C₁' := le_max_left _ _
    have hlam_nonneg : 0 ≤ lambda := by linarith
    have hrpow_nonneg : 0 ≤ Real.rpow lambda 3 := Real.rpow_nonneg hlam_nonneg 3
    have h3 : C₁ * Real.rpow lambda 3 * delta ≤ C₁' * Real.rpow lambda 3 * delta := by
      have h31 : C₁ * Real.rpow lambda 3 ≤ C₁' * Real.rpow lambda 3 := by gcongr
      have h32 : 0 ≤ delta := by linarith
      exact mul_le_mul_of_nonneg_right h31 h32
    constructor
    · exact h.1
    · intro x hx
      have h2 : |R.function x - S.function x| ≤ C₁ * Real.rpow lambda 3 * delta := h.2 x hx
      linarith
  let B : ℝ := C₁' * C^3
  have hB_pos : 0 < B := by positivity
  let lambda : ℝ := B + 1
  have hlambda_100 : 100 ≤ lambda := by
    have h1 : 0 < C₁' := hC₁'_pos
    have h2 : C^3 ≥ 100^3 := by gcongr
    nlinarith
  set M : ℝ := 42 * lambda^2 * (2 * Real.sqrt C) with hM_def
  have hM_pos : 0 < M := by positivity
  let retention : ℝ := 1 / (1 + M)
  have hret_pos : 0 < retention := by positivity
  have hret_le_one : retention ≤ 1 := by
    have h : 0 < 1 + M := by positivity
    exact (div_le_one (by positivity)).mpr (by linarith)
  use retention
  constructor
  · exact hret_pos
  constructor
  · exact hret_le_one
  intro family hCurv
  let hCinematic : IsCinematicFamily family K D := hDouble family hCurv
  intro I hI delta t hdelta hdt ht _hAdm center R hCenters hOver hIncomp hdist
  -- Step 3: Get maximal C-incomparable subfamily
  rcases hSubfamily delta t family C hC R hCenters with ⟨S, hSCenters, hSIncomp, hCover⟩
  -- Define neighbor sets
  let N (j : Fin S.card) : Finset (Fin R.card) :=
    Finset.univ.filter fun i : Fin R.card =>
      (R.rectangle i).AreLambdaComparable (S.family.rectangle j) family C
  -- Step 4: Bound neighbors of each S_j
  have h_neighbor_bound : ∀ (j : Fin S.card), (N j).card ≤ M := by
    intro j
    let S_j : CurvilinearRectangle delta t := S.family.rectangle j
    let N_j : Finset (Fin R.card) := N j
    let L : ℝ := Real.sqrt (delta / t)
    have hL_pos : 0 < L := Real.sqrt_pos.mpr (div_pos hdelta (by linarith))
    let d : ℝ := (Real.sqrt C - 1) * L
    have hd_nonneg : 0 ≤ d := by
      have h1 : 1 ≤ Real.sqrt C := by
        have h2 : (1 : ℝ)^2 ≤ C := by norm_num; linarith
        exact Real.le_sqrt_of_sq_le h2
      have h3 : 0 ≤ Real.sqrt C - 1 := by linarith
      positivity
    -- Hull bounds from hComparable
    have h_hull_left : ∀ i ∈ N_j, S_j.interval.left - d ≤
        (R.rectangle i).interval.left := by
      intro i hi
      have hcomp : (R.rectangle i).AreLambdaComparable S_j family C := by
        simpa [N_j, N, Finset.mem_filter] using hi
      have h_main := (hComp_prop' family hCinematic I hI delta t C hdelta hdt ht (by linarith)
        (R.rectangle i) S_j
        (hCenters i) (hSCenters j) (hOver i) (hOver (S.embedding j)) hcomp).1
      have h2 : Real.sqrt (C * delta / t) = Real.sqrt C * L := by
        rw [show C * delta / t = C * (delta / t) by ring]
        rw [Real.sqrt_mul (by linarith)]
      rw [h2] at h_main
      have hSlen : S_j.interval.right - S_j.interval.left = L := by
        simpa [ParameterInterval.length] using S_j.interval_length
      by_cases h : (R.rectangle i).interval.left ≤ S_j.interval.left
      · have h3 : min (R.rectangle i).interval.left S_j.interval.left =
            (R.rectangle i).interval.left := by
          rw [min_eq_left]; exact h
        rw [h3] at h_main
        have h4 : max (R.rectangle i).interval.right S_j.interval.right ≥ S_j.interval.right :=
          le_max_right _ _
        linarith
      · have h3 : S_j.interval.left < (R.rectangle i).interval.left := by linarith
        linarith
    have h_hull_right : ∀ i ∈ N_j,
        (R.rectangle i).interval.right ≤ S_j.interval.right + d := by
      intro i hi
      have hcomp : (R.rectangle i).AreLambdaComparable S_j family C := by
        simpa [N_j, N, Finset.mem_filter] using hi
      have h_main := (hComp_prop' family hCinematic I hI delta t C hdelta hdt ht (by linarith)
        (R.rectangle i) S_j
        (hCenters i) (hSCenters j) (hOver i) (hOver (S.embedding j)) hcomp).1
      have h2 : Real.sqrt (C * delta / t) = Real.sqrt C * L := by
        rw [show C * delta / t = C * (delta / t) by ring]
        rw [Real.sqrt_mul (by linarith)]
      rw [h2] at h_main
      have hSlen : S_j.interval.right - S_j.interval.left = L := by
        simpa [ParameterInterval.length] using S_j.interval_length
      by_cases h : S_j.interval.right ≤ (R.rectangle i).interval.right
      · have h3 : max (R.rectangle i).interval.right S_j.interval.right =
            (R.rectangle i).interval.right := by
          rw [max_eq_left]; exact h
        rw [h3] at h_main
        have h4 : min (R.rectangle i).interval.left S_j.interval.left ≤ S_j.interval.left :=
          min_le_right _ _
        linarith
      · linarith
    -- Construct J explicitly
    let Jleft : ℝ := max 0 (S_j.interval.left - d)
    let Jright : ℝ := min 1 (S_j.interval.right + d)
    have hJleft_mem : Jleft ∈ Set.Icc (0 : ℝ) 1 := by
      have h1 : 0 ≤ Jleft := le_max_left _ _
      have h2 : Jleft ≤ S_j.interval.left := by
        exact max_le (by linarith [S_j.interval.left_mem.1]) (by linarith)
      have h3 : S_j.interval.left ≤ 1 := S_j.interval.left_mem.2
      exact ⟨h1, by linarith⟩
    have hJright_mem : Jright ∈ Set.Icc (0 : ℝ) 1 := by
      have h1 : Jright ≤ 1 := by
        dsimp only [Jright]
        have h : min (1 : ℝ) (S_j.interval.right + d) ≤ (1 : ℝ) :=
          min_le_left _ _
        exact h
      have h2 : S_j.interval.right ≤ Jright := by
        exact le_min (by linarith [S_j.interval.right_mem.2]) (by linarith)
      have h3 : 0 ≤ S_j.interval.right := S_j.interval.right_mem.1
      exact ⟨by linarith, h1⟩
    have hJleft_le_right : Jleft ≤ Jright := by
      have h1 : Jleft ≤ S_j.interval.left := by
        exact max_le (by linarith [S_j.interval.left_mem.1]) (by linarith)
      have h2 : S_j.interval.left ≤ S_j.interval.right := S_j.interval.left_le_right
      have h3 : S_j.interval.right ≤ Jright := by
        exact le_min (by linarith [S_j.interval.right_mem.2]) (by linarith)
      linarith
    let J : ParameterInterval :=
      { left := Jleft
        right := Jright
        left_mem := hJleft_mem
        right_mem := hJright_mem
        left_le_right := hJleft_le_right }
    have hJ_len : J.length ≤ 2 * Real.sqrt C * L := by
      have h1 : Jleft ≥ S_j.interval.left - d := le_max_of_le_right (by linarith)
      have h2 : Jright ≤ S_j.interval.right + d := by
        dsimp only [Jright]
        have h : min (1 : ℝ) (S_j.interval.right + d) ≤ S_j.interval.right + d :=
          min_le_right _ _
        exact h
      have hSlen : S_j.interval.right - S_j.interval.left = L := by
        simpa [ParameterInterval.length] using S_j.interval_length
      simp only [ParameterInterval.length]
      linarith
    have hJ_contains : ∀ i ∈ N_j, (R.rectangle i).interval.carrier ⊆ J.carrier := by
      intro i hi x hx
      have h_left1 : S_j.interval.left - d ≤ (R.rectangle i).interval.left := h_hull_left i hi
      have h_left2 : 0 ≤ (R.rectangle i).interval.left := (R.rectangle i).interval.left_mem.1
      have h_gi : Jleft ≤ (R.rectangle i).interval.left := by
        simp only [Jleft]
        exact max_le_iff.mpr ⟨by linarith, h_hull_left i hi⟩
      have h_right1 : (R.rectangle i).interval.right ≤ S_j.interval.right + d := h_hull_right i hi
      have h_right2 : (R.rectangle i).interval.right ≤ 1 := (R.rectangle i).interval.right_mem.2
      have h_le : (R.rectangle i).interval.right ≤ Jright := by
        simp only [Jright]
        exact le_min (by linarith) (by linarith)
      have h_x_left : Jleft ≤ (x : ℝ) := by linarith [hx.1]
      have h_x_right : (x : ℝ) ≤ Jright := by linarith [hx.2]
      exact ⟨h_x_left, h_x_right⟩
    -- Value bound from hComparable
    have h_val_bound : ∀ i ∈ N_j, ∀ x ∈ (R.rectangle i).interval.carrier,
        |(R.rectangle i).function x - S_j.function x| ≤ B * delta := by
      intro i hi x hx
      have hcomp : (R.rectangle i).AreLambdaComparable S_j family C := by
        simpa [N_j, N, Finset.mem_filter] using hi
      have h_main := (hComp_prop' family hCinematic I hI delta t C hdelta hdt ht (by linarith)
        (R.rectangle i) S_j
          (hCenters i) (hSCenters j) (hOver i) (hOver (S.embedding j)) hcomp).2
      have h_x_in_hull : x ∈ (R.rectangle i).intervalHullCarrier S_j := by
        simp only [CurvilinearRectangle.intervalHullCarrier]
        constructor
        · exact le_trans (min_le_left _ _) hx.1
        · exact le_trans hx.2 (le_max_left _ _)
      have h4 : |(R.rectangle i).function x - S_j.function x| ≤
          C₁' * Real.rpow C 3 * delta := h_main x h_x_in_hull
      have h5 : Real.rpow C 3 = C^3 := by simp
      rw [h5] at h4
      simpa [B] using h4
    -- Carrier containment
    have h_carrier : ∀ i ∈ N_j,
        (R.rectangle i).carrier ⊆ verticalNeighborhoodOn S_j.function (lambda * delta) J := by
      intro i hi p hp
      have h1 : p.1 ∈ (R.rectangle i).interval.carrier := hp.1
      have h2 : |p.2 - (R.rectangle i).function p.1| ≤ delta := hp.2
      have h3 : p.1 ∈ J.carrier := hJ_contains i hi h1
      have h4 : |(R.rectangle i).function p.1 - S_j.function p.1| ≤ B * delta :=
        h_val_bound i hi p.1 h1
      have h5 : |p.2 - S_j.function p.1| ≤
          |p.2 - (R.rectangle i).function p.1| +
          |(R.rectangle i).function p.1 - S_j.function p.1| := by
        exact abs_sub_le _ _ _
      have h6 : |p.2 - S_j.function p.1| ≤ lambda * delta := by
        have h7 : |p.2 - S_j.function p.1| ≤ delta + B * delta := by
          calc
            |p.2 - S_j.function p.1|
              ≤ |p.2 - (R.rectangle i).function p.1| + |(R.rectangle i).function p.1 - S_j.function p.1| := h5
            _ ≤ delta + B * delta := by linarith
        have h8 : delta + B * delta = lambda * delta := by
          simp only [lambda, B]; ring
        rw [h8] at h7
        exact h7
      exact ⟨h3, h6⟩
    -- Construct neighbor RectangleFamily
    let e : Fin N_j.card ↪ Fin R.card :=
      (Finset.orderEmbOfFin N_j rfl).toEmbedding
    let N_j_family : RectangleFamily delta t :=
      { card := N_j.card
        rectangle := fun k => R.rectangle (e k) }
    have hN_centers : N_j_family.CentersIn family := by
      intro k; exact hCenters (e k)
    have hN_over : N_j_family.IsOverCentralQuarterOf I := by
      intro k; exact hOver (e k)
    have hN_incomp : N_j_family.IsPairwiseIncomparable family 100 := by
      intro k l hne
      exact hIncomp (e k) (e l) (e.inj'.ne hne)
    have hN_dist : ∀ k, c2Distance center (N_j_family.rectangle k).function ≤ 3 * t := by
      intro k; exact hdist (e k)
    have hN_J : ∀ k, (N_j_family.rectangle k).interval.carrier ⊆ J.carrier := by
      intro k; exact hJ_contains (e k) (Finset.orderEmbOfFin_mem N_j rfl k)
    have hN_carrier : ∀ k,
        (N_j_family.rectangle k).carrier ⊆
          verticalNeighborhoodOn S_j.function (lambda * delta) J := by
      intro k; exact h_carrier (e k) (Finset.orderEmbOfFin_mem N_j rfl k)
    -- Apply generalized packing bound
    have h_pack : (N_j_family.card : ℝ) ≤
        42 * lambda^2 * J.length / Real.sqrt (delta / t) :=
      generalized_packing_bound hK hI.2 hdelta hdt hlambda_100
        hN_centers hN_over hN_incomp hN_dist
        (J := J) (g := S_j.function) hN_carrier
    have h_final : (N_j.card : ℝ) ≤ M := by
      have h1 : (N_j_family.card : ℝ) = (N_j.card : ℝ) := by rfl
      rw [h1] at h_pack
      have h2 : J.length ≤ 2 * Real.sqrt C * L := hJ_len
      have h3 : 0 < L := hL_pos
      calc
        (N_j.card : ℝ)
          ≤ 42 * lambda^2 * J.length / L := h_pack
        _ ≤ 42 * lambda^2 * (2 * Real.sqrt C * L) / L := by gcongr
        _ = 42 * lambda^2 * (2 * Real.sqrt C) := by
          field_simp [h3.ne']
        _ = M := by simp only [M]
    exact h_final
  -- Step 5: Counting
  let S_set : Finset (Fin R.card) := Finset.image S.embedding Finset.univ
  have hS_card : S_set.card = S.card := by
    dsimp only [S_set]
    have h : (Finset.image S.embedding (Finset.univ : Finset (Fin S.card))).card = (Finset.univ : Finset (Fin S.card)).card := by
      apply Finset.card_image_of_injOn
      intro x _ y _ hxy
      exact S.embedding.inj' hxy
    rw [h]
    ; simp
  let Filtered : Finset (Fin R.card) :=
    Finset.univ.filter fun i : Fin R.card =>
      ∃ (j : Fin S.card), (R.rectangle i).AreLambdaComparable (S.family.rectangle j) family C
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
        (R.rectangle i).AreLambdaComparable (S.family.rectangle j) family C :=
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
  refine' ⟨S, hSIncomp, _⟩
  have h5 : retention * (R.card : ℝ) ≤ (S.card : ℝ) := by
    have h6 : (R.card : ℝ) ≤ (S.card : ℝ) * (1 + M) := h_count
    have h7 : retention = 1 / (1 + M) := by rfl
    rw [h7]
    have h8 : 0 < 1 + M := by positivity
    calc
      (1 / (1 + M)) * (R.card : ℝ)
        ≤ (1 / (1 + M)) * ((S.card : ℝ) * (1 + M)) := by gcongr
      _ = (S.card : ℝ) := by
        field_simp [h8.ne']
  exact h5

theorem rectangle_refinement
    (hScaling : IntervalScalingStatement)
    (hComparable : ComparableRectanglesStatement)
    (hPacking : RectanglePackingStatement)
    (hSubfamily : RectangleSubfamilySelectionStatement) :
    RectangleRefinementStatement := by
  have h_part1 : ∀ K D : ℝ, 1 ≤ K → 1 ≤ D →
      ∀ c : ℝ, 0 < c → c < 1 →
        ∃ C : ℝ, 100 ≤ C ∧
          ∀ family : Set C2Function,
            IsCinematicFamily family K D →
            ∀ I : ParameterInterval, I.IsControlled K →
              ∀ delta t : ℝ, 0 < delta → delta ≤ t → t ≤ 1 →
                IsAdmissibleComparisonScale delta t C →
                ∀ R S R' S' : CurvilinearRectangle delta t,
                  R.function ∈ family → S.function ∈ family →
                  R.IsOverCentralQuarterOf I →
                  S.IsOverCentralQuarterOf I →
                  R'.IsCenteredShrinkOf R c →
                  S'.IsCenteredShrinkOf S c →
                  R.AreLambdaIncomparable S family C →
                  R'.AreLambdaIncomparable S' family 100 :=
    shrinking_preserves_incomparability hComparable
  have h_part2 := rectangle_refinement_part2 hPacking hSubfamily hComparable
  exact ⟨h_part1, h_part2⟩

end Kakeya.Cinematic
