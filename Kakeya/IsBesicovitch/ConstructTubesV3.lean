/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib
public import Kakeya.IsBesicovitch.PiTransfer
public import Kakeya.Shading

/-!
# Constructing tubes for the Katz–Tao reduction

A direct proof of the tube-construction lemma (B7.5). The construction produces
Euclidean tubes whose shades lie inside the δ-thickening of E.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

/-- Construct the shaded Euclidean tubes used in the B7.5 reduction: each shade lies inside the
`δ`-thickening of `E`, has volume at least `(1 / 2) · ρ · δ²`, and its tube axis is aligned with
`ω` with scale in `[1, 2]`. -/
theorem B7_5_construct_tubes_v3
    {δ ρ : ℝ} (hδ_pos : 0 < δ) (hρ_pos : 0 < ρ)
    (Ω : Finset (EuclideanSpace ℝ (Fin 3)))
    (hΩ_unit : ∀ ω ∈ Ω, ‖ω‖ = 1)
    {E : Set (EuclideanSpace ℝ (Fin 3))}
    (hseg : ∀ ω ∈ Ω, ∃ a : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal ρ ≤
          (μH[(1 : ℝ)] : MeasureTheory.Measure _)
            (affineSegment ℝ a (a + ω) ∩ E)) :
    ∃ T : (ω : EuclideanSpace ℝ (Fin 3)) → ω ∈ Ω →
            ShadedTube δ.toNNReal (EuclideanSpace ℝ (Fin 3)),
      (∀ ω (hω : ω ∈ Ω),
          MeasureTheory.volume.real (T ω hω).shade ≥ (1 / 2 : ℝ) * ρ * δ ^ 2) ∧
      (∀ ω (hω : ω ∈ Ω),
          ∃ s : ℝ, 1 ≤ s ∧ s ≤ 2 ∧
            ∀ i : Fin 3, ((T ω hω).y - (T ω hω).x) i = s * ω i) ∧
      (∀ ω (hω : ω ∈ Ω),
          ((T ω hω).shade : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            Metric.thickening δ E) := by
  classical
  by_cases hΩ_empty : Ω = ∅
  · subst hΩ_empty
    refine ⟨fun ω hω => absurd hω (Finset.notMem_empty _), ?_, ?_, ?_⟩
    · intro ω hω; exact absurd hω (Finset.notMem_empty _)
    · intro ω hω; exact absurd hω (Finset.notMem_empty _)
    · intro ω hω; exact absurd hω (Finset.notMem_empty _)
  have hΩ_ne : Ω.Nonempty := Finset.nonempty_iff_ne_empty.mpr hΩ_empty
  have hρ_le_one : ρ ≤ 1 := by
    obtain ⟨ω, hω⟩ := hΩ_ne
    obtain ⟨a, hseg_a⟩ := hseg ω hω
    have h_inter_le :
        (μH[(1 : ℝ)] : MeasureTheory.Measure _)
            (affineSegment ℝ a (a + ω) ∩ E) ≤
          (μH[(1 : ℝ)] : MeasureTheory.Measure _) (affineSegment ℝ a (a + ω)) :=
      MeasureTheory.measure_mono Set.inter_subset_left
    have h_aff : (μH[(1 : ℝ)] : MeasureTheory.Measure _)
            (affineSegment ℝ a (a + ω)) = edist a (a + ω) :=
      MeasureTheory.hausdorffMeasure_affineSegment a (a + ω)
    have h_edist : edist a (a + ω) = ENNReal.ofReal 1 := by
      rw [edist_eq_enorm_sub]
      have h_sub : a - (a + ω) = -ω := by abel
      rw [h_sub, enorm_neg]
      rw [show (1 : ℝ) = ‖ω‖ from (hΩ_unit ω hω).symm]
      exact (ofReal_norm ω).symm
    have h_le_one : ENNReal.ofReal ρ ≤ ENNReal.ofReal 1 := by
      calc ENNReal.ofReal ρ
          ≤ _ := hseg_a
        _ ≤ _ := h_inter_le
        _ = _ := h_aff
        _ = _ := h_edist
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h_le_one
  suffices h : ∀ ω ∈ Ω,
      ∃ T : ShadedTube δ.toNNReal (EuclideanSpace ℝ (Fin 3)),
        MeasureTheory.volume.real T.shade ≥ ((1:ℝ)/2) * ρ * δ ^ 2 ∧
        (∃ s : ℝ, 1 ≤ s ∧ s ≤ 2 ∧
            ∀ i : Fin 3, (T.y - T.x) i = s * ω i) ∧
        (T.shade : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Metric.thickening δ E by
    refine ⟨fun ω hω => (h ω hω).choose, ?_, ?_, ?_⟩
    · intro ω hω; exact (h ω hω).choose_spec.1
    · intro ω hω; exact (h ω hω).choose_spec.2.1
    · intro ω hω; exact (h ω hω).choose_spec.2.2
  intro ω hω
  set aω : EuclideanSpace ℝ (Fin 3) := Classical.choose (hseg ω hω) with haω_def
  have h_aω_spec : ENNReal.ofReal ρ ≤
      (μH[(1 : ℝ)] : MeasureTheory.Measure _)
        (affineSegment ℝ aω (aω + ω) ∩ E) := Classical.choose_spec (hseg ω hω)
  let xpt : EuclideanSpace ℝ (Fin 3) := aω
  have h_univ_ne : (Finset.univ : Finset (Fin 3)).Nonempty := ⟨0, Finset.mem_univ _⟩
  obtain ⟨i_max, _, h_i_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 3)) (fun i => |ω i|) h_univ_ne
  let normInf : ℝ := |ω i_max|
  have h_normInf_def : normInf = |ω i_max| := rfl
  have hsum : ∑ i : Fin 3, |ω i|^2 = 1 := by
    have h_norm_sq : ‖ω‖^2 = 1 := by rw [hΩ_unit ω hω]; ring
    have h_norm_eq := EuclideanSpace.real_norm_sq_eq ω
    rw [h_norm_eq] at h_norm_sq
    simpa [Real.norm_eq_abs, sq_abs] using h_norm_sq
  have h_normInf_pos : 0 < normInf := by
    by_contra h
    push Not at h
    have h_le_zero : normInf ≤ 0 := h
    have h_abs_nn : 0 ≤ normInf := abs_nonneg _
    have h_normInf_zero : normInf = 0 := le_antisymm h_le_zero h_abs_nn
    have h_all_zero : ∀ i : Fin 3, |ω i| = 0 := by
      intro i
      have h_le_max : |ω i| ≤ |ω i_max| := h_i_max i (Finset.mem_univ _)
      have : |ω i| ≤ 0 := h_le_max.trans (by rw [h_normInf_def] at h_normInf_zero; linarith)
      linarith [abs_nonneg (ω i)]
    have hsum_zero : ∑ i : Fin 3, |ω i|^2 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [h_all_zero i]
      ring
    linarith
  have h_normInf_sq_ge : (1 / 3 : ℝ) ≤ normInf ^ 2 := by
    have h_each_le : ∀ i : Fin 3, |ω i| ^ 2 ≤ normInf ^ 2 := by
      intro i
      have h_le : |ω i| ≤ normInf := h_i_max i (Finset.mem_univ _)
      exact sq_le_sq' (by linarith [abs_nonneg (ω i), abs_nonneg (ω i_max)]) h_le
    have h_sum_le : ∑ i : Fin 3, |ω i| ^ 2 ≤ ∑ _i : Fin 3, normInf ^ 2 :=
      Finset.sum_le_sum (fun i _ => h_each_le i)
    have h_card : ∑ _i : Fin 3, normInf ^ 2 = 3 * normInf ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [h_card] at h_sum_le
    rw [hsum] at h_sum_le
    linarith
  have h_normInf_ge_half : (1 / 2 : ℝ) ≤ normInf := by
    have h_sq : (1 / 2 : ℝ) ^ 2 ≤ normInf ^ 2 := by nlinarith
    have := Real.sqrt_le_sqrt h_sq
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2),
        Real.sqrt_sq h_normInf_pos.le] at this
    exact this
  let ypt : EuclideanSpace ℝ (Fin 3) := aω + ω
  have h_dist_xy : dist xpt ypt = 1 := by
    rw [dist_eq_norm]
    have h_sub : xpt - ypt = -ω := by simp [xpt, ypt]
    rw [h_sub, norm_neg, hΩ_unit ω hω]
  have h_seg_eq_image : segment ℝ xpt ypt =
      (fun θ : ℝ => (1 - θ) • xpt + θ • ypt) '' Set.Icc (0 : ℝ) 1 :=
    segment_eq_image ℝ xpt ypt
  have h_seg_compact : IsCompact (segment ℝ xpt ypt) := by
    rw [h_seg_eq_image]
    refine IsCompact.image isCompact_Icc ?_
    exact (continuous_const.sub continuous_id).smul continuous_const
      |>.add (continuous_id.smul continuous_const)
  have h_seg_closed : IsClosed (segment ℝ xpt ypt) := h_seg_compact.isClosed
  have h_seg_convex : Convex ℝ (segment ℝ xpt ypt) := convex_segment xpt ypt
  let carrier : Set (EuclideanSpace ℝ (Fin 3)) :=
    ⋃ z ∈ segment ℝ xpt ypt, Metric.closedBall z δ
  have h_carrier_eq_cthick : carrier = Metric.cthickening δ (segment ℝ xpt ypt) := by
    change (⋃ z ∈ segment ℝ xpt ypt, Metric.closedBall z δ) = _
    rw [← h_seg_closed.cthickening_eq_biUnion_closedBall hδ_pos.le]
  have h_carrier_convex : Convex ℝ carrier := by
    rw [h_carrier_eq_cthick]
    exact h_seg_convex.cthickening δ
  have h_carrier_compact : IsCompact carrier := by
    rw [h_carrier_eq_cthick]
    exact h_seg_compact.cthickening
  have h_carrier_nonempty : carrier.Nonempty := by
    refine ⟨xpt, ?_⟩
    change xpt ∈ ⋃ z ∈ segment ℝ xpt ypt, Metric.closedBall z δ
    exact Set.mem_iUnion₂.mpr ⟨xpt, left_mem_segment ℝ xpt ypt,
      Metric.mem_closedBall_self hδ_pos.le⟩
  let body : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    { carrier := carrier
      convex' := h_carrier_convex.isConvexSet
      isCompact' := h_carrier_compact
      nonempty' := h_carrier_nonempty }
  let tube : Tube δ.toNNReal (EuclideanSpace ℝ (Fin 3)) :=
    { toConvexSpaceBody := body
      x := xpt
      y := ypt
      dist_eq_one := h_dist_xy
      carrier_eq := by
        change (⋃ z ∈ segment ℝ xpt ypt, Metric.closedBall z δ) = _
        rw [Real.coe_toNNReal δ hδ_pos.le] }
  let othersF : Finset (Fin 3) :=
    (Finset.univ : Finset (Fin 3)).filter (· ≠ i_max)
  have h_others_card : othersF.card = 2 := by
    have h_compl : othersF = Finset.univ \ {i_max} := by
      ext i; simp [othersF]
    rw [h_compl, Finset.card_univ_sdiff]; simp
  have h_others_ne : othersF.Nonempty := by
    rw [← Finset.card_pos, h_others_card]; omega
  obtain ⟨j₁, hj₁_mem⟩ := h_others_ne
  have hj₁_ne : j₁ ≠ i_max := (Finset.mem_filter.mp hj₁_mem).2
  let othersF' : Finset (Fin 3) := othersF.erase j₁
  have h_others'_card : othersF'.card = 1 := by
    have : othersF'.card = othersF.card - 1 :=
      Finset.card_erase_of_mem hj₁_mem
    rw [this, h_others_card]
  have h_others'_ne : othersF'.Nonempty := by
    rw [← Finset.card_pos, h_others'_card]; omega
  obtain ⟨j₂, hj₂_mem'⟩ := h_others'_ne
  have hj₂_mem : j₂ ∈ othersF := Finset.mem_of_mem_erase hj₂_mem'
  have hj₂_ne : j₂ ≠ i_max := (Finset.mem_filter.mp hj₂_mem).2
  have hj₂_ne_j₁ : j₂ ≠ j₁ := (Finset.mem_erase.mp hj₂_mem').1
  have h_3_partition : ∀ i : Fin 3, i = i_max ∨ i = j₁ ∨ i = j₂ := by
    intro i
    by_contra h
    push Not at h
    obtain ⟨hi₀, hi₁, hi₂⟩ := h
    have h_3_distinct : ({i_max, j₁, j₂} : Finset (Fin 3)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_singleton] <;>
        simp [Ne.symm hj₁_ne, Ne.symm hj₂_ne, Ne.symm hj₂_ne_j₁]
    have h_i_not_in : i ∉ ({i_max, j₁, j₂} : Finset (Fin 3)) := by
      simp [hi₀, hi₁, hi₂]
    have h_4 : ({i, i_max, j₁, j₂} : Finset (Fin 3)).card = 4 := by
      rw [Finset.card_insert_of_notMem h_i_not_in, h_3_distinct]
    have h_le : ({i, i_max, j₁, j₂} : Finset (Fin 3)).card ≤ Finset.univ.card :=
      Finset.card_le_univ _
    rw [h_4] at h_le
    have : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
    omega
  let pmap : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun q i =>
    q i_max * ω i +
    q j₁ * (if i = j₁ then (1 : ℝ) else 0) +
    q j₂ * (if i = j₂ then (1 : ℝ) else 0)
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i k =>
    if k = i_max then ω i
    else if k = j₁ then (if i = j₁ then (1 : ℝ) else 0)
    else (if i = j₂ then (1 : ℝ) else 0)
  have h_pmap_eq_mulVec : ∀ q : Fin 3 → ℝ, pmap q = M.mulVecLin q := by
    intro q
    funext i
    change _ = ∑ k : Fin 3, M i k * q k
    have h3_eq : (Finset.univ : Finset (Fin 3)) = {i_max, j₁, j₂} := by
      apply Finset.eq_of_subset_of_card_le
      · intro x _; rcases h_3_partition x with rfl | rfl | rfl <;> simp
      · rw [Finset.card_univ, Fintype.card_fin]
        have hc : ({i_max, j₁, j₂} : Finset (Fin 3)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by
              simp [Ne.symm hj₁_ne, Ne.symm hj₂_ne]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hj₂_ne_j₁]),
            Finset.card_singleton]
        omega
    have h_imax_notMem : i_max ∉ ({j₁, j₂} : Finset (Fin 3)) := by
      simp [Ne.symm hj₁_ne, Ne.symm hj₂_ne]
    have h_j1_notMem : j₁ ∉ ({j₂} : Finset (Fin 3)) := by
      simp [Ne.symm hj₂_ne_j₁]
    rw [h3_eq, Finset.sum_insert h_imax_notMem,
      Finset.sum_insert h_j1_notMem, Finset.sum_singleton]
    simp only [M, if_neg hj₁_ne, if_neg hj₂_ne, if_neg hj₂_ne_j₁,
      if_pos rfl]
    change _ = (ω i) * q i_max +
      ((if i = j₁ then (1 : ℝ) else 0) * q j₁ +
       (if i = j₂ then (1 : ℝ) else 0) * q j₂)
    simp only [pmap]
    ring
  have h_det_M_abs : |M.det| = normInf := by
    have h_imax_ne_j1 : i_max ≠ j₁ := Ne.symm hj₁_ne
    have h_imax_ne_j2 : i_max ≠ j₂ := Ne.symm hj₂_ne
    have h_j1_ne_j2 : j₁ ≠ j₂ := Ne.symm hj₂_ne_j₁
    have h_det_via : M.det = M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1
                            - M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0
                            + M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 :=
      Matrix.det_fin_three M
    rw [h_det_via]
    fin_cases i_max <;> fin_cases j₁ <;> fin_cases j₂ <;>
      first
        | (exact absurd rfl h_imax_ne_j1)
        | (exact absurd rfl h_imax_ne_j2)
        | (exact absurd rfl h_j1_ne_j2)
        | (exact absurd rfl h_imax_ne_j1.symm)
        | (exact absurd rfl h_imax_ne_j2.symm)
        | (exact absurd rfl h_j1_ne_j2.symm)
        | skip
    all_goals {
      simp only [M]
      norm_num [Fin.ext_iff]
      simp [h_normInf_def]
    }
  let A : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ {t | aω + t • ω ∈ E}
  have h_lineMap : ∀ t : ℝ, AffineMap.lineMap aω (aω + ω) t = aω + t • ω := by
    intro t
    rw [AffineMap.lineMap_apply, vsub_eq_sub, add_sub_cancel_left,
        vadd_eq_add, add_comm]
  have h_aff_eq : affineSegment ℝ aω (aω + ω) =
      AffineMap.lineMap aω (aω + ω) '' Set.Icc (0 : ℝ) 1 := rfl
  have h_aff_inter_eq : affineSegment ℝ aω (aω + ω) ∩ E =
      AffineMap.lineMap aω (aω + ω) '' A := by
    ext p
    simp only [Set.mem_inter_iff, h_aff_eq, Set.mem_image, A]
    constructor
    · rintro ⟨⟨t, ht_mem, ht_eq⟩, hp⟩
      refine ⟨t, ⟨ht_mem, ?_⟩, ht_eq⟩
      simp only [Set.mem_setOf_eq]
      rw [← h_lineMap t, ht_eq]
      exact hp
    · rintro ⟨t, ⟨ht_mem, hAt⟩, ht_eq⟩
      refine ⟨⟨t, ht_mem, ht_eq⟩, ?_⟩
      rw [← ht_eq, h_lineMap]
      exact hAt
  have h_nndist_real : (nndist aω (aω + ω) : ℝ) = 1 := by
    rw [nndist_eq_nnnorm_sub]
    have h_sub : aω - (aω + ω) = -ω := by abel
    rw [h_sub]
    rw [show (‖-ω‖₊ : ℝ) = ‖-ω‖ from rfl, norm_neg, hΩ_unit ω hω]
  have h_hM_eq :
      (μH[(1 : ℝ)] : MeasureTheory.Measure _)
        (affineSegment ℝ aω (aω + ω) ∩ E) =
      (μH[(1 : ℝ)] : MeasureTheory.Measure _) A := by
    rw [h_aff_inter_eq, MeasureTheory.hausdorffMeasure_lineMap_image]
    rw [show (nndist aω (aω + ω) • (μH[(1 : ℝ)] A : ℝ≥0∞) : ℝ≥0∞) =
          (nndist aω (aω + ω) : ℝ≥0∞) * (μH[(1 : ℝ)] A : ℝ≥0∞) from rfl]
    have h_nndist_one : (nndist aω (aω + ω) : ℝ≥0∞) = 1 := by
      have : ((nndist aω (aω + ω) : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal ((nndist aω (aω + ω) : NNReal) : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]
      rw [this, h_nndist_real, ENNReal.ofReal_one]
    rw [h_nndist_one, one_mul]
  have h_volA_ge_rho : ENNReal.ofReal ρ ≤
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) A := by
    rw [← MeasureTheory.hausdorffMeasure_real]
    rw [← h_hM_eq]
    exact h_aω_spec
  let boxComp : (i : Fin 3) → Set ℝ := fun i =>
    if i = i_max then A
    else Set.Icc (-(δ / 2)) (δ / 2)
  let boxQ : Set (Fin 3 → ℝ) := Set.univ.pi boxComp
  let xptPi : Fin 3 → ℝ := fun i => aω i
  let shadePi : Set (Fin 3 → ℝ) := (fun q => xptPi + pmap q) '' boxQ
  let toEucl : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3) := fromPi
  let shadeS : Set (EuclideanSpace ℝ (Fin 3)) := toEucl '' shadePi
  have h_cross_dist (q : Fin 3 → ℝ) :
      dist (toEucl (xptPi + pmap q)) (aω + q i_max • ω) =
        Real.sqrt (q j₁ ^ 2 + q j₂ ^ 2) := by
    rw [EuclideanSpace.dist_eq]
    congr 1
    rw [Fin.sum_univ_three]
    have h_imax_ne_j1 : i_max ≠ j₁ := Ne.symm hj₁_ne
    have h_imax_ne_j2 : i_max ≠ j₂ := Ne.symm hj₂_ne
    have h_j1_ne_j2 : j₁ ≠ j₂ := Ne.symm hj₂_ne_j₁
    fin_cases i_max <;> fin_cases j₁ <;> fin_cases j₂ <;>
      first
        | (exact absurd rfl h_imax_ne_j1)
        | (exact absurd rfl h_imax_ne_j2)
        | (exact absurd rfl h_j1_ne_j2)
        | (exact absurd rfl h_imax_ne_j1.symm)
        | (exact absurd rfl h_imax_ne_j2.symm)
        | (exact absurd rfl h_j1_ne_j2.symm)
        | skip
    all_goals
      simp [toEucl, fromPi, xptPi, pmap, sq_abs, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul] <;> ring
  have h_cross_dist_lt (q : Fin 3 → ℝ)
      (hq_j₁ : q j₁ ∈ Set.Icc (-(δ / 2)) (δ / 2))
      (hq_j₂ : q j₂ ∈ Set.Icc (-(δ / 2)) (δ / 2)) :
      dist (toEucl (xptPi + pmap q)) (aω + q i_max • ω) < δ := by
    rw [h_cross_dist]
    rw [Real.sqrt_lt' hδ_pos]
    rcases hq_j₁ with ⟨hq_j₁_lo, hq_j₁_hi⟩
    rcases hq_j₂ with ⟨hq_j₂_lo, hq_j₂_hi⟩
    nlinarith [sq_nonneg (q j₁ + δ / 2), sq_nonneg (q j₂ + δ / 2),
      sq_nonneg (δ / 2 - q j₁), sq_nonneg (δ / 2 - q j₂)]
  have h_shade_sub_carrier : shadeS ⊆ carrier := by
    rintro p ⟨pPi, ⟨q, hq, rfl⟩, rfl⟩
    change toEucl (xptPi + pmap q) ∈
      ⋃ z ∈ segment ℝ xpt ypt, Metric.closedBall z δ
    have hq_imax : q i_max ∈ A := by
      have := hq i_max (Set.mem_univ _)
      simp only [boxComp, if_pos rfl] at this
      exact this
    have hq_imax_in_Icc : q i_max ∈ Set.Icc (0 : ℝ) 1 := hq_imax.1
    have hq_j₁ : q j₁ ∈ Set.Icc (-(δ / 2)) (δ / 2) := by
      have := hq j₁ (Set.mem_univ _)
      simp only [boxComp, if_neg hj₁_ne] at this
      exact this
    have hq_j₂ : q j₂ ∈ Set.Icc (-(δ / 2)) (δ / 2) := by
      have := hq j₂ (Set.mem_univ _)
      simp only [boxComp, if_neg hj₂_ne] at this
      exact this
    set z : EuclideanSpace ℝ (Fin 3) := aω + q i_max • ω with hz_def
    have hz_seg : z ∈ segment ℝ xpt ypt := by
      refine ⟨1 - q i_max, q i_max, sub_nonneg.mpr hq_imax_in_Icc.2,
        hq_imax_in_Icc.1, by ring, ?_⟩
      ext i
      simp [hz_def, xpt, ypt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    refine Set.mem_iUnion₂.mpr ⟨z, hz_seg, ?_⟩
    rw [Metric.mem_closedBall]
    exact (h_cross_dist_lt q hq_j₁ hq_j₂).le
  have h_shade_sub_thick : shadeS ⊆ Metric.thickening δ E := by
    rintro p ⟨pPi, ⟨q, hq, rfl⟩, rfl⟩
    have hq_imax : q i_max ∈ A := by
      have := hq i_max (Set.mem_univ _)
      simp only [boxComp, if_pos rfl] at this
      exact this
    have hq_imax_E : aω + (q i_max) • ω ∈ E := hq_imax.2
    have hq_j₁ : q j₁ ∈ Set.Icc (-(δ / 2)) (δ / 2) := by
      have := hq j₁ (Set.mem_univ _)
      simp only [boxComp, if_neg hj₁_ne] at this
      exact this
    have hq_j₂ : q j₂ ∈ Set.Icc (-(δ / 2)) (δ / 2) := by
      have := hq j₂ (Set.mem_univ _)
      simp only [boxComp, if_neg hj₂_ne] at this
      exact this
    rw [Metric.mem_thickening_iff]
    exact ⟨aω + q i_max • ω, hq_imax_E, h_cross_dist_lt q hq_j₁ hq_j₂⟩
  have h_pmap_fn_eq : pmap = ⇑M.mulVecLin := by
    funext q; exact h_pmap_eq_mulVec q
  have h_shadePi_eq : shadePi = xptPi +ᵥ (pmap '' boxQ) := by
    change (fun q => xptPi + pmap q) '' boxQ = xptPi +ᵥ (pmap '' boxQ)
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨pmap q, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
  have h_vol_trans_pi :
      MeasureTheory.volume shadePi = MeasureTheory.volume (pmap '' boxQ) := by
    rw [h_shadePi_eq]
    exact MeasureTheory.measure_vadd (μ := MeasureTheory.volume) _ _
  have h_vol_transfer : MeasureTheory.volume shadeS = MeasureTheory.volume shadePi := by
    change MeasureTheory.volume (fromPi '' shadePi) = MeasureTheory.volume shadePi
    exact volume_image_fromPi (S := shadePi)
  have h_vol_lin : MeasureTheory.volume (pmap '' boxQ)
      = ENNReal.ofReal |M.det| * MeasureTheory.volume boxQ := by
    rw [h_pmap_fn_eq]
    rw [MeasureTheory.Measure.addHaar_image_linearMap
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)))
      M.mulVecLin boxQ]
    have h_det : LinearMap.det (M.mulVecLin) = M.det := by
      rw [show M.mulVecLin = Matrix.toLin' M from rfl]
      exact LinearMap.det_toLin' M
    rw [h_det]
  have h_vol_boxQ : MeasureTheory.volume boxQ =
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) A *
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (-(δ/2)) (δ/2)) *
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc (-(δ/2)) (δ/2)) := by
    have hpi : MeasureTheory.volume boxQ = ∏ i, MeasureTheory.volume (boxComp i) := by
      change MeasureTheory.volume (Set.univ.pi boxComp) = _
      exact MeasureTheory.volume_pi_pi boxComp
    rw [hpi]
    have h3_eq : (Finset.univ : Finset (Fin 3)) = {i_max, j₁, j₂} := by
      apply Finset.eq_of_subset_of_card_le
      · intro x _; rcases h_3_partition x with rfl | rfl | rfl <;> simp
      · rw [Finset.card_univ, Fintype.card_fin]
        have hc : ({i_max, j₁, j₂} : Finset (Fin 3)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by
              simp [Ne.symm hj₁_ne, Ne.symm hj₂_ne]),
            Finset.card_insert_of_notMem (by simp [Ne.symm hj₂_ne_j₁]),
            Finset.card_singleton]
        omega
    have h_imax_notMem : i_max ∉ ({j₁, j₂} : Finset (Fin 3)) := by
      simp [Ne.symm hj₁_ne, Ne.symm hj₂_ne]
    have h_j1_notMem : j₁ ∉ ({j₂} : Finset (Fin 3)) := by
      simp [Ne.symm hj₂_ne_j₁]
    rw [h3_eq, Finset.prod_insert h_imax_notMem,
      Finset.prod_insert h_j1_notMem, Finset.prod_singleton]
    simp only [boxComp, if_pos rfl, if_neg hj₁_ne, if_neg hj₂_ne]
    ring
  have h_vol_Icc : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (Set.Icc (-(δ/2)) (δ/2)) = ENNReal.ofReal δ := by
    rw [Real.volume_Icc]
    congr 1; ring
  have h_vol_boxQ' : MeasureTheory.volume boxQ =
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) A *
      (ENNReal.ofReal δ) * (ENNReal.ofReal δ) := by
    rw [h_vol_boxQ, h_vol_Icc]
  have h_vol_shade_ge :
      ENNReal.ofReal ((1 : ℝ) / 2 * ρ * δ ^ 2) ≤ MeasureTheory.volume shadeS := by
    rw [h_vol_transfer, h_vol_trans_pi, h_vol_lin, h_vol_boxQ', h_det_M_abs]
    calc ENNReal.ofReal ((1 : ℝ) / 2 * ρ * δ ^ 2)
        = ENNReal.ofReal ((1 / 2 : ℝ)) * ENNReal.ofReal ρ
            * ENNReal.ofReal δ * ENNReal.ofReal δ := by
          rw [show ((1 : ℝ) / 2 * ρ * δ ^ 2) = ((1 / 2 : ℝ)) * ρ * δ * δ from by ring]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by norm_num)]
      _ ≤ ENNReal.ofReal normInf * ENNReal.ofReal ρ
            * ENNReal.ofReal δ * ENNReal.ofReal δ := by
          gcongr
      _ ≤ ENNReal.ofReal normInf
            * (MeasureTheory.volume : MeasureTheory.Measure ℝ) A
            * ENNReal.ofReal δ * ENNReal.ofReal δ := by
          gcongr
      _ = _ := by ring
  have h_vol_shade_real :
      ((1 : ℝ) / 2) * ρ * δ ^ 2 ≤ MeasureTheory.volume.real shadeS := by
    have h_fin : MeasureTheory.volume shadeS ≠ ∞ := by
      have h_sub : shadeS ⊆ carrier := h_shade_sub_carrier
      exact ne_top_of_le_ne_top h_carrier_compact.measure_lt_top.ne
        (MeasureTheory.measure_mono h_sub)
    have := ENNReal.toReal_mono h_fin h_vol_shade_ge
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  let shadeS' : Set (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.toMeasurable MeasureTheory.volume shadeS ∩ carrier
      ∩ Metric.thickening δ E
  have h_shadeS'_meas : MeasurableSet shadeS' :=
    ((MeasureTheory.measurableSet_toMeasurable _ _).inter
      h_carrier_compact.measurableSet).inter
      Metric.isOpen_thickening.measurableSet
  have h_shadeS_sub_shadeS' : shadeS ⊆ shadeS' := fun x hx =>
    ⟨⟨MeasureTheory.subset_toMeasurable _ _ hx, h_shade_sub_carrier hx⟩,
      h_shade_sub_thick hx⟩
  have h_shadeS'_sub_carrier : shadeS' ⊆ carrier := fun _ hx => hx.1.2
  have h_shadeS'_sub_thick : shadeS' ⊆ Metric.thickening δ E :=
    fun _ hx => hx.2
  have h_vol_shade'_real :
      ((1 : ℝ) / 2) * ρ * δ ^ 2 ≤ MeasureTheory.volume.real shadeS' := by
    have h_fin' : MeasureTheory.volume shadeS' ≠ ∞ :=
      ne_top_of_le_ne_top h_carrier_compact.measure_lt_top.ne
        (MeasureTheory.measure_mono h_shadeS'_sub_carrier)
    have h_mono : MeasureTheory.volume.real shadeS ≤
        MeasureTheory.volume.real shadeS' := by
      apply ENNReal.toReal_mono h_fin'
      exact MeasureTheory.measure_mono h_shadeS_sub_shadeS'
    exact h_vol_shade_real.trans h_mono
  let stube : ShadedTube δ.toNNReal (EuclideanSpace ℝ (Fin 3)) :=
    { toTube := tube
      shade := shadeS'
      measurableSet_shade := h_shadeS'_meas
      shade_subset := by
        change shadeS' ⊆ carrier
        exact h_shadeS'_sub_carrier }
  refine ⟨stube, ?_, ?_, ?_⟩
  · change (1 : ℝ) / 2 * ρ * δ ^ 2 ≤ MeasureTheory.volume.real shadeS'
    exact h_vol_shade'_real
  · refine ⟨1, le_rfl, by norm_num, ?_⟩
    intro i
    change (ypt - xpt) i = 1 * ω i
    simp [xpt, ypt]
  · exact h_shadeS'_sub_thick

end Kakeya.IsBesicovitch
