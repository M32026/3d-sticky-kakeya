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
public import Kakeya.Frostman
public import Kakeya.IsBesicovitch.CircularCone
public import Kakeya.IsBesicovitch.DifferenceBody
public import Kakeya.IsBesicovitch.KatzTaoGeometry
public import Kakeya.KakeyaEstimate
import Kakeya.IsBesicovitch.PiTransfer

/-!
# Scale-local Kakeya and Katz–Tao tube bounds

This file localizes a Kakeya estimate to arbitrary finite tube families and proves the
separated-direction Katz–Tao inequality for Euclidean tubes. It packages both estimates in the
forms used by the B7.5 construction.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

private noncomputable def kakeyaGridIndex
    (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ :=
  fun j ↦ ⌊4 * x j⌋

private noncomputable def kakeyaGridCenter
    (c : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j ↦ (c j : ℝ) / 4 + 1 / 8

private def kakeyaGridColor (c : Fin 3 → ℤ) : Fin 3 → ZMod 9 :=
  fun j ↦ c j

private lemma dist_gridCenter_le_quarter (x : EuclideanSpace ℝ (Fin 3)) :
    dist x (kakeyaGridCenter (kakeyaGridIndex x)) ≤ 1 / 4 := by
  have hcoord : ∀ j : Fin 3,
      |x j - (kakeyaGridCenter (kakeyaGridIndex x)) j| ≤ 1 / 8 := by
    intro j
    have hfloor_le : ((⌊4 * x j⌋ : ℤ) : ℝ) ≤ 4 * x j := Int.floor_le _
    have hlt_floor : 4 * x j < ((⌊4 * x j⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    change |x j - (((⌊4 * x j⌋ : ℤ) : ℝ) / 4 + 1 / 8)| ≤ 1 / 8
    rw [abs_le]
    constructor <;> linarith
  rw [EuclideanSpace.dist_eq]
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  rw [Fin.sum_univ_three]
  have h0 := sq_le_sq' (neg_le_of_abs_le (hcoord 0)) (le_of_abs_le (hcoord 0))
  have h1 := sq_le_sq' (neg_le_of_abs_le (hcoord 1)) (le_of_abs_le (hcoord 1))
  have h2 := sq_le_sq' (neg_le_of_abs_le (hcoord 2)) (le_of_abs_le (hcoord 2))
  norm_num [Real.dist_eq, sq_abs] at h0 h1 h2 ⊢
  nlinarith

private lemma two_lt_dist_gridCenter_of_same_color {c c' : Fin 3 → ℤ}
    (hcc' : c ≠ c') (hcolor : kakeyaGridColor c = kakeyaGridColor c') :
    2 < dist (kakeyaGridCenter c) (kakeyaGridCenter c') := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ c' j := by
    by_contra h
    push Not at h
    exact hcc' (funext h)
  have hcast : (c j : ZMod 9) = c' j := congrFun hcolor j
  have hdvd : (9 : ℤ) ∣ c' j - c j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (c j) (c' j) 9).mp hcast
  have hsub_ne : c' j - c j ≠ 0 := sub_ne_zero.mpr (Ne.symm hj)
  have habs : (9 : ℤ) ≤ |c' j - c j| := Int.le_abs_of_dvd hsub_ne hdvd
  have hcoord : (9 / 4 : ℝ) ≤
      dist (kakeyaGridCenter c j) (kakeyaGridCenter c' j) := by
    change (9 / 4 : ℝ) ≤
      |((c j : ℝ) / 4 + 1 / 8) - ((c' j : ℝ) / 4 + 1 / 8)|
    rw [show ((c j : ℝ) / 4 + 1 / 8) - ((c' j : ℝ) / 4 + 1 / 8) =
      -((c' j - c j : ℤ) : ℝ) / 4 by push_cast; ring, abs_div, abs_neg]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4), ← Int.cast_abs]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
    norm_num
    exact_mod_cast habs
  have hpi : dist (kakeyaGridCenter c j) (kakeyaGridCenter c' j) ≤
      dist (toPi (kakeyaGridCenter c)) (toPi (kakeyaGridCenter c')) :=
    dist_le_pi_dist _ _ j
  have heucl := dist_toPi_le (kakeyaGridCenter c) (kakeyaGridCenter c')
  linarith

/-- The loss in the grid localization of the Kakeya estimate: `9³` colors suffice. -/
def kakeyaLocalizationConstant : ℝ := 729

/-- A centered Kakeya estimate localizes to an arbitrary finite family of tubes, at the cost of
the absolute constant `kakeyaLocalizationConstant`. -/
theorem kakeyaEstimateAt_localized.{u_KE}
    {δ : NNReal} {β η : ℝ} (hδ_le : (δ : ℝ) ≤ 1 / 4)
    (hcen : ∀ (c : EuclideanSpace ℝ (Fin 3)) (ι : Type u_KE) (s : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall c 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        MeasureTheory.volume (⋃ i ∈ s, (T i).shade) ≥
          δ ^ β * s.card * δ ^ (3 - 1))
    {ι : Type u_KE} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hKT : ConvexSpaceBody.IsKatzTao s
      (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (-η)))
    (hfull : ∀ s' ⊆ s, s'.Nonempty →
      ShadedBody.fullness s' (fun i ↦ (T i).toShadedBody) ≥ δ ^ η) :
    MeasureTheory.volume.real (⋃ i ∈ s, (T i).shade) ≥
      ((δ : ℝ) ^ β * (s.card : ℝ) * (δ : ℝ) ^ 2) /
        kakeyaLocalizationConstant := by
  classical
  let g : ι → Fin 3 → ℤ := fun i ↦
    kakeyaGridIndex (midpoint ℝ (T i).x (T i).y)
  let cells : Finset (Fin 3 → ℤ) := s.image g
  let fiber : (Fin 3 → ℤ) → Finset ι := fun c ↦ s.filter fun i ↦ g i = c
  let A : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)) := fun c ↦
    ⋃ i ∈ fiber c, (T i).shade
  let U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (T i).shade
  let colorFiber : (Fin 3 → ZMod 9) → Finset (Fin 3 → ℤ) := fun q ↦
    cells.filter fun c ↦ kakeyaGridColor c = q
  have hfiber_subset (c : Fin 3 → ℤ) : fiber c ⊆ s :=
    Finset.filter_subset _ _
  have hfiber_nonempty (c : Fin 3 → ℤ) (hc : c ∈ cells) : (fiber c).Nonempty := by
    obtain ⟨i, hi, hic⟩ := Finset.mem_image.mp hc
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hic⟩⟩
  have hA_ball (c : Fin 3 → ℤ) :
      A c ⊆ Metric.closedBall (kakeyaGridCenter c) 1 := by
    intro x hx
    simp only [A, Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hi := Finset.mem_filter.mp hi
    have hcarrier := Kakeya.Tube.carrier_subset_closedBall_midpoint
      (E := EuclideanSpace ℝ (Fin 3)) (T i).toTube
      ((T i).shade_subset hxi)
    rw [Metric.mem_closedBall] at hcarrier ⊢
    have hmid : dist (midpoint ℝ (T i).x (T i).y) (kakeyaGridCenter c) ≤ 1 / 4 := by
      rw [← hi.2]
      exact dist_gridCenter_le_quarter _
    calc
      dist x (kakeyaGridCenter c) ≤
          dist x (midpoint ℝ (T i).x (T i).y) +
            dist (midpoint ℝ (T i).x (T i).y) (kakeyaGridCenter c) := dist_triangle _ _ _
      _ ≤ (1 / 2 + (δ : ℝ)) + 1 / 4 := add_le_add hcarrier hmid
      _ ≤ 1 := by linarith
  have hA_meas (c : Fin 3 → ℤ) : MeasurableSet (A c) := by
    exact Finset.measurableSet_biUnion (fiber c) fun i _ ↦ (T i).measurableSet_shade
  have hA_ne_top (c : Fin 3 → ℤ) : MeasureTheory.volume (A c) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_biUnion_finset_le (fiber c) _)
    exact ENNReal.sum_ne_top.mpr fun i _ ↦
      ne_top_of_le_ne_top (T i).isCompact'.measure_ne_top
        (MeasureTheory.measure_mono (T i).shade_subset)
  have hU_ne_top : MeasureTheory.volume U ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_biUnion_finset_le s _)
    exact ENNReal.sum_ne_top.mpr fun i _ ↦
      ne_top_of_le_ne_top (T i).isCompact'.measure_ne_top
        (MeasureTheory.measure_mono (T i).shade_subset)
  have hA_sub_U (c : Fin 3 → ℤ) : A c ⊆ U := by
    intro x hx
    simp only [A, U, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hfiber_subset c hi, hxi⟩
  have hcell_lower (c : Fin 3 → ℤ) (hc : c ∈ cells) :
      (δ : ℝ) ^ β * ((fiber c).card : ℝ) * (δ : ℝ) ^ 2 ≤
        MeasureTheory.volume.real (A c) := by
    have hestimate := hcen (kakeyaGridCenter c) ι (fiber c) T
      (fun i hi ↦ by
        intro x hx
        have hcarrier := Kakeya.Tube.carrier_subset_closedBall_midpoint
          (E := EuclideanSpace ℝ (Fin 3)) (T i).toTube hx
        rw [Metric.mem_closedBall] at hcarrier ⊢
        have hi' := Finset.mem_filter.mp hi
        have hmid : dist (midpoint ℝ (T i).x (T i).y) (kakeyaGridCenter c) ≤ 1 / 4 := by
          rw [← hi'.2]
          exact dist_gridCenter_le_quarter _
        calc
          dist x (kakeyaGridCenter c) ≤
              dist x (midpoint ℝ (T i).x (T i).y) +
                dist (midpoint ℝ (T i).x (T i).y) (kakeyaGridCenter c) :=
            dist_triangle _ _ _
          _ ≤ (1 / 2 + (δ : ℝ)) + 1 / 4 := add_le_add hcarrier hmid
          _ ≤ 1 := by linarith)
      (hKT.subset (hfiber_subset c))
      (hfull (fiber c) (hfiber_subset c) (hfiber_nonempty c hc))
    have hreal := ENNReal.toReal_mono (hA_ne_top c) hestimate
    simpa [A, MeasureTheory.Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ← ENNReal.toReal_rpow] using hreal
  have hcolors_disj (q : Fin 3 → ZMod 9) :
      Set.PairwiseDisjoint (↑(colorFiber q)) A := by
    intro c hc c' hc' hcc'
    have hc_mem := Finset.mem_filter.mp hc
    have hc'_mem := Finset.mem_filter.mp hc'
    apply Set.disjoint_of_subset (hA_ball c) (hA_ball c')
    apply Metric.closedBall_disjoint_closedBall
    simpa only [one_add_one_eq_two] using
      two_lt_dist_gridCenter_of_same_color hcc' (hc_mem.2.trans hc'_mem.2.symm)
  have hcolor_sum_le (q : Fin 3 → ZMod 9) :
      ∑ c ∈ colorFiber q, MeasureTheory.volume.real (A c) ≤
        MeasureTheory.volume.real U := by
    rw [← MeasureTheory.measureReal_biUnion_finset (hcolors_disj q)
      (fun c _ ↦ hA_meas c) (fun c _ ↦ hA_ne_top c)]
    exact MeasureTheory.measureReal_mono
      (Set.iUnion₂_subset fun c _ ↦ hA_sub_U c) hU_ne_top
  have hsum_partition :
      ∑ q : Fin 3 → ZMod 9, ∑ c ∈ colorFiber q, MeasureTheory.volume.real (A c) =
        ∑ c ∈ cells, MeasureTheory.volume.real (A c) := by
    simpa [colorFiber] using Finset.sum_fiberwise_eq_sum_filter cells Finset.univ
      kakeyaGridColor (fun c ↦ MeasureTheory.volume.real (A c))
  have hsum_upper :
      ∑ c ∈ cells, MeasureTheory.volume.real (A c) ≤
        729 * MeasureTheory.volume.real U := by
    rw [← hsum_partition]
    calc
      ∑ q : Fin 3 → ZMod 9, ∑ c ∈ colorFiber q, MeasureTheory.volume.real (A c) ≤
          ∑ _q : Fin 3 → ZMod 9, MeasureTheory.volume.real U :=
        Finset.sum_le_sum fun q _ ↦ hcolor_sum_le q
      _ = 729 * MeasureTheory.volume.real U := by norm_num [Finset.sum_const]
  have hsum_lower :
      (δ : ℝ) ^ β * (s.card : ℝ) * (δ : ℝ) ^ 2 ≤
        ∑ c ∈ cells, MeasureTheory.volume.real (A c) := by
    calc
      (δ : ℝ) ^ β * (s.card : ℝ) * (δ : ℝ) ^ 2 =
          ∑ c ∈ cells,
            ((δ : ℝ) ^ β * ((fiber c).card : ℝ) * (δ : ℝ) ^ 2) := by
        rw [Finset.card_eq_sum_card_fiberwise
          (show (s : Set ι).MapsTo g cells from fun i hi ↦ Finset.mem_image_of_mem g hi)]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ ∑ c ∈ cells, MeasureTheory.volume.real (A c) :=
        Finset.sum_le_sum fun c hc ↦ hcell_lower c hc
  change _ ≥ _ / 729
  have h := hsum_lower.trans hsum_upper
  linarith

theorem _aux_apply_kakeya_estimate.{u_KE}
    {q η : ℝ} (_hq_pos : 0 < q) (_hq_lt : q < 3)
    (hKE : KakeyaEstimate.{u_KE} 3 ((3 - q) / 2) η) :
    ∃ k_min : ℕ, ∀ ⦃k : ℕ⦄, k_min ≤ k →
      ∀ (ι : Type u_KE) (s : Finset ι)
        (T : ι → ShadedTube ((1/2 : NNReal) ^ k) (EuclideanSpace ℝ (Fin 3))),
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
          (((1/2 : NNReal) ^ k) ^ (-η)) →
        (∀ s' ⊆ s, s'.Nonempty →
          ShadedBody.fullness s' (fun i ↦ (T i).toShadedBody) ≥
            ((1/2 : NNReal) ^ k) ^ η) →
        MeasureTheory.volume.real (⋃ i ∈ s, (T i).shade) ≥
          (((1/2 : ℝ) ^ k) ^ ((3 - q) / 2) * (s.card : ℝ) *
            ((1/2 : ℝ) ^ k) ^ 2) / kakeyaLocalizationConstant := by
  have hKE' := hKE.centered
  rw [Filter.eventually_iff_exists_mem] at hKE'
  obtain ⟨U, hU_mem, hU⟩ := hKE'
  rw [mem_nhdsGT_iff_exists_Ioc_subset] at hU_mem
  obtain ⟨ε, hε_pos, hε_subset⟩ := hU_mem
  rw [Set.mem_Ioi] at hε_pos
  have h_half_lt_one_nn : (1/2 : NNReal) < 1 := by
    rw [← NNReal.coe_lt_coe]; push_cast; norm_num
  have h_half_le_one_nn : (1/2 : NNReal) ≤ 1 := h_half_lt_one_nn.le
  obtain ⟨k_min, hk_min⟩ : ∃ n : ℕ, ((1/2 : NNReal)) ^ n < ε :=
    exists_pow_lt_of_lt_one hε_pos h_half_lt_one_nn
  refine ⟨max k_min 2, ?_⟩
  intro k hk ι s T hKT hfull
  have hk_min_le : k_min ≤ k := (Nat.le_max_left _ _).trans hk
  have htwo_le : 2 ≤ k := (Nat.le_max_right _ _).trans hk
  have hhalf_pos : (0 : NNReal) < (1/2 : NNReal) ^ k :=
    pow_pos (by norm_num) k
  have hhalf_le : (1/2 : NNReal) ^ k ≤ (1/2 : NNReal) ^ k_min :=
    pow_le_pow_of_le_one (by positivity) h_half_le_one_nn hk_min_le
  have hhalf_lt_eps : (1/2 : NNReal) ^ k < ε := lt_of_le_of_lt hhalf_le hk_min
  have hmem : (1/2 : NNReal) ^ k ∈ U := hε_subset ⟨hhalf_pos, hhalf_lt_eps.le⟩
  have hquarter : (((1/2 : NNReal) ^ k : NNReal) : ℝ) ≤ 1 / 4 := by
    have hpow : (1/2 : NNReal) ^ k ≤ (1/2 : NNReal) ^ 2 :=
      pow_le_pow_of_le_one (by positivity) h_half_le_one_nn htwo_le
    calc
      (((1/2 : NNReal) ^ k : NNReal) : ℝ) ≤ (((1/2 : NNReal) ^ 2 : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mpr hpow
      _ = 1 / 4 := by norm_num
  have h_coe : (((1/2 : NNReal) ^ k : NNReal) : ℝ) = (1/2 : ℝ) ^ k := by
    push_cast; rfl
  have h_apply := kakeyaEstimateAt_localized hquarter (hU _ hmem) s T hKT hfull
  simp only [h_coe] at h_apply
  exact h_apply


/-- The absolute constant in the separated-direction Katz--Tao inequality in dimension three. -/
def katzTaoSeparatedConstant : ℝ := 1000

/-- **The geometric Katz–Tao inequality.**  For a δ-separated family `{T_ω}_{ω∈Ω}` of `1×δ`-tubes
in `ℝ³`, aligned to their direction `ω`, the tubes whose carrier lies inside a convex body `K`
satisfy `∑_ω vol(T_ω.carrier) ≤ 1000 · vol(K)`.  The proof packs disjoint circular cones, one for
each direction, into the difference body `K - K`. -/
theorem katz_tao_separated_inequality
    (Ω : Finset (EuclideanSpace ℝ (Fin 3)))
    (hΩ_unit : ∀ ω ∈ Ω, ‖ω‖ = 1)
    {δ_sep : ℝ} (_hδ_sep_pos : 0 < δ_sep) (hδ_sep_le : δ_sep ≤ 1)
    (hsep : ∀ ω₁ ∈ Ω, ∀ ω₂ ∈ Ω, ω₁ ≠ ω₂ → δ_sep ≤ dist ω₁ ω₂)
    {δ : NNReal} (hδ_pos : 0 < δ) (hδ_le : (δ : ℝ) ≤ δ_sep)
    (T : (ω : EuclideanSpace ℝ (Fin 3)) → ω ∈ Ω →
      ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (h_align : ∀ ω (hω : ω ∈ Ω), ∃ s : ℝ, 1 ≤ s ∧ s ≤ 2 ∧
        ∀ i : Fin 3, ((T ω hω).y - (T ω hω).x) i = s * ω i)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    ∑ i ∈ Ω.attach with (T i.val i.property).toConvexSpaceBody ≤ K,
        MeasureTheory.volume.real (T i.val i.property).carrier
      ≤ katzTaoSeparatedConstant * MeasureTheory.volume.real K.carrier := by
  classical
  let I := Ω.attach.filter fun i => (T i.val i.property).toConvexSpaceBody ≤ K
  let D : Set (EuclideanSpace ℝ (Fin 3)) := K.carrier - K.carrier
  let C : {ω // ω ∈ Ω} → Set (EuclideanSpace ℝ (Fin 3)) := fun i =>
    Kakeya.IsBesicovitch.CircularCone.cone i.val ((δ : ℝ) / 2)
  change (∑ i ∈ I, MeasureTheory.volume.real (T i.val i.property).carrier) ≤ _
  have hδ_real_pos : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ_pos
  have hδ_real_le_one : (δ : ℝ) ≤ 1 := hδ_le.trans hδ_sep_le
  have hDconv : Convex ℝ D := K.convex.sub K.convex
  obtain ⟨x, hx⟩ := K.nonempty
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ D :=
    ⟨x, hx, x, hx, sub_self x⟩
  have hTiK (i : {ω // ω ∈ Ω}) (hi : i ∈ I) :
      (T i.val i.property).carrier ⊆ K.carrier := by
    have h := (Finset.mem_filter.mp hi).2
    change (T i.val i.property).carrier ⊆ K.carrier at h
    exact h
  by_cases hIempty : I = ∅
  · rw [hIempty]
    simp only [Finset.sum_empty]
    unfold katzTaoSeparatedConstant
    positivity
  have hIne : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hIempty
  obtain ⟨i0, hi0⟩ := hIne
  have hballK : Metric.closedBall (T i0.val i0.property).x (δ : ℝ) ⊆ K.carrier :=
    ((T i0.val i0.property).toTube.closedBall_subset_carrier_of_mem_segment
      (left_mem_segment ℝ _ _)).trans (hTiK i0 hi0)
  have hKvol : MeasureTheory.volume K.carrier ≠ 0 := by
    apply ne_of_gt
    exact (Metric.measure_closedBall_pos MeasureTheory.volume _ hδ_real_pos).trans_le
      (MeasureTheory.measure_mono hballK)
  have hcone_sub (i : {ω // ω ∈ Ω}) (hi : i ∈ I) : C i ⊆ D := by
    apply Kakeya.IsBesicovitch.CircularCone.cone_subset_convex (hΩ_unit i.val i.property) hDconv
      hzero
    have hclosed := closedBall_aligned_two_mul_subset_sub
      (T i.val i.property).toTube K (hΩ_unit i.val i.property)
      (h_align i.val i.property) (hTiK i hi)
    intro z hz
    apply hclosed
    rw [Metric.mem_closedBall]
    have hzdist : dist z i.val < (δ : ℝ) / 2 := by
      simpa [Metric.mem_ball] using hz
    linarith
  have hcones_disj : Set.PairwiseDisjoint (↑I) C := by
    intro i hi j hj hij
    apply Kakeya.IsBesicovitch.CircularCone.disjoint_cone
      (hΩ_unit i.val i.property) (hΩ_unit j.val j.property)
    · exact hδ_le.trans (hsep i.val i.property j.val j.property fun h => hij (Subtype.ext h))
    · linarith
  have hDcompact : IsCompact D := by
    change IsCompact (K.carrier - K.carrier)
    rw [sub_eq_add_neg]
    exact K.isCompact.add K.isCompact.neg
  have hCfin (i : {ω // ω ∈ Ω}) (hi : i ∈ I) :
      MeasureTheory.volume (C i) ≠ ⊤ :=
    ne_top_of_le_ne_top hDcompact.measure_ne_top
      (MeasureTheory.measure_mono (hcone_sub i hi))
  have hunion : (⋃ i ∈ I, C i) ⊆ D := Set.iUnion₂_subset hcone_sub
  have hcones_sum_le :
      (∑ i ∈ I, MeasureTheory.volume.real (C i)) ≤ MeasureTheory.volume.real D := by
    rw [← MeasureTheory.measureReal_biUnion_finset hcones_disj
      (fun i _ => Kakeya.IsBesicovitch.CircularCone.measurableSet_cone i.val ((δ : ℝ) / 2)) hCfin]
    exact MeasureTheory.measureReal_mono hunion hDcompact.measure_ne_top
  have hTubeCone (i : {ω // ω ∈ Ω}) (hi : i ∈ I) :
      MeasureTheory.volume.real (T i.val i.property).carrier ≤
        36 * MeasureTheory.volume.real (C i) := by
    rw [Kakeya.IsBesicovitch.CircularCone.volume_real_cone_half (by simp)
      (hΩ_unit i.val i.property) hδ_real_pos.le]
    calc
      MeasureTheory.volume.real (T i.val i.property).carrier ≤
          3 * Real.pi * (δ : ℝ) ^ 2 :=
        tube_volume_real_le_three_pi hδ_real_le_one (T i.val i.property).toTube
      _ = 36 * (Real.pi * (δ : ℝ) ^ 2 / 12) := by ring
  have hsum_le_D :
      (∑ i ∈ I, MeasureTheory.volume.real (T i.val i.property).carrier) ≤
        36 * MeasureTheory.volume.real D := by
    calc
      _ ≤ ∑ i ∈ I, 36 * MeasureTheory.volume.real (C i) := by
        exact Finset.sum_le_sum fun i hi => hTubeCone i hi
      _ = 36 * ∑ i ∈ I, MeasureTheory.volume.real (C i) := by
        rw [Finset.mul_sum]
      _ ≤ 36 * MeasureTheory.volume.real D :=
        mul_le_mul_of_nonneg_left hcones_sum_le (by norm_num)
  have hD := Kakeya.IsBesicovitch.volumeReal_difference_le_explicit K.isCompact K.convex hKvol
  change 37269 * MeasureTheory.volume.real D ≤
    1000000 * MeasureTheory.volume.real K.carrier at hD
  have hfinal : 36 * MeasureTheory.volume.real D ≤
      1000 * MeasureTheory.volume.real K.carrier := by
    have hDnonneg : 0 ≤ MeasureTheory.volume.real D := MeasureTheory.measureReal_nonneg
    have hKnonneg : 0 ≤ MeasureTheory.volume.real K.carrier :=
      MeasureTheory.measureReal_nonneg
    nlinarith
  unfold katzTaoSeparatedConstant
  exact hsum_le_D.trans hfinal

/-- **Genuine geometric Katz–Tao bound** for δ-separated `1×δ`-tubes in
`ℝ³` with carriers in `B̄(0,1)`. The Katz–Tao constant `C₀ = 1000` is
*absolute*: it depends only on the dimension `3`, not on `δ`, `δ_sep`,
`Ω`, or the choice of tube family `T`. -/
theorem B7_5_isKatzTao_v2
    (Ω : Finset (EuclideanSpace ℝ (Fin 3)))
    (hΩ_unit : ∀ ω ∈ Ω, ‖ω‖ = 1)
    {δ_sep : ℝ} (hδ_sep_pos : 0 < δ_sep) (hδ_sep_le : δ_sep ≤ 1)
    (hsep : ∀ ω₁ ∈ Ω, ∀ ω₂ ∈ Ω, ω₁ ≠ ω₂ → δ_sep ≤ dist ω₁ ω₂)
    {δ : NNReal} (hδ_pos : 0 < δ) (hδ_le : (δ : ℝ) ≤ δ_sep)
    (T : (ω : EuclideanSpace ℝ (Fin 3)) → ω ∈ Ω →
      ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (h_align : ∀ ω (hω : ω ∈ Ω), ∃ s : ℝ, 1 ≤ s ∧ s ≤ 2 ∧
        ∀ i : Fin 3, ((T ω hω).y - (T ω hω).x) i = s * ω i) :
    ConvexSpaceBody.IsKatzTao (Ω.attach) (fun i => (T i.val i.property).toConvexSpaceBody)
      (1000 : ℝ≥0∞) := by
  classical
  set W : {x // x ∈ Ω} → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => (T i.val i.property).toConvexSpaceBody with hW_def
  change Kakeya.maxDensity (Ω.attach) W ≤ (1000 : ℝ≥0∞)
  set t := Kakeya.density_maximizer (Ω.attach) W with ht_def
  have ht_sub : t ⊆ Ω.attach := Kakeya.density_maximizer_subset (Ω.attach) W
  unfold Kakeya.maxDensity
  rw [← ht_def]
  unfold Kakeya.densityInConvexHulliUnion
  by_cases ht_empty : t = ∅
  · simp [ht_empty]
  · have ht_ne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
    set K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := t.convexHull_biUnion W with hK_def
    have hK_carrier :
        K.carrier = Convexity.convexHull ℝ (⋃ i ∈ t, (W i).carrier) :=
      ht_ne.convexHull_biUnion_carrier W
    have h_sub_K : ∀ i ∈ t, W i ≤ K := fun i hi =>
      Finset.le_convexHull_biUnion W hi
    have hWi_top : ∀ i, MeasureTheory.volume (W i).carrier ≠ ⊤ := fun i =>
      (W i).isCompact.measure_ne_top
    have hK_top : MeasureTheory.volume K.carrier ≠ ⊤ :=
      K.isCompact.measure_ne_top
    have h_real := katz_tao_separated_inequality Ω hΩ_unit hδ_sep_pos hδ_sep_le
      hsep hδ_pos hδ_le T h_align K
    have hfilter_eq : (Ω.attach).filter (fun i => W i ≤ K) = (Ω.attach).filter
        (fun i => (T i.val i.property).toConvexSpaceBody ≤ K) := rfl
    have h_sum_e :
        (∑ i ∈ (Ω.attach).filter (fun i => W i ≤ K),
            MeasureTheory.volume (W i).carrier)
          = ENNReal.ofReal
              (∑ i ∈ (Ω.attach).filter
                  (fun i => (T i.val i.property).toConvexSpaceBody ≤ K),
                MeasureTheory.volume.real (T i.val i.property).carrier) := by
      rw [hfilter_eq,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => MeasureTheory.measureReal_nonneg)]
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal (hWi_top i)]
    have h_K_e : MeasureTheory.volume K.carrier
        = ENNReal.ofReal (MeasureTheory.volume.real K.carrier) :=
      (ENNReal.ofReal_toReal hK_top).symm
    have h_1000_e : (1000 : ℝ≥0∞) = ENNReal.ofReal 1000 := by
      rw [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
      norm_num
    have h_sum_le :
        (∑ i ∈ (Ω.attach).filter (fun i => W i ≤ K),
            MeasureTheory.volume (W i).carrier)
          ≤ (1000 : ℝ≥0∞) * MeasureTheory.volume K.carrier := by
      rw [h_sum_e, h_K_e, h_1000_e,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1000)]
      exact ENNReal.ofReal_le_ofReal h_real
    have ht_sub_attach :
        t ⊆ (Ω.attach).filter (fun i => W i ≤ K) := by
      intro i hi
      simp only [Finset.mem_filter]
      exact ⟨ht_sub hi, h_sub_K i hi⟩
    have h_t_sum_le :
        (∑ i ∈ t, MeasureTheory.volume (W i).carrier)
          ≤ ∑ i ∈ (Ω.attach).filter (fun i => W i ≤ K),
              MeasureTheory.volume (W i).carrier :=
      Finset.sum_le_sum_of_subset ht_sub_attach
    have h_hull_eq :
        MeasureTheory.volume (Convexity.convexHull ℝ (⋃ i ∈ t, (W i).carrier))
          = MeasureTheory.volume K.carrier := by rw [hK_carrier]
    rw [h_hull_eq]
    exact ENNReal.div_le_of_le_mul (h_t_sum_le.trans h_sum_le)

end Kakeya.IsBesicovitch
