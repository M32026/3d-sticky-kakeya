/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.RandomTranslation.EDChernoffNet
public import Kakeya.RandomTranslation.ScaledCounting
public import Kakeya.Tube.EDPacking.IntersectionVolume
public import Kakeya.Discretization
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Random-translation refinement at a single scale (GWZ Lemma 7.6)

`Kakeya.RandomTranslation.exists_refinement` is the single-scale form of GWZ
Lemma 7.6 in which the caller controls the failure budget: the statement exposes
the underlying probability space, a measurable bad set whose measure is at most
the caller's `ε_budget`, and a deterministic refinement on the complement of that
bad set.

Callers needing this form (e.g., `Kakeya/Sticky.lean`'s parent-level
union-bound construction) import this file directly.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory
open Kakeya.Tube

namespace Kakeya.RandomTranslation

universe u

/-- Polylog `M_cap` bound chain from `exists_refinement`, extracted to keep the
main theorem inside the default heartbeat budget. The proof is pure linear
arithmetic combining the ceiling bounds for `M_log_term`, `M_const`, the
`-log δ ≤ δ^(-ε)/ε` inequality, and the two `Cε` envelope bounds. -/
private lemma M_cap_le_of_log_chain
    (M_dim_R M_log_term_R M_const_R M_cap_R : ℝ)
    (δr ε εbR A Cε netM netC : ℝ)
    (hM_dim_nn : 0 ≤ M_dim_R)
    (hδr_pos : 0 < δr) (hδr_le_one : δr ≤ 1)
    (hε : 0 < ε)
    (hεbR_pos : 0 < εbR) (hεbR_lt_one : εbR < 1)
    (hnetM_pos : 0 < netM) (hnetC_pos : 0 < netC)
    (hcast_eq : M_cap_R + 1 =
        M_dim_R * M_dim_R + M_dim_R * M_log_term_R +
          M_dim_R * M_const_R + M_dim_R + 1)
    (hM_log_term_le : M_log_term_R ≤ netM * Real.log (1 / δr) + 1)
    (hM_const_le : M_const_R ≤
        10 * Real.exp 1 + Real.log (3 * netC + 1) +
          Real.log (1 / εbR) + 1)
    (hCε_sub : M_dim_R * M_dim_R + M_dim_R * (netM / ε)
        + M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2)
        + 2 * M_dim_R + 1 ≤ Cε)
    (hM_dim_le_Cε : M_dim_R ≤ Cε)
    (hA_bound : Cε * (δr ^ (-ε) + Real.log (1 / εbR)) ≤ A) :
    M_cap_R + 1 ≤ A := by
  set X : ℝ := δr ^ (-ε) with hX_def
  set L : ℝ := Real.log (1 / εbR) with hL_def
  have hX_pos : 0 < X := Real.rpow_pos_of_pos hδr_pos _
  have hX_ge_one : 1 ≤ X := by
    rw [hX_def, Real.rpow_neg hδr_pos.le, one_le_inv_iff₀]
    exact ⟨Real.rpow_pos_of_pos hδr_pos ε,
      Real.rpow_le_one hδr_pos.le hδr_le_one hε.le⟩
  have hL_nn : 0 ≤ L := by
    rw [hL_def, Real.log_div one_ne_zero (ne_of_gt hεbR_pos), Real.log_one,
        zero_sub, neg_nonneg]
    exact Real.log_nonpos hεbR_pos.le hεbR_lt_one.le
  have h_neglog_le : -Real.log δr ≤ δr ^ (-ε) / ε := by
    have hrpow_eq : δr ^ (-ε) = Real.exp (-ε * Real.log δr) := by
      rw [Real.rpow_def_of_pos hδr_pos]; congr 1; ring
    have h_exp_ge : 1 + (-ε * Real.log δr) ≤ Real.exp (-ε * Real.log δr) :=
      by linarith [Real.add_one_le_exp (-ε * Real.log δr)]
    have hrearr : -ε * Real.log δr = ε * (-Real.log δr) := by ring
    have h_ε_log : ε * (-Real.log δr) ≤ δr ^ (-ε) := by
      rw [hrpow_eq, ← hrearr]; linarith
    rw [le_div_iff₀ hε]; linarith
  have hlog_inv_eq : Real.log (1 / δr) = -Real.log δr := by
    rw [Real.log_div one_ne_zero (ne_of_gt hδr_pos), Real.log_one, zero_sub]
  have h_dim_log_term :
      M_dim_R * M_log_term_R ≤
        M_dim_R * (netM / ε) * X + M_dim_R := by
    have step1 : M_dim_R * M_log_term_R ≤
        M_dim_R * (netM * Real.log (1 / δr) + 1) :=
      mul_le_mul_of_nonneg_left hM_log_term_le hM_dim_nn
    have hrhs_eq : netM * Real.log (1 / δr) = netM * (-Real.log δr) := by
      rw [hlog_inv_eq]
    have h_bound : netM * (-Real.log δr) ≤ netM / ε * X := by
      have h1 : netM * (-Real.log δr) ≤ netM * (δr ^ (-ε) / ε) :=
        mul_le_mul_of_nonneg_left h_neglog_le hnetM_pos.le
      have h2 : netM * (δr ^ (-ε) / ε) = netM / ε * δr ^ (-ε) := by ring
      rw [hX_def]; linarith
    have step2 : M_dim_R * (netM * Real.log (1 / δr) + 1) ≤
        M_dim_R * (netM / ε * X + 1) := by
      apply mul_le_mul_of_nonneg_left _ hM_dim_nn
      rw [hrhs_eq]; linarith
    have step3 : M_dim_R * (netM / ε * X + 1) =
        M_dim_R * (netM / ε) * X + M_dim_R := by ring
    linarith
  have h_dim_const_term :
      M_dim_R * M_const_R ≤
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 1)
          + M_dim_R * L := by
    have step1 : M_dim_R * M_const_R ≤
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1)
          + L + 1) :=
      mul_le_mul_of_nonneg_left hM_const_le hM_dim_nn
    have step2 : M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) +
          L + 1) =
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 1)
          + M_dim_R * L := by ring
    linarith
  have hM_dim_sq_nn : 0 ≤ M_dim_R * M_dim_R := mul_nonneg hM_dim_nn hM_dim_nn
  have hnetM_div_nn : 0 ≤ netM / ε := div_nonneg hnetM_pos.le hε.le
  have hMdim_div_nn : 0 ≤ M_dim_R * (netM / ε) := mul_nonneg hM_dim_nn hnetM_div_nn
  have hlog3C_nn : 0 ≤ Real.log (3 * netC + 1) := by
    apply Real.log_nonneg; linarith
  have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
  have hMdim_const_nn : 0 ≤ M_dim_R *
      (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2) :=
    mul_nonneg hM_dim_nn (by linarith)
  have h_2mdim_nn : 0 ≤ 2 * M_dim_R := by linarith
  have hLHS_X :
      M_dim_R * M_dim_R + M_dim_R * (netM / ε) * X +
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2)
        + 2 * M_dim_R + 1 ≤ Cε * X := by
    have h_mdim_sq_X : M_dim_R * M_dim_R ≤ M_dim_R * M_dim_R * X := by
      have := mul_le_mul_of_nonneg_left hX_ge_one hM_dim_sq_nn; linarith
    have h_mdim_const_X :
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2) ≤
          M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2) * X := by
      have := mul_le_mul_of_nonneg_left hX_ge_one hMdim_const_nn; linarith
    have h_2mdim_X : 2 * M_dim_R ≤ 2 * M_dim_R * X := by
      have := mul_le_mul_of_nonneg_left hX_ge_one h_2mdim_nn; linarith
    have h_one_X : (1 : ℝ) ≤ 1 * X := by linarith
    have hsumX : M_dim_R * M_dim_R * X +
        M_dim_R * (netM / ε) * X +
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2) * X
        + 2 * M_dim_R * X + 1 * X =
      (M_dim_R * M_dim_R + M_dim_R * (netM / ε) +
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2)
        + 2 * M_dim_R + 1) * X := by ring
    have hsumX_le : (M_dim_R * M_dim_R + M_dim_R * (netM / ε) +
        M_dim_R * (10 * Real.exp 1 + Real.log (3 * netC + 1) + 2)
        + 2 * M_dim_R + 1) * X ≤ Cε * X :=
      mul_le_mul_of_nonneg_right hCε_sub hX_pos.le
    linarith [h_mdim_sq_X, h_mdim_const_X, h_2mdim_X, h_one_X, hsumX, hsumX_le]
  have hLHS_L : M_dim_R * L ≤ Cε * L :=
    mul_le_mul_of_nonneg_right hM_dim_le_Cε hL_nn
  have h_expand : Cε * (X + L) = Cε * X + Cε * L := by ring
  rw [hcast_eq]
  linarith [h_dim_log_term, h_dim_const_term, hLHS_X, hLHS_L, hA_bound,
    h_expand]

/-- Cthickening-by-1 of `closedBall 0 5` lies in `closedBall 0 6`. Carrier inclusion for the
bodies of the hoisted density net, which is taken at radius `5` so that it also covers the
translated family. -/
private lemma cthickening_carrier_subset_closedBall_six
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [ProperSpace E] (K : ConvexSpaceBody E)
    (hKle : K ≤ ConvexSpaceBody.cthickening 1
      (ConvexSpaceBody.closedBall (0 : E) (5 : ℝ) (by norm_num))) :
    K.carrier ⊆ Metric.closedBall (0 : E) 6 := by
  intro x hx
  have hx_mem : x ∈ Metric.cthickening 1
      (ConvexSpaceBody.closedBall (0 : E) (5 : ℝ) (by norm_num)).carrier := hKle hx
  rw [ConvexSpaceBody.closedBall_carrier,
      cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 5)] at hx_mem
  rw [Metric.mem_closedBall, dist_zero_right]
  have : ‖x‖ ≤ 1 + 5 := by rwa [Metric.mem_closedBall, dist_zero_right] at hx_mem
  linarith

/-- `tubeContainedSet` is closed (hence measurable) whenever the target
set `K` is closed: it is the intersection over `x ∈ T.carrier` of the
closed preimages `{t | t + x ∈ K}`. Used in both the per-net-tube and
per-Frostman-K Chernoff measurability blocks. (extracted by Fuse golfer) -/
private lemma isClosed_tubeContainedSet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {δ : NNReal}
    (T₁ : Tube δ E) (K : Set E) (hK_closed : IsClosed K) :
    IsClosed (HasUniformTranslation.tubeContainedSet (Ω := E) T₁ K) := by
  have hset_eq :
      HasUniformTranslation.tubeContainedSet (Ω := E) T₁ K =
        ⋂ x ∈ T₁.carrier, {t : E | t + x ∈ K} := by
    ext t
    simp only [HasUniformTranslation.tubeContainedSet, Set.mem_setOf_eq,
      Translation.actSet, Set.image_subset_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h x hx => h hx, fun h x hx => h x hx⟩
  rw [hset_eq]
  exact isClosed_biInter fun x _ =>
    hK_closed.preimage (continuous_id.add continuous_const)

/-- The "outside the unit ball" event in `(Fin J → E)`: measurability and
zero-measure under the product uniform-ball measure. -/
private lemma measure_badOut_eq_zero
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (J : ℕ) :
    MeasurableSet { ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1 } ∧
    HasUniformTranslation.productMeasure E E J
      { ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1 } = 0 := by
  have hBall_compl_meas :
      MeasurableSet ((Metric.closedBall (0 : E) 1)ᶜ) :=
    Metric.isClosed_closedBall.measurableSet.compl
  have hUnion_eq :
      { ω : Fin J → E | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1 } =
        ⋃ j : Fin J, {ω : Fin J → E | ω j ∉ Metric.closedBall (0 : E) 1} := by
    ext ω; simp
  have hpre : ∀ j : Fin J,
      {ω : Fin J → E | ω j ∉ Metric.closedBall (0 : E) 1} =
        (Function.eval j : (Fin J → E) → E) ⁻¹'
          ((Metric.closedBall (0 : E) 1)ᶜ) := by
    intro j; ext ω; simp [Function.eval]
  refine ⟨?_, ?_⟩
  · rw [hUnion_eq]
    refine MeasurableSet.iUnion fun j => ?_
    rw [hpre j]
    exact (measurable_pi_apply j) hBall_compl_meas
  · rw [hUnion_eq]
    refine measure_iUnion_null_iff.mpr fun j => ?_
    rw [hpre j,
        ← MeasureTheory.Measure.map_apply (measurable_pi_apply j) hBall_compl_meas,
        HasUniformTranslation.productMeasure_map_eval]
    change uniformBallMeasure E ((Metric.closedBall (0 : E) 1)ᶜ) = 0
    unfold uniformBallMeasure
    rw [Measure.smul_apply, Measure.restrict_apply hBall_compl_meas]
    simp

/-- Standard Chernoff tail wrapper used by both the per-T₀ ED-Chernoff
and per-K Frostman-density-Chernoff blocks of `exists_refinement`. Calling
`productTubeContainedCount_chernoff_tail_scaledM_general` at
`S := A * M` and simplifying `A * M / M = A` collapses the exponent to
`exp(10·e - A)`. -/
private lemma chernoff_badCount_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {ι : Type u} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (hxT : ∀ i ∈ s, (T i).x ∈ (T i).carrier)
    {K : Set E} (hK_meas : MeasurableSet K) (hK_top : volume K ≠ ⊤)
    (hMeas : ∀ i ∈ s,
        MeasurableSet (HasUniformTranslation.tubeContainedSet (Ω := E) (T i) K))
    {J : ℕ} [NeZero J] (M : ℝ) (hM_pos : 0 < M)
    (hXM : ∀ j ω,
        (HasUniformTranslation.productTubeContainedCount (Ω := E) s T K J j ω : ℝ)
          ≤ M)
    (hJmM : (J : ℝ) *
        (@HasUniformTranslation.uniformConstant E _ E _ _ _ _ _
            (instHasUniformTranslationSelf E) *
          (s.card : ℝ) * volume.real K) < M)
    (A : ℝ) :
    (HasUniformTranslation.productMeasure E E J
        { ω : Fin J → E | A * M <
            ∑ j : Fin J, HasUniformTranslation.productTubeContainedCount
              (Ω := E) s T K J j ω }).toReal ≤
      Real.exp (10 * Real.exp 1 - A) := by
  have hChernoff :=
    HasUniformTranslation.productTubeContainedCount_chernoff_tail_scaledM_general
      (Ω := E) (E := E) (δ := δ) s T (fun i => (T i).x) hxT
      hK_meas hK_top hMeas (J := J) M hM_pos hXM hJmM (A * M)
  have hexp_eq : Real.exp (10 * Real.exp 1 - A * M / M) =
      Real.exp (10 * Real.exp 1 - A) := by
    congr 1; field_simp
  rw [hexp_eq] at hChernoff
  exact hChernoff

/-- Scaled analogue of `chernoff_badCount_le`.  Applies
`scaledProductTubeContainedCount_chernoff_tail` at `S := A * M`, collapsing the exponent to
`exp(10·e - A)`.  Unlike the unscaled version the mean is controlled by the sharp per-tube
probability `probConst E r * vol K`, so `hJmM` is GWZ's total-volume calibration. -/
private lemma chernoff_scaled_badCount_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {ι : Type u} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) {r : ℝ} (hr_pos : 0 < r)
    (hMeas : ∀ i ∈ s, MeasurableSet (scaledTubeContainedSet r (T i) K.carrier))
    {J : ℕ} [NeZero J] (M : ℝ) (hM_pos : 0 < M)
    (hXM : ∀ t : E, scaledTubeContainedCount r s T K.carrier t ≤ M)
    (hJmM : (J : ℝ) * ((s.card : ℝ) * (probConst E r * volume.real K.carrier)) < M)
    (A : ℝ) :
    (HasUniformTranslation.productMeasure E E J
        { ω : Fin J → E | A * M <
            ∑ j : Fin J, scaledProductTubeContainedCount r s T K.carrier J j ω }).toReal ≤
      Real.exp (10 * Real.exp 1 - A) := by
  have hChernoff :=
    scaledProductTubeContainedCount_chernoff_tail
      s T K hr_pos hMeas (J := J) M hM_pos hXM
      (by
        simpa [probConst] using hJmM)
      (A * M)
  have hexp_eq : Real.exp (10 * Real.exp 1 - A * M / M) =
      Real.exp (10 * Real.exp 1 - A) := by
    congr 1; field_simp
  rw [hexp_eq] at hChernoff
  exact hChernoff

/-- The scaled count is the cardinality of the corresponding filter. -/
private lemma scaledTubeContainedCount_eq_filter_card
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type u} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (r : ℝ) (t : E) :
    scaledTubeContainedCount r s T K.carrier t
      = ((s.filter (fun i => ((T i).translate (r • t)).toConvexSpaceBody ≤ K)).card : ℝ) := by
  classical
  unfold scaledTubeContainedCount
  have hind : ∀ i ∈ s,
      (scaledTubeContainedSet r (T i) K.carrier).indicator (fun _ : E => (1 : ℝ)) t =
      if t ∈ scaledTubeContainedSet r (T i) K.carrier then (1 : ℝ) else 0 := by
    intro i _
    by_cases ht : t ∈ scaledTubeContainedSet r (T i) K.carrier
    · rw [Set.indicator_of_mem ht, if_pos ht]
    · rw [Set.indicator_of_notMem ht, if_neg ht]
  rw [Finset.sum_congr rfl hind, Finset.sum_boole]
  have hfilter_eq : s.filter (fun i => t ∈ scaledTubeContainedSet r (T i) K.carrier) =
      s.filter (fun i => ((T i).translate (r • t)).toConvexSpaceBody ≤ K) := by
    refine Finset.filter_congr ?_
    intro i hi
    unfold scaledTubeContainedSet
    rfl
  rw [hfilter_eq]

/-- Summing the scaled count over the `J` translations counts the pairs of the product family. -/
private lemma sum_scaledProductTubeContainedCount_eq_filter_card
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type u} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (K : ConvexSpaceBody E) (r : ℝ) {J : ℕ} (ω : Fin J → E) :
    (∑ j : Fin J, scaledProductTubeContainedCount r s T K.carrier J j ω)
      = (((s ×ˢ (Finset.univ : Finset (Fin J))).filter
            (fun p => ((T p.1).translate (r • ω p.2)).toConvexSpaceBody ≤ K)).card : ℝ) := by
  classical
  simp_rw [scaledProductTubeContainedCount, scaledTubeContainedCount_eq_filter_card]
  rw [Finset.natCast_card_filter (s := s ×ˢ (Finset.univ : Finset (Fin J)))]
  rw [Finset.sum_product_right]
  simp_rw [Finset.natCast_card_filter]

/-- **Count-to-density conversion for a single test body.**  If at most `N` members of the
translated product family fit inside `K`, then the density of the family in `K` is at most
`N · |T_δ^{ub}| / |K|`, and if `K` cannot contain a single tube the density is `0`.  With the
Chernoff cap the `|K|` cancels and `A · M_dens · K_vol` is left, with no `J` anywhere. -/
private lemma densityIn_le_of_count
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    {ι : Type u} {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) (hδ_le : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E) {J : ℕ} (v : Fin J → E)
    (K : ConvexSpaceBody E) (M_dens A : ℝ) (hM_dens_one : 1 ≤ M_dens) (hA_one : 1 ≤ A)
    (hcount : (((s ×ˢ (Finset.univ : Finset (Fin J))).filter
          (fun p => ((T p.1).translate (v p.2)).toConvexSpaceBody ≤ K)).card : ℝ)
        ≤ A * max (M_dens * volume.real K.carrier /
          ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
            (δ : ℝ) ^ (Module.finrank ℝ E - 1))) 1) :
    densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p => ((T p.1).translate (v p.2)).toConvexSpaceBody) K
      ≤ ENNReal.ofReal (A * M_dens *
          ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
            (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set V_lb : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
    (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hV_lb_def
  set V_ub : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
    (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hV_ub_def
  set vK : ℝ := volume.real K.carrier with hvK_def
  have hV_lb_pos : 0 < V_lb := by
    rw [hV_lb_def]
    exact mul_pos (by exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E))
      (pow_pos hδ_pos _)
  have hV_ub_pos : 0 < V_ub := by rw [hV_ub_def]; positivity
  have hK_ne_top : volume K.carrier ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hK_toReal : ENNReal.ofReal vK = volume K.carrier :=
    ENNReal.ofReal_toReal hK_ne_top
  have hvol_translate : ∀ (i : ι) (w : E),
      volume.real ((T i).translate w).carrier = volume.real (T i).carrier := by
    intro i w
    rw [Tube.translate_carrier]
    unfold MeasureTheory.Measure.real
    congr 1
    exact MeasureTheory.measure_preimage_add volume _ _
  set u : Finset (ι × Fin J) := s ×ˢ (Finset.univ : Finset (Fin J)) with hu_def
  set W : ι × Fin J → ConvexSpaceBody E :=
    fun p => ((T p.1).translate (v p.2)).toConvexSpaceBody with hW_def
  have hV_ub_div : V_ub / V_lb = ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) := by
    rw [hV_ub_def, hV_lb_def, hn_def]
    field_simp
  have hcard_nonneg : 0 ≤ ((u.filter (fun p => W p ≤ K)).card : ℝ) := by
    exact Nat.cast_nonneg _
  rw [densityIn_le_iff]
  by_cases hvK_lt_V_lb : vK < V_lb
  · have hfilter_empty : u.filter (fun p => W p ≤ K) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro p hp hWp_le_K
      have hcarrier : (W p).carrier ⊆ K.carrier := hWp_le_K
      have hvol_real : volume.real (W p).carrier ≤ vK :=
        MeasureTheory.measureReal_mono hcarrier hK_ne_top
      have h_vol_real_T : volume.real ((T p.1).translate (v p.2)).carrier =
          volume.real (T p.1).carrier :=
        hvol_translate p.1 (v p.2)
      have h_vol_real_lb : V_lb ≤ volume.real ((T p.1).translate (v p.2)).carrier := by
        rw [h_vol_real_T]
        change V_lb ≤ (volume ((T p.1).toConvexSpaceBody : Set E)).toReal
        have h := Tube.le_volume (T p.1)
        have hreal := ENNReal.toReal_mono (T p.1).isCompact.measure_lt_top.ne h
        simpa [hV_lb_def, Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.coe_toReal] using hreal
      have hW_carrier_eq : (W p).carrier = ((T p.1).translate (v p.2)).carrier := rfl
      rw [hW_carrier_eq] at hvol_real
      have : V_lb ≤ vK := le_trans h_vol_real_lb hvol_real
      linarith
    have hsum_empty : ∑ p ∈ u.filter (fun p => W p ≤ K), volume (W p).carrier = 0 := by
      simp [hfilter_empty]
    have hC_nonneg : 0 ≤ ENNReal.ofReal (A * M_dens *
        ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
          (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))) := by
      positivity
    rw [hsum_empty]
    exact mul_nonneg (by positivity) (by positivity)
  · push Not at hvK_lt_V_lb
    have hV_lb_le_vK : V_lb ≤ vK := hvK_lt_V_lb
    have h_div_ge_one : 1 ≤ M_dens * vK / V_lb := by
      have h1 : 1 ≤ vK / V_lb := by
        refine (one_le_div hV_lb_pos).mpr ?_
        exact hV_lb_le_vK
      have h2 : 1 ≤ M_dens := hM_dens_one
      have h3 : 1 ≤ M_dens * (vK / V_lb) := by
        nlinarith
      calc
        (1 : ℝ) ≤ M_dens * (vK / V_lb) := h3
        _ = M_dens * vK / V_lb := by ring
    have hmax_eq : max (M_dens * vK / V_lb) 1 = M_dens * vK / V_lb :=
      max_eq_left h_div_ge_one
    have hcount' : ((u.filter (fun p => W p ≤ K)).card : ℝ) ≤ A * (M_dens * vK / V_lb) := by
      rw [hmax_eq] at hcount
      simpa [hu_def, hW_def, hvK_def] using hcount
    have hcard_ennreal : ((u.filter (fun p => W p ≤ K)).card : ENNReal) ≤
        ENNReal.ofReal (A * (M_dens * vK / V_lb)) := by
      calc
        ((u.filter (fun p => W p ≤ K)).card : ENNReal) =
            ENNReal.ofReal ((u.filter (fun p => W p ≤ K)).card : ℝ) := by
          exact (ENNReal.ofReal_natCast _).symm
        _ ≤ ENNReal.ofReal (A * (M_dens * vK / V_lb)) :=
          ENNReal.ofReal_le_ofReal hcount'
    have hvol_bound : ∀ p ∈ u.filter (fun p => W p ≤ K),
        volume (W p).carrier ≤ ENNReal.ofReal V_ub := by
      intro p hp
      have hp_mem : p ∈ u := Finset.mem_filter.mp hp |>.left
      have hvol_real_T : volume.real ((T p.1).translate (v p.2)).carrier =
          volume.real (T p.1).carrier :=
        hvol_translate p.1 (v p.2)
      have hvol_real_ub : volume.real ((T p.1).translate (v p.2)).carrier ≤ V_ub := by
        rw [hvol_real_T]
        have h := Tube.volume_le hδ_le (T p.1)
        have hRHS_ne_top :
            (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
                (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
        have hreal := ENNReal.toReal_mono hRHS_ne_top h
        simpa [hV_ub_def, Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.coe_toReal] using hreal
      have hvol_ennreal : volume ((T p.1).translate (v p.2)).carrier ≤ ENNReal.ofReal V_ub := by
        have htop : volume ((T p.1).translate (v p.2)).carrier ≠ ⊤ :=
          ((T p.1).translate (v p.2)).isCompact.measure_lt_top.ne
        calc
          volume ((T p.1).translate (v p.2)).carrier =
              ENNReal.ofReal (volume.real ((T p.1).translate (v p.2)).carrier) :=
            (ENNReal.ofReal_toReal htop).symm
          _ ≤ ENNReal.ofReal V_ub := ENNReal.ofReal_le_ofReal hvol_real_ub
      simpa [hW_def] using hvol_ennreal
    have hsum : ∑ p ∈ u.filter (fun p => W p ≤ K), volume (W p).carrier ≤
        ((u.filter (fun p => W p ≤ K)).card : ENNReal) * ENNReal.ofReal V_ub := by
      calc
        ∑ p ∈ u.filter (fun p => W p ≤ K), volume (W p).carrier
            ≤ ∑ p ∈ u.filter (fun p => W p ≤ K), ENNReal.ofReal V_ub :=
          Finset.sum_le_sum hvol_bound
        _ = ((u.filter (fun p => W p ≤ K)).card : ENNReal) * ENNReal.ofReal V_ub := by
          simp [Finset.sum_const, nsmul_eq_mul]
    have hsum' : ∑ p ∈ u.filter (fun p => W p ≤ K), volume (W p).carrier ≤
        ENNReal.ofReal (A * (M_dens * vK / V_lb)) * ENNReal.ofReal V_ub :=
      hsum.trans (mul_le_mul_left hcard_ennreal (ENNReal.ofReal V_ub))
    have h_real_eq : (A * (M_dens * vK / V_lb)) * V_ub = A * M_dens * (V_ub / V_lb) * vK := by
      field_simp [hV_lb_pos.ne']
    have h_nonneg_V_ub : 0 ≤ V_ub := hV_ub_pos.le
    have h_nonneg_A : 0 ≤ A := by linarith
    have h_nonneg_M_dens : 0 ≤ M_dens := by linarith
    have h_nonneg_vK : 0 ≤ vK := ENNReal.toReal_nonneg
    have h_nonneg_product : 0 ≤ A * (M_dens * vK / V_lb) := by
      positivity
    have h_real_eq' : (A * (M_dens * vK / V_lb)) * V_ub =
          A * M_dens * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) * vK := by
      calc
        (A * (M_dens * vK / V_lb)) * V_ub = A * M_dens * (V_ub / V_lb) * vK := h_real_eq
        _ = A * M_dens * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) * vK := by
          rw [hV_ub_div]
    have h_nonneg_a : 0 ≤ A * M_dens * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) := by
      positivity
    have h_nonneg_RHS : 0 ≤ A * M_dens *
          ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) * vK := by
      positivity
    calc
      ∑ p ∈ u.filter (fun p => W p ≤ K), volume (W p).carrier
          ≤ ENNReal.ofReal (A * (M_dens * vK / V_lb)) *
              ENNReal.ofReal V_ub := hsum'
      _ = ENNReal.ofReal ((A * (M_dens * vK / V_lb)) * V_ub) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * (M_dens * vK / V_lb))]
      _ = ENNReal.ofReal (A * M_dens *
          ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) * vK) := by
        rw [h_real_eq']
      _ = ENNReal.ofReal (A * M_dens * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))) *
          ENNReal.ofReal vK := by
        rw [← ENNReal.ofReal_mul h_nonneg_a]
      _ = ENNReal.ofReal (A * M_dens * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))) *
          volume K.carrier := by rw [hK_toReal]
      _ = (ENNReal.ofReal (A * M_dens *
          ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
            (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))) * volume K.carrier := by
        simp [hn_def]

/-- Common log-to-exp reduction for the three calibration blocks (`hcalib_main`, `hhalf_NetED`,
`hhalf_KTest`) in `exists_refinement`.  Given the assembled log-chain
`log Cd + Md · (-log δ) + 10·e + log(1/budget) ≤ A`, exponentiate to
`Cd · δ^(-Md) · exp(10·e - A) ≤ budget`. -/
private lemma calibration_exp_of_log
    {δ Cd Md budget A : ℝ} (hδ_pos : 0 < δ) (hCd_pos : 0 < Cd)
    (hbudget_pos : 0 < budget)
    (h_log :
      Real.log Cd + Md * (-Real.log δ) + 10 * Real.exp 1
        + Real.log (1 / budget) ≤ A) :
    Cd * δ ^ (-Md) * Real.exp (10 * Real.exp 1 - A) ≤ budget := by
  have hδ_rpow_pos : 0 < δ ^ (-Md) := Real.rpow_pos_of_pos hδ_pos _
  have hCdδ_pos : 0 < Cd * δ ^ (-Md) := mul_pos hCd_pos hδ_rpow_pos
  have hLHS_pos : 0 < Cd * δ ^ (-Md) * Real.exp (10 * Real.exp 1 - A) :=
    mul_pos hCdδ_pos (Real.exp_pos _)
  rw [← Real.exp_log hbudget_pos, ← Real.exp_log hLHS_pos]
  refine Real.exp_le_exp.mpr ?_
  rw [Real.log_mul hCdδ_pos.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hCd_pos.ne' hδ_rpow_pos.ne', Real.log_rpow hδ_pos]
  have hlogbudget : Real.log (1 / budget) = -Real.log budget := by
    rw [Real.log_div one_ne_zero hbudget_pos.ne', Real.log_one, zero_sub]
  linarith [hlogbudget]

set_option maxHeartbeats 820000 in
-- The polylog `M_cap` chain and the per-net-point Chernoff bookkeeping push
-- elaboration above the default budget. The `M_cap_le_of_log_chain` and
-- `chernoff_badCount_le` helpers carry the polylog `M_cap` arithmetic and
-- per-net-point Chernoff bookkeeping; the remaining budget covers the
-- Cε-calibration log chain.
/-- **Random-translation refinement at a single scale** (GWZ Lemma 7.6).  The output exposes the
underlying probability measure `HasUniformTranslation.productMeasure E E J` and a measurable bad set
`Bad` of measure at most the caller-supplied `ε_budget`; the deterministic Lemma 7.6 conclusion
holds for every `ω ∈ Badᶜ`, with translation vector `v j := r • ω j`.  Exposing the bad set is what
the parent-level union bound of `Sticky.subStickyFrostmanLemma.iterate` needs. -/
theorem exists_refinement
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] :
    ∀ ε > (0 : ℝ),
    ∃ Cε C_dens : ℝ, 0 < Cε ∧ 0 < C_dens ∧
    ∀ {δ ρ : NNReal}, 0 < (δ : ℝ) → (δ : ℝ) < 1 → (δ : ℝ) ≤ (ρ : ℝ) → (ρ : ℝ) ≤ 1 →
    ∀ {r : NNReal}, 0 < (r : ℝ) → (r : ℝ) ≤ (ρ : ℝ) →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → Tube δ E) (Tρ : Tube ρ E),
      s.Nonempty →
      Tρ.carrier ⊆ Metric.closedBall (0 : E) 4 →
      (∀ i ∈ s, (T i).carrier ⊆ Tρ.carrier) →
    ∀ M_dens : ℝ,
      (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal ≤ M_dens →
    ∀ J : ℕ, 1 ≤ J →
      (J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) *
        ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
          (δ : ℝ) ^ (Module.finrank ℝ E - 1)) < M_dens →
    ∀ (ε_budget : ENNReal), 0 < ε_budget → ε_budget < 1 →
    ∀ (A : ℝ),
      Cε * ((δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal)) ≤ A →
    ∃ Bad : Set (Fin J → E),
      MeasurableSet Bad ∧
      HasUniformTranslation.productMeasure E E J Bad ≤ ε_budget ∧
      (∀ ω : Fin J → E, ω ∉ Bad →
        ∃ s' : Finset (ι × Fin J),
          (∀ j, ‖(r : ℝ) • ω j‖ ≤ (r : ℝ)) ∧
          s' ⊆ s ×ˢ Finset.univ ∧
          A⁻¹ * (J : ℝ) * (s.card : ℝ) ≤ (s'.card : ℝ) ∧
          (s'.card : ℝ) ≤ (J : ℝ) * (s.card : ℝ) ∧
          maxDensity s'
              (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) ≤
            ENNReal.ofReal (C_dens * A * M_dens) ∧
          maxDensity (s ×ˢ Finset.univ)
              (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) ≤
            ENNReal.ofReal (C_dens * A * M_dens)) := by
  classical
  let K_vol : ℝ :=
    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
      (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set c_low : ℝ := ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) with hc_low_def
  have hc_low_pos : 0 < c_low := by
    rw [hc_low_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  set c_up : ℝ := ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) with hc_up_def
  have hc_up_pos : 0 < c_up := by
    rw [hc_up_def]
    refine NNReal.coe_pos.mpr ?_
    unfold Tube.volume_le.C
    positivity
  have hK_vol_eq : K_vol = c_up / c_low := rfl
  have hK_vol_pos : 0 < K_vol := hK_vol_eq ▸ div_pos hc_up_pos hc_low_pos
  intro ε hε
  obtain ⟨M_net, C_net, hM_net_pos, hC_net_pos, hM_net_eq, hC_net_eq⟩ :
      ∃ M C : ℝ, 0 < M ∧ 0 < C ∧
        M = exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) ∧
        C = (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) *
          5 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) := by
    refine ⟨_, _, exists_volume_bounded_prism_discretization.M_pos (Module.finrank ℝ E), ?_,
      rfl, rfl⟩
    have hC : (0 : ℝ) < (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) :=
      NNReal.coe_pos.mpr (exists_volume_bounded_prism_discretization.C_pos _)
    positivity
  have hCprism_le_C_net :
      (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) ≤ C_net := by
    rw [hC_net_eq]
    have h5 : (1 : ℝ) ≤ 5 ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) := by
      calc (1 : ℝ) = (5 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 5).symm
        _ ≤ (5 : ℝ) ^ exists_volume_bounded_prism_discretization.M (Module.finrank ℝ E) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (exists_volume_bounded_prism_discretization.M_pos _).le
    have hC : (0 : ℝ) ≤ (exists_volume_bounded_prism_discretization.C (Module.finrank ℝ E) : ℝ) :=
      NNReal.coe_nonneg _
    nlinarith
  set C_slice_w : ℝ := sliceIntersectionVolumeConstant E with hC_slice_w_def
  have hC_slice_pos_w : 0 < C_slice_w := by
    rw [hC_slice_w_def]
    exact sliceIntersectionVolumeConstant_pos E
  set vol_B1 : ℝ := volume.real (Metric.closedBall (0 : E) 1) with hvol_B1_def
  have hvol_B1_pos : 0 < vol_B1 := by
    rw [hvol_B1_def]
    refine ENNReal.toReal_pos
      (ne_of_gt (Metric.measure_closedBall_pos volume (0:E) one_pos)) ?_
    exact (isCompact_closedBall (0:E) 1).measure_lt_top.ne
  set c_density : ℝ := c_low / (2 * c_up) with hc_density_def
  have hc_density_pos : 0 < c_density := by
    rw [hc_density_def]; exact div_pos hc_low_pos (by linarith)
  have hc_density_le_one : c_density ≤ 1 := by
    rw [hc_density_def]
    rw [div_le_one (by linarith : (0:ℝ) < 2 * c_up)]
    have hc_up_eq : c_up = 2 ^ (Module.finrank ℝ E + 1) := by
      rw [hc_up_def]
      show ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) = _
      unfold Tube.volume_le.C; push_cast; ring
    have hLHS : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) =
        Real.sqrt Real.pi ^ Module.finrank ℝ E /
          Real.Gamma (Module.finrank ℝ E / 2 + 1) / 3 := rfl
    rw [hc_low_def, hLHS, hc_up_eq]
    set V : ℝ := Real.sqrt Real.pi ^ Module.finrank ℝ E /
                   Real.Gamma (Module.finrank ℝ E / 2 + 1) with hV_def
    have hV_pos : 0 < V := by rw [hV_def]; positivity
    have h2pow_pos : (0 : ℝ) < 2 ^ (Module.finrank ℝ E + 1) := by positivity
    have hsqrt_le_two : Real.sqrt Real.pi ≤ 2 := by
      have h : Real.sqrt Real.pi ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
      rwa [show (4 : ℝ) = 2 ^ 2 from by norm_num,
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
    have hΓ_pos : 0 < Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by positivity
    have hsqrtpow_le : Real.sqrt Real.pi ^ Module.finrank ℝ E ≤ 2 ^ Module.finrank ℝ E :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le_two _
    have hV_le : V ≤ 2 ^ Module.finrank ℝ E /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
      rw [hV_def]
      exact div_le_div_of_nonneg_right hsqrtpow_le hΓ_pos.le
    have hΓ_ge_half : (1 / 2 : ℝ) ≤ Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
      by_cases h2 : 2 ≤ Module.finrank ℝ E
      · have hx : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2 + 1 := by
          have h2' : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast h2
          linarith
        have hone : (1 : ℝ) ≤ Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) :=
          calc (1 : ℝ) = Real.Gamma 2 := Real.Gamma_two.symm
            _ ≤ _ := Real.Gamma_strictMonoOn_Ici.monotoneOn
                Set.self_mem_Ici (Set.mem_Ici.mpr hx) hx
        linarith
      · push Not at h2
        have hn1 : Module.finrank ℝ E = 1 := by omega
        rw [hn1]
        have h32 : ((1 : ℕ) : ℝ) / 2 + 1 = (1 : ℕ) + 1 / 2 := by push_cast; ring
        rw [h32, Real.Gamma_nat_add_half 1]
        have hdf : ((2 * 1 - 1 : ℕ).doubleFactorial : ℝ) = 1 := by
          norm_num [Nat.doubleFactorial]
        rw [hdf, pow_one]
        have hπ : (1 : ℝ) ≤ Real.sqrt Real.pi := by
          have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt hpi
        linarith
    have h1 : V ≤ 2 * 2 ^ Module.finrank ℝ E := by
      calc V ≤ 2 ^ Module.finrank ℝ E /
              Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := hV_le
        _ ≤ 2 ^ Module.finrank ℝ E / (1 / 2) := by
            apply div_le_div_of_nonneg_left _ (by norm_num) hΓ_ge_half
            positivity
        _ = 2 * 2 ^ Module.finrank ℝ E := by ring
    have hpow_succ : (2 : ℝ) ^ (Module.finrank ℝ E + 1) = 2 * 2 ^ Module.finrank ℝ E := by
      rw [pow_succ]; ring
    rw [hpow_succ]
    linarith
  set K_unif : ℝ := K_vol with hK_unif_def
  have hK_unif_pos : 0 < K_unif := hK_unif_def ▸ hK_vol_pos
  have hThinBox_witness :
      ∃ (C_dim : ℕ) (δ₀ : ℝ), 0 < C_dim ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
        (1 < Module.finrank ℝ E →
          ∀ {ι : Type u} {δ' : NNReal} (_hδ' : 0 < δ') (_hδ'_le : (δ' : ℝ) ≤ δ₀)
            (s' : Finset ι) (T' : ι → Tube δ' E) (T₀' : Tube δ' E)
            (_hK_in_B2 : T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2))
            (M : ℝ) (_hM_pos : 0 < M)
            (_h_vol_ub :
              volume (Metric.cthickening (99 * (δ' : ℝ)) T₀'.carrier)
                ≤ ENNReal.ofReal M *
                  (δ' : ENNReal) ^ (Module.finrank ℝ E - 1))
            (v : E),
            (s' : Set ι).Pairwise
              (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier) →
            (s'.filter (fun i => BadAgainstSet ((T' i).translate v)
                (Metric.cthickening (99 * (δ' : ℝ)) T₀'.carrier)
                (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
                  (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))))).card
              ≤ ⌈(C_dim : ℝ) * M ^ 2 /
                  (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
                    (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))) ^
                    (Module.finrank ℝ E)⌉₊) := by
    by_cases hfr : 1 < Module.finrank ℝ E
    · obtain ⟨C_dim, δ₀, hC_pos, hδ₀_pos, hδ₀_le, h⟩ :=
        badAgainstSet_count_le_of_ED_thinBox E hfr
      exact ⟨C_dim, δ₀, hC_pos, hδ₀_pos, hδ₀_le, fun _ => h⟩
    · exact ⟨1, 1, Nat.one_pos, one_pos, le_refl _,
        fun h => absurd h hfr⟩
  obtain ⟨C_dim_outer, δ₀_dim_outer, hC_dim_outer_pos, hδ₀_dim_outer_pos,
          hδ₀_dim_outer_le_one, h_thinBox_outer⟩ := hThinBox_witness
  set C_pack_ext : ℕ :=
    ⌈(C_dim_outer : ℝ) * netVolThinConstantM E ^ 2 /
        c_density ^ Module.finrank ℝ E⌉₊ + 1
    with hC_pack_ext_def
  have hC_pack_ext_pos : 0 < C_pack_ext := by
    rw [hC_pack_ext_def]; exact Nat.succ_pos _
  set M_ED : ℕ :=
    max (2 ^ Module.finrank ℝ E * C_pack_ext + 1)
        (⌈2 * K_unif * c_up ^ 2 * C_slice_w / (c_low ^ 2 * vol_B1)⌉₊ + 1)
    with hM_ED_def
  have hM_ED_pos : 0 < M_ED := by
    rw [hM_ED_def]
    exact lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  have hM_ED_outer_ge_dimC_pack :
      2 ^ Module.finrank ℝ E * C_pack_ext < M_ED := by
    rw [hM_ED_def]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hM_ED_ge_C_pack_ext : C_pack_ext ≤ M_ED := by
    have h2n : 1 ≤ 2 ^ Module.finrank ℝ E := Nat.one_le_pow _ _ (by norm_num)
    have h : C_pack_ext ≤ 2 ^ Module.finrank ℝ E * C_pack_ext + 1 := by
      calc C_pack_ext = 1 * C_pack_ext := (one_mul _).symm
        _ ≤ 2 ^ Module.finrank ℝ E * C_pack_ext :=
            Nat.mul_le_mul_right _ h2n
        _ ≤ 2 ^ Module.finrank ℝ E * C_pack_ext + 1 := Nat.le_succ _
    rw [hM_ED_def]
    exact le_trans h (le_max_left _ _)
  set M_dim : ℕ := max M_ED C_pack_ext with hM_dim_def
  have hM_dim_pos : 0 < M_dim := lt_of_lt_of_le hM_ED_pos (le_max_left _ _)
  have hMax_M_ED : max M_ED C_pack_ext = M_ED :=
    max_eq_left hM_ED_ge_C_pack_ext
  set Cε : ℝ :=
      max 1
        ((max (netGeomConstantM E) M_net) / ε
          + Real.log (max (netGeomConstantC E) C_net + 1)
          + Real.log 2
          + 10 * Real.exp 1
          + 1
          + (M_dim : ℝ) * (M_dim : ℝ)
          + (M_dim : ℝ) * (netGeomConstantM E / ε)
          + (M_dim : ℝ) *
              (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
          + 2 * (M_dim : ℝ) + 1)
      + 1
    with hCε_def
  have hCε_pos : 0 < Cε := by
    rw [hCε_def]
    have h1 : (1 : ℝ) ≤ max 1
        ((max (netGeomConstantM E) M_net) / ε
          + Real.log (max (netGeomConstantC E) C_net + 1)
          + Real.log 2
          + 10 * Real.exp 1
          + 1
          + (M_dim : ℝ) * (M_dim : ℝ)
          + (M_dim : ℝ) * (netGeomConstantM E / ε)
          + (M_dim : ℝ) *
              (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
          + 2 * (M_dim : ℝ) + 1) := le_max_left _ _
    linarith
  have hCε_ge_one : (1 : ℝ) ≤ Cε := by
    rw [hCε_def]
    have h1 : (1 : ℝ) ≤ max 1
        ((max (netGeomConstantM E) M_net) / ε
          + Real.log (max (netGeomConstantC E) C_net + 1)
          + Real.log 2
          + 10 * Real.exp 1
          + 1
          + (M_dim : ℝ) * (M_dim : ℝ)
          + (M_dim : ℝ) * (netGeomConstantM E / ε)
          + (M_dim : ℝ) *
              (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
          + 2 * (M_dim : ℝ) + 1) := le_max_left _ _
    linarith
  set C_dens : ℝ := C_net * K_vol with hC_dens_def
  have hC_dens_pos : 0 < C_dens := hC_dens_def ▸ mul_pos hC_net_pos hK_vol_pos
  refine ⟨Cε, C_dens, hCε_pos, hC_dens_pos, ?_⟩
  intro δ ρ hδ_pos hδ_lt1 hδρ hρ_le r hr_pos hr_le ι s T Tρ hs_ne
    hTρ_ball hT_in_Tρ M_dens hM_dens_bound J hJ hCalib ε_budget hε_budget_pos
    hε_budget_lt A h_A
  by_cases hδ_lt_one : (δ : ℝ) < 1
  · have hδ_nn_pos : (0 : NNReal) < δ := by exact_mod_cast hδ_pos
    have hδ_nn_lt_one : δ < 1 := by exact_mod_cast hδ_lt_one
    set M_log_term : ℕ := ⌈netGeomConstantM E * Real.log (1 / (δ : ℝ))⌉₊
      with hM_log_term_def
    set M_const : ℕ :=
        ⌈10 * Real.exp 1 +
          Real.log (3 * netGeomConstantC E / ε_budget.toReal)⌉₊
      with hM_const_def
    set M_inner : ℕ := M_dim + M_log_term + M_const + 1 with hM_inner_def
    have hM_inner_pos : 0 < M_inner := by simp [hM_inner_def]
    set M_cap : ℕ := M_dim * M_inner with hM_cap_def
    have hM_cap_pos : 0 < M_cap := by
      rw [hM_cap_def]; exact Nat.mul_pos hM_dim_pos hM_inner_pos
    have hδr_pos_C : (0 : ℝ) < (δ : ℝ) := hδ_pos
    have hδr_le_one_C : (δ : ℝ) ≤ 1 := hδ_lt_one.le
    have hδ_rpow_pos_C : (0 : ℝ) < (δ : ℝ) ^ (-ε) :=
      Real.rpow_pos_of_pos hδr_pos_C (-ε)
    have hδ_rpow_ge_one_C : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε) := by
      rw [Real.rpow_neg hδr_pos_C.le, one_le_inv_iff₀]
      refine ⟨Real.rpow_pos_of_pos hδr_pos_C ε, ?_⟩
      exact Real.rpow_le_one hδr_pos_C.le hδr_le_one_C hε.le
    have hε_budget_ne_top_C : ε_budget ≠ ⊤ := LT.lt.ne_top hε_budget_lt
    have hε_budget_toReal_pos_C : 0 < ε_budget.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hε_budget_pos, lt_of_lt_of_le hε_budget_lt le_top⟩
    have hε_budget_toReal_lt_one_C : ε_budget.toReal < 1 := by
      have h := (ENNReal.toReal_lt_toReal hε_budget_ne_top_C
        (by exact ENNReal.one_ne_top)).mpr hε_budget_lt
      simpa using h
    have hlog_inv_nn_C : 0 ≤ Real.log (1 / ε_budget.toReal) := by
      rw [Real.log_div one_ne_zero (ne_of_gt hε_budget_toReal_pos_C),
          Real.log_one, zero_sub, neg_nonneg]
      exact Real.log_nonpos hε_budget_toReal_pos_C.le hε_budget_toReal_lt_one_C.le
    have hnetM_pos_C : 0 < netGeomConstantM E := netGeomConstantM_pos E
    have hnetC_pos_C : 0 < netGeomConstantC E := netGeomConstantC_pos E
    have hM_dim_nn_C : (0 : ℝ) ≤ (M_dim : ℝ) := Nat.cast_nonneg _
    have h_neglog_le : -Real.log (δ : ℝ) ≤ (δ : ℝ) ^ (-ε) / ε := by
      have h_neg_log : 0 ≤ -Real.log (δ : ℝ) := by
        rw [neg_nonneg]; exact Real.log_nonpos hδr_pos_C.le hδr_le_one_C
      have hrpow_eq : (δ : ℝ) ^ (-ε) = Real.exp (-ε * Real.log (δ : ℝ)) := by
        rw [Real.rpow_def_of_pos hδr_pos_C]; congr 1; ring
      have h_exp_ge : 1 + (-ε * Real.log (δ : ℝ)) ≤ Real.exp (-ε * Real.log (δ : ℝ)) := by
        have := Real.add_one_le_exp (-ε * Real.log (δ : ℝ))
        linarith
      have hrearr : -ε * Real.log (δ : ℝ) = ε * (-Real.log (δ : ℝ)) := by ring
      have h_ε_log : ε * (-Real.log (δ : ℝ)) ≤ (δ : ℝ) ^ (-ε) := by
        rw [hrpow_eq, ← hrearr]; linarith
      rw [le_div_iff₀ hε]; linarith
    have hlog_inv_δ_nn : 0 ≤ Real.log (1 / (δ : ℝ)) := by
      rw [Real.log_div one_ne_zero (ne_of_gt hδr_pos_C), Real.log_one, zero_sub, neg_nonneg]
      exact Real.log_nonpos hδr_pos_C.le hδr_le_one_C
    have hM_log_term_le :
        (M_log_term : ℝ) ≤ netGeomConstantM E * Real.log (1 / (δ : ℝ)) + 1 := by
      rw [hM_log_term_def]
      have := Nat.ceil_lt_add_one (a := netGeomConstantM E * Real.log (1 / (δ : ℝ)))
        (by positivity)
      linarith [this.le]
    have hM_const_le :
        (M_const : ℝ) ≤ 10 * Real.exp 1 +
            Real.log (3 * netGeomConstantC E + 1) +
            Real.log (1 / ε_budget.toReal) + 1 := by
      rw [hM_const_def]
      have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
      have hlog3C_nn : 0 ≤ Real.log (3 * netGeomConstantC E + 1) := by
        apply Real.log_nonneg; have := hnetC_pos_C; linarith
      have h_log_decomp_arg : Real.log (3 * netGeomConstantC E / ε_budget.toReal) =
          Real.log (3 * netGeomConstantC E) - Real.log ε_budget.toReal :=
        Real.log_div (by positivity) (ne_of_gt hε_budget_toReal_pos_C)
      have h_log_3C_le : Real.log (3 * netGeomConstantC E) ≤
          Real.log (3 * netGeomConstantC E + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      have h_log_ε_inv_eq : -Real.log ε_budget.toReal = Real.log (1 / ε_budget.toReal) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hε_budget_toReal_pos_C), Real.log_one,
            zero_sub]
      have h_arg_bound : 10 * Real.exp 1 +
          Real.log (3 * netGeomConstantC E / ε_budget.toReal) ≤
          10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) +
            Real.log (1 / ε_budget.toReal) := by
        rw [h_log_decomp_arg]
        linarith [h_log_ε_inv_eq, h_log_3C_le]
      by_cases hpos : 0 ≤ 10 * Real.exp 1 +
          Real.log (3 * netGeomConstantC E / ε_budget.toReal)
      · have hlt := Nat.ceil_lt_add_one hpos
        linarith
      · push Not at hpos
        have h_eq_zero : ⌈10 * Real.exp 1 +
            Real.log (3 * netGeomConstantC E / ε_budget.toReal)⌉₊ = 0 :=
          Nat.ceil_eq_zero.mpr hpos.le
        rw [h_eq_zero]
        push_cast
        have hlog_inv_nn : 0 ≤ Real.log (1 / ε_budget.toReal) := hlog_inv_nn_C
        linarith
    have h_log_decomp : Real.log (3 * netGeomConstantC E / ε_budget.toReal) =
        Real.log (3 * netGeomConstantC E) - Real.log ε_budget.toReal := by
      rw [Real.log_div (by positivity) (ne_of_gt hε_budget_toReal_pos_C)]
    have h_log_ε_inv : -Real.log ε_budget.toReal = Real.log (1 / ε_budget.toReal) := by
      rw [Real.log_div one_ne_zero (ne_of_gt hε_budget_toReal_pos_C), Real.log_one,
          zero_sub]
    have h_log_3C_le : Real.log (3 * netGeomConstantC E) ≤
        Real.log (3 * netGeomConstantC E + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hcast_eq : (M_cap : ℝ) + 1 =
        (M_dim : ℝ) * (M_dim : ℝ) + (M_dim : ℝ) * (M_log_term : ℝ) +
          (M_dim : ℝ) * (M_const : ℝ) + (M_dim : ℝ) + 1 := by
      simp only [hM_cap_def, hM_inner_def]; push_cast; ring
    have hCε_sub :
        (M_dim : ℝ) * (M_dim : ℝ) + (M_dim : ℝ) * (netGeomConstantM E / ε)
          + (M_dim : ℝ) * (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
          + 2 * (M_dim : ℝ) + 1 ≤ Cε := by
      rw [hCε_def]
      have h1 := le_max_right (1 : ℝ)
        ((max (netGeomConstantM E) M_net) / ε
          + Real.log (max (netGeomConstantC E) C_net + 1)
          + Real.log 2 + 10 * Real.exp 1 + 1
          + (M_dim : ℝ) * (M_dim : ℝ)
          + (M_dim : ℝ) * (netGeomConstantM E / ε)
          + (M_dim : ℝ) *
              (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
          + 2 * (M_dim : ℝ) + 1)
      have hpart1_nn : 0 ≤ (max (netGeomConstantM E) M_net) / ε :=
        div_nonneg (le_max_of_le_left hnetM_pos_C.le) hε.le
      have hpart2_nn : 0 ≤ Real.log (max (netGeomConstantC E) C_net + 1) := by
        apply Real.log_nonneg
        have h : 0 ≤ max (netGeomConstantC E) C_net :=
          le_max_of_le_left hnetC_pos_C.le
        linarith
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
      linarith
    have hM_dim_le_Cε : (M_dim : ℝ) ≤ Cε := by
      rw [hCε_def]
      have h1 := le_max_right (1 : ℝ)
        ((max (netGeomConstantM E) M_net) / ε
          + Real.log (max (netGeomConstantC E) C_net + 1)
          + Real.log 2 + 10 * Real.exp 1 + 1
          + (M_dim : ℝ) * (M_dim : ℝ)
          + (M_dim : ℝ) * (netGeomConstantM E / ε)
          + (M_dim : ℝ) *
              (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
          + 2 * (M_dim : ℝ) + 1)
      have hpart1_nn : 0 ≤ (max (netGeomConstantM E) M_net) / ε :=
        div_nonneg (le_max_of_le_left hnetM_pos_C.le) hε.le
      have hpart2_nn : 0 ≤ Real.log (max (netGeomConstantC E) C_net + 1) := by
        apply Real.log_nonneg
        have h : 0 ≤ max (netGeomConstantC E) C_net :=
          le_max_of_le_left hnetC_pos_C.le
        linarith
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
      have hM_dim_sq_nn : 0 ≤ (M_dim : ℝ) * (M_dim : ℝ) :=
        mul_nonneg hM_dim_nn_C hM_dim_nn_C
      have hMdim_div_nn : 0 ≤ (M_dim : ℝ) * (netGeomConstantM E / ε) :=
        mul_nonneg hM_dim_nn_C (by positivity)
      have hMdim_const_nn : 0 ≤ (M_dim : ℝ) *
          (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2) := by
        have hlog3C_nn : 0 ≤ Real.log (3 * netGeomConstantC E + 1) := by
          apply Real.log_nonneg; linarith
        exact mul_nonneg hM_dim_nn_C (by linarith)
      linarith
    have hM_cap_bound : (M_cap : ℝ) + 1 ≤ A :=
      M_cap_le_of_log_chain (M_dim_R := (M_dim : ℝ))
        (M_log_term_R := (M_log_term : ℝ))
        (M_const_R := (M_const : ℝ)) (M_cap_R := (M_cap : ℝ))
        (δr := (δ : ℝ)) (ε := ε) (εbR := ε_budget.toReal) (A := A) (Cε := Cε)
        (netM := netGeomConstantM E) (netC := netGeomConstantC E)
        hM_dim_nn_C hδr_pos_C hδr_le_one_C hε
        hε_budget_toReal_pos_C hε_budget_toReal_lt_one_C
        hnetM_pos_C hnetC_pos_C hcast_eq hM_log_term_le hM_const_le
        hCε_sub hM_dim_le_Cε h_A
    obtain ⟨NetED, hNetED_card, hNetED_meas, hNetED_sub, hNetED_vol, _hNetED_cover⟩ :=
      exists_ed_tube_net_thin (E := E) hδ_nn_pos hδ_nn_lt_one
    set uc : ℝ := @HasUniformTranslation.uniformConstant E _ E _ _ _ _ _
      (instHasUniformTranslationSelf E) with huc_def
    have huc_pos : 0 < uc :=
      @HasUniformTranslation.uniformConstantPos E _ E _ _ _ _ _
        (instHasUniformTranslationSelf E)
    set M_ED_const : ℝ :=
        max ((s.card : ℝ) + 1)
          ((J : ℝ) * uc *
            (s.card : ℝ) *
            (netVolThinConstantM E * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) + 1)
      with hM_ED_const_def
    have hM_ED_const_pos : 0 < M_ED_const := by
      rw [hM_ED_const_def]
      exact lt_of_lt_of_le one_pos
        (le_max_of_le_left (by linarith [(Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)]))
    let K_truncated : Tube δ E → Set E := fun T₀ =>
      Metric.cthickening (99 * (δ : ℝ)) T₀.carrier ∩ Metric.closedBall (0 : E) 4
    let badED : Tube δ E → Set (Fin J → E) := fun T₀ =>
      { ω | A * M_ED_const <
            ∑ j : Fin J, HasUniformTranslation.productTubeContainedCount
              (Ω := E) s T (K_truncated T₀) J j ω }
    let BadOut : Set (Fin J → E) :=
      { ω | ∃ j, ω j ∉ Metric.closedBall (0 : E) 1 }
    set i₀ : ι := Classical.choose hs_ne with hi₀_def
    have hi₀_mem : i₀ ∈ s := Classical.choose_spec hs_ne
    set T_shaded : ι → ShadedTube δ E := fun i =>
      if i ∈ s then
        { toTube := T i, shade := ∅, shade_subset := Set.empty_subset _,
          measurableSet_shade := MeasurableSet.empty }
      else
        { toTube := T i₀, shade := ∅, shade_subset := Set.empty_subset _,
          measurableSet_shade := MeasurableSet.empty }
      with hT_shaded_def
    have hT_shaded_carrier_of_mem :
        ∀ i ∈ s, (T_shaded i).carrier = (T i).carrier := by
      intro i hi
      simp [hT_shaded_def, hi]
    have hT_shaded_in_B4 : ∀ i, (T_shaded i).carrier ⊆ Metric.closedBall (0 : E) 4 := by
      intro i
      by_cases hi : i ∈ s
      · have h : (T i).carrier ⊆ Metric.closedBall (0 : E) 4 :=
          (hT_in_Tρ i hi).trans hTρ_ball
        rw [hT_shaded_carrier_of_mem i hi]
        exact h
      · have h : (T i₀).carrier ⊆ Metric.closedBall (0 : E) 4 :=
          (hT_in_Tρ i₀ hi₀_mem).trans hTρ_ball
        have hcarr : (T_shaded i).carrier = (T i₀).carrier := by
          simp [hT_shaded_def, hi]
        rw [hcarr]
        exact h
    obtain ⟨KTest, hKTest_sub, hKTest_card_nn, hKTest_cover⟩ :=
      Kakeya.exists_localized_finite_test_family_maxDensity.{u, _} (E := E)
        (r := δ) (R := 5) hδ_nn_pos hδ_nn_lt_one.le (by norm_num)
    have hKTest_le : ∀ K ∈ KTest, K ≤ ConvexSpaceBody.cthickening 1
        (ConvexSpaceBody.closedBall (0 : E) (5 : ℝ) (by norm_num)) := by
      intro K hK x hx
      have hx5 : x ∈ Metric.closedBall (0 : E) 5 := by simpa using hKTest_sub K hK hx
      exact Metric.self_subset_cthickening _ hx5
    have hKTest_card : (KTest.card : ℝ) ≤ C_net * (δ : ℝ) ^ (-M_net) := by
      rw [hC_net_eq, hM_net_eq]
      have h := NNReal.coe_le_coe.mpr hKTest_card_nn
      rwa [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow,
        NNReal.coe_natCast, NNReal.coe_ofNat] at h
    have hKTest_carrier_in_B6 : ∀ K ∈ KTest, K.carrier ⊆ Metric.closedBall (0 : E) 6 :=
      fun K hK => cthickening_carrier_subset_closedBall_six K (hKTest_le K hK)
    set V_lb : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
      (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hV_lb_def
    have hV_lb_pos : 0 < V_lb := by rw [hV_lb_def]; positivity
    set M_F : ConvexSpaceBody E → ℝ := fun K =>
        max (M_dens * volume.real K.carrier / V_lb) 1
      with hM_F_def
    have hM_F_pos : ∀ K : ConvexSpaceBody E, 0 < M_F K := fun K =>
      hM_F_def ▸ lt_of_lt_of_le one_pos (le_max_right _ _)
    let badF : ConvexSpaceBody E → Set (Fin J → E) := fun K =>
      { ω | A * M_F K <
            ∑ j : Fin J, scaledProductTubeContainedCount (r : ℝ) s T K.carrier J j ω }
    set Bad : Set (Fin J → E) :=
      ((⋃ T₀ ∈ NetED, badED T₀) ∪ (⋃ K ∈ KTest, badF K)) ∪ BadOut with hBad_def
    have hK_truncated_meas : ∀ T₀ : Tube δ E, MeasurableSet (K_truncated T₀) := by
      intro T₀
      exact (Metric.isClosed_cthickening.inter Metric.isClosed_closedBall).measurableSet
    have hTubeContained_meas : ∀ T₀ : Tube δ E,
        ∀ i ∈ s, MeasurableSet (HasUniformTranslation.tubeContainedSet (Ω := E)
          (T i) (K_truncated T₀)) := fun T₀ i _ =>
      (isClosed_tubeContainedSet (T i) (K_truncated T₀)
        (Metric.isClosed_cthickening.inter Metric.isClosed_closedBall)).measurableSet
    have hBadOut_meas : MeasurableSet BadOut :=
      (measure_badOut_eq_zero E J).1
    have hBadED_meas : MeasurableSet (⋃ T₀ ∈ NetED, badED T₀) := by
      refine Set.Finite.measurableSet_biUnion (Finset.finite_toSet _) fun T₀ _ => ?_
      exact (Finset.measurable_sum _ fun j _ =>
          HasUniformTranslation.productTubeContainedCount_measurable
            (Ω := E) s T (K_truncated T₀) (hTubeContained_meas T₀) J j)
        measurableSet_Ioi
    have hTubeContainedF_meas : ∀ K ∈ KTest,
        ∀ i ∈ s, MeasurableSet (HasUniformTranslation.tubeContainedSet (Ω := E)
          (T i) K.carrier) := fun K _ i _ =>
      (isClosed_tubeContainedSet (T i) K.carrier K.isCompact.isClosed).measurableSet
    have hScaledF_meas : ∀ K ∈ KTest,
        ∀ i ∈ s, MeasurableSet (scaledTubeContainedSet (r : ℝ) (T i) K.carrier) :=
      fun K _ i _ =>
        (isClosed_scaledTubeContainedSet (r : ℝ) (T i) K.isCompact.isClosed).measurableSet
    have hBadF_meas : MeasurableSet (⋃ K ∈ KTest, badF K) := by
      refine Set.Finite.measurableSet_biUnion (Finset.finite_toSet _) fun K hK => ?_
      exact (Finset.measurable_sum _ fun j _ =>
          scaledProductTubeContainedCount_measurable hr_pos s T K.carrier
            (hScaledF_meas K hK) J j)
        measurableSet_Ioi
    have hBad_meas : MeasurableSet Bad := by
      rw [hBad_def]
      exact (hBadED_meas.union hBadF_meas).union hBadOut_meas
    have hBadOut_zero :
        HasUniformTranslation.productMeasure E E J BadOut = 0 :=
      (measure_badOut_eq_zero E J).2
    haveI hJ_neZero : NeZero J := ⟨by omega⟩
    have hxT : ∀ i ∈ s, (T i).x ∈ (T i).carrier := fun i _ => by
      rw [(T i).carrier_eq]
      exact Set.mem_iUnion₂.mpr
        ⟨(T i).x, left_mem_segment ℝ (T i).x (T i).y,
         Metric.mem_closedBall_self (NNReal.coe_nonneg _)⟩
    have hBadT₀_bound : ∀ T₀ ∈ NetED,
        (HasUniformTranslation.productMeasure E E J (badED T₀)).toReal ≤
          Real.exp (10 * Real.exp 1 - A) := by
      intro T₀ hT₀
      have hK_truncated_sub : K_truncated T₀ ⊆ Metric.closedBall (0 : E) 4 :=
        Set.inter_subset_right
      have hK_truncated_top : volume (K_truncated T₀) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt (measure_mono hK_truncated_sub)
          measure_closedBall_lt_top)
      have hXM : ∀ j ω,
          (HasUniformTranslation.productTubeContainedCount (Ω := E) s T
            (K_truncated T₀) J j ω : ℝ) ≤ M_ED_const := by
        intro j ω
        have h1 := HasUniformTranslation.productTubeContainedCount_le_card
          (Ω := E) s T (K_truncated T₀) J j ω
        have h2 : (s.card : ℝ) ≤ M_ED_const := by
          rw [hM_ED_const_def]
          refine le_trans ?_ (le_max_left _ _)
          linarith
        linarith
      have hvol_K_le : volume.real (K_truncated T₀) ≤
          netVolThinConstantM E * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
        have hsub : K_truncated T₀ ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀.carrier :=
          Set.inter_subset_left
        have hfin : volume (Metric.cthickening (99 * (δ : ℝ)) T₀.carrier) ≠ ⊤ :=
          (IsCompact.cthickening T₀.isCompact).measure_lt_top.ne
        have hvol_ennreal : volume (K_truncated T₀) ≤
            ENNReal.ofReal (netVolThinConstantM E) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
          (measure_mono hsub).trans (hNetED_vol T₀ hT₀)
        have hRHS_ne_top : ENNReal.ofReal (netVolThinConstantM E) *
            (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ :=
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.pow_ne_top ENNReal.coe_ne_top)
        have hreal := ENNReal.toReal_mono hRHS_ne_top hvol_ennreal
        simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.coe_toReal, ENNReal.toReal_ofReal (netVolThinConstantM_pos E).le] using hreal
      have hJmM : (J : ℝ) *
          (uc * (s.card : ℝ) *
            volume.real (K_truncated T₀)) < M_ED_const := by
        have hJuc_nn : (0 : ℝ) ≤ (J : ℝ) * uc * (s.card : ℝ) :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) huc_pos.le) (Nat.cast_nonneg _)
        have hgoal :
            (J : ℝ) * uc * (s.card : ℝ) *
              (netVolThinConstantM E * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) <
            M_ED_const := by
          rw [hM_ED_const_def]
          refine lt_of_lt_of_le ?_ (le_max_right _ _)
          linarith
        calc (J : ℝ) * (uc * (s.card : ℝ) * volume.real (K_truncated T₀))
            = (J : ℝ) * uc * (s.card : ℝ) * volume.real (K_truncated T₀) := by ring
          _ ≤ (J : ℝ) * uc * (s.card : ℝ) *
              (netVolThinConstantM E * (δ : ℝ) ^ (Module.finrank ℝ E - 1)) :=
              mul_le_mul_of_nonneg_left hvol_K_le hJuc_nn
          _ < M_ED_const := hgoal
      exact chernoff_badCount_le (E := E) s T hxT
        (hK_truncated_meas T₀) hK_truncated_top (hTubeContained_meas T₀)
        M_ED_const hM_ED_const_pos hXM hJmM A
    have hBadF_K_bound : ∀ K ∈ KTest,
        (HasUniformTranslation.productMeasure E E J (badF K)).toReal ≤
          Real.exp (10 * Real.exp 1 - A) := by
      intro K hK
      have hXM : ∀ t : E, scaledTubeContainedCount (r : ℝ) s T K.carrier t ≤ M_F K :=
        scaledTubeContainedCount_le_of_maxDensity hr_pos s T K M_dens hM_dens_bound V_lb
          hV_lb_pos (fun i _ => by
            rw [hV_lb_def]
            change (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
                (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤
              (volume ((T i).toConvexSpaceBody : Set E)).toReal
            have h := Tube.le_volume (T i)
            have hreal := ENNReal.toReal_mono (T i).isCompact.measure_lt_top.ne h
            simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
              ENNReal.coe_toReal] using hreal) (M_F K)
          (hM_F_def ▸ le_max_left _ _)
      have hJmM : (J : ℝ) *
          ((s.card : ℝ) * (probConst E (r : ℝ) * volume.real K.carrier)) < M_F K := by
        set v := volume.real K.carrier with hv_def
        by_cases hvz : v = 0
        · rw [hvz]
          simp only [mul_zero, mul_zero]
          exact hM_F_pos K
        · have hv_pos : 0 < v := lt_of_le_of_ne measureReal_nonneg (Ne.symm hvz)
          have h_calib_V : (J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * V_lb < M_dens := by
            rw [hV_lb_def]
            exact hCalib
          have hpos : 0 < v / V_lb := div_pos hv_pos hV_lb_pos
          have hcalc : (J : ℝ) * ((s.card : ℝ) * (probConst E (r : ℝ) * v)) =
              ((J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * V_lb) * (v / V_lb) := by
            calc
              (J : ℝ) * ((s.card : ℝ) * (probConst E (r : ℝ) * v))
                  = (J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * v := by ring
              _ = (J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * v * 1 := by ring
              _ = (J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * v * (V_lb / V_lb) := by
                rw [div_self (hV_lb_pos.ne')]
              _ = ((J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * V_lb) * (v / V_lb) := by ring
          have h_lt : (J : ℝ) * ((s.card : ℝ) * (probConst E (r : ℝ) * v)) < M_dens * v / V_lb := by
            calc
              (J : ℝ) * ((s.card : ℝ) * (probConst E (r : ℝ) * v))
                  = ((J : ℝ) * (s.card : ℝ) * probConst E (r : ℝ) * V_lb) * (v / V_lb) := hcalc
              _ < M_dens * (v / V_lb) := mul_lt_mul_of_pos_right h_calib_V hpos
              _ = M_dens * v / V_lb := by ring
          have h_cap : M_dens * v / V_lb ≤ M_F K := by
            rw [hM_F_def, hv_def]
            exact le_max_left _ _
          rw [hv_def]
          exact lt_of_lt_of_le h_lt h_cap
      exact chernoff_scaled_badCount_le (E := E) s T K hr_pos
        (hScaledF_meas K hK) (M_F K) (hM_F_pos K) hXM hJmM A
    have hMeasure_bound :
        HasUniformTranslation.productMeasure E E J Bad ≤ ε_budget := by
      have hUnion_le :
          HasUniformTranslation.productMeasure E E J Bad ≤
            ∑ T₀ ∈ NetED, HasUniformTranslation.productMeasure E E J (badED T₀) +
            ∑ K ∈ KTest, HasUniformTranslation.productMeasure E E J (badF K) := by
        rw [hBad_def]
        calc HasUniformTranslation.productMeasure E E J
                (((⋃ T₀ ∈ NetED, badED T₀) ∪ (⋃ K ∈ KTest, badF K)) ∪ BadOut)
            ≤ HasUniformTranslation.productMeasure E E J
                ((⋃ T₀ ∈ NetED, badED T₀) ∪ (⋃ K ∈ KTest, badF K))
                + HasUniformTranslation.productMeasure E E J BadOut :=
              MeasureTheory.measure_union_le _ _
          _ = HasUniformTranslation.productMeasure E E J
                ((⋃ T₀ ∈ NetED, badED T₀) ∪ (⋃ K ∈ KTest, badF K))
                + 0 := by rw [hBadOut_zero]
          _ = HasUniformTranslation.productMeasure E E J
                ((⋃ T₀ ∈ NetED, badED T₀) ∪ (⋃ K ∈ KTest, badF K)) := by rw [add_zero]
          _ ≤ HasUniformTranslation.productMeasure E E J (⋃ T₀ ∈ NetED, badED T₀)
              + HasUniformTranslation.productMeasure E E J (⋃ K ∈ KTest, badF K) :=
              MeasureTheory.measure_union_le _ _
          _ ≤ (∑ T₀ ∈ NetED, HasUniformTranslation.productMeasure E E J (badED T₀))
              + ∑ K ∈ KTest, HasUniformTranslation.productMeasure E E J (badF K) := by
              gcongr
              · exact MeasureTheory.measure_biUnion_finset_le NetED _
              · exact MeasureTheory.measure_biUnion_finset_le KTest _
      have hμ_finite : ∀ T₀ ∈ NetED,
          HasUniformTranslation.productMeasure E E J (badED T₀) ≠ ⊤ := by
        intro T₀ _hT₀
        exact MeasureTheory.measure_ne_top _ _
      have hμ_le : ∀ T₀ ∈ NetED,
          HasUniformTranslation.productMeasure E E J (badED T₀) ≤
            ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
        intro T₀ hT₀
        have h := hBadT₀_bound T₀ hT₀
        rw [← ENNReal.ofReal_toReal (hμ_finite T₀ hT₀)]
        exact ENNReal.ofReal_le_ofReal h
      have hSum_le :
          ∑ T₀ ∈ NetED, HasUniformTranslation.productMeasure E E J (badED T₀) ≤
            ∑ _T₀ ∈ NetED, ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) :=
        Finset.sum_le_sum hμ_le
      have hSum_const :
          ∑ _T₀ ∈ NetED, ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) =
            (NetED.card : ENNReal) * ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hμF_finite : ∀ K ∈ KTest,
          HasUniformTranslation.productMeasure E E J (badF K) ≠ ⊤ := by
        intro K _hK
        exact MeasureTheory.measure_ne_top _ _
      have hμF_le : ∀ K ∈ KTest,
          HasUniformTranslation.productMeasure E E J (badF K) ≤
            ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
        intro K hK
        have h := hBadF_K_bound K hK
        rw [← ENNReal.ofReal_toReal (hμF_finite K hK)]
        exact ENNReal.ofReal_le_ofReal h
      have hSumF_le :
          ∑ K ∈ KTest, HasUniformTranslation.productMeasure E E J (badF K) ≤
            ∑ _K ∈ KTest, ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) :=
        Finset.sum_le_sum hμF_le
      have hSumF_const :
          ∑ _K ∈ KTest, ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) =
            (KTest.card : ENNReal) * ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hμBad_le :
          HasUniformTranslation.productMeasure E E J Bad ≤
            ((NetED.card : ENNReal) + (KTest.card : ENNReal)) *
              ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
        calc HasUniformTranslation.productMeasure E E J Bad
            ≤ (∑ T₀ ∈ NetED, HasUniformTranslation.productMeasure E E J (badED T₀))
                + ∑ K ∈ KTest, HasUniformTranslation.productMeasure E E J (badF K) :=
              hUnion_le
          _ ≤ (∑ _T₀ ∈ NetED, ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)))
                + ∑ _K ∈ KTest, ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
              gcongr
          _ = (NetED.card : ENNReal) * ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A))
                + (KTest.card : ENNReal) * ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by
              rw [hSum_const, hSumF_const]
          _ = ((NetED.card : ENNReal) + (KTest.card : ENNReal)) *
                ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) := by ring
      have hε_budget_ne_top : ε_budget ≠ ⊤ := LT.lt.ne_top hε_budget_lt
      have hε_budget_toReal_pos : 0 < ε_budget.toReal := by
        rw [ENNReal.toReal_pos_iff]
        refine ⟨hε_budget_pos, ?_⟩
        exact lt_of_lt_of_le hε_budget_lt le_top
      have hε_budget_toReal_lt_one : ε_budget.toReal < 1 := by
        have h := (ENNReal.toReal_lt_toReal hε_budget_ne_top
          (by exact ENNReal.one_ne_top)).mpr hε_budget_lt
        simpa using h
      have hCε_pos' : 0 < Cε := hCε_pos
      have hδr_pos : (0 : ℝ) < (δ : ℝ) := hδ_pos
      have hδr_le_one : (δ : ℝ) ≤ 1 := hδ_lt_one.le
      have hδr_ne_zero : (δ : ℝ) ≠ 0 := ne_of_gt hδr_pos
      have hδ_rpow_pos : (0 : ℝ) < (δ : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hδr_pos (-ε)
      have hδ_rpow_ge_one : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε) := by
        rw [Real.rpow_neg hδr_pos.le]
        rw [one_le_inv_iff₀]
        refine ⟨?_, ?_⟩
        · exact Real.rpow_pos_of_pos hδr_pos ε
        · exact Real.rpow_le_one hδr_pos.le hδr_le_one (le_of_lt hε)
      have hδ_rpow_M_pos : 0 < (δ : ℝ) ^ (-(netGeomConstantM E)) :=
        Real.rpow_pos_of_pos hδr_pos _
      have hnetC_pos : 0 < netGeomConstantC E := netGeomConstantC_pos E
      have hnetM_pos : 0 < netGeomConstantM E := netGeomConstantM_pos E
      have hlog_inv_nn : 0 ≤ Real.log (1 / ε_budget.toReal) := by
        rw [Real.log_div one_ne_zero (ne_of_gt hε_budget_toReal_pos),
            Real.log_one, zero_sub]
        rw [neg_nonneg]
        exact Real.log_nonpos hε_budget_toReal_pos.le hε_budget_toReal_lt_one.le
      have hA_part1 : Cε * Real.log (1 / ε_budget.toReal) ≤ A := by
        have h1 : Cε * Real.log (1 / ε_budget.toReal) ≤
            Cε * ((δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal)) :=
          mul_le_mul_of_nonneg_left (by linarith [hδ_rpow_pos]) hCε_pos'.le
        linarith
      have hA_part2 : Cε * (δ : ℝ) ^ (-ε) ≤ A := by
        have h1 : Cε * (δ : ℝ) ^ (-ε) ≤
            Cε * ((δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal)) :=
          mul_le_mul_of_nonneg_left (by linarith [hlog_inv_nn]) hCε_pos'.le
        linarith
      have hε_log_inv : Real.exp (-Cε * Real.log (1 / ε_budget.toReal)) ≤ ε_budget.toReal :=
        Kakeya.exp_neg_mul_log_inv_le_self hε_budget_toReal_pos
          hε_budget_toReal_lt_one.le hCε_ge_one
      have hCε_ge :
          (netGeomConstantM E) / ε
            + Real.log (netGeomConstantC E + 1)
            + 10 * Real.exp 1
            + 1 ≤ Cε := by
        rw [hCε_def]
        have h1 := le_max_right (1 : ℝ)
          ((max (netGeomConstantM E) M_net) / ε
            + Real.log (max (netGeomConstantC E) C_net + 1)
            + Real.log 2
            + 10 * Real.exp 1
            + 1
            + (M_dim : ℝ) * (M_dim : ℝ)
            + (M_dim : ℝ) * (netGeomConstantM E / ε)
            + (M_dim : ℝ) *
                (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
            + 2 * (M_dim : ℝ) + 1)
        have hMle : (netGeomConstantM E) / ε ≤ (max (netGeomConstantM E) M_net) / ε :=
          div_le_div_of_nonneg_right (le_max_left _ _) hε.le
        have hClog_le : Real.log (netGeomConstantC E + 1) ≤
            Real.log (max (netGeomConstantC E) C_net + 1) := by
          apply Real.log_le_log (by linarith [netGeomConstantC_pos E])
          have := le_max_left (netGeomConstantC E) C_net
          linarith
        have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hM_dim_nn : (0 : ℝ) ≤ (M_dim : ℝ) := Nat.cast_nonneg _
        have hM_dim_sq_nn : (0 : ℝ) ≤ (M_dim : ℝ) * (M_dim : ℝ) :=
          mul_nonneg hM_dim_nn hM_dim_nn
        have hMdim_div_nn : (0 : ℝ) ≤ (M_dim : ℝ) * (netGeomConstantM E / ε) := by
          have : (0 : ℝ) ≤ netGeomConstantM E / ε := by positivity
          exact mul_nonneg hM_dim_nn this
        have hMdim_const_nn : (0 : ℝ) ≤ (M_dim : ℝ) *
            (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2) := by
          have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
          have hlog3C_nn : (0 : ℝ) ≤ Real.log (3 * netGeomConstantC E + 1) := by
            apply Real.log_nonneg
            have hC_pos := netGeomConstantC_pos E
            linarith
          have : (0 : ℝ) ≤ 10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2 := by
            linarith
          exact mul_nonneg hM_dim_nn this
        linarith
      have hcalib_main :
          netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) *
            Real.exp (10 * Real.exp 1 - A) ≤ ε_budget.toReal := by
        refine calibration_exp_of_log hδr_pos hnetC_pos hε_budget_toReal_pos ?_
        have hA_bound : Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) ≤ A := by
          have hexpand : Cε * ((δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal)) =
              Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) := by ring
          linarith [h_A, hexpand]
        have hMlog_le : (netGeomConstantM E) * (-Real.log (δ : ℝ)) ≤
            (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) :=
          Kakeya.neglog_le_rpow_div hδr_pos hδr_le_one hε hnetM_pos.le
        have hlogC_le : Real.log (netGeomConstantC E) ≤ Real.log (netGeomConstantC E + 1) := by
          apply Real.log_le_log hnetC_pos
          linarith
        have hδ_rpow_ge_one' : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε) := hδ_rpow_ge_one
        have hcombine : Real.log (netGeomConstantC E) + (netGeomConstantM E) * (-Real.log (δ : ℝ))
            + 10 * Real.exp 1 + Real.log (1 / ε_budget.toReal) ≤ A := by
          have hstep1 : Real.log (netGeomConstantC E) +
              (netGeomConstantM E) * (-Real.log (δ : ℝ)) + 10 * Real.exp 1 +
              Real.log (1 / ε_budget.toReal) ≤
            Real.log (netGeomConstantC E + 1) +
              (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) + 10 * Real.exp 1 +
              Real.log (1 / ε_budget.toReal) := by linarith
          have hMε_nn : 0 ≤ (netGeomConstantM E) / ε := by positivity
          have hlogC1_nn : 0 ≤ Real.log (netGeomConstantC E + 1) :=
            Real.log_nonneg (by linarith)
          have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
          have hbound_logC1 : Real.log (netGeomConstantC E + 1) ≤
              Real.log (netGeomConstantC E + 1) * (δ : ℝ) ^ (-ε) := by
            have : Real.log (netGeomConstantC E + 1) * 1 ≤
                Real.log (netGeomConstantC E + 1) * (δ : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_left hδ_rpow_ge_one' hlogC1_nn
            linarith
          have hbound_10e : 10 * Real.exp 1 ≤ 10 * Real.exp 1 * (δ : ℝ) ^ (-ε) := by
            have : 10 * Real.exp 1 * 1 ≤ 10 * Real.exp 1 * (δ : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_left hδ_rpow_ge_one' h10e_nn
            linarith
          have hsum_le_Cε_rpow :
              (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) +
              Real.log (netGeomConstantC E + 1) + 10 * Real.exp 1 ≤
              Cε * (δ : ℝ) ^ (-ε) := by
            calc (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) +
                  Real.log (netGeomConstantC E + 1) + 10 * Real.exp 1
                ≤ (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) +
                  Real.log (netGeomConstantC E + 1) * (δ : ℝ) ^ (-ε) +
                  10 * Real.exp 1 * (δ : ℝ) ^ (-ε) := by linarith
              _ = ((netGeomConstantM E) / ε +
                    Real.log (netGeomConstantC E + 1) +
                    10 * Real.exp 1) * (δ : ℝ) ^ (-ε) := by ring
              _ ≤ Cε * (δ : ℝ) ^ (-ε) := by
                  apply mul_le_mul_of_nonneg_right _ (le_of_lt hδ_rpow_pos)
                  linarith [hCε_ge]
          have hlog_inv_bound : Real.log (1 / ε_budget.toReal) ≤
              Cε * Real.log (1 / ε_budget.toReal) := by
            have : 1 * Real.log (1 / ε_budget.toReal) ≤
                Cε * Real.log (1 / ε_budget.toReal) :=
              mul_le_mul_of_nonneg_right hCε_ge_one hlog_inv_nn
            linarith
          calc Real.log (netGeomConstantC E) +
              (netGeomConstantM E) * (-Real.log (δ : ℝ)) + 10 * Real.exp 1 +
              Real.log (1 / ε_budget.toReal)
              ≤ Real.log (netGeomConstantC E + 1) +
                (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) + 10 * Real.exp 1 +
                Real.log (1 / ε_budget.toReal) := hstep1
            _ ≤ Cε * (δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal) := by linarith
            _ ≤ Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) := by linarith
            _ ≤ A := hA_bound
        linarith
      have hNetCardReal_nn : 0 ≤ (NetED.card : ℝ) := Nat.cast_nonneg _
      have hKTestCardReal_nn : 0 ≤ (KTest.card : ℝ) := Nat.cast_nonneg _
      have hexp_nn : 0 ≤ Real.exp (10 * Real.exp 1 - A) := (Real.exp_pos _).le
      have hcombo :
          ((NetED.card : ℝ) + (KTest.card : ℝ)) * Real.exp (10 * Real.exp 1 - A)
            ≤ ε_budget.toReal := by
        have hε_half_pos : 0 < ε_budget.toReal / 2 := by linarith
        have hε_half_lt_one : ε_budget.toReal / 2 < 1 := by linarith
        have hε_half_le_one : ε_budget.toReal / 2 ≤ 1 := hε_half_lt_one.le
        have hlog_inv_half_eq :
            Real.log (1 / (ε_budget.toReal / 2)) =
              Real.log 2 + Real.log (1 / ε_budget.toReal) := by
          have h2_pos : (0 : ℝ) < 2 := by norm_num
          rw [show (1 / (ε_budget.toReal / 2) : ℝ) = 2 * (1 / ε_budget.toReal) by
                field_simp]
          rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
                (by positivity : (1 / ε_budget.toReal : ℝ) ≠ 0)]
        have hlog_inv_half_nn : 0 ≤ Real.log (1 / (ε_budget.toReal / 2)) := by
          rw [Real.log_div one_ne_zero (ne_of_gt hε_half_pos), Real.log_one, zero_sub,
              neg_nonneg]
          exact Real.log_nonpos hε_half_pos.le hε_half_le_one
        have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hCε_ge' :
            (max (netGeomConstantM E) M_net) / ε
              + Real.log (max (netGeomConstantC E) C_net + 1)
              + Real.log 2
              + 10 * Real.exp 1
              + 1 ≤ Cε := by
          rw [hCε_def]
          have h1 := le_max_right (1 : ℝ)
            ((max (netGeomConstantM E) M_net) / ε
              + Real.log (max (netGeomConstantC E) C_net + 1)
              + Real.log 2
              + 10 * Real.exp 1
              + 1
              + (M_dim : ℝ) * (M_dim : ℝ)
              + (M_dim : ℝ) * (netGeomConstantM E / ε)
              + (M_dim : ℝ) *
                  (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2)
              + 2 * (M_dim : ℝ) + 1)
          have hM_dim_nn : (0 : ℝ) ≤ (M_dim : ℝ) := Nat.cast_nonneg _
          have hM_dim_sq_nn : (0 : ℝ) ≤ (M_dim : ℝ) * (M_dim : ℝ) :=
            mul_nonneg hM_dim_nn hM_dim_nn
          have hMdim_div_nn : (0 : ℝ) ≤ (M_dim : ℝ) * (netGeomConstantM E / ε) := by
            have : (0 : ℝ) ≤ netGeomConstantM E / ε := by positivity
            exact mul_nonneg hM_dim_nn this
          have hMdim_const_nn : (0 : ℝ) ≤ (M_dim : ℝ) *
              (10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2) := by
            have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
            have hlog3C_nn : (0 : ℝ) ≤ Real.log (3 * netGeomConstantC E + 1) := by
              apply Real.log_nonneg
              have hC_pos := netGeomConstantC_pos E
              linarith
            have : (0 : ℝ) ≤ 10 * Real.exp 1 + Real.log (3 * netGeomConstantC E + 1) + 2 := by
              linarith
            exact mul_nonneg hM_dim_nn this
          linarith
        have hhalf_NetED :
            netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) *
              Real.exp (10 * Real.exp 1 - A) ≤ ε_budget.toReal / 2 := by
          refine calibration_exp_of_log hδr_pos hnetC_pos hε_half_pos ?_
          rw [hlog_inv_half_eq]
          have hMε_le : (netGeomConstantM E) / ε ≤ (max (netGeomConstantM E) M_net) / ε := by
            apply div_le_div_of_nonneg_right (le_max_left _ _) hε.le
          have hlogC_le_max : Real.log (netGeomConstantC E + 1) ≤
              Real.log (max (netGeomConstantC E) C_net + 1) := by
            apply Real.log_le_log (by linarith)
            have := le_max_left (netGeomConstantC E) C_net
            linarith
          have hlogC_le : Real.log (netGeomConstantC E) ≤ Real.log (netGeomConstantC E + 1) := by
            apply Real.log_le_log hnetC_pos; linarith
          have hMlog_le : (netGeomConstantM E) * (-Real.log (δ : ℝ)) ≤
              (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) :=
            Kakeya.neglog_le_rpow_div hδr_pos hδr_le_one hε hnetM_pos.le
          have hMlog_le_max : (netGeomConstantM E) * (-Real.log (δ : ℝ)) ≤
              (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) := by
            calc (netGeomConstantM E) * (-Real.log (δ : ℝ))
                ≤ (netGeomConstantM E) / ε * (δ : ℝ) ^ (-ε) := hMlog_le
              _ ≤ (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) :=
                  mul_le_mul_of_nonneg_right hMε_le hδ_rpow_pos.le
          have hδ_rpow_ge_one' : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε) := hδ_rpow_ge_one
          have hMε_nn : 0 ≤ (max (netGeomConstantM E) M_net) / ε := by
            have : 0 ≤ max (netGeomConstantM E) M_net :=
              le_max_of_le_left hnetM_pos.le
            positivity
          have hlogCmax1_nn : 0 ≤ Real.log (max (netGeomConstantC E) C_net + 1) :=
            Real.log_nonneg (by
              have := le_max_left (netGeomConstantC E) C_net
              linarith)
          have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
          have hlog2_mul_nn : 0 ≤ Real.log 2 * (δ : ℝ) ^ (-ε) :=
            mul_nonneg hlog2_nn hδ_rpow_pos.le
          have hbound_logCmax1 : Real.log (max (netGeomConstantC E) C_net + 1) ≤
              Real.log (max (netGeomConstantC E) C_net + 1) * (δ : ℝ) ^ (-ε) := by
            have : Real.log (max (netGeomConstantC E) C_net + 1) * 1 ≤
                Real.log (max (netGeomConstantC E) C_net + 1) * (δ : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_left hδ_rpow_ge_one' hlogCmax1_nn
            linarith
          have hbound_log2 : Real.log 2 ≤ Real.log 2 * (δ : ℝ) ^ (-ε) := by
            have : Real.log 2 * 1 ≤ Real.log 2 * (δ : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_left hδ_rpow_ge_one' hlog2_nn
            linarith
          have hbound_10e : 10 * Real.exp 1 ≤ 10 * Real.exp 1 * (δ : ℝ) ^ (-ε) := by
            have : 10 * Real.exp 1 * 1 ≤ 10 * Real.exp 1 * (δ : ℝ) ^ (-ε) :=
              mul_le_mul_of_nonneg_left hδ_rpow_ge_one' h10e_nn
            linarith
          have hsum_le_Cε_rpow :
              (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) +
                Real.log (max (netGeomConstantC E) C_net + 1) +
                Real.log 2 + 10 * Real.exp 1 ≤
              Cε * (δ : ℝ) ^ (-ε) := by
            calc (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) +
                  Real.log (max (netGeomConstantC E) C_net + 1) +
                  Real.log 2 + 10 * Real.exp 1
                ≤ (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) +
                  Real.log (max (netGeomConstantC E) C_net + 1) * (δ : ℝ) ^ (-ε) +
                  Real.log 2 * (δ : ℝ) ^ (-ε) +
                  10 * Real.exp 1 * (δ : ℝ) ^ (-ε) := by linarith
              _ = ((max (netGeomConstantM E) M_net) / ε +
                    Real.log (max (netGeomConstantC E) C_net + 1) +
                    Real.log 2 +
                    10 * Real.exp 1) * (δ : ℝ) ^ (-ε) := by ring
              _ ≤ Cε * (δ : ℝ) ^ (-ε) := by
                  apply mul_le_mul_of_nonneg_right _ hδ_rpow_pos.le
                  linarith [hCε_ge']
          have hlog_inv_bound : Real.log (1 / ε_budget.toReal) ≤
              Cε * Real.log (1 / ε_budget.toReal) := by
            have : 1 * Real.log (1 / ε_budget.toReal) ≤
                Cε * Real.log (1 / ε_budget.toReal) :=
              mul_le_mul_of_nonneg_right hCε_ge_one hlog_inv_nn
            linarith
          have hA_bound : Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) ≤ A := by
            have hexpand : Cε * ((δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal)) =
                Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) := by ring
            linarith [h_A, hexpand]
          have hcombine :
              Real.log (netGeomConstantC E) + (netGeomConstantM E) * (-Real.log (δ : ℝ))
              + 10 * Real.exp 1 + (Real.log 2 + Real.log (1 / ε_budget.toReal)) ≤ A := by
            calc Real.log (netGeomConstantC E) +
                (netGeomConstantM E) * (-Real.log (δ : ℝ)) + 10 * Real.exp 1 +
                (Real.log 2 + Real.log (1 / ε_budget.toReal))
                ≤ Real.log (max (netGeomConstantC E) C_net + 1) +
                  (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) + 10 * Real.exp 1 +
                  (Real.log 2 + Real.log (1 / ε_budget.toReal)) := by linarith
              _ ≤ Cε * (δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal) := by linarith
              _ ≤ Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) := by linarith
              _ ≤ A := hA_bound
          linarith
        have hδ_rpow_Mnet_pos : 0 < (δ : ℝ) ^ (-M_net) :=
          Real.rpow_pos_of_pos hδr_pos _
        have hhalf_KTest :
            C_net * (δ : ℝ) ^ (-M_net) *
              Real.exp (10 * Real.exp 1 - A) ≤ ε_budget.toReal / 2 := by
          have hcalib_KTest :
              C_net * (δ : ℝ) ^ (-M_net) *
                Real.exp (10 * Real.exp 1 - A) ≤ ε_budget.toReal / 2 := by
            refine calibration_exp_of_log hδr_pos hC_net_pos hε_half_pos ?_
            rw [hlog_inv_half_eq]
            have hlogCnet_le : Real.log C_net ≤
                Real.log (max (netGeomConstantC E) C_net + 1) := by
              refine Real.log_le_log hC_net_pos ?_
              have := le_max_right (netGeomConstantC E) C_net
              linarith
            have hMε_le : M_net / ε ≤ (max (netGeomConstantM E) M_net) / ε :=
              div_le_div_of_nonneg_right (le_max_right _ _) hε.le
            have hMlog_le_max : M_net * (-Real.log (δ : ℝ)) ≤
                (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) :=
              (Kakeya.neglog_le_rpow_div hδr_pos hδr_le_one hε hM_net_pos.le).trans
                (mul_le_mul_of_nonneg_right hMε_le hδ_rpow_pos.le)
            have hδ_rpow_ge_one' : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε) := hδ_rpow_ge_one
            have hlogCmax1_nn : 0 ≤ Real.log (max (netGeomConstantC E) C_net + 1) :=
              Real.log_nonneg (by
                have := le_max_left (netGeomConstantC E) C_net
                linarith)
            have h10e_nn : 0 ≤ 10 * Real.exp 1 := by positivity
            have hMε_nn : 0 ≤ (max (netGeomConstantM E) M_net) / ε := by
              have : 0 ≤ max (netGeomConstantM E) M_net :=
                le_max_of_le_left hnetM_pos.le
              positivity
            have hbound_logCmax1 :
                Real.log (max (netGeomConstantC E) C_net + 1) ≤
                Real.log (max (netGeomConstantC E) C_net + 1) * (δ : ℝ) ^ (-ε) := by
              have := mul_le_mul_of_nonneg_left hδ_rpow_ge_one' hlogCmax1_nn
              linarith
            have hbound_log2 : Real.log 2 ≤ Real.log 2 * (δ : ℝ) ^ (-ε) := by
              have := mul_le_mul_of_nonneg_left hδ_rpow_ge_one' hlog2_nn
              linarith
            have hbound_10e : 10 * Real.exp 1 ≤ 10 * Real.exp 1 * (δ : ℝ) ^ (-ε) := by
              have := mul_le_mul_of_nonneg_left hδ_rpow_ge_one' h10e_nn
              linarith
            have hsum_le_Cε_rpow :
                (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) +
                  Real.log (max (netGeomConstantC E) C_net + 1) +
                  Real.log 2 + 10 * Real.exp 1 ≤
                Cε * (δ : ℝ) ^ (-ε) := by
              calc (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) +
                    Real.log (max (netGeomConstantC E) C_net + 1) +
                    Real.log 2 + 10 * Real.exp 1
                  ≤ (max (netGeomConstantM E) M_net) / ε * (δ : ℝ) ^ (-ε) +
                    Real.log (max (netGeomConstantC E) C_net + 1) * (δ : ℝ) ^ (-ε) +
                    Real.log 2 * (δ : ℝ) ^ (-ε) +
                    10 * Real.exp 1 * (δ : ℝ) ^ (-ε) := by linarith
                _ = ((max (netGeomConstantM E) M_net) / ε +
                      Real.log (max (netGeomConstantC E) C_net + 1) +
                      Real.log 2 + 10 * Real.exp 1) * (δ : ℝ) ^ (-ε) := by ring
                _ ≤ Cε * (δ : ℝ) ^ (-ε) :=
                    mul_le_mul_of_nonneg_right (by linarith [hCε_ge']) hδ_rpow_pos.le
            have hlog_inv_bound : Real.log (1 / ε_budget.toReal) ≤
                Cε * Real.log (1 / ε_budget.toReal) := by
              have := mul_le_mul_of_nonneg_right hCε_ge_one hlog_inv_nn
              linarith
            have hA_bound : Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) ≤ A := by
              have hexpand : Cε * ((δ : ℝ) ^ (-ε) + Real.log (1 / ε_budget.toReal)) =
                  Cε * (δ : ℝ) ^ (-ε) + Cε * Real.log (1 / ε_budget.toReal) := by ring
              linarith [h_A, hexpand]
            linarith [hlogCnet_le, hMlog_le_max, hsum_le_Cε_rpow, hlog_inv_bound, hA_bound]
          linarith [hcalib_KTest]
        have hexp_nn : 0 ≤ Real.exp (10 * Real.exp 1 - A) := (Real.exp_pos _).le
        have hNetED_mul_le :
            (NetED.card : ℝ) * Real.exp (10 * Real.exp 1 - A) ≤ ε_budget.toReal / 2 := by
          calc (NetED.card : ℝ) * Real.exp (10 * Real.exp 1 - A)
              ≤ (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) *
                  Real.exp (10 * Real.exp 1 - A) :=
                mul_le_mul_of_nonneg_right hNetED_card hexp_nn
            _ = netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)) *
                  Real.exp (10 * Real.exp 1 - A) := by ring
            _ ≤ ε_budget.toReal / 2 := hhalf_NetED
        have hKTest_mul_le :
            (KTest.card : ℝ) * Real.exp (10 * Real.exp 1 - A) ≤ ε_budget.toReal / 2 := by
          calc (KTest.card : ℝ) * Real.exp (10 * Real.exp 1 - A)
              ≤ (C_net * (δ : ℝ) ^ (-M_net)) * Real.exp (10 * Real.exp 1 - A) :=
                mul_le_mul_of_nonneg_right hKTest_card hexp_nn
            _ = C_net * (δ : ℝ) ^ (-M_net) * Real.exp (10 * Real.exp 1 - A) := by ring
            _ ≤ ε_budget.toReal / 2 := hhalf_KTest
        have hsum_eq :
            ((NetED.card : ℝ) + (KTest.card : ℝ)) * Real.exp (10 * Real.exp 1 - A) =
              (NetED.card : ℝ) * Real.exp (10 * Real.exp 1 - A) +
              (KTest.card : ℝ) * Real.exp (10 * Real.exp 1 - A) := by ring
        linarith [hNetED_mul_le, hKTest_mul_le, hsum_eq]
      have hSumCardReal_nn : 0 ≤ (NetED.card : ℝ) + (KTest.card : ℝ) :=
        add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hENN_le :
          ((NetED.card : ENNReal) + (KTest.card : ENNReal)) *
              ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) ≤
          ENNReal.ofReal ε_budget.toReal := by
        have h1 :
            ((NetED.card : ENNReal) + (KTest.card : ENNReal)) *
                ENNReal.ofReal (Real.exp (10 * Real.exp 1 - A)) =
            ENNReal.ofReal
              (((NetED.card : ℝ) + (KTest.card : ℝ)) * Real.exp (10 * Real.exp 1 - A)) := by
          rw [ENNReal.ofReal_mul hSumCardReal_nn,
              ENNReal.ofReal_add hNetCardReal_nn hKTestCardReal_nn,
              ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        rw [h1]
        exact ENNReal.ofReal_le_ofReal hcombo
      have hENN_ofReal_eq : ENNReal.ofReal ε_budget.toReal = ε_budget := by
        exact ENNReal.ofReal_toReal hε_budget_ne_top
      rw [hENN_ofReal_eq] at hENN_le
      exact le_trans hμBad_le hENN_le
    refine ⟨Bad, hBad_meas, hMeasure_bound, ?_⟩
    intro ω _hω_notMem
    have h_per_T₀_bound : ∀ T₀ ∈ NetED,
        (∑ j : Fin J, HasUniformTranslation.productTubeContainedCount
            (Ω := E) s T (K_truncated T₀) J j ω : ℝ) ≤ A * M_ED_const := by
      intro T₀ hT₀
      by_contra h_gt
      push Not at h_gt
      apply _hω_notMem
      rw [hBad_def]
      exact Or.inl (Or.inl (Set.mem_biUnion hT₀ h_gt))
    have h_per_K_bound : ∀ K ∈ KTest,
        (∑ j : Fin J, scaledProductTubeContainedCount (r : ℝ) s T K.carrier J j ω : ℝ)
          ≤ A * M_F K := by
      intro K hK
      by_contra h_gt
      push Not at h_gt
      apply _hω_notMem
      rw [hBad_def]
      exact Or.inl (Or.inr (Set.mem_biUnion hK h_gt))
    have hω_inBall : ∀ j, ω j ∈ Metric.closedBall (0 : E) 1 := by
      intro j
      by_contra h_notMem
      apply _hω_notMem
      rw [hBad_def]
      exact Or.inr ⟨j, h_notMem⟩
    have hCε_le_A : Cε ≤ A :=
      Kakeya.le_of_mul_add_le_of_one_le Cε A hCε_pos.le
        hδ_rpow_ge_one_C hlog_inv_nn_C h_A
    have hA_ge_one : (1 : ℝ) ≤ A := hCε_ge_one.trans hCε_le_A
    have hJ_pos : 0 < J := by omega
    have hA_pos : 0 < A := by linarith
    have hω_j_norm : ∀ j, ‖(r : ℝ) • ω j‖ ≤ (r : ℝ) := by
      intro j
      have hnorm : ‖ω j‖ ≤ 1 := by
        have h := hω_inBall j
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h
      calc
        ‖(r : ℝ) • ω j‖ = |(r : ℝ)| * ‖ω j‖ := norm_smul (r : ℝ) (ω j)
        _ = (r : ℝ) * ‖ω j‖ := by rw [abs_of_nonneg (by exact_mod_cast NNReal.coe_nonneg r)]
        _ ≤ (r : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hnorm (by exact_mod_cast NNReal.coe_nonneg r)
        _ = (r : ℝ) := by simp
    have hTranslated_in_B5 : ∀ p : ι × Fin J, p.1 ∈ s →
        ((T p.1).translate ((r : ℝ) • ω p.2)).carrier ⊆ Metric.closedBall (0 : E) 5 := by
      intro p hp
      rcases p with ⟨i, j⟩
      have hi : i ∈ s := hp
      set v := (r : ℝ) • ω j with hv_def
      have hv_norm : ‖v‖ ≤ (r : ℝ) := hω_j_norm j
      have h_carrier_eq : ((T i).translate v).carrier = (v + ·) '' (T i).carrier := by
        simp [Tube.translate]
      rw [h_carrier_eq]
      intro x hx
      rcases hx with ⟨y, hy, hx_eq⟩
      have hy_in_B4 : y ∈ Metric.closedBall (0 : E) 4 :=
        hTρ_ball (hT_in_Tρ i hi hy)
      have hy_norm : ‖y‖ ≤ 4 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hy_in_B4
        exact hy_in_B4
      have h_norm_v_bound : ‖v‖ ≤ 1 := by
        calc
          ‖v‖ ≤ (r : ℝ) := hv_norm
          _ ≤ (ρ : ℝ) := hr_le
          _ ≤ 1 := hρ_le
      have hx_norm : ‖x‖ ≤ 5 := by
        calc
          ‖x‖ = ‖v + y‖ := by rw [← hx_eq]
          _ ≤ ‖v‖ + ‖y‖ := norm_add_le v y
          _ ≤ 1 + 4 := add_le_add h_norm_v_bound hy_norm
          _ = 5 := by norm_num
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hx_norm
    have hM_dens_one : (1 : ℝ) ≤ M_dens := by
      have hvol_pos : 0 < volume (T i₀).carrier := by
        have h_tubeVol_pos : 0 <
            (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
          ENNReal.mul_pos
            (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos _).ne')
            (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ_nn_pos.ne'))
        have h_tubeVol_le := Tube.le_volume (T i₀)
        exact lt_of_lt_of_le h_tubeVol_pos h_tubeVol_le
      have h_one_le_max : (1 : ENNReal) ≤ maxDensity s (fun i => (T i).toConvexSpaceBody) :=
        one_le_maxDensity ⟨i₀, hi₀_mem, hvol_pos⟩
      have hmax_ne_top : maxDensity s (fun i => (T i).toConvexSpaceBody) ≠ ⊤ :=
        maxDensity_ne_top _ _
      have h_one_toReal : (1 : ℝ) ≤ (maxDensity s (fun i => (T i).toConvexSpaceBody)).toReal := by
        simpa [ENNReal.toReal_one] using ENNReal.toReal_mono hmax_ne_top h_one_le_max
      linarith
    set T_tr : ι × Fin J → ShadedTube δ E := fun p =>
      if p.1 ∈ s then
        { toTube := (T p.1).translate ((r : ℝ) • ω p.2), shade := ∅,
          shade_subset := Set.empty_subset _, measurableSet_shade := MeasurableSet.empty }
      else
        { toTube := (T i₀).translate ((r : ℝ) • ω p.2), shade := ∅,
          shade_subset := Set.empty_subset _, measurableSet_shade := MeasurableSet.empty }
      with hT_tr_def
    have hT_tr_in_B5 : ∀ p : ι × Fin J, (T_tr p).carrier ⊆ Metric.closedBall (0 : E) 5 := by
      intro p
      by_cases hp : p.1 ∈ s
      · have h := hTranslated_in_B5 p hp
        simpa [hT_tr_def, hp] using h
      · have h := hTranslated_in_B5 (i₀, p.2) hi₀_mem
        simpa [hT_tr_def, hp] using h
    have hT_tr_eq : ∀ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)),
        (T_tr p).toConvexSpaceBody
          = ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody := by
      intro p hp
      have hp1 : p.1 ∈ s := (Finset.mem_product.mp hp).1
      simp [hT_tr_def, hp1]
    have h_density_full :
        maxDensity (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) ≤
          ENNReal.ofReal (C_dens * A * M_dens) := by
      obtain ⟨K, hK, hK_bound⟩ :=
        hKTest_cover (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (T_tr p).toConvexSpaceBody)
          (fun p _ => by simpa using hT_tr_in_B5 p)
          (fun p _ => Tube.le_ethickness_scale (T_tr p).toTube)
      have h_maxDensity_congr : maxDensity (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (T_tr p).toConvexSpaceBody) = maxDensity (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) :=
        maxDensity_congr hT_tr_eq
      have h_densityIn_congr : densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (T_tr p).toConvexSpaceBody) K = densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) K :=
        densityIn_congr hT_tr_eq
      rw [h_maxDensity_congr, h_densityIn_congr] at hK_bound
      have hcount : (((s ×ˢ (Finset.univ : Finset (Fin J))).filter
            (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody ≤ K)).card : ℝ) ≤
          A * max (M_dens * volume.real K.carrier /
            ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
              (δ : ℝ) ^ (Module.finrank ℝ E - 1))) 1 := by
        have hM_F_K : M_F K = max (M_dens * volume.real K.carrier /
            ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
              (δ : ℝ) ^ (Module.finrank ℝ E - 1))) 1 := rfl
        have h_per_K_bound_K := h_per_K_bound K hK
        have h_sum_eq : (∑ j : Fin J,
            scaledProductTubeContainedCount (r : ℝ) s T K.carrier J j ω : ℝ) =
          (((s ×ˢ (Finset.univ : Finset (Fin J))).filter
            (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody ≤ K)).card : ℝ) := by
          simpa using sum_scaledProductTubeContainedCount_eq_filter_card s T K (r : ℝ) ω
        rw [h_sum_eq, hM_F_K] at h_per_K_bound_K
        exact h_per_K_bound_K
      have hδ_le : (δ : ℝ) ≤ 1 := hδ_lt_one.le
      have h_densityIn_bound : densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) K ≤
        ENNReal.ofReal (A * M_dens * ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
          (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))) :=
        densityIn_le_of_count hδ_pos hδ_le s T (fun j => (r : ℝ) • ω j) K M_dens A
          hM_dens_one hA_ge_one hcount
      calc
        maxDensity (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) ≤
          ENNReal.ofReal C_net * densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
              (fun p => ((T p.1).translate ((r : ℝ) • ω p.2)).toConvexSpaceBody) K := by
            refine hK_bound.trans (mul_le_mul' ?_ le_rfl)
            rw [← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal hCprism_le_C_net
        _ ≤ ENNReal.ofReal C_net * ENNReal.ofReal (A * M_dens *
            ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
              (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))) :=
          mul_le_mul_of_nonneg_left h_densityIn_bound (by positivity)
        _ = ENNReal.ofReal (C_net * (A * M_dens *
            ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
              (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))) := by
          rw [ENNReal.ofReal_mul hC_net_pos.le]
        _ = ENNReal.ofReal (C_net * K_vol * A * M_dens) := by
          dsimp [K_vol]
          ring_nf
        _ = ENNReal.ofReal (C_dens * A * M_dens) := by
          rw [hC_dens_def]
    have hcard_prod : ((s ×ˢ (Finset.univ : Finset (Fin J))).card : ℝ) =
          (s.card : ℝ) * (J : ℝ) := by
      rw [Finset.card_product]
      simp
    refine ⟨s ×ˢ Finset.univ, hω_j_norm, Finset.Subset.refl _, ?_, ?_, h_density_full,
      h_density_full⟩
    · rw [hcard_prod]
      have h_sc_nonneg : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
      have hJ_nonneg : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
      have hAinv_le_one : A⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr hA_ge_one
      calc
        A⁻¹ * (J : ℝ) * (s.card : ℝ) ≤ 1 * (J : ℝ) * (s.card : ℝ) := by
          have := mul_le_mul_of_nonneg_right hAinv_le_one hJ_nonneg
          exact mul_le_mul_of_nonneg_right this h_sc_nonneg
        _ = (s.card : ℝ) * (J : ℝ) := by ring
    · rw [hcard_prod]
      exact le_of_eq (by ring)
  · exact absurd hδ_lt1 hδ_lt_one

end Kakeya.RandomTranslation
