/-
# BV Compactness for Sequences via Translation Continuity

Sequence version of BV compactness: given a sequence of measurable sets
with uniform volume bounds and uniform translation continuity on compact
sets, extract an L¹_loc-convergent subsequence.

This is the form needed by the blow-up lemma.

## Main result

- `bv_compactness_sequence_of_translation`: sequence version

## Proof route

Same ball-average mollification + diagonal extraction pipeline as
`bv_compactness_of_translation`, but applied to an arbitrary sequence
rather than a continuous family indexed by `r : ℝ`.

## References

- Ambrosio-Fusco-Pallara, Functions of BV, Theorem 3.23
- Maggi, Sets of Finite Perimeter, Theorem 12.26
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.Helpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.BVCauchy
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.Compatibility
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- **BV compactness for indicator sequences** (via translation continuity).

Given a sequence `E_k` of measurable sets with uniform volume bounds and
uniform translation continuity on every compact set, there exists a
measurable set `F` and a strictly increasing `subseq` such that
`E_{subseq k} → F` in L¹_loc (symmetric difference volume → 0 on every
compact set). -/
theorem bv_compactness_sequence_of_translation
    {E_seq : ℕ → Set (E n)}
    (h_meas : ∀ k, MeasurableSet (E_seq k))
    (h_vol : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ k, volume (E_seq k ∩ K) ≤ C)
    (h_trans : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ k, ∀ (h : E n),
        volume (symmDiff (E_seq k) ((fun x => x + h) '' (E_seq k)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖)) :
    ∃ (F : Set (E n)) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      MeasurableSet F ∧
      ∀ (K : Set (E n)), IsCompact K →
        Tendsto (fun k => volume (symmDiff (E_seq (subseq k)) F ∩ K))
          atTop (nhds 0) := by
  -- 1. Setup
  let K : ℕ → Set (E n) := fun j => closedBall (0 : E n) (j + 1 : ℝ)
  have hK_compact : ∀ j, IsCompact (K j) := by intro j; exact isCompact_closedBall _ _
  have hK_meas : ∀ j, MeasurableSet (K j) := by intro j; exact isClosed_closedBall.measurableSet
  have hK_fin : ∀ j, volume (K j) ≠ ⊤ := by intro j; exact (hK_compact j).measure_lt_top.ne
  have hK_exhaust : ∀ (K' : Set (E n)), IsCompact K' → ∃ j, K' ⊆ K j := by
    intro K' hK'; have hbdd : Bornology.IsBounded K' := hK'.isBounded
    rcases hbdd.subset_closedBall (0 : E n) with ⟨R, hR⟩
    refine ⟨Nat.ceil R + 1, ?_⟩
    intro x hx; have hdist : dist x 0 ≤ R := hR hx
    simpa [K, mem_closedBall, dist_zero_right] using le_trans hdist (by linarith [Nat.le_ceil R])
  let ε : ℕ → ℝ := fun m => 1 / (m + 1 : ℝ)
  have hε_pos : ∀ m, 0 < ε m := by intro m; positivity
  have hε_le_one : ∀ m, ε m ≤ 1 := by
    intro m; have h : (1 : ℝ) / (m + 1 : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr <;> linarith
    exact h
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have h1 : Tendsto (fun m : ℕ => (m + 1 : ℝ)) atTop atTop := by
      apply Filter.tendsto_atTop_atTop.mpr; intro b
      refine ⟨Nat.ceil b, fun k hk => ?_⟩
      have h5 : (k : ℝ) ≥ (Nat.ceil b : ℝ) := by exact_mod_cast hk
      linarith [Nat.le_ceil b]
    have h2 : Tendsto (fun m : ℕ => ((m + 1 : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 : (fun m : ℕ => ((m + 1 : ℝ))⁻¹) = ε := by funext m; simp [ε, one_div]
    rw [h3] at h2; exact h2
  let K' : ℕ → Set (E n) := fun j => closedBall (0 : E n) (j + 2 : ℝ)
  have hK'_compact : ∀ j, IsCompact (K' j) := by intro j; exact isCompact_closedBall _ _
  have hK'_neigh : ∀ j m x, x ∈ K j → ∀ (h : E n), ‖h‖ < ε m → x + h ∈ K' j := by
    intro j m x hx h hnorm
    have h1 : ‖x + h‖ ≤ ‖x‖ + ‖h‖ := norm_add_le _ _
    have h2 : ‖x‖ ≤ (j + 1 : ℝ) := by simpa [K, mem_closedBall, dist_zero_right] using hx
    have h3 : ‖x + h‖ ≤ (j + 2 : ℝ) := by linarith [hε_le_one m]
    simpa [K', mem_closedBall, dist_zero_right] using h3

  -- 2. Translation constants
  have h_error_const : ∀ j, ∃ (C : ℝ), 0 ≤ C ∧
      ∀ k, ∀ (h : E n),
        volume (symmDiff (E_seq k) ((fun x => x + h) '' (E_seq k)) ∩ K' j) ≤
        ENNReal.ofReal (C * ‖h‖) := by
    intro j
    rcases h_trans (K' j) (hK'_compact j) with ⟨C, hC⟩
    by_cases h : 0 ≤ C
    · exact ⟨C, h, hC⟩
    · have hC' : ∀ k, ∀ (hvec : E n),
          volume (symmDiff (E_seq k) ((fun x => x + hvec) '' (E_seq k)) ∩ K' j) ≤
          ENNReal.ofReal ((0 : ℝ) * ‖hvec‖) := by
        intro k hvec
        have hneg : C * ‖hvec‖ ≤ 0 := by
          have hCneg : C < 0 := by linarith
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        have h9 : ENNReal.ofReal (C * ‖hvec‖) = 0 := by rw [ENNReal.ofReal_eq_zero.mpr hneg]
        have h10 := hC k hvec
        rw [h9] at h10; simpa using h10
      exact ⟨0, by norm_num, hC'⟩
  choose C_j hCj_nonneg hCj using h_error_const

  -- 3. Define f and verify hypotheses
  let f : ℕ → ℕ → (E n → ℝ) := fun k m x => (ballAverage (E_seq k) (ε m) x).toReal
  have h_bounded : ∀ k m x, 0 ≤ f k m x ∧ f k m x ≤ 1 := by
    intro k m x; exact ballAverage_bounded (hε_pos m) x
  have h_cont : ∀ k m, Continuous (f k m) := by
    intro k m; exact (ballAverage_equicontinuous (hε_pos m)).continuous (E_seq k)
  have h_eqcont : ∀ j m, EquicontinuousOn (fun k => f k m) (K j) := by
    intro j m
    have h : Equicontinuous (fun k : ℕ => f k m) :=
      (ballAverage_equicontinuous (hε_pos m)).comp (fun k => E_seq k)
    exact h.equicontinuousOn (K j)

  -- 4. Diagonal extraction
  rcases diagonal_extraction f K hK_compact h_bounded h_cont h_eqcont with ⟨subseq, hsub_strict, h_conv⟩

  -- 5. L¹ error bound for each j, m, k
  have h_l1_error : ∀ j m k,
      ∫ x in K j, |f (subseq k) m x - Set.indicator (E_seq (subseq k)) (1 : E n → ℝ) x| ≤ C_j j * ε m := by
    intro j m k
    exact l1_error_bound (h_meas (subseq k)) (hK_meas j) (hK_fin j) (ε m) (hε_pos m)
      (C_j j) (hCj_nonneg j) (K' j) (hK'_neigh j m)
      (hCj j (subseq k))

  -- 6. For each j, get pointwise limit g_{j,m} and L¹ convergence of f
  have h_f_l1_conv : ∀ j m, ∃ (gjm : E n → ℝ),
      ContinuousOn gjm (K j) ∧
      (∀ x ∈ K j, 0 ≤ gjm x ∧ gjm x ≤ 1) ∧
      Tendsto (fun k => ∫ x in K j, |f (subseq k) m x - gjm x|) atTop (nhds 0) := by
    intro j m
    rcases h_conv j m with ⟨gjm, hg_cont, hg_tendsto⟩
    have h_gjm_bound : ∀ x ∈ K j, 0 ≤ gjm x ∧ gjm x ≤ 1 := by
      intro x hx
      have h3 : Tendsto (fun k => f (subseq k) m x) atTop (nhds (gjm x)) := hg_tendsto x hx
      have h4 : ∀ k, 0 ≤ f (subseq k) m x := fun k => (h_bounded (subseq k) m x).1
      have h5 : ∀ k, f (subseq k) m x ≤ 1 := fun k => (h_bounded (subseq k) m x).2
      exact ⟨ge_of_tendsto h3 (Eventually.of_forall h4),
        le_of_tendsto h3 (Eventually.of_forall h5)⟩
    refine ⟨gjm, hg_cont, h_gjm_bound, ?_⟩
    let μ := volume.restrict (K j)
    let Fseq : ℕ → (E n → ℝ) := fun k x => |f (subseq k) m x - gjm x|
    have hF_meas : ∀ k, AEStronglyMeasurable (Fseq k) μ := by
      intro k
      have h1 : AEStronglyMeasurable (f (subseq k) m) μ :=
        (h_cont (subseq k) m).measurable.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      have h2 : AEStronglyMeasurable gjm μ :=
        hg_cont.aestronglyMeasurable (hK_meas j)
      have h3 : AEStronglyMeasurable (f (subseq k) m - gjm) μ :=
        AEStronglyMeasurable.sub h1 h2
      have h4 : AEStronglyMeasurable (Fseq k) μ := h3.norm
      exact h4
    have h_bound_ae : ∀ k, ∀ᵐ x ∂μ, ‖Fseq k x‖ ≤ 2 := by
      intro k
      filter_upwards [ae_restrict_mem (hK_meas j)] with x hx
      have h1 : 0 ≤ f (subseq k) m x ∧ f (subseq k) m x ≤ 1 := h_bounded (subseq k) m x
      have h2 : 0 ≤ gjm x ∧ gjm x ≤ 1 := h_gjm_bound x hx
      have h3 : |f (subseq k) m x - gjm x| ≤ 2 := by
        have h4 : -1 ≤ f (subseq k) m x - gjm x := by linarith
        have h5 : f (subseq k) m x - gjm x ≤ 1 := by linarith
        rw [abs_le] <;> constructor <;> linarith
      have h3' : ‖Fseq k x‖ ≤ 2 := by
        have h_eq : ‖Fseq k x‖ = |f (subseq k) m x - gjm x| := by
          simp [Fseq, Real.norm_eq_abs] <;> rfl
        rw [h_eq]; exact h3
      exact h3'
    have h_lim_ae : ∀ᵐ x ∂μ, Tendsto (fun k => Fseq k x) atTop (nhds 0) := by
      filter_upwards [ae_restrict_mem (hK_meas j)] with x hx
      have h : Tendsto (fun k => f (subseq k) m x) atTop (nhds (gjm x)) := hg_tendsto x hx
      have h_sub : Tendsto (fun k : ℕ => f (subseq k) m x - gjm x) atTop (nhds 0) := by
        have h' : Tendsto (fun k : ℕ => f (subseq k) m x - gjm x) atTop (nhds (gjm x - gjm x)) :=
          h.sub (tendsto_const_nhds (x := gjm x))
        have h_zero : gjm x - gjm x = 0 := by ring
        simpa [h_zero] using h'
      have h_abs : Tendsto (fun k => Fseq k x) atTop (nhds 0) := by
        have h := h_sub.abs
        simpa [Fseq] using h
      exact h_abs
    have h_lt : volume (K j) < ⊤ := IsCompact.measure_lt_top (hK_compact j)
    letI : IsFiniteMeasure μ := by
      constructor
      simpa [μ] using h_lt
    have h_bound_int : Integrable (fun _ : E n => (2 : ℝ)) μ := integrable_const (2 : ℝ)
    have h_main : Tendsto (fun k => ∫ x, Fseq k x ∂μ) atTop (nhds 0) := by
      have h := MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun _ => (2 : ℝ))
        (F_measurable := hF_meas)
        (bound_integrable := h_bound_int)
        (h_bound := h_bound_ae)
        (h_lim := h_lim_ae)
      simpa using h
    exact h_main
  choose gjm hgjm_cont hgjm_bound hgjm_l1 using h_f_l1_conv

  -- 7. Define h_k := indicator(E(subseq k))
  let h : ℕ → (E n → ℝ) := fun k => Set.indicator (E_seq (subseq k)) (1 : E n → ℝ)
  have h_meas_h : ∀ k, Measurable (h k) := by
    intro k
    exact measurable_const.indicator (h_meas (subseq k))
  have h_bound_h : ∀ k x, |h k x| ≤ 1 := by
    intro k x
    have h1 : h k x = 0 ∨ h k x = 1 := by
      by_cases h2 : x ∈ E_seq (subseq k) <;> simp [h, Set.indicator_apply, h2]
    rcases h1 with (h1 | h1) <;> rw [h1] <;> norm_num
  have h_binary_h : ∀ k x, h k x = 0 ∨ h k x = 1 := by
    intro k x
    by_cases h2 : x ∈ E_seq (subseq k) <;> simp [h, Set.indicator_apply, h2] <;> tauto

  -- 8. L¹-Cauchy of h_k on each K_j
  have h_cauchy_real : ∀ j, ∀ (eps : ℝ), 0 < eps → ∃ N, ∀ k l, N ≤ k → N ≤ l →
      ∫ x in K j, |h k x - h l x| ≤ eps := by
    intro j
    let f' := fun k m => f (subseq k) m
    have h_cont_f' : ∀ k m, Continuous (f' k m) := fun k m => h_cont (subseq k) m
    have h_bound_f' : ∀ k m x, 0 ≤ f' k m x ∧ f' k m x ≤ 1 :=
      fun k m x => h_bounded (subseq k) m x
    have h_error' : ∀ k m, ∫ x in K j, |h k x - f' k m x| ≤ C_j j * ε m := by
      intro k m
      have h_eq : ∫ x in K j, |h k x - f' k m x| = ∫ x in K j, |f' k m x - h k x| := by
        apply MeasureTheory.setIntegral_congr_fun (hK_meas j); intro x _; exact abs_sub_comm _ _
      rw [h_eq]
      exact h_l1_error j m k
    have h_conv' : ∀ m, Tendsto (fun k => ∫ x in K j, |f' k m x - gjm j m x|) atTop (nhds 0) :=
      fun m => hgjm_l1 j m
    exact l1_cauchy_of_mollified_per_m
      (hK_meas j) (hK_fin j)
      h f' (gjm j) (C_j j) (hCj_nonneg j) ε hε_pos hε_tendsto
      h_meas_h h_bound_h h_cont_f' h_bound_f'
      (fun m => hgjm_cont j m) (fun m x hx => hgjm_bound j m x hx)
      h_error' h_conv'

  -- 9. For each j, get L¹ limit that is {0,1}-valued a.e.
  have h_main2 : ∀ j, ∃ (g_j : E n → ℝ),
      Measurable g_j ∧
      IntegrableOn g_j (K j) ∧
      Tendsto (fun k => ∫ x in K j, |h k x - g_j x|) atTop (nhds 0) ∧
      (∀ᵐ x ∂volume.restrict (K j), g_j x = 0 ∨ g_j x = 1) := by
    intro j
    exact cauchy_complete_binary_limit (K j) (hK_compact j) (hK_meas j) (hK_fin j)
      h h_meas_h h_bound_h h_binary_h (h_cauchy_real j)
  choose g_j hg_meas hg_integrable hg_conv hg_binary using h_main2

  -- 10. Global compatibility across scales
  have hK_mono : ∀ j1 j2, j1 ≤ j2 → K j1 ⊆ K j2 := by
    intro j1 j2 hj12 x hx
    simp only [K, mem_closedBall, dist_zero_right] at hx ⊢
    have h : (j1 : ℝ) ≤ (j2 : ℝ) := by exact_mod_cast hj12
    linarith
  have h_compat_pair : ∀ j1 j2, j1 ≤ j2 → ∀ᵐ x ∂volume.restrict (K j1), g_j j1 x = g_j j2 x := by
    intro j1 j2 hj12
    exact limits_compatible_across_scales (K j1) (K j2)
      (hK_meas j1) (hK_meas j2) (hK_fin j1) (hK_fin j2)
      (hK_mono j1 j2 hj12) h h_meas_h h_bound_h
      (g_j j1) (g_j j2) (hg_integrable j1) (hg_integrable j2)
      (hg_conv j1) (hg_conv j2)

  -- 11. Define F
  let F : Set (E n) := {x | ∃ j, x ∈ K j ∧ g_j j x = 1}

  -- 12. Compatibility: χ_F = g_j a.e. on K_j
  have h_compat : ∀ j, ∀ᵐ x ∂volume.restrict (K j), Set.indicator F (1 : E n → ℝ) x = g_j j x := by
    intro j
    have h1 : ∀ j', j ≤ j' → ∀ᵐ x ∂volume.restrict (K j), g_j j x = g_j j' x :=
      fun j' hjj' => h_compat_pair j j' hjj'
    have h_in_F : ∀ᵐ x ∂volume.restrict (K j), g_j j x = 1 → x ∈ F := by
      filter_upwards [hg_binary j, ae_restrict_mem (hK_meas j)] with x hx_binary hx_K
      intro hgj1
      exact ⟨j, hx_K, hgj1⟩
    have h_not_F : ∀ᵐ x ∂volume.restrict (K j), x ∈ F → g_j j x = 1 := by
      have h_all : ∀ j', ∀ᵐ x ∂volume.restrict (K j), x ∈ K j' → g_j j x = g_j j' x := by
        intro j'
        by_cases h : j ≤ j'
        · filter_upwards [h_compat_pair j j' h] with x h_eq
          intro _; exact h_eq
        · have h_j'_le_j : j' ≤ j := by linarith
          have h_eq_on_Kj' : ∀ᵐ x ∂volume.restrict (K j'), g_j j' x = g_j j x := h_compat_pair j' j h_j'_le_j
          have h6 : ∀ᵐ x ∂volume, x ∈ K j' → g_j j' x = g_j j x :=
            (MeasureTheory.ae_restrict_iff' (hK_meas j')).mp h_eq_on_Kj'
          have h7 : ∀ᵐ x ∂volume.restrict (K j), x ∈ K j' → g_j j' x = g_j j x :=
            h6.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
          filter_upwards [h7] with x h_impl
          intro hxK; exact (h_impl hxK).symm
      have h_all' : ∀ᵐ x ∂volume.restrict (K j), ∀ j', x ∈ K j' → g_j j x = g_j j' x :=
        ae_all_iff.mpr h_all
      filter_upwards [h_all'] with x hx_all
      intro hxF
      rcases hxF with ⟨j', hxj', hgj'1⟩
      have h_eq : g_j j x = g_j j' x := hx_all j' hxj'
      rw [h_eq, hgj'1] <;> norm_num
    filter_upwards [h_in_F, h_not_F, hg_binary j] with x h1 h2 hx_binary
    by_cases h : g_j j x = 1
    · have h3 : x ∈ F := h1 h
      simp [Set.indicator_apply, h3, h]
    · have h4 : x ∉ F := by intro h5; exact h (h2 h5)
      have h5 : g_j j x = 0 := by
        rcases hx_binary with (h6 | h6)
        · exact h6
        · exfalso; exact h h6
      simp [Set.indicator_apply, h4, h5]

  -- 12b. F is measurable
  have hF_meas : MeasurableSet F := by
    have h1 : F = ⋃ j, (K j ∩ {x | g_j j x = 1}) := by
      ext x
      simp only [F, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      <;> rfl
    rw [h1]
    apply MeasurableSet.iUnion
    intro j
    exact (hK_meas j).inter ((hg_meas j) (MeasurableSet.singleton 1))
  -- 13. Conclude
  refine ⟨F, subseq, hsub_strict, hF_meas, fun Kset hK => ?_⟩
  rcases hK_exhaust Kset hK with ⟨j, hj⟩
  have h_main_conv : Tendsto (fun k => ∫ x in K j, |h k x - Set.indicator F (1 : E n → ℝ) x|) atTop (nhds 0) := by
    have h_eq : ∀ k, ∫ x in K j, |h k x - Set.indicator F (1 : E n → ℝ) x| = ∫ x in K j, |h k x - g_j j x| := by
      intro k
      have h_ae : ∀ᵐ x ∂volume.restrict (K j), |h k x - Set.indicator F (1 : E n → ℝ) x| = |h k x - g_j j x| := by
        filter_upwards [h_compat j] with x hx
        rw [hx]
      exact integral_congr_ae h_ae
    have h : Tendsto (fun k => ∫ x in K j, |h k x - g_j j x|) atTop (nhds 0) := hg_conv j
    simpa [funext h_eq] using h
  have h_vol_eq : ∀ k, volume (symmDiff (E_seq (subseq k)) F ∩ K j) =
      ENNReal.ofReal (∫ x in K j, |h k x - Set.indicator F (1 : E n → ℝ) x|) := by
    intro k
    let g_j' := (hg_integrable j).1.mk
    have hg_j'_meas : Measurable g_j' := (hg_integrable j).1.measurable_mk
    have hg_j'_eq : ∀ᵐ x ∂volume.restrict (K j), g_j j x = g_j' x := (hg_integrable j).1.ae_eq_mk
    let S' : Set (E n) := {x ∈ K j | h k x ≠ g_j' x}
    let A : Set (E n) := Set.inter (symmDiff (E_seq (subseq k)) F) (K j)
    have h_sub_meas : Measurable (fun x => h k x - g_j' x) := (h_meas_h k).sub hg_j'_meas
    have h_zero_meas : MeasurableSet ({(0 : ℝ)} : Set ℝ) := measurableSet_singleton 0
    have h_zero_compl : MeasurableSet ({(0 : ℝ)}ᶜ) := h_zero_meas.compl
    have h_preimage_eq : (fun x : E n => h k x - g_j' x) ⁻¹' ({(0 : ℝ)}ᶜ) = {x | h k x ≠ g_j' x} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
      <;> exact sub_ne_zero
    have h_ne_set : MeasurableSet {x | h k x ≠ g_j' x} := by
      rw [←h_preimage_eq]; exact h_sub_meas h_zero_compl
    have hS'_meas : MeasurableSet S' := (hK_meas j).inter h_ne_set
    have hS'_sub : S' ⊆ K j := by simp [S']
    have hS'_fin : volume S' ≠ ⊤ := ne_top_of_le_ne_top (hK_fin j) (measure_mono hS'_sub)
    let A2 : Set (E n) := symmDiff (E_seq (subseq k)) F ∩ K j
    have h_symm_iff : ∀ (x : E n), x ∈ symmDiff (E_seq (subseq k)) F ↔
        Set.indicator (E_seq (subseq k)) (1 : E n → ℝ) x ≠ Set.indicator F (1 : E n → ℝ) x := by
      intro x
      by_cases hA : x ∈ E_seq (subseq k) <;> by_cases hB : x ∈ F <;> simp [symmDiff, Set.indicator_apply, hA, hB] <;> decide
    have h_ae2 : ∀ᵐ x ∂volume, (x ∈ A2) = (x ∈ S') := by
      have h1 : ∀ᵐ x ∂volume.restrict (K j), (x ∈ A2) ↔ (x ∈ S') := by
        filter_upwards [h_compat j, hg_j'_eq, ae_restrict_mem (hK_meas j)] with x hcompat hgeq hxK
        have h_ind : h k x = Set.indicator (E_seq (subseq k)) (1 : E n → ℝ) x := by rfl
        have h_iff : x ∈ symmDiff (E_seq (subseq k)) F ↔ h k x ≠ g_j' x := by
          rw [h_symm_iff x, h_ind, hcompat, hgeq]
        simp only [A2, S', Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [and_comm, and_congr_right_iff]; intro _; exact h_iff
      have h2 : ∀ᵐ x ∂volume, x ∈ K j → ((x ∈ A2) ↔ (x ∈ S')) :=
        (MeasureTheory.ae_restrict_iff' (hK_meas j)).mp h1
      filter_upwards [h2] with x h2
      classical
      by_cases hx : x ∈ K j
      · exact propext (h2 hx)
      · have h3 : x ∉ A2 := by simp [A2, hx]
        have h4 : x ∉ S' := by intro h5; exact hx h5.1
        exact propext (by simp [h3, h4])
    have h_vol_eq1 : volume A2 = volume S' := measure_congr h_ae2
    rw [h_vol_eq1]
    have h_binary_gj' : ∀ᵐ x ∂volume.restrict (K j), g_j' x = 0 ∨ g_j' x = 1 := by
      filter_upwards [hg_binary j, hg_j'_eq] with x hbin heq
      rw [←heq]; exact hbin
    have h3_ae : ∀ᵐ x ∂volume.restrict (K j), |h k x - g_j' x| = Set.indicator S' (1 : E n → ℝ) x := by
      filter_upwards [h_binary_gj', ae_restrict_mem (hK_meas j)] with x hbin hxK
      have h_hbin : h k x = 0 ∨ h k x = 1 := h_binary_h k x
      by_cases h_ne : h k x ≠ g_j' x
      · have h4 : x ∈ S' := ⟨hxK, h_ne⟩
        have h5 : |h k x - g_j' x| = 1 := by
          rcases h_hbin with (h_h | h_h) <;> rcases hbin with (h_g | h_g) <;> simp [h_h, h_g] at h_ne ⊢ <;> linarith
        have h6 : Set.indicator S' (1 : E n → ℝ) x = 1 := by
          simp [Set.indicator_apply, h4] <;> norm_num
        rw [h5, h6]
      · have h4 : x ∉ S' := by intro h5; exact h_ne h5.2
        have h5 : |h k x - g_j' x| = 0 := by
          have h6 : h k x = g_j' x := by tauto
          rw [h6] <;> simp
        have h7 : Set.indicator S' (1 : E n → ℝ) x = 0 := by
          simp [Set.indicator_apply, h4] <;> norm_num
        rw [h5, h7]
    have h4 : ∫ x in K j, |h k x - g_j' x| = (volume S').toReal := by
      have h_ihk : IntegrableOn (h k) (K j) :=
        Measure.integrableOn_of_bounded (hK_fin j) (h_meas_h k).aestronglyMeasurable
          (by filter_upwards with x; simp [Real.norm_eq_abs]; exact h_bound_h k x)
      have h_igj' : IntegrableOn g_j' (K j) := by
        have h_int : IntegrableOn (g_j j) (K j) := hg_integrable j
        exact h_int.congr_fun_ae hg_j'_eq
      have h_i1 : IntegrableOn (fun x => |h k x - g_j' x|) (K j) :=
        (h_ihk.sub h_igj').norm
      have h_bound2 : ∀ᵐ x ∂volume.restrict (K j), ‖Set.indicator S' (1 : E n → ℝ) x‖ ≤ 1 := by
        filter_upwards with x
        by_cases hx : x ∈ S'
        · have h9 : Set.indicator S' (1 : E n → ℝ) x = 1 := by
            simp [Set.indicator_apply, hx] <;> norm_num
          rw [h9] <;> norm_num
        · have h9 : Set.indicator S' (1 : E n → ℝ) x = 0 := by
            simp [Set.indicator_apply, hx] <;> norm_num
          rw [h9] <;> norm_num
      have h_i2 : IntegrableOn (Set.indicator S' (1 : E n → ℝ)) (K j) :=
        Measure.integrableOn_of_bounded (hK_fin j)
          (measurable_const.indicator hS'_meas).aestronglyMeasurable
          h_bound2
      have h_int : ∫ x in K j, |h k x - g_j' x| = ∫ x in K j, Set.indicator S' (1 : E n → ℝ) x :=
        MeasureTheory.integral_congr_ae h3_ae
      rw [h_int]
      have h5 : ∫ x in K j, Set.indicator S' (1 : E n → ℝ) x = ∫ x in (K j ∩ S'), (1 : ℝ) := by
        rw [setIntegral_indicator hS'_meas] <;> rfl
      rw [h5]
      have h6 : K j ∩ S' = S' := by ext x; simp [S'] <;> tauto
      rw [h6, setIntegral_const]
      have h7 : volume.real S' • (1 : ℝ) = (volume S').toReal := by
        simp [Measure.real, smul_eq_mul] <;> ring
      exact h7
    have h5 : ∫ x in K j, |h k x - Set.indicator F (1 : E n → ℝ) x| = ∫ x in K j, |h k x - g_j' x| := by
      have h_eq : ∀ᵐ x ∂volume.restrict (K j), |h k x - Set.indicator F (1 : E n → ℝ) x| = |h k x - g_j' x| := by
        filter_upwards [h_compat j, hg_j'_eq] with x hcompat hgeq
        rw [hcompat, hgeq]
      exact integral_congr_ae h_eq
    rw [h5, h4]
    rw [ENNReal.ofReal_toReal hS'_fin]
  have h_final : Tendsto (fun k => volume (symmDiff (E_seq (subseq k)) F ∩ K j)) atTop (nhds 0) := by
    rw [funext h_vol_eq]
    have h_cont : Continuous ENNReal.ofReal := continuous_ofReal
    have h_ofReal_tendsto : Tendsto ENNReal.ofReal (nhds (0 : ℝ)) (nhds (ENNReal.ofReal (0 : ℝ))) := h_cont.tendsto 0
    have h : Tendsto (fun k => ENNReal.ofReal (∫ x in K j, |h k x - Set.indicator F (1 : E n → ℝ) x|)) atTop (nhds (ENNReal.ofReal 0)) :=
      h_ofReal_tendsto.comp h_main_conv
    simpa using h
  have h_le : ∀ k, volume (symmDiff (E_seq (subseq k)) F ∩ Kset) ≤ volume (symmDiff (E_seq (subseq k)) F ∩ K j) :=
    fun k => measure_mono (inter_subset_inter_right _ hj)
  have h_zero : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_zero h_final (fun _ => bot_le) h_le

end Geometry
