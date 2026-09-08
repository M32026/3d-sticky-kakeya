/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.ChainScale
public import Kakeya.StickyKakeya.AnchorDensity
public import Kakeya.Density
public import Kakeya.FibreCommon
public import Kakeya.Frostman
public import Kakeya.KatzTao
public import Kakeya.Multiplicity
public import Kakeya.Uniform.ParentBodyDensity
public import Kakeya.RandomTranslation.Erosion
public import Kakeya.RandomTranslation.SampleDistinct
public import Kakeya.RandomTranslation.TranslationRefinement
public import Kakeya.RandomTranslation.TranslationRefinementJoint
public import Kakeya.ShadedUniform
public import Kakeya.Shading
public import Kakeya.StickyKakeya.Lemma75.Calibration
public import Kakeya.StickyKakeya.Lemma75.Counting
public import Kakeya.StickyKakeya.Lemma75.OuterBody
public import Kakeya.StickyKakeya.Lemma75.PerScaleDensity
public import Kakeya.Tube.Basic
public import Kakeya.Uniform

/-!
# GWZ Lemma 7.5 (the sub-sticky Frostman estimate)

`Kakeya.StickyKakeya.subStickyFrostmanLemma`: for `δ` small, a uniform family of `δ`-tubes admits a
finite set of translation vectors and a refinement of the translated family that is Frostman at
every scale with error `δ^{-(n+3)ε}`.  This is the main content of the proof of GWZ Theorem 7.3(B),
and its only consumer is the step-1 bridge of that proof.

The proof is assembled from the files re-exported here: the translation-count arithmetic
(`Lemma75.Calibration`), the per-scale density bound (`Lemma75.PerScaleDensity`), the finite-set
counting bounds (`Lemma75.Counting`) and the Minkowski-sum chain (`Lemma75.OuterBody`).
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open scoped Topology
open Tube

namespace Kakeya


namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

set_option maxHeartbeats 4000000 in
-- Heartbeat bump for `subStickyFrostmanLemma`: the leaf-shape construction
-- (`s'_at`, `S_per`, `anc`, `chain_geo_gen`) and the per-scale Lemma 7.4
-- bundle elaboration push the default 200k heartbeat budget past its limit.
-- Raised again for the prefix-offset chain of eq. (52): the nodes-indexed
-- chain adds the fattened scale `σ`, the parent map `proj` and their five
-- clause-7 obligations on top of the existing construction.
open scoped Classical in
/-- GWZ Lemma 7.5 (sub-sticky Frostman estimate).  Let `T = (T i)_{i ∈ s}` be `δ`-tubes in
`B₁ ⊂ ℝⁿ`, uniform at each of the scales `δ = ρ_M < ⋯ < ρ_0 = 1`, and suppose that for each
`k = 1, …, M` one has `ρ_k / ρ_{k-1} ≥ δ^ε` and `Δ_max(T_{ρ_k}) ≤ (ρ_{k-1}/ρ_k)^ε`.  Then for `δ`
small enough there are a finite set `R` of translation vectors and a refined `s' ⊆ s ×ˢ R` whose
translated family is Frostman at every scale with error `δ^{-(n+3)ε}`. -/
theorem subStickyFrostmanLemma (ε : ℝ) (hε : 0 < ε) (M : ℕ) (hM : 1 ≤ M)
    (Cn : ℝ) (hCn_pos : 0 < Cn) (hCn_ge_one : 1 ≤ Cn)
    (C_prod : ℝ) (hC_prod_pos : 0 < C_prod)
    (C_box : ℝ) (hC_box_pos : 0 < C_box) (μ_cov : ℕ) (hμ_cov_pos : 0 < μ_cov) :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      ∀ {ι : Type} (s : Finset ι), s.Nonempty →
      ∀ (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (ρ : Fin (M + 1) → NNReal),
        ρ 0 = 1 → ρ (Fin.last M) = δ → StrictAnti ρ →
      ∀ (C_uniform : NNReal)
        (h_uni : (k : Fin (M + 1)) →
          Tube.IsUniformAtScale s T (ρ k) C_uniform),
        (∀ k : Fin (M + 1), (1 : NNReal) ≤ (h_uni k).branchingN) →
        (∀ k : Fin M,
            ((h_uni k.castSucc).parent.card : ℝ)
              ≤ C_box * ((4 : ℝ) / (ρ k.castSucc : ℝ)) ^ (2 * Module.finrank ℝ E)) →
        (∀ {δ' : NNReal} (W : Tube δ' E) (k : Fin (M + 1)),
            (∃ i ∈ s, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) →
            (((h_uni k).parent.filter (fun j =>
                W.toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody)).card)
              ≤ μ_cov) →
        (∀ k : Fin M, (δ : ℝ) ^ ε ≤ (ρ k.succ : ℝ) / (ρ k.castSucc : ℝ)) →
        (∀ k : Fin M, 8 * (ρ k.succ : ℝ) ≤ (ρ k.castSucc : ℝ)) →
        ∀ (P : Fin (M + 1) → Finset ι),
        (∀ k : Fin (M + 1), P k ⊆ (h_uni k).parent) →
        (∀ i ∈ s, ∃ j ∈ P 0,
            (T i).toConvexSpaceBody ≤ ((h_uni 0).parentTube j).toConvexSpaceBody) →
        ∀ (N₂ : Fin M → ℕ),
        (∀ k : Fin M, 0 < N₂ k) →
        (∀ k : Fin M,
          ∀ j ∈ P k.castSucc,
            (N₂ k : ℝ) ≤ Cn *
              (((P k.succ).filter (fun i : ι =>
                ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                  ((h_uni k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)) →
        (∀ k : Fin M,
          ∀ j ∈ P k.castSucc,
            ((((P k.succ).filter (fun i : ι =>
                ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                  ((h_uni k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ))
              ≤ Cn * (N₂ k : ℝ)) →
        (∀ k : Fin M, (N₂ k : ℝ)
          ≤ Cn * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
              ^ (((Module.finrank ℝ E : ℝ) - 1) + ε)) →
        ((s.card : ℝ) ≤ C_prod * ∏ k : Fin M, (N₂ k : ℝ)) →
        (∀ k : Fin M,
            Kakeya.maxDensity
                ((h_uni k.succ).parent.image
                  (fun j => (h_uni k.succ).parentTube j))
                (fun u : Tube (ρ k.succ) E => u.toConvexSpaceBody)
              ≤ ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)) →
        ∃ (C : ℝ) (C_s' : ℝ) (R : Finset E)
          (Rs : Fin M → Finset E)
          (R_partial : Fin (M + 1) → Finset E)
          (s' : Finset (ι × E)),
          R.Nonempty ∧
          s' ⊆ s ×ˢ R ∧
          (R.card : ℝ) ≤ C * (δ : ℝ) ^ (-ε) *
              max 1
                ((s.card : ℝ) *
                    (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1))⁻¹ ∧
          C ≤ qCardConst (Module.finrank ℝ E) M Cn C_prod ∧
          R_partial 0 = {0} ∧
          (∀ k : Fin M, R_partial k.succ =
              (R_partial k.castSucc ×ˢ Rs k).image (fun p : E × E => p.1 + p.2)) ∧
          R_partial (Fin.last M) = R ∧
          s'.Nonempty ∧
          IsFrostmanAtEveryScale (E := E) s'
            (fun p : ι × E => (T p.1).translate p.2)
            (ENNReal.ofReal
              ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε))) ∧
          0 < C_s' ∧
          (δ : ℝ) ^ ε * (s.card : ℝ) * (R.card : ℝ)
            ≤ C_s' * (s'.card : ℝ) ∧
          (∀ p ∈ s', ((T p.1).translate p.2).carrier
            ⊆ Metric.closedBall (0 : E) ((M : ℝ) + 1)) ∧
          (∃ K_cnt : ℝ, 1 ≤ K_cnt ∧
            ∀ ρ_anchor : NNReal, δ ≤ ρ_anchor → ρ_anchor ≤ 1 → ∀ p₀ ∈ s',
              ENNReal.ofReal
                  (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
                      (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2 *
                    ((δ : ℝ) ^ ε / K_cnt ^ M) /
                    ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) *
                      (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))))
                ≤ Kakeya.densityIn
                    (s'.filter (fun p : ι × E =>
                      ((T p.1).translate p.2).toConvexSpaceBody ≤
                        (Tube.rescale ((T p₀.1).translate p₀.2) ρ_anchor).toConvexSpaceBody))
                    (fun p : ι × E => ((T p.1).translate p.2).toConvexSpaceBody)
                    (Tube.rescale ((T p₀.1).translate p₀.2) ρ_anchor).toConvexSpaceBody) ∧
          Kakeya.maxDensity s' (fun p : ι × E => ((T p.1).translate p.2).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε))) := by
  obtain ⟨K_53, C_R, c_R, hK_53_ge_one, hc_R_pos, hC_R_pos, hC_R_le_two,
      h_perScale_uniform⟩ :=
    subStickyFrostmanLemma.perScaleDeltaMax (E := E) ε hε M hM C_box hC_box_pos Cn hCn_ge_one
  have hK_53_pos : 0 < K_53 := lt_of_lt_of_le zero_lt_one hK_53_ge_one
  have hmin_pos : 0 < min c_R 1 := by
    exact lt_min_iff.mpr ⟨hc_R_pos, by norm_num⟩
  have hmin_le_one : min c_R 1 ≤ 1 := min_le_right _ _
  have hmin_le_cR : min c_R 1 ≤ c_R := min_le_left _ _
  obtain ⟨Cn_eff, hCn_eff_ge_one, hCn_le_eff, hCn_div_cR_le_eff⟩ :
      ∃ c : ℝ, 1 ≤ c ∧ Cn ≤ c ∧ Cn / c_R ≤ c := by
    refine ⟨Cn / min c_R 1, ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hmin_pos]; nlinarith [hmin_le_one, hCn_ge_one]
    · rw [le_div_iff₀ hmin_pos]; nlinarith [hmin_le_one, hCn_pos]
    · field_simp [hc_R_pos.ne', hmin_pos.ne']; nlinarith [hmin_le_cR, hCn_pos]
  have hCn_eff_pos : (0 : ℝ) < Cn_eff := lt_of_lt_of_le zero_lt_one hCn_eff_ge_one
  set K_cnt : ℝ := K_53 * max Cn_eff 1 * (μ_cov : ℝ) with hK_cnt_def
  have hK_cnt_ge_one : (1 : ℝ) ≤ K_cnt := by
    rw [hK_cnt_def]
    have h1 : (1 : ℝ) ≤ K_53 := hK_53_ge_one
    have h2 : (1 : ℝ) ≤ max Cn_eff 1 := le_max_right _ _
    have h3 : (1 : ℝ) ≤ (μ_cov : ℝ) := by exact_mod_cast hμ_cov_pos
    have h12 : (1 : ℝ) ≤ K_53 * max Cn_eff 1 := by nlinarith [h1, h2]
    nlinarith [h12, h3]
  have hK_cnt_pos : 0 < K_cnt := lt_of_lt_of_le zero_lt_one hK_cnt_ge_one
  obtain ⟨K_53_KT, hK_53_KT_pos, hK_53_KT_ge_one, hK_53_KT_absorb⟩ :
      ∃ K : ℝ, 0 < K ∧ 1 ≤ K ∧
        5 * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
            * 3 ^ (Module.finrank ℝ E - 1) * K_53
          ≤ K := by
    let lhs : ℝ := 5 * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
      / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
      * 3 ^ (Module.finrank ℝ E - 1) * K_53
    have hpos : 0 < lhs := by
      dsimp [lhs]
      have hCpos : 0 < (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) := by
        unfold Tube.volume_le.C; positivity
      have hcpos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
        exact_mod_cast Tube.le_volume.c_pos _
      have h3pos : 0 < 3 ^ (Module.finrank ℝ E - 1) := by positivity
      have hK53pos : 0 < K_53 := hK_53_pos
      positivity
    have hone : (1 : ℝ) ≤ lhs := by
      have h5 : (1 : ℝ) ≤ 5 := by norm_num
      have hCdiv : (1 : ℝ) ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
        have hcpos : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
          exact_mod_cast Tube.le_volume.c_pos _
        exact (one_le_div hcpos).mpr le_volume_c_le_volume_le_C
      have h3pow : (1 : ℝ) ≤ 3 ^ (Module.finrank ℝ E - 1) := by
        calc
          (1 : ℝ) = (1 : ℝ) ^ (Module.finrank ℝ E - 1) := by simp
          _ ≤ 3 ^ (Module.finrank ℝ E - 1) :=
            pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 3) _
      calc
        (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
        _ ≤ 5 * ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
            * 3 ^ (Module.finrank ℝ E - 1) * K_53 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul h5 hCdiv (by norm_num) ?_) h3pow ?_ ?_)
            hK_53_ge_one ?_ ?_
          · positivity
          · positivity
          · positivity
          · positivity
          · positivity
        _ = lhs := by ring
    exact ⟨lhs, hpos, hone, le_refl lhs⟩
  set R : ℝ := (M : ℝ) + 4 with hR_def
  have hR_ge_one : (1 : ℝ) ≤ R := by
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
    rw [hR_def]; linarith
  obtain ⟨C_7_4, hC_7_4_pos, h_md_template⟩ :=
    Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales
      (E := E) R hR_ge_one C_box hC_box_pos
  have h_factor_pos : 0 < C_7_4 * K_53_KT := mul_pos hC_7_4_pos hK_53_KT_pos
  have h_exp_pos : 0 < ((Module.finrank ℝ E : ℝ) + 1) * ε := by
    have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have h1 : 0 < (Module.finrank ℝ E : ℝ) + 1 := by linarith
    exact mul_pos h1 hε
  have h_D_le_eventually : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      (C_7_4 * K_53_KT) ^ M
        ≤ (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 1) * ε)) := by
    set D_const : ℝ := (C_7_4 * K_53_KT) ^ M with hD_const_def
    have hAtTop : ∀ᶠ y : ℝ in Filter.atTop,
        D_const ≤ y ^ (((Module.finrank ℝ E : ℝ) + 1) * ε) := by
      have hyc : Filter.Tendsto
          (fun y : ℝ => y ^ (((Module.finrank ℝ E : ℝ) + 1) * ε))
          Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop h_exp_pos
      exact hyc.eventually_ge_atTop D_const
    have hInv : Filter.Tendsto (fun x : ℝ => x⁻¹)
        (𝓝[>] (0 : ℝ)) Filter.atTop := tendsto_inv_nhdsGT_zero
    have hRealEv : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        D_const ≤ x⁻¹ ^ (((Module.finrank ℝ E : ℝ) + 1) * ε) :=
      hInv.eventually hAtTop
    have hReal : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        D_const ≤ x ^ (-(((Module.finrank ℝ E : ℝ) + 1) * ε)) := by
      filter_upwards [hRealEv] with x hx
      have hxinv : x⁻¹ ^ (((Module.finrank ℝ E : ℝ) + 1) * ε)
          = x ^ (-(((Module.finrank ℝ E : ℝ) + 1) * ε)) :=
        (Real.rpow_neg_eq_inv_rpow x _).symm
      rw [← hxinv]; exact hx
    have hmap : (𝓝[>] (0 : NNReal)).map ((↑) : NNReal → ℝ)
        = 𝓝[>] (0 : ℝ) := by
      have h := NNReal.map_coe_nhdsGT (0 : NNReal)
      rw [NNReal.coe_zero] at h
      exact h
    rw [← hmap] at hReal
    exact hReal
  set K_inv_n_outer : ℝ :=
    (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
      (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hK_inv_n_outer_def
  have hK_inv_n_outer_pos : 0 < K_inv_n_outer := by
    rw [hK_inv_n_outer_def]
    refine div_pos ?_ ?_
    · exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
    · have h : (0 : NNReal) < Tube.volume_le.C (Module.finrank ℝ E) := by
        unfold Tube.volume_le.C; positivity
      exact_mod_cast h
  have hK_inv_n_outer_sq_pos : 0 < K_inv_n_outer ^ 2 := by positivity
  have h_D_inv_le_eventually : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      (C_7_4 * K_53_KT) ^ M * K_cnt ^ M *
            (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) /
            K_inv_n_outer ^ 2
        ≤ (δ : ℝ) ^ (-ε) := by
    set D_inv : ℝ := (C_7_4 * K_53_KT) ^ M * K_cnt ^ M *
        (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) / K_inv_n_outer ^ 2 with hD_inv_def
    have h_eps_pos : 0 < ε := hε
    have hAtTop : ∀ᶠ y : ℝ in Filter.atTop,
        D_inv ≤ y ^ ε := by
      have hyc : Filter.Tendsto (fun y : ℝ => y ^ ε)
          Filter.atTop Filter.atTop := tendsto_rpow_atTop h_eps_pos
      exact hyc.eventually_ge_atTop D_inv
    have hInv : Filter.Tendsto (fun x : ℝ => x⁻¹)
        (𝓝[>] (0 : ℝ)) Filter.atTop := tendsto_inv_nhdsGT_zero
    have hRealEv : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        D_inv ≤ x⁻¹ ^ ε :=
      hInv.eventually hAtTop
    have hReal : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
        D_inv ≤ x ^ (-ε) := by
      filter_upwards [hRealEv] with x hx
      have hxinv : x⁻¹ ^ ε = x ^ (-ε) :=
        (Real.rpow_neg_eq_inv_rpow x _).symm
      rw [← hxinv]; exact hx
    have hmap : (𝓝[>] (0 : NNReal)).map ((↑) : NNReal → ℝ)
        = 𝓝[>] (0 : ℝ) := by
      have h := NNReal.map_coe_nhdsGT (0 : NNReal)
      rw [NNReal.coe_zero] at h
      exact h
    rw [← hmap] at hReal
    exact hReal
  filter_upwards [h_perScale_uniform,
      self_mem_nhdsWithin (s := Set.Ioi (0 : NNReal)),
      h_D_le_eventually, h_D_inv_le_eventually]
    with δ h_perScale_uni hδ_mem h_D_le_δ h_D_inv_le_δ
  intro ι s hs_nonempty
  have hδ_pos : 0 < δ := hδ_mem
  have h_perScale := h_perScale_uni (ι := ι) s
  intro T hT_in_unit ρ hρ_0 hρ_M hρ_anti C_uniform h_uni hNonDegen h_count h_cov
    hρ_ratio hρ_quarter P hP_sub hP_zero N₂ hN₂_pos hCnBracket hCnBracketUB hN₂_xm hN₂_prod
    hΔ_input
  have hParentBall :
      ∀ k : Fin (M + 1), ∀ j ∈ (h_uni k).parent,
        ((h_uni k).parentTube j).carrier ⊆ Metric.closedBall (0 : E) 4 :=
    subStickyFrostmanLemma.outerBody.bridge1_parentBall
      (E := E) s T hT_in_unit M ρ hρ_anti hρ_0 C_uniform h_uni hNonDegen
  have hΔ_input_bracket :
      ∀ k : Fin M, ∀ j ∈ (h_uni k.castSucc).parent,
        Kakeya.maxDensity
            (((h_uni k.succ).parent.image
                (fun i => (h_uni k.succ).parentTube i)).filter
              (fun w : Tube (ρ k.succ) E =>
                w.toConvexSpaceBody ≤
                  ((h_uni k.castSucc).parentTube j).toConvexSpaceBody))
            (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody)
          ≤ ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) :=
    subStickyFrostmanLemma.outerBody.bridge6_bracketDeltaMax
      (E := E) ε M s T ρ C_uniform h_uni hΔ_input
  obtain ⟨R_per, S_per,
      hRk_norm, hRk_card, hSkj_sub, hSkj_count_LB, hSkj_density, _hRk_singleton_if,
      hRk_direct⟩ :=
    h_perScale T hT_in_unit ρ hρ_0.le hρ_M hρ_anti hρ_ratio C_uniform h_uni
      hParentBall h_count P hP_sub N₂ hN₂_pos hCnBracket hCnBracketUB hN₂_xm
      (fun k j hj => hΔ_input_bracket k j (hP_sub k.castSucc hj))
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have h_pow_neg2eps_pos : 0 < (δ : ℝ) ^ (-(2 * ε)) :=
    Real.rpow_pos_of_pos hδ_pos_real _
  have h_target_split : (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε))
      = (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 1) * ε))
          * (δ : ℝ) ^ (-(2 * ε)) := by
    rw [← Real.rpow_add hδ_pos_real]
    congr 1; ring
  have hδ_small :
      (C_7_4 * K_53_KT) ^ M * (δ : ℝ) ^ (-(2 * ε))
          ≤ (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε)) := by
    rw [h_target_split]
    exact mul_le_mul_of_nonneg_right h_D_le_δ h_pow_neg2eps_pos.le
  have h_8_pow_pos : (0 : ℝ) < (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) := by positivity
  have hK_53_M_pos : (0 : ℝ) < K_cnt ^ M := pow_pos hK_cnt_pos M
  have hδ_small_sharp :
      (C_7_4 * K_53_KT) ^ M * (δ : ℝ) ^ (-(2 * ε))
          ≤ K_inv_n_outer ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
              (δ : ℝ) ^ (-(3 * ε)) := by
    have hKden_pos : (0 : ℝ) <
        K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) :=
      mul_pos hK_53_M_pos h_8_pow_pos
    have h_D_le' : (C_7_4 * K_53_KT) ^ M ≤
        K_inv_n_outer ^ 2 /
            (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
          (δ : ℝ) ^ (-ε) := by
      have h0 := (div_le_iff₀ hK_inv_n_outer_sq_pos).mp h_D_inv_le_δ
      have h1 : (C_7_4 * K_53_KT) ^ M ≤
          (δ : ℝ) ^ (-ε) * K_inv_n_outer ^ 2 /
            (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) := by
        rw [le_div_iff₀ hKden_pos]
        nlinarith [h0]
      have h2 : (δ : ℝ) ^ (-ε) * K_inv_n_outer ^ 2 /
            (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) =
          K_inv_n_outer ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
            (δ : ℝ) ^ (-ε) := by ring
      rw [h2] at h1
      exact h1
    have h_mul := mul_le_mul_of_nonneg_right h_D_le' h_pow_neg2eps_pos.le
    have h_pow_combine : (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-(2 * ε))
        = (δ : ℝ) ^ (-(3 * ε)) := by
      rw [← Real.rpow_add hδ_pos_real]
      congr 1; ring
    calc (C_7_4 * K_53_KT) ^ M * (δ : ℝ) ^ (-(2 * ε))
        ≤ K_inv_n_outer ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
            (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-(2 * ε)) := h_mul
      _ = K_inv_n_outer ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
            ((δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-(2 * ε))) := by ring
      _ = K_inv_n_outer ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
            (δ : ℝ) ^ (-(3 * ε)) := by rw [h_pow_combine]
  have hρ_pos_all : ∀ k : Fin (M + 1), (0 : ℝ) < (ρ k : ℝ) := by
    intro k
    have h_le_last : ρ (Fin.last M) ≤ ρ k := hρ_anti.antitone (Fin.le_last k)
    have : (δ : ℝ) ≤ (ρ k : ℝ) := by
      have := h_le_last; rw [hρ_M] at this; exact_mod_cast this
    exact lt_of_lt_of_le hδ_pos_real this
  have hρ_anti_le : ∀ k : Fin M, (ρ k.succ : ℝ) ≤ (ρ k.castSucc : ℝ) := by
    intro k
    have h_le : ρ k.succ ≤ ρ k.castSucc := (hρ_anti Fin.castSucc_lt_succ).le
    exact_mod_cast h_le
  have hR_per_nonempty : ∀ k : Fin M, (R_per k).Nonempty := by
    intro k
    rcases (R_per k).eq_empty_or_nonempty with hempty | hne
    · exfalso
      have hLB := (hRk_card k).1
      rw [hempty, Finset.card_empty, Nat.cast_zero] at hLB
      have hmax : (1 : ℝ) ≤ max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
          ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)) := le_max_left _ _
      have hpos : 0 < c_R * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
          ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)) :=
        mul_pos hc_R_pos (lt_of_lt_of_le zero_lt_one hmax)
      linarith
    · exact hne
  obtain ⟨R_partial, hR_partial_zero, hR_partial_succ, hR_total_nonempty⟩ :=
    subStickyFrostmanLemma.outerBody.buildRPartial
      (E := E) M R_per hR_per_nonempty
  have hδ_le_one_real : (δ : ℝ) ≤ 1 := by
    have h_lt : ρ (Fin.last M) < ρ 0 := hρ_anti (by
      refine Fin.lt_def.mpr ?_
      simpa using Nat.pos_of_ne_zero (by omega))
    rw [hρ_M, hρ_0] at h_lt
    exact_mod_cast h_lt.le
  obtain ⟨C_card, hC_card_pos, hC_card_le2, hR_total_card⟩ :=
    subStickyFrostmanLemma.outerBody.cardUB
      (E := E) hε M s hs_nonempty hδ_pos_real hδ_le_one_real ρ hρ_pos_all
      (by rw [hρ_0]; norm_num) hρ_M hρ_anti_le N₂ hN₂_pos hCn_ge_one hN₂_xm
      hC_prod_pos hN₂_prod R_per
      (fun k => le_trans (hRk_card k).2 (by
        have hmax : (1 : ℝ) ≤ max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
            ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)) := le_max_left _ _
        nlinarith))
      R_partial hR_partial_zero hR_partial_succ
  set T' : ι × E → Tube δ E := fun p => (T p.1).translate p.2 with hT'_def
  set Δ : Fin M → ENNReal := fun m =>
    ENNReal.ofReal (K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
      ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε) with hΔ_def
  have hΔ_top : ∀ m : Fin M, Δ m ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  obtain ⟨s', hs'_nonempty, hs'_sub, _hs'_proj, hs'_T_in_ball,
          h_anchor_density, h_paper_kt⟩ :
      ∃ s' : Finset (ι × E),
        s'.Nonempty ∧
        s' ⊆ s ×ˢ R_partial (Fin.last M) ∧
        (∀ p ∈ s', p.1 ∈ s) ∧
        (∀ p ∈ s', (T' p).carrier ⊆ Metric.closedBall (0 : E) ((M : ℝ) + 1)) ∧
        (∀ ρ_anchor : NNReal, δ ≤ ρ_anchor → ρ_anchor ≤ 1 →
          ∀ p₀ ∈ s',
            ENNReal.ofReal
                (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
                    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2 *
                  ((δ : ℝ) ^ ε / K_cnt ^ M) /
                  ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) *
                    (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))))
              ≤ Kakeya.densityIn
                  (s'.filter (fun p : ι × E =>
                    (T' p).toConvexSpaceBody ≤
                      (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody))
                  (fun p : ι × E => (T' p).toConvexSpaceBody)
                  (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody) ∧
        (∃ (σ : Fin (M + 1) → NNReal) (Q : Fin (M + 1) → Finset (ι × E))
            (tb : ∀ k : Fin (M + 1), (ι × E) → Tube (σ k) E)
            (proj : Fin M → (ι × E) → (ι × E)),
          1 ≤ σ 0 ∧ σ 0 ≤ 4 ∧ σ (Fin.last M) = δ ∧ Antitone σ ∧
          (∀ m : Fin M, 4 * (σ m.succ : ℝ) ≤ (σ m.castSucc : ℝ)) ∧
          (∀ m : Fin M, ∀ w ∈ Q m.succ, proj m w ∈ Q m.castSucc) ∧
          (∀ m : Fin M, ∀ w ∈ Q m.succ,
              (tb m.succ w).toConvexSpaceBody
                ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody) ∧
          (((Q (0 : Fin (M + 1))).card : ℝ)
              ≤ C_box * (R + 3) ^ (2 * Module.finrank ℝ E)) ∧
          (∀ k : Fin (M + 1), ∀ t ∈ Q k,
              (tb k t).carrier ⊆ Metric.closedBall (0 : E) (R + 3)) ∧
          (∀ m : Fin M, (Q m.castSucc).Nonempty) ∧
          (∃ cover : (ι × E) → (ι × E),
            (∀ p ∈ s', cover p ∈ Q (Fin.last M)) ∧
            (∀ p ∈ s', (T' p).toConvexSpaceBody
                ≤ (tb (Fin.last M) (cover p)).toConvexSpaceBody) ∧
            Set.InjOn cover (↑s' : Set (ι × E)) ∧
            (∀ m : Fin M, ∀ p ∈ Q m.castSucc,
                IsKatzTao
                  ((Q m.succ).filter (fun w : ι × E => proj m w = p))
                  (fun w : ι × E => (tb m.succ w).toConvexSpaceBody)
                  (Δ m)))) := by
    classical
    let s'_at : Fin (M + 1) → Finset (ι × E) :=
      Fin.induction
        ((P 0).image (fun j : ι => (j, (0 : E))))
        (fun k prev =>
          prev.biUnion (fun p : ι × E =>
            (S_per k p.1).image
              (fun pair : ι × E => (pair.1, p.2 + pair.2))))
    have hs'_at_zero :
        s'_at 0 = (P 0).image (fun j : ι => (j, (0 : E))) := by
      simp [s'_at]
    have hs'_at_succ : ∀ k : Fin M,
        s'_at k.succ =
          (s'_at k.castSucc).biUnion (fun p : ι × E =>
            (S_per k p.1).image
              (fun pair : ι × E => (pair.1, p.2 + pair.2))) := by
      intro k
      simp [s'_at]
    have h_invariant : ∀ k : Fin (M + 1), ∀ p ∈ s'_at k,
        p.1 ∈ P k ∧ p.2 ∈ R_partial k := by
      intro k
      induction k using Fin.induction with
      | zero =>
        intro p hp
        rw [hs'_at_zero] at hp
        obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hp
        subst hpj
        refine ⟨hj, ?_⟩
        rw [hR_partial_zero]; exact Finset.mem_singleton.mpr rfl
      | succ k ih =>
        intro p hp
        rw [hs'_at_succ k] at hp
        obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.mp hp
        obtain ⟨ih1, ih2⟩ := ih q hq
        obtain ⟨pair, hpair, heq⟩ := Finset.mem_image.mp hpq
        have hsub := hSkj_sub k q.1 ih1 hpair
        rw [Finset.mem_product] at hsub
        obtain ⟨hpair1, hpair2⟩ := hsub
        rw [Finset.mem_filter] at hpair1
        obtain ⟨hpair1_par, _⟩ := hpair1
        subst heq
        refine ⟨hpair1_par, ?_⟩
        rw [hR_partial_succ k]
        exact Finset.mem_image.mpr
          ⟨(q.2, pair.2), Finset.mem_product.mpr ⟨ih2, hpair2⟩, rfl⟩
    have parent_has_leaf : ∀ k : Fin (M + 1), ∀ j ∈ (h_uni k).parent,
        ∃ i ∈ s, (T i).toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody := by
      intro k j hj
      have h_le_filter := (h_uni k).le_mul_card_filter hj
      have h_one_le : (1 : NNReal) ≤ C_uniform *
          ({ i ∈ s |
            (T i).toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody}.card : NNReal) :=
        (hNonDegen k).trans h_le_filter
      have h_card_pos :
          0 < { i ∈ s |
            (T i).toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody}.card := by
        by_contra h_neg
        have h_neg' :
            ({ i ∈ s |
              (T i).toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody}.card) ≤ 0 :=
          Nat.le_zero.mpr (Nat.eq_zero_of_not_pos h_neg)
        have h_zero :
            ({ i ∈ s | (T i).toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody}.card
              : NNReal) = 0 := by
          simp [Nat.le_zero.mp h_neg']
        rw [h_zero, mul_zero] at h_one_le
        exact absurd h_one_le (by norm_num)
      obtain ⟨i, hi_mem⟩ :
          Finset.Nonempty
            ({ i ∈ s | (T i).toConvexSpaceBody ≤ ((h_uni k).parentTube j).toConvexSpaceBody}) :=
        Finset.card_pos.mp h_card_pos
      rw [Finset.mem_filter] at hi_mem
      exact ⟨i, hi_mem.1, hi_mem.2⟩
    let leafChoice : ι × E → ι := fun p =>
      if h : p.1 ∈ (h_uni (Fin.last M)).parent then
        (parent_has_leaf (Fin.last M) p.1 h).choose
      else p.1
    have hLeafChoice_spec : ∀ p ∈ s'_at (Fin.last M),
        leafChoice p ∈ s ∧
          (T (leafChoice p)).toConvexSpaceBody
            ≤ ((h_uni (Fin.last M)).parentTube p.1).toConvexSpaceBody := by
      intro p hp
      have hp_par : p.1 ∈ (h_uni (Fin.last M)).parent :=
        hP_sub _ (h_invariant _ p hp).1
      have hspec := (parent_has_leaf (Fin.last M) p.1 hp_par).choose_spec
      simp only [leafChoice, dif_pos hp_par]
      exact hspec
    set s' : Finset (ι × E) :=
      (s'_at (Fin.last M)).image (fun p : ι × E => (leafChoice p, p.2)) with hs'_def
    have hR_partial_norm : ∀ k : Fin (M + 1), ∀ v ∈ R_partial k,
        ‖v‖ ≤ (k.val : ℝ) := by
      intro k
      induction k using Fin.induction with
      | zero =>
        intro v hv
        rw [hR_partial_zero, Finset.mem_singleton] at hv
        subst hv
        simp
      | succ j ih =>
        intro v hv
        rw [hR_partial_succ j] at hv
        obtain ⟨⟨vp, vr⟩, hpr, hsum⟩ := Finset.mem_image.mp hv
        rw [Finset.mem_product] at hpr
        obtain ⟨hvp, hvr⟩ := hpr
        have h1 : ‖vp‖ ≤ (j.castSucc.val : ℝ) := ih vp hvp
        have h2 : ‖vr‖ ≤ (ρ j.castSucc : ℝ) := hRk_norm j vr hvr
        have hρ_le_1 : (ρ j.castSucc : ℝ) ≤ 1 := by
          have hle : ρ j.castSucc ≤ ρ 0 :=
            hρ_anti.antitone (Fin.zero_le _)
          rw [hρ_0] at hle
          exact_mod_cast hle
        rw [← hsum]
        have h3 : ‖vp + vr‖ ≤ ‖vp‖ + ‖vr‖ := norm_add_le _ _
        have hjvals : (j.succ.val : ℝ) = (j.castSucc.val : ℝ) + 1 := by
          simp [Fin.val_succ, Fin.val_castSucc]
        rw [hjvals]
        linarith
    have chain_recovery :
        ∃ anc : (k : Fin (M + 1)) → (q : ι × E) →
            q ∈ s'_at (Fin.last M) → ι × E,
          (∀ q hq, anc (Fin.last M) q hq = q) ∧
          (∀ k q hq, anc k q hq ∈ s'_at k) ∧
          (∀ (k : Fin M) (q : ι × E) (hq : q ∈ s'_at (Fin.last M)),
            ∃ pair ∈ S_per k (anc k.castSucc q hq).1,
              anc k.succ q hq = (pair.1, (anc k.castSucc q hq).2 + pair.2)) := by
      classical
      let mkChain : (q : ι × E) → q ∈ s'_at (Fin.last M) →
          (k : Fin (M + 1)) → (Σ' p : ι × E, p ∈ s'_at k) :=
        fun q hq =>
          Fin.reverseInduction
            (motive := fun k => Σ' p : ι × E, p ∈ s'_at k)
            ⟨q, hq⟩
            (fun j ih =>
              have hsucc : ih.1 ∈
                  (s'_at j.castSucc).biUnion (fun p : ι × E =>
                    (S_per j p.1).image
                      (fun pair : ι × E => (pair.1, p.2 + pair.2))) := by
                rw [← hs'_at_succ j]; exact ih.2
              let hex := Finset.mem_biUnion.mp hsucc
              ⟨hex.choose, hex.choose_spec.1⟩)
      refine ⟨fun k q hq => (mkChain q hq k).1, ?_, ?_, ?_⟩
      · intro q hq
        change (mkChain q hq (Fin.last M)).1 = q
        simp [mkChain]
      · intro k q hq
        exact (mkChain q hq k).2
      · intro j q hq
        have hStep : mkChain q hq j.castSucc =
            (fun ih : Σ' p : ι × E, p ∈ s'_at j.succ =>
              have hsucc : ih.1 ∈
                  (s'_at j.castSucc).biUnion (fun p : ι × E =>
                    (S_per j p.1).image
                      (fun pair : ι × E => (pair.1, p.2 + pair.2))) := by
                rw [← hs'_at_succ j]; exact ih.2
              let hex := Finset.mem_biUnion.mp hsucc
              (⟨hex.choose, hex.choose_spec.1⟩ : Σ' p : ι × E, p ∈ s'_at j.castSucc))
              (mkChain q hq j.succ) := by
          simp [mkChain]
        set ih := mkChain q hq j.succ with hih_def
        have hsucc : ih.1 ∈
            (s'_at j.castSucc).biUnion (fun p : ι × E =>
              (S_per j p.1).image
                (fun pair : ι × E => (pair.1, p.2 + pair.2))) := by
          rw [← hs'_at_succ j]; exact ih.2
        let hex := Finset.mem_biUnion.mp hsucc
        have h_anc_cs : (mkChain q hq j.castSucc).1 = hex.choose := by
          rw [hStep]
        have h_image_mem : ih.1 ∈
            (S_per j hex.choose.1).image
              (fun pair : ι × E => (pair.1, hex.choose.2 + pair.2)) :=
          hex.choose_spec.2
        obtain ⟨pair, hpair_mem, hpair_eq⟩ := Finset.mem_image.mp h_image_mem
        refine ⟨pair, ?_, ?_⟩
        · change pair ∈ S_per j ((mkChain q hq j.castSucc).fst.1)
          rw [h_anc_cs]; exact hpair_mem
        · change ih.fst = (pair.1, (mkChain q hq j.castSucc).fst.2 + pair.2)
          rw [h_anc_cs]
          exact hpair_eq.symm
    obtain ⟨anc, hanc_last, hanc_mem, hanc_step⟩ := chain_recovery
    have hanc_tail : ∀ (k : Fin (M + 1)) (q : ι × E) (hq : q ∈ s'_at (Fin.last M)),
        ‖q.2 - (anc k q hq).2‖ ≤ 2 * (ρ k : ℝ) := by
      have hρ_nonneg : ∀ k : Fin (M + 1), 0 ≤ (ρ k : ℝ) :=
        fun k => NNReal.coe_nonneg _
      refine Fin.reverseInduction ?tail_base ?tail_step
      · intro q hq
        have hlast_snd : (anc (Fin.last M) q hq).2 = q.2 := by rw [hanc_last q hq]
        rw [hlast_snd]
        have hzero : ‖q.2 - q.2‖ = 0 := by simp
        rw [hzero]
        have hpos_nonneg_finlast : 0 ≤ 2 * (ρ (Fin.last M) : ℝ) :=
          mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hρ_nonneg (Fin.last M))
        exact hpos_nonneg_finlast
      · intro k ih q hq
        obtain ⟨pair, hpair_mem, hstep⟩ := hanc_step k q hq
        have hpar : (anc k.castSucc q hq).1 ∈ P k.castSucc :=
          (h_invariant _ _ (hanc_mem _ q hq)).1
        have hpair_in := hSkj_sub k (anc k.castSucc q hq).1 hpar hpair_mem
        rw [Finset.mem_product] at hpair_in
        obtain ⟨_, hpairR⟩ := hpair_in
        have hpair_norm : ‖pair.2‖ ≤ (ρ k.castSucc : ℝ) := hRk_norm k pair.2 hpairR
        have hstep_snd : (anc k.succ q hq).2 = (anc k.castSucc q hq).2 + pair.2 := by
          rw [hstep]
        have hsub_snd : (anc k.succ q hq).2 - (anc k.castSucc q hq).2 = pair.2 := by
          rw [hstep_snd, add_sub_cancel_left]
        have h_eq : q.2 - (anc k.castSucc q hq).2
            = (q.2 - (anc k.succ q hq).2) + pair.2 := by
          calc
            q.2 - (anc k.castSucc q hq).2
                = (q.2 - (anc k.succ q hq).2) + ((anc k.succ q hq).2 - (anc k.castSucc q hq).2)
                  := by
              abel
            _ = (q.2 - (anc k.succ q hq).2) + pair.2 := by rw [hsub_snd]
        have h_norm_le1 : ‖q.2 - (anc k.castSucc q hq).2‖
            ≤ ‖q.2 - (anc k.succ q hq).2‖ + ‖pair.2‖ := by
          rw [h_eq]
          exact norm_add_le _ _
        have h_norm_le2 : ‖q.2 - (anc k.succ q hq).2‖ + ‖pair.2‖
            ≤ 2 * (ρ k.succ : ℝ) + (ρ k.castSucc : ℝ) :=
          add_le_add (ih q hq) hpair_norm
        have h_quarter := hρ_quarter k
        have h_sum_le : 2 * (ρ k.succ : ℝ) + (ρ k.castSucc : ℝ) ≤ 2 * (ρ k.castSucc : ℝ) := by
          nlinarith [NNReal.coe_nonneg (ρ k.succ), NNReal.coe_nonneg (ρ k.castSucc), h_quarter]
        exact le_trans h_norm_le1 (le_trans h_norm_le2 h_sum_le)
    have leaf_recovery :
        ∀ p ∈ s', ∃ q ∈ s'_at (Fin.last M), (leafChoice q, q.2) = p := by
      intro p hp
      rw [hs'_def, Finset.mem_image] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      exact ⟨q, hq, hqp⟩
    have h_nonempty_at : ∀ k : Fin (M + 1), (s'_at k).Nonempty := by
      intro k
      induction k using Fin.induction with
      | zero =>
        rw [hs'_at_zero]
        obtain ⟨i, hi⟩ := hs_nonempty
        obtain ⟨j, hj, _⟩ := hP_zero i hi
        exact ⟨(j, (0 : E)), Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
      | succ k ih =>
        rw [hs'_at_succ k]
        obtain ⟨p, hp⟩ := ih
        have hp1_par : p.1 ∈ P k.castSucc := (h_invariant _ p hp).1
        have hρ_succ_pos : (0 : ℝ) < (ρ k.succ : ℝ) := by
          have hle : ρ (Fin.last M) ≤ ρ k.succ :=
            hρ_anti.antitone (Fin.le_last _)
          rw [hρ_M] at hle
          have hle' : (δ : ℝ) ≤ (ρ k.succ : ℝ) := by exact_mod_cast hle
          exact lt_of_lt_of_le hδ_pos_real hle'
        have hρ_cs_pos : (0 : ℝ) < (ρ k.castSucc : ℝ) := by
          have hle : ρ (Fin.last M) ≤ ρ k.castSucc :=
            hρ_anti.antitone (Fin.le_last _)
          rw [hρ_M] at hle
          have hle' : (δ : ℝ) ≤ (ρ k.castSucc : ℝ) := by exact_mod_cast hle
          exact lt_of_lt_of_le hδ_pos_real hle'
        have hratio_pos : (0 : ℝ) < (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ) :=
          div_pos hρ_cs_pos hρ_succ_pos
        have hratio_pow_pos : (0 : ℝ) <
            ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) :=
          Real.rpow_pos_of_pos hratio_pos _
        have hCn_LB := hCnBracket k
        have hN₂_pos_real : (0 : ℝ) < (N₂ k : ℝ) := by exact_mod_cast hN₂_pos k
        have h_filter_card_pos :
            (0 : ℝ) <
              ({ i ∈ P k.succ |
                  ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                    ((h_uni k.castSucc).parentTube p.1).toConvexSpaceBody }.card : ℝ) := by
          have hLB := hCn_LB p.1 hp1_par
          have hpos : (0 : ℝ) <
              Cn *
                ({ i ∈ P k.succ |
                    ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                      ((h_uni k.castSucc).parentTube p.1).toConvexSpaceBody}.card : ℝ) :=
            lt_of_lt_of_le hN₂_pos_real hLB
          exact (mul_pos_iff_of_pos_left hCn_pos).mp hpos
        have hR_per_card_pos : (0 : ℝ) < ((R_per k).card : ℝ) := by
          have hne : (R_per k).Nonempty := hR_per_nonempty k
          exact_mod_cast Finset.card_pos.mpr hne
        have hδ_pow_pos : (0 : ℝ) < (δ : ℝ) ^ (ε / (M : ℝ)) :=
          Real.rpow_pos_of_pos hδ_pos_real _
        have h_LHS_pos :
            (0 : ℝ) <
              (δ : ℝ) ^ (ε / (M : ℝ)) * ((R_per k).card : ℝ) *
                ({ i ∈ P k.succ |
                    ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                      ((h_uni k.castSucc).parentTube p.1).toConvexSpaceBody}.card : ℝ) :=
          mul_pos (mul_pos hδ_pow_pos hR_per_card_pos) h_filter_card_pos
        have hS_card_pos_real : (0 : ℝ) < K_53 * ((S_per k p.1).card : ℝ) :=
          lt_of_lt_of_le h_LHS_pos (hSkj_count_LB k p.1 hp1_par)
        have hS_card_pos : (0 : ℝ) < ((S_per k p.1).card : ℝ) :=
          (mul_pos_iff_of_pos_left hK_53_pos).mp hS_card_pos_real
        have hS_nonempty : (S_per k p.1).Nonempty := by
          rw [← Finset.card_pos]
          exact_mod_cast hS_card_pos
        obtain ⟨pair, hpair⟩ := hS_nonempty
        refine Finset.biUnion_nonempty.mpr ⟨p, hp, ?_⟩
        exact ⟨(pair.1, p.2 + pair.2), Finset.mem_image.mpr ⟨pair, hpair, rfl⟩⟩
    have chain_geo_gen :
        ∀ (k : Fin (M + 1)) (q : ι × E) (hq : q ∈ s'_at (Fin.last M)),
          (T (leafChoice q)).toConvexSpaceBody ≤
            ((h_uni k).parentTube (anc k q hq).1).toConvexSpaceBody := by
      intro k
      refine Fin.reverseInduction ?base ?step k
      · intro q hq
        have hlast := hanc_last q hq
        have h1 : (anc (Fin.last M) q hq).1 = q.1 := by rw [hlast]
        rw [h1]
        exact (hLeafChoice_spec q hq).2
      · intro k ih q hq
        obtain ⟨pair, hpair_mem, hstep⟩ := hanc_step k q hq
        have hpar : (anc k.castSucc q hq).1 ∈ P k.castSucc :=
          (h_invariant _ _ (hanc_mem _ q hq)).1
        have hpair_in := hSkj_sub k (anc k.castSucc q hq).1 hpar hpair_mem
        rw [Finset.mem_product, Finset.mem_filter] at hpair_in
        obtain ⟨⟨_, hpair1_le⟩, _⟩ := hpair_in
        have heq1 : (anc k.succ q hq).1 = pair.1 := by rw [hstep]
        have ih' :
            (T (leafChoice q)).toConvexSpaceBody ≤
              ((h_uni k.succ).parentTube pair.1).toConvexSpaceBody := by
          have := ih q hq
          rw [heq1] at this
          exact this
        exact le_trans ih' hpair1_le
    have hchild_pair : ∀ m : Fin M, ∀ p ∈ s'_at m.castSucc, ∀ (pair : ι × E),
        pair ∈ S_per m p.1 → ((h_uni m.succ).parentTube pair.1).toConvexSpaceBody
            ≤ ((h_uni m.castSucc).parentTube p.1).toConvexSpaceBody
          ∧ ‖pair.2‖ ≤ (ρ m.castSucc : ℝ) := by
      intro m p hp pair hpair
      have hp_par : p.1 ∈ P m.castSucc := (h_invariant m.castSucc p hp).1
      have hsub := hSkj_sub m p.1 hp_par hpair
      rw [Finset.mem_product, Finset.mem_filter] at hsub
      obtain ⟨⟨_, hbody⟩, hpairR⟩ := hsub
      have hnorm : ‖pair.2‖ ≤ (ρ m.castSucc : ℝ) := hRk_norm m pair.2 hpairR
      exact ⟨hbody, hnorm⟩
    obtain ⟨σ, hσ_last, hσ_0_ge_one, hσ_0_le_four, hσ_anti, hσ_gap, hσ_cs,
        hρ_le_σ, hσ_le_four, hσ_le_threeρ⟩ :=
      Tube.exists_fattened_chain_scale hM ρ hρ_0 hρ_M hρ_anti.antitone
        (fun k => by
          have := hρ_quarter k
          have h0 : (0 : ℝ) ≤ (ρ k.succ : ℝ) := NNReal.coe_nonneg _
          linarith)
    obtain ⟨proj, hproj_mem, hproj_spec, hproj_le⟩ :=
      Tube.exists_prefix_offset_chain hσ_gap hσ_cs
        (fun k => (h_uni k).parentTube) s'_at S_per hs'_at_succ hchild_pair
    have chain_geo :
        ∀ (m : Fin M) (q : ι × E) (hq : q ∈ s'_at (Fin.last M)),
          (T (leafChoice q)).toConvexSpaceBody ≤
            ((h_uni m.castSucc).parentTube (anc m.castSucc q hq).1).toConvexSpaceBody :=
      fun m q hq => chain_geo_gen m.castSucc q hq
    have chain_geo_succ :
        ∀ (m : Fin M) (q : ι × E) (hq : q ∈ s'_at (Fin.last M)),
          (T (leafChoice q)).toConvexSpaceBody ≤
            ((h_uni m.succ).parentTube (anc m.succ q hq).1).toConvexSpaceBody :=
      fun m q hq => chain_geo_gen m.succ q hq
    have Q_count_nodes : ((s'_at (0 : Fin (M + 1))).card : ℝ)
        ≤ C_box * (R + 3) ^ (2 * Module.finrank ℝ E) := by
      have hM_pos : 0 < M := by
        have h1 : 1 ≤ M := hM
        omega
      let zeroM : Fin M := ⟨0, hM_pos⟩
      have hzero_castSucc : (zeroM.castSucc : Fin (M + 1)) = (0 : Fin (M + 1)) :=
        Fin.ext (by simp [zeroM])
      have hcard0 : (s'_at (0 : Fin (M + 1))).card ≤ (P 0).card := by
        rw [hs'_at_zero]
        exact Finset.card_image_le
      have hcard0_P : (P 0).card ≤ ((h_uni 0).parent).card :=
        Finset.card_le_card (hP_sub 0)
      have hcount0 : ((h_uni zeroM.castSucc).parent.card : ℝ) ≤
          C_box * ((4 : ℝ) / (ρ zeroM.castSucc : ℝ)) ^ (2 * Module.finrank ℝ E) :=
        h_count zeroM
      have hρ0_real : (ρ (0 : Fin (M + 1)) : ℝ) = (1 : ℝ) := by exact_mod_cast hρ_0
      have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
      have hC_box_nonneg : 0 ≤ C_box := le_of_lt hC_box_pos
      have h4_le_R3 : (4 : ℝ) ≤ R + 3 := by
        rw [hR_def]; linarith
      calc
        ((s'_at (0 : Fin (M + 1))).card : ℝ) ≤ ((P 0).card : ℝ) := by exact_mod_cast hcard0
        _ ≤ (((h_uni 0).parent).card : ℝ) := by exact_mod_cast hcard0_P
        _ = ((h_uni zeroM.castSucc).parent.card : ℝ) := by rw [hzero_castSucc]
        _ ≤ C_box * ((4 : ℝ) / (ρ zeroM.castSucc : ℝ)) ^ (2 * Module.finrank ℝ E) := hcount0
        _ = C_box * ((4 : ℝ) / (ρ (0 : Fin (M + 1)) : ℝ)) ^ (2 * Module.finrank ℝ E) := by
          rw [hzero_castSucc]
        _ = C_box * ((4 : ℝ) / (1 : ℝ)) ^ (2 * Module.finrank ℝ E) := by rw [hρ0_real]
        _ = C_box * (4 : ℝ) ^ (2 * Module.finrank ℝ E) := by norm_num
        _ ≤ C_box * (R + 3) ^ (2 * Module.finrank ℝ E) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ h4_nonneg h4_le_R3 (2 * Module.finrank ℝ E)) hC_box_nonneg
    have Q_in_ball_nodes : ∀ k : Fin (M + 1), ∀ t ∈ s'_at k,
        ((((h_uni k).parentTube t.1).rescale (σ k)).translate t.2).carrier
          ⊆ Metric.closedBall (0 : E) (R + 3) := by
      intro k t ht
      have ht_inv := h_invariant k t ht
      have hPmem : t.1 ∈ (h_uni k).parent := hP_sub k ht_inv.1
      have hball4 : ((h_uni k).parentTube t.1).carrier ⊆ Metric.closedBall (0 : E) 4 :=
        hParentBall k t.1 hPmem
      have hc_nonneg : (0 : ℝ) ≤ 2 := by norm_num
      have hρk_le_one : (ρ k : ℝ) ≤ 1 := by
        have h0le : ρ k ≤ ρ 0 := hρ_anti.antitone (Fin.zero_le k)
        have h1 : (ρ k : ℝ) ≤ (ρ 0 : ℝ) := by exact_mod_cast h0le
        rw [hρ_0] at h1; exact h1
      have hr : (σ k : ℝ) ≤ (ρ k : ℝ) + 2 := by
        have htmp : (σ k : ℝ) ≤ 3 * (ρ k : ℝ) := hσ_le_threeρ k
        nlinarith
      have hnorm_t2 : ‖t.2‖ ≤ (k.val : ℝ) := hR_partial_norm k t.2 ht_inv.2
      have hk_val_le_M : (k.val : ℝ) ≤ (M : ℝ) := by
        have hk_val_le_M' : k.val ≤ M := k.is_le
        exact_mod_cast hk_val_le_M'
      have hv : ‖t.2‖ ≤ (M : ℝ) := le_trans hnorm_t2 hk_val_le_M
      have h_sub : ((((h_uni k).parentTube t.1).rescale (σ k)).translate t.2).carrier
          ⊆ Metric.closedBall (0 : E) (4 + 2 + (M : ℝ)) :=
        Tube.rescale_translate_carrier_subset_closedBall
          ((h_uni k).parentTube t.1) hball4 hc_nonneg hr
          t.2 hv
      have hR3_eq : (R + 3 : ℝ) = ((M : ℝ) + 4) + 3 := by rw [hR_def]
      have h_sum_le : 4 + 2 + (M : ℝ) ≤ R + 3 := by
        rw [hR_def]; linarith
      exact h_sub.trans (Metric.closedBall_subset_closedBall h_sum_le)
    have Q_ne_nodes : ∀ m : Fin M, (s'_at m.castSucc).Nonempty := fun m => h_nonempty_at _
    obtain ⟨cover_nodes, cover_nodes_mem, cover_nodes_body, cover_nodes_inj⟩ :
        ∃ cover : (ι × E) → (ι × E),
          (∀ p ∈ s', cover p ∈ s'_at (Fin.last M)) ∧
          (∀ p ∈ s', (T' p).toConvexSpaceBody
            ≤ ((((h_uni (Fin.last M)).parentTube (cover p).1).rescale (σ (Fin.last M))).translate
                (cover p).2).toConvexSpaceBody) ∧
          Set.InjOn cover (↑s' : Set (ι × E)) := by
      classical
      set cover : (ι × E) → (ι × E) := fun p =>
        if hp : p ∈ s' then (leaf_recovery p hp).choose else p with hcover_def
      have hcover_mem : ∀ p ∈ s', cover p ∈ s'_at (Fin.last M) := by
        intro p hp
        dsimp [cover]
        rw [dif_pos hp]
        exact (leaf_recovery p hp).choose_spec.1
      have hcover_body : ∀ p ∈ s', (T' p).toConvexSpaceBody
          ≤ ((((h_uni (Fin.last M)).parentTube (cover p).1).rescale (σ (Fin.last M))).translate
              (cover p).2).toConvexSpaceBody := by
        intro p hp
        dsimp [cover]
        rw [dif_pos hp]
        set q := (leaf_recovery p hp).choose with hq_def
        have hq_mem : q ∈ s'_at (Fin.last M) := (leaf_recovery p hp).choose_spec.1
        have hqp : (leafChoice q, q.2) = p := (leaf_recovery p hp).choose_spec.2
        have hp1 : p.1 = leafChoice q := by rw [← hqp]
        have hp2 : p.2 = q.2 := by rw [← hqp]
        have hchain : (T (leafChoice q)).toConvexSpaceBody
            ≤ ((h_uni (Fin.last M)).parentTube (anc (Fin.last M) q hq_mem).1).toConvexSpaceBody :=
          chain_geo_gen (Fin.last M) q hq_mem
        have hanc_last_q : anc (Fin.last M) q hq_mem = q := hanc_last q hq_mem
        rw [hanc_last_q] at hchain
        have h_rescale : ((h_uni (Fin.last M)).parentTube q.1).toConvexSpaceBody
            ≤ (((h_uni (Fin.last M)).parentTube q.1).rescale (σ (Fin.last M))).toConvexSpaceBody :=
          Tube.le_rescale ((h_uni (Fin.last M)).parentTube q.1) (hρ_le_σ (Fin.last M))
        have hchain_rescale : (T (leafChoice q)).toConvexSpaceBody
            ≤ (((h_uni (Fin.last M)).parentTube q.1).rescale (σ (Fin.last M))).toConvexSpaceBody :=
          le_trans hchain h_rescale
        have htrans : ((T (leafChoice q)).translate q.2).toConvexSpaceBody
            ≤ ((((h_uni (Fin.last M)).parentTube q.1).rescale (σ (Fin.last M))).translate
              q.2).toConvexSpaceBody
              := by
          apply translate_le_translate q.2 hchain_rescale
        calc
          (T' p).toConvexSpaceBody = ((T p.1).translate p.2).toConvexSpaceBody := rfl
          _ = ((T (leafChoice q)).translate q.2).toConvexSpaceBody := by rw [hp1, hp2]
          _ ≤ ((((h_uni (Fin.last M)).parentTube q.1).rescale (σ (Fin.last M))).translate
              q.2).toConvexSpaceBody
            := htrans
      have hcover_inj : Set.InjOn cover (↑s' : Set (ι × E)) := by
        intro a ha b hb hcover_eq
        have ha_s' : a ∈ s' := ha
        have hb_s' : b ∈ s' := hb
        set qa := (leaf_recovery a ha_s').choose with hqa_def
        set qb := (leaf_recovery b hb_s').choose with hqb_def
        have hca : cover a = qa := by
          dsimp [cover]; rw [dif_pos ha_s']
        have hcb : cover b = qb := by
          dsimp [cover]; rw [dif_pos hb_s']
        have hqa_eq : (leafChoice qa, qa.2) = a := (leaf_recovery a ha_s').choose_spec.2
        have hqb_eq : (leafChoice qb, qb.2) = b := (leaf_recovery b hb_s').choose_spec.2
        have hq_eq : qa = qb := by
          rw [← hca, ← hcb, hcover_eq]
        rw [hq_eq] at hqa_eq
        rw [← hqa_eq, ← hqb_eq]
      exact ⟨cover, hcover_mem, hcover_body, hcover_inj⟩
    have Q_KT_nodes : ∀ m : Fin M, ∀ p ∈ s'_at m.castSucc,
        IsKatzTao
          ((s'_at m.succ).filter (fun w : ι × E => proj m w = p))
          (fun w : ι × E =>
            ((((h_uni m.succ).parentTube w.1).rescale (σ m.succ)).translate w.2).toConvexSpaceBody)
          (Δ m) := by
      intro m p hp
      rw [IsKatzTao_def]
      have hp_par : p.1 ∈ P m.castSucc := (h_invariant m.castSucc p hp).1
      have hρs_pos : 0 < ρ m.succ := by exact_mod_cast hρ_pos_all m.succ
      have hle : ρ m.succ ≤ σ m.succ := hρ_le_σ m.succ
      have hσs_le_four : σ m.succ ≤ 4 := hσ_le_four m.succ
      have hσs_ratio : (σ m.succ : ℝ) ≤ 3 * (ρ m.succ : ℝ) := hσ_le_threeρ m.succ
      set B : ℝ := K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ)))
        * ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε with hB_def
      have hB_nonneg : 0 ≤ B := by
        dsimp [B]
        refine mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)) ?_
        exact Real.rpow_nonneg (by positivity) _
      have hg_mem : ∀ q ∈ ((s'_at m.succ).filter (fun w : ι × E => proj m w = p)),
          (fun w : ι × E => (w.1, w.2 - p.2)) q ∈ S_per m p.1 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hq_mem : q ∈ s'_at m.succ := hq.1
        have hproj_eq : proj m q = p := hq.2
        rcases hproj_spec m q hq_mem with ⟨pair, hpair_mem, hq_eq⟩
        rw [hproj_eq] at hq_eq hpair_mem
        rw [hq_eq]
        simp only [add_sub_cancel_left]
        exact hpair_mem
      have hg_eq : ∀ q ∈ ((s'_at m.succ).filter (fun w : ι × E => proj m w = p)),
          q = (((fun w : ι × E => (w.1, w.2 - p.2)) q).1, p.2
            + ((fun w : ι × E => (w.1, w.2 - p.2)) q).2) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hq_mem : q ∈ s'_at m.succ := hq.1
        have hproj_eq : proj m q = p := hq.2
        rcases hproj_spec m q hq_mem with ⟨pair, hpair_mem, hq_eq⟩
        rw [hproj_eq] at hq_eq
        rw [hq_eq]
        simp
      have hmax : Kakeya.maxDensity (S_per m p.1)
          (fun pr : ι × E => (((h_uni m.succ).parentTube pr.1).translate pr.2).toConvexSpaceBody)
          ≤ ENNReal.ofReal B := by
        rw [hB_def]
        exact hSkj_density m p.1 hp_par
      have htemp := Tube.maxDensity_fibre_rescale_translate_le
        hρs_pos hle hσs_le_four hσs_ratio ((h_uni m.succ).parentTube) p.2
        ((s'_at m.succ).filter (fun w : ι × E => proj m w = p)) (S_per m p.1)
        (fun w : ι × E => (w.1, w.2 - p.2)) hg_mem hg_eq B hB_nonneg hmax
      have hfinal : Kakeya.maxDensity ((s'_at m.succ).filter (fun w : ι × E => proj m w = p))
          (fun w : ι × E =>
            ((((h_uni m.succ).parentTube w.1).rescale (σ m.succ)).translate w.2).toConvexSpaceBody)
          ≤ Δ m := by
        have h_weaken : ENNReal.ofReal
            (5 * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
              * 3 ^ (Module.finrank ℝ E - 1) * B) ≤ Δ m := by
          rw [hΔ_def, hB_def]
          refine ENNReal.ofReal_le_ofReal ?_
          have hf_nonneg : 0 ≤ (δ : ℝ) ^ (-(ε / (M : ℝ)))
            * ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε := by
            positivity
          have htemp_mul := mul_le_mul_of_nonneg_right hK_53_KT_absorb hf_nonneg
          simpa [mul_assoc] using htemp_mul
        exact le_trans htemp h_weaken
      exact hfinal
    have clause6_anchor_density :
        ∀ ρ_anchor : NNReal, δ ≤ ρ_anchor → ρ_anchor ≤ 1 →
          ∀ p₀ ∈ s',
            ENNReal.ofReal
                (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
                    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2 *
                  ((δ : ℝ) ^ ε / K_cnt ^ M) /
                  ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) *
                    (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))))
              ≤ Kakeya.densityIn
                  (s'.filter (fun p : ι × E =>
                    (T' p).toConvexSpaceBody ≤
                      (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody))
                  (fun p : ι × E => (T' p).toConvexSpaceBody)
                  (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody := by
      set max_ratio_n : ℝ :=
        (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) with hmax_ratio_n_def
      have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
      have h_max_ratio_n_pos : 0 < max_ratio_n := by
        rw [hmax_ratio_n_def]
        exact Real.rpow_pos_of_pos hδ_pos_real _
      have h_max_ratio_bound : ∀ k : Fin M,
          ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) ≤ max_ratio_n := by
        intro k
        have hρ_cs_pos : (0 : ℝ) < (ρ k.castSucc : ℝ) := by
          have hle := hρ_anti.antitone (Fin.le_last k.castSucc)
          rw [hρ_M] at hle
          have : (δ : ℝ) ≤ (ρ k.castSucc : ℝ) := by exact_mod_cast hle
          linarith
        have hρ_s_pos : (0 : ℝ) < (ρ k.succ : ℝ) := by
          have hle := hρ_anti.antitone (Fin.le_last k.succ)
          rw [hρ_M] at hle
          have : (δ : ℝ) ≤ (ρ k.succ : ℝ) := by exact_mod_cast hle
          linarith
        have h_δε_pos : (0 : ℝ) < (δ : ℝ) ^ ε := Real.rpow_pos_of_pos hδ_pos_real _
        have h_ratio_le : (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ) ≤ (δ : ℝ) ^ (-ε) := by
          have h_inv_eq : (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)
              = ((ρ k.succ : ℝ) / (ρ k.castSucc : ℝ))⁻¹ := (inv_div _ _).symm
          rw [h_inv_eq, Real.rpow_neg hδ_pos_real.le]
          exact inv_anti₀ h_δε_pos (hρ_ratio k)
        have hn_minus_one_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) - 1 := by
          have hfn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
          have h1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hfn
          linarith
        have hbase_nn : (0 : ℝ) ≤ (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ) :=
          le_of_lt (div_pos hρ_cs_pos hρ_s_pos)
        calc ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
                ((Module.finrank ℝ E : ℝ) - 1)
            ≤ ((δ : ℝ) ^ (-ε)) ^ ((Module.finrank ℝ E : ℝ) - 1) :=
              Real.rpow_le_rpow hbase_nn h_ratio_le hn_minus_one_nn
          _ = (δ : ℝ) ^ ((-ε) * ((Module.finrank ℝ E : ℝ) - 1)) := by
              rw [← Real.rpow_mul hδ_pos_real.le]
          _ = (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) := by
              congr 1; ring
          _ = max_ratio_n := by rw [hmax_ratio_n_def]
      have segment_hausdorff :
          ∀ {δ' ρ' : NNReal} (T_in T_out : Tube δ' E),
            δ' ≤ ρ' →
            T_in.toConvexSpaceBody ≤ (T_out.rescale ρ').toConvexSpaceBody →
            (T_out.rescale ρ').toConvexSpaceBody
              ≤ (T_in.rescale (4 * ρ')).toConvexSpaceBody :=
        fun T_in T_out _hδρ hsub =>
          Tube.rescale_le_rescale_of_le_rescale T_in T_out hsub
      have h_disc :
          ∀ k : Fin M, ∀ p₀ ∈ s',
            ENNReal.ofReal
                (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
                    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) *
                  ((δ : ℝ) ^ ε / K_cnt ^ M)
                  / (8 : ℝ) ^ (Module.finrank ℝ E - 1))
              ≤ Kakeya.densityIn
                  (s'.filter (fun p : ι × E =>
                    (T' p).toConvexSpaceBody ≤
                      (Tube.rescale (T' p₀)
                          ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody))
                  (fun p : ι × E => (T' p).toConvexSpaceBody)
                  (Tube.rescale (T' p₀)
                      ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody := by
        intro k p₀ hp₀
        obtain ⟨q₀, hq₀, hq₀p₀⟩ := leaf_recovery p₀ hp₀
        set A : ι := (anc k.succ q₀ hq₀).1 with hA_def
        have hδ_le_ρ_succ : δ ≤ ρ k.succ := by
          have := hρ_anti.antitone (Fin.le_last k.succ)
          rw [hρ_M] at this; exact this
        have hp0_eq_leafChoice : p₀.1 = leafChoice q₀ := by rw [← hq₀p₀]
        have hp0_tail : ‖p₀.2 - (anc k.succ q₀ hq₀).2‖ ≤ 2 * (ρ k.succ : ℝ) := by
          have h2 : p₀.2 = q₀.2 := by rw [← hq₀p₀]
          rw [h2]; exact hanc_tail k.succ q₀ hq₀
        have h_chain : (T p₀.1).toConvexSpaceBody ≤
            ((h_uni k.succ).parentTube A).toConvexSpaceBody := by
          have := chain_geo_succ k q₀ hq₀
          rw [hp0_eq_leafChoice]
          exact this
        have h_bridge : ((h_uni k.succ).parentTube A).toConvexSpaceBody
            ≤ ((T p₀.1).rescale ((4 : NNReal) * ρ k.succ)).toConvexSpaceBody :=
          Tube.rescale_le_of_le (T p₀.1) ((h_uni k.succ).parentTube A) h_chain
        have hT'p0_rescale_8ρ_body :
            ((T' p₀).rescale ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody =
              (((T p₀.1).rescale ((8 : NNReal) * ρ k.succ)).translate p₀.2
                ).toConvexSpaceBody := by
          change (((T p₀.1).translate p₀.2).rescale ((8 : NNReal) * ρ k.succ)
              ).toConvexSpaceBody = _
          rw [Tube.translate_rescale_swap]
        have h_shift_into_cap : ∀ p : ι × E,
            (T p.1).toConvexSpaceBody ≤
                ((T p₀.1).rescale ((4 : NNReal) * ρ k.succ)).toConvexSpaceBody →
            ‖p.2 - p₀.2‖ ≤ 4 * (ρ k.succ : ℝ) →
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀) ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody := by
          intro p h_chain_p_4ρ h_off
          have hρ_nn : (0 : ℝ) ≤ (ρ k.succ : ℝ) := NNReal.coe_nonneg _
          have hbudget : (((4 : NNReal) * ρ k.succ : NNReal) : ℝ) + 4 * (ρ k.succ : ℝ)
              ≤ (((8 : NNReal) * ρ k.succ : NNReal) : ℝ) := by push_cast; linarith
          have hstep := Tube.translate_le_rescale_of_body_le (T p.1)
            ((T p₀.1).rescale ((4 : NNReal) * ρ k.succ)) h_chain_p_4ρ (p.2 - p₀.2)
            (by linarith) h_off hbudget
          have hresc : (((T p₀.1).rescale ((4 : NNReal) * ρ k.succ)).rescale
                ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody
              = ((T p₀.1).rescale ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody := rfl
          rw [hresc] at hstep
          have hmono := translate_le_translate p₀.2 hstep
          rw [hT'p0_rescale_8ρ_body]
          refine le_trans (le_of_eq ?_) hmono
          change ConvexSpaceBody.translate (T p.1).toConvexSpaceBody p.2
              = ConvexSpaceBody.translate
                  (ConvexSpaceBody.translate (T p.1).toConvexSpaceBody (p.2 - p₀.2)) p₀.2
          rw [ConvexSpaceBody.translate_translate]
          congr 1
          abel
        have hp₀_in_filter : p₀ ∈ s'.filter (fun p : ι × E =>
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀)
                  ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody) := by
          refine Finset.mem_filter.mpr ⟨hp₀, ?_⟩
          have hδ_le_8ρ : δ ≤ (8 : NNReal) * ρ k.succ := by
            have h8 : ρ k.succ ≤ (8 : NNReal) * ρ k.succ := by
              have : (1 : NNReal) * ρ k.succ ≤ (8 : NNReal) * ρ k.succ :=
                mul_le_mul_left (by norm_num : (1 : NNReal) ≤ 8) (ρ k.succ)
              simpa using this
            exact hδ_le_ρ_succ.trans h8
          rw [← (T' p₀).toConvexBody_cthickening_sub hδ_le_8ρ]
          intro x hx
          exact Metric.self_subset_cthickening _ hx
        set n_dim : ℕ := Module.finrank ℝ E with hn_dim_def
        have hn_pos : 0 < n_dim := Module.finrank_pos
        have hδ_le_one : δ ≤ (1 : NNReal) := by
          have := hρ_anti.antitone (Fin.zero_le (Fin.last M))
          rw [hρ_0, hρ_M] at this
          exact this
        have h8ρ_le_one : (8 : NNReal) * ρ k.succ ≤ (1 : NNReal) := by
          have hρ_gap_k_real : 8 * (ρ k.succ : ℝ) ≤ (ρ k.castSucc : ℝ) :=
            hρ_quarter k
          have hρ_gap_k : (8 : NNReal) * ρ k.succ ≤ ρ k.castSucc := by
            have h := hρ_gap_k_real
            have : ((8 : NNReal) * ρ k.succ : ℝ) ≤ ((ρ k.castSucc : NNReal) : ℝ) := by
              push_cast; linarith
            exact_mod_cast this
          have h_cs_le_one : ρ k.castSucc ≤ (1 : NNReal) := by
            have h1 : ρ k.castSucc ≤ ρ 0 :=
              hρ_anti.antitone (Fin.zero_le _)
            rw [hρ_0] at h1; exact h1
          exact hρ_gap_k.trans h_cs_le_one
        have h_vol_p0_ge :
            (Tube.le_volume.c n_dim : ENNReal) * (δ : ENNReal) ^ (n_dim - 1) ≤
              volume (T' p₀).carrier := by
          have := Tube.le_volume (T' p₀)
          change (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
              ((δ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≤ _ at this
          exact this
        have h_vol_denom_le :
            volume ((T' p₀).rescale ((8 : NNReal) * ρ k.succ)).carrier ≤
              (Tube.volume_le.C n_dim : ENNReal) *
                (((8 : NNReal) * ρ k.succ : NNReal) : ENNReal) ^ (n_dim - 1) :=
          Tube.volume_le h8ρ_le_one _
        classical
        set A_node : ι × E := anc k.succ q₀ hq₀ with hA_node_def
        have hA_node_fst : A_node.1 = A := by rw [hA_node_def, ← hA_def]
        set D : Fin (M + 1) → Finset (ι × E) :=
          Fin.induction
            (∅)
            (fun j prev =>
              if j.succ = k.succ then {A_node}
              else prev.biUnion (fun p : ι × E =>
                (S_per j p.1).image
                  (fun pair : ι × E => (pair.1, p.2 + pair.2)))) with hD_def
        have hD_zero : D 0 = ∅ := by simp [hD_def]
        have hD_succ : ∀ j : Fin M,
            D j.succ =
              if j.succ = k.succ then ({A_node} : Finset (ι × E))
              else (D j.castSucc).biUnion (fun p : ι × E =>
                (S_per j p.1).image
                  (fun pair : ι × E => (pair.1, p.2 + pair.2))) := by
          intro j; simp [hD_def]
        have hD_seed : D k.succ = {A_node} := by
          rw [hD_succ k, if_pos rfl]
        have hD_sub : ∀ d : Fin (M + 1), D d ⊆ s'_at d := by
          intro d
          induction d using Fin.induction with
          | zero => rw [hD_zero]; exact Finset.empty_subset _
          | succ j ih =>
            rw [hD_succ j]
            by_cases hj : j.succ = k.succ
            · rw [if_pos hj]
              rw [Finset.singleton_subset_iff]
              have : A_node ∈ s'_at k.succ := by
                rw [hA_node_def]; exact hanc_mem k.succ q₀ hq₀
              rw [hj]; exact this
            · rw [if_neg hj, hs'_at_succ j]
              exact Finset.biUnion_subset_biUnion_of_subset_left _ ih
        have hD_tail : ∀ d : Fin (M + 1), ∀ q ∈ D d,
            ‖q.2 - A_node.2‖ ≤ 2 * (ρ k.succ : ℝ) - 2 * (ρ d : ℝ) := by
          intro d
          induction d using Fin.induction with
          | zero => rw [hD_zero]; intro q hq; exact absurd hq (Finset.notMem_empty _)
          | succ j ih =>
            intro q hq
            rw [hD_succ j] at hq
            by_cases hj : j.succ = k.succ
            · rw [if_pos hj, Finset.mem_singleton] at hq
              subst hq
              rw [hj]
              simp
            · rw [if_neg hj] at hq
              obtain ⟨p, hp_mem, hq_img⟩ := Finset.mem_biUnion.mp hq
              obtain ⟨pair, hpair, hpair_eq⟩ := Finset.mem_image.mp hq_img
              have hpar : p.1 ∈ P j.castSucc :=
                (h_invariant _ p (hD_sub j.castSucc hp_mem)).1
              have hpair_in := hSkj_sub j p.1 hpar hpair
              rw [Finset.mem_product] at hpair_in
              obtain ⟨_, hpairR⟩ := hpair_in
              have hpair_norm : ‖pair.2‖ ≤ (ρ j.castSucc : ℝ) := hRk_norm j pair.2 hpairR
              have hq2 : q.2 = p.2 + pair.2 := by rw [← hpair_eq]
              have hsplit : q.2 - A_node.2 = (p.2 - A_node.2) + pair.2 := by
                rw [hq2]; abel
              have h1 : ‖q.2 - A_node.2‖ ≤ ‖p.2 - A_node.2‖ + ‖pair.2‖ := by
                rw [hsplit]; exact norm_add_le _ _
              have h2 := ih p hp_mem
              have hgap := hρ_quarter j
              have hρ_nn : (0 : ℝ) ≤ (ρ j.succ : ℝ) := NNReal.coe_nonneg _
              linarith
        have hD_node_geo : ∀ d : Fin (M + 1), ∀ q ∈ D d,
            ((h_uni d).parentTube q.1).toConvexSpaceBody ≤
              ((h_uni k.succ).parentTube A).toConvexSpaceBody := by
          intro d
          induction d using Fin.induction with
          | zero => rw [hD_zero]; intro q hq; exact absurd hq (Finset.notMem_empty _)
          | succ j ih =>
            intro q hq
            rw [hD_succ j] at hq
            by_cases hj : j.succ = k.succ
            · rw [if_pos hj] at hq
              rw [Finset.mem_singleton] at hq
              subst hq
              rw [hA_node_fst]
              rw [hj]
            · rw [if_neg hj] at hq
              obtain ⟨p, hp_mem, hq_img⟩ := Finset.mem_biUnion.mp hq
              obtain ⟨pair, hpair, hpair_eq⟩ := Finset.mem_image.mp hq_img
              have hpar : p.1 ∈ P j.castSucc :=
                (h_invariant _ p (hD_sub j.castSucc hp_mem)).1
              have hpair_in := hSkj_sub j p.1 hpar hpair
              rw [Finset.mem_product, Finset.mem_filter] at hpair_in
              obtain ⟨⟨_, hpair1_le⟩, _⟩ := hpair_in
              have hq1 : q.1 = pair.1 := by rw [← hpair_eq]
              rw [hq1]
              exact le_trans hpair1_le (ih p hp_mem)
        set F_A : Finset (ι × E) :=
          (D (Fin.last M)).image (fun q : ι × E => (leafChoice q, q.2)) with hF_A_def
        have hD_last_sub : D (Fin.last M) ⊆ s'_at (Fin.last M) := hD_sub (Fin.last M)
        have hF_A_subset_filter :
            F_A ⊆ s'.filter (fun p : ι × E =>
              (T' p).toConvexSpaceBody ≤
                (Tube.rescale (T' p₀)
                    ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody) := by
          intro p hp
          rw [hF_A_def, Finset.mem_image] at hp
          obtain ⟨q, hq, hqp⟩ := hp
          have hq_s'at : q ∈ s'_at (Fin.last M) := hD_last_sub hq
          have hp_s' : p ∈ s' := by
            rw [hs'_def]; exact Finset.mem_image.mpr ⟨q, hq_s'at, hqp⟩
          refine Finset.mem_filter.mpr ⟨hp_s', ?_⟩
          have h_leaf_le : (T (leafChoice q)).toConvexSpaceBody ≤
              ((h_uni k.succ).parentTube A).toConvexSpaceBody := by
            have h1 : (T (leafChoice q)).toConvexSpaceBody ≤
                ((h_uni (Fin.last M)).parentTube q.1).toConvexSpaceBody :=
              (hLeafChoice_spec q hq_s'at).2
            exact le_trans h1 (hD_node_geo (Fin.last M) q hq)
          have h_leaf_4ρ : (T (leafChoice q)).toConvexSpaceBody ≤
              ((T p₀.1).rescale ((4 : NNReal) * ρ k.succ)).toConvexSpaceBody :=
            le_trans h_leaf_le h_bridge
          have hp1 : p.1 = leafChoice q := by rw [← hqp]
          have hp2 : p.2 = q.2 := by rw [← hqp]
          have h_chain_p_4ρ : (T p.1).toConvexSpaceBody ≤
              ((T p₀.1).rescale ((4 : NNReal) * ρ k.succ)).toConvexSpaceBody := by
            rw [hp1]; exact h_leaf_4ρ
          have h_off : ‖p.2 - p₀.2‖ ≤ 4 * (ρ k.succ : ℝ) := by
            have hq_tail : ‖q.2 - A_node.2‖ ≤ 2 * (ρ k.succ : ℝ) := by
              have h := hD_tail (Fin.last M) q hq
              have hnn : (0 : ℝ) ≤ (ρ (Fin.last M) : ℝ) := NNReal.coe_nonneg _
              linarith
            have hp0_tail' : ‖A_node.2 - p₀.2‖ ≤ 2 * (ρ k.succ : ℝ) := by
              have := hp0_tail
              rw [hA_node_def]
              rw [← norm_neg]
              simpa using this
            have hsplit : p.2 - p₀.2 = (q.2 - A_node.2) + (A_node.2 - p₀.2) := by
              rw [hp2]; abel
            calc ‖p.2 - p₀.2‖ ≤ ‖q.2 - A_node.2‖ + ‖A_node.2 - p₀.2‖ := by
                  rw [hsplit]; exact norm_add_le _ _
              _ ≤ 2 * (ρ k.succ : ℝ) + 2 * (ρ k.succ : ℝ) := add_le_add hq_tail hp0_tail'
              _ = 4 * (ρ k.succ : ℝ) := by ring
          exact h_shift_into_cap p h_chain_p_4ρ h_off
        have hF_A_in_K : ∀ p ∈ F_A,
            (T' p).toConvexSpaceBody ≤
              (Tube.rescale (T' p₀)
                  ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody := by
          intro p hp
          have := hF_A_subset_filter hp
          exact (Finset.mem_filter.mp this).2
        have hF_A_vol :
            ∀ p ∈ F_A, (Tube.le_volume.c n_dim : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)
              ≤ volume (T' p).carrier := by
          intro p _
          have := Tube.le_volume (T' p)
          change (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
              ((δ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) ≤ _ at this
          exact this
        have h_count_LB :
            ((ρ k.succ : ENNReal) ^ (n_dim - 1)) *
                ENNReal.ofReal ((δ : ℝ) ^ ε / K_cnt ^ M) ≤
              (F_A.card : ENNReal) * ((δ : ENNReal) ^ (n_dim - 1)) := by
          set m : ℕ := n_dim - 1 with hm_def
          have hn_eq : (n_dim : ℝ) = (m : ℝ) + 1 := by
            rw [hm_def, hn_dim_def]
            have : 1 ≤ Module.finrank ℝ E := Module.finrank_pos
            rw [Nat.cast_sub this]; push_cast; ring
          have hn_real_sub : (n_dim : ℝ) - 1 = (m : ℝ) := by rw [hn_eq]; ring
          have hρ_pos : ∀ d : Fin (M + 1), (0 : ℝ) < (ρ d : ℝ) := by
            intro d
            have hle := hρ_anti.antitone (Fin.le_last d)
            rw [hρ_M] at hle
            have : (δ : ℝ) ≤ (ρ d : ℝ) := by exact_mod_cast hle
            have hδr : (0 : ℝ) < (δ : ℝ) := hδ_pos_real
            linarith
          have hρ_le_one : ∀ d : Fin (M + 1), (ρ d : ℝ) ≤ 1 := by
            intro d
            have hle := hρ_anti.antitone (Fin.zero_le d)
            rw [hρ_0] at hle
            exact_mod_cast hle
          have hrpow_eq : ∀ x : ℝ, 0 ≤ x → x ^ ((Module.finrank ℝ E : ℝ) - 1) = x ^ m := by
            intro x hx
            rw [show ((Module.finrank ℝ E : ℝ) - 1) = (m : ℝ) by
                  rw [← hn_dim_def]; exact hn_real_sub]
            rw [Real.rpow_natCast]
          set C0 : ℝ := Cn_eff * K_53 * (μ_cov : ℝ) with hC0_def
          have hμ_cov_real_pos : (0 : ℝ) < (μ_cov : ℝ) := by exact_mod_cast hμ_cov_pos
          have hC0_pos : (0 : ℝ) < C0 := by
            rw [hC0_def]; positivity
          have hM_real_pos : (0 : ℝ) < (M : ℝ) := by
            have : 1 ≤ M := hM; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
          have hS_LB : ∀ (d : Fin M) (p : ι × E),
              p.1 ∈ P d.castSucc →
              (δ : ℝ) ^ (ε / (M : ℝ)) *
                  ((ρ d.castSucc : ℝ) / (ρ d.succ : ℝ)) ^ m / (Cn_eff * K_53)
                ≤ ((S_per d p.1).card : ℝ) := by
            intro d p hpar
            have hCn_LB := hCnBracket d
            have hδpow_pos : (0 : ℝ) < (δ : ℝ) ^ (ε / (M : ℝ)) :=
              Real.rpow_pos_of_pos hδ_pos_real _
            have hratio_pos : (0 : ℝ) < (ρ d.castSucc : ℝ) / (ρ d.succ : ℝ) :=
              div_pos (hρ_pos _) (hρ_pos _)
            have hN₂d_pos : (0 : ℝ) < (N₂ d : ℝ) := by exact_mod_cast hN₂_pos d
            set x_d : ℝ := ((ρ d.castSucc : ℝ) / (ρ d.succ : ℝ)) ^ m / (N₂ d : ℝ) with hx_d_def
            have hx_d_nonneg : 0 ≤ x_d := by
              rw [hx_d_def]; positivity
            have hRk_lb' : c_R * max 1 x_d ≤ ((R_per d).card : ℝ) := by
              have hx_d_eq' : x_d = ((ρ d.castSucc : ℝ) / (ρ d.succ : ℝ)) ^
                  ((Module.finrank ℝ E : ℝ) - 1) / (N₂ d : ℝ) := by
                rw [hx_d_def, hrpow_eq _ hratio_pos.le]
              rw [hx_d_eq']; exact (hRk_card d).1
            set filt : ℕ :=
              ({ i ∈ P d.succ |
                  ((h_uni d.succ).parentTube i).toConvexSpaceBody ≤
                    ((h_uni d.castSucc).parentTube p.1).toConvexSpaceBody }.card) with hfilt_def
            have hfilt_LB : (N₂ d : ℝ) ≤ Cn * (filt : ℝ) := hCn_LB p.1 hpar
            have hcount := hSkj_count_LB d p.1 hpar
            have hfilt_nn : (0 : ℝ) ≤ (filt : ℝ) := Nat.cast_nonneg _
            have hratio_pow_le : ((ρ d.castSucc : ℝ) / (ρ d.succ : ℝ)) ^ m
                ≤ ((R_per d).card : ℝ) / c_R * (N₂ d : ℝ) := by
              calc ((ρ d.castSucc : ℝ) / (ρ d.succ : ℝ)) ^ m
                  = x_d * (N₂ d : ℝ) := by
                    dsimp [x_d]; field_simp [hN₂d_pos.ne']
                _ ≤ max 1 x_d * (N₂ d : ℝ) := by
                  nlinarith [hx_d_nonneg, le_max_right 1 x_d]
                _ ≤ ((R_per d).card : ℝ) / c_R * (N₂ d : ℝ) := by
                  have hmax_nonneg : 0 ≤ max 1 x_d :=
                    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
                  have hdiv : max 1 x_d ≤ ((R_per d).card : ℝ) / c_R := by
                    rw [le_div_iff₀ hc_R_pos]
                    calc
                      max 1 x_d * c_R = c_R * max 1 x_d := mul_comm _ _
                      _ ≤ ((R_per d).card : ℝ) := hRk_lb'
                  exact mul_le_mul_of_nonneg_right hdiv hN₂d_pos.le
            have hN₂_filt : (N₂ d : ℝ) ≤ Cn * (filt : ℝ) := hfilt_LB
            rw [div_le_iff₀ (mul_pos hCn_eff_pos hK_53_pos : 0 < Cn_eff * K_53)]
            calc (δ : ℝ) ^ (ε / (M : ℝ)) * ((ρ d.castSucc : ℝ) / (ρ d.succ : ℝ)) ^ m
                ≤ (δ : ℝ) ^ (ε / (M : ℝ)) * (((R_per d).card : ℝ) / c_R * (N₂ d : ℝ)) :=
                  mul_le_mul_of_nonneg_left hratio_pow_le hδpow_pos.le
              _ ≤ (δ : ℝ) ^ (ε / (M : ℝ)) * (((R_per d).card : ℝ) / c_R * (Cn * (filt : ℝ))) := by
                refine mul_le_mul_of_nonneg_left ?_ hδpow_pos.le
                have h_mul_nonneg : 0 ≤ ((R_per d).card : ℝ) / c_R :=
                  div_nonneg (Nat.cast_nonneg _) hc_R_pos.le
                exact mul_le_mul_of_nonneg_left hN₂_filt h_mul_nonneg
              _ = (Cn / c_R) * ((δ : ℝ) ^ (ε / (M : ℝ)) * ((R_per d).card : ℝ)
                * (filt : ℝ)) := by ring
              _ ≤ (Cn / c_R) * (K_53 * ((S_per d p.1).card : ℝ)) :=
                mul_le_mul_of_nonneg_left hcount (div_nonneg hCn_pos.le hc_R_pos.le)
              _ ≤ Cn_eff * (K_53 * ((S_per d p.1).card : ℝ)) :=
                mul_le_mul_of_nonneg_right hCn_div_cR_le_eff
                  (mul_nonneg (by positivity) (Nat.cast_nonneg _))
              _ = ((S_per d p.1).card : ℝ) * (Cn_eff * K_53) := by ring
          have hoffset_det : ∀ (d : Fin M) (q p p' : ι × E),
              p ∈ D d.castSucc → p' ∈ D d.castSucc →
              q ∈ (S_per d p.1).image (fun pair : ι × E => (pair.1, p.2 + pair.2)) →
              q ∈ (S_per d p'.1).image (fun pair : ι × E => (pair.1, p'.2 + pair.2)) →
              p.2 = p'.2 := by
            intro d q p p' hp hp' hq hq'
            obtain ⟨pair, hpair, hpair_eq⟩ := Finset.mem_image.mp hq
            obtain ⟨pair', hpair', hpair'_eq⟩ := Finset.mem_image.mp hq'
            have hpar : p.1 ∈ P d.castSucc :=
              (h_invariant _ p (hD_sub d.castSucc hp)).1
            have hpar' : p'.1 ∈ P d.castSucc :=
              (h_invariant _ p' (hD_sub d.castSucc hp')).1
            have hpairR : pair.2 ∈ R_per d := by
              have := hSkj_sub d p.1 hpar hpair
              rw [Finset.mem_product] at this
              exact this.2
            have hpairR' : pair'.2 ∈ R_per d := by
              have := hSkj_sub d p'.1 hpar' hpair'
              rw [Finset.mem_product] at this
              exact this.2
            have h1 : p.2 + pair.2 = q.2 := by rw [← hpair_eq]
            have h2 : p'.2 + pair'.2 = q.2 := by rw [← hpair'_eq]
            have hpmem : p.2 ∈ R_partial d.castSucc :=
              (h_invariant _ p (hD_sub d.castSucc hp)).2
            have hp'mem : p'.2 ∈ R_partial d.castSucc :=
              (h_invariant _ p' (hD_sub d.castSucc hp')).2
            exact (subStickyFrostmanLemma.outerBody.RPartial_add_inj
              M R_per hR_per_nonempty R_partial hR_partial_zero hR_partial_succ
              hRk_direct d hpmem hp'mem hpairR hpairR' (h1.trans h2.symm)).1
          have hNode_step : ∀ d : Fin M,
              (∑ p ∈ D d.castSucc, (S_per d p.1).card)
                ≤ μ_cov * ((D d.castSucc).biUnion
                    (fun p : ι × E => (S_per d p.1).image
                      (fun pair : ι × E => (pair.1, p.2 + pair.2)))).card := by
            intro d
            refine card_biUnion_image_translate_ge (μ := μ_cov) ?_
            intro q hq
            set Filt : Finset (ι × E) :=
              (D d.castSucc).filter (fun p : ι × E =>
                q ∈ (S_per d p.1).image
                  (fun pair : ι × E => (pair.1, p.2 + pair.2))) with hFilt_def
            have hFilt_cond : ∀ p ∈ Filt,
                ((h_uni d.succ).parentTube q.1).toConvexSpaceBody ≤
                  ((h_uni d.castSucc).parentTube p.1).toConvexSpaceBody := by
              intro p hp
              rw [hFilt_def, Finset.mem_filter] at hp
              obtain ⟨hp_mem, hq_img⟩ := hp
              obtain ⟨pair, hpair, hpair_eq⟩ := Finset.mem_image.mp hq_img
              have hpar : p.1 ∈ P d.castSucc :=
                (h_invariant _ p (hD_sub d.castSucc hp_mem)).1
              have hpair_in := hSkj_sub d p.1 hpar hpair
              rw [Finset.mem_product, Finset.mem_filter] at hpair_in
              obtain ⟨⟨_, hpair1_le⟩, _⟩ := hpair_in
              have hq1 : q.1 = pair.1 := by rw [← hpair_eq]
              rw [hq1]; exact hpair1_le
            have hFst_sub : (Filt.image Prod.fst) ⊆ (h_uni d.castSucc).parent := by
              intro a ha
              obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp ha
              rw [hFilt_def, Finset.mem_filter] at hp
              rw [← hpa]
              exact hP_sub _ (h_invariant _ p (hD_sub d.castSucc hp.1)).1
            have hq1_par : q.1 ∈ (h_uni d.succ).parent := by
              obtain ⟨p, hp_mem, hq_img⟩ := Finset.mem_biUnion.mp hq
              obtain ⟨pair, hpair, hpair_eq⟩ := Finset.mem_image.mp hq_img
              have hpar : p.1 ∈ P d.castSucc :=
                (h_invariant _ p (hD_sub d.castSucc hp_mem)).1
              have hsub := hSkj_sub d p.1 hpar hpair
              rw [Finset.mem_product] at hsub
              obtain ⟨hpair1, _⟩ := hsub
              rw [Finset.mem_filter] at hpair1
              have hq1_eq : q.1 = pair.1 := by rw [← hpair_eq]
              rw [hq1_eq]; exact hP_sub d.succ hpair1.1
            have hμ' := h_cov ((h_uni d.succ).parentTube q.1) d.castSucc
              (parent_has_leaf d.succ q.1 hq1_par)
            have himg_sub : Filt.image Prod.fst ⊆
                (h_uni d.castSucc).parent.filter (fun j =>
                  ((h_uni d.succ).parentTube q.1).toConvexSpaceBody ≤
                    ((h_uni d.castSucc).parentTube j).toConvexSpaceBody) := by
              intro a ha
              obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp ha
              refine Finset.mem_filter.mpr ⟨hFst_sub ha, ?_⟩
              rw [← hpa]; exact hFilt_cond p hp
            have hcard_img : (Filt.image Prod.fst).card = Filt.card := by
              apply Finset.card_image_of_injOn
              intro x hx y hy hxy
              rw [hFilt_def, Finset.coe_filter] at hx hy
              exact Prod.ext hxy (hoffset_det d q x y hx.1 hy.1 hx.2 hy.2)
            calc Filt.card = (Filt.image Prod.fst).card := hcard_img.symm
              _ ≤ ((h_uni d.castSucc).parent.filter (fun j =>
                    ((h_uni d.succ).parentTube q.1).toConvexSpaceBody ≤
                      ((h_uni d.castSucc).parentTube j).toConvexSpaceBody)).card :=
                  Finset.card_le_card himg_sub
              _ ≤ μ_cov := hμ'
          set g : Fin (M + 1) → ℝ := fun d =>
            ((ρ k.succ : ℝ) / (ρ d : ℝ)) ^ m *
              (δ : ℝ) ^ (ε * ((d.val - k.succ.val : ℕ) : ℝ) / (M : ℝ)) /
              C0 ^ (d.val - k.succ.val : ℕ) with hg_def
          have hD_count : ∀ d : Fin (M + 1), k.succ ≤ d → g d ≤ ((D d).card : ℝ) := by
            intro d
            induction d using Fin.induction with
            | zero =>
              intro hle
              exact absurd hle (by
                simp only [Fin.le_def, Fin.val_zero]
                exact Nat.not_le.mpr (Nat.succ_pos _))
            | succ j ih =>
              intro hle
              by_cases hj : j.succ = k.succ
              · have hgap0 : (j.succ.val - k.succ.val : ℕ) = 0 := by
                  rw [hj]; exact Nat.sub_self _
                have hg1 : g j.succ = 1 := by
                  rw [hg_def]
                  simp only [hgap0, Nat.cast_zero, pow_zero, mul_zero, zero_div,
                    Real.rpow_zero, mul_one, div_one]
                  rw [hj]
                  rw [div_self (hρ_pos k.succ).ne', one_pow]
                rw [hg1, hD_succ j, if_pos hj]
                simp
              · have hvs : j.succ.val = j.val + 1 := Fin.val_succ j
                have hvc : j.castSucc.val = j.val := Fin.val_castSucc j
                have hks : k.succ.val = k.val + 1 := Fin.val_succ k
                have hle_val : k.succ.val ≤ j.succ.val := by
                  rw [Fin.le_def] at hle; exact hle
                have hne_val : k.succ.val ≠ j.succ.val := by
                  intro h; exact hj (Fin.ext h.symm)
                have hle_cs : k.succ ≤ j.castSucc := by
                  rw [Fin.le_def]; omega
                have ihv := ih hle_cs
                have hle_cs_val : k.succ.val ≤ j.castSucc.val := by
                  rw [Fin.le_def] at hle_cs; exact hle_cs
                have hgap_cs : (j.castSucc.val - k.succ.val : ℕ) =
                    (j.succ.val - k.succ.val : ℕ) - 1 := by omega
                have hgap_succ_pos : 1 ≤ (j.succ.val - k.succ.val : ℕ) := by omega
                have hρratio_cs_pos : (0 : ℝ) < (ρ k.succ : ℝ) / (ρ j.castSucc : ℝ) :=
                  div_pos (hρ_pos _) (hρ_pos _)
                have hδpow_pos : (0 : ℝ) <
                    (δ : ℝ) ^ (ε * ((j.castSucc.val - k.succ.val : ℕ) : ℝ) / (M : ℝ)) :=
                  Real.rpow_pos_of_pos hδ_pos_real _
                have hg_cs_pos : 0 < g j.castSucc := by
                  rw [hg_def]; positivity
                set σ : ℝ := (δ : ℝ) ^ (ε / (M : ℝ)) *
                  ((ρ j.castSucc : ℝ) / (ρ j.succ : ℝ)) ^ m / (Cn_eff * K_53) with hσ_def
                have hσ_pos : 0 < σ := by
                  rw [hσ_def]
                  have : (0 : ℝ) < (ρ j.castSucc : ℝ) / (ρ j.succ : ℝ) :=
                    div_pos (hρ_pos _) (hρ_pos _)
                  positivity
                have hsum_lb : ((D j.castSucc).card : ℝ) * σ ≤
                    (∑ p ∈ D j.castSucc, ((S_per j p.1).card : ℝ)) := by
                  have hconst : ((D j.castSucc).card : ℝ) * σ
                      = ∑ _p ∈ D j.castSucc, σ := by
                    rw [Finset.sum_const, nsmul_eq_mul]
                  rw [hconst]
                  apply Finset.sum_le_sum
                  intro p hp
                  have hpar : p.1 ∈ P j.castSucc :=
                    (h_invariant _ p (hD_sub j.castSucc hp)).1
                  rw [hσ_def]
                  exact hS_LB j p hpar
                have hstep_real : ((D j.castSucc).card : ℝ) * σ ≤
                    (μ_cov : ℝ) * ((D j.succ).card : ℝ) := by
                  rw [hD_succ j, if_neg hj]
                  have h1 := hNode_step j
                  have h1r : (∑ p ∈ D j.castSucc, ((S_per j p.1).card : ℝ)) ≤
                      (μ_cov : ℝ) * (((D j.castSucc).biUnion
                        (fun p : ι × E => (S_per j p.1).image
                          (fun pair : ι × E => (pair.1, p.2 + pair.2)))).card : ℝ) := by
                    exact_mod_cast h1
                  exact le_trans hsum_lb h1r
                have hμ_pos : (0 : ℝ) < (μ_cov : ℝ) := hμ_cov_real_pos
                have hDsucc_lb : g j.castSucc * σ / (μ_cov : ℝ) ≤ ((D j.succ).card : ℝ) := by
                  rw [div_le_iff₀ hμ_pos]
                  calc g j.castSucc * σ
                      ≤ ((D j.castSucc).card : ℝ) * σ :=
                        mul_le_mul_of_nonneg_right ihv hσ_pos.le
                    _ ≤ (μ_cov : ℝ) * ((D j.succ).card : ℝ) := hstep_real
                    _ = ((D j.succ).card : ℝ) * (μ_cov : ℝ) := by ring
                have hg_step : g j.succ = g j.castSucc * σ / (μ_cov : ℝ) := by
                  simp only [hg_def, hσ_def, hC0_def]
                  have hρcs_ne : (ρ j.castSucc : ℝ) ≠ 0 := (hρ_pos _).ne'
                  have hρsucc_ne : (ρ j.succ : ℝ) ≠ 0 := (hρ_pos _).ne'
                  have hδ_ne : (δ : ℝ) ≠ 0 := hδ_pos_real.ne'
                  have hCn_ne : Cn ≠ 0 := hCn_pos.ne'
                  have hK53_ne : K_53 ≠ 0 := hK_53_pos.ne'
                  have hμ_ne : (μ_cov : ℝ) ≠ 0 := hμ_cov_real_pos.ne'
                  have hratio_tel :
                      ((ρ k.succ : ℝ) / (ρ j.succ : ℝ)) ^ m =
                      ((ρ k.succ : ℝ) / (ρ j.castSucc : ℝ)) ^ m *
                        ((ρ j.castSucc : ℝ) / (ρ j.succ : ℝ)) ^ m := by
                    rw [← mul_pow]
                    congr 1
                    field_simp
                  have hgap_eq : (j.succ.val - k.succ.val : ℕ) =
                      (j.castSucc.val - k.succ.val : ℕ) + 1 := by omega
                  have hgap_cast : ((j.succ.val - k.succ.val : ℕ) : ℝ) =
                      ((j.castSucc.val - k.succ.val : ℕ) : ℝ) + 1 := by
                    rw [hgap_eq]; push_cast; ring
                  have hδ_tel :
                      (δ : ℝ) ^ (ε * ((j.succ.val - k.succ.val : ℕ) : ℝ) / (M : ℝ)) =
                      (δ : ℝ) ^ (ε * ((j.castSucc.val - k.succ.val : ℕ) : ℝ) / (M : ℝ)) *
                        (δ : ℝ) ^ (ε / (M : ℝ)) := by
                    rw [← Real.rpow_add hδ_pos_real]
                    congr 1
                    rw [hgap_cast, mul_add, mul_one, add_div]
                  have hC0_tel :
                      (Cn_eff * K_53 * (μ_cov : ℝ)) ^ (j.succ.val - k.succ.val : ℕ) =
                      (Cn_eff * K_53 * (μ_cov : ℝ)) ^ (j.castSucc.val - k.succ.val : ℕ) *
                        (Cn_eff * K_53 * (μ_cov : ℝ)) := by
                    rw [hgap_eq, pow_succ]
                  rw [hratio_tel, hδ_tel, hC0_tel]
                  field_simp
                rw [hg_step]
                exact hDsucc_lb
          have hLeaf_fiber : ((D (Fin.last M)).card : ℝ) ≤
              (μ_cov : ℝ) * (F_A.card : ℝ) := by
            have hMapsTo : Set.MapsTo (fun q : ι × E => (leafChoice q, q.2))
                (D (Fin.last M) : Set (ι × E)) (F_A : Set (ι × E)) := by
              intro q hq
              rw [Finset.mem_coe, hF_A_def]
              exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
            have hcard_eq := Finset.card_eq_sum_card_fiberwise hMapsTo
            have hfiber_le : ∀ p ∈ F_A,
                ({q ∈ D (Fin.last M) | (leafChoice q, q.2) = p}.card) ≤ μ_cov := by
              intro p hp_FA
              set Fib : Finset (ι × E) :=
                {q ∈ D (Fin.last M) | (leafChoice q, q.2) = p} with hFib_def
              have hp1_s : p.1 ∈ s := by
                rw [hF_A_def] at hp_FA
                obtain ⟨q', hq'_mem, hq'_eq⟩ := Finset.mem_image.mp hp_FA
                have hlc : leafChoice q' = p.1 := by rw [← hq'_eq]
                rw [← hlc]
                exact (hLeafChoice_spec q' (hD_last_sub hq'_mem)).1
              have hFib_cond : ∀ q ∈ Fib,
                  (T p.1).toConvexSpaceBody ≤
                    ((h_uni (Fin.last M)).parentTube q.1).toConvexSpaceBody := by
                intro q hq
                rw [hFib_def, Finset.mem_filter] at hq
                obtain ⟨hq_mem, hq_eq⟩ := hq
                have hlc : leafChoice q = p.1 := by
                  rw [← hq_eq]
                have hspec := (hLeafChoice_spec q (hD_last_sub hq_mem)).2
                rw [hlc] at hspec
                exact hspec
              have hFst_sub : (Fib.image Prod.fst) ⊆ (h_uni (Fin.last M)).parent := by
                intro a ha
                obtain ⟨q, hq, hqa⟩ := Finset.mem_image.mp ha
                rw [hFib_def, Finset.mem_filter] at hq
                rw [← hqa]
                exact hP_sub _ (h_invariant _ q (hD_last_sub hq.1)).1
              have hμ := h_cov (T p.1) (Fin.last M) ⟨p.1, hp1_s, le_refl _⟩
              have himg_sub : Fib.image Prod.fst ⊆
                  (h_uni (Fin.last M)).parent.filter (fun j =>
                    (T p.1).toConvexSpaceBody ≤
                      ((h_uni (Fin.last M)).parentTube j).toConvexSpaceBody) := by
                intro a ha
                obtain ⟨q, hq, hqa⟩ := Finset.mem_image.mp ha
                refine Finset.mem_filter.mpr ⟨hFst_sub ha, ?_⟩
                rw [← hqa]; exact hFib_cond q hq
              have hcard_img : (Fib.image Prod.fst).card = Fib.card := by
                apply Finset.card_image_of_injOn
                intro x hx y hy hxy
                rw [hFib_def, Finset.coe_filter] at hx hy
                have hx2 : x.2 = p.2 := by
                  have := hx.2
                  simpa using congrArg Prod.snd this
                have hy2 : y.2 = p.2 := by
                  have := hy.2
                  simpa using congrArg Prod.snd this
                exact Prod.ext hxy (hx2.trans hy2.symm)
              calc Fib.card = (Fib.image Prod.fst).card := hcard_img.symm
                _ ≤ ((h_uni (Fin.last M)).parent.filter (fun j =>
                      (T p.1).toConvexSpaceBody ≤
                        ((h_uni (Fin.last M)).parentTube j).toConvexSpaceBody)).card :=
                    Finset.card_le_card himg_sub
                _ ≤ μ_cov := hμ
            have hsum_le : (D (Fin.last M)).card ≤ μ_cov * F_A.card := by
              rw [hcard_eq]
              calc (∑ p ∈ F_A, {q ∈ D (Fin.last M) | (leafChoice q, q.2) = p}.card)
                  ≤ ∑ _p ∈ F_A, μ_cov := Finset.sum_le_sum hfiber_le
                _ = μ_cov * F_A.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
            exact_mod_cast hsum_le
          have hgap_last : (Fin.last M).val - k.succ.val = M - (k.val + 1) := by
            rw [Fin.val_last, Fin.val_succ]
          have hk_lt : k.val + 1 ≤ M := k.isLt
          set target : ℝ := ((ρ k.succ : ℝ) / (δ : ℝ)) ^ m * (δ : ℝ) ^ ε / K_cnt ^ M
            with htarget_def
          have htarget_nn : 0 ≤ target := by
            rw [htarget_def]
            have hbase_nn : (0 : ℝ) ≤ ((ρ k.succ : ℝ) / (δ : ℝ)) ^ m :=
              pow_nonneg (div_nonneg (ρ k.succ).coe_nonneg (δ : NNReal).coe_nonneg) _
            positivity
          have hg_last_ge : (μ_cov : ℝ) * target ≤ g (Fin.last M) := by
            simp only [hg_def, htarget_def]
            have hρlast : (ρ (Fin.last M) : ℝ) = (δ : ℝ) := by rw [hρ_M]
            rw [hρlast]
            set gp : ℕ := (Fin.last M).val - k.succ.val with hgp_def
            have hgp_le_M : gp ≤ M := by rw [hgap_last]; omega
            have hgp_succ_le_M : gp + 1 ≤ M := by rw [hgap_last]; omega
            have hδ_le1 : (δ : ℝ) ≤ 1 := by
              have := hρ_anti.antitone (Fin.zero_le (Fin.last M))
              rw [hρ_0, hρ_M] at this; exact_mod_cast this
            have hδ_exp : (δ : ℝ) ^ ε ≤ (δ : ℝ) ^ (ε * (gp : ℝ) / (M : ℝ)) := by
              apply Real.rpow_le_rpow_of_exponent_ge hδ_pos_real hδ_le1
              rw [mul_div_assoc]
              calc ε * ((gp : ℝ) / (M : ℝ)) ≤ ε * 1 := by
                    apply mul_le_mul_of_nonneg_left _ hε.le
                    rw [div_le_one hM_real_pos]
                    exact_mod_cast hgp_le_M
                _ = ε := mul_one _
            have hC0_le_Kcnt : C0 ≤ K_cnt := by
              rw [hC0_def, hK_cnt_def]
              have h1 : Cn_eff ≤ max Cn_eff 1 := le_max_left _ _
              have : Cn_eff * K_53 ≤ max Cn_eff 1 * K_53 :=
                mul_le_mul_of_nonneg_right h1 hK_53_pos.le
              calc Cn_eff * K_53 * (μ_cov : ℝ)
                  ≤ max Cn_eff 1 * K_53 * (μ_cov : ℝ) :=
                    mul_le_mul_of_nonneg_right this hμ_cov_real_pos.le
                _ = K_53 * max Cn_eff 1 * (μ_cov : ℝ) := by ring
            have hKcnt_ge_μ : (μ_cov : ℝ) ≤ K_cnt := by
              rw [hK_cnt_def]
              have h1 : (1 : ℝ) ≤ K_53 * max Cn_eff 1 := by
                have ha : (1 : ℝ) ≤ K_53 := hK_53_ge_one
                have hb : (1 : ℝ) ≤ max Cn_eff 1 := le_max_right _ _
                nlinarith [ha, hb]
              nlinarith [h1, hμ_cov_real_pos.le]
            have hC0_pow_le : (μ_cov : ℝ) * C0 ^ gp ≤ K_cnt ^ M := by
              calc (μ_cov : ℝ) * C0 ^ gp
                  ≤ K_cnt * K_cnt ^ gp := by
                    apply mul_le_mul hKcnt_ge_μ _ (by positivity) hK_cnt_pos.le
                    exact pow_le_pow_left₀ hC0_pos.le hC0_le_Kcnt gp
                _ = K_cnt ^ (gp + 1) := by rw [pow_succ]; ring
                _ ≤ K_cnt ^ M := pow_le_pow_right₀ hK_cnt_ge_one hgp_succ_le_M
            set base : ℝ := ((ρ k.succ : ℝ) / (δ : ℝ)) ^ m with hbase_def
            have hbase_nn : (0 : ℝ) ≤ base :=
              pow_nonneg (div_nonneg (ρ k.succ).coe_nonneg (δ : NNReal).coe_nonneg) _
            have hC0gp_pos : (0 : ℝ) < C0 ^ gp := pow_pos hC0_pos _
            have hKcntM_pos : (0 : ℝ) < K_cnt ^ M := pow_pos hK_cnt_pos _
            have hδε_pos : (0 : ℝ) < (δ : ℝ) ^ ε := Real.rpow_pos_of_pos hδ_pos_real _
            have hδεgp_pos : (0 : ℝ) < (δ : ℝ) ^ (ε * (gp : ℝ) / (M : ℝ)) :=
              Real.rpow_pos_of_pos hδ_pos_real _
            rw [show (μ_cov : ℝ) * (base * (δ : ℝ) ^ ε / K_cnt ^ M)
                  = ((μ_cov : ℝ) * base * (δ : ℝ) ^ ε) / K_cnt ^ M from by ring]
            rw [div_le_div_iff₀ hKcntM_pos hC0gp_pos]
            calc (μ_cov : ℝ) * base * (δ : ℝ) ^ ε * C0 ^ gp
                = base * (δ : ℝ) ^ ε * ((μ_cov : ℝ) * C0 ^ gp) := by ring
              _ ≤ base * (δ : ℝ) ^ (ε * (gp : ℝ) / (M : ℝ)) * (K_cnt ^ M) := by
                  apply mul_le_mul _ hC0_pow_le (by positivity) (by positivity)
                  exact mul_le_mul_of_nonneg_left hδ_exp hbase_nn
          have hD_last_ge : (μ_cov : ℝ) * target ≤ ((D (Fin.last M)).card : ℝ) :=
            le_trans hg_last_ge (hD_count (Fin.last M) (Fin.le_last _))
          have hFA_real : target ≤ (F_A.card : ℝ) := by
            have hchain : (μ_cov : ℝ) * target ≤ (μ_cov : ℝ) * (F_A.card : ℝ) :=
              le_trans hD_last_ge hLeaf_fiber
            exact le_of_mul_le_mul_left hchain hμ_cov_real_pos
          have hδ_pow_pos : (0 : ℝ) < (δ : ℝ) ^ m := pow_pos hδ_pos_real _
          have hR1 : (ρ k.succ : ℝ) ^ m * ((δ : ℝ) ^ ε / K_cnt ^ M)
              ≤ (F_A.card : ℝ) * (δ : ℝ) ^ m := by
            have hmul := mul_le_mul_of_nonneg_right hFA_real hδ_pow_pos.le
            have hδm_ne : (δ : ℝ) ^ m ≠ 0 := hδ_pow_pos.ne'
            have hKcntM_ne : (K_cnt : ℝ) ^ M ≠ 0 := (pow_pos hK_cnt_pos M).ne'
            have hδ_ne : (δ : ℝ) ≠ 0 := hδ_pos_real.ne'
            have hlhs : target * (δ : ℝ) ^ m
                = (ρ k.succ : ℝ) ^ m * ((δ : ℝ) ^ ε / K_cnt ^ M) := by
              rw [htarget_def, div_pow]
              rw [show (ρ k.succ : ℝ) ^ m / (δ : ℝ) ^ m * (δ : ℝ) ^ ε / K_cnt ^ M *
                      (δ : ℝ) ^ m
                  = (ρ k.succ : ℝ) ^ m / (δ : ℝ) ^ m * (δ : ℝ) ^ m *
                      ((δ : ℝ) ^ ε / K_cnt ^ M) from by ring]
              rw [div_mul_cancel₀ _ hδm_ne]
            rw [hlhs] at hmul
            exact hmul
          have hρsucc_nn : (0 : ℝ) ≤ (ρ k.succ : ℝ) := (ρ k.succ).coe_nonneg
          have hslack_nn : (0 : ℝ) ≤ (δ : ℝ) ^ ε / K_cnt ^ M :=
            div_nonneg (Real.rpow_pos_of_pos hδ_pos_real _).le (pow_pos hK_cnt_pos M).le
          have he1 : (ρ k.succ : ENNReal) ^ m = ENNReal.ofReal ((ρ k.succ : ℝ) ^ m) := by
            rw [ENNReal.ofReal_pow hρsucc_nn, ENNReal.ofReal_coe_nnreal]
          have he2 : (δ : ENNReal) ^ m = ENNReal.ofReal ((δ : ℝ) ^ m) := by
            rw [ENNReal.ofReal_pow (δ : NNReal).coe_nonneg, ENNReal.ofReal_coe_nnreal]
          have he3 : (F_A.card : ENNReal) = ENNReal.ofReal (F_A.card : ℝ) := by
            rw [ENNReal.ofReal_natCast]
          rw [he1, he2, he3]
          rw [← ENNReal.ofReal_mul (pow_nonneg hρsucc_nn _),
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          exact hR1
        have h_dens_LB :
            (F_A.card : ENNReal) *
                ((Tube.le_volume.c n_dim : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) /
              volume ((T' p₀).rescale ((8 : NNReal) * ρ k.succ)).carrier ≤
            Kakeya.densityIn
              (s'.filter (fun p : ι × E =>
                (T' p).toConvexSpaceBody ≤
                  (Tube.rescale (T' p₀)
                      ((8 : NNReal) * ρ k.succ)).toConvexSpaceBody))
              (fun p : ι × E => (T' p).toConvexSpaceBody)
              ((Tube.rescale (T' p₀)
                  ((8 : NNReal) * ρ k.succ))).toConvexSpaceBody :=
          Kakeya.densityIn_ge_of_count_volume
            hF_A_subset_filter hF_A_in_K hF_A_vol
        have h_denom_LB :
            (F_A.card : ENNReal) *
                ((Tube.le_volume.c n_dim : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) /
              ((Tube.volume_le.C n_dim : ENNReal) *
                (((8 : NNReal) * ρ k.succ : NNReal) : ENNReal) ^ (n_dim - 1)) ≤
            (F_A.card : ENNReal) *
                ((Tube.le_volume.c n_dim : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) /
              volume ((T' p₀).rescale ((8 : NNReal) * ρ k.succ)).carrier :=
          ENNReal.div_le_div_left h_vol_denom_le _
        refine le_trans ?_ (le_trans h_denom_LB h_dens_LB)
        have h_vol_C_pos : (0 : ℝ) < (Tube.volume_le.C n_dim : ℝ) := by
          unfold Tube.volume_le.C
          positivity
        have h_vol_C_ne_top : (Tube.volume_le.C n_dim : ENNReal) ≠ ⊤ :=
          ENNReal.coe_ne_top
        have h_vol_C_ne_zero : (Tube.volume_le.C n_dim : ENNReal) ≠ 0 := by
          rw [ne_eq, ENNReal.coe_eq_zero]
          unfold Tube.volume_le.C
          positivity
        have h_4_ne_top : (8 : ENNReal) ≠ ⊤ := by norm_num
        have h_4_ne_zero : (8 : ENNReal) ≠ 0 := by norm_num
        have h_4_pow_ne_top : (8 : ENNReal) ^ (n_dim - 1) ≠ ⊤ :=
          ENNReal.pow_ne_top h_4_ne_top
        have h_4_pow_ne_zero : (8 : ENNReal) ^ (n_dim - 1) ≠ 0 :=
          pow_ne_zero _ h_4_ne_zero
        have h_ρ_pos : (0 : NNReal) < ρ k.succ := hδ_pos.trans_le hδ_le_ρ_succ
        have h_ρ_ne_zero : (ρ k.succ : ENNReal) ≠ 0 := by
          rw [ne_eq, ENNReal.coe_eq_zero]; exact h_ρ_pos.ne'
        have h_ρ_ne_top : (ρ k.succ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        have h_ρ_pow_ne_zero : (ρ k.succ : ENNReal) ^ (n_dim - 1) ≠ 0 :=
          pow_ne_zero _ h_ρ_ne_zero
        have h_ρ_pow_ne_top : (ρ k.succ : ENNReal) ^ (n_dim - 1) ≠ ⊤ :=
          ENNReal.pow_ne_top h_ρ_ne_top
        have h_inSlack_real_nonneg : (0 : ℝ) ≤ (δ : ℝ) ^ ε / K_cnt ^ M := by
          have hδr : (0 : ℝ) < (δ : ℝ) := hδ_pos_real
          exact le_of_lt (div_pos (Real.rpow_pos_of_pos hδr _) (pow_pos hK_cnt_pos M))
        have h_ofReal_eq :
            ENNReal.ofReal (((Tube.le_volume.c n_dim : ℝ) /
                (Tube.volume_le.C n_dim : ℝ)) * ((δ : ℝ) ^ ε / K_cnt ^ M)
                / (8 : ℝ) ^ (n_dim - 1)) =
              (Tube.le_volume.c n_dim : ENNReal) /
                (Tube.volume_le.C n_dim : ENNReal) /
                ((8 : ENNReal) ^ (n_dim - 1)) *
                ENNReal.ofReal ((δ : ℝ) ^ ε / K_cnt ^ M) := by
          rw [show ((Tube.le_volume.c n_dim : ℝ) /
                (Tube.volume_le.C n_dim : ℝ)) * ((δ : ℝ) ^ ε / K_cnt ^ M)
                / (8 : ℝ) ^ (n_dim - 1)
              = (((Tube.le_volume.c n_dim : ℝ) /
                (Tube.volume_le.C n_dim : ℝ)) / (8 : ℝ) ^ (n_dim - 1))
                * ((δ : ℝ) ^ ε / K_cnt ^ M) by ring]
          rw [ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < (8 : ℝ) ^ (n_dim - 1))]
          rw [ENNReal.ofReal_div_of_pos h_vol_C_pos]
          rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
          rw [show ((8 : ℝ) ^ (n_dim - 1)) = (((8 : ℕ) : ℝ) ^ (n_dim - 1)) by norm_num]
          rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ (8 : ℕ))]
          rw [show ((8 : ENNReal) ^ (n_dim - 1)) = (((8 : ℕ) : ENNReal) ^ (n_dim - 1)) by norm_num]
          rw [show ENNReal.ofReal ((8 : ℕ) : ℝ) = ((8 : ℕ) : ENNReal) by
                rw [ENNReal.ofReal_natCast]]
        rw [h_ofReal_eq]
        have h_pow_4ρ_eq :
            (((8 : NNReal) * ρ k.succ : NNReal) : ENNReal) ^ (n_dim - 1) =
              (8 : ENNReal) ^ (n_dim - 1) * (ρ k.succ : ENNReal) ^ (n_dim - 1) := by
          push_cast
          rw [mul_pow]
        rw [h_pow_4ρ_eq]
        rw [ENNReal.le_div_iff_mul_le
              (Or.inl (mul_ne_zero h_vol_C_ne_zero (mul_ne_zero h_4_pow_ne_zero h_ρ_pow_ne_zero)))
              (Or.inl (ENNReal.mul_ne_top h_vol_C_ne_top
                (ENNReal.mul_ne_top h_4_pow_ne_top h_ρ_pow_ne_top)))]
        have h_LHS_simp :
            (Tube.le_volume.c n_dim : ENNReal) /
                  (Tube.volume_le.C n_dim : ENNReal) /
                  ((8 : ENNReal) ^ (n_dim - 1)) *
                ((Tube.volume_le.C n_dim : ENNReal) *
                  ((8 : ENNReal) ^ (n_dim - 1) * (ρ k.succ : ENNReal) ^ (n_dim - 1))) =
            (Tube.le_volume.c n_dim : ENNReal) * (ρ k.succ : ENNReal) ^ (n_dim - 1) := by
          rw [show (Tube.volume_le.C n_dim : ENNReal) *
                ((8 : ENNReal) ^ (n_dim - 1) * (ρ k.succ : ENNReal) ^ (n_dim - 1)) =
                ((Tube.volume_le.C n_dim : ENNReal) * (8 : ENNReal) ^ (n_dim - 1)) *
                  (ρ k.succ : ENNReal) ^ (n_dim - 1) from by
              rw [mul_assoc]]
          rw [← mul_assoc]
          rw [show (Tube.volume_le.C n_dim : ENNReal) * (8 : ENNReal) ^ (n_dim - 1) =
                ((8 : ENNReal) ^ (n_dim - 1)) * (Tube.volume_le.C n_dim : ENNReal) from
              mul_comm _ _]
          rw [← mul_assoc]
          rw [ENNReal.div_mul_cancel h_4_pow_ne_zero h_4_pow_ne_top]
          rw [ENNReal.div_mul_cancel h_vol_C_ne_zero h_vol_C_ne_top]
        rw [mul_right_comm _ (ENNReal.ofReal ((δ : ℝ) ^ ε / K_cnt ^ M)) _]
        rw [h_LHS_simp]
        rw [show (F_A.card : ENNReal) *
              ((Tube.le_volume.c n_dim : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) =
              (Tube.le_volume.c n_dim : ENNReal) *
                ((F_A.card : ENNReal) * (δ : ENNReal) ^ (n_dim - 1)) by ring]
        rw [mul_assoc]
        exact mul_le_mul_right h_count_LB _
      have hδ_le_one_NN : δ ≤ (1 : NNReal) := by
        have := hρ_anti.antitone (Fin.zero_le (Fin.last M))
        rw [hρ_0, hρ_M] at this; exact this
      have hδ_le_one_real : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ_le_one_NN
      have h_inSlack_pos : 0 < (δ : ℝ) ^ ε / K_cnt ^ M :=
        div_pos (Real.rpow_pos_of_pos hδ_pos_real _) (pow_pos hK_cnt_pos M)
      have h_inSlack_le_one : (δ : ℝ) ^ ε / K_cnt ^ M ≤ 1 := by
        rw [div_le_one (pow_pos hK_cnt_pos M)]
        calc (δ : ℝ) ^ ε ≤ 1 := Real.rpow_le_one hδ_pos_real.le hδ_le_one_real hε.le
          _ ≤ K_cnt ^ M := one_le_pow₀ hK_cnt_ge_one
      exact Kakeya.StickyKakeya.anchor_densityIn_ge_of_discrete
        M hM δ hδ_pos ρ hρ_anti hρ_0 hρ_M T' s'
        (8 : NNReal) (by norm_num : (1 : NNReal) ≤ 8)
        max_ratio_n h_max_ratio_n_pos h_max_ratio_bound
        ((δ : ℝ) ^ ε / K_cnt ^ M) h_inSlack_pos h_inSlack_le_one h_disc
    have clause1_nonempty : s'.Nonempty := by
      rw [hs'_def]
      exact (h_nonempty_at _).image _
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact clause1_nonempty
    · intro p hp
      rw [hs'_def, Finset.mem_image] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      have hq_inv := h_invariant (Fin.last M) q hq
      have hq_leaf := (hLeafChoice_spec q hq).1
      subst hqp
      exact Finset.mem_product.mpr ⟨hq_leaf, hq_inv.2⟩
    · intro p hp
      rw [hs'_def, Finset.mem_image] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      have hq_leaf := (hLeafChoice_spec q hq).1
      subst hqp
      exact hq_leaf
    · intro p hp
      rw [hs'_def, Finset.mem_image] at hp
      obtain ⟨q, hq, hqp⟩ := hp
      have hq_inv := h_invariant (Fin.last M) q hq
      have hq_leaf := (hLeafChoice_spec q hq).1
      have hq2_norm : ‖q.2‖ ≤ (M : ℝ) := by
        have := hR_partial_norm (Fin.last M) q.2 hq_inv.2
        simpa [Fin.val_last] using this
      have hTl_ball : (T (leafChoice q)).carrier ⊆ Metric.closedBall (0 : E) 1 :=
        hT_in_unit _ hq_leaf
      subst hqp
      intro x hx
      have hx' : ∃ y ∈ (T (leafChoice q)).carrier, q.2 + y = x := by
        change x ∈ (q.2 + ·) '' (T (leafChoice q)).carrier at hx
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, hxy⟩
      obtain ⟨y, hy_in, hy_eq⟩ := hx'
      have hy_ball := hTl_ball hy_in
      rw [Metric.mem_closedBall, dist_zero_right] at hy_ball
      rw [Metric.mem_closedBall, dist_zero_right, ← hy_eq]
      have hadd := norm_add_le q.2 y
      linarith
    · exact clause6_anchor_density
    · exact ⟨σ, s'_at,
        (fun k p => (((h_uni k).parentTube p.1).rescale (σ k)).translate p.2), proj,
        hσ_0_ge_one, hσ_0_le_four, hσ_last, hσ_anti, hσ_gap, hproj_mem, hproj_le,
        Q_count_nodes, Q_in_ball_nodes, Q_ne_nodes,
        cover_nodes, cover_nodes_mem, cover_nodes_body, cover_nodes_inj, Q_KT_nodes⟩
  obtain ⟨σ, Q, tb, proj, hσ_0_ge_one, hσ_0_le_four, hσ_last, hσ_anti, hσ_gap,
          hproj_mem, hproj_le, hQ_count, hQ_in_ball, hQ_ne,
          cover, hcover_mem, hcover_body, hcover_inj, hQ_KT⟩ := h_paper_kt
  have hs'_T_in_ball_R : ∀ p ∈ s', (T' p).carrier ⊆ Metric.closedBall (0 : E) R := fun p hp =>
    (hs'_T_in_ball p hp).trans (Metric.closedBall_subset_closedBall
      (by rw [hR_def]; linarith))
  have h_md_le := h_md_template hδ_pos hδ_le_one_real s' T' hs'_T_in_ball_R M hM σ
    hσ_0_ge_one hσ_0_le_four hσ_last hσ_anti (fun m => by exact_mod_cast hσ_gap m)
    tb Q proj hproj_mem hproj_le
    hQ_count hQ_in_ball hQ_ne cover hcover_mem hcover_body hcover_inj Δ hΔ_top
    (fun m : Fin M => fun (p : ι × E) (hp : p ∈ Q m.castSucc) => by
      convert hQ_KT m p hp)
  have h_s'_Frostman_and_md :
      IsFrostmanAtEveryScale (E := E) s' T'
        (ENNReal.ofReal ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε))) ∧
      Kakeya.maxDensity s' (fun p : ι × E => (T' p).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε))) := by
    classical
    set n := Module.finrank ℝ E with hn_def
    have hδ_real_nonneg : (0 : ℝ) ≤ (δ : ℝ) := hδ_pos_real.le
    have hρ_le_δ : ∀ k : Fin (M+1), δ ≤ ρ k := by
      intro k
      have h1 : ρ (Fin.last M) ≤ ρ k := hρ_anti.antitone (Fin.le_last k)
      rw [hρ_M] at h1; exact h1
    have hρ_pos : ∀ k : Fin (M+1), (0 : ℝ) < (ρ k : ℝ) := by
      intro k
      have h1 : δ ≤ ρ k := hρ_le_δ k
      have h2 : (δ : ℝ) ≤ (ρ k : ℝ) := by exact_mod_cast h1
      linarith
    have hρ_nonneg : ∀ k : Fin (M+1), (0 : ℝ) ≤ (ρ k : ℝ) := fun k => (hρ_pos k).le
    have h_telescope :
        ∀ {N : ℕ} (g : Fin (N+1) → ℝ), (∀ k, 0 < g k) →
          (∏ m : Fin N, g m.castSucc / g m.succ) = g 0 / g (Fin.last N) := by
      intro N
      induction N with
      | zero =>
        intro g hg
        simp only [Fin.prod_univ_zero, Fin.last_zero]
        exact (div_self (hg 0).ne').symm
      | succ N ih =>
        intro g hg
        rw [Fin.prod_univ_castSucc]
        have hgcast : ∀ k : Fin (N+1), 0 < (g ∘ Fin.castSucc) k := fun k => hg _
        have hih := ih (g ∘ Fin.castSucc) hgcast
        have h_inner_eq :
            (∏ m : Fin N, g m.castSucc.castSucc / g m.castSucc.succ)
              = (∏ m : Fin N, g (m.castSucc.castSucc) / g (m.succ.castSucc)) := by
          refine Finset.prod_congr rfl ?_
          intro m _
          rw [show m.castSucc.succ = m.succ.castSucc from
            (Fin.castSucc_succ m).symm]
        rw [h_inner_eq]
        have h_inner_eq2 :
            (∏ m : Fin N, g (m.castSucc.castSucc) / g (m.succ.castSucc))
              = (g ∘ Fin.castSucc) 0 / (g ∘ Fin.castSucc) (Fin.last N) := by
          have : (∏ m : Fin N,
                    (g ∘ Fin.castSucc) m.castSucc / (g ∘ Fin.castSucc) m.succ)
                  = (g ∘ Fin.castSucc) 0 / (g ∘ Fin.castSucc) (Fin.last N) := hih
          simpa [Function.comp_def] using this
        rw [h_inner_eq2]
        have hlast_succ_eq : (Fin.last N).succ = Fin.last (N+1) := Fin.succ_last N
        have hgcs_ne : g (Fin.last N).castSucc ≠ 0 := (hg _).ne'
        have hgsc_ne : g (Fin.last N).succ ≠ 0 := (hg _).ne'
        have h_eq : (g 0 / g ((Fin.last N).castSucc)) *
                (g (Fin.last N).castSucc / g (Fin.last N).succ)
            = g 0 / g (Fin.last (N+1)) := by
          rw [← hlast_succ_eq]
          field_simp
        simpa [Function.comp_def] using h_eq
    set ρ_real : Fin (M+1) → ℝ := fun k => (ρ k : ℝ) with hρ_real_def
    have hρ_real_pos : ∀ k, 0 < ρ_real k := fun k => hρ_pos k
    have h_tele : (∏ m : Fin M, ρ_real m.castSucc / ρ_real m.succ)
                  = ρ_real 0 / ρ_real (Fin.last M) := h_telescope ρ_real hρ_real_pos
    have hρ0_real : ρ_real 0 = 1 := by simp [hρ_real_def, hρ_0]
    have hρM_real : ρ_real (Fin.last M) = (δ : ℝ) := by simp [hρ_real_def, hρ_M]
    rw [hρ0_real, hρM_real] at h_tele
    have hfactor_nonneg : ∀ m : Fin M,
        0 ≤ K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
              ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε := by
      intro m
      have h1 : (0 : ℝ) ≤ K_53_KT := hK_53_KT_pos.le
      have h2 : (0 : ℝ) ≤ (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
        Real.rpow_nonneg hδ_real_nonneg _
      have h3 : (0 : ℝ) ≤ ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε := by
        have hbase : 0 ≤ (ρ m.castSucc : ℝ) / (ρ m.succ : ℝ) :=
          div_nonneg (hρ_nonneg _) (hρ_nonneg _)
        exact Real.rpow_nonneg hbase _
      positivity
    have h_prod_ofReal :
        (∏ m : Fin M, Δ m) =
          ENNReal.ofReal (∏ m : Fin M,
              K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε) := by
      rw [hΔ_def]
      symm
      apply ENNReal.ofReal_prod_of_nonneg
      intro m _
      exact hfactor_nonneg m
    have h_prod_eq :
        (∏ m : Fin M,
              K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε)
          = K_53_KT ^ M * ((δ : ℝ) ^ (-(ε / (M : ℝ)))) ^ M *
              (∏ m : Fin M, ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε) := by
      have step1 :
          (∏ m : Fin M,
                K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                  ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε)
            = (∏ m : Fin M, K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ)))) *
                  (∏ m : Fin M, ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε) := by
        rw [← Finset.prod_mul_distrib]
      rw [step1]
      have step2 : (∏ _ : Fin M, K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))))
                    = (K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ)))) ^ M := by
        simp
      rw [step2]
      ring
    have h_pow_collapse :
        ((δ : ℝ) ^ (-(ε / (M : ℝ)))) ^ M = (δ : ℝ) ^ (-ε) := by
      have hMnat_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
      have : ((δ : ℝ) ^ (-(ε / (M : ℝ)))) ^ M
              = (δ : ℝ) ^ ((-(ε / (M : ℝ))) * (M : ℝ)) := by
        rw [← Real.rpow_mul_natCast hδ_real_nonneg]
      rw [this]
      congr 1
      field_simp
    have h_telescoped_pow :
        (∏ m : Fin M, ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε)
          = (1 / (δ : ℝ)) ^ ε := by
      rw [Real.finsetProd_rpow]
      · rw [h_tele]
      · intro m _
        exact div_nonneg (hρ_nonneg _) (hρ_nonneg _)
    have h_one_div_delta : ((1 : ℝ) / (δ : ℝ)) ^ ε = (δ : ℝ) ^ (-ε) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul hδ_real_nonneg]
      ring_nf
    rw [h_one_div_delta] at h_telescoped_pow
    rw [h_pow_collapse, h_telescoped_pow] at h_prod_eq
    have h_two_eps : (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-ε) = (δ : ℝ) ^ (-(2 * ε)) := by
      rw [← Real.rpow_add hδ_pos_real]; congr 1; ring
    have h_prod_final :
        (∏ m : Fin M,
              K_53_KT * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ m.castSucc : ℝ) / (ρ m.succ : ℝ)) ^ ε)
          = K_53_KT ^ M * (δ : ℝ) ^ (-(2 * ε)) := by
      rw [h_prod_eq, mul_assoc, h_two_eps]
    set W : ι × E → ConvexSpaceBody E := fun p => (T' p).toConvexSpaceBody with hW_def
    have h_md_le' :
        (Kakeya.maxDensity s' W).toReal
          ≤ (C_7_4 * K_53_KT) ^ M * (δ : ℝ) ^ (-(2 * ε)) := by
      refine ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (pow_nonneg h_factor_pos.le _) (Real.rpow_nonneg hδ_real_nonneg _)) ?_
      refine h_md_le.trans (le_of_eq ?_)
      rw [h_prod_ofReal, h_prod_final, ← ENNReal.ofReal_pow hC_7_4_pos.le,
        ← ENNReal.ofReal_mul (pow_nonneg hC_7_4_pos.le M)]
      congr 1
      rw [mul_pow]; ring
    have h_md_le_final_real :
        (Kakeya.maxDensity s' W).toReal ≤ (δ : ℝ) ^ (-(((n : ℝ) + 3) * ε)) :=
      h_md_le'.trans hδ_small
    have h_md_ne_top : Kakeya.maxDensity s' W ≠ ⊤ :=
      Kakeya.maxDensity_ne_top s' W
    have h_md_le_ENN :
        Kakeya.maxDensity s' W ≤
          ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε))) := by
      rw [← ENNReal.ofReal_toReal h_md_ne_top]
      exact ENNReal.ofReal_le_ofReal h_md_le_final_real
    refine ⟨?_, h_md_le_ENN⟩
    have h_exp_eq :
        (δ : ℝ) ^ (-((n : ℝ) + 3) * ε)
          = (δ : ℝ) ^ (-(((n : ℝ) + 3) * ε)) := by
      congr 1; ring
    rw [h_exp_eq]
    rw [IsFrostmanAtEveryScale_def]
    intro ρ_anchor hρ_anchor_ge hρ_anchor_le p₀ hp₀
    set F : Finset (ι × E) :=
      s'.filter (fun p : ι × E =>
        (T' p).toConvexSpaceBody ≤
          (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody)
      with hF_def
    set K_anchor : ConvexSpaceBody E :=
      (Tube.rescale (T' p₀) ρ_anchor).toConvexSpaceBody
      with hK_anchor_def
    have hF_sub : F ⊆ s' := Finset.filter_subset _ _
    have hmaxF_le :
        Kakeya.maxDensity F W ≤ Kakeya.maxDensity s' W :=
      Kakeya.maxDensity_mono W hF_sub
    have hmaxF_le_C :
        Kakeya.maxDensity F W ≤
          ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε))) :=
      hmaxF_le.trans h_md_le_ENN
    refine ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le ?_
    set K_inv_n : ℝ :=
      (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
        (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hK_inv_n_def
    set max_ratio_n : ℝ :=
      (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) with hmax_ratio_n_def
    set max_ratio_n_C : ℝ :=
      max_ratio_n * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) with hmax_ratio_n_C_def
    set inSlack_n : ℝ := (δ : ℝ) ^ ε / K_cnt ^ M with hinSlack_n_def
    have h_anchor :
        ENNReal.ofReal (K_inv_n ^ 2 * inSlack_n / max_ratio_n_C)
          ≤ Kakeya.densityIn F W K_anchor :=
      h_anchor_density ρ_anchor hρ_anchor_ge hρ_anchor_le p₀ hp₀
    have h_8_pow_pos : (0 : ℝ) < (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) := by positivity
    have hmaxF_le_C_sharp :
        Kakeya.maxDensity F W ≤
          ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε))) *
            ENNReal.ofReal (K_inv_n ^ 2 * inSlack_n / max_ratio_n_C) := by
      have hK_eq : K_inv_n = K_inv_n_outer := rfl
      have h_md_le_sharp_real :
          (Kakeya.maxDensity s' W).toReal
            ≤ K_inv_n ^ 2 /
                (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
                (δ : ℝ) ^ (-(3 * ε)) := by
        rw [hK_eq]; exact h_md_le'.trans hδ_small_sharp
      have h_md_le_sharp_ENN :
          Kakeya.maxDensity s' W
            ≤ ENNReal.ofReal (K_inv_n ^ 2 /
                (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
                  (δ : ℝ) ^ (-(3 * ε))) := by
        rw [← ENNReal.ofReal_toReal h_md_ne_top]
        exact ENNReal.ofReal_le_ofReal h_md_le_sharp_real
      have hmaxF_le_sharp_ENN :
          Kakeya.maxDensity F W
            ≤ ENNReal.ofReal (K_inv_n ^ 2 /
                (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
                  (δ : ℝ) ^ (-(3 * ε))) :=
        hmaxF_le.trans h_md_le_sharp_ENN
      have h_algebra :
          K_inv_n ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
              (δ : ℝ) ^ (-(3 * ε))
            = (δ : ℝ) ^ (-(((n : ℝ) + 3) * ε)) *
              (K_inv_n ^ 2 * inSlack_n / max_ratio_n_C) := by
        rw [hmax_ratio_n_C_def, hmax_ratio_n_def, hinSlack_n_def, hn_def]
        have h_K53M_ne : K_cnt ^ M ≠ 0 := (pow_pos hK_cnt_pos M).ne'
        have hP_ne : (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1)) ≠ 0 := h_8_pow_pos.ne'
        have hMr_ne : (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) ≠ 0 :=
          (Real.rpow_pos_of_pos hδ_pos_real _).ne'
        have h_pow_frac :
            (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε)) * (δ : ℝ) ^ ε /
                (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε)
              = (δ : ℝ) ^ (-(3 * ε)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hδ_pos_real.le,
            ← Real.rpow_add hδ_pos_real, ← Real.rpow_add hδ_pos_real]
          congr 1; ring
        rw [show (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε)) *
              (K_inv_n ^ 2 * ((δ : ℝ) ^ ε / K_cnt ^ M) /
                ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε) *
                  (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))))
            = K_inv_n ^ 2 /
                (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
              ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε)) * (δ : ℝ) ^ ε /
                (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε)) from by
            field_simp]
        rw [h_pow_frac]
      have h_factor1_nonneg : 0 ≤ (δ : ℝ) ^ (-(((n : ℝ) + 3) * ε)) :=
        Real.rpow_nonneg hδ_pos_real.le _
      calc Kakeya.maxDensity F W
          ≤ ENNReal.ofReal (K_inv_n ^ 2 /
              (K_cnt ^ M * (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))) *
                (δ : ℝ) ^ (-(3 * ε))) := hmaxF_le_sharp_ENN
        _ = ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε)) *
              (K_inv_n ^ 2 * inSlack_n / max_ratio_n_C)) := by rw [h_algebra]
        _ = ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε))) *
              ENNReal.ofReal (K_inv_n ^ 2 * inSlack_n / max_ratio_n_C) :=
            ENNReal.ofReal_mul h_factor1_nonneg
    calc Kakeya.maxDensity F W
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε))) *
            ENNReal.ofReal (K_inv_n ^ 2 * inSlack_n / max_ratio_n_C) := hmaxF_le_C_sharp
      _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(((n : ℝ) + 3) * ε))) *
            Kakeya.densityIn F W K_anchor :=
          mul_le_mul_of_nonneg_left h_anchor bot_le
  obtain ⟨h_s'_Frostman, h_md_clean⟩ := h_s'_Frostman_and_md
  refine ⟨C_card,
    (δ : ℝ) ^ ε * (s.card : ℝ) * ((R_partial (Fin.last M)).card : ℝ),
    R_partial (Fin.last M), R_per, R_partial, s',
    hR_total_nonempty, hs'_sub, hR_total_card, hC_card_le2,
    hR_partial_zero, hR_partial_succ, rfl, hs'_nonempty, h_s'_Frostman,
    ?_, ?_, hs'_T_in_ball, ⟨K_cnt, hK_cnt_ge_one, h_anchor_density⟩, h_md_clean⟩
  · have hδ_pow_pos_ε : 0 < (δ : ℝ) ^ ε :=
      Real.rpow_pos_of_pos hδ_pos_real _
    have hs_card_pos : 0 < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs_nonempty
    have hR_card_pos : 0 < ((R_partial (Fin.last M)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hR_total_nonempty
    exact mul_pos (mul_pos hδ_pow_pos_ε hs_card_pos) hR_card_pos
  · have hδ_pow_nn : (0 : ℝ) ≤ (δ : ℝ) ^ ε :=
      Real.rpow_nonneg hδ_pos_real.le _
    have hs_card_nn : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    have hR_card_nn : (0 : ℝ) ≤ ((R_partial (Fin.last M)).card : ℝ) :=
      Nat.cast_nonneg _
    have hC_s'_nn : (0 : ℝ) ≤
        (δ : ℝ) ^ ε * (s.card : ℝ) * ((R_partial (Fin.last M)).card : ℝ) :=
      mul_nonneg (mul_nonneg hδ_pow_nn hs_card_nn) hR_card_nn
    have hs'_card_ge_one : (1 : ℝ) ≤ (s'.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs'_nonempty
    calc (δ : ℝ) ^ ε * (s.card : ℝ) * ((R_partial (Fin.last M)).card : ℝ)
        = ((δ : ℝ) ^ ε * (s.card : ℝ) *
              ((R_partial (Fin.last M)).card : ℝ)) * 1 :=
          (mul_one _).symm
      _ ≤ ((δ : ℝ) ^ ε * (s.card : ℝ) *
              ((R_partial (Fin.last M)).card : ℝ)) * (s'.card : ℝ) :=
          mul_le_mul_of_nonneg_left hs'_card_ge_one hC_s'_nn
end StickyKakeya

end Kakeya
