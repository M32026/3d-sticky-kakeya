/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.Multiplicity
public import Kakeya.RandomTranslation.Erosion
public import Kakeya.RandomTranslation.SampleDistinct
public import Kakeya.RandomTranslation.TranslationRefinement
public import Kakeya.RandomTranslation.TranslationRefinementJoint
public import Kakeya.Shading
public import Kakeya.StickyKakeya.Lemma75.Calibration
public import Kakeya.Tube.Basic
public import Kakeya.Uniform

/-!
# GWZ Lemma 7.5, part 1: the per-scale `Δ_max` bound

`Kakeya.StickyKakeya.subStickyFrostmanLemma.perScaleDeltaMax` (paper `section7.tex` eq. (52)–(54)):
at each scale of the chain, the `R`-translated children family satisfies a `Δ_max` bound with the
paper-faithful constant `K_53`.  The two helpers above it are the packing estimate that feeds the
bound and the closed form of that constant.
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

/-- Analytic helper for `subStickyFrostmanLemma.perScaleDeltaMax`: for `K > 0`, `n : ℕ` and `c > 0`,
the logarithm `log(2 K (2/δ)^{2n} + 4)` is eventually dominated by `δ^{-c}` as `δ → 0⁺` in
`NNReal`.  This is the log-vs-rpow domination that discharges the per-parent union-bound budget
after the ED packing bound `|parent| ≤ C_crude · (2/δ)^{2n}`. -/
private lemma subStickyFrostmanLemma.perScaleDeltaMax.packingLogBound
    (K : ℝ) (hK : 0 < K) (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Real.log (2 * K * (2 / (δ : ℝ)) ^ (2 * n) + 4) ≤ (δ : ℝ) ^ (-c) := by
  have hAtTop : ∀ᶠ y : ℝ in Filter.atTop,
      Real.log (2 * K * (2 * y) ^ (2 * n) + 4) ≤ y ^ c := by
    have hloglim : Filter.Tendsto (fun y : ℝ => Real.log y / y ^ c)
        Filter.atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero
    set D : ℝ := 2 * K * 2 ^ (2 * n) + 4 with hD_def
    have hD_pos : 0 < D := by
      have hpow_pos : (0 : ℝ) < 2 ^ (2 * n) := by positivity
      have h1 : 0 < 2 * K * 2 ^ (2 * n) := by positivity
      linarith
    have hbound : ∀ᶠ y : ℝ in Filter.atTop,
        Real.log (2 * K * (2 * y) ^ (2 * n) + 4) ≤
          Real.log D + ((2 * n + 1 : ℕ) : ℝ) * Real.log y := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
      have hy_pos : 0 < y := lt_of_lt_of_le one_pos hy
      have hy2n_pos : 0 < y ^ (2 * n) := by positivity
      have hy2n_le : y ^ (2 * n) ≤ y ^ (2 * n + 1) := by
        calc y ^ (2 * n) = y ^ (2 * n) * 1 := (mul_one _).symm
          _ ≤ y ^ (2 * n) * y := by nlinarith [hy2n_pos]
          _ = y ^ (2 * n + 1) := by ring
      have hy2n1_ge_one : (1 : ℝ) ≤ y ^ (2 * n + 1) := one_le_pow₀ hy
      have h4_le : (4 : ℝ) ≤ 4 * y ^ (2 * n + 1) := by nlinarith
      have h2yexpand : (2 * y) ^ (2 * n) = 2 ^ (2 * n) * y ^ (2 * n) := mul_pow _ _ _
      have hpoly_pos : 0 < 2 * K * (2 * y) ^ (2 * n) + 4 := by
        have : 0 < 2 * K * (2 * y) ^ (2 * n) := by
          rw [h2yexpand]; positivity
        linarith
      have hD_yk_pos : 0 < D * y ^ (2 * n + 1) := by positivity
      have hineq : 2 * K * (2 * y) ^ (2 * n) + 4 ≤ D * y ^ (2 * n + 1) := by
        have hKpow_nn : 0 ≤ 2 * K * 2 ^ (2 * n) := by positivity
        have h1 : 2 * K * 2 ^ (2 * n) * y ^ (2 * n)
            ≤ 2 * K * 2 ^ (2 * n) * y ^ (2 * n + 1) :=
          mul_le_mul_of_nonneg_left hy2n_le hKpow_nn
        have hrew : 2 * K * (2 * y) ^ (2 * n)
            = 2 * K * 2 ^ (2 * n) * y ^ (2 * n) := by
          rw [h2yexpand]; ring
        have heq : 2 * K * 2 ^ (2 * n) * y ^ (2 * n + 1) + 4 * y ^ (2 * n + 1)
            = D * y ^ (2 * n + 1) := by
          simp only [hD_def]; ring
        linarith
      have hlog_mono : Real.log (2 * K * (2 * y) ^ (2 * n) + 4) ≤
          Real.log (D * y ^ (2 * n + 1)) := Real.log_le_log hpoly_pos hineq
      have hlog_prod : Real.log (D * y ^ (2 * n + 1))
          = Real.log D + ((2 * n + 1 : ℕ) : ℝ) * Real.log y := by
        rw [Real.log_mul hD_pos.ne' (by positivity), Real.log_pow]
      linarith
    have hlowbound : ∀ᶠ y : ℝ in Filter.atTop,
        (0 : ℝ) ≤ Real.log (2 * K * (2 * y) ^ (2 * n) + 4) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
      have hy_pos : 0 < y := lt_of_lt_of_le one_pos hy
      have hKpos : 0 < 2 * K * (2 * y) ^ (2 * n) := by positivity
      have h1 : 1 ≤ 2 * K * (2 * y) ^ (2 * n) + 4 := by linarith
      exact Real.log_nonneg h1
    have hRHS_tend : Filter.Tendsto
        (fun y : ℝ => (Real.log D + ((2 * n + 1 : ℕ) : ℝ) * Real.log y) / y ^ c)
        Filter.atTop (nhds 0) := by
      have hyc : Filter.Tendsto (fun y : ℝ => y ^ c) Filter.atTop Filter.atTop :=
        tendsto_rpow_atTop hc
      have hinv : Filter.Tendsto (fun y : ℝ => (y ^ c)⁻¹) Filter.atTop (nhds 0) := by
        have h := hyc.inv_tendsto_atTop
        simpa [Pi.inv_def] using h
      have h1 : Filter.Tendsto (fun y : ℝ => Real.log D / y ^ c)
          Filter.atTop (nhds 0) := by
        have h0' : Filter.Tendsto (fun y : ℝ => Real.log D * (y ^ c)⁻¹)
            Filter.atTop (nhds (Real.log D * 0)) := hinv.const_mul (Real.log D)
        simpa [mul_zero, div_eq_mul_inv] using h0'
      have h2 : Filter.Tendsto
          (fun y : ℝ => ((2 * n + 1 : ℕ) : ℝ) * Real.log y / y ^ c)
          Filter.atTop (nhds 0) := by
        have h2a : Filter.Tendsto
            (fun y : ℝ => ((2 * n + 1 : ℕ) : ℝ) * (Real.log y / y ^ c))
            Filter.atTop (nhds (((2 * n + 1 : ℕ) : ℝ) * 0)) :=
          hloglim.const_mul _
        simpa [mul_zero, mul_div_assoc] using h2a
      have hsum : Filter.Tendsto
          (fun y : ℝ => Real.log D / y ^ c +
            ((2 * n + 1 : ℕ) : ℝ) * Real.log y / y ^ c)
          Filter.atTop (nhds (0 + 0)) := h1.add h2
      have hrew : (fun y : ℝ =>
          (Real.log D + ((2 * n + 1 : ℕ) : ℝ) * Real.log y) / y ^ c)
          = (fun y : ℝ => Real.log D / y ^ c
              + ((2 * n + 1 : ℕ) : ℝ) * Real.log y / y ^ c) := by
        funext y; ring
      rw [hrew]; simpa using hsum
    have htend : Filter.Tendsto
        (fun y : ℝ => Real.log (2 * K * (2 * y) ^ (2 * n) + 4) / y ^ c)
        Filter.atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          Filter.atTop (nhds 0))
        hRHS_tend ?_ ?_
      · filter_upwards [hlowbound, Filter.eventually_gt_atTop (0 : ℝ)]
          with y hlb hy_pos
        have hyc_pos : 0 < y ^ c := Real.rpow_pos_of_pos hy_pos c
        exact div_nonneg hlb hyc_pos.le
      · filter_upwards [hbound, Filter.eventually_gt_atTop (0 : ℝ)]
          with y hb hy_pos
        have hyc_pos : 0 < y ^ c := Real.rpow_pos_of_pos hy_pos c
        exact div_le_div_of_nonneg_right hb hyc_pos.le
    rw [Metric.tendsto_nhds] at htend
    have htend1 := htend 1 (by norm_num)
    filter_upwards [htend1, hlowbound, Filter.eventually_gt_atTop (0 : ℝ)]
      with y hy hlb hy_pos
    have hyc_pos : 0 < y ^ c := Real.rpow_pos_of_pos hy_pos c
    rw [Real.dist_eq, sub_zero] at hy
    have habs : |Real.log (2 * K * (2 * y) ^ (2 * n) + 4) / y ^ c| < 1 := hy
    rw [abs_div, abs_of_pos hyc_pos] at habs
    have habs' : |Real.log (2 * K * (2 * y) ^ (2 * n) + 4)| < 1 * y ^ c := by
      rw [div_lt_iff₀ hyc_pos] at habs; exact habs
    have habs'' : |Real.log (2 * K * (2 * y) ^ (2 * n) + 4)| ≤ y ^ c := by
      simpa [one_mul] using habs'.le
    exact (le_abs_self _).trans habs''
  have hInv : Filter.Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] (0 : ℝ)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hRealEv : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      Real.log (2 * K * (2 * x⁻¹) ^ (2 * n) + 4) ≤ x⁻¹ ^ c :=
    hInv.eventually hAtTop
  have hReal : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      Real.log (2 * K * (2 / x) ^ (2 * n) + 4) ≤ x ^ (-c) := by
    filter_upwards [hRealEv] with x hx
    have h_two_div : (2 : ℝ) * x⁻¹ = 2 / x := by
      rw [div_eq_mul_inv, mul_comm]
    have h_rpow : x⁻¹ ^ c = x ^ (-c) := (Real.rpow_neg_eq_inv_rpow x c).symm
    rw [h_two_div, h_rpow] at hx
    exact hx
  have hmap : (𝓝[>] (0 : NNReal)).map ((↑) : NNReal → ℝ) = 𝓝[>] (0 : ℝ) := by
    have h := NNReal.map_coe_nhdsGT (0 : NNReal)
    rw [NNReal.coe_zero] at h
    exact h
  have hPullback : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Real.log (2 * K * (2 / ((δ : ℝ))) ^ (2 * n) + 4) ≤ (δ : ℝ) ^ (-c) := by
    rw [← hmap] at hReal
    exact hReal
  exact hPullback

/-- Paper-faithful closed form of the per-scale density-band constant `K_53` (paper L143-144,
Lemma 7.5 eq. (53)): `K_53 := 1 + Cε · (1 + max 1 K_vol)`, built from the refinement slack constant
`Cε` and the dimension-only volume ratio `K_vol = c_up / c_low`.  The `1+` floor gives positivity
and `max 1 K_vol` folds the low-dimensional corner case into the same formula. -/
private noncomputable def subStickyFrostmanLemma.perScaleDeltaMax.K_53_form
    (n : ℕ) (Cε : ℝ) : ℝ := 1 + Cε * (1 + max 1
    ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)))

/-- `K_53_form n Cε ≥ 1` whenever `Cε ≥ 0`. This is immediate from the
closed form `K_53_form n Cε = 1 + Cε · (1 + max 1 (...))`. -/
private lemma subStickyFrostmanLemma.perScaleDeltaMax.K_53_form_ge_one
    (n : ℕ) (Cε : ℝ) (hCε : 0 ≤ Cε) :
    1 ≤ subStickyFrostmanLemma.perScaleDeltaMax.K_53_form n Cε := by
  unfold subStickyFrostmanLemma.perScaleDeltaMax.K_53_form
  have hmax : (1 : ℝ) ≤ max 1
      ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) := le_max_left _ _
  have h_mul_nn : 0 ≤ Cε * (1 + max 1
      ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))) :=
    mul_nonneg hCε (by linarith)
  linarith

set_option linter.style.setOption false in
open scoped Classical in
set_option maxHeartbeats 1200000 in
-- Six-fold heartbeat bump: the joint random-translation calibration 1 block (R4) inside
-- `hR_construction` builds a chain of `linarith`/`calc` steps over a heavy
-- elaboration context (joint refinement body + Tube ENNReal/Real volume bands +
-- `K_53_form` unfold), pushing the default 200000 ceiling.
/-- **Part 1 of GWZ Lemma 7.5** (paper section7.tex eq. (52)–(54), L128–L145): the per-scale `Δ_max`
bound on the `R`-translated children family.  From per-scale `Tube.IsUniformAtScale` witnesses along
`ρ_0 = 1 > … > ρ_M = δ` and the anchored input `Δ_max(TT_{ρ_k}[T_{ρ_{k-1}}]) ≤ (ρ_{k-1}/ρ_k)^ε` it
produces per-scale translation sets `R k` of norm `≤ ρ_{k.castSucc}`, of two-sided cardinality
`∼ max{1, (ρ_{k.castSucc}/ρ_{k.succ})^{n-1} / N₂ k}`, satisfying eq. (53) at the constant `K_53`. -/
theorem subStickyFrostmanLemma.perScaleDeltaMax
    (ε : ℝ) (hε : 0 < ε) (M : ℕ) (hM : 1 ≤ M)
    (C_box : ℝ) (hC_box_pos : 0 < C_box)
    (Cn : ℝ) (hCn_ge_one : 1 ≤ Cn) :
    ∃ K_53 C_R c_R : ℝ, 1 ≤ K_53 ∧ 0 < c_R ∧ 0 < C_R ∧ C_R ≤ 2 ∧
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      ∀ {ι : Type} (s : Finset ι),
      ∀ (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (ρ : Fin (M + 1) → NNReal),
        ρ 0 ≤ 1 → ρ (Fin.last M) = δ → StrictAnti ρ →
        (∀ k : Fin M, (δ : ℝ) ^ ε ≤ (ρ k.succ : ℝ) / (ρ k.castSucc : ℝ)) →
      ∀ (Cu : NNReal)
        (u : ∀ k : Fin (M + 1), Tube.IsUniformAtScale s T (ρ k) Cu),
        (∀ k : Fin (M + 1), ∀ j ∈ (u k).parent,
            ((u k).parentTube j).carrier ⊆ Metric.closedBall (0 : E) 4) →
        (∀ k : Fin M,
            ((u k.castSucc).parent.card : ℝ)
              ≤ C_box * ((4 : ℝ) / (ρ k.castSucc : ℝ)) ^ (2 * Module.finrank ℝ E)) →
      ∀ (P : Fin (M + 1) → Finset ι),
        (∀ k : Fin (M + 1), P k ⊆ (u k).parent) →
      ∀ (N₂ : Fin M → ℕ),
        (∀ k : Fin M, 0 < N₂ k) →
        (∀ k : Fin M,
          ∀ j ∈ P k.castSucc,
            (N₂ k : ℝ) ≤ Cn *
              (((P k.succ).filter (fun i : ι =>
                ((u k.succ).parentTube i).toConvexSpaceBody ≤
                  ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)) →
        (∀ k : Fin M,
          ∀ j ∈ P k.castSucc,
            ((((P k.succ).filter (fun i : ι =>
                ((u k.succ).parentTube i).toConvexSpaceBody ≤
                  ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ))
              ≤ Cn * (N₂ k : ℝ)) →
        (∀ k : Fin M, (N₂ k : ℝ)
          ≤ Cn * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
              ^ (((Module.finrank ℝ E : ℝ) - 1) + ε)) →
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          Kakeya.maxDensity
              (((u k.succ).parent.image
                  (fun i => (u k.succ).parentTube i)).filter
                (fun w : Tube (ρ k.succ) E =>
                  w.toConvexSpaceBody ≤
                    ((u k.castSucc).parentTube j).toConvexSpaceBody))
              (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody)
            ≤ ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)) →
        ∃ (R : Fin M → Finset E) (S : Fin M → ι → Finset (ι × E)),
          (∀ k : Fin M, ∀ v ∈ R k, ‖v‖ ≤ (ρ k.castSucc : ℝ)) ∧
          (∀ k : Fin M,
            c_R * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
                ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))
              ≤ ((R k).card : ℝ) ∧
            ((R k).card : ℝ) ≤
              C_R * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
                ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))) ∧
          (∀ k : Fin M, ∀ j ∈ P k.castSucc,
            S k j ⊆ ((P k.succ).filter (fun i : ι =>
                ((u k.succ).parentTube i).toConvexSpaceBody ≤
                  ((u k.castSucc).parentTube j).toConvexSpaceBody)) ×ˢ (R k)) ∧
          (∀ k : Fin M, ∀ j ∈ P k.castSucc,
            (δ : ℝ) ^ (ε / (M : ℝ)) * ((R k).card : ℝ) *
              (((P k.succ).filter (fun i : ι =>
                ((u k.succ).parentTube i).toConvexSpaceBody ≤
                  ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)
              ≤ K_53 * ((S k j).card : ℝ)) ∧
          (∀ k : Fin M, ∀ j ∈ P k.castSucc,
            Kakeya.maxDensity (S k j)
              (fun p : ι × E =>
                (((u k.succ).parentTube p.1).translate p.2).toConvexSpaceBody)
            ≤ ENNReal.ofReal
                (K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                  ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)) ∧
          ((∀ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ) ≤ 1) →
            ∀ k : Fin M, (R k).card ≤ 1) ∧
          (∀ v v' : Fin M → E, (∀ k : Fin M, v k ∈ R k) → (∀ k : Fin M, v' k ∈ R k) →
            ∑ k : Fin M, v k = ∑ k : Fin M, v' k → ∀ k : Fin M, v k = v' k) := by
  classical
  set εM : ℝ := ε / (M : ℝ) with hεM_def
  have hM_pos_real : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hM
  have hεM_pos : 0 < εM := by rw [hεM_def]; exact div_pos hε hM_pos_real
  obtain ⟨Cε, C_dens, hCε_pos, hC_dens_pos, h_refinement_body⟩ :=
    Kakeya.RandomTranslation.exists_joint_refinement E εM hεM_pos
  set Cε_unified : ℝ := Cε with hCε_unified_def
  have hCε_unified_pos : 0 < Cε_unified := hCε_pos
  have hCε_le_unified : Cε ≤ Cε_unified := le_refl _
  set K_53 : ℝ :=
    subStickyFrostmanLemma.perScaleDeltaMax.K_53_form
      (Module.finrank ℝ E) Cε_unified with hK_53_def
  have hK_53_ge_one : 1 ≤ K_53 :=
    subStickyFrostmanLemma.perScaleDeltaMax.K_53_form_ge_one
      (Module.finrank ℝ E) Cε_unified hCε_unified_pos.le
  have hK_53_pos : 0 < K_53 := lt_of_lt_of_le zero_lt_one hK_53_ge_one
  have hK_53_ge_2Cε_unified : 2 * Cε_unified ≤ K_53 := by
    rw [hK_53_def]
    unfold subStickyFrostmanLemma.perScaleDeltaMax.K_53_form
    have hmax_ge_one : (1 : ℝ) ≤ max 1
        ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
          (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)) := le_max_left _ _
    nlinarith [hCε_unified_pos.le, hmax_ge_one]
  have hK_53_ge_2Cε : 2 * Cε ≤ K_53 := by
    have h2 : 2 * Cε ≤ 2 * Cε_unified := by
      have : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left hCε_le_unified this
    exact le_trans h2 hK_53_ge_2Cε_unified
  set K_pack : ℝ :=
    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
        (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
          MeasureTheory.volume.real (Metric.closedBall (0 : E) 1) + 1
    with hK_pack_def
  have hK_pack_ge_one : 1 ≤ K_pack := by
    rw [hK_pack_def]
    have h1 : 0 ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) :=
      by exact_mod_cast (Tube.volume_le.C (Module.finrank ℝ E)).coe_nonneg
    have h2 : 0 ≤ (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) :=
      by exact_mod_cast
        (translationErosionVolumeConstant (Module.finrank ℝ E)).coe_nonneg
    have h3 : 0 ≤ MeasureTheory.volume.real (Metric.closedBall (0 : E) 1) := by
      positivity
    have hdiv_nonneg : 0 ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
      (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
      MeasureTheory.volume.real (Metric.closedBall (0 : E) 1) :=
      div_nonneg (mul_nonneg h1 h2) h3
    linarith
  have hK_pack_pos : 0 < K_pack := lt_of_lt_of_le zero_lt_one hK_pack_ge_one
  have hCn_pos' : 0 < Cn := lt_of_lt_of_le zero_lt_one hCn_ge_one
  set K_pack2 : ℝ := 2 * Cn ^ 2 * K_pack with hK_pack2_def
  have hK_pack2_ge_one : 1 ≤ K_pack2 := by
    rw [hK_pack2_def]
    nlinarith [hK_pack_ge_one, hCn_ge_one, hCn_pos', hK_pack_pos]
  have hK_pack2_pos : 0 < K_pack2 := lt_of_lt_of_le zero_lt_one hK_pack2_ge_one
  set K_53_out : ℝ := C_dens * K_53 * K_pack2 + K_53 with hK_53_out_def
  have hK_53_out_ge_one : 1 ≤ K_53_out := by
    rw [hK_53_out_def]
    have h_nonneg : 0 ≤ C_dens * K_53 * K_pack2 := by
      positivity
    linarith
  have hK_53_out_ge : C_dens * K_53 * K_pack2 ≤ K_53_out := by
    rw [hK_53_out_def]
    nlinarith [hK_53_ge_one]
  have hK_53_le_out : K_53 ≤ K_53_out := by
    rw [hK_53_out_def]
    have h_nonneg : 0 ≤ C_dens * K_53 * K_pack2 := by
      positivity
    linarith
  refine ⟨K_53_out, 2, 1, hK_53_out_ge_one, one_pos, by norm_num, le_rfl, ?_⟩
  set C_crude : ℝ := C_box with hC_crude_def
  have hC_crude_pos : 0 < C_crude := hC_box_pos
  set C_crude' : ℝ :=
      (M : ℝ) * C_crude * (2 : ℝ) ^ (2 * Module.finrank ℝ E) with hC_crude'_def
  have hC_crude'_pos : 0 < C_crude' := by
    have hM_pos_R0 : (0 : ℝ) < (M : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hM).bot_lt
    exact mul_pos (mul_pos hM_pos_R0 hC_crude_pos) (by positivity)
  have hM_pos_R : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hM).bot_lt
  have hε_div_M_pos : 0 < ε / (M : ℝ) := div_pos hε hM_pos_R
  have hδ_log_bound : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      Real.log
          (2 * C_crude' * (2 / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) + 4)
        ≤ (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
    subStickyFrostmanLemma.perScaleDeltaMax.packingLogBound
      C_crude' hC_crude'_pos (Module.finrank ℝ E) (ε / (M : ℝ)) hε_div_M_pos
  have hδ_le_one_evt : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), (δ : ℝ) ≤ 1 := by
    have h_zero_lt_one : (0 : NNReal) < 1 := by norm_num
    have h_open : Set.Iio (1 : NNReal) ∈ 𝓝 (0 : NNReal) :=
      isOpen_Iio.mem_nhds (show (0 : NNReal) ∈ Set.Iio 1 from h_zero_lt_one)
    refine Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds h_open) ?_
    intro δ hδ
    have : (δ : NNReal) ≤ 1 := le_of_lt hδ
    exact_mod_cast this
  filter_upwards [self_mem_nhdsWithin, hδ_log_bound, hδ_le_one_evt]
    with δ hδ_pos hδ_log hδ_le_one
  intro ι s T hT_in_unit ρ hρ0 hρM hρ_anti hρ_ratio Cu u hParentBall h_count P hP_sub N₂ hN₂_pos
    hCnBracket hCnBracketUB hN₂_xm hInputDeltaMax
  let _h_refinement_universe_pin :=
    fun {M' : ℕ} (hM' : 1 ≤ M') => @h_refinement_body M' hM' (ι := ι)
  suffices hBundle :
      ∃ (R : Fin M → Finset E) (S : Fin M → ι → Finset (ι × E)),
        (∀ k : Fin M, ∀ v ∈ R k, ‖v‖ ≤ (ρ k.castSucc : ℝ)) ∧
        (∀ k : Fin M,
          (1 : ℝ) * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))
            ≤ ((R k).card : ℝ) ∧
          ((R k).card : ℝ) ≤
            2 * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))) ∧
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          S k j ⊆ ((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)) ×ˢ (R k)) ∧
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          (δ : ℝ) ^ (ε / (M : ℝ)) * ((R k).card : ℝ) *
            (((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)
            ≤ K_53_out * ((S k j).card : ℝ)) ∧
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          Kakeya.maxDensity (S k j)
            (fun p : ι × E =>
              (((u k.succ).parentTube p.1).translate p.2).toConvexSpaceBody)
          ≤ ENNReal.ofReal
              (K_53_out * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)) ∧
        ((∀ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
            ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ) ≤ 1) →
          ∀ k : Fin M, (R k).card ≤ 1) ∧
        (∀ v v' : Fin M → E, (∀ k : Fin M, v k ∈ R k) → (∀ k : Fin M, v' k ∈ R k) →
          ∑ k : Fin M, v k = ∑ k : Fin M, v' k → ∀ k : Fin M, v k = v' k) by
    exact hBundle
  set K_vol : ℝ :=
    (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) /
      (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hK_vol_def
  have hK_vol_nn : 0 ≤ K_vol := by
    rw [hK_vol_def]
    exact div_nonneg
      (by exact_mod_cast (Tube.volume_le.C (Module.finrank ℝ E)).coe_nonneg)
      (by exact_mod_cast (Tube.le_volume.c (Module.finrank ℝ E)).coe_nonneg)
  have hM_pos : 0 < M := hM
  have hFinM_ne : (Finset.univ : Finset (Fin M)).Nonempty :=
    ⟨⟨0, hM_pos⟩, Finset.mem_univ _⟩
  set Cn_fn : Fin M → ℝ := fun _ => Cn with hCn_fn_def
  have hCn_pos : ∀ k : Fin M, 0 < Cn_fn k :=
    fun _ => hCn_pos'
  set Cn_max : ℝ := (Finset.univ : Finset (Fin M)).sup' hFinM_ne Cn_fn
    with hCn_max_def
  have hCn_le_max : ∀ k : Fin M, Cn_fn k ≤ Cn_max :=
    fun k => Finset.le_sup' Cn_fn (Finset.mem_univ k)
  have hCn_max_pos : 0 < Cn_max :=
    lt_of_lt_of_le (hCn_pos ⟨0, hM_pos⟩) (hCn_le_max ⟨0, hM_pos⟩)
  set C_F_eff : ℝ := max Cn_max 2 with hC_F_eff_def
  have hCn_max_le_C_F_eff : Cn_max ≤ C_F_eff := le_max_left _ _
  have h2_le_C_F_eff : (2 : ℝ) ≤ C_F_eff := le_max_right _ _
  have hC_F_eff_pos : 0 < C_F_eff :=
    lt_of_lt_of_le hCn_max_pos hCn_max_le_C_F_eff
  set C₀_eff : ℝ := K_vol * C_F_eff + 2 * K_vol + 1 with hC₀_eff_def
  have hK_vol_C_F_nn : 0 ≤ K_vol * C_F_eff :=
    mul_nonneg hK_vol_nn hC_F_eff_pos.le
  have hC₀_eff_ge_K_vol : K_vol ≤ C₀_eff := by
    rw [hC₀_eff_def]; linarith
  have hC₀_eff_ge_2K_vol : 2 * K_vol ≤ C₀_eff := by
    rw [hC₀_eff_def]; linarith
  have hC₀_eff_ge_K_vol_C_F : K_vol * C_F_eff ≤ C₀_eff := by
    rw [hC₀_eff_def]; linarith
  have hFiltPos : ∀ k : Fin M, ∀ j ∈ P k.castSucc,
      (0 : ℝ) <
        (((P k.succ).filter (fun i : ι =>
          ((u k.succ).parentTube i).toConvexSpaceBody ≤
            ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ) := by
    intro k j hj
    have h1 : (0 : ℝ) < (N₂ k : ℝ) := by exact_mod_cast hN₂_pos k
    have h2 : (N₂ k : ℝ) ≤ Cn *
        (((P k.succ).filter (fun i : ι =>
          ((u k.succ).parentTube i).toConvexSpaceBody ≤
            ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ) :=
      hCnBracket k j hj
    have hcard_nn :
        (0 : ℝ) ≤ (((P k.succ).filter (fun i : ι =>
          ((u k.succ).parentTube i).toConvexSpaceBody ≤
            ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rcases eq_or_lt_of_le hcard_nn with h_eq | h_lt
    · exfalso; rw [← h_eq, mul_zero] at h2; linarith
    · exact h_lt
  have hR_construction :
      ∃ (R : Fin M → Finset E) (S : Fin M → ι → Finset (ι × E)),
        (∀ k : Fin M, ∀ v ∈ R k, ‖v‖ ≤ (ρ k.castSucc : ℝ)) ∧
        (∀ k : Fin M,
          (1 : ℝ) * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))
            ≤ ((R k).card : ℝ) ∧
          ((R k).card : ℝ) ≤
            2 * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
              ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))) ∧
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          S k j ⊆ ((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)) ×ˢ (R k)) ∧
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          (δ : ℝ) ^ (ε / (M : ℝ)) * ((R k).card : ℝ) *
            (((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)
            ≤ K_53_out * ((S k j).card : ℝ)) ∧
        (∀ k : Fin M, ∀ j ∈ P k.castSucc,
          Kakeya.maxDensity (S k j)
            (fun p : ι × E =>
              (((u k.succ).parentTube p.1).translate p.2).toConvexSpaceBody)
          ≤ ENNReal.ofReal
              (K_53_out * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)) ∧
        ((∀ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
            ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ) ≤ 1) →
          ∀ k : Fin M, (R k).card ≤ 1) ∧
        (∀ v v' : Fin M → E, (∀ k : Fin M, v k ∈ R k) → (∀ k : Fin M, v' k ∈ R k) →
          ∑ k : Fin M, v k = ∑ k : Fin M, v' k → ∀ k : Fin M, v k = v' k) := by
    set h_joint_body := h_refinement_body with h_joint_body_def
    have hδ_pos_R : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hρ_succ_pos : ∀ k : Fin M, (0 : ℝ) < (ρ k.succ : ℝ) := by
      intro k
      have h_le_last : ρ (Fin.last M) ≤ ρ k.succ := by
        rcases lt_or_eq_of_le (Fin.le_last k.succ) with h | h
        · exact (hρ_anti h).le
        · exact h ▸ le_rfl
      have : ((ρ (Fin.last M) : NNReal) : ℝ) ≤ ((ρ k.succ : NNReal) : ℝ) :=
        by exact_mod_cast h_le_last
      rw [hρM] at this; linarith
    have hρ_cs_pos : ∀ k : Fin M, (0 : ℝ) < (ρ k.castSucc : ℝ) := by
      intro k
      have h_le_last : ρ (Fin.last M) ≤ ρ k.castSucc := by
        rcases lt_or_eq_of_le (Fin.le_last k.castSucc) with h | h
        · exact (hρ_anti h).le
        · exact h ▸ le_rfl
      have : ((ρ (Fin.last M) : NNReal) : ℝ) ≤ ((ρ k.castSucc : NNReal) : ℝ) :=
        by exact_mod_cast h_le_last
      rw [hρM] at this; linarith
    set filt : Fin M → ι → Finset ι := fun k j =>
      (P k.succ).filter (fun i : ι =>
        ((u k.succ).parentTube i).toConvexSpaceBody ≤
          ((u k.castSucc).parentTube j).toConvexSpaceBody) with hfilt_def
    have h_children_density : ∀ k : Fin M, ∀ j ∈ P k.castSucc,
        Kakeya.maxDensity (filt k j)
            (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) ≤
          ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) := by
      intro k j hj
      have h_rescale_inj :
          ((u k.succ).parent : Set ι).InjOn
            (fun i : ι => (u k.succ).parentTube i) :=
        (u k.succ).parentTube_injOn
      have h_inj_on_filter :
          ((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody) :
            Set ι).InjOn
            (fun i : ι => (u k.succ).parentTube i) := by
        intro a ha b hb hab
        have ha' : a ∈ (u k.succ).parent := hP_sub k.succ (Finset.mem_filter.mp ha).1
        have hb' : b ∈ (u k.succ).parent := hP_sub k.succ (Finset.mem_filter.mp hb).1
        exact h_rescale_inj ha' hb' hab
      have h_max_dens_via_image :
          Kakeya.maxDensity (filt k j)
              (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) ≤
            Kakeya.maxDensity
              (((u k.succ).parent.image
                  (fun i => (u k.succ).parentTube i)).filter
                (fun w : Tube (ρ k.succ) E =>
                  w.toConvexSpaceBody ≤
                    ((u k.castSucc).parentTube j).toConvexSpaceBody))
              (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody) := by
        rw [Kakeya.maxDensity_le_iff]
        intro K
        have h_filter_image :
            (filt k j).image (fun i : ι => (u k.succ).parentTube i) ⊆
              ((u k.succ).parent.image
                (fun i : ι => (u k.succ).parentTube i)).filter
                (fun w : Tube (ρ k.succ) E =>
                  w.toConvexSpaceBody ≤
                    ((u k.castSucc).parentTube j).toConvexSpaceBody) := by
          intro w hw
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
          have hiP : i ∈ P k.succ := by
            rw [hfilt_def] at hi
            exact (Finset.mem_filter.mp hi).1
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_image_of_mem _ (hP_sub k.succ hiP), ?_⟩
          rw [hfilt_def] at hi
          exact (Finset.mem_filter.mp hi).2
        have h_num_eq :
            ∑ i ∈ (filt k j) with
                ((u k.succ).parentTube i).toConvexSpaceBody ≤ K,
                MeasureTheory.volume
                  ((u k.succ).parentTube i).toConvexSpaceBody.carrier =
              ∑ w ∈
                  ((filt k j).image
                      (fun i : ι => (u k.succ).parentTube i)).filter
                    (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody ≤ K),
                MeasureTheory.volume w.toConvexSpaceBody.carrier := by
          rw [Finset.filter_image]
          rw [Finset.sum_image]
          intro a ha b hb hab
          have h_inj_on_filtered :
              ((filt k j).filter (fun i : ι =>
                  ((u k.succ).parentTube i).toConvexSpaceBody ≤ K) :
                Set ι).InjOn
                (fun i : ι => (u k.succ).parentTube i) := by
            intro a' ha' b' hb' hab'
            have ha'' : a' ∈ (filt k j) := (Finset.mem_filter.mp ha').1
            have hb'' : b' ∈ (filt k j) := (Finset.mem_filter.mp hb').1
            exact h_inj_on_filter ha'' hb'' hab'
          exact h_inj_on_filtered ha hb hab
        calc Kakeya.densityIn (filt k j)
                (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) K
            = (∑ i ∈ (filt k j) with
                  ((u k.succ).parentTube i).toConvexSpaceBody ≤ K,
                MeasureTheory.volume
                  ((u k.succ).parentTube i).toConvexSpaceBody.carrier) /
                MeasureTheory.volume K.carrier := rfl
          _ = (∑ w ∈
                ((filt k j).image
                    (fun i : ι => (u k.succ).parentTube i)).filter
                  (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody ≤ K),
                MeasureTheory.volume w.toConvexSpaceBody.carrier) /
                MeasureTheory.volume K.carrier := by rw [h_num_eq]
          _ ≤ Kakeya.densityIn
                (((u k.succ).parent.image
                    (fun i : ι => (u k.succ).parentTube i)).filter
                  (fun w : Tube (ρ k.succ) E =>
                    w.toConvexSpaceBody ≤
                      ((u k.castSucc).parentTube j).toConvexSpaceBody))
                (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody) K := by
                  simp only [Kakeya.densityIn]
                  gcongr
          _ ≤ Kakeya.maxDensity
                (((u k.succ).parent.image
                    (fun i : ι => (u k.succ).parentTube i)).filter
                  (fun w : Tube (ρ k.succ) E =>
                    w.toConvexSpaceBody ≤
                      ((u k.castSucc).parentTube j).toConvexSpaceBody))
                (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody) :=
                Kakeya.le_maxDensity _ _ _
      have h_input := hInputDeltaMax k j hj
      exact le_trans h_max_dens_via_image h_input
    set xval : Fin M → ℝ := fun k =>
      ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)
      with hxval_def
    set Jval : Fin M → ℕ := fun k => max 1 ⌈xval k⌉₊ with hJval_def
    have hJval_ge_one : ∀ k, 1 ≤ Jval k := fun k => le_max_left _ _
    have hxval_nonneg : ∀ k, 0 ≤ xval k := by
      intro k
      rw [hxval_def]
      have hN₂k : (0 : ℝ) ≤ (N₂ k : ℝ) := Nat.cast_nonneg _
      have := Real.rpow_nonneg
        (div_nonneg (hρ_cs_pos k).le (hρ_succ_pos k).le) ((Module.finrank ℝ E : ℝ) - 1)
      positivity
    have h_joint := h_joint_body hM
      (δ := fun k => ρ k.succ) (ρ := fun k => ρ k.castSucc)
      (r := fun k => ρ k.castSucc)
      (fun k => hρ_succ_pos k)
      (by
        intro k
        have h_lt : k.castSucc < k.succ := Fin.castSucc_lt_succ
        have h_strict : ρ k.succ < ρ k.castSucc := hρ_anti h_lt
        have h_strict' : (ρ k.succ : ℝ) < (ρ k.castSucc : ℝ) := by exact_mod_cast h_strict
        have h_cs_le_one : (ρ k.castSucc : ℝ) ≤ 1 := by
          have h_cs_le_ρ0 : ρ k.castSucc ≤ ρ 0 := hρ_anti.antitone (Fin.zero_le _)
          have h_ρ0_one : (ρ 0 : ℝ) ≤ 1 := by exact_mod_cast hρ0
          calc
            (ρ k.castSucc : ℝ) ≤ (ρ 0 : ℝ) := by exact_mod_cast h_cs_le_ρ0
            _ ≤ 1 := h_ρ0_one
        linarith)
      (by
        intro k
        have h_lt : k.castSucc < k.succ := Fin.castSucc_lt_succ
        have h_le : ρ k.succ ≤ ρ k.castSucc := (hρ_anti h_lt).le
        exact_mod_cast h_le)
      (by
        intro k
        have h_le : ρ k.castSucc ≤ ρ 0 := hρ_anti.antitone (Fin.zero_le _)
        have h1 : ((ρ k.castSucc : NNReal) : ℝ) ≤ ((ρ 0 : NNReal) : ℝ) :=
          by exact_mod_cast h_le
        have h2 : ((ρ 0 : NNReal) : ℝ) ≤ 1 := by exact_mod_cast hρ0
        linarith)
      (fun k => hρ_cs_pos k)
      (fun _ => le_rfl)
      (ι := ι) (α := fun _ => ι)
      (P := fun k => P k.castSucc)
      (s := fun k p => filt k p)
      (T := fun k i => (u k.succ).parentTube i)
      (Tρ := fun k p => (u k.castSucc).parentTube p)
      (by
        intro k p hp
        have hcard_pos_real : (0 : ℝ) < ((filt k p).card : ℝ) := hFiltPos k p hp
        have hcard_pos : 0 < (filt k p).card := by
          exact_mod_cast hcard_pos_real
        exact Finset.card_pos.mp hcard_pos)
      (fun k p hp => hParentBall k.castSucc p (hP_sub k.castSucc hp))
      (by
        intro k p hp i hi
        have hi_filter : i ∈ P k.succ ∧
            ((u k.succ).parentTube i).toConvexSpaceBody ≤
              ((u k.castSucc).parentTube p).toConvexSpaceBody := by
          simpa [filt, Finset.mem_filter] using hi
        exact SetLike.coe_subset_coe.mpr hi_filter.2)
      (M_dens := fun k p => K_pack2 * (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε))
      (by
        intro k p hp
        have h_ratio_nonneg : 0 ≤ ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε :=
          Real.rpow_nonneg (div_nonneg (hρ_cs_pos k).le (hρ_succ_pos k).le) _
        have h_density_real : (Kakeya.maxDensity (filt k p)
            (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody)).toReal ≤
            ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε := by
          have h_ennreal := h_children_density k p hp
          have h_maxfinite : Kakeya.maxDensity (filt k p)
              (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) ≠ ⊤ :=
            Kakeya.maxDensity_ne_top _ _
          have h_toReal_le : (Kakeya.maxDensity (filt k p)
              (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody)).toReal ≤
              (ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)).toReal :=
            ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) h_ennreal
          rw [ENNReal.toReal_ofReal h_ratio_nonneg] at h_toReal_le
          exact h_toReal_le
        calc
          (Kakeya.maxDensity (filt k p)
              (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody)).toReal
              ≤ ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε := h_density_real
          _ ≤ K_pack2 * (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) :=
            le_mul_of_one_le_left h_ratio_nonneg hK_pack2_ge_one)
      (J := Jval)
      hJval_ge_one
      (by
        intro k p hp
        have hρ_cs_le_one' : (ρ k.castSucc : NNReal) ≤ 1 := by
          have h_cs_le_ρ0 : ρ k.castSucc ≤ ρ 0 := hρ_anti.antitone (Fin.zero_le _)
          exact h_cs_le_ρ0.trans hρ0
        have hρ_succ_le_cs : (ρ k.succ : ℝ) ≤ (ρ k.castSucc : ℝ) := by
          have h_le : ρ k.succ ≤ ρ k.castSucc := (hρ_anti Fin.castSucc_lt_succ).le
          exact_mod_cast h_le
        have hK_pack_eq : ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
            (ρ k.castSucc : ℝ) ^ (Module.finrank ℝ E - 1)) *
            Kakeya.probConst E ((ρ k.castSucc : ℝ)) + 1 ≤ K_pack := by
          have h_scale_free : ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
              (ρ k.castSucc : ℝ) ^ (Module.finrank ℝ E - 1)) *
              Kakeya.probConst E ((ρ k.castSucc : ℝ)) =
              (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
                (translationErosionVolumeConstant (Module.finrank ℝ E) : ℝ) /
                MeasureTheory.volume.real (Metric.closedBall (0 : E) 1) := by
            unfold Kakeya.probConst
            set n := Module.finrank ℝ E with hn_def
            have hx : (ρ k.castSucc : ℝ) ^ (n - 1) ≠ 0 :=
              pow_ne_zero (n - 1) (hρ_cs_pos k).ne'
            field_simp [hx]
          rw [h_scale_free, hK_pack_def]
        have hcalib := calibration_core (E := E) (hρ_succ_pos k) (hρ_cs_pos k)
          hρ_succ_le_cs hε hCn_ge_one (hN₂_pos k) (hCnBracketUB k p hp) (hN₂_xm k) hK_pack_eq
        rw [hJval_def, hxval_def, hK_pack2_def]
        exact hcalib)
      ((1 : ENNReal) / 2)
      (by
        simp)
      (by
        rw [ENNReal.div_lt_iff (by norm_num) (by norm_num)]
        simp)
      (A := fun _ => K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))))
      (by
        intro k
        set n_dim : ℕ := Module.finrank ℝ E with hn_dim_def
        have hneg_le : -(ε / (M : ℝ)) ≤ 0 :=
          neg_nonpos_of_nonneg hε_div_M_pos.le
        have hδ_pow_pos : (0 : ℝ) < (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
          Real.rpow_pos_of_pos hδ_pos_R _
        have hδ_pow_ge_one : (1 : ℝ) ≤ (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos_R hδ_le_one hneg_le
        have hρ_succ_ge_δ : (δ : ℝ) ≤ (ρ k.succ : ℝ) := by
          have h_le_last : ρ (Fin.last M) ≤ ρ k.succ := by
            rcases lt_or_eq_of_le (Fin.le_last k.succ) with h | h
            · exact (hρ_anti h).le
            · exact h ▸ le_rfl
          have : ((ρ (Fin.last M) : NNReal) : ℝ) ≤ ((ρ k.succ : NNReal) : ℝ) :=
            by exact_mod_cast h_le_last
          rw [hρM] at this; exact this
        have hρ_succ_pos_R : (0 : ℝ) < (ρ k.succ : ℝ) :=
          lt_of_lt_of_le hδ_pos_R hρ_succ_ge_δ
        have h_chain1 : ((ρ k.succ : ℝ)) ^ (-(ε / (M : ℝ))) ≤
            (δ : ℝ) ^ (-(ε / (M : ℝ))) := by
          exact Real.rpow_le_rpow_of_nonpos hδ_pos_R hρ_succ_ge_δ hneg_le
        set N_real : ℝ := ∑ l : Fin M, ((P l.castSucc).card : ℝ) with hN_real_def
        have hN_real_nn : 0 ≤ N_real := by
          rw [hN_real_def]
          exact Finset.sum_nonneg (fun l _ => by positivity)
        have hCε_nn : 0 ≤ Cε := hCε_pos.le
        have h_half_toReal : ((1 : ENNReal) / 2).toReal = 1 / 2 := by
          rw [ENNReal.toReal_div]
          simp
        have h_log_arg :
            Real.log (N_real / ((1 : ENNReal) / 2).toReal) =
              Real.log (2 * N_real) := by
          rw [h_half_toReal]
          congr 1; field_simp
        have h_parent_card_bd : ∀ l : Fin M,
            ((u l.castSucc).parent.card : ℝ) ≤
              C_crude * (4 / (δ : ℝ)) ^ (2 * n_dim) := by
          intro l
          have hρ_lcs_pos_R : (0 : ℝ) < (ρ l.castSucc : ℝ) := by
            have h_le_last : ρ (Fin.last M) ≤ ρ l.castSucc := by
              rcases lt_or_eq_of_le (Fin.le_last l.castSucc) with h | h
              · exact (hρ_anti h).le
              · exact h ▸ le_rfl
            have : ((ρ (Fin.last M) : NNReal) : ℝ) ≤ ((ρ l.castSucc : NNReal) : ℝ) :=
              by exact_mod_cast h_le_last
            rw [hρM] at this; linarith
          have hρ_lcs_ge_δ : (δ : ℝ) ≤ (ρ l.castSucc : ℝ) := by
            have h_le_last : ρ (Fin.last M) ≤ ρ l.castSucc := by
              rcases lt_or_eq_of_le (Fin.le_last l.castSucc) with h | h
              · exact (hρ_anti h).le
              · exact h ▸ le_rfl
            have : ((ρ (Fin.last M) : NNReal) : ℝ) ≤ ((ρ l.castSucc : NNReal) : ℝ) :=
              by exact_mod_cast h_le_last
            rw [hρM] at this; exact this
          have h_at_scale :
              (((u l.castSucc).parent.card : ℝ)) ≤
                C_crude * ((4 : ℝ) / (ρ l.castSucc : ℝ)) ^ (2 * n_dim) := by
            rw [hC_crude_def, hn_dim_def]
            exact h_count l
          have h4_pos : (0 : ℝ) < 4 := by norm_num
          have hdiv_le : (4 : ℝ) / (ρ l.castSucc : ℝ) ≤ (4 : ℝ) / (δ : ℝ) := by
            exact div_le_div_of_nonneg_left h4_pos.le hδ_pos_R hρ_lcs_ge_δ
          have hdiv_nn : (0 : ℝ) ≤ (4 : ℝ) / (ρ l.castSucc : ℝ) :=
            div_nonneg h4_pos.le hρ_lcs_pos_R.le
          have hpow_le : ((4 : ℝ) / (ρ l.castSucc : ℝ)) ^ (2 * n_dim) ≤
              ((4 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) :=
            pow_le_pow_left₀ hdiv_nn hdiv_le _
          have hmul_le : C_crude * ((4 : ℝ) / (ρ l.castSucc : ℝ)) ^ (2 * n_dim) ≤
              C_crude * ((4 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) :=
            mul_le_mul_of_nonneg_left hpow_le hC_crude_pos.le
          exact le_trans h_at_scale hmul_le
        have h_N_real_bd :
            N_real ≤ (M : ℝ) * C_crude * (4 / (δ : ℝ)) ^ (2 * n_dim) := by
          rw [hN_real_def]
          have h_sum_bd : ∑ l : Fin M, ((P l.castSucc).card : ℝ) ≤
              ∑ _l : Fin M, C_crude * (4 / (δ : ℝ)) ^ (2 * n_dim) :=
            Finset.sum_le_sum (fun l _ =>
              le_trans (by exact_mod_cast Finset.card_le_card (hP_sub l.castSucc))
                (h_parent_card_bd l))
          have h_sum_eq : ∑ _l : Fin M, C_crude * (4 / (δ : ℝ)) ^ (2 * n_dim) =
              (M : ℝ) * C_crude * (4 / (δ : ℝ)) ^ (2 * n_dim) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
          exact h_sum_eq ▸ h_sum_bd
        have h_pow_split :
            ((4 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) =
              ((2 : ℝ) ^ (2 * n_dim)) * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) := by
          have h_factor : (4 : ℝ) / (δ : ℝ) = 2 * (2 / (δ : ℝ)) := by ring
          rw [h_factor, mul_pow]
        have h_2N_bd :
            2 * N_real ≤
              2 * C_crude' * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) := by
          have h_C_crude'_eq :
              C_crude' = (M : ℝ) * C_crude * (2 : ℝ) ^ (2 * n_dim) :=
            hC_crude'_def
          calc 2 * N_real
              ≤ 2 * ((M : ℝ) * C_crude * (4 / (δ : ℝ)) ^ (2 * n_dim)) :=
                  mul_le_mul_of_nonneg_left h_N_real_bd (by norm_num)
            _ = 2 * ((M : ℝ) * C_crude *
                  ((2 : ℝ) ^ (2 * n_dim) * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim))) := by
                rw [h_pow_split]
            _ = 2 * C_crude' * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) := by
                rw [h_C_crude'_eq]; ring
        have h2δ_pos : (0 : ℝ) < (2 : ℝ) / (δ : ℝ) := by
          apply div_pos; · norm_num
          · exact hδ_pos_R
        have h2δ_pow_pos : (0 : ℝ) < ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) :=
          pow_pos h2δ_pos _
        have h2N_pos_arg : (0 : ℝ) <
            2 * C_crude' * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) :=
          mul_pos (mul_pos (by norm_num) hC_crude'_pos) h2δ_pow_pos
        have h2N_le_inside_log :
            2 * C_crude' * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) ≤
              2 * C_crude' * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) + 4 :=
          le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 4)
        have h_log_inside_pos : (0 : ℝ) <
            2 * C_crude' * ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) + 4 :=
          lt_of_lt_of_le h2N_pos_arg h2N_le_inside_log
        have h_chain2 :
            Real.log (2 * N_real) ≤ (δ : ℝ) ^ (-(ε / (M : ℝ))) := by
          by_cases hN_zero : N_real = 0
          · rw [hN_zero]
            simp only [mul_zero, Real.log_zero]
            exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hδ_pow_ge_one
          · have hN_real_pos : 0 < N_real :=
              lt_of_le_of_ne hN_real_nn (Ne.symm hN_zero)
            have h2N_pos : (0 : ℝ) < 2 * N_real :=
              mul_pos (by norm_num : (0 : ℝ) < 2) hN_real_pos
            have h_log_mono1 :
                Real.log (2 * N_real) ≤
                  Real.log (2 * C_crude' *
                    ((2 : ℝ) / (δ : ℝ)) ^ (2 * n_dim) + 4) :=
              Real.log_le_log h2N_pos (le_trans h_2N_bd h2N_le_inside_log)
            exact le_trans h_log_mono1 hδ_log
        have h_chain2' :
            Real.log (N_real / ((1 : ENNReal) / 2).toReal) ≤
              (δ : ℝ) ^ (-(ε / (M : ℝ))) := by
          rw [h_log_arg]; exact h_chain2
        have h_sum_bd_chain :
            ((ρ k.succ : ℝ)) ^ (-(ε / (M : ℝ))) +
                Real.log (N_real / ((1 : ENNReal) / 2).toReal) ≤
              (δ : ℝ) ^ (-(ε / (M : ℝ))) +
                (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
          add_le_add h_chain1 h_chain2'
        calc Cε * (((ρ k.succ : ℝ)) ^ (-(ε / (M : ℝ))) +
                Real.log (N_real / ((1 : ENNReal) / 2).toReal))
            ≤ Cε * ((δ : ℝ) ^ (-(ε / (M : ℝ))) +
                (δ : ℝ) ^ (-(ε / (M : ℝ)))) :=
              mul_le_mul_of_nonneg_left h_sum_bd_chain hCε_nn
          _ = (2 * Cε) * (δ : ℝ) ^ (-(ε / (M : ℝ))) := by ring
          _ ≤ K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
              mul_le_mul_of_nonneg_right hK_53_ge_2Cε hδ_pow_pos.le)
    obtain ⟨BadJoint, hBadJoint_meas, hBadJoint_budget, h_witness⟩ := h_joint
    have hω₀_ex : ∃ ω₀ : ∀ k : Fin M, Fin (Jval k) → E,
        ω₀ ∉ BadJoint ∧ ω₀ ∉ Kakeya.RandomTranslation.jointCollision (E := E) Jval ∧
          ω₀ ∉ Kakeya.RandomTranslation.jointOutside (E := E) Jval ∧
          ω₀ ∉ Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
            (fun k : Fin M => (ρ k.castSucc : ℝ)) := by
      by_contra h_no
      push Not at h_no
      have h_univ_subset : (Set.univ : Set (∀ k : Fin M, Fin (Jval k) → E)) ⊆
          BadJoint ∪ (Kakeya.RandomTranslation.jointCollision (E := E) Jval ∪
            (Kakeya.RandomTranslation.jointOutside (E := E) Jval ∪
              Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
                (fun k : Fin M => (ρ k.castSucc : ℝ)))) := by
        intro ω _
        by_cases hb : ω ∈ BadJoint
        · exact Or.inl hb
        · by_cases hc : ω ∈ Kakeya.RandomTranslation.jointCollision (E := E) Jval
          · exact Or.inr (Or.inl hc)
          · by_cases ho : ω ∈ Kakeya.RandomTranslation.jointOutside (E := E) Jval
            · exact Or.inr (Or.inr (Or.inl ho))
            · exact Or.inr (Or.inr (Or.inr (h_no ω hb hc ho)))
      have h_univ_le : HasUniformTranslation.productMeasureIndexed E E Jval Set.univ ≤
          HasUniformTranslation.productMeasureIndexed E E Jval
            (BadJoint ∪ (Kakeya.RandomTranslation.jointCollision (E := E) Jval ∪
              (Kakeya.RandomTranslation.jointOutside (E := E) Jval ∪
                Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
                  (fun k : Fin M => (ρ k.castSucc : ℝ))))) :=
        measure_mono h_univ_subset
      have h_union_le : HasUniformTranslation.productMeasureIndexed E E Jval
            (BadJoint ∪ (Kakeya.RandomTranslation.jointCollision (E := E) Jval ∪
              (Kakeya.RandomTranslation.jointOutside (E := E) Jval ∪
                Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
                  (fun k : Fin M => (ρ k.castSucc : ℝ))))) ≤ (1 : ENNReal) / 2 := by
        refine le_trans (measure_union_le _ _) ?_
        have h_sum_null : HasUniformTranslation.productMeasureIndexed E E Jval
            (Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
              (fun k : Fin M => (ρ k.castSucc : ℝ))) = 0 :=
          Kakeya.RandomTranslation.productMeasureIndexed_jointSumCollision_null (E := E) Jval _
            (fun k => ne_of_gt (hρ_cs_pos k))
        have h_inner : HasUniformTranslation.productMeasureIndexed E E Jval
            (Kakeya.RandomTranslation.jointCollision (E := E) Jval ∪
              (Kakeya.RandomTranslation.jointOutside (E := E) Jval ∪
                Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
                  (fun k : Fin M => (ρ k.castSucc : ℝ)))) = 0 := by
          refine le_antisymm (le_trans (measure_union_le _ _) ?_) (by simp)
          have h_inner2 : HasUniformTranslation.productMeasureIndexed E E Jval
              (Kakeya.RandomTranslation.jointOutside (E := E) Jval ∪
                Kakeya.RandomTranslation.jointSumCollision (E := E) Jval
                  (fun k : Fin M => (ρ k.castSucc : ℝ))) = 0 := by
            refine le_antisymm (le_trans (measure_union_le _ _) ?_) (by simp)
            rw [Kakeya.RandomTranslation.productMeasureIndexed_jointOutside_null (E := E) Jval
              hJval_ge_one,
              h_sum_null, add_zero]
          rw [Kakeya.RandomTranslation.productMeasureIndexed_jointCollision_null (E := E) Jval,
            h_inner2,
            add_zero]
        rw [h_inner, add_zero]
        exact hBadJoint_budget
      have h_univ_eq : HasUniformTranslation.productMeasureIndexed E E Jval Set.univ = 1 :=
        measure_univ
      rw [h_univ_eq] at h_univ_le
      have h_one_le_half : (1 : ENNReal) ≤ (1 : ENNReal) / 2 :=
        le_trans h_univ_le h_union_le
      have h_half_lt_one : (1 : ENNReal) / 2 < 1 := by
        have h_half_real : ((1 : ENNReal) / 2).toReal = 1 / 2 := by
          rw [ENNReal.toReal_div]; simp
        have h_half_ne_top : (1 : ENNReal) / 2 ≠ ⊤ :=
          ENNReal.div_ne_top (by norm_num) (by norm_num)
        rw [← ENNReal.toReal_lt_toReal h_half_ne_top (by norm_num)]
        rw [h_half_real]
        simp
        norm_num
      exact absurd (lt_of_le_of_lt h_one_le_half h_half_lt_one) (lt_irrefl _)
    obtain ⟨ω₀, hω₀_notin_joint, hω₀_notin_coll, hω₀_notin_out, hω₀_notin_sum⟩ := hω₀_ex
    have hω₀_inj : ∀ k : Fin M, Function.Injective (ω₀ k) := fun k =>
      Kakeya.RandomTranslation.injective_of_notMem_jointCollision hω₀_notin_coll k
    have hω₀_norm : ∀ (k : Fin M) (j : Fin (Jval k)), ‖ω₀ k j‖ ≤ 1 := fun k j =>
      Kakeya.RandomTranslation.norm_le_one_of_notMem_jointOutside hω₀_notin_out k j
    have hω₀_sum_inj : Function.Injective
        (fun j : ∀ k : Fin M, Fin (Jval k) =>
          ∑ k : Fin M, (ρ k.castSucc : ℝ) • ω₀ k (j k)) :=
      Kakeya.RandomTranslation.sum_injective_of_notMem_jointSumCollision hω₀_notin_sum
    obtain ⟨s', h_clauses⟩ := h_witness ω₀ hω₀_notin_joint
    classical
    refine ⟨fun k =>
              (Finset.univ : Finset (Fin (Jval k))).image
                (fun j : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k j),
            fun k p =>
              if _h : (P k.castSucc).Nonempty then
                (s' k p).image
                  (fun a : ι × Fin (Jval k) => (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2))
              else (∅ : Finset (ι × E)),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k v hv
      change v ∈ (Finset.univ : Finset (Fin (Jval k))).image
                  (fun j : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k j) at hv
      obtain ⟨j, _, h_eq⟩ := Finset.mem_image.mp hv
      rw [← h_eq]
      have h : ‖(ρ k.castSucc : ℝ) • ω₀ k j‖ = |(ρ k.castSucc : ℝ)| * ‖ω₀ k j‖ := norm_smul _ _
      rw [h, abs_of_nonneg (hρ_cs_pos k).le]
      calc (ρ k.castSucc : ℝ) * ‖ω₀ k j‖
          ≤ (ρ k.castSucc : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (hω₀_norm k j) (hρ_cs_pos k).le
        _ = (ρ k.castSucc : ℝ) := mul_one _
    · intro k
      have hR_card : ((Finset.univ : Finset (Fin (Jval k))).image
          (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj)).card = Jval k := by
        have hρ_ne : (ρ k.castSucc : ℝ) ≠ 0 := ne_of_gt (hρ_cs_pos k)
        have hsmul_inj : Function.Injective (fun x : E => (ρ k.castSucc : ℝ) • x) :=
          smul_right_injective E hρ_ne
        have hR_inj : Function.Injective (fun (jj : Fin (Jval k)) =>
          (ρ k.castSucc : ℝ) • ω₀ k jj) :=
          fun a b h => hω₀_inj k (hsmul_inj h)
        calc
          _ = (Finset.univ : Finset (Fin (Jval k))).card :=
            Finset.card_image_of_injective _ hR_inj
          _ = Jval k := by simp
      have hR_card_real : (((Finset.univ : Finset (Fin (Jval k))).image
          (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj)).card : ℝ) = (Jval k : ℝ) := by
        exact_mod_cast hR_card
      have hbracket := jval_bracket (hxval_nonneg k)
      have hleft : (1 : ℝ) * max 1 (xval k) ≤ (Jval k : ℝ) := by
        calc
          (1 : ℝ) * max 1 (xval k) = max 1 (xval k) := by simp
          _ ≤ ((max 1 ⌈xval k⌉₊ : ℕ) : ℝ) := hbracket.1
          _ = (Jval k : ℝ) := by simp [hJval_def]
      have hright : (Jval k : ℝ) ≤ (2 : ℝ) * max 1 (xval k) := by
        calc
          (Jval k : ℝ) = ((max 1 ⌈xval k⌉₊ : ℕ) : ℝ) := by simp [hJval_def]
          _ ≤ (2 : ℝ) * max 1 (xval k) := hbracket.2
      have hRk_card_eq : ↑((fun (k' : Fin M) => (Finset.univ : Finset (Fin (Jval k'))).image
          (fun (j : Fin (Jval k')) => (ρ k'.castSucc : ℝ) • ω₀ k' j)) k).card = (Jval k : ℝ) := by
        calc
          ↑((fun (k' : Fin M) => (Finset.univ : Finset (Fin (Jval k'))).image
              (fun (j : Fin (Jval k')) => (ρ k'.castSucc : ℝ) • ω₀ k' j)) k).card
              = (((Finset.univ : Finset (Fin (Jval k))).image
                  (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj)).card : ℝ) := rfl
          _ = (Jval k : ℝ) := hR_card_real
      simpa [hxval_def, hRk_card_eq, one_mul] using And.intro hleft hright
    · intro k j hj
      have h_ne : (P k.castSucc).Nonempty := ⟨j, hj⟩
      change (if _h : (P k.castSucc).Nonempty then
                (s' k j).image
                  (fun a : ι × Fin (Jval k) => (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2))
              else (∅ : Finset (ι × E))) ⊆
            ((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)) ×ˢ
              ((Finset.univ : Finset (Fin (Jval k))).image
                (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj))
      rw [dif_pos h_ne]
      have h_joint_sub := (h_clauses k j hj).2.1
      intro a ha
      obtain ⟨b, hb_in_s', hb_eq⟩ := Finset.mem_image.mp ha
      rw [← hb_eq]
      have hb_mem := h_joint_sub hb_in_s'
      rw [Finset.mem_product] at hb_mem
      rw [Finset.mem_product]
      refine ⟨hb_mem.1, ?_⟩
      refine Finset.mem_image.mpr ⟨b.2, Finset.mem_univ _, rfl⟩
    · intro k j hj
      have h_ne : (P k.castSucc).Nonempty := ⟨j, hj⟩
      change (δ : ℝ) ^ (ε / (M : ℝ)) *
          ((((Finset.univ : Finset (Fin (Jval k))).image
                (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj)).card : ℝ)) *
          ((filt k j).card : ℝ) ≤
        K_53_out * (((if _h : (P k.castSucc).Nonempty then
          (s' k j).image
            (fun a : ι × Fin (Jval k) => (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2))
        else (∅ : Finset (ι × E))).card : ℝ))
      rw [dif_pos h_ne]
      have hρ_ne : (ρ k.castSucc : ℝ) ≠ 0 := ne_of_gt (hρ_cs_pos k)
      have hsmul_inj : Function.Injective (fun x : E => (ρ k.castSucc : ℝ) • x) :=
        smul_right_injective E hρ_ne
      have hR_inj : Function.Injective (fun (jj : Fin (Jval k)) =>
          (ρ k.castSucc : ℝ) • ω₀ k jj) :=
        fun a b h => hω₀_inj k (hsmul_inj h)
      have hR_card :
          ((Finset.univ : Finset (Fin (Jval k))).image
            (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj)).card = Jval k := by
        calc
          _ = (Finset.univ : Finset (Fin (Jval k))).card :=
            Finset.card_image_of_injective _ hR_inj
          _ = Jval k := by simp
      have hR_card_real : (((Finset.univ : Finset (Fin (Jval k))).image
          (fun jj : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k jj)).card : ℝ) = (Jval k : ℝ) := by
        exact_mod_cast hR_card
      rw [hR_card_real]
      have hS_inj : Function.Injective
          (fun (a : ι × Fin (Jval k)) => (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2)) := by
        intro x y h
        have h_pair : (x.1, (ρ k.castSucc : ℝ) • ω₀ k x.2) = (y.1, (ρ k.castSucc : ℝ) • ω₀ k y.2)
          := h
        have h_fst : x.1 = y.1 := (Prod.mk.inj h_pair).1
        have h_snd : (ρ k.castSucc : ℝ) • ω₀ k x.2 = (ρ k.castSucc : ℝ) • ω₀ k y.2
          := (Prod.mk.inj h_pair).2
        have h_omega : ω₀ k x.2 = ω₀ k y.2 := hsmul_inj h_snd
        have h_snd' : x.2 = y.2 := hω₀_inj k h_omega
        exact Prod.ext h_fst h_snd'
      have hS_card : ((s' k j).image
          (fun (a : ι × Fin (Jval k)) =>
            (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2))).card = (s' k j).card :=
        Finset.card_image_of_injective _ hS_inj
      have hS_card_real : (((s' k j).image
          (fun (a : ι × Fin (Jval k)) =>
            (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2))).card : ℝ) = ((s' k j).card : ℝ) := by
        exact_mod_cast hS_card
      rw [hS_card_real]
      have h_joint_count := (h_clauses k j hj).2.2.1
      have hδ_pow_pos : 0 < (δ : ℝ) ^ (ε / (M : ℝ)) :=
        Real.rpow_pos_of_pos hδ_pos_R _
      have hδ_pow_neg_pos : 0 < (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
        Real.rpow_pos_of_pos hδ_pos_R _
      have hK53_mul_pos : 0 < K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))) := by positivity
      have h_step1 : (Jval k : ℝ) * ((filt k j).card : ℝ) ≤
          K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))) * ((s' k j).card : ℝ) := by
        calc
          (Jval k : ℝ) * ((filt k j).card : ℝ)
              = (K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ)))) *
                  ((K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))))⁻¹ * (Jval k : ℝ) * ((filt k j).card : ℝ))
                  := by
            field_simp [hK53_mul_pos.ne']
          _ ≤ (K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ)))) * ((s' k j).card : ℝ) := by
            refine mul_le_mul_of_nonneg_left h_joint_count (by positivity)
          _ = K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))) * ((s' k j).card : ℝ) := by ring
      have hδ_pow_mul_self : (δ : ℝ) ^ (ε / (M : ℝ)) * (δ : ℝ) ^ (-(ε / (M : ℝ))) = 1 := by
        calc
          (δ : ℝ) ^ (ε / (M : ℝ)) * (δ : ℝ) ^ (-(ε / (M : ℝ)))
              = (δ : ℝ) ^ (ε / (M : ℝ)) * ((δ : ℝ) ^ (ε / (M : ℝ)))⁻¹ := by
                rw [Real.rpow_neg (hδ_pos_R.le)]
          _ = 1 := by field_simp [hδ_pow_pos.ne']
      have h_step2 : (δ : ℝ) ^ (ε / (M : ℝ)) * (Jval k : ℝ) * ((filt k j).card : ℝ) ≤
          K_53 * ((s' k j).card : ℝ) := by
        calc
          (δ : ℝ) ^ (ε / (M : ℝ)) * (Jval k : ℝ) * ((filt k j).card : ℝ)
              = (δ : ℝ) ^ (ε / (M : ℝ)) * ((Jval k : ℝ) * ((filt k j).card : ℝ)) := by ring
          _ ≤ (δ : ℝ) ^ (ε / (M : ℝ)) *
              (K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ))) * ((s' k j).card : ℝ)) :=
            mul_le_mul_of_nonneg_left h_step1 (by positivity)
          _ = K_53 * ((δ : ℝ) ^ (ε / (M : ℝ)) * (δ : ℝ) ^ (-(ε / (M : ℝ))))
            * ((s' k j).card : ℝ) := by ring
          _ = K_53 * 1 * ((s' k j).card : ℝ) := by rw [hδ_pow_mul_self]
          _ = K_53 * ((s' k j).card : ℝ) := by ring
      have h_card_nonneg : 0 ≤ ((s' k j).card : ℝ) := by exact_mod_cast Nat.zero_le _
      calc
        (δ : ℝ) ^ (ε / (M : ℝ)) * (Jval k : ℝ) * ((filt k j).card : ℝ) ≤
            K_53 * ((s' k j).card : ℝ) := h_step2
        _ ≤ K_53_out * ((s' k j).card : ℝ) :=
          mul_le_mul_of_nonneg_right hK_53_le_out h_card_nonneg
    · intro k j hj
      have h_ne : (P k.castSucc).Nonempty := ⟨j, hj⟩
      change Kakeya.maxDensity
          ((if _h : (P k.castSucc).Nonempty then
              (s' k j).image
                (fun a : ι × Fin (Jval k) => (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2))
            else (∅ : Finset (ι × E))))
          (fun p : ι × E =>
            (((u k.succ).parentTube p.1).translate p.2).toConvexSpaceBody)
        ≤ ENNReal.ofReal
            (K_53_out * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
              ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)
      rw [dif_pos h_ne]
      set pairMap : ι × Fin (Jval k) → ι × E :=
        fun a : ι × Fin (Jval k) => (a.1, (ρ k.castSucc : ℝ) • ω₀ k a.2) with hpairMap_def
      set hMap : ι × Fin (Jval k) → Tube (ρ k.succ) E :=
        fun a : ι × Fin (Jval k) =>
          ((u k.succ).parentTube a.1).translate
            ((ρ k.castSucc : ℝ) • ω₀ k a.2) with hMap_def
      have h_image_le :
          Kakeya.maxDensity ((s' k j).image pairMap)
              (fun p : ι × E =>
              (((u k.succ).parentTube p.1).translate p.2).toConvexSpaceBody) ≤
            Kakeya.maxDensity (s' k j)
              (fun a : ι × Fin (Jval k) => (hMap a).toConvexSpaceBody) := by
        rw [Kakeya.maxDensity_le_iff]
        intro K
        set tcb : ι × E → ConvexSpaceBody E :=
          fun p : ι × E =>
            (((u k.succ).parentTube p.1).translate p.2).toConvexSpaceBody with htcb_def
        have h_rew :
            (((s' k j).image pairMap).filter (fun p => tcb p ≤ K)) =
              ((s' k j).filter (fun a => tcb (pairMap a) ≤ K)).image pairMap :=
          Finset.filter_image
        have h_num_le :
            (∑ p ∈ ((s' k j).image pairMap).filter (fun p => tcb p ≤ K),
                MeasureTheory.volume (tcb p).carrier) ≤
              ∑ a ∈ (s' k j).filter (fun a => tcb (pairMap a) ≤ K),
                MeasureTheory.volume (tcb (pairMap a)).carrier := by
          rw [h_rew]
          exact Finset.sum_image_le_of_nonneg (fun _ _ => bot_le)
        change Kakeya.densityIn ((s' k j).image pairMap) tcb K ≤
          Kakeya.maxDensity (s' k j) (fun p => tcb (pairMap p))
        calc Kakeya.densityIn ((s' k j).image pairMap) tcb K
            = (∑ p ∈ ((s' k j).image pairMap).filter (fun p => tcb p ≤ K),
                MeasureTheory.volume (tcb p).carrier) /
                MeasureTheory.volume K.carrier := rfl
          _ ≤ (∑ a ∈ (s' k j).filter (fun a => tcb (pairMap a) ≤ K),
                MeasureTheory.volume (tcb (pairMap a)).carrier) /
                MeasureTheory.volume K.carrier := ENNReal.div_le_div_right h_num_le _
          _ = Kakeya.densityIn (s' k j) (fun p => tcb (pairMap p)) K := rfl
          _ ≤ Kakeya.maxDensity (s' k j) (fun p => tcb (pairMap p)) :=
                Kakeya.le_maxDensity _ _ _
      have h_joint_density := (h_clauses k j hj).2.2.2.2
      have h_rescale_inj :
          ((u k.succ).parent : Set ι).InjOn
            (fun i : ι => (u k.succ).parentTube i) :=
        (u k.succ).parentTube_injOn
      have h_inj_on_filter :
          ((P k.succ).filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody) :
            Set ι).InjOn
            (fun i : ι => (u k.succ).parentTube i) := by
        intro a ha b hb hab
        have ha' : a ∈ (u k.succ).parent := hP_sub k.succ (Finset.mem_filter.mp ha).1
        have hb' : b ∈ (u k.succ).parent := hP_sub k.succ (Finset.mem_filter.mp hb).1
        exact h_rescale_inj ha' hb' hab
      have h_max_dens_via_image :
          Kakeya.maxDensity (filt k j)
              (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) ≤
            Kakeya.maxDensity
              (((u k.succ).parent.image
                  (fun i => (u k.succ).parentTube i)).filter
                (fun w : Tube (ρ k.succ) E =>
                  w.toConvexSpaceBody ≤
                    ((u k.castSucc).parentTube j).toConvexSpaceBody))
              (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody) := by
        rw [Kakeya.maxDensity_le_iff]
        intro K
        have h_filter_image :
            (filt k j).image (fun i : ι => (u k.succ).parentTube i) ⊆
              ((u k.succ).parent.image
                (fun i : ι => (u k.succ).parentTube i)).filter
                (fun w : Tube (ρ k.succ) E =>
                  w.toConvexSpaceBody ≤
                    ((u k.castSucc).parentTube j).toConvexSpaceBody) := by
          intro w hw
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
          have hiP : i ∈ P k.succ := by
            rw [hfilt_def] at hi
            exact (Finset.mem_filter.mp hi).1
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_image_of_mem _ (hP_sub k.succ hiP), ?_⟩
          rw [hfilt_def] at hi
          exact (Finset.mem_filter.mp hi).2
        have h_num_eq :
            ∑ i ∈ (filt k j) with
                ((u k.succ).parentTube i).toConvexSpaceBody ≤ K,
                MeasureTheory.volume
                  ((u k.succ).parentTube i).toConvexSpaceBody.carrier =
              ∑ w ∈
                  ((filt k j).image
                      (fun i : ι => (u k.succ).parentTube i)).filter
                    (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody ≤ K),
                MeasureTheory.volume w.toConvexSpaceBody.carrier := by
          rw [Finset.filter_image]
          rw [Finset.sum_image]
          intro a ha b hb hab
          have h_inj_on_filtered :
              ((filt k j).filter (fun i : ι =>
                  ((u k.succ).parentTube i).toConvexSpaceBody ≤ K) :
                Set ι).InjOn
                (fun i : ι => (u k.succ).parentTube i) := by
            intro a' ha' b' hb' hab'
            have ha'' : a' ∈ (filt k j) := (Finset.mem_filter.mp ha').1
            have hb'' : b' ∈ (filt k j) := (Finset.mem_filter.mp hb').1
            exact h_inj_on_filter ha'' hb'' hab'
          exact h_inj_on_filtered ha hb hab
        calc Kakeya.densityIn (filt k j)
                (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) K
            = (∑ i ∈ (filt k j) with
                  ((u k.succ).parentTube i).toConvexSpaceBody ≤ K,
                MeasureTheory.volume
                  ((u k.succ).parentTube i).toConvexSpaceBody.carrier) /
                MeasureTheory.volume K.carrier := rfl
          _ = (∑ w ∈
                ((filt k j).image
                    (fun i : ι => (u k.succ).parentTube i)).filter
                  (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody ≤ K),
                MeasureTheory.volume w.toConvexSpaceBody.carrier) /
                MeasureTheory.volume K.carrier := by rw [h_num_eq]
          _ ≤ Kakeya.densityIn
                (((u k.succ).parent.image
                    (fun i : ι => (u k.succ).parentTube i)).filter
                  (fun w : Tube (ρ k.succ) E =>
                    w.toConvexSpaceBody ≤
                      ((u k.castSucc).parentTube j).toConvexSpaceBody))
                (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody) K := by
                  simp only [Kakeya.densityIn]
                  gcongr
          _ ≤ Kakeya.maxDensity
                (((u k.succ).parent.image
                    (fun i : ι => (u k.succ).parentTube i)).filter
                  (fun w : Tube (ρ k.succ) E =>
                    w.toConvexSpaceBody ≤
                      ((u k.castSucc).parentTube j).toConvexSpaceBody))
                (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody) :=
                Kakeya.le_maxDensity _ _ _
      have h_input := hInputDeltaMax k j hj
      have h_combined_children :
          Kakeya.maxDensity (filt k j)
              (fun i : ι => ((u k.succ).parentTube i).toConvexSpaceBody) ≤
            ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) :=
        le_trans h_max_dens_via_image h_input
      have h_ratio_nn : 0 ≤ ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε := by
        apply Real.rpow_nonneg
        exact div_nonneg (hρ_cs_pos k).le (hρ_succ_pos k).le
      have h_chain_density :
          Kakeya.maxDensity (s' k j)
              (fun a : ι × Fin (Jval k) => (hMap a).toConvexSpaceBody) ≤
            ENNReal.ofReal
              (K_53_out * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) := by
        have hδ_pow_nonneg : 0 ≤ (δ : ℝ) ^ (-(ε / (M : ℝ))) :=
          Real.rpow_nonneg hδ_pos_R.le _
        have hA_times_R_nonneg : 0 ≤ (δ : ℝ) ^ (-(ε / (M : ℝ))) *
            ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε := by
          nlinarith
        refine le_trans (by simpa [hMap_def] using h_joint_density.1) ?_
        refine ENNReal.ofReal_le_ofReal ?_
        calc C_dens * (K_53 * (δ : ℝ) ^ (-(ε / (M : ℝ)))) *
              (K_pack2 * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)
            = (C_dens * K_53 * K_pack2) *
                ((δ : ℝ) ^ (-(ε / (M : ℝ))) * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) := by ring
          _ ≤ K_53_out *
                ((δ : ℝ) ^ (-(ε / (M : ℝ))) * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) := by
            nlinarith
          _ = K_53_out * (δ : ℝ) ^ (-(ε / (M : ℝ))) *
                ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε := by ring
      exact h_image_le.trans h_chain_density
    · intro hx_le_one k
      have hceil : ⌈xval k⌉₊ ≤ 1 := by
        refine Nat.ceil_le.mpr ?_
        simpa [hxval_def] using hx_le_one k
      have hJ : Jval k = 1 := by
        simp only [hJval_def]
        omega
      change (((Finset.univ : Finset (Fin (Jval k))).image
                (fun j : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k j)).card) ≤ 1
      calc ((Finset.univ : Finset (Fin (Jval k))).image
              (fun j : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k j)).card
          ≤ (Finset.univ : Finset (Fin (Jval k))).card := Finset.card_image_le
        _ = Jval k := by simp
        _ = 1 := hJ
    · intro v v' hv hv' hsum
      have hpick : ∀ (w : Fin M → E), (∀ k : Fin M, w k ∈
          (Finset.univ : Finset (Fin (Jval k))).image
            (fun j : Fin (Jval k) => (ρ k.castSucc : ℝ) • ω₀ k j)) →
          ∃ j : ∀ k : Fin M, Fin (Jval k),
            ∀ k : Fin M, w k = (ρ k.castSucc : ℝ) • ω₀ k (j k) := by
        intro w hw
        choose j _ hj using fun k : Fin M => Finset.mem_image.mp (hw k)
        exact ⟨j, fun k => (hj k).symm⟩
      obtain ⟨j, hj⟩ := hpick v hv
      obtain ⟨j', hj'⟩ := hpick v' hv'
      have hsum' : (∑ k : Fin M, (ρ k.castSucc : ℝ) • ω₀ k (j k)) =
          ∑ k : Fin M, (ρ k.castSucc : ℝ) • ω₀ k (j' k) := by
        rw [← Finset.sum_congr rfl (fun k _ => hj k), ← Finset.sum_congr rfl (fun k _ => hj' k)]
        exact hsum
      have hjj' : j = j' := hω₀_sum_inj hsum'
      intro k
      rw [hj k, hj' k, hjj']
  obtain ⟨R, S, hNorm, hCardRk, hSub, hCount, hDensity, hSingletonIf, hDirect⟩ :=
    hR_construction
  exact ⟨R, S, hNorm, hCardRk, hSub, hCount, hDensity, hSingletonIf, hDirect⟩
end StickyKakeya

end Kakeya
