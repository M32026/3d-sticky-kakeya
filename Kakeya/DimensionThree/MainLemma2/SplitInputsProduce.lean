/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabSplit
public import Kakeya.DimensionThree.MainLemma2.AScaleRounding
public import Kakeya.DimensionThree.MainLemma2.SetupAbsorption

/-!
# Producing `SplitInputs` in the degenerate regime `a = b = δ` (side-data steps T8)

`Kakeya.VeryNotSticky.SplitInputs cfg bd` is the input bundle of the non-slab splitting at a
ball (`Kakeya.VeryNotSticky.nonslabSplitBound`). This file produces it — as far as the
configuration `cfg` and the ball datum `bd` allow — for the configurations the tree actually
builds, those of `Kakeya.VeryNotSticky.eventually_exists_config_of_slackCut` with
`cfg.a = cfg.b = cfg.δ`.

## What is produced from `cfg` and `bd`

* `uniform := cfg.splitHierarchy`, the tube hierarchy of the configuration's own Definition 2.2
  datum `cfg.uniform` (`gwz.txt` l.177-195), at `N = ⌈log log 1/δ⌉` and `Cu = cfg.C₀`.
* The level `k` with `ρ₂* ≤ δ^{k/N} ≤ δ^{-η} ρ₂*` (`Kakeya.VeryNotSticky.exists_splitLevel`):
  the rounding of `Kakeya.VeryNotSticky.exists_gridIndex` applied to `ρ₂* ∈ [a, 1]`, the range
  supplied by `Kakeya.VeryNotSticky.rho2Star_range`; at `b = δ` the non-slab hypothesis
  `b ≤ δ^{exscal} r₁` of that lemma is `δ ≤ δ^{2 exscal}`, i.e. `exscal ≤ 1/2`.
* `katzTao : cfg.KTScaleData cfg.ϱ` (`Kakeya.VeryNotSticky.ktScaleData_of_ckt`): the
  configuration's own coarse Katz–Tao window `cfg.ckt` read at the scale `ρ = τ = δ`. Its
  `WindowFour` bound carries the density factor `Δ_max^{1-β}`, which the Katz–Tao antecedent
  `Δ_max ≤ δ^{-η}` turns into `δ^{-η(1-β)}`; the loss exponents then satisfy
  `we + η(1-β) ≤ ϱ` from `hwe`, `hηbud` and `ϱ ≤ 1`, and the fullness thresholds
  `2η ≤ wη` from `hηKT`. No threshold on `δ` beyond the configuration's own is needed.
* `fibreConstant` (`Kakeya.VeryNotSticky.fibreConstant_of_threshold`): the absorption clause
  `cfg.aScaleData_absorb` bounds `C₀⁸ ≤ δ^{-η}` (`Kakeya.aScaleVolumeConstant C₀ D₀ ≥ C₀⁴`,
  `Kakeya.VeryNotSticky.coe_C₀_pow_eight_le_rpow_neg_eta`), so `Cu² = C₀² ≤ δ^{-η/4}`, and the
  remaining factor `(2 C_{lem:ml2bodyAngle}(bd.C₀))² ≤ δ^{-3η/4}` is a smallness condition on
  `δ` once `bd.C₀` is fixed before `δ`.
* `fibreCount`: one application of `Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le`.

## What is NOT produced here, and why — two obligations carried as binders

`Kakeya.VeryNotSticky.SplitInputs.ofLevel` packages the structure from its fields; the
`∀ᶠ` entry point `Kakeya.VeryNotSticky.eventually_exists_splitInputs_degenerate` discharges
every field from `cfg`, `bd` and thresholds on `δ`, **except** two, which it takes as
hypotheses stated byte-for-byte as the fields (at `uniform := cfg.splitHierarchy` and the
produced level `k`):

1. `Ccnt`, `countConstant`, `fibreScaleCount : ρ₂^{-2-ζ} ≤ Ccnt · |𝕋_{ρ₂*}|` with
   `Ccnt ≤ δ^{-18η}`.
   The only count the configuration carries is `cfg.rho_count`: an essentially distinct, all-used family of
   `ρ`-tubes for the *parent* family `sPar ⊇ cfg.s`, together — since F12b — with the parent's
   uniform hierarchy at `1 ≤ Cpar ≤ δ^{-η}` and the retention `δ^{2η}|sPar| ≤ |cfg.s|`, which
   close gap 1.
   Three independent gaps separated the earlier, **δ-free** form of the clause from that datum:
   the parent family's tubes need not lie in any node of `cfg.s`'s hierarchy;
   the count's constant `C₀` had no room in `(2 C_{lem:ml2bodyAngle})²`; and the level `k`
   sits at `ρ_k ∈ [ρ₂*, δ^{-η} ρ₂*]`, so a comparison of `ρ₂`-tubes
   with `ρ_k`-nodes costs `(ρ_k/ρ₂)^{2}` times a dimensional cover-comparison constant, at least
   `(2 C_{lem:ml2bodyAngle})² · δ^{-2η} · Tube.coverCountLoss 3`, against the old form's bare
   `(2 C_{lem:ml2bodyAngle})²`. At `a = b = δ` the count window's finest scale is `ρ₂` itself
   (`Kakeya.VeryNotSticky.rho2_range`), so no finer count is available to pay for the rounding.
   The δ-free constant was the exact-scale idealisation of blueprint `lem:ml2tubeScaleCompare`
   and  measured it as unreachable from the configuration; `Ccnt`/`countConstant`
   is what pays for all three gaps, and
   `Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` closes the clause at the
   measured `M = 18`. The clause remains a binder here because that producer imports this
   module.
2. `Cang`, `angularConstant`, `angularFibre_le_fibreMult`. The derivation sketched in  (e) needs, as its step (i), that
   the tubes of an angular fibre `{T ∈ 𝕋_Y(x) : ∠(T, v) ≤ ρ₂*}` lie in boundedly many nodes of
   the level `k`, by covering the `ρ₂*`-cone through `x` with `O(1)` tubes of radius `ρ_k`
   and applying `Tube.UniformTubeSet.boundedOverlap`. **That cover does not exist in this
   tree's model of a tube.** A `Tube` has length exactly one (`Tube.dist_eq_one`), and the
   `δ`-tubes through `x` with a common direction are parametrised by their axial position; two
   of them shifted by `1/2` lie in no common `ρ`-tube for `ρ < 1/4`
   (`Kakeya.VeryNotSticky.two_shifted_tubes_not_in_common_tube` below), so a family of `n`
   equally shifted tubes through `x` needs `n` covering tubes, and `n` may be of size `1/ρ_k`.
   GWZ do not meet this because Definition 2.1(ii) makes the *parents* `𝕋_ρ` essentially
   distinct, which forces the parents through `x` with a common direction to be `O(1)` in
   number; `Tube.UniformTubeSet` deliberately replaced that clause by `boundedOverlap`
   (Uniform.lean), which bounds the nodes meeting a *given* `ρ_k`-tube and says nothing about
   the nodes through a point. Consequently the number of nodes an angular fibre meets is not
   controlled by `cfg.uniform`, and the field cannot be derived from it: additional control of the nodes, such as the relevant consequence of GWZ Definition 2.1(ii), is needed.

Nothing in this file weakens, restates or adds a hypothesis to any existing declaration.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace Kakeya.VeryNotSticky

universe u

/-! ### The hierarchy of the configuration's own uniformity datum -/

/-- The tube hierarchy of the configuration's Definition 2.2 datum `cfg.uniform`, at the grid
length `Tube.ssfGridLen cfg.δ` and the constant `cfg.C₀`. This is the `uniform` field a
`SplitInputs` built here carries. -/
noncomputable def splitHierarchy (cfg : VeryNotSticky.{u}) :
    Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀ :=
  cfg.uniform.some.tubeUniform

/-! ### The level `k` at the dilated angular scale `ρ₂*` -/

/-- **The grid level at `ρ₂*`, two-sided**. In the degenerate regime `b = δ`
the non-slab hypothesis `b ≤ δ^{exscal} r₁` of `Kakeya.VeryNotSticky.rho2Star_range` reads
`δ ≤ δ^{2 exscal}`, which is `exscal ≤ 1/2`; that lemma places `ρ₂*` in `[δ, 1] ⊆ [a, 1]`, and
`Kakeya.VeryNotSticky.exists_gridIndex` rounds it up to a grid scale at the cost `δ^{-η}`
(`cfg.gridFine`). The threshold `hscale` is a smallness condition on `δ` once `C₀` is fixed. -/
theorem exists_splitLevel (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hexscal : cfg.exscal ≤ 1 / 2)
    (hscale : cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant C₀)⁻¹)
    (hb : cfg.b = cfg.δ) :
    ∃ k ≤ Tube.ssfGridLen cfg.δ,
      cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀ := by
  have hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
    rw [hb]
    unfold r₁
    rw [← NNReal.rpow_add cfg.hδ.ne']
    calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (cfg.exscal + cfg.exscal) :=
        NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith)
  obtain ⟨hδρ, -, hρ1⟩ := rho2Star_range cfg cfg.hδ cfg.hδ1 hC₀ hscale hnotslab
  have ha : cfg.a ≤ cfg.rho2Star C₀ :=
    le_trans (cfg.hdims.2.1.trans hb.le) (hδρ.trans (rho2_le_rho2Star cfg hC₀))
  exact exists_gridIndex cfg ha hρ1

/-! ### `K_KT(β)` at the scale `δ`, from the configuration's coarse window -/

/-- Two shaded families that agree on `s` have the same fullness on `s`. -/
theorem fullness_congr_of_eqOn {ι : Type*} (s : Finset ι)
    {V W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} (h : ∀ i ∈ s, V i = W i) :
    ShadedBody.fullness s V = ShadedBody.fullness s W := by
  have h1 : ∑ i ∈ s, volume (V i).shade = ∑ i ∈ s, volume (W i).shade :=
    Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]
  have h2 : ∑ i ∈ s, volume (V i).carrier = ∑ i ∈ s, volume (W i).carrier :=
    Finset.sum_congr rfl fun i hi ↦ by rw [h i hi]
  unfold ShadedBody.fullness ShadedBody.fullness'
  rw [h1, h2]

/-- **`K_KT(β)` at the fixed scale `δ` with loss `ϱ`, from the coarse Katz–Tao window**
(field `katzTao` of `Kakeya.VeryNotSticky.SplitInputs`; blueprint `lem:ml2ktScaleDataAvail`).

The configuration's field `cfg.ckt` carries `Kakeya.WindowFour cfg.β we wη wρ` (the windowed
Katz–Tao multiplicity bound of `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`
at radius `4`) together with `6 δ^{exscal-η} ≤ wρ`, `3η ≤ exscal · wη` and
`3η ≤ exscal · we ≤ exscal · ϱ² wb / 1440`. Read at `ρ = τ = δ`, for a subfamily `s' ⊆ 𝕋` with
`Δ_max ≤ δ^{-η}` and `λ ≥ δ^{2η}`, it gives
`μ ≤ δ^{-we} · Δ_max^{1-β} · |s'|^β ≤ δ^{-(we + η(1-β))} |s'|^β ≤ δ^{-ϱ} |s'|^β`,
the last step because `we + η(1-β) ≤ we + η ≤ (7/6) we ≤ ϱ/1000` once `ϱ ≤ 1` and
`exscal ≤ 1/2`. The window asks for every tube of the *indexed family* to lie in `B(0, 4)`,
not only those of `s'`; the family is therefore re-indexed to agree with `𝕋` on `s'` and to
repeat one tube of `𝕋` elsewhere (`Kakeya.multiplicity_eq_of_eqOn`, `maxDensity_congr`). -/
theorem ktScaleData_of_ckt (cfg : VeryNotSticky.{u}) (hexscal : cfg.exscal ≤ 1 / 2)
    (hϱ1 : cfg.ϱ ≤ 1) : cfg.KTScaleData cfg.ϱ := by
  classical
  intro s' hs' hKT hfull
  obtain ⟨i₀, hi₀⟩ := s_nonempty cfg
  -- the re-indexed family: `𝕋` on `s`, one tube of `𝕋` off `s`
  obtain ⟨T'', hT'', hball⟩ : ∃ T'' : cfg.ι → ShadedTube cfg.δ (EuclideanSpace ℝ (Fin 3)),
      (∀ i ∈ s', T'' i = cfg.T i) ∧
        ∀ i, (T'' i).carrier ⊆ Metric.closedBall 0 (4 : ℝ) := by
    refine ⟨fun i ↦ if i ∈ cfg.s then cfg.T i else cfg.T i₀, fun i hi ↦ by simp [hs' hi], ?_⟩
    intro i
    refine Set.Subset.trans ?_ (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 4))
    by_cases hi : i ∈ cfg.s
    · simpa [hi] using cfg.contained i hi
    · simpa [hi] using cfg.contained i₀ hi₀
  -- the scale `δ` is below the window radius
  have hδwρ : cfg.δ ≤ cfg.ckt.wρ := by
    have h1 : cfg.δ ≤ cfg.δ ^ (cfg.exscal - cfg.η) := by
      calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
        _ ≤ cfg.δ ^ (cfg.exscal - cfg.η) :=
          NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 (by linarith [cfg.hη])
    calc cfg.δ ≤ cfg.δ ^ (cfg.exscal - cfg.η) := h1
      _ ≤ 6 * cfg.δ ^ (cfg.exscal - cfg.η) :=
          le_mul_of_one_le_left (by positivity) (by norm_num)
      _ ≤ cfg.ckt.wρ := cfg.ckt.hδrad
  -- the fullness threshold: `2η ≤ wη`
  have h2η : 2 * cfg.η ≤ cfg.ckt.wη := by
    have h := cfg.ckt.hηKT
    have h' : cfg.exscal * cfg.ckt.wη ≤ (1 / 2) * cfg.ckt.wη :=
      mul_le_mul_of_nonneg_right hexscal cfg.ckt.hwη.le
    linarith [cfg.hη]
  have hfull'' : ShadedBody.fullness s' (fun i ↦ (T'' i).toShadedBody) ≥ cfg.δ ^ cfg.ckt.wη := by
    rw [fullness_congr_of_eqOn s' (fun i hi ↦ by rw [hT'' i hi])]
    exact le_trans (NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 h2η) hfull
  have hw := cfg.ckt.hwin
  unfold Kakeya.WindowFour at hw
  have hmult := hw cfg.δ cfg.hδ hδwρ cfg.δ cfg.hδ le_rfl s' T'' hball hfull''
  rw [Kakeya.multiplicity_eq_of_eqOn _ s' (fun i hi ↦ by rw [hT'' i hi]),
    maxDensity_congr (fun i hi ↦ by rw [hT'' i hi])] at hmult
  -- the density factor and the exponent budget
  have hmd : maxDensity s' (fun i ↦ (cfg.T i).toConvexSpaceBody) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) := hKT
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1 : (cfg.δ : ENNReal) ≤ 1 := by exact_mod_cast cfg.hδ1
  have hmdpow : maxDensity s' (fun i ↦ (cfg.T i).toConvexSpaceBody) ^ (1 - cfg.β) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.η * (1 - cfg.β))) := by
    calc maxDensity s' (fun i ↦ (cfg.T i).toConvexSpaceBody) ^ (1 - cfg.β)
        ≤ ((cfg.δ : ENNReal) ^ (-cfg.η)) ^ (1 - cfg.β) :=
          ENNReal.rpow_le_rpow hmd (by linarith [cfg.hβ1])
      _ = (cfg.δ : ENNReal) ^ (-(cfg.η * (1 - cfg.β))) := by
          rw [← ENNReal.rpow_mul]; congr 1; ring
  have hexp : cfg.ckt.we + cfg.η * (1 - cfg.β) ≤ cfg.ϱ := by
    have hwe := cfg.ckt.hwe
    have hwb := cfg.ckt.hwb
    have hwb0 := cfg.ckt.hwb0
    have hbud := cfg.ckt.hηbud
    have hwe0 := cfg.ckt.hwe0
    have hϱ := cfg.hϱ
    have hβ1 := cfg.hβ1
    have hβ := cfg.hβ
    have hη := cfg.hη
    have h1 : cfg.ϱ ^ 2 * cfg.ckt.wb ≤ cfg.ϱ := by
      nlinarith [mul_le_mul_of_nonneg_left (hwb.trans hβ1) (sq_nonneg cfg.ϱ),
        mul_le_mul_of_nonneg_left hϱ1 hϱ.le]
    have h2 : cfg.exscal * cfg.ckt.we ≤ (1 / 2) * cfg.ckt.we :=
      mul_le_mul_of_nonneg_right hexscal hwe0.le
    have h3 : cfg.η * (1 - cfg.β) ≤ cfg.η :=
      mul_le_of_le_one_right hη.le (by linarith)
    linarith
  calc ShadedBody.multiplicity s' (fun i ↦ (cfg.T i).toShadedBody)
      ≤ (cfg.δ : ENNReal) ^ (-cfg.ckt.we) *
          maxDensity s' (fun i ↦ (cfg.T i).toConvexSpaceBody) ^ (1 - cfg.β) *
          (s'.card : ENNReal) ^ cfg.β := hmult
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.ckt.we) *
          (cfg.δ : ENNReal) ^ (-(cfg.η * (1 - cfg.β))) * (s'.card : ENNReal) ^ cfg.β := by
        gcongr
    _ = (cfg.δ : ENNReal) ^ (-(cfg.ckt.we + cfg.η * (1 - cfg.β))) *
          (s'.card : ENNReal) ^ cfg.β := by
        rw [← ENNReal.rpow_add _ _ hδ0 hδtop]; congr 2; ring
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.ϱ) * (s'.card : ENNReal) ^ cfg.β :=
        mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith)) le_rfl

/-! ### The fibre-constant threshold -/

/-- **`C₀⁸ ≤ δ^{-η}`**: the absorption clause `cfg.aScaleData_absorb` bounds the square of
`Kakeya.aScaleDataConstant C₀ D₀ ≥ Kakeya.aScaleVolumeConstant C₀ D₀ = C₀⁴ D₀ / c²` with
`c = Kakeya.tubeVolumeRatioConstant 3 ≤ 1` and `D₀ ≥ 1`. Sharpens
`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta` (which reads off `C₀ ≤ δ^{-η}` from the same
clause) to the eighth power. -/
theorem coe_C₀_pow_eight_le_rpow_neg_eta (cfg : VeryNotSticky.{u}) :
    (cfg.C₀ : ENNReal) ^ 8 ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have ht : 0 < tubeVolumeRatioConstant 3 := tubeVolumeRatioConstant_pos 3
  have ht1 : tubeVolumeRatioConstant 3 ≤ 1 := tubeVolumeRatioConstant_three_le_one
  have hdm : cfg.C₀ ^ 2 ≤ deltamaxScaleAConstant cfg.C₀ cfg.D₀ := by
    unfold deltamaxScaleAConstant
    rw [le_div_iff₀ ht]
    calc cfg.C₀ ^ 2 * tubeVolumeRatioConstant 3 ≤ cfg.C₀ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ ≤ cfg.C₀ ^ 2 * cfg.D₀ := mul_le_mul_of_nonneg_left cfg.hD₀ (by positivity)
  have hvol : cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ ≤
      aScaleVolumeConstant cfg.C₀ cfg.D₀ := by
    unfold aScaleVolumeConstant
    rw [le_div_iff₀ ht]
    exact mul_le_of_le_one_right (by positivity) ht1
  have h4 : cfg.C₀ ^ 4 ≤ aScaleDataConstant cfg.C₀ cfg.D₀ := by
    calc cfg.C₀ ^ 4 = cfg.C₀ ^ 2 * cfg.C₀ ^ 2 := by ring
      _ ≤ cfg.C₀ ^ 2 * deltamaxScaleAConstant cfg.C₀ cfg.D₀ :=
          mul_le_mul_of_nonneg_left hdm (by positivity)
      _ ≤ aScaleVolumeConstant cfg.C₀ cfg.D₀ := hvol
      _ ≤ aScaleDataConstant cfg.C₀ cfg.D₀ := aScaleVolumeConstant_le_aScaleDataConstant _ _
  have h8 : cfg.C₀ ^ 8 ≤ aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 := by
    calc cfg.C₀ ^ 8 = (cfg.C₀ ^ 4) ^ 2 := by ring
      _ ≤ aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
  calc (cfg.C₀ : ENNReal) ^ 8 = ((cfg.C₀ ^ 8 : NNReal) : ENNReal) := by push_cast; rfl
    _ ≤ ((aScaleDataConstant cfg.C₀ cfg.D₀ ^ 2 : NNReal) : ENNReal) := by exact_mod_cast h8
    _ = (aScaleDataConstant cfg.C₀ cfg.D₀ : ENNReal) ^ 2 := by push_cast; rfl
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := cfg.aScaleData_absorb

/-- `C₀² ≤ δ^{-η/4}`, the fourth root of `Kakeya.VeryNotSticky.coe_C₀_pow_eight_le_rpow_neg_eta`. -/
theorem coe_C₀_sq_le_rpow_neg_quarter_eta (cfg : VeryNotSticky.{u}) :
    (cfg.C₀ : ENNReal) ^ 2 ≤ (cfg.δ : ENNReal) ^ (-(cfg.η / 4)) := by
  have h := ENNReal.rpow_le_rpow (coe_C₀_pow_eight_le_rpow_neg_eta cfg)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hl : ((cfg.C₀ : ENNReal) ^ 8) ^ ((1 : ℝ) / 4) = (cfg.C₀ : ENNReal) ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hr : ((cfg.δ : ENNReal) ^ (-cfg.η)) ^ ((1 : ℝ) / 4) =
      (cfg.δ : ENNReal) ^ (-(cfg.η / 4)) := by
    rw [← ENNReal.rpow_mul]; congr 1; ring
  rwa [hl, hr] at h

/-- **The fibre-constant threshold**: `C₀² ≤ δ^{-η/4}`
from the configuration, and `(2 C_{lem:ml2bodyAngle}(C₀'))² ≤ δ^{-3η/4}` as a threshold on
`δ`, which `Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg` arranges once `C₀'` (the ball
datum's constant) is fixed before `δ`. -/
theorem fibreConstant_of_threshold (cfg : VeryNotSticky.{u}) {C₀ : NNReal}
    (hthr : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 4))) :
    ((cfg.C₀ : ENNReal) ^ 2) * ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) := by
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by exact_mod_cast cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc ((cfg.C₀ : ENNReal) ^ 2) * ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2
      ≤ (cfg.δ : ENNReal) ^ (-(cfg.η / 4)) * (cfg.δ : ENNReal) ^ (-(3 * cfg.η / 4)) :=
        mul_le_mul' (coe_C₀_sq_le_rpow_neg_quarter_eta cfg) hthr
    _ = (cfg.δ : ENNReal) ^ (-cfg.η) := by
        rw [← ENNReal.rpow_add _ _ hδ0 hδtop]; congr 1; ring

/-! ### The structure, from its fields -/

/-- **`SplitInputs` from a level of a hierarchy and the remaining clauses.** The field
`fibreCount` is discharged by `Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le`; every other field is taken as given, with the text of the field. The
two clauses this file cannot produce from the configuration — the count clause
`Ccnt`/`countConstant`/`fibreScaleCount` and the angular clause
`Cang`/`angularConstant`/`angularFibre_le_fibreMult` — enter here as binders (see the module
docstring). The count binders are placed last so that the `∀`-tail of
`Kakeya.VeryNotSticky.eventually_exists_splitInputs_degenerate` mirrors the `∀ Cang` shape. -/
def SplitInputs.ofLevel (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {N : ℕ} {Cu : NNReal}
    (uniform : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N Cu) {k : ℕ}
    (k_le : k ≤ N)
    (gridScale_ge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ N k)
    (gridScale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀)
    (katzTao : cfg.KTScaleData cfg.ϱ)
    (fibreConstant : ((Cu : ENNReal) ^ 2) *
        ((2 * NonSlab.bodyAngleConstant bd.C₀ : NNReal) : ENNReal) ^ 2 ≤
      (cfg.δ : ENNReal) ^ (-cfg.η))
    (Cang : NNReal)
    (angularConstant : (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    (angularFibre_le_fibreMult : ∀ j ∈ cfg.activeTubeNodes uniform k,
      ∀ x v : EuclideanSpace ℝ (Fin 3),
        (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
          (Cang : ENNReal) *
            ShadedBody.multiplicity (cfg.tubeFibre uniform k j)
              (fun i ↦ (cfg.T i).toShadedBody))
    (Ccnt : NNReal)
    (countConstant : (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)))
    (fibreScaleCount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
      (Ccnt : ℝ) * ((uniform.cover.indexSet k).card : ℝ)) :
    SplitInputs cfg bd where
  N := N
  Cu := Cu
  uniform := uniform
  k := k
  k_le := k_le
  gridScale_ge := gridScale_ge
  gridScale_le := gridScale_le
  katzTao := katzTao
  fibreConstant := fibreConstant
  fibreCount := cfg.card_indexSet_mul_card_tubeFibre_le uniform k k_le
  Ccnt := Ccnt
  countConstant := countConstant
  fibreScaleCount := fibreScaleCount
  Cang := Cang
  angularConstant := angularConstant
  angularFibre_le_fibreMult := angularFibre_le_fibreMult

/-! ### The degenerate-regime entry point -/

/-- **`SplitInputs` in the degenerate regime, up to two obligations**.

For all small `δ`, every configuration `cfg` at the fixed parameters `(η, exscal, ϱ)` with
`cfg.b = cfg.δ` (as `Kakeya.VeryNotSticky.eventually_exists_config_of_slackCut` produces it)
and every ball datum `bd` with `bd.C₀ = C₀` carry a level `k` of the configuration's own
hierarchy `cfg.splitHierarchy` sitting at `ρ₂*` two-sidedly, and a `SplitInputs cfg bd` on that
hierarchy and level **once the two clauses below are supplied for them**:

* the angular clause `Cang`/`angularConstant`/`angularFibre_le_fibreMult`, and
* the count clause `Ccnt`/`countConstant`/`fibreScaleCount` (the count's constant is carried at `Ccnt ≤ δ^{-18η}`, and is no longer the δ-free
  `(2 C_{lem:ml2bodyAngle}(C₀))²` that  measured as unreachable from `cfg`),

each stated exactly as the field, at `uniform := cfg.splitHierarchy`. Everything else —
`N`, `Cu`, `uniform`, `k`, `k_le`, `gridScale_ge`, `gridScale_le`, `katzTao`, `fibreConstant`,
`fibreCount` — is discharged here from `cfg`, `bd` and the two thresholds
`δ^{exscal} ≤ (2 C_{lem:ml2bodyAngle}(C₀))⁻¹` and `(2 C_{lem:ml2bodyAngle}(C₀))² ≤ δ^{-3η/4}`.
The module docstring records why the two clauses are not produced from `cfg.uniform`.

The fixed-parameter hypotheses are those of `Kakeya.VeryNotSticky.CaseParams`:
`exscal ≤ 1/2` is `scale`, `ϱ ≤ 1` follows from `slabBias` (`2^20 ϱ < exscal < 1/2`), and
`1 ≤ C₀` is `Kakeya.VeryNotSticky.BallData.hC₀` (the T3 producer takes `4 ≤ C₀`). -/
theorem eventually_exists_splitInputs_degenerate (C₀ : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal ϱ η : ℝ} (hη : 0 < η) (hexscal0 : 0 < exscal) (hexscal : exscal ≤ 1 / 2)
    (hϱ1 : ϱ ≤ 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
        cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → bd.C₀ = C₀ →
        cfg.b = cfg.δ →
        ∃ k ≤ Tube.ssfGridLen cfg.δ,
          cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ∧
          Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ ∧
          ∀ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) →
            (∀ j ∈ cfg.activeTubeNodes cfg.splitHierarchy k,
              ∀ x v : EuclideanSpace ℝ (Fin 3),
                (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                  (Cang : ENNReal) *
                    ShadedBody.multiplicity (cfg.tubeFibre cfg.splitHierarchy k j)
                      (fun i ↦ (cfg.T i).toShadedBody)) →
            ∀ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) →
              (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
                (Ccnt : ℝ) * ((cfg.splitHierarchy.cover.indexSet k).card : ℝ) →
              Nonempty (SplitInputs cfg bd) := by
  have hpos : (0 : NNReal) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant C₀ :=
      one_le_mul_of_one_le_of_one_le (by norm_num) (NonSlab.one_le_bodyAngleConstant hC₀)
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one h1)
  have hKtop : ((2 * NonSlab.bodyAngleConstant C₀ : NNReal) : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.coe_ne_top
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hpos hexscal0,
    eventually_ennreal_le_rpow_neg hKtop (by positivity : (0 : ℝ) < 3 * η / 4)]
    with d hscale hthr
  intro cfg bd hδ hη' hexs hϱ' hC₀' hb
  subst hδ hη' hexs hϱ' hC₀'
  rw [one_mul] at hscale
  obtain ⟨k, hk, hge, hle⟩ := exists_splitLevel cfg hC₀ hexscal hscale hb
  refine ⟨k, hk, hge, hle, fun Cang hCang hang Ccnt hCcnt hfsc ↦ ?_⟩
  exact ⟨SplitInputs.ofLevel cfg bd cfg.splitHierarchy hk hge hle
    (ktScaleData_of_ckt cfg hexscal hϱ1) (fibreConstant_of_threshold cfg hthr)
    Cang hCang hang Ccnt hCcnt hfsc⟩

/-! ### Why the angular clause is not derived here: no `O(1)` cover of a cone by unit tubes

The derivation of `angularFibre_le_fibreMult` sketched in  (e) rests on covering the
`δ`-tubes through a point `x` within angle `ρ₂*` of a direction by `O(1)` tubes of radius
`ρ_k ≥ ρ₂*`, so that `Tube.UniformTubeSet.boundedOverlap` bounds the nodes they meet. In this
tree a `Tube` has length exactly `1`, and the tubes through `x` with a *common* direction differ
by their axial position: the two below, shifted by `1/2`, lie in no common `ρ`-tube for
`ρ < 1/4`. So the number of covering tubes grows with the number of axial positions, which
`cfg.uniform` does not bound; the clause is a statement question, not a proof steps. -/

/-- Two unit `δ`-tubes through `x` with the same direction `v`, shifted by `1/2` along it, are
contained in no common `ρ`-tube when `ρ < 1/4`: the union of their cores has diameter `3/2`,
while a `ρ`-tube has diameter at most `1 + 2ρ`
(`Kakeya.Tube.carrier_subset_closedBall_midpoint`). -/
theorem two_shifted_tubes_not_in_common_tube {δ ρ : NNReal} (hρ : (ρ : ℝ) < 1 / 4)
    (x v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ∃ T₀ T₁ : Tube δ (EuclideanSpace ℝ (Fin 3)),
      x ∈ T₀.carrier ∧ x ∈ T₁.carrier ∧ T₀.direction = T₁.direction ∧
        ¬ ∃ V : Tube ρ (EuclideanSpace ℝ (Fin 3)),
          T₀.toConvexSpaceBody ≤ V.toConvexSpaceBody ∧
            T₁.toConvexSpaceBody ≤ V.toConvexSpaceBody := by
  have h0 : dist (x - (1 / 2 : ℝ) • v) (x + (1 / 2 : ℝ) • v) = 1 := by
    rw [dist_eq_norm, show x - (1 / 2 : ℝ) • v - (x + (1 / 2 : ℝ) • v) = -v by module,
      norm_neg, hv]
  have h1 : dist x (x + v) = 1 := by
    rw [dist_eq_norm, show x - (x + v) = -v by module, norm_neg, hv]
  refine ⟨Tube.mk' δ h0, Tube.mk' δ h1, ?_, ?_, ?_, ?_⟩
  · -- `x` is the midpoint of the first core
    change x ∈ ⋃ z ∈ segment ℝ (x - (1 / 2 : ℝ) • v) (x + (1 / 2 : ℝ) • v), Metric.closedBall z δ
    refine Set.mem_iUnion₂.mpr ⟨x, ?_, Metric.mem_closedBall_self δ.coe_nonneg⟩
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  · exact Tube.x_mem_carrier (Tube.mk' δ h1)
  · change (x + (1 / 2 : ℝ) • v) - (x - (1 / 2 : ℝ) • v) = (x + v) - x
    module
  · rintro ⟨V, hV0, hV1⟩
    have hx0 : x - (1 / 2 : ℝ) • v ∈ V.carrier :=
      SetLike.le_def.mp hV0 (Tube.x_mem_carrier (Tube.mk' δ h0))
    have hy1 : x + v ∈ V.carrier := SetLike.le_def.mp hV1 (Tube.y_mem_carrier (Tube.mk' δ h1))
    have hb0 := Tube.carrier_subset_closedBall_midpoint _ V hx0
    have hb1 := Tube.carrier_subset_closedBall_midpoint _ V hy1
    rw [Metric.mem_closedBall] at hb0 hb1
    have hd : dist (x - (1 / 2 : ℝ) • v) (x + v) = 3 / 2 := by
      rw [dist_eq_norm, show x - (1 / 2 : ℝ) • v - (x + v) = -((3 / 2 : ℝ) • v) by module,
        norm_neg, norm_smul, hv]
      norm_num
    have htri := dist_triangle_right (x - (1 / 2 : ℝ) • v) (x + v) (midpoint ℝ V.x V.y)
    linarith

end Kakeya.VeryNotSticky
