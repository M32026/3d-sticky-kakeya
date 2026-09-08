/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase

@[expose] public section

open Filter Topology MeasureTheory

namespace Kakeya.VeryNotSticky

universe u

/-- A finite constant times a higher power of a small scale is eventually bounded by a
lower power. This is the common absorption step in the slab and non-slab scale bundles. -/
theorem eventually_ennreal_mul_rpow_le_rpow {K : ENNReal} (hK : K ≠ ⊤)
    {p q : Real} (hqp : q < p) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, K * (d : ENNReal) ^ p ≤ (d : ENNReal) ^ q := by
  have hgap : 0 < p - q := sub_pos.mpr hqp
  filter_upwards [ENNReal.eventually_coe_rpow_le_of_pos hgap
      (show 0 < K⁻¹ by simpa using ENNReal.inv_pos.mpr hK), self_mem_nhdsWithin]
      with d hd hd0
  have hdne : (d : ENNReal) ≠ 0 := by simpa using ne_of_gt hd0
  have hdtop : (d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hKK : K * K⁻¹ ≤ 1 := by
    by_cases hK0 : K = 0
    · simp [hK0]
    · rw [ENNReal.mul_inv_cancel hK0 hK]
  calc
    K * (d : ENNReal) ^ p
        = (K * (d : ENNReal) ^ (p - q)) * (d : ENNReal) ^ q := by
            rw [mul_assoc, ← ENNReal.rpow_add (p - q) q hdne hdtop]
            congr 2
            ring
    _ ≤ (K * K⁻¹) * (d : ENNReal) ^ q := by gcongr
    _ ≤ 1 * (d : ENNReal) ^ q := by gcongr
    _ = (d : ENNReal) ^ q := one_mul _

/-- Two fixed finite constants can be absorbed together without first choosing a larger
`NNReal` comparison constant. -/
theorem eventually_ennreal_mul_mul_rpow_le_rpow {K L : ENNReal}
    (hK : K ≠ ⊤) (hL : L ≠ ⊤) {p q : Real} (hqp : q < p) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      K * L * (d : ENNReal) ^ p ≤ (d : ENNReal) ^ q := by
  exact eventually_ennreal_mul_rpow_le_rpow (ENNReal.mul_ne_top hK hL) hqp

/-- The three fixed-scale power absorptions of `SlabScale` hold simultaneously once the three
comparison factors have fixed finite upper bounds. -/
theorem eventually_slabScale_power_bounds {beta exscal eta rho tau : Real}
    (hdensity hanti hfinal : ENNReal)
    (hdensity_top : hdensity ≠ ⊤) (hanti_top : hanti ≠ ⊤)
    (hfinal_top : hfinal ≠ ⊤)
    (hdensity_gap : 6 * eta < exscal)
    (hanti_gap : 2 * rho < exscal)
    (hfinal_gap : 12 * eta + 12 * exscal + 3 * tau < beta / 2) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
        hdensity * (d : ENNReal) ^ exscal ≤ (d : ENNReal) ^ (6 * eta) ∧
        hanti * (d : ENNReal) ^ exscal ≤ (d : ENNReal) ^ (2 * rho) ∧
        hfinal * (d : ENNReal) ^ (beta / 2) ≤
          (d : ENNReal) ^ (12 * eta + 12 * exscal + 3 * tau) := by
  filter_upwards [eventually_ennreal_mul_rpow_le_rpow hdensity_top hdensity_gap,
    eventually_ennreal_mul_rpow_le_rpow hanti_top hanti_gap,
    eventually_ennreal_mul_rpow_le_rpow hfinal_top hfinal_gap] with d h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- Uniform fixed bounds for the three comparison factors produce the complete `SlabScale`
bundle for every sufficiently small configuration. The configuration and its ball/thin data may
depend on the scale; only the displayed comparison factors must share fixed bounds. The
fibre-count budget `Cm · m ≤ fibreMassConstant · δ^{-(η+2 exscal)}` of `SlabScale.fibreMass` is
a bound on a datum of `bd`, not on a `δ`-free constant, so it is passed through as a hypothesis
. The `final` factor
carries `fibreMassConstant`, the thin-case constant `C` and the dilation constant `Cdil` of the
repaired (T7) and (C3). -/
theorem eventually_slabScale_of_uniform_bounds {beta exscal eta rho tau : Real}
    (hdensity hanti hfinal : ENNReal)
    (hdensity_top : hdensity ≠ ⊤) (hanti_top : hanti ≠ ⊤)
    (hfinal_top : hfinal ≠ ⊤)
    (hdensity_gap : 6 * eta < exscal)
    (hanti_gap : 2 * rho < exscal)
    (hfinal_gap : 12 * eta + 12 * exscal + 3 * tau < beta / 2) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky) (bd : BallData cfg) (tc : ThinConfig cfg bd),
        cfg.δ = d → cfg.β = beta → cfg.exscal = exscal → cfg.η = eta → cfg.ϱ = rho →
        (tc.C : ENNReal) * (slabInputsConstant bd.C₀ : ENNReal) ≤ hdensity →
        (slabInputsConstant bd.C₀ : ENNReal) * (bd.Cbias : ENNReal) ≤ hanti →
        (fibreMassConstant : ENNReal) * (tc.C : ENNReal) * (bd.Cdil : ENNReal) *
          (slabUnionConstant tc.C bd.C₀ cfg.exscal : ENNReal) ≤ hfinal →
        (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
          (fibreMassConstant : ENNReal) *
            (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) →
        SlabScale cfg bd tc tau := by
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [eventually_slabScale_power_bounds hdensity hanti hfinal hdensity_top
      hanti_top hfinal_top hdensity_gap hanti_gap hfinal_gap, hsmall] with d hpowers hd1
  intro cfg bd tc hdelta hbeta he heta hrho hden hanti hfin hfib
  constructor
  · simpa [hdelta] using hd1
  · rw [hdelta, he, heta]
    exact le_trans (mul_le_mul_right' hden ((d : ENNReal) ^ exscal)) hpowers.1
  · rw [hdelta, he, hrho]
    exact le_trans (mul_le_mul_right' hanti ((d : ENNReal) ^ exscal)) hpowers.2.1
  · rw [hdelta, hbeta, he, heta]
    rw [he] at hfin
    exact le_trans (mul_le_mul_right' hfin ((d : ENNReal) ^ (beta / 2))) hpowers.2.2
  · exact hfib


/-! ### Scalar workhorses

The `ℝ≥0` and `ℝ` companions of `Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow`.
Every fixed-scale clause of Configuration `hyp:ml2scale` is one of the four shapes below, so
the whole arithmetic half of `Kakeya.VeryNotSticky.exists_setup_caseSideData` reduces to them.
-/

/-- `ℝ≥0` form of `Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow`. -/
theorem eventually_nnreal_mul_rpow_le_rpow (K : NNReal) {p q : Real} (hqp : q < p) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, K * d ^ p ≤ d ^ q := by
  filter_upwards [eventually_ennreal_mul_rpow_le_rpow (K := (K : ENNReal))
      ENNReal.coe_ne_top hqp, self_mem_nhdsWithin] with d hd hd0
  have hdne : d ≠ 0 := ne_of_gt (by simpa using hd0)
  rw [← ENNReal.coe_rpow_of_ne_zero hdne, ← ENNReal.coe_rpow_of_ne_zero hdne,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe] at hd
  exact hd

/-- A fixed `ℝ≥0` constant is eventually dominated by any negative power of the scale. -/
theorem eventually_nnreal_le_rpow_neg (K : NNReal) {ν : Real} (hν : 0 < ν) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, K ≤ d ^ (-ν) := by
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow K (p := 0) (q := -ν)
    (by linarith)] with d hd
  simpa using hd

/-- A fixed finite `ℝ≥0∞` constant is eventually dominated by any negative power of the
scale. -/
theorem eventually_ennreal_le_rpow_neg {K : ENNReal} (hK : K ≠ ⊤) {ν : Real} (hν : 0 < ν) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, K ≤ (d : ENNReal) ^ (-ν) := by
  filter_upwards [eventually_ennreal_mul_rpow_le_rpow hK (p := 0) (q := -ν)
    (by linarith)] with d hd
  simpa using hd

/-- `ℝ` form of `Kakeya.VeryNotSticky.eventually_nnreal_le_rpow_neg`. -/
theorem eventually_real_le_rpow_neg (K : NNReal) {ν : Real} (hν : 0 < ν) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, (K : Real) ≤ (d : Real) ^ (-ν) := by
  filter_upwards [eventually_nnreal_le_rpow_neg K hν] with d hd
  have h := NNReal.coe_le_coe.2 hd
  rwa [NNReal.coe_rpow] at h

/-- A fixed constant times a positive power of the scale eventually falls below any fixed
positive bound. This is the shape of the clauses that compare with an absolute constant
(`Real.exp (-1)`, `1`) rather than with a power of the scale. -/
theorem eventually_nnreal_mul_rpow_le_const (K c : NNReal) (hc : 0 < c) {p : Real}
    (hp : 0 < p) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, K * d ^ p ≤ c := by
  have hcne : c ≠ 0 := hc.ne'
  filter_upwards [eventually_nnreal_mul_rpow_le_rpow (K / c) (p := p) (q := 0) hp] with d hd
  have h1 : K / c * d ^ p ≤ 1 := by simpa using hd
  calc K * d ^ p = c * (K / c * d ^ p) := by field_simp
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

/-! ### The `δ`-thresholds of Configuration `hyp:ml2setup` and of the thick bundle -/

/-- **The honest Section-5 loss constant is eventually absorbed** (the field
`Kakeya.VeryNotSticky.coarseLoss_absorb`).

This is the arrangeability certificate for that field, and it has the same shape as
`Kakeya.VeryNotSticky.eventually_aScaleData_absorb` with one extra ingredient: the loss
`ShadedBody.rhoTubesSection9Loss 3 N δ` is *not* a closed constant — it is a function of both
`δ` and the family size `N` — so a plain `K ≤ δ^{-η}` absorption does not apply. What makes it
absorbable anyway is that it is only `δ^{-o(1)}` in the *pair*: by
`ShadedBody.rhoTubesSection9Loss_le_rpow_neg` (whose input is
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C_leApprox`) it is at most `δ^{-η}`
below a threshold determined by `η` and by a polynomial cardinality budget `N ≤ δ^{-K}`.

`K` is a free parameter here, so a producer may take whatever budget its family satisfies; in
dimension three `K = 2` suffices for a family of essentially distinct `δ`-tubes in `B_1`. The
budget is genuinely needed and is not cosmetic: without a bound on `N` the loss has no bound
at all uniform in the family, since `C_leApprox` charges `N^ε`. -/
theorem eventually_coarseLoss_absorb {η K : Real} (hη : 0 < η) (hK : 0 ≤ K) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ N : ℕ, 0 < N → (N : NNReal) ≤ d ^ (-K) →
        ((_root_.ShadedBody.rhoTubesSection9Loss 3 N d : NNReal) : ENNReal) ≤
          (d : ENNReal) ^ (-η) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := _root_.ShadedBody.rhoTubesSection9Loss_le_rpow_neg 3 hη hK
  have hmin : (0 : NNReal) < min δ₀ 1 := lt_min hδ₀pos one_pos
  filter_upwards [Ioo_mem_nhdsGT hmin, self_mem_nhdsWithin] with d hd hd0
  intro N hN hNbd
  have hdpos : 0 < d := hd0
  have hdle : d ≤ δ₀ := le_trans hd.2.le (min_le_left _ _)
  have hd1 : d ≤ 1 := le_trans hd.2.le (min_le_right _ _)
  have h := hδ₀ d hdpos hdle hd1 N hN hNbd
  rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne']
  exact ENNReal.coe_le_coe.mpr h

/-- **The exponent budget of the scale-`r` layer tolerates a coarse fullness exponent `9η`.**

The standing budget of the layer is `hνη : 90 η ≤ ν` (a binder of
`Kakeya.VeryNotSticky.exists_aScaleData`, `Kakeya.VeryNotSticky.aScaleVolume` and
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale`), and what the layer must deliver is the
gain `δ^{ν/9}` of `Kakeya.VeryNotSticky.AScaleData`. This says the coarse path may spend up to
`9 η` on its fullness exponent and still land inside that gain. The layer runs at `2 η`
(`Kakeya.VeryNotSticky.rpow_two_eta_mul_sq_le_sq_of_gridStep`), so the extra `η` charged by
`Kakeya.VeryNotSticky.coarseLoss_absorb` leaves six spare. -/
theorem coarseLossExponentHeadroom {η ν : Real} (hνη : 90 * η ≤ ν) :
    9 * η + ν / 90 ≤ ν / 9 := by
  linarith

/-- **And `10 η` is already too much**, so the previous lemma is sharp: at the boundary
`ν = 90 η` of the budget the inequality fails at the very next integer coefficient. This is
what makes the headroom a measurement rather than an estimate. -/
theorem coarseLossExponentHeadroom_sharp {η : Real} (hη : 0 < η) :
    ¬ (10 * η + (90 * η) / 90 ≤ (90 * η) / 9) := by
  intro h
  linarith

/-- **The scale-`r` comparison constant is eventually absorbed** (the field
`Kakeya.VeryNotSticky.aScaleData_absorb`).

This is the clause whose quantifier order is the delicate one: `C₀` and `D₀` are fields of the
configuration, hence produced *after* `δ`, and the docstring of the field records that the
statement is arrangeable only because the uniformization producing them,
`Kakeya.ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, binds its constant
`Kakeya.ShadedTube.ssfUniformConst` before the scale *and* before the family. Given that, the
clause is a plain threshold on `δ`, and this is it. -/
theorem eventually_aScaleData_absorb (C₀ D₀ : NNReal) {η : Real} (hη : 0 < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      (aScaleDataConstant C₀ D₀ : ENNReal) ^ 2 ≤ (d : ENNReal) ^ (-η) :=
  eventually_ennreal_le_rpow_neg (ENNReal.pow_ne_top ENNReal.coe_ne_top) hη

/-- **The same absorption, uniformly over a sub-polynomially bounded `C₀`.**

`Kakeya.VeryNotSticky.eventually_aScaleData_absorb` fixes `C₀` before `δ`, which is why
`Kakeya.VeryNotSticky.BandUniformRefinement` was forced to name a `δ`-free uniformity constant.
The quantifier order is not a mathematical necessity: `aScaleDataConstant` is a closed-form
polynomial in `C₀` of degree exactly `4` —
`aScaleVolumeConstant C₀ D₀ = C₀^4 · D₀ / (tubeVolumeRatioConstant 3)^2`, and
`aScaleBallConstant` is `C₀`-free — so squaring gives degree `8`, and a bound
`C₀ ≤ δ^{-η'}` is absorbed as soon as `8 η' < η`.

`Kakeya.VeryNotSticky.aScaleData_absorb` is the **only** field of `Kakeya.VeryNotSticky` that
bounds `C₀` from above; `hC₀`, `uniform` and `rho_count` consume `1 ≤ C₀` alone. So `8 η' < η`
is the whole admissibility condition on a `δ`-dependent uniformity constant, and
`η' := η / 16` leaves half the budget.

No positivity of `η'` is needed: at `η' ≤ 0` the cap reads `C₀ ≤ δ^{-η'} ≤ 1`, which is a
*stronger* hypothesis on the caller. -/
theorem eventually_aScaleData_absorb_of_le (D₀ : NNReal) {η η' : Real} (h8 : 8 * η' < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ C₀ : NNReal, 1 ≤ C₀ → (C₀ : ENNReal) ≤ (d : ENNReal) ^ (-η') →
        (aScaleDataConstant C₀ D₀ : ENNReal) ^ 2 ≤ (d : ENNReal) ^ (-η) := by
  have hgap : 0 < η - 8 * η' := by linarith
  obtain ⟨M, hM⟩ : ∃ M : NNReal, ∀ C₀ : NNReal, 1 ≤ C₀ →
      aScaleDataConstant C₀ D₀ ≤ C₀ ^ 4 * M := by
    refine ⟨max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
      (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3), fun C₀ hC₀ => ?_⟩
    have h1 : (1 : NNReal) ≤ C₀ ^ 4 := one_le_pow₀ hC₀
    have hvol : aScaleVolumeConstant C₀ D₀
        = C₀ ^ 4 * (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) := by
      simp only [aScaleVolumeConstant, deltamaxScaleAConstant]
      ring
    rw [aScaleDataConstant, hvol]
    refine max_le ?_ (mul_le_mul_left' (le_max_right _ _) _)
    calc aScaleBallConstant (max 1 (Tube.dilateFullness.C 3))
        ≤ max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
            (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) := le_max_left _ _
      _ = 1 * max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
            (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) := (one_mul _).symm
      _ ≤ C₀ ^ 4 * max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
            (D₀ / tubeVolumeRatioConstant 3 / tubeVolumeRatioConstant 3) :=
          mul_le_mul_right' h1 _
  filter_upwards [eventually_ennreal_le_rpow_neg
      (K := ((M ^ 2 : NNReal) : ENNReal)) ENNReal.coe_ne_top hgap,
    self_mem_nhdsWithin] with d hd hd0
  have hdpos : (0 : NNReal) < d := hd0
  have hdE : ((d : ENNReal)) ≠ 0 := by simpa using hdpos.ne'
  intro C₀ hC₀ hcap
  calc (aScaleDataConstant C₀ D₀ : ENNReal) ^ 2
      ≤ ((C₀ ^ 4 * M : NNReal) : ENNReal) ^ 2 := by
        gcongr
        exact_mod_cast hM C₀ hC₀
    _ = (C₀ : ENNReal) ^ 8 * ((M ^ 2 : NNReal) : ENNReal) := by push_cast; ring
    _ ≤ ((d : ENNReal) ^ (-η')) ^ 8 * ((M ^ 2 : NNReal) : ENNReal) := by gcongr
    _ = (d : ENNReal) ^ (-(8 * η')) * ((M ^ 2 : NNReal) : ENNReal) := by
        rw [← ENNReal.rpow_natCast ((d : ENNReal) ^ (-η')) 8, ← ENNReal.rpow_mul]
        norm_num
        ring_nf
    _ ≤ (d : ENNReal) ^ (-(8 * η')) * (d : ENNReal) ^ (-(η - 8 * η')) := by gcongr
    _ = (d : ENNReal) ^ (-η) := by
        rw [← ENNReal.rpow_add _ _ hdE ENNReal.coe_ne_top]
        ring_nf

/-- **(T3) is eventually met** (the field `Kakeya.VeryNotSticky.ThickDensityThresholds.bias`).

`C_bias · (48 C₀^6)^3 ≤ δ^{-τϱ}`. Both constants are `δ`-free: `C₀` by the argument recorded
under `Kakeya.VeryNotSticky.eventually_aScaleData_absorb`, and `C_bias` because
`Kakeya.ConvexSpaceBody.nonempty_biasedFactorization` produces its factoring at the constant
`nonempty_biasedFactorization.C (Module.finrank ℝ E) ϖ`, a function of the ambient dimension
and the bias exponent alone — the `δ`-dependence of that lemma is confined to its *volume
loss*, which is a refinement cost and not a constant of the bundle. -/
theorem eventually_thick_bias (Cbias C₀ : NNReal) {τ ϱ : Real} (hτ : 0 < τ) (hϱ : 0 < ϱ) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      (Cbias : ENNReal) * (((48 * C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
        (d : ENNReal) ^ (-(τ * ϱ)) :=
  eventually_ennreal_le_rpow_neg
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) (by positivity)

/-- **The two fixed-scale thresholds of blueprint `plankF` are eventually met.**

These are the hypotheses `hb₀` and `hc₁` of
`Kakeya.VeryNotSticky.plankFrostmanUsable_of_thick`, and with them that lemma discharges the
field `Kakeya.VeryNotSticky.ThickDensityThresholds.plankF` outright. The second threshold is
where the binder `hplankF` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is spent, the
lemma being read at `η := 2 cfg.η` (F8: (C5) at `δ^{2η}`): the exponent `τ ηF - 2 cfg.η` is
positive exactly under that budget, `2 cfg.η < τ ηF`, and
without it the threshold is a condition that *fails* as `δ → 0`.

`b₀` is `δ`-free by `Kakeya.VeryNotSticky.exists_plankFrostmanVolumeAt_canonical`, and `c₁` is
a free field of `Kakeya.VeryNotSticky.BallData` occurring here on the large side, so both
hypotheses are genuine smallness conditions on `δ`. -/
theorem eventually_plankFrostman_thresholds (CP b₀ c₁ : NNReal) (hb₀ : 0 < b₀) (hc₁ : 0 < c₁)
    {τ ηF η : Real} (hτ : 0 < τ) (hbudget : η < τ * ηF) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      CP * d ^ τ ≤ b₀ ∧ CP ^ (1 + ηF) * d ^ (τ * ηF - η) ≤ c₁ := by
  filter_upwards [eventually_nnreal_mul_rpow_le_const CP b₀ hb₀ hτ,
    eventually_nnreal_mul_rpow_le_const (CP ^ (1 + ηF)) c₁ hc₁ (p := τ * ηF - η)
      (by linarith)] with d h1 h2
  exact ⟨h1, h2⟩

/-! ### The fixed-scale clauses of Configuration `hyp:ml2scale`

`Kakeya.VeryNotSticky.CaseScale` has fifteen clauses. Nine of them, together with
`Kakeya.VeryNotSticky.eventually_multiplicity_large` and the two threshold clauses that
`Kakeya.VeryNotSticky.nonempty_caseSideData` reads at the trivial bundle, are pure absorptions
of a `δ`-free constant into a positive power of the scale, and are discharged here. What is
left after this lemma is exactly three clauses: `typicalAngle_const`, whose left-hand side is
the constant `Kakeya.typicalAngleScaledConst` (discharged separately, by
`Kakeya.VeryNotSticky.eventually_typicalAngle_const`, once
`Kakeya.typicalAngleScaledConst_le` exposes its polylogarithmic growth);
`transverseFill_threshold`, which is
`Kakeya.VeryNotSticky.exists_isReductionFillAvailable` but needs that threshold quantified
ahead of the index type `bd.ω`; and `transverseFill_fullness`, which the field's own docstring
declares a mathematical input rather than plumbing.

The constants are pinned to `δ`-free values by hypothesis rather than bounded, matching
`Kakeya.VeryNotSticky.eventually_slabScale_of_uniform_bounds`: `bd.C₀` is `δ`-free by the
uniformization (see `Kakeya.VeryNotSticky.eventually_aScaleData_absorb`), `bd.Cbias` by the
biased factoring lemma (see `Kakeya.VeryNotSticky.eventually_thick_bias`), while `C` — the
thin-case comparison constant — is the one genuinely `δ`-dependent quantity, and pinning it is
what records the outstanding debt that it be sub-polynomial in `δ⁻¹`. -/
theorem eventually_caseScale_clauses (C₀ Cbias C : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' : Real} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthin : τ + exscal < 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky) (bd : BallData cfg),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias →
        (cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant bd.C₀)⁻¹) ∧
        (cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → bd.C₀ * cfg.b ≤ cfg.r₁) ∧
        (cfg.a ≤ cfg.δ ^ (1 - τ) →
          ((bd.C₀ * (cfg.a / cfg.r₁) : NNReal) : Real) ≤ Real.exp (-1)) ∧
        (6 * ThinCase.w1Constant bd.C₀ ≤ cfg.δ ^ (-τ')) ∧
        (27 * max 1 (bd.C₀ / 3) ^ 3 ≤ cfg.δ ^ (-(cfg.η / 2))) ∧
        (1000 * ThinCase.transferConstant C bd.C₀ ≤ cfg.δ ^ (-cfg.η)) ∧
        (plankEnclosureConstant bd.C₀ * bd.Cbias * cfg.δ ^ cfg.ϱ ≤ 1) ∧
        ((plankSelectionConstant bd.C₀ : Real) ≤ (cfg.δ : Real) ^ (-(cfg.exscal * cfg.η))) ∧
        ((2 : Real) ≤ ((cfg.δ / cfg.r₁ : NNReal) : Real) ^ (-(cfg.η / 512))) := by
  have hangle : (0 : NNReal) < (2 * NonSlab.bodyAngleConstant C₀)⁻¹ := by
    have h1 : (1 : NNReal) ≤ NonSlab.bodyAngleConstant C₀ :=
      NonSlab.one_le_bodyAngleConstant hC₀
    have h2 : (0 : NNReal) < 2 * NonSlab.bodyAngleConstant C₀ := by
      have : (0 : NNReal) < NonSlab.bodyAngleConstant C₀ := lt_of_lt_of_le zero_lt_one h1
      positivity
    simpa using inv_pos.mpr h2
  have hexp : (0 : NNReal) < Real.toNNReal (Real.exp (-1)) :=
    Real.toNNReal_pos.mpr (Real.exp_pos _)
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 _ hangle hexscal,
    eventually_nnreal_mul_rpow_le_rpow C₀ (p := 2 * exscal) (q := exscal) (by linarith),
    eventually_nnreal_mul_rpow_le_const C₀ _ hexp (p := 1 - τ - exscal) (by linarith),
    eventually_nnreal_le_rpow_neg (6 * ThinCase.w1Constant C₀) hτ',
    eventually_nnreal_le_rpow_neg (27 * max 1 (C₀ / 3) ^ 3) (show (0:Real) < η / 2 by linarith),
    eventually_nnreal_le_rpow_neg (1000 * ThinCase.transferConstant C C₀) hη,
    eventually_nnreal_mul_rpow_le_const (plankEnclosureConstant C₀ * Cbias) 1 one_pos hϱ,
    eventually_real_le_rpow_neg (plankSelectionConstant C₀)
      (show (0:Real) < exscal * η by positivity),
    eventually_real_le_rpow_neg 2
      (show (0:Real) < (1 - exscal) * (η / 512) by
        have : (0:Real) < 1 - exscal := by linarith
        positivity),
    self_mem_nhdsWithin] with d h1 h2 h3 h4 h5 h6 h7 h8 h9 hd0
  intro cfg bd hδ hex hη' hϱ' hC hCb
  have hdpos : (0 : NNReal) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hr₁ : cfg.r₁ = d ^ exscal := by
    simp only [VeryNotSticky.r₁, hδ, hex]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hδ, hex, hC]
    simpa using h1
  · intro hb
    rw [hδ, hex] at hb
    rw [hC, hr₁]
    calc C₀ * cfg.b ≤ C₀ * d ^ (2 * exscal) := by gcongr
      _ ≤ d ^ exscal := h2
  · intro ha
    rw [hδ] at ha
    have hquot : cfg.a / cfg.r₁ ≤ d ^ (1 - τ - exscal) := by
      rw [hr₁]
      calc cfg.a / d ^ exscal ≤ d ^ (1 - τ) / d ^ exscal := by gcongr
        _ = d ^ (1 - τ - exscal) := by
              rw [show (1 : Real) - τ - exscal = (1 - τ) - exscal from by ring]
              exact (NNReal.rpow_sub hdne (1 - τ) exscal).symm
    have hstep : C₀ * (cfg.a / cfg.r₁) ≤ Real.toNNReal (Real.exp (-1)) :=
      le_trans (by gcongr) h3
    rw [hC]
    calc ((C₀ * (cfg.a / cfg.r₁) : NNReal) : Real)
        ≤ ((Real.toNNReal (Real.exp (-1)) : NNReal) : Real) := NNReal.coe_le_coe.2 hstep
      _ = Real.exp (-1) := Real.coe_toNNReal _ (Real.exp_pos _).le
  · rw [hδ, hC]; exact h4
  · rw [hδ, hC, hη']; exact h5
  · rw [hδ, hC, hη']; exact h6
  · rw [hδ, hC, hCb, hϱ']; exact h7
  · rw [hδ, hC, hex, hη']; exact h8
  · have hdiv : (cfg.δ / cfg.r₁ : NNReal) = d ^ (1 - exscal) := by
      rw [hδ, hr₁, NNReal.rpow_sub hdne, NNReal.rpow_one]
    rw [hdiv, hη', NNReal.coe_rpow, ← Real.rpow_mul (by positivity)]
    have hsign : (1 - exscal) * (-(η / 512)) = -((1 - exscal) * (η / 512)) := by ring
    rw [hsign]
    simpa using h9

/-! ### The reduction-fill threshold, quantified ahead of the index type

`Kakeya.VeryNotSticky.exists_isReductionFillAvailable` binds its threshold `δ_*` *after* the
index type `ω`, which is unusable for a producer of `Kakeya.VeryNotSticky.CaseScale`: there
`ω = bd.ω` is a field of the ball data, hence chosen after `δ`. The threshold does not in fact
depend on `ω` — `ShadedPlank.reduction_to_slab_atTypicalAngle` binds it before its index type
— so hoisting the binder is legitimate, and this is that hoist.
-/

/-- **The reduction is available below a threshold fixed before the index type as well as
before the scale.** The `ω`-uniform form of
`Kakeya.VeryNotSticky.exists_isReductionFillAvailable`. -/
theorem exists_isReductionFillAvailable_uniform {η : Real} (hη : 0 < η) (Ccard : NNReal)
    (D : Real) :
    ∃ δthr : NNReal, 0 < δthr ∧ δthr ≤ 1 ∧
      ∀ (ω : Type*) (δ : NNReal), 0 < δ → δ ≤ δthr →
        IsReductionFillAvailable ω η Ccard D δ := by
  have hεpos : 0 < η / 256 := by positivity
  have hε'pos : 0 < η / 2 := by positivity
  have hgap : 128 * (η / 256) ≤ η / 2 := le_of_eq (by ring)
  rcases ShadedPlank.reduction_to_slab_atTypicalAngle
      (η := η) (ε := η / 256) (ε' := η / 2) hη hεpos hε'pos hgap Ccard D with
    ⟨δthr, hδthrpos, hδthr1, hred⟩
  refine ⟨δthr, hδthrpos, hδthr1, ?_⟩
  intro ω δ hδpos hδle
  unfold IsReductionFillAvailable
  intro s a b hab hb1 Y θ hθ1 C Y'' hδpos0 hδa ha1 hwin hfull hmulti_a hmulti_δ h2 hcard
    h_ab h1leC hCle hcref hcm htyp hmaxAbsP
  have hred3 := hred (ι := ω) s (δ := δ) (a := a) (b := b) (hab := hab) (hb1 := hb1) Y θ hθ1 C Y''
      hδpos0 hδa ha1 hδle hwin hfull hmulti_a hmulti_δ h2 hcard h_ab h1leC hCle
      hcref hcm htyp hmaxAbsP
  rcases hred3 with ⟨s', Y', c1, hc1, href, href2, hfull', hitem1, hitem5⟩
  have hapos : 0 < a := lt_of_lt_of_le hδpos0 hδa
  have hfullpos : (0 : NNReal) < ShadedBody.fullness s' Y' := by
    have haeps : (0 : NNReal) < a ^ (η / 256) := NNReal.rpow_pos hapos
    have haeta : (0 : NNReal) < a ^ η := NNReal.rpow_pos hapos
    have hprod : (0 : NNReal) < c1 * (a ^ (η / 256)) * a ^ η :=
      mul_pos (mul_pos hc1 haeps) haeta
    have hle : c1 * (a ^ (η / 256)) * a ^ η ≤ ShadedBody.fullness s' Y' := by
      calc
        c1 * (a ^ (η / 256)) * a ^ η
            = (c1 * (a ^ (η / 256))) * a ^ η := by ring
        _ ≤ (c1 * (a ^ (η / 256))) * ShadedBody.fullness s (ShadedPlank.bodies Y) := by
                exact mul_le_mul_right hfull (c1 * (a ^ (η / 256)))
        _ ≤ ShadedBody.fullness s' Y' := hfull'
    exact lt_of_lt_of_le hprod hle
  have hfullE : (0 : ENNReal) < (ShadedBody.fullness s' Y' : ENNReal) :=
    ENNReal.coe_pos.mpr hfullpos
  have hsumne : (∑ i ∈ s', volume (Y' i).shade) ≠ 0 := by
    rw [ShadedBody.fullness_def s' Y'] at hfullE
    exact (ENNReal.div_pos_iff.mp hfullE).1
  have hneu : (ShadedBody.iUnionShade s' Y').Nonempty := by
    rcases Finset.exists_ne_zero_of_sum_ne_zero (s := s') (f := fun i => volume (Y' i).shade)
        hsumne with ⟨j, hj, hjne⟩
    have hvolj : (0 : ENNReal) < volume (Y' j).shade := pos_iff_ne_zero.mpr hjne
    have hjne' : volume (Y' j).shade ≠ 0 := ne_of_gt hvolj
    have hjNonempty : (Y' j).shade.Nonempty := MeasureTheory.nonempty_of_measure_ne_zero hjne'
    rcases hjNonempty with ⟨p, hp⟩
    exact ⟨p, Finset.subset_set_biUnion_of_mem (s := s') (f := fun i => (Y' i).shade) hj hp⟩
  refine ⟨s', Y', c1, hc1, href, href2, hneu, ?_, hitem5⟩
  intro x hx
  simpa using hitem1 x hx

/-- **The eleventh clause of Configuration `hyp:ml2scale` holds eventually**
(`Kakeya.VeryNotSticky.CaseScale.transverseFill_threshold`).

The clause is the availability of the plank-to-slab reduction at the *rescaled* scale
`δ' = δ / r₁ = δ^{1-exscal}`, which tends to `0` with `δ` because `exscal < 1`; the threshold
comes from `Kakeya.VeryNotSticky.exists_isReductionFillAvailable_uniform`, so it is fixed
before `δ` and before `bd.ω`. -/
theorem eventually_transverseFill_threshold {exscal η ϱ : Real} (hη : 0 < η)
    (hexscal1 : exscal < 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky) (bd : BallData cfg),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        IsReductionFillAvailable bd.ω (16 * cfg.η) plankCardConstant
          (plankCardExponent + 6 * cfg.ϱ) (cfg.δ / cfg.r₁) := by
  obtain ⟨δthr, hδthrpos, -, hthr⟩ :=
    exists_isReductionFillAvailable_uniform (show (0:Real) < 16 * η by linarith)
      plankCardConstant (plankCardExponent + 6 * ϱ)
  filter_upwards [eventually_nnreal_mul_rpow_le_const 1 δthr hδthrpos
    (show (0 : Real) < 1 - exscal by linarith), self_mem_nhdsWithin] with d hd hd0
  intro cfg bd hδ hex hη' hϱ'
  have hdpos : (0 : NNReal) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdiv : (cfg.δ / cfg.r₁ : NNReal) = d ^ (1 - exscal) := by
    simp only [VeryNotSticky.r₁, hδ, hex]
    rw [NNReal.rpow_sub hdne, NNReal.rpow_one]
  rw [hη', hϱ', hdiv]
  exact hthr bd.ω (d ^ (1 - exscal)) (NNReal.rpow_pos hdpos) (by simpa using hd)

/-- **The typical-angle constant threshold is eventually met** — the tenth clause
`Kakeya.VeryNotSticky.CaseScale.typicalAngle_const`, discharged from the *eleventh*,
`plankCard_bias`, and nothing else.

This clause was the second compiler-verified defect of Configuration `hyp:ml2scale`. Its
left-hand side is `Kakeya.typicalAngleScaledConst`, and while that constant is bound before
every geometric datum, the statement it was read off,
`Kakeya.findingTypicalAngleOfIntersection_scaled`, quantifies it *after* the plank-count
constant `C₀` and so says nothing about how it grows with `C₀`. Here `C₀` carries `δ^{-2ϱ}`,
and `Kakeya.CaseParams.densityBias` forces `ϱ > 2^20 η`, so the clause demanded growth below
the power `2^{-25}` of `C₀` — which no `Classical.choose` constant supplies and which no
smallness hypothesis on `δ` can repair.

The repair is `Kakeya.typicalAngleScaledConst_le`: the constant is at most
`typicalAngleScaledBase (η/1024) plankCardExponent · (log⁺C₀ + 1)²`, with the base independent
of `C₀`. The growth is **polylogarithmic**, which is what the clause needs and more than the
`2^{-25}` power it asked for. The rest is `Kakeya.linlog_le` and one power absorption:
with `plankCard_bias` the argument is at most `plankCardConstant · δ^{-3ϱ}`, so
`log⁺C₀ + 1 = O(log δ⁻¹)`, hence `O(δ^{-ε})` for every `ε > 0`, and two of those are beaten by
`(δ/r₁)^{-η/1024} = δ^{-(1-exscal)η/1024}`.

Note what is *not* assumed: no `δ`-free bound on `plankEnclosureConstant bd.C₀ · bd.Cbias`.
Those constants are produced after `δ`, and they enter only through a logarithm, so the
`δ`-dependent bound that `plankCard_bias` already supplies is enough. -/
theorem eventually_typicalAngle_const {η ϱ exscal : Real} (hη : 0 < η) (hϱ : 0 < ϱ)
    (hexscal1 : exscal < 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ X : NNReal, X * d ^ ϱ ≤ 1 →
        Kakeya.typicalAngleScaledConst.{u} (η / 1024)
            (plankCardConstant * (X * d ^ (-(2 * ϱ)))) plankCardExponent ≤
          (d / d ^ exscal : NNReal) ^ (-(η / 1024)) := by
  have hη16 : (0:Real) < η / 1024 := by linarith
  set B : NNReal := Kakeya.typicalAngleScaledBase.{u} (η / 1024) plankCardExponent with hBdef
  set κ : Real := (1 - exscal) * (η / 1024) with hκdef
  have hκ0 : 0 < κ := mul_pos (by linarith) hη16
  set ε' : Real := κ / 4 with hε'def
  have hε'0 : (0:Real) < ε' := by rw [hε'def]; linarith
  have hKpos : (0:Real) < ((plankCardConstant : NNReal) : Real) := by
    have : (plankCardConstant : NNReal) = 2 ^ 20 := rfl
    rw [this]; norm_num
  set c : Real := |Real.log ((plankCardConstant : NNReal) : Real)| + 1 with hcdef
  have hc0 : (0:Real) ≤ c := by
    rw [hcdef]; positivity
  set Cfin : NNReal := B * Real.toNNReal (c + 3 * ϱ / ε') ^ 2 with hCfindef
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [eventually_nnreal_le_rpow_neg Cfin (show (0:Real) < 2 * ε' by positivity),
    self_mem_nhdsWithin, hsmall] with d hCf hd0 hd1
  intro X hX
  have hdpos : (0 : NNReal) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdR : (0:Real) < (d : Real) := by exact_mod_cast hdpos
  have hd1R : (d : Real) < 1 := by exact_mod_cast hd1
  have hpow0 : d ^ ϱ ≠ 0 := ne_of_gt (NNReal.rpow_pos hdpos)
  -- the argument of the constant is at most `plankCardConstant · δ^{-3ϱ}`
  have hXle : X ≤ d ^ (-ϱ) := by
    have h := mul_le_mul_right' hX (d ^ ϱ)⁻¹
    rwa [mul_assoc, mul_inv_cancel₀ hpow0, mul_one, one_mul, ← NNReal.rpow_neg] at h
  have hprod : X * d ^ (-(2 * ϱ)) ≤ d ^ (-(3 * ϱ)) := by
    calc X * d ^ (-(2 * ϱ)) ≤ d ^ (-ϱ) * d ^ (-(2 * ϱ)) := by gcongr
      _ = d ^ (-(3 * ϱ)) := by rw [← NNReal.rpow_add hdne]; congr 1; ring
  have hargle : plankCardConstant * (X * d ^ (-(2 * ϱ)))
      ≤ plankCardConstant * d ^ (-(3 * ϱ)) := by gcongr
  have hargR : ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)
      ≤ ((plankCardConstant : NNReal) : Real) * (d : Real) ^ (-(3 * ϱ)) := by
    have h := NNReal.coe_le_coe.mpr hargle
    calc ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)
        ≤ ((plankCardConstant * d ^ (-(3 * ϱ)) : NNReal) : Real) := h
      _ = ((plankCardConstant : NNReal) : Real) * (d : Real) ^ (-(3 * ϱ)) := by
          rw [NNReal.coe_mul, NNReal.coe_rpow]
  -- the logarithm of the argument is linear in `log δ⁻¹`
  have ht0 : (0:Real) ≤ Real.log (d : Real)⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_nonpos hdR.le hd1R.le]
  have h3t : (0:Real) ≤ 3 * ϱ * Real.log (d : Real)⁻¹ :=
    mul_nonneg (by positivity) ht0
  have hUpos : (0:Real) < ((plankCardConstant : NNReal) : Real) * (d : Real) ^ (-(3 * ϱ)) :=
    mul_pos hKpos (Real.rpow_pos_of_pos hdR _)
  have hlogU : Real.log (((plankCardConstant : NNReal) : Real) * (d : Real) ^ (-(3 * ϱ)))
      = Real.log ((plankCardConstant : NNReal) : Real) + 3 * ϱ * Real.log (d : Real)⁻¹ := by
    rw [Real.log_mul (ne_of_gt hKpos) (ne_of_gt (Real.rpow_pos_of_pos hdR _)),
      Real.log_rpow hdR, Real.log_inv]
    ring
  have hcabs : c - 1 = |Real.log ((plankCardConstant : NNReal) : Real)| := by
    rw [hcdef]; ring
  have habs : (0:Real) ≤ c - 1 := by rw [hcabs]; exact abs_nonneg _
  have hmaxlog :
      max (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)) 0
        ≤ c - 1 + 3 * ϱ * Real.log (d : Real)⁻¹ := by
    have hub : Real.log (((plankCardConstant : NNReal) : Real) * (d : Real) ^ (-(3 * ϱ)))
        ≤ c - 1 + 3 * ϱ * Real.log (d : Real)⁻¹ := by
      rw [hlogU, hcabs]
      linarith [le_abs_self (Real.log ((plankCardConstant : NNReal) : Real))]
    refine max_le ?_ (by linarith)
    rcases lt_or_eq_of_le
        (NNReal.coe_nonneg (plankCardConstant * (X * d ^ (-(2 * ϱ))))) with hpos | hzero
    · exact le_trans (Real.log_le_log hpos hargR) hub
    · rw [← hzero, Real.log_zero]
      linarith
  -- the polylogarithmic bound, then two power absorptions
  have hlin : c + 3 * ϱ * Real.log (d : Real)⁻¹ ≤ (c + 3 * ϱ / ε') * (d : Real) ^ (-ε') :=
    linlog_le hc0 (by positivity) hε'0 hdR hd1R.le
  have hMnn :
      Real.toNNReal (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)) + 1
        ≤ Real.toNNReal (c + 3 * ϱ / ε') * d ^ (-ε') := by
    refine NNReal.coe_le_coe.mp ?_
    have hL : ((Real.toNNReal
          (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)) + 1
            : NNReal) : Real)
        = max (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)) 0 + 1 := by
      rw [NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal']
    have hR : ((Real.toNNReal (c + 3 * ϱ / ε') * d ^ (-ε') : NNReal) : Real)
        = (c + 3 * ϱ / ε') * (d : Real) ^ (-ε') := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), NNReal.coe_rpow]
    rw [hL, hR]
    linarith [hmaxlog, hlin]
  have hM2 :
      (Real.toNNReal (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real))
          + 1) ^ 2
        ≤ Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * d ^ (-(2 * ε')) := by
    calc (Real.toNNReal
            (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)) + 1) ^ 2
        ≤ (Real.toNNReal (c + 3 * ϱ / ε') * d ^ (-ε')) ^ 2 := by gcongr
      _ = Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * (d ^ (-ε')) ^ 2 := by rw [mul_pow]
      _ = Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * d ^ (-(2 * ε')) := by
          congr 1
          rw [← NNReal.rpow_natCast (d ^ (-ε')) 2, ← NNReal.rpow_mul]
          congr 1
          push_cast
          ring
  calc Kakeya.typicalAngleScaledConst.{u} (η / 1024)
          (plankCardConstant * (X * d ^ (-(2 * ϱ)))) plankCardExponent
      ≤ B * (Real.toNNReal
            (Real.log ((plankCardConstant * (X * d ^ (-(2 * ϱ))) : NNReal) : Real)) + 1) ^ 2 :=
        Kakeya.typicalAngleScaledConst_le.{u} hη16 _ _
    _ ≤ B * (Real.toNNReal (c + 3 * ϱ / ε') ^ 2 * d ^ (-(2 * ε'))) := by gcongr
    _ = Cfin * d ^ (-(2 * ε')) := by rw [hCfindef]; ring
    _ ≤ d ^ (-(2 * ε')) * d ^ (-(2 * ε')) := by gcongr
    _ = d ^ (-(4 * ε')) := by rw [← NNReal.rpow_add hdne]; congr 1; ring
    _ = (d / d ^ exscal : NNReal) ^ (-(η / 1024)) := by
        rw [show (d / d ^ exscal : NNReal) = d ^ (1 - exscal) by
              rw [NNReal.rpow_sub hdne, NNReal.rpow_one],
          ← NNReal.rpow_mul]
        congr 1
        rw [hε'def, hκdef]
        ring

/-! ### Configuration `hyp:ml2scale`, reduced to its one irreducible clause

The assembly of the clauses above into the bundle
`Kakeya.VeryNotSticky.CaseScale`. **Fourteen of the fifteen clauses are discharged**; the one
that remains is a hypothesis of this lemma, *by name*:

* `htypfill` is `Kakeya.VeryNotSticky.CaseScale.transverseFill_fullness`, which that field's
  own docstring declares "a mathematical input and not a matter of plumbing": the largest
  fullness the configuration supplies is `δ^{2η}`, and `(a')^η` exceeds it by a positive power
  of `δ`, so no smallness hypothesis repairs it. It is an obligation on whatever produces the
  factoring bodies.

`typicalAngle_const` used to be the second such hypothesis, and it was not merely undischarged
but *undischargeable*: its left-hand side is `Kakeya.typicalAngleScaledConst`, which was
`Classical.choose` applied to `Kakeya.findingTypicalAngleOfIntersection_scaled`, a statement
that quantifies the constant after the plank-count constant `C₀` and so bounds its growth in
`C₀` not at all — while the clause feeds it a `C₀` of size `δ^{-2ϱ}` and
`Kakeya.VeryNotSticky.CaseParams.densityBias` forces `ϱ > 2^20 η`, so that only growth below
the power `2^{-25}` would serve. It is discharged here by
`Kakeya.VeryNotSticky.eventually_typicalAngle_const`, out of the clause `plankCard_bias` and
the exposure `Kakeya.typicalAngleScaledConst_le`, which says the constant grows at most
**polylogarithmically** in `C₀`.

**This lemma does not close anything by deferral.** It is an accounting statement: it says
precisely that the arithmetic of Configuration `hyp:ml2scale` is finished and that the one
named item above is all that is left of it. -/
theorem eventually_caseScale_of_constants (C₀ Cbias C : NNReal) (hC₀ : 1 ≤ C₀)
    {exscal η ϱ τ τ' ν : Real} (hexscal : 0 < exscal) (hexscal1 : exscal < 1) (hη : 0 < η)
    (hϱ : 0 < ϱ) (hτ' : 0 < τ') (hthin : τ + exscal < 1) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (thr : ScaleThresholds),
        cfg.δ = d → cfg.exscal = exscal → cfg.η = η → cfg.ϱ = ϱ →
        bd.C₀ = C₀ → bd.Cbias = Cbias →
        cfg.δ ≤ thr.aScale ν → cfg.δ ≤ thr.typical →
        (cfg.a ≤ cfg.δ ^ (1 - τ) →
          cfg.δ ^ (-τ') * (cfg.a / cfg.b) ≤ 1 →
          ∀ (B : bd.bι) (_hB : B ∈ bd.bs)
            (tb : ThinCase.ThinBall C bd.C₀ (bd.segs B) bd.Y (bd.bodies B) bd.Wb bd.blk
              cfg.δ cfg.a (2 * cfg.η))
            {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
            (t : Finset bd.ω) (SP : bd.ω → ShadedPlank a' b' hab' hb1'),
            t ⊆ tb.bodies' →
            bd.C₀⁻¹ * (cfg.a / cfg.r₁) ≤ a' → a' ≤ bd.C₀ * (cfg.a / cfg.r₁) →
            b' ≤ bd.C₀ * (cfg.b / cfg.r₁) →
            ((plankSelectionConstant bd.C₀ : ENNReal))⁻¹ *
                (∑ i ∈ tb.bodies', volume (tb.W i).shade) ≤ ∑ i ∈ t, volume (tb.W i).shade →
            (∀ i ∈ t, volume (ShadedPlank.bodies SP i).shade *
                ENNReal.ofReal ((2 * (cfg.r₁ : Real)) ^ 3) = volume (tb.W i).shade) →
            a' ^ (16 * cfg.η) ≤ ShadedBody.fullness t (ShadedPlank.bodies SP)) →
        CaseScale cfg bd τ τ' ν C thr := by
  filter_upwards [eventually_caseScale_clauses C₀ Cbias C hC₀ hexscal hexscal1 hη hϱ hτ' hthin,
    eventually_transverseFill_threshold (exscal := exscal) (ϱ := ϱ) hη hexscal1,
    eventually_multiplicity_large (η := 16 * η) (exscal := exscal)
      (by linarith : (0:Real) < 16 * η) hexscal1,
    eventually_typicalAngle_const.{u} (exscal := exscal) hη hϱ hexscal1,
    self_mem_nhdsWithin] with d hcl hfill hmult htyp hd0
  intro cfg bd thr hδ hex hη' hϱ' hC hCb hthrA hthrT htypfill
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hcl cfg bd hδ hex hη' hϱ' hC hCb
  have hdpos : (0 : NNReal) < d := by simpa using hd0
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdiv : (cfg.δ / cfg.r₁ : NNReal) = d ^ (1 - exscal) := by
    simp only [VeryNotSticky.r₁, hδ, hex]
    rw [NNReal.rpow_sub hdne, NNReal.rpow_one]
  exact
    { rho2Star_le_one := c1
      body_fits_ball := c2
      plank_small := c3
      multiplicity_large := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη']
        exact hmult
      transverse_radius := c4
      transverse_fill := c5
      transverse_ballFill := c6
      aScaleData_threshold := hthrA
      typicalAngle_threshold := hthrT
      typicalAngle_const := by
        have hr : (cfg.δ / cfg.r₁ : NNReal) = (d / d ^ exscal : NNReal) := by
          simp only [VeryNotSticky.r₁, hδ, hex]
        rw [hr, hη', hϱ', hδ]
        refine htyp (plankEnclosureConstant bd.C₀ * bd.Cbias) ?_
        rw [← hδ, ← hϱ']
        exact c7
      plankCard_bias := c7
      transverseFill_threshold := hfill cfg bd hδ hex hη' hϱ'
      transverseFill_fullness := htypfill
      typicalAngle_selection := c8
      typicalAngle_cap := c9 }

/-! ### What the density band of Configuration `hyp:ml2setup` actually forces -/

/-- **Every tube of the configuration is individually `δ^{2η}`-full.**

The composition of the two fields `Kakeya.VeryNotSticky.lam_ge` (`Cd δ^{2η} ≤ lam`) and
`Kakeya.VeryNotSticky.shading_lb` (`Cd⁻¹ lam |T| ≤ |Y(T)|`): the comparison constant cancels
and every tube of `cfg.s` has shading density at least `δ^{2η}`.

This is the sharp form of the obligation on the refinement that produces `cfg`: it may keep
only tubes that are individually `δ^{2η}`-full, so the dyadic pigeonholing into a density band
is not optional bookkeeping but the step that makes the two fields simultaneously satisfiable.

**The exponent used to be `η`, and at `η` this statement was fatal.** The binder `hfull` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` gives only the *aggregate* ratio
`λ(𝕋, Y) ≥ δ^η`, and a ratio of sums bounds no summand, so the target could not deliver a
configuration all of whose tubes are individually `δ^η`-full — see
`Kakeya.VeryNotSticky.tubeCount_of_setupCaseSideDataStatement` below for the exact obstruction
and `Kakeya.VeryNotSticky.sum_volume_shade_lowDensity_le` for the mechanical check that at
`δ^{2η}` the obstruction is gone. -/
theorem rpow_two_eta_mul_volume_carrier_le_volume_shade (cfg : VeryNotSticky.{u}) {i : cfg.ι}
    (hi : i ∈ cfg.s) :
    (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (cfg.T i).toShadedBody.carrier ≤
      volume (cfg.T i).toShadedBody.shade := by
  have hCd0 : (cfg.Cd : ENNReal) ≠ 0 := by
    have : (0 : NNReal) < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
    simpa using this.ne'
  have hCdtop : (cfg.Cd : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hlam : ((cfg.Cd * cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) ≤ (cfg.lam : ENNReal) := by
    exact_mod_cast cfg.lam_ge
  have hlam' : (cfg.Cd : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) ≤ (cfg.lam : ENNReal) := by
    have hcoe : ((cfg.Cd * cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal)
        = (cfg.Cd : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg]
      linarith [cfg.hη]
    rwa [hcoe] at hlam
  refine le_trans ?_ (cfg.shading_lb i hi)
  have hstep : (cfg.δ : ENNReal) ^ (2 * cfg.η) ≤ (cfg.Cd : ENNReal)⁻¹ * (cfg.lam : ENNReal) := by
    calc (cfg.δ : ENNReal) ^ (2 * cfg.η)
        = (cfg.Cd : ENNReal)⁻¹ * ((cfg.Cd : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hCd0 hCdtop, one_mul]
      _ ≤ (cfg.Cd : ENNReal)⁻¹ * (cfg.lam : ENNReal) := by gcongr
  calc (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (cfg.T i).toShadedBody.carrier
      ≤ ((cfg.Cd : ENNReal)⁻¹ * (cfg.lam : ENNReal)) *
          volume (cfg.T i).toShadedBody.carrier := by gcongr
    _ = (cfg.Cd : ENNReal)⁻¹ * ((cfg.lam : ENNReal) *
          volume (cfg.T i).toShadedBody.carrier) := by rw [mul_assoc]

open MeasureTheory ShadedBody in
/-- **The repaired `Kakeya.VeryNotSticky.fullness_ge` is *implied* by the per-tube band.**

`shading_lb` composed with the repaired `lam_ge` makes every tube of `cfg.s` individually
`δ^{2η}`-full (`rpow_two_eta_mul_volume_carrier_le_volume_shade` above); summing that over `𝕋`
and dividing by `∑|T| ∈ (0, ∞)` is exactly the field `fullness_ge` at `δ^{2η}`.

**This is the fidelity certificate for that field's exponent, and it is why `δ^{2η}` and not
`c · δ^{η}` is the right repair.** At `δ^{2η}` the aggregate clause is not an extra demand at
all — it is a consequence of clauses the configuration already carries, so the two fullness
levels of the structure agree and the field is *consistent by construction*. At the old `δ^{η}`
no such derivation exists, and could not: `lam_ge` was itself repaired away from `δ^{η}` for the
same reason (`tubeCount_of_setupCaseSideDataStatement`), so the old `fullness_ge` was strictly
stronger than anything the band gives — which is precisely the rigidity that
`Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge` measures.

Nothing reads this lemma; it exists so that the claim in the field's docstring is compiler-checked
rather than asserted. It does **not** use `cfg.fullness_ge`. -/
theorem rpow_two_eta_le_fullness (cfg : VeryNotSticky.{u}) :
    cfg.δ ^ (2 * cfg.η) ≤ ShadedBody.fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
  set V : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (cfg.T i).toShadedBody
  have hc0 : ∑ i ∈ cfg.s, volume (V i).carrier ≠ 0 := cfg.sum_volume_carrier_ne_zero
  have hctop : ∑ i ∈ cfg.s, volume (V i).carrier ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ ↦ (V i).isCompact.measure_lt_top).ne
  have hsum : (cfg.δ : ENNReal) ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (V i).carrier ≤
      ∑ i ∈ cfg.s, volume (V i).shade := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ rpow_two_eta_mul_volume_carrier_le_volume_shade cfg hi
  have hdiv : (cfg.δ : ENNReal) ^ (2 * cfg.η) ≤
      (∑ i ∈ cfg.s, volume (V i).shade) / (∑ i ∈ cfg.s, volume (V i).carrier) :=
    ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop) |>.2
      ((mul_comm ((cfg.δ : ENNReal) ^ (2 * cfg.η))
        (∑ i ∈ cfg.s, volume (V i).carrier)) ▸ hsum)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne',
    ShadedBody.fullness_def cfg.s V]
  exact hdiv

/-- **The Markov step that makes the repaired exponent deliverable.**

If the aggregate fullness of `(s, V)` is at least `a`, and every member of a subfamily `u ⊆ s`
is individually *less* than `θ`-full, then `u` carries at most a `θ/a` fraction of the total
shade mass:

`a · ∑_{i ∈ u} |Y_i| ≤ θ · ∑_{i ∈ s} |Y_i|`.

Read at `a = δ^η` (the binder `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData`) and
`θ = δ^{2η}` (the level of the repaired `Kakeya.VeryNotSticky.lam_ge`): the tubes that fail to
be individually `δ^{2η}`-full carry at most a `δ^η` fraction of the shade mass, so a producer
may discard them and still meet a refinement constant `c ≥ δ^η`. That is precisely what fails
at `θ = δ^η`, where the bound degenerates to `∑_u |Y| ≤ ∑_s |Y|`, and it is why the field had
to move from `δ^η` to `δ^{2η}`.

No comparability of the carriers is needed: the proof is
`∑_u |Y| ≤ θ ∑_u |T| ≤ θ ∑_s |T|` together with `a ∑_s |T| ≤ ∑_s |Y|`. -/
theorem sum_volume_shade_lowDensity_le {ι : Type*} {s u : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} (hus : u ⊆ s) {a θ : NNReal}
    (hfull : a ≤ ShadedBody.fullness s V)
    (hlow : ∀ i ∈ u, volume (V i).shade ≤ (θ : ENNReal) * volume (V i).carrier) :
    (a : ENNReal) * ∑ i ∈ u, volume (V i).shade
      ≤ (θ : ENNReal) * ∑ i ∈ s, volume (V i).shade := by
  classical
  have hcar : (a : ENNReal) * ∑ i ∈ s, volume (V i).carrier
      ≤ ∑ i ∈ s, volume (V i).shade := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V]
    exact mul_le_mul' (ENNReal.coe_le_coe.mpr hfull) le_rfl
  have hu : ∑ i ∈ u, volume (V i).shade ≤ (θ : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
    calc ∑ i ∈ u, volume (V i).shade
        ≤ ∑ i ∈ u, (θ : ENNReal) * volume (V i).carrier := Finset.sum_le_sum hlow
      _ = (θ : ENNReal) * ∑ i ∈ u, volume (V i).carrier := by rw [Finset.mul_sum]
      _ ≤ (θ : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
          gcongr
  calc (a : ENNReal) * ∑ i ∈ u, volume (V i).shade
      ≤ (a : ENNReal) * ((θ : ENNReal) * ∑ i ∈ s, volume (V i).carrier) := by gcongr
    _ = (θ : ENNReal) * ((a : ENNReal) * ∑ i ∈ s, volume (V i).carrier) := by ring
    _ ≤ (θ : ENNReal) * ∑ i ∈ s, volume (V i).shade := by gcongr

/-! ### Guardrail: what the setup statement forces about the *individual* shading densities

The house pattern of `Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`: restate the target
with every binder explicit, pin the restatement to the real declaration with a tripwire
`example`, and then derive from it a consequence that can be compared with the hypotheses.
-/

open MeasureTheory Topology Filter ShadedBody in
/-- **`Kakeya.VeryNotSticky.exists_setup_caseSideData`, restated with every binder explicit.**

Kept in lockstep with the real declaration by the tripwire
`Kakeya.VeryNotSticky.setupCaseSideDataStatement_tripwire` immediately below: if the target's
statement ever changes, that `example` stops typechecking. -/
def SetupCaseSideDataStatement : Prop :=
  ∀ {β ζ exscal ϱ η τ τ' : Real}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
    CaseParams β ζ exscal ϱ η τ τ' →
    PlankFrostmanBudget.{u} β ϱ τ η →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    Kakeya.CoarseKTWindow.{u} β ϱ η exscal →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ')

/- The tripwire `example : SetupCaseSideDataStatement := @exists_setup_caseSideData` lives in
`MainLemma2/VeryNotStickyClosed.lean` since the  A.5 relocation of the leaf downstream of its
producers; this module is upstream of that file. -/

open MeasureTheory Topology Filter ShadedBody in
/-- **The form `Kakeya.VeryNotSticky.SetupCaseSideDataStatement` carried with an unbounded uniformity constant.**

Character for character the pre-F12a statement: its uniformity binder is the unbounded
`∃ C : NNReal, Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)`, which
`Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn` inhabits for *every* family with
pairwise distinct axes (at `C = |s| + 1`), so that binder constrained nothing. The live statement
now demands `1 ≤ C ∧ C ≤ δ^{-η}` — GWZ's `∼1` at the lemma's own exponent — and on every
Lemma 9.1 input (`δ⁻¹ ≤ |s|`) the free witness `|s| + 1` exceeds `δ^{-η}`, so the counterexample
families of the refutation records below no longer discharge the live binder. Those records —
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_concentrated`,
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_flat_island`,
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_carrier_holes` — are therefore stated
against this frozen record, in the house pattern of
`Kakeya.VeryNotSticky.RhoCountFieldOldStatement` and `Kakeya.VeryNotSticky.RigidFullnessField`:
what they proved is kept on the record, and the fact that the bounded binder *excludes* their
witness families is said rather than hidden. `setupCaseSideDataStatement_of_old` records the
direction of the repair: the old statement is the stronger one. Nothing reads this `Prop`. -/
def SetupCaseSideDataStatementOld : Prop :=
  ∀ {β ζ exscal ϱ η τ τ' : Real}, 0 < β → β ≤ 1 → 0 < ζ → 0 < exscal → 0 < ϱ → 0 < η →
    CaseParams β ζ exscal ϱ η τ τ' →
    PlankFrostmanBudget.{u} β ϱ τ η →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    Kakeya.CoarseKTWindow.{u} β ϱ η exscal →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ')

/-- **Direction of the F12a repair, at the setup statement**: the pre-F12a statement implies the
live one, because the live binder's `Nonempty` clause is the whole of the old binder. Not
conversely. -/
theorem setupCaseSideDataStatement_of_old (H : SetupCaseSideDataStatementOld.{u}) :
    SetupCaseSideDataStatement.{u} := by
  intro β ζ exscal ϱ η τ τ' hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
  filter_upwards [H hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w] with δ hδ
  intro ι s T hball _hcen huni hmax hfull hcount
  obtain ⟨C, -, -, hC⟩ := huni
  exact hδ s T hball ⟨C, hC⟩ hmax hfull hcount

open MeasureTheory Topology Filter ShadedBody in
/-- **The setup statement forces at least `δ^{-1}` tubes to be individually `δ^{2η}`-full.**

The chain is: `Kakeya.VeryNotSticky.rpow_two_eta_mul_volume_carrier_le_volume_shade` makes
every tube of `cfg.s` individually `δ^{2η}`-full; `ShadedBody.IsRefinement` keeps the carriers
*equal* and shrinks the shades, so the corresponding tube of the original family is
`δ^{2η}`-full too; hence `cfg.s` injects into the set of individually `δ^{2η}`-full members of
`s`, and `Kakeya.VeryNotSticky.tube_count` (`1 ≤ δ |cfg.s|`) transfers to it.

**History, and why the exponent matters.** With `Kakeya.VeryNotSticky.lam_ge` at `δ^η` this
same chain forced at least `δ^{-1}` tubes to be individually `δ^η`-full, which the target's
binders do not supply: `hfull` is the *aggregate* ratio
`λ(𝕋, Y) = (∑|Y(T)|)/(∑|T|) ≥ δ^η`, and a weighted average bounds no summand — a family of `N`
tubes with one tube fully shaded and the remaining `N-1` at the common density
`(Nδ^η - 1)/(N-1) < δ^η` has aggregate fullness exactly `δ^η` and exactly **one**
individually-`δ^η`-full member. `hmax` and `hcount` constrain the carriers only and `huni`
carries a free constant, so none of them excludes such a shading. The repair was to weaken
`lam_ge` to `Cd δ^{2η} ≤ lam`, and at `δ^{2η}` the demand *is* met:
`Kakeya.VeryNotSticky.sum_volume_shade_lowDensity_le` shows the tubes below that density carry
at most a `δ^η` fraction of the shade mass, so the concentrated family above has all but one
of its members individually `δ^{2η}`-full. The refutation
`Kakeya.VeryNotSticky.not_setupCaseSideDataStatement_of_concentrated` below is kept, restated
at `δ^{2η}`, precisely so that a future re-strengthening of `lam_ge` is caught at once.

The subfamily is described by an arbitrary superset `u` rather than by `Finset.filter` so that
no decidability instance enters the statement.

Here the target's uniformity binder is bounded, and this consequence
is stated twice: for the live `Kakeya.VeryNotSticky.SetupCaseSideDataStatement` (below) and for
the frozen `Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`
(`tubeCount_of_setupCaseSideDataStatementOld`), which the refutation record
`not_setupCaseSideDataStatement_of_concentrated` consumes. Both are the per-`δ` core
`tubeCount_of_setupConclusion`, which reads only the target's *conclusion* at one family — the
binder is never used. -/
theorem tubeCount_of_setupConclusion {β ζ exscal ϱ η τ τ' : Real} {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (u : Finset ι)
    (hδ : ∃ (cfg : VeryNotSticky.{u}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
      (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
          cfg.η = η) ∧
      ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
          (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
          s (fun i ↦ (T i).toShadedBody) c ∧
      (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
      Nonempty (CaseSideData cfg bd τ τ'))
    (hu : ∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).toShadedBody.carrier ≤
        volume (T i).toShadedBody.shade → i ∈ u) :
    (1 : ENNReal) ≤ (δ : ENNReal) * (u.card : ENNReal) := by
  obtain ⟨cfg, -, e, c, hexp, href, -, -⟩ := hδ
  have hδeq : cfg.δ = δ := hexp.2.2.1
  have hηeq : cfg.η = η := hexp.2.2.2.2.2
  -- every member of the refined family is individually `δ^{2η}`-full, and so is its parent
  have hsub : cfg.s.map e.toEmbedding ⊆ u := by
    intro j hj
    obtain ⟨j', hj', hje⟩ := Finset.mem_map.mp hj
    have hjs : j ∈ s := href.1.1 hj
    refine hu j hjs ?_
    obtain ⟨hcar, hsh⟩ := href.1.2 j hj
    have hje' : e.symm j = j' := by
      rw [← hje]; simp
    have hfullj := rpow_two_eta_mul_volume_carrier_le_volume_shade cfg (i := j') hj'
    have hcarvol : volume (cfg.T j').toShadedBody.carrier = volume (T j).toShadedBody.carrier := by
      rw [← hje'] at hfullj ⊢
      exact congrArg (fun B => volume (ConvexSpaceBody.carrier B)) hcar
    calc (δ : ENNReal) ^ (2 * η) * volume (T j).toShadedBody.carrier
        = (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (cfg.T j').toShadedBody.carrier := by
          rw [hcarvol, hδeq, hηeq]
      _ ≤ volume (cfg.T j').toShadedBody.shade := hfullj
      _ ≤ volume (T j).toShadedBody.shade := by
          rw [← hje'] at *
          exact measure_mono hsh
  have hcard : cfg.s.card ≤ u.card := by
    calc cfg.s.card = (cfg.s.map e.toEmbedding).card := (Finset.card_map _).symm
      _ ≤ u.card := Finset.card_le_card hsub
  have hcount' : (1 : ENNReal) ≤ (cfg.δ : ENNReal) * (cfg.s.card : ENNReal) := cfg.tube_count
  rw [hδeq] at hcount'
  refine hcount'.trans ?_
  gcongr

open MeasureTheory Topology Filter ShadedBody in
/-- The tube-count consequence of the live setup statement (see
`tubeCount_of_setupConclusion`). -/
theorem tubeCount_of_setupCaseSideDataStatement (H : SetupCaseSideDataStatement.{u})
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∀ i ∈ s, (T i).toTube.IsCentred) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∀ u : Finset ι,
          (∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).toShadedBody.carrier ≤
              volume (T i).toShadedBody.shade → i ∈ u) →
          (1 : ENNReal) ≤ (δ : ENNReal) * (u.card : ENNReal) := by
  filter_upwards [H hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w] with δ hδ
  intro ι s T hball hcen huni hmax hfull hcount u hu
  exact tubeCount_of_setupConclusion s T u (hδ s T hball hcen huni hmax hfull hcount) hu

open MeasureTheory Topology Filter ShadedBody in
/-- The tube-count consequence of the frozen pre-F12a statement
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld` — the same per-`δ` core
`tubeCount_of_setupConclusion`, read through the old (unbounded) uniformity binder. Consumed by
the refutation record `not_setupCaseSideDataStatement_of_concentrated`. -/
theorem tubeCount_of_setupCaseSideDataStatementOld (H : SetupCaseSideDataStatementOld.{u})
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∀ u : Finset ι,
          (∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).toShadedBody.carrier ≤
              volume (T i).toShadedBody.shade → i ∈ u) →
          (1 : ENNReal) ≤ (δ : ENNReal) * (u.card : ENNReal) := by
  filter_upwards [H hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w] with δ hδ
  intro ι s T hball huni hmax hfull hcount u hu
  exact tubeCount_of_setupConclusion s T u (hδ s T hball huni hmax hfull hcount) hu

open MeasureTheory Topology Filter ShadedBody in
/-- **The setup statement is refuted by any family with few individually-`δ^{2η}`-full tubes.**

The tripwire that keeps the repair of `Kakeya.VeryNotSticky.lam_ge` honest: if, for arbitrarily
small `δ`, there is a family satisfying all five binders of the target whose
individually-`δ^{2η}`-full members number fewer than `δ^{-1}`, the target is false.

At the *previous* exponent `δ^η` such a witness was free — `hfull` is an aggregate ratio,
`hmax` and `hcount` constrain the carriers only, and `huni` carries a free constant, so a
concentrated shading satisfies every binder while having exactly one individually-`δ^η`-full
member. At `δ^{2η}` the hypothesis `hwit` is no longer free:
`Kakeya.VeryNotSticky.sum_volume_shade_lowDensity_le` bounds the shade mass of the
non-`δ^{2η}`-full tubes by a `δ^η` fraction of the total, so the tubes that *are*
individually `δ^{2η}`-full carry all but a `δ^η` fraction of the mass, and `hcount` forces
`|s| ≫ δ^{-1}`. This declaration is retained, restated at `δ^{2η}`, so that any future
re-strengthening of `lam_ge` immediately re-exposes the defect rather than hiding it.

The witness is stated as an eventual hypothesis rather than at one scale because the target's
own conclusion is eventual: a single bad `δ` need not lie in the target's threshold set.

**This counterexample concerns the frozen
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`, not the live statement.** The witness
`hwit` discharges the uniformity binder in its old, unbounded form; the live binder demands
`1 ≤ C ≤ δ^{-η}`, and on every Lemma 9.1 input (`δ⁻¹ ≤ |s|`) the free witness `C = |s| + 1` of
`Kakeya.VeryNotSticky.exists_shadedUniformTubeSet_of_axes_injOn` exceeds that bound, so a
concentrated family is excluded by the bounded binder unless it is genuinely uniform at a
sub-polynomial constant. The derivation is unchanged; only its target moved, in the house pattern
of `Kakeya.VeryNotSticky.RhoCountFieldOldStatement`. -/
theorem not_setupCaseSideDataStatement_of_concentrated
    {β ζ exscal ϱ η τ τ' : Real} (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal)
    (hϱ : 0 < ϱ) (hη : 0 < η) (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hwit : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∃ (ι : Type u) (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (u : Finset ι),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) ∧
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) ∧
        (∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).toShadedBody.carrier ≤
            volume (T i).toShadedBody.shade → i ∈ u) ∧
        (δ : ENNReal) * (u.card : ENNReal) < 1)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ¬ SetupCaseSideDataStatementOld.{u} := by
  intro H
  obtain ⟨δ, hforce, ι, s, T, u, hball, huni, hmax, hfull, hcount, hu, hlt⟩ :=
    ((tubeCount_of_setupCaseSideDataStatementOld H hβ hβ1 hζ hexscal hϱ hη params hplankF hKT
        hF w).and hwit).exists
  exact absurd (hforce s T hball huni hmax hfull hcount u hu) (not_le.mpr hlt)

/-! ### Guardrail: the slack the repaired fullness clause buys

The companion of the block above for `Kakeya.VeryNotSticky.fullness_ge`. The *rigidity* half —
that an aggregate fullness clause asserted at exactly the value the input family already attains
forbids deleting any shading mass at all — is `Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge`
in `Kakeya.DimensionThree.MainLemma2.BallJoint`, which is the termwise form and is the one the
refutation `Kakeya.VeryNotSticky.not_rigidFullnessField_of_flat_island` consumes. What is recorded
here is the other half: at the repaired exponent that rigidity **cannot fire**, because its
hypothesis is incompatible with the target's own binder.
-/

open MeasureTheory ShadedBody in
/-- **The slack the repair buys, and it is exactly one `η`.**

At the repaired exponent the rigidity above cannot fire, because its hypothesis
`λ(𝕋, Y) ≤ δ^{2η}` is *incompatible* with the binder `λ(𝕋, Y) ≥ δ^η` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`: for `δ < 1` and `η > 0` one has
`δ^{2η} < δ^{η}`. So a producer handed the binder is free to delete up to a `1 - δ^η` fraction
of the shading mass and still meet `Kakeya.VeryNotSticky.fullness_ge`, which is what the
refinement budget `δ^η ≤ c` of the target's own conclusion pays for.

This is the compiled form of "the repair is a factor `δ^η` of room", and together with
`Kakeya.VeryNotSticky.volume_shade_eq_of_fullness_ge` (the rigidity itself) and
`Kakeya.VeryNotSticky.not_rigidFullnessField_of_flat_island` (the refutation it powers) it is the
whole check of the change: the old exponent had no room, the new one has exactly `δ^η`. -/
theorem not_fullness_le_rpow_two_eta {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {δ : NNReal} {η : Real}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hbind : δ ^ η ≤ ShadedBody.fullness s V) :
    ¬ (ShadedBody.fullness s V ≤ δ ^ (2 * η)) := by
  intro hle
  have hlt : δ ^ (2 * η) < δ ^ η :=
    NNReal.rpow_lt_rpow_of_exponent_gt hδ hδ1 (by linarith)
  exact absurd (hbind.trans hle) (not_le.2 hlt)

/-! ### The density band: `lam`, `Cd`, `lam_ge`, `shading_lb`, `shading_ub` are now deliverable

The five fields `Kakeya.VeryNotSticky.lam`, `Cd`, `lam_ge`, `shading_lb`, `shading_ub` were the
one group of the configuration whose satisfiability was *in doubt*, not merely unformalized: at
the old exponent `lam_ge : Cd δ^η ≤ lam` they contradict the aggregate binder `hfull` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` (that is
`Kakeya.VeryNotSticky.tubeCount_of_setupCaseSideDataStatement`). At the repaired
`Cd δ^{2η} ≤ lam` they are deliverable, and the two lemmas below are the proof — not an
accounting statement, an actual construction:

* `Kakeya.VeryNotSticky.exists_isCRefinement_pointwise_density` turns the *aggregate* ratio
  into a *pointwise* density bound at a lower level, at the cost of a refinement constant. This
  is the step that has no analogue at level `δ^η`;
* `Kakeya.VeryNotSticky.exists_shadingBand` then feeds it to the repository's dyadic density
  pigeonhole `Kakeya.ShadedBody.exists_isCRefinement_comparable_density` and packages the output
  in exactly the shape of the three fields, at `Cd = 2`.

Read at `a = δ^η` (the binder), `q = δ^η` and `θ = δ^{2η}` (the repaired level) the composite
refinement constant is `(1 - δ^η) · (1 + log₂ δ^{-2η})⁻¹`, which exceeds `δ^η` for all small
`δ`, so the target's own conjunct `δ^η ≤ c` is met with room. At `θ = δ^η` the hypothesis
`hθq : θ ≤ q · a` would force `q ≥ 1` and the refinement constant `1 - q` would be `0`: the
obstruction and the repair are visible in the same inequality.
-/

open MeasureTheory Topology Filter ShadedBody in
/-- **From aggregate fullness to pointwise fullness at a lower level** — the Markov step of the
density-band pigeonhole, as a refinement.

If `λ(𝕍, Y) ≥ a` and `θ ≤ q · a` with `q ≤ 1`, then the members that are individually
`θ`-full form a `(1 - q)`-refinement: the members that are *not* carry at most a `q` fraction
of the shade mass.

This is `Kakeya.VeryNotSticky.sum_volume_shade_lowDensity_le` packaged as a
`ShadedBody.IsCRefinement`, and it is the step the target needs and the reason
`Kakeya.VeryNotSticky.lam_ge` had to move from `δ^η` to `δ^{2η}`: at `θ = a` the hypothesis
`hθq` forces `q = 1` and the conclusion degenerates to the trivial refinement constant `0`.
Nothing is assumed about the carriers — no common volume, no comparability — and the subfamily
is `Finset.filter`ed rather than existentially opaque only inside the proof; the statement
exposes it as an arbitrary `s' ⊆ s`, so no decidability instance leaks out. -/
theorem exists_isCRefinement_pointwise_density {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {a θ q : NNReal}
    (ha : 0 < a) (hfull : a ≤ ShadedBody.fullness s V) (hq1 : q ≤ 1) (hθq : θ ≤ q * a) :
    ∃ s' ⊆ s,
      (∀ i ∈ s', (θ : ENNReal) * volume (V i).carrier ≤ volume (V i).shade) ∧
      ShadedBody.IsCRefinement s' V s V (1 - q) := by
  classical
  set P : ι → Prop := fun i ↦ (θ : ENNReal) * volume (V i).carrier ≤ volume (V i).shade with hP
  set X : ENNReal := ∑ i ∈ s, volume (V i).shade with hX
  have hXtop : X ≠ ⊤ := by
    rw [hX]
    refine ne_of_lt (lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦
      measure_mono (V i).shade_subset) ?_)
    exact ENNReal.sum_lt_top.2 fun i _ ↦ (V i).isCompact.measure_lt_top
  have hlow : ∀ i ∈ s.filter (fun i ↦ ¬ P i),
      volume (V i).shade ≤ (θ : ENNReal) * volume (V i).carrier := by
    intro i hi
    exact le_of_not_ge (Finset.mem_filter.mp hi).2
  have hMark := sum_volume_shade_lowDensity_le (Finset.filter_subset _ s) hfull hlow
  have hane : (a : ENNReal) ≠ 0 := by
    simpa using ha.ne'
  have hatop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hu : ∑ i ∈ s.filter (fun i ↦ ¬ P i), volume (V i).shade ≤ (q : ENNReal) * X := by
    refine (ENNReal.mul_le_mul_iff_right hane hatop).mp ?_
    refine hMark.trans ?_
    calc (θ : ENNReal) * X ≤ ((q * a : NNReal) : ENNReal) * X := by
          gcongr
      _ = (a : ENNReal) * ((q : ENNReal) * X) := by
          rw [ENNReal.coe_mul]; ring
  have hsplit : ∑ i ∈ s.filter P, volume (V i).shade
      + ∑ i ∈ s.filter (fun i ↦ ¬ P i), volume (V i).shade = X :=
    Finset.sum_filter_add_sum_filter_not s P _
  have hqXtop : (q : ENNReal) * X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hXtop
  have hone : ((1 - q : NNReal) : ENNReal) + (q : ENNReal) = 1 := by
    rw [← ENNReal.coe_add, tsub_add_cancel_of_le hq1, ENNReal.coe_one]
  have hkey : ((1 - q : NNReal) : ENNReal) * X ≤ ∑ i ∈ s.filter P, volume (V i).shade := by
    refine (ENNReal.add_le_add_iff_right hqXtop).mp ?_
    calc ((1 - q : NNReal) : ENNReal) * X + (q : ENNReal) * X
        = X := by rw [← add_mul, hone, one_mul]
      _ = ∑ i ∈ s.filter P, volume (V i).shade
            + ∑ i ∈ s.filter (fun i ↦ ¬ P i), volume (V i).shade := hsplit.symm
      _ ≤ ∑ i ∈ s.filter P, volume (V i).shade + (q : ENNReal) * X := by gcongr
  exact ⟨s.filter P, Finset.filter_subset _ _,
    fun i hi ↦ (Finset.mem_filter.mp hi).2,
    ⟨Finset.filter_subset _ _, fun i _ ↦ ⟨rfl, subset_rfl⟩⟩, hkey⟩

open MeasureTheory Topology Filter ShadedBody in
/-- **The shading band of Configuration `hyp:ml2setup`, from the aggregate fullness binder
alone.**

Given a family of equal-carrier-volume shaded bodies with `λ(𝕍, Y) ≥ a`, and a density floor
`θ ≤ q · a` with `q < 1`, there is a subfamily and a `lam > 0` with

* `Cd · θ ≤ lam` at `Cd = 2` — the field `Kakeya.VeryNotSticky.lam_ge` at `θ = δ^{2η}`;
* `Cd⁻¹ · lam · |V| ≤ |Y(V)| ≤ Cd · lam · |V|` on the subfamily — the fields
  `Kakeya.VeryNotSticky.shading_lb` and `Kakeya.VeryNotSticky.shading_ub`;
* and the subfamily is a `(1 - q) · (1 + log₂ θ^{-1})⁻¹`-refinement of the original.

So the whole `(lam, Cd, lam_ge, shading_lb, shading_ub)` group of the configuration is
**deliverable** from the target's aggregate binder — at the repaired exponent, and only there.
The equal-volume hypothesis `hvol` is the one the repository's pigeonhole
`Kakeya.ShadedBody.exists_isCRefinement_comparable_density` asks for; for a family of
`Kakeya.ShadedTube δ` it is `Tube.volume_carrier_eq_volume_carrier`, a proved equality,
so it costs the producer nothing. Nonemptiness of the subfamily is *derived*, not assumed:
`(1 - q) > 0` and the total shade mass is positive because the fullness is.

`Cd = 2` is the dyadic band's own comparison constant, and it is exactly the `Cd = 2` that the
docstring of `Kakeya.VeryNotSticky.lam_ge` identifies as what the `⪆` of GWZ §9 hides. -/
theorem exists_shadingBand {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {v : ENNReal}
    (hvol : ∀ i ∈ s, volume (V i).carrier = v) (hv : v ≠ 0)
    {a θ q : NNReal} (ha : 0 < a) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hfull : a ≤ ShadedBody.fullness s V) (hq1 : q < 1) (hθq : θ ≤ q * a) :
    ∃ s₂ ⊆ s, ∃ lam : NNReal, 0 < lam ∧ 2 * θ ≤ lam ∧
      (∀ i ∈ s₂,
        (2 : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier) ≤ volume (V i).shade ∧
          volume (V i).shade ≤ (2 : ENNReal) * ((lam : ENNReal) * volume (V i).carrier)) ∧
      ShadedBody.IsCRefinement s₂ V s V
        ((1 - q) * ((1 + Real.logb 2 ((θ : ℝ))⁻¹).toNNReal)⁻¹) := by
  classical
  obtain ⟨s', hs's, hdense, href⟩ :=
    exists_isCRefinement_pointwise_density ha hfull hq1.le hθq
  -- `s'` is nonempty: it carries a `(1 - q) > 0` share of a positive shade mass.
  have hXne : ∑ i ∈ s, volume (V i).shade ≠ 0 := by
    intro h0
    have hz : ShadedBody.fullness s V = 0 := by
      have hc := ShadedBody.fullness_def s V
      have : ((ShadedBody.fullness s V : NNReal) : ENNReal) = 0 := by
        rw [hc, h0, ENNReal.zero_div]
      exact_mod_cast this
    rw [hz] at hfull
    exact absurd (le_antisymm hfull (by simp)) ha.ne'
  have hqne : (1 - q : NNReal) ≠ 0 := by
    have : 0 < 1 - q := tsub_pos_of_lt hq1
    exact this.ne'
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with hemp | hne
    · exfalso
      have hm := href.2
      rw [hemp] at hm
      simp only [Finset.sum_empty, nonpos_iff_eq_zero] at hm
      rcases mul_eq_zero.mp hm with h | h
      · exact hqne (by exact_mod_cast h)
      · exact hXne h
    · exact hne
  obtain ⟨s₂, hs₂s', lam₀, hlam₀pos, href₂, hband, hθlam, -⟩ :=
    ShadedBody.exists_isCRefinement_comparable_density (s := s') (V := V) (a := θ) (v := v)
      hs'ne (fun i hi ↦ hvol i (hs's hi)) hv hθ0 hθ1 hdense
  refine ⟨s₂, hs₂s'.trans hs's, 2 * lam₀, by positivity, by
    exact mul_le_mul_of_nonneg_left hθlam (by simp), ?_, href₂.trans href⟩
  intro i hi
  obtain ⟨hlo, hhi⟩ := hband i hi
  have hcoe : ((2 * lam₀ : NNReal) : ENNReal) = 2 * (lam₀ : ENNReal) := by
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hcoe]
    calc (2 : ENNReal)⁻¹ * (2 * (lam₀ : ENNReal) * volume (V i).carrier)
        = (lam₀ : ENNReal) * volume (V i).carrier := by
          rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
      _ ≤ volume (V i).shade := hlo
  · rw [hcoe]
    calc volume (V i).shade ≤ 2 * (lam₀ : ENNReal) * volume (V i).carrier := hhi
      _ ≤ 2 * (2 * (lam₀ : ENNReal) * volume (V i).carrier) :=
          le_mul_of_one_le_left zero_le one_le_two

/-! ### What the shading band does *not* buy: no lower bound on the shaded union

Recorded because it was asked for, and because the answer is negative and worth having in
compiled form rather than in prose.
-/

open MeasureTheory Topology Filter ShadedBody in
/-- **The shading band bounds the multiplicity only by the cardinality.**

`∑_i |Y(V_i)| ≤ Cd² |𝕍| · |U(𝕍, Y)|`, from `shading_ub` on the numerator, `shading_lb` on a
*single* member (`Y(V_{i₀}) ⊆ U`), and the equal carrier volumes. Nothing better is available:
the two band inequalities constrain each shade only against its own carrier, so the only way
they see the union is through one member of it.

**Consequence, and it is the point of this declaration.** A field on
`Kakeya.VeryNotSticky` asserting `δ^η · ∑_i |Y(T_i)| ≤ |U(𝕋, Y)|` — equivalently
`μ(𝕋, Y) ≤ δ^{-η}` — is **not** supplied by anything a producer of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` has. What the construction can supply is this
inequality, i.e. `μ ≤ Cd² |𝕋|`, and `|𝕋|` is only bounded by `≈ δ^{-2-η}`: the field
`Kakeya.VeryNotSticky.maxDensity_le` bounds `Kakeya.maxDensity`, which is built from
`Kakeya.densityIn` and therefore counts only tubes *contained* in the convex test body, and a
bush of tubes through one point has a convex hull of unit volume, so density says nothing about
pointwise multiplicity. Such a field would be unsatisfiable at any exponent better than `2 + η`
and must not be added. -/
theorem sum_volume_shade_le_card_mul_volume_iUnion {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {v : ENNReal}
    (hs : s.Nonempty) (hvol : ∀ i ∈ s, volume (V i).carrier = v)
    {Cd lam : NNReal} (hCd : 1 ≤ Cd)
    (hlb : ∀ i ∈ s,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier) ≤ volume (V i).shade)
    (hub : ∀ i ∈ s,
      volume (V i).shade ≤ (Cd : ENNReal) * ((lam : ENNReal) * volume (V i).carrier)) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (Cd : ENNReal) ^ 2 * (s.card : ENNReal) * volume (⋃ i ∈ s, (V i).shade) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs
  have hCd0 : (Cd : ENNReal) ≠ 0 := by
    have : (0 : NNReal) < Cd := lt_of_lt_of_le zero_lt_one hCd
    simpa using this.ne'
  have hCdtop : (Cd : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hU : (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * v) ≤ volume (⋃ i ∈ s, (V i).shade) := by
    refine le_trans ?_ (measure_mono (Set.subset_biUnion_of_mem (u := fun i ↦ (V i).shade) hi₀))
    rw [← hvol i₀ hi₀]
    exact hlb i₀ hi₀
  have hsum : ∑ i ∈ s, volume (V i).shade
      ≤ (s.card : ENNReal) * ((Cd : ENNReal) * ((lam : ENNReal) * v)) := by
    calc ∑ i ∈ s, volume (V i).shade
        ≤ ∑ _i ∈ s, (Cd : ENNReal) * ((lam : ENNReal) * v) := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          rw [← hvol i hi]
          exact hub i hi
      _ = (s.card : ENNReal) * ((Cd : ENNReal) * ((lam : ENNReal) * v)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  refine hsum.trans ?_
  calc (s.card : ENNReal) * ((Cd : ENNReal) * ((lam : ENNReal) * v))
      = ((Cd : ENNReal) ^ 2 * (s.card : ENNReal)) *
          ((Cd : ENNReal)⁻¹ * ((lam : ENNReal) * v)) := by
        rw [sq]
        rw [show (Cd : ENNReal) * (Cd : ENNReal) * (s.card : ENNReal) *
              ((Cd : ENNReal)⁻¹ * ((lam : ENNReal) * v))
            = ((Cd : ENNReal) * (Cd : ENNReal)⁻¹) *
              ((Cd : ENNReal) * (s.card : ENNReal) * ((lam : ENNReal) * v)) by ring,
          ENNReal.mul_inv_cancel hCd0 hCdtop, one_mul]
        ring
    _ ≤ ((Cd : ENNReal) ^ 2 * (s.card : ENNReal)) * volume (⋃ i ∈ s, (V i).shade) := by
        gcongr

open MeasureTheory Topology Filter ShadedBody in
/-- `Kakeya.VeryNotSticky.sum_volume_shade_le_card_mul_volume_iUnion` read as a multiplicity
bound: the shading band gives `μ(𝕍, Y) ≤ Cd² |𝕍|` and nothing sharper. -/
theorem multiplicity_le_of_shadingBand {ι : Type*} {s : Finset ι}
    {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {v : ENNReal}
    (hs : s.Nonempty) (hvol : ∀ i ∈ s, volume (V i).carrier = v)
    {Cd lam : NNReal} (hCd : 1 ≤ Cd)
    (hlb : ∀ i ∈ s,
      (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier) ≤ volume (V i).shade)
    (hub : ∀ i ∈ s,
      volume (V i).shade ≤ (Cd : ENNReal) * ((lam : ENNReal) * volume (V i).carrier)) :
    ShadedBody.multiplicity s V ≤ (Cd : ENNReal) ^ 2 * (s.card : ENNReal) :=
  (ShadedBody.multiplicity_le_iff s V).mpr
    (sum_volume_shade_le_card_mul_volume_iUnion hs hvol hCd hlb hub)

/-! ### The repair is quantitatively sufficient, not merely shape-compatible

`Kakeya.VeryNotSticky.exists_shadingBand` produces a refinement constant
`(1 - q) · (1 + log₂ θ^{-1})⁻¹`. The target's own conjunct demands `δ^η ≤ c`. The two lemmas
below check that at the intended parameters the demand is met — the logarithmic loss of the
dyadic band is sub-polynomial, so it is beaten by `δ^η` for all small `δ` — and then package
the whole chain in the exact form a producer of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` consumes.
-/

open MeasureTheory Topology Filter in
/-- **The composite refinement constant of the density band beats `δ^η`.**

`δ^η ≤ (1 - δ^η) · (1 + log₂ δ^{-2η})⁻¹` for all small `δ`, which is the conjunct
`(δ : ENNReal)^η ≤ (c : ENNReal)` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` read at
the constant `Kakeya.VeryNotSticky.exists_shadingBand` delivers at `a = q = δ^η`,
`θ = δ^{2η}`.

The Markov half costs the factor `1 - δ^η ≥ 1/2`; the dyadic half costs
`(1 + 2η log₂ δ^{-1})⁻¹`, a *logarithmic* loss, and `Kakeya.linlog_le` is exactly the statement
that a logarithm is beaten by every positive power. So the price of the whole density-band
pigeonhole is sub-polynomial and the target's refinement budget pays for it with room to
spare. -/
theorem eventually_shadingBand_refinement_ge {η : Real} (hη : 0 < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      d ^ η ≤ (1 - d ^ η) *
        ((1 + Real.logb 2 (((d ^ (2 * η) : NNReal) : Real))⁻¹).toNNReal)⁻¹ := by
  have hlog2 : (0:Real) < Real.log 2 := Real.log_pos (by norm_num)
  set Kc : Real := 1 + (2 * η / Real.log 2) / (η / 2) with hKc
  have hKc0 : (0:Real) < Kc := by
    rw [hKc]
    have h : (0:Real) ≤ (2 * η / Real.log 2) / (η / 2) := by positivity
    linarith
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_nnreal_mul_rpow_le_const 1 (1/2) (by norm_num) hη,
    eventually_nnreal_mul_rpow_le_const (Real.toNNReal Kc) (1/2) (by norm_num)
      (show (0:Real) < η / 2 by linarith)] with d hd0 hd1 hhalf hK
  have hdpos : (0:NNReal) < d := by simpa using hd0
  have hdR : (0:Real) < (d:Real) := by exact_mod_cast hdpos
  have hd1R : (d:Real) < 1 := by exact_mod_cast hd1
  have hcoe : ((d ^ (2 * η) : NNReal) : Real) = (d:Real) ^ (2 * η) := NNReal.coe_rpow d _
  set L : Real := 1 + Real.logb 2 (((d ^ (2 * η) : NNReal) : Real))⁻¹ with hLdef
  have hlogpos : (0:Real) ≤ Real.log (d:Real)⁻¹ := by
    rw [Real.log_inv]; linarith [Real.log_nonpos hdR.le hd1R.le]
  have hLform : L = 1 + (2 * η / Real.log 2) * Real.log (d:Real)⁻¹ := by
    rw [hLdef, hcoe, Real.logb, Real.log_inv, Real.log_rpow hdR, Real.log_inv]
    field_simp
  have hL1 : (1:Real) ≤ L := by
    rw [hLform]
    have h : (0:Real) ≤ (2 * η / Real.log 2) * Real.log (d:Real)⁻¹ := by positivity
    linarith
  have hL0 : (0:Real) ≤ L := by linarith
  have hLle : L ≤ Kc * (d:Real) ^ (-(η/2)) := by
    rw [hLform, hKc]
    exact linlog_le (by norm_num) (by positivity) (by linarith) hdR hd1R.le
  have hLnn0 : L.toNNReal ≠ 0 := by
    have hpos : (0:Real) < L := lt_of_lt_of_le zero_lt_one hL1
    simp [Real.toNNReal_eq_zero, not_le.mpr hpos]
  rw [mul_comm (1 - d ^ η) (L.toNNReal)⁻¹, ← div_eq_inv_mul,
    le_div_iff₀ (pos_iff_ne_zero.mpr hLnn0)]
  have hhalf' : d ^ η ≤ (1/2 : NNReal) := by simpa using hhalf
  have hlow : (1/2 : NNReal) ≤ 1 - d ^ η := by
    refine le_tsub_of_add_le_left ?_
    calc d ^ η + (1/2:NNReal) ≤ 1/2 + 1/2 := by gcongr
      _ = 1 := by norm_num
  refine le_trans ?_ hlow
  have hcast : ((d ^ η * L.toNNReal : NNReal) : Real) = (d:Real) ^ η * L := by
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal L hL0]
  have hKR : Kc * (d:Real) ^ (η/2) ≤ 1/2 := by
    have h := NNReal.coe_le_coe.mpr hK
    rw [NNReal.coe_mul, NNReal.coe_rpow, Real.coe_toNNReal Kc hKc0.le] at h
    simpa using h
  have hfin : ((d ^ η * L.toNNReal : NNReal) : Real) ≤ ((1/2 : NNReal) : Real) := by
    rw [hcast]
    have hstep : (d:Real) ^ η * L ≤ (d:Real) ^ η * (Kc * (d:Real) ^ (-(η/2))) := by
      have hp : (0:Real) < (d:Real) ^ η := Real.rpow_pos_of_pos hdR η
      exact mul_le_mul_of_nonneg_left hLle hp.le
    refine hstep.trans ?_
    have heq : (d:Real) ^ η * (Kc * (d:Real) ^ (-(η/2))) = Kc * (d:Real) ^ (η/2) := by
      rw [show (d:Real) ^ η * (Kc * (d:Real) ^ (-(η/2)))
          = Kc * ((d:Real) ^ η * (d:Real) ^ (-(η/2))) by ring,
        ← Real.rpow_add hdR]
      congr 2
      ring
    rw [heq]
    simpa using hKR
  exact_mod_cast hfin

open MeasureTheory Topology Filter ShadedBody in
/-- **The density band of Configuration `hyp:ml2setup`, end to end, at the target's own
parameters.**

For all sufficiently small `δ`: every equal-carrier-volume family whose *aggregate* fullness is
at least `δ^η` — the binder `hfull` of `Kakeya.VeryNotSticky.exists_setup_caseSideData`
verbatim — has a subfamily and a `lam > 0` with

* `2 · δ^{2η} ≤ lam`, i.e. the repaired field `Kakeya.VeryNotSticky.lam_ge` at `Cd = 2`;
* `Cd⁻¹ lam |V| ≤ |Y(V)| ≤ Cd lam |V|` on the subfamily, i.e.
  `Kakeya.VeryNotSticky.shading_lb` and `Kakeya.VeryNotSticky.shading_ub`;
* and a refinement constant `c` with `δ^η ≤ c`, i.e. the target's own conjunct.

**This is the compiler-checked statement that the `lam_ge` repair is exactly right.** At the old
exponent the same construction is impossible: `Kakeya.VeryNotSticky.exists_shadingBand` needs
`θ ≤ q · a`, so at `θ = a = δ^η` it forces `q = 1` and the Markov refinement constant `1 - q`
collapses to `0`; and independently
`Kakeya.VeryNotSticky.tubeCount_of_setupCaseSideDataStatement` shows the old exponent demands
`δ^{-1}` individually-`δ^η`-full tubes, which an aggregate ratio cannot supply. At `2η` both
obstructions vanish and the price is only the sub-polynomial
`(1 - δ^η)(1 + 2η log₂ δ^{-1})⁻¹`.

What is *not* claimed: the rest of the configuration. This closes the five fields
`lam`, `Cd`, `lam_ge`, `shading_lb`, `shading_ub` and nothing else; `rho_count` for the refined
family, `uniform`, the biased factoring and the whole of
`Kakeya.VeryNotSticky.BallData` remain open. -/
theorem eventually_exists_shadingBand_eta {η : Real} (hη : 0 < η) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ∀ {ι : Type u} {s : Finset ι} {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
        {v : ENNReal},
        (∀ i ∈ s, volume (V i).carrier = v) → v ≠ 0 →
        d ^ η ≤ ShadedBody.fullness s V →
        ∃ s₂ ⊆ s, ∃ lam : NNReal, 0 < lam ∧ 2 * d ^ (2 * η) ≤ lam ∧
          (∀ i ∈ s₂,
            (2 : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier) ≤ volume (V i).shade ∧
              volume (V i).shade ≤ (2 : ENNReal) * ((lam : ENNReal) * volume (V i).carrier)) ∧
          ∃ c : NNReal, d ^ η ≤ c ∧ ShadedBody.IsCRefinement s₂ V s V c := by
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2
  filter_upwards [self_mem_nhdsWithin, hsmall, eventually_shadingBand_refinement_ge hη]
    with d hd0 hd1 hcgood
  intro ι s V v hvol hv hfull
  have hdpos : (0:NNReal) < d := by simpa using hd0
  have hdne : d ≠ 0 := hdpos.ne'
  have ha : 0 < d ^ η := NNReal.rpow_pos hdpos
  have hθ0 : 0 < d ^ (2 * η) := NNReal.rpow_pos hdpos
  have hθ1 : d ^ (2 * η) ≤ 1 := NNReal.rpow_le_one hd1.le (by linarith)
  have hq1 : d ^ η < 1 := NNReal.rpow_lt_one hd1 hη
  have hθq : d ^ (2 * η) ≤ d ^ η * d ^ η := by
    rw [← NNReal.rpow_add hdne]
    exact le_of_eq (by congr 1; ring)
  obtain ⟨s₂, hs₂, lam, hlampos, hlamge, hband, href⟩ :=
    exists_shadingBand (v := v) hvol hv ha hθ0 hθ1 hfull hq1 hθq
  exact ⟨s₂, hs₂, lam, hlampos, hlamge, hband, _, hcgood, href⟩

end Kakeya.VeryNotSticky
