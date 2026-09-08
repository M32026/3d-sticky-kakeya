/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.Bridge
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# Ports between the uniform bridge and the dichotomy

The Katz-Tao readings of the uniform bridge, and the reading of a Frostman constant against a
cover class that the two upper bounds of the dichotomy consume.

This module is the merge of the former `UniformBridgeKTPorts`, `FrostmanClassRead`.  Each keeps its
own section, so its file-level `open`s and `variable`s stay confined to it.

## The two alternatives of GWZ Lemma 7.7(B) with the grid length separated from the step bound

`Kakeya/MultiScaleFac/UniformBridgeKT.lean` states both alternatives on a grid whose length is
the *same* natural number `N` that bounds the number of stopping-time steps.  The amended dichotomy
`Kakeya.MultiScaleFac.dividingScalesKatzTao` runs on the grid of length `ssfGridLen δ`, which
grows with `δ`, while `N` stays fixed.  The two statements of this file are therefore the same two
alternatives with the grid length `Mgrid` a parameter of its own and `ε = 1/√N` still governed by
the step bound.

Two things change beyond the renaming.

* The accumulated constant is displayed as an explicit power `Q^{Mgrid+1}` (resp. `Q^{Mgrid+2}`) of
  a base `Q` quantified *before* `Mgrid`, instead of being hidden inside a single existential
  constant.  A hidden constant would be allowed to depend on the grid length, hence on `δ`, which
  is exactly what the amended dichotomy forbids.  That the base can be hoisted out is the content
  of the hoisted forms of `Kakeya.MultiScaleFac.exists_maxDensity_parent_le_of_index` and
  `Kakeya.MultiScaleFac.exists_maxDensity_parent_le_of_cutIndex`.
* Alternative (ii) states the admissible range of the interior index `c` as the *index* window
  `a + ⌈ε(b-a)⌉ ≤ c ≤ b - ⌈ε(b-a)⌉` rather than as a window of grid scales.  That is the form the
  assembly consumes (`Kakeya.MultiScaleFac.KT.bulletThreeGen`), and it is the only form the proof
  ever uses: `Kakeya.MultiScaleFac.grid_window_admissible` converts a scale window into it, and
  `Kakeya.MultiScaleFac.alternative_two_of_terminal_blockKT_grid` records that conversion.

The absorption of `Q^{Mgrid+1}` into `totalLoss` is the last group of lemmas; it needs
`Mgrid ≤ ssfGridLen δ`, which is how a bound growing with the grid length is paid for at all.

## Reading a grid Frostman bound directly at the nodes

The producers of alternative (i) of GWZ Lemma 7.7(A) in `Kakeya/MultiScaleFac/Assembly.lean` all
hold a `Tube.UniformTubeSet` on the *same* index set `s` that carries their fibre Frostman
bounds. Whenever that is so, the environment-level predicate
`Kakeya.StickyKakeya.IsFrostmanAtEveryScale` is an unnecessary detour: the node reading
`StickyKakeya.UniformTubeSet.IsFrostmanAtEveryScale` is available directly from the *grid* bounds
through `MultiScaleFac.isFrostmanIn_coverClass_of_fibre_grid`.

Taking that route is not merely a simplification.  The environment-level route has to interpolate
the grid bounds to every real scale `ρ ∈ [δ, 1]` before it can even state its conclusion, and that
interpolation costs a factor `δ^{-12ε²}` (`MultiScaleFac.isFrostmanAtEveryScale_of_grid_bounds`).
The node reading never leaves the grid, so it keeps the grid exponent unchanged.

The two results here are the node-reading counterparts of
`MultiScaleFac.isFrostmanAtEveryScale_of_grid_bounds_factor` and
`MultiScaleFac.isFrostmanAtEveryScale_of_cuts`.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cv : NNReal}

/-! ### Paying a power of the grid length with `totalLoss` -/

/-- **A power whose exponent is the grid length is a `gridLoss`.**  Since `gridLoss A K δ` carries
the factor `A^{ssfGridLen δ + 1}`, a power `Q^{M+2}` with `M ≤ ssfGridLen δ` is bounded by the loss
at base `Q²`.  Stated on the real product underlying `totalLoss`; `pow_le_totalLoss` below reads it
off the displayed loss. -/
private theorem pow_le_gridLoss_mul_scaleGapLoss {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) :
    (Q : ℝ) ^ (M + 2) ≤ gridLoss (Q ^ 2) K δ * scaleGapLoss c δ := by
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hbase : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
    have := Real.log_nonpos (by positivity) hδ1'; linarith
  calc
    (Q : ℝ) ^ (M + 2) ≤ (Q : ℝ) ^ (2 * (ssfGridLen δ + 1)) :=
        pow_le_pow_right₀ (by exact_mod_cast hQ) (by omega)
    _ = ((Q ^ 2 : NNReal) : ℝ) ^ (ssfGridLen δ + 1) := by rw [NNReal.coe_pow, ← pow_mul]
    _ ≤ gridLoss (Q ^ 2) K δ :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hbase)
    _ ≤ gridLoss (Q ^ 2) K δ * scaleGapLoss c δ :=
        le_mul_of_one_le_right
          (zero_le_one.trans (one_le_gridLoss (Q ^ 2) (one_le_pow₀ hQ) K hδ1))
          (one_le_scaleGapLoss c hδ hδ1)

/-- **A power whose exponent is the grid length is a `gridLoss`.**  Since `gridLoss A K δ` carries
the factor `A^{ssfGridLen δ + 1}`, a power `Q^{M+2}` with `M ≤ ssfGridLen δ` is bounded by the loss
at base `Q²`.  This is the only reason the two alternatives may be stated with a base quantified
before `δ` and still be absorbed. -/
theorem pow_le_totalLoss {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) :
    (Q : ℝ) ^ (M + 2) ≤ (totalLoss (Q ^ 2) K c δ).toReal := by
  rw [totalLoss_toReal (Q ^ 2) (one_le_pow₀ hQ) K c hδ hδ1]
  exact pow_le_gridLoss_mul_scaleGapLoss hQ hδ hδ1 hM K c

/-- The same bound in `[0,∞]`, for the every-scale error of alternative (i). -/
theorem pow_le_ofReal_totalLoss {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) :
    (Q : ENNReal) ^ (M + 2) ≤ totalLoss (Q ^ 2) K c δ := by
  rw [totalLoss_eq_ofReal, ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow]
  exact ENNReal.ofReal_le_ofReal (pow_le_gridLoss_mul_scaleGapLoss hQ hδ hδ1 hM K c)

/-- The `ENNReal` form used by the three density clauses of alternative (ii). -/
theorem pow_le_mul_ofReal_totalLoss {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) :
    (Q : ENNReal) ^ (M + 1)
      ≤ ((Q ^ 2 : NNReal) : ENNReal) * totalLoss (Q ^ 2) K c δ := by
  have hone : (1 : ENNReal) ≤ ((Q ^ 2 : NNReal) : ENNReal) := by
    exact_mod_cast (one_le_pow₀ hQ : (1 : NNReal) ≤ Q ^ 2)
  exact (pow_le_pow_right₀ (by exact_mod_cast hQ : (1 : ENNReal) ≤ (Q : ENNReal))
      (by omega : M + 1 ≤ M + 2)).trans
    ((pow_le_ofReal_totalLoss hQ hδ hδ1 hM K c).trans (le_mul_of_one_le_left' hone))

/-- **The cardinality clause of alternative (ii), read in `[0,∞]`.**  The grid form of alternative
(ii) states the proportion between the level-`a` nodes and the good ones on the real line, whereas
every consumer of the amended dichotomy counts in `ℝ≥0∞`; the transfer is the only conversion
involved, so it is isolated here rather than repeated at each use. -/
theorem natCast_le_mul_totalLoss_mul_natCast {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) {m n : ℕ}
    (h : (m : ℝ) ≤ ((Q ^ (M + 1) : NNReal) : ℝ) * (n : ℝ)) :
    (m : ENNReal) ≤ ((Q ^ 2 : NNReal) : ENNReal) * totalLoss (Q ^ 2) K c δ * (n : ENNReal) := by
  refine natCast_le_mul_natCast_of_ofReal_le ?_ h
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
  exact pow_le_mul_ofReal_totalLoss hQ hδ hδ1 hM K c

/-- One `Q^{M+1}` on the greater side of a lower bound, in the `[0,∞]` form the third clause of
alternative (ii) uses. -/
theorem pow_mul_le_mul_ofReal_totalLoss_mul {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) (x : ENNReal) :
    (Q : ENNReal) ^ (M + 1) * x
      ≤ ((Q ^ 2 : NNReal) : ENNReal) * totalLoss (Q ^ 2) K c δ * x := by
  exact mul_le_mul_left (pow_le_mul_ofReal_totalLoss hQ hδ hδ1 hM K c) x

/-- **The whole error of alternative (i), absorbed.**  The displayed loss of the amended dichotomy
is `B · totalLoss B K c δ · δ^{-5ε}`; what the grid form of alternative (i) delivers is
`Q^{Mgrid+2} · δ^{-4ε}`.  The power is paid by `gridLoss` at base `B = Q²` and the spare `ε` of the
budget is not needed for it. -/
theorem katzTao_bound_le_totalLoss_bound {Q : NNReal} (hQ : 1 ≤ Q) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {M : ℕ} (hM : M ≤ ssfGridLen δ) (K c : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    (Q : ENNReal) ^ (M + 2) * ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε)))
      ≤ ((Q ^ 2 : NNReal) : ENNReal) * totalLoss (Q ^ 2) K c δ
          * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) := by
  have hdR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hone : (1 : ENNReal) ≤ ((Q ^ 2 : NNReal) : ENNReal) := by
    exact_mod_cast (one_le_pow₀ hQ)
  exact mul_le_mul'
    ((pow_le_ofReal_totalLoss hQ hδ hδ1 hM K c).trans (le_mul_of_one_le_left' hone))
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdR
      (by exact_mod_cast hδ1) (by linarith)))

/-! ### Alternative (i) on a grid of independent length -/

/-- **A short block of the `M`-grid has length at most `ε M + 1`.**  The unfolding of
`Kakeya.MultiScaleFac.IsLongBlock` that the node-chain telescope consumes. -/
theorem sub_le_succ_of_not_isLongBlock {M : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a b : ℕ}
    (h : ¬ IsLongBlock M ε a b) : (b : ℝ) - (a : ℝ) ≤ ε * (M : ℝ) + 1 := by
  have hble : b ≤ ⌈ε * (M : ℝ)⌉₊ + a := Nat.not_lt.mp (by simpa [IsLongBlock] using h)
  have hcast : (b : ℝ) ≤ (⌈ε * (M : ℝ)⌉₊ : ℝ) + (a : ℝ) := by exact_mod_cast hble
  linarith [Nat.ceil_lt_add_one (mul_nonneg hε (Nat.cast_nonneg M))]

/-- **The exponent budget of alternative (i) on a grid longer than the step bound.**

The short-gap factor of `Kakeya.MultiScaleFac.exists_maxDensity_parent_le_of_index` at grid length
`M` is `δ^{-(ζ+n-1)(ε+1/M)}`, and with `n = 3` the whole exponent is at most `4ε` exactly as on the
diagonal `M = N`: the only place the grid length enters is `1/M ≤ 1/N = ε²`. -/
theorem shortGap_exponent_le {N M : ℕ} (hN : 4096 ≤ N) (hNM : N ≤ M) {ε ζ : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) (hζ0 : 0 ≤ ζ) (hζε : ζ ≤ ε) :
    ζ + (ζ + 2) * (ε + 1 / (M : ℝ)) ≤ 4 * ε := by
  have hN0R : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hepspos : 0 < ε := by rw [hε]; exact one_div_pos.mpr (Real.sqrt_pos.mpr hN0R)
  have hsqrt64 : (64 : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.le_sqrt_of_sq_le (by rw [show (64 : ℝ) ^ 2 = 4096 by norm_num]; exact_mod_cast hN)
  have hepsle : ε ≤ 1 / 64 := by
    rw [hε]; exact one_div_le_one_div_of_le (by norm_num) hsqrt64
  have hu0 : (0 : ℝ) ≤ 1 / (M : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg M)
  have hu : 1 / (M : ℝ) ≤ ε * ε := by
    rw [hε, div_mul_div_comm, Real.mul_self_sqrt hN0R.le, one_mul]
    exact one_div_le_one_div_of_le hN0R (by exact_mod_cast hNM)
  have p1 : ζ * ε ≤ ε * ε := mul_le_mul hζε le_rfl hepspos.le (hζ0.trans hζε)
  have p2 : ζ * (1 / (M : ℝ)) ≤ ε * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_right hζε hu0
  have p3 : ε * (1 / (M : ℝ)) ≤ ε * (ε * ε) := mul_le_mul_of_nonneg_left hu hepspos.le
  have q1 : ε * ε ≤ ε / 64 := by
    have h := mul_le_mul_of_nonneg_right hepsle hepspos.le
    linarith only [h]
  have q2 : ε * (ε * ε) ≤ ε / 64 := by
    have h := mul_le_mul_of_nonneg_right hepsle (mul_nonneg hepspos.le hepspos.le)
    linarith only [h, q1, hepspos]
  linarith only [p1, p2, p3, q1, q2, hu, hζε, hepspos]

/-- **The anchor factor at a grid index is at most the one at the bottom of the grid.**  A grid
scale is `δ^{k/M}` with `k/M ≤ 1`, hence at least `δ`, and the exponent `-ζ` is nonpositive. -/
theorem ofReal_gridScale_rpow_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M k : ℕ} (hk : k ≤ M)
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ENNReal.ofReal ((gridScale δ M k : ℝ) ^ (-ζ)) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have hdR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hq1 : (k : ℝ) / (M : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos M with rfl | hM1
    · simp
    · rw [div_le_one (by exact_mod_cast hM1)]; exact_mod_cast hk
  rw [show (gridScale δ M k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) from
    by rw [gridScale, NNReal.coe_rpow], ← Real.rpow_mul hdR.le]
  exact Real.rpow_le_rpow_of_exponent_ge hdR (by exact_mod_cast hδ1)
    (by linarith [mul_nonneg (sub_nonneg.mpr hq1) hζ])

/-- **Collapsing the two `δ`-powers of alternative (i).**  The anchor factor at a grid index is at
most the one at the bottom of the grid, and the two powers of `δ` then add. -/
theorem mul_ofReal_rpow_mul_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M k : ℕ} (hk : k ≤ M)
    {ζ θ α : ℝ} (hζ : 0 ≤ ζ) (hsum : ζ + θ ≤ α) (X : ENNReal) :
    X * ENNReal.ofReal ((δ : ℝ) ^ (-θ)) * ENNReal.ofReal ((gridScale δ M k : ℝ) ^ (-ζ))
      ≤ X * ENNReal.ofReal ((δ : ℝ) ^ (-α)) := by
  have hdR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hd1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  calc X * ENNReal.ofReal ((δ : ℝ) ^ (-θ))
          * ENNReal.ofReal ((gridScale δ M k : ℝ) ^ (-ζ))
      ≤ X * ENNReal.ofReal ((δ : ℝ) ^ (-θ))
          * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
        mul_le_mul_right (ofReal_gridScale_rpow_le hδ hδ1 hk hζ)
          (X * ENNReal.ofReal ((δ : ℝ) ^ (-θ)))
    _ = X * ENNReal.ofReal ((δ : ℝ) ^ (-θ + -ζ)) := by
      rw [mul_assoc, Real.rpow_add hdR, ENNReal.ofReal_mul (Real.rpow_nonneg hdR.le _)]
    _ ≤ X * ENNReal.ofReal ((δ : ℝ) ^ (-α)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hdR hd1R (by linarith))) X

/-- **Alternative (i) of GWZ Lemma 7.7(B), over `GridUniformCore`** (route (a)).  The `GridUniform` original below is the case `Cw := uniformTubeSetCuOf Cv`,
`𝒱 := 𝒢.toUniformTubeSet`, `hcov := rfl`.

`Tube.UniformTubeSet.IsKatzTaoAtEveryScale` (`Kakeya/Sticky.lean:115`) is a statement about
`𝒰.cover.indexSet` and `𝒰.cover.tube` only, so the conclusion transports along `hcov` alone.

**The constant, named.**  `Q = Cbig * Cb`, with `Cbig` the constant of
`exists_maxDensity_parent_le_of_index_core` at `Cw` — linear in `Cw` above that form's engine
constant, and taking no power of it.  At the `Cu²` reading (`Cv := Cu ^ 2`, `Cw := Cu`) the
squaring is confined to `Cv`, which does not enter `Q` here at all.  The displayed
`δ`-power `δ^{-4ε}` is untouched.

**A1-a.**  `GridUniformCore` enters this alternative and `BlockKatzTaoOn` only; no (F)-branch
interface statement moves. -/
theorem isKatzTaoAtEveryScale_of_cutsKT_grid_core (hn : Module.finrank ℝ E = 3)
    (Cv Cw : NNReal) (hCv : 1 ≤ Cv) (hCw : 1 ≤ Cw) (Cb : NNReal) (hCb : 1 ≤ Cb) :
    ∃ Q : NNReal, 1 ≤ Q ∧ Cb ≤ Q ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒞 : GridUniformCore t T Mgrid Cv) (𝒱 : Tube.UniformTubeSet t T Mgrid Cw),
        𝒱.cover = 𝒞.cover →
      ∀ (ζ : ℝ), 0 ≤ ζ → ζ ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒞.uniformAt Cb ζ a b ∧ ¬ IsLongBlock Mgrid ε a b) →
      𝒱.IsKatzTaoAtEveryScale
        ((Q : ENNReal) ^ (Mgrid + 2) * ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε)))) := by
  classical
  obtain ⟨Cbig, hCbig1, hidx⟩ :=
    exists_maxDensity_parent_le_of_index_core.{u, _} (E := E) Cv Cw hCv hCw
  refine ⟨Cbig * Cb, one_le_mul hCbig1 hCb, le_mul_of_one_le_left' hCbig1, ?_⟩
  intro N hN ε hε Mgrid hNM iota δ hd0 hd1 hdM t T hNonempty hBall 𝒞 𝒱 hcov ζ hzeta0
    hzetaeps S hS0 hMem
    hBlocks k hk
  have hepsnn : (0 : ℝ) ≤ ε := by rw [hε]; positivity
  have hmain := hidx Mgrid (by omega) hd0 hd1 hdM t T hNonempty hBall 𝒞 𝒱 hcov
    Cb ε ζ hCb hzeta0 hepsnn S
    hS0 hMem
    (fun a hSa b hSb hlt1 hAdj => ⟨(hBlocks a hSa b hSb hlt1 hAdj).1,
      sub_le_succ_of_not_isLongBlock hepsnn (hBlocks a hSa b hSb hlt1 hAdj).2⟩) k hk
  simp only [hcov]
  refine le_trans hmain ?_
  rw [show ((Module.finrank ℝ E - 1 : ℕ) : ℝ) = 2 by rw [hn]; norm_num]
  exact mul_ofReal_rpow_mul_le hd0 hd1 hk hzeta0
    (shortGap_exponent_le hN hNM hε hzeta0 hzetaeps) _

/-- **Alternative (i) of GWZ Lemma 7.7(B), with the grid length separated from the step bound.**
`Kakeya.StickyKakeya.isKatzTaoAtEveryScale_of_cutsKT` with the single parameter `N` split into a
grid length `Mgrid` — governing the cover system, the cut set and the long-block test — and a step
bound `N`, governing only `ε = 1/√N`.  The accumulated constant is displayed as `Q^{Mgrid+2}`.

**The statement is unchanged**; the proof is one line through
`isKatzTaoAtEveryScale_of_cutsKT_grid_core` at `Cw := uniformTubeSetCuOf Cv`. -/
theorem isKatzTaoAtEveryScale_of_cutsKT_grid (hn : Module.finrank ℝ E = 3) (Cv : NNReal)
    (hCv : 1 ≤ Cv) (Cb : NNReal) (hCb : 1 ≤ Cb) :
    ∃ Q : NNReal, 1 ≤ Q ∧ Cb ≤ Q ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒢 : GridUniform t T Mgrid Cv) (ζ : ℝ), 0 ≤ ζ → ζ ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒢.uniformAt Cb ζ a b ∧ ¬ IsLongBlock Mgrid ε a b) →
      (𝒢.toUniformTubeSet).IsKatzTaoAtEveryScale
        ((Q : ENNReal) ^ (Mgrid + 2) * ENNReal.ofReal ((δ : ℝ) ^ (-(4 * ε)))) := by
  obtain ⟨Q, hQ1, hQb, h⟩ := isKatzTaoAtEveryScale_of_cutsKT_grid_core.{u, _} (E := E) hn Cv
    (uniformTubeSetCuOf (E := E) Cv) hCv (le_trans hCv (le_max_left _ _)) Cb hCb
  refine ⟨Q, hQ1, hQb, ?_⟩
  intro N hN ε hε Mgrid hNM iota δ hd0 hd1 hdM t T hNonempty hBall 𝒢 ζ hzeta0 hzetaeps S hS0
    hMem hBlocks
  exact h N hN hε Mgrid hNM hd0 hd1 hdM t T hNonempty hBall 𝒢.toGridUniformCore
    𝒢.toUniformTubeSet rfl ζ hzeta0 hzetaeps S hS0 hMem hBlocks

/-! ### Alternative (ii) on a grid of independent length -/

omit [Nontrivial E] in
open scoped Classical in
/-- **The lower bound of alternative (ii) at one good node, over `GridUniformCore`**
(route (a)).  A pure binder swap: `goodNodes`, `nodesIn` and the class
extraction `exists_good_mem_coverClass_of_mem_goodNodes` all read the *cover*, so `𝒱` may be any
uniform tube set sharing `𝒞`'s cover.  `hCw : 1 ≤ Cw` replaces the derived
`1 ≤ uniformTubeSetCuOf Cv`; **no constant appears in the conclusion**, so there is no `Cu²`
bookkeeping at this declaration. -/
theorem le_maxDensity_nodesIn_of_mem_goodNodes_core {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {M : ℕ} (hM : 0 < M) {t : Finset ι} {T : ι → Tube δ E} {Cv : NNReal} (_hCv : 1 ≤ Cv)
    (𝒞 : GridUniformCore t T M Cv) {Cw : NNReal}
    {𝒱 : Tube.UniformTubeSet t T M Cw} (hCw : 1 ≤ Cw) (hcov : 𝒱.cover = 𝒞.cover)
    (hs : t.Nonempty) {Cb : NNReal} (hCb : 1 ≤ Cb)
    {ε ζ' : ℝ} {a b c : ℕ} (haM : a ≤ M) (_hcM : c ≤ M)
    (hadm : a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c)
    (hadm' : c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b)
    {j : ι} (hjF : j ∈ goodNodes 𝒱 a
      (failingNodesKT t 𝒞.uniformAt Cb ε ζ' a b)) :
    ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ')
      ≤ Kakeya.maxDensity
          (𝒱.nodesIn c
            (((𝒞.cover.tube a j).rescale (8 * gridScale δ M a)).toConvexSpaceBody))
          (fun j' => (𝒞.cover.tube c j').toConvexSpaceBody) := by
  classical
  have hCu1 : (1 : NNReal) ≤ Cw := hCw
  obtain ⟨i0, hi0cls, hi0G⟩ :=
    exists_good_mem_coverClass_of_mem_goodNodes hCu1 hs 𝒱 haM hjF
  have hnotQall : ¬ (∀ hc : c ≤ M, ConvexSpaceBody.IsKatzTao
      (gapNodeIndexAtScale (𝒞.uniformAt c hc) i0 (5 * gridScale δ M a))
      (fun j' => ((𝒞.uniformAt c hc).parentTube j').toConvexSpaceBody)
      ((Cb : ENNReal) * ENNReal.ofReal
        (((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ'))) := by
    have hnotblk : ¬ BlockKatzTaoAt 𝒞.uniformAt Cb ζ' a c i0 := fun hblk =>
      (mem_failingNodesKT.mp hi0G).2 ⟨c, hadm, hadm', hblk⟩
    simpa [BlockKatzTaoAt] using hnotblk
  push Not at hnotQall
  obtain ⟨hc', hnotQ⟩ := hnotQall
  rw [ConvexSpaceBody.IsKatzTao_def] at hnotQ
  rw [coverClass, Finset.mem_filter] at hi0cls
  simp only [hcov] at hi0cls
  have hile : (T i0).toConvexSpaceBody ≤ (𝒞.cover.tube a j).toConvexSpaceBody := by
    have h := 𝒞.cover.le_tube_assign a haM i0 hi0cls.1
    rwa [show 𝒞.cover.assign a i0 = j from hi0cls.2] at h
  exact le_of_lt ((le_mul_of_one_le_left' (by exact_mod_cast hCb)).trans_lt
    ((lt_of_not_ge hnotQ).trans_le
      (maxDensity_gapNodeIndex_le_maxDensity_nodesIn_core hδ hδ1 hM 𝒞 hcov haM hc' hile)))

omit [Nontrivial E] in
open scoped Classical in
/-- **The lower bound of alternative (ii), at one good node and one index of the window.**  A node
`j` counted as good carries a leaf `i₀` of its class failing the per-anchor split test
(`Kakeya.MultiScaleFac.NodeSplitTestKT`), so at every index `c` of the stopping window the maximal
density at the `5σ_a`-thickening of `i₀` exceeds `(σ_a/σ_c)^{ζ'}`, and that thickening sits inside
the `8σ_a`-dilate of the node.  No constant survives on the right.

**The statement is unchanged**; the proof is one line through
`le_maxDensity_nodesIn_of_mem_goodNodes_core`. -/
theorem le_maxDensity_nodesIn_of_mem_goodNodes {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M : ℕ}
    (hM : 0 < M) {t : Finset ι} {T : ι → Tube δ E} {Cv : NNReal} (hCv : 1 ≤ Cv)
    (𝒢 : GridUniform t T M Cv) (hs : t.Nonempty) {Cb : NNReal} (hCb : 1 ≤ Cb)
    {ε ζ' : ℝ} {a b c : ℕ} (haM : a ≤ M) (_hcM : c ≤ M)
    (hadm : a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c)
    (hadm' : c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b)
    {j : ι} (hjF : j ∈ goodNodes 𝒢.toUniformTubeSet a
      (failingNodesKT t 𝒢.uniformAt Cb ε ζ' a b)) :
    ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ')
      ≤ Kakeya.maxDensity
          (𝒢.toUniformTubeSet.nodesIn c
            (((𝒢.cover.tube a j).rescale (8 * gridScale δ M a)).toConvexSpaceBody))
          (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody) := by
  exact le_maxDensity_nodesIn_of_mem_goodNodes_core hδ hδ1 hM hCv 𝒢.toGridUniformCore
    (𝒱 := 𝒢.toUniformTubeSet) (le_trans hCv (le_max_left _ _)) rfl hs hCb haM _hcM hadm hadm'
    hjF

/-- **Alternative (ii) of GWZ Lemma 7.7(B), over `GridUniformCore`** (route (a)).  The `GridUniform` original below is the case `Cw := uniformTubeSetCuOf Cv`,
`𝒱 := 𝒢.toUniformTubeSet`, `hcov := rfl`.

Everything the statement says factors through the *cover*: `nodesIn` (`Kakeya/Uniform.lean:229`),
`goodNodes` (`MultiScaleFac/Bridge.lean:621`) and `Tube.UniformTubeSet.nodesUnder` are all filters
of `𝒱.cover.indexSet`, so pinning `𝒱.cover = 𝒞.cover` is the whole content of the swap and no
proof step changes.

**The constant, named.**  `Q = Cbig * (1 + Cb) + 4 * Cw ^ 2 + Cb`, with `Cbig` the constant of
`exists_maxDensity_parent_le_of_cutIndex_core` at `Cw`.  The `Cw ^ 2` is *not* the `Cu²` —
it is the node-proportion constant of `card_parent_le_mul_card_goodNodes`, which was already
`4 * Cu ^ 2` in the original.  Feeding the `Cu²` core (`Cv := Cu ^ 2`, `Cw := Cu`) therefore leaves
`Q` reading `Cbig * (1 + Cb) + 4 * Cu ^ 2 + Cb`: **`Cu` is squared once here and once in `Cv`, and
the two do not multiply.**  `Q` is `δ`-free.

**A1-a.**  `GridUniformCore` enters only this alternative, `BlockKatzTaoOn` and `passingNodesKT`.
No `FloorHypothesisAt` / `FloorDataAtTrichotomy` / `RefinedFloorHypothesis` / `hfac` /
`IsKatzTaoDividingWindow(Levels)` field is touched. -/
theorem alternative_two_of_terminal_blockKT_grid_core (hn : Module.finrank ℝ E = 3)
    (Cv Cw : NNReal) (hCv : 1 ≤ Cv) (hCw : 1 ≤ Cw) (Cb : NNReal) (hCb : 1 ≤ Cb) :
    ∃ Q : NNReal, 1 ≤ Q ∧ Cb ≤ Q ∧
      ∀ (Mgrid : ℕ), 0 < Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒞 : GridUniformCore t T Mgrid Cv) (𝒱 : Tube.UniformTubeSet t T Mgrid Cw),
        𝒱.cover = 𝒞.cover →
      ∀ (ε ζ ζ' : ℝ), 0 ≤ ζ → 0 ≤ ζ' →
      ∀ S : Finset ℕ, 0 ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒞.uniformAt Cb ζ a b) →
      ∀ a b : ℕ, a ∈ S → b ∈ S → a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) → b ≤ Mgrid →
      ¬ (t.card ≤ 2 * (passingNodesKT t 𝒞.uniformAt Cb ε ζ' a b).card) →
      ∃ F ⊆ 𝒞.cover.indexSet a,
        (((𝒞.cover.indexSet a).card : ℝ) ≤ ((Q ^ (Mgrid + 1) : NNReal) : ℝ) * (F.card : ℝ)) ∧
        Kakeya.maxDensity (𝒞.cover.indexSet a)
            (fun j => (𝒞.cover.tube a j).toConvexSpaceBody)
          ≤ (Q : ENNReal) ^ (Mgrid + 1)
              * ENNReal.ofReal ((gridScale δ Mgrid a : ℝ) ^ (-ζ)) ∧
        (∀ j ∈ 𝒞.cover.indexSet a,
          Kakeya.maxDensity (𝒱.nodesUnder b a j)
              (fun j' => (𝒞.cover.tube b j').toConvexSpaceBody)
            ≤ (Q : ENNReal) ^ (Mgrid + 1) * ENNReal.ofReal
                (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid b : ℝ)) ^ ζ)) ∧
        (∀ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
          ∀ j ∈ F,
            ENNReal.ofReal (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid c : ℝ)) ^ ζ')
              ≤ (Q : ENNReal) ^ (Mgrid + 1) *
                  Kakeya.maxDensity
                    (𝒱.nodesIn c
                      (((𝒞.cover.tube a j).rescale
                          (8 * gridScale δ Mgrid a)).toConvexSpaceBody))
                    (fun j' => (𝒞.cover.tube c j').toConvexSpaceBody)) := by
  classical
  have _ := hn
  obtain ⟨Cbig, hCbig1, hcut⟩ :=
    exists_maxDensity_parent_le_of_cutIndex_core.{u, _} (E := E) Cv Cw hCv hCw
  let Q : NNReal := Cbig * (1 + Cb) + 4 * Cw ^ 2 + Cb
  have hCbig_le : (Cbig * (1 + Cb) : NNReal) ≤ Q := by
    dsimp only [Q]; exact le_self_add.trans le_self_add
  have hCu_leQ : 4 * Cw ^ 2 ≤ Q := by
    dsimp only [Q]; exact le_add_self.trans le_self_add
  have hQb : Cb ≤ Q := by
    dsimp only [Q]; exact le_add_self
  have hQ1 : (1 : NNReal) ≤ Q :=
    (one_le_mul hCbig1 (self_le_add_right (a := (1 : NNReal)) (b := Cb))).trans hCbig_le
  refine ⟨Q, hQ1, hQb, ?_⟩
  intro Mgrid hMpos ι δ hδ hδ1 hδ0 t T hs hball 𝒞 𝒱 hcov ε ζ ζ' hζ hζ' S h0 hblocks a b haS
    hbS hab hadj hbM hnotpass
  have haM : a ≤ Mgrid := le_trans (le_of_lt hab) hbM
  have hQp : Q ≤ Q ^ (Mgrid + 1) := le_self_pow hQ1 (by omega : Mgrid + 1 ≠ 0)
  have hCu1 : (1 : NNReal) ≤ Cw := hCw
  have h1powE : (1 : ENNReal) ≤ (Q : ENNReal) ^ (Mgrid + 1) := by
    rw [← ENNReal.coe_pow]
    exact_mod_cast one_le_pow₀ hQ1
  have hFleaf : t.card ≤ 2 * (failingNodesKT t 𝒞.uniformAt Cb ε ζ' a b).card :=
    (card_le_two_mul_card_passingNodesKT_or_failingNodesKT t 𝒞.uniformAt Cb ε ζ'
      a b).resolve_left hnotpass
  let G0 : Finset ι := failingNodesKT t 𝒞.uniformAt Cb ε ζ' a b
  let F : Finset ι := goodNodes 𝒱 a G0
  have hGsub : G0 ⊆ t := failingNodesKT_subset t 𝒞.uniformAt Cb ε ζ' a b
  have hFsub : F ⊆ 𝒞.cover.indexSet a := fun j hj => by
    rw [← hcov]; exact (Finset.mem_filter.mp hj).1
  refine ⟨F, hFsub, ?_, ?_, ?_, ?_⟩
  · have hpropNN : ((𝒞.cover.indexSet a).card : NNReal) ≤
        4 * Cw ^ 2 * (F.card : NNReal) := by
      have h := card_parent_le_mul_card_goodNodes hCu1 𝒱 haM hGsub hFleaf
      dsimp [F, G0]
      simpa [hcov] using h
    calc
      ((𝒞.cover.indexSet a).card : ℝ)
          ≤ ((4 * Cw ^ 2 : NNReal) : ℝ) * (F.card : ℝ) := by
              exact_mod_cast hpropNN
      _ ≤ ((Q ^ (Mgrid + 1) : NNReal) : ℝ) * (F.card : ℝ) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hCu_leQ.trans hQp)
                (Nat.cast_nonneg _)
  · refine le_trans (hcut Mgrid hMpos hδ hδ1 hδ0 t T hs hball 𝒞 𝒱 hcov Cb ζ S h0 hblocks a haS haM)
      (mul_le_mul' ?_ le_rfl)
    rw [← ENNReal.coe_pow, ← ENNReal.coe_pow]
    exact_mod_cast pow_le_pow_left₀ zero_le hCbig_le (Mgrid + 1)
  · intro j hjp
    have hne := coverClass_nonempty_of_mem_parent 𝒱 haM hs
      (by simpa [hcov] using hjp)
    have hspec : hne.choose ∈ t ∧ 𝒞.cover.assign a hne.choose = j := by
      simpa [coverClass, hcov] using hne.choose_spec
    have hile : (T hne.choose).toConvexSpaceBody ≤ (𝒞.cover.tube a j).toConvexSpaceBody := by
      have hleTube := 𝒞.cover.le_tube_assign a haM _ hspec.1
      rwa [hspec.2] at hleTube
    refine le_trans (maxDensity_nodesUnder_le_of_blockKatzTaoAt_core hδ hδ1 𝒞 hcov
      haM hbM hab.le hjp hile
      (hblocks a haS b hbS hab hadj hne.choose hspec.1)) (mul_le_mul' ?_ le_rfl)
    rw [← ENNReal.coe_pow]
    exact_mod_cast hQb.trans hQp
  · intro c hc1 hc2 j hjF
    have hcM : c ≤ Mgrid := by omega
    have hcore := le_maxDensity_nodesIn_of_mem_goodNodes_core hδ hδ1 hMpos hCv 𝒞 hCw
      hcov hs hCb
      haM hcM hc1 hc2 (by simpa [F, G0] using hjF)
    exact le_trans hcore (le_mul_of_one_le_left' h1powE)

/-- **Alternative (ii) of GWZ Lemma 7.7(B), with the grid length separated from the step bound.**
The grid length `Mgrid` is a parameter of its own, the accumulated constant is displayed as
`Q^{Mgrid+1}` with `Q` quantified before `Mgrid`, and the interior index `c` of the third bullet is
restricted by the *index* window `a + ⌈ε(b-a)⌉ ≤ c`, `c + ⌈ε(b-a)⌉ ≤ b` rather than by grid scales.
Neither `N` nor a long-block hypothesis survives.

**The statement is unchanged**; the proof is one line through
`alternative_two_of_terminal_blockKT_grid_core` at `Cw := uniformTubeSetCuOf Cv`. -/
theorem alternative_two_of_terminal_blockKT_grid (hn : Module.finrank ℝ E = 3) (Cv : NNReal)
    (hCv : 1 ≤ Cv) (Cb : NNReal) (hCb : 1 ≤ Cb) :
    ∃ Q : NNReal, 1 ≤ Q ∧ Cb ≤ Q ∧
      ∀ (Mgrid : ℕ), 0 < Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒢 : GridUniform t T Mgrid Cv) (ε ζ ζ' : ℝ), 0 ≤ ζ → 0 ≤ ζ' →
      ∀ S : Finset ℕ, 0 ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒢.uniformAt Cb ζ a b) →
      ∀ a b : ℕ, a ∈ S → b ∈ S → a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) → b ≤ Mgrid →
      ¬ (t.card ≤ 2 * (passingNodesKT t 𝒢.uniformAt Cb ε ζ' a b).card) →
      ∃ F ⊆ 𝒢.cover.indexSet a,
        (((𝒢.cover.indexSet a).card : ℝ) ≤ ((Q ^ (Mgrid + 1) : NNReal) : ℝ) * (F.card : ℝ)) ∧
        Kakeya.maxDensity (𝒢.cover.indexSet a)
            (fun j => (𝒢.cover.tube a j).toConvexSpaceBody)
          ≤ (Q : ENNReal) ^ (Mgrid + 1)
              * ENNReal.ofReal ((gridScale δ Mgrid a : ℝ) ^ (-ζ)) ∧
        (∀ j ∈ 𝒢.cover.indexSet a,
          Kakeya.maxDensity (𝒢.toUniformTubeSet.nodesUnder b a j)
              (fun j' => (𝒢.cover.tube b j').toConvexSpaceBody)
            ≤ (Q : ENNReal) ^ (Mgrid + 1) * ENNReal.ofReal
                (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid b : ℝ)) ^ ζ)) ∧
        (∀ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
          ∀ j ∈ F,
            ENNReal.ofReal (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid c : ℝ)) ^ ζ')
              ≤ (Q : ENNReal) ^ (Mgrid + 1) *
                  Kakeya.maxDensity
                    (𝒢.toUniformTubeSet.nodesIn c
                      (((𝒢.cover.tube a j).rescale
                          (8 * gridScale δ Mgrid a)).toConvexSpaceBody))
                    (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨Q, hQ1, hQb, h⟩ := alternative_two_of_terminal_blockKT_grid_core.{u, _} (E := E) hn Cv
    (uniformTubeSetCuOf (E := E) Cv) hCv (le_trans hCv (le_max_left _ _)) Cb hCb
  refine ⟨Q, hQ1, hQb, ?_⟩
  intro Mgrid hMpos ι δ hδ hδ1 hδ0 t T hs hball 𝒢 ε ζ ζ' hζ hζ' S h0 hblocks a b haS hbS hab
    hadj hbM hnotpass
  exact h Mgrid hMpos hδ hδ1 hδ0 t T hs hball 𝒢.toGridUniformCore 𝒢.toUniformTubeSet rfl
    ε ζ ζ' hζ hζ' S h0 hblocks a b haS hbS hab hadj hbM hnotpass

end MultiScaleFac
end Kakeya

end
