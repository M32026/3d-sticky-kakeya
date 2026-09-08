/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.Tube.Rescale
public import Kakeya.PartialEstimates

/-!
# Main Lemma 1, Case (ii): the fine and coarse factors, and the reduction

This file formalizes the three subsections of Section 8 of the adapted blueprint that treat
the second alternative of `dividingScalesLemmaA`, the case complementary to the sticky case
of `Kakeya/DimensionThree/MainLemma1/Setup.lean`:

* `GWZAdapted/section8_finescale.tex` — the **output scale of the fine normalization**:
  `Kakeya.ml1Boot.fineScale`, `Kakeya.ml1Boot.fineScale_bounds`,
  `Kakeya.ml1Boot.fineScale_bracket_le`;
* `GWZAdapted/section8_cases.tex` — the **fine-scale factor** `μ(𝕋[T_τ], Y)`:
  `Kakeya.ml1Boot.fineNormalize.C`, `Kakeya.ml1Boot.fineFactor.C`,
  `Kakeya.ml1Boot.exists_fineNormalization`,
  `Kakeya.ml1Boot.fine_genKF`, `Kakeya.ml1Boot.multiplicity_le_fine`;
* `GWZAdapted/section8_coarse.tex` — the **coarse-scale factor** `μ(𝕋_θ, Y_{𝕋_θ})`:
  `Kakeya.ml1Boot.IsParentFamily.finpartition`,
  `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le`,
  `Kakeya.ml1Boot.multiplicity_le_coarse`;
* `GWZAdapted/section8_reduction.tex` — the **reduction to the middle factor**:
  `Kakeya.ml1Boot.tripleCollapse`, `Kakeya.ml1Boot.exponentShift`,
  `Kakeya.ml1Boot.lossNumerics`, `Kakeya.ml1Boot.multiplicity_le_of_middle`,
  `Kakeya.ml1Boot.fibre_product_card_le`.

## Divergence from the informal statement: bare exponents

The blueprint states the fine and coarse factor estimates in terms of the parameter package
`Kakeya.ml1Boot.params`: the loss exponent is `ε♯ = η₀ = p.η 0`, the Frostman exponent is
`η_{j-1} = p.η (j - 1)`, the fullness threshold is `η(γ) = p.ηGamma γ`, and `η = p.η 0`
again for the coarse family.  Here those exponents are *bare real numbers*: `e` for the loss
exponent `η₀`, `a` for `η_{j-1}`, `n₀` for `η`, and the fullness threshold is the exponent
`ηs` produced by the existential of `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`.

This is the same device the blueprint itself uses for `lem:ml1bootCaseNonSticky` ("we state
the assembly for bare real numbers so that it does not depend on the data produced by
`lem:ml1bootFactorTwoScales`"), extended to the two factor estimates.  The gain is that none
of these statements mentions `Kakeya.ml1Boot.params`, so none of them has to carry the
specification hypotheses of `Kakeya.ml1Boot.params_spec` and
`Kakeya.ml1Boot.etaGamma_spec`.  A consumer instantiates
`e := p.η 0`, `a := p.η (j - 1)`, `n₀ := p.η 0`, and obtains the fullness hypothesis at the
threshold `ηs` from the blueprint's `λ ≥ δ ^ η(γ)` together with
`Kakeya.ml1Boot.etaGamma_spec`, which gives `p.ηGamma γ ≤ ηKF γ ≤ ηs` and hence
`δ ^ ηs ≤ δ ^ p.ηGamma γ`.

Correspondingly the fullness threshold is *existentially* quantified in
`Kakeya.ml1Boot.multiplicity_le_fine` and `Kakeya.ml1Boot.multiplicity_le_coarse`, exactly as
`η` is in `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`; the assembly of Case (ii)
takes the minimum of the two thresholds.

## Powers of the tube scales

Throughout, `δ` is the auxiliary small parameter and `τ`, `θ` are tube scales with
`δ ≤ τ ≤ θ ≤ 1`.  The ambient dimension is `3`, so the common volume of a `ρ`-tube enters as
`ρ ^ 2`; the exponent `2` is written literally rather than as `Module.finrank ℝ E - 1`, since
every statement here already carries `hdim : Module.finrank ℝ E = 3` or is dimension-free.

The total-volume bracket is always written cardinality-first, `(|s| * ρ ^ 2)`, matching
`Kakeya.FrostmanEstimate`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### Case (ii): the fine-scale factor -/

/-- **The output scale of the fine normalization** (blueprint `def:ml1bootFineScale`).

`fineScale δ τ = min (δ / τ) (1 / 4)`.  This is the scale of the tube family that
`Kakeya.ml1Boot.exists_fineNormalization` produces in `B₁`, in place of the bare ratio
`δ / τ`.

The truncation at `1 / 4` is forced, and is what makes that lemma true.  A `Kakeya.Tube` has
a core of length exactly `1`, so a `ρ`-tube has diameter `1 + 2 ρ` and is contained in no ball
of radius `1` once `ρ > 1/2` (`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt`); the
hypotheses `0 < δ ≤ τ ≤ 1` permit `δ = τ`, hence `δ / τ = 1`, and the earlier form of the
lemma — which asked for `δ / τ`-tubes in `B₁` — is refuted there by
`Kakeya.ml1Boot.not_exists_fineNormalization`.  Truncating the output scale removes the
obstruction without weakening anything in the regime that matters: `fineScale δ τ = δ / τ`
whenever `δ / τ ≤ 1/4`, so in that regime the statement is *unchanged*.

Nothing is lost in the regime `δ / τ > 1/4` either, because the two scales stay within a
bounded factor of each other, `(δ / τ) / 4 ≤ fineScale δ τ ≤ δ / τ` — the first and third
clauses of the conjunction `Kakeya.ml1Boot.fineScale_bounds` — so the fine-factor bracket
changes by at most a factor `16` (`Kakeya.ml1Boot.fineScale_bracket_le`).  That factor is paid
out of the *constant*: `Kakeya.ml1Boot.fineFactor.C = 16 * Kakeya.ml1Boot.fineNormalize.C C_N`,
and the difference is spent exactly once, in `Kakeya.ml1Boot.fine_genKF`.  It is **not**
absorbed into the subpolynomial loss `δ ^ (-ε♯)`; that route is unsound in this development,
for the reason recorded in blueprint `note:ml1bootFineScaleWhyConstant`.  So no hypothesis
bounding `δ / τ` is needed anywhere in Section 8; see the module docstring of
`Kakeya/DimensionThree/MainLemma1/Cases.lean` and blueprint
`note:ml1bootFineNormalizeScaleObstruction`. -/
noncomputable abbrev fineScale (δ τ : NNReal) : NNReal := min (δ / τ) (1 / 4)

/-- **The output scale is pinned to the ratio it truncates** (blueprint
`lem:ml1bootFineScaleBounds`).

For `0 < τ` and `δ ≤ τ`:

* `fineScale δ τ ≤ δ / τ` and `δ / τ ≤ 4 * fineScale δ τ`, i.e.
  `(δ/τ)/4 ≤ fineScale δ τ ≤ δ/τ`.  This is what makes the truncation invisible to the
  fine-factor estimate (`Kakeya.ml1Boot.fineScale_bracket_le`).
* `fineScale δ τ ≤ 1/4`, which is `1 ≤ 1` short of the hypothesis `ρ ≤ 1` that
  `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` puts on its tube scale, and is on its
  own why a `fineScale δ τ`-tube in `B₁` is not asking for the impossible: `1/4` is strictly
  below the threshold `1/2` of `Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt`.

The remaining clause `δ ≤ fineScale δ τ` needs `δ ≤ 1/4` and `τ ≤ 1` and is
`Kakeya.ml1Boot.le_fineScale`; it is kept separate because
`Kakeya.ml1Boot.fineScale_bracket_le` has neither hypothesis and would not be able to cite a
bundled form. -/
theorem fineScale_bounds {δ τ : NNReal} (hδτ : δ ≤ τ) (hτ : 0 < τ) :
    fineScale δ τ ≤ δ / τ ∧ fineScale δ τ ≤ 1 / 4 ∧ δ / τ ≤ 4 * fineScale δ τ := by
  constructor
  · exact min_le_left (δ / τ) (1 / 4 : NNReal)
  constructor
  · exact min_le_right (δ / τ) (1 / 4 : NNReal)
  · have hρ1 : δ / τ ≤ 1 := by
      exact_mod_cast (div_le_one_of_le₀
        (by exact_mod_cast hδτ : (δ : ℝ) ≤ (τ : ℝ))
        (by exact_mod_cast hτ.le : (0 : ℝ) ≤ (τ : ℝ)))
    rcases le_total (δ / τ) (1 / 4 : NNReal) with hle | hge
    · rw [fineScale, min_eq_left hle]
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
    · rw [fineScale, min_eq_right hge]
      calc
        δ / τ ≤ (1 : NNReal) := hρ1
        _ = 4 * (1 / 4 : NNReal) := by norm_num

/-- **The auxiliary parameter is below the output scale** (blueprint
`lem:ml1bootDeltaLeFineScale`), which with `fineScale δ τ ≤ 1/4 ≤ 1` is the pair of hypotheses
`δ ≤ ρ ≤ 1` that `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` puts on the tube scale
`ρ` it is applied at.

The hypothesis `δ ≤ 1/4` is harmless: every consumer quantifies `δ` through
`∀ᶠ δ in 𝓝[>] 0` (`Kakeya.ml1Boot.eventually_le_quarter`). -/
theorem le_fineScale {δ τ : NNReal} (hδ4 : δ ≤ 1 / 4) (hτ1 : τ ≤ 1) (hτ : 0 < τ) :
    δ ≤ fineScale δ τ := by
  exact le_min
    (by
      have hreal : (δ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hτ : (0 : ℝ) < (τ : ℝ))]
        have hτle1 : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
        have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
        calc
          (δ : ℝ) * (τ : ℝ) ≤ (δ : ℝ) * 1 := mul_le_mul_of_nonneg_left hτle1 hδ0
          _ = (δ : ℝ) := by ring
      exact_mod_cast hreal)
    hδ4

/-- **The truncation costs a factor `16` in the fine-factor bracket.**

The two occurrences of the tube scale in the conclusion of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` are `ρ ^ (-2γ)` and `(|s| ρ²) ^ (1-γ/2)`.
Reading them at `ρ = fineScale δ τ` instead of at `ρ = δ / τ` costs at most `4 ^ (2γ) ≤ 16` in
the first — by the last clause of `Kakeya.ml1Boot.fineScale_bounds` — and nothing at all in
the second, which only decreases, by its first clause.

The factor `16` is paid out of the *constant*, not out of the subpolynomial loss:
`Kakeya.ml1Boot.fineFactor.C = 16 * Kakeya.ml1Boot.fineNormalize.C C_N`, the normalization
lemma is stated at the smaller constant and `Kakeya.ml1Boot.fine_genKF` at the larger, and
this is the one step that spends the difference.  Paying it out of the loss instead — apply
the underlying estimate at `ε♯/2` and use `16 δ ^ (-ε♯/2) ≤ δ ^ (-ε♯)` — would change the
fullness threshold that `Kakeya.FrostmanEstimate.multiplicity_bound_auxScale` hands back, and
the calibration of that threshold against `Kakeya.ml1Boot.params` is fixed upstream at the
full exponent; see blueprint `note:ml1bootFineScaleWhyConstant`. -/
-- The first (negative-exponent) factor of the fine-factor bracket: reading `ρ ^ (-2γ)` at
-- `σ = fineScale δ τ` instead of at `ρ = δ / τ` costs `4 ^ (2γ) ≤ 16`, by the last clause
-- `δ / τ ≤ 4 * fineScale δ τ` of `fineScale_bounds`.
private lemma fineScale_rpow_neg_le {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ : 0 < τ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
      ≤ 16 * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ) := by
  let σ : ENNReal := (fineScale δ τ : NNReal)
  let ρ : ENNReal := (δ / τ : NNReal)
  have hρσ4 : ρ ≤ 4 * σ := by
    dsimp [ρ, σ]
    exact_mod_cast (fineScale_bounds hδτ hτ).2.2
  have hρ0 : (0 : NNReal) < δ / τ := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact ENNReal.coe_pos.mpr hρ0
  have hσpos : 0 < σ := by
    dsimp [σ]
    exact ENNReal.coe_pos.mpr (by
      exact lt_min hρ0 (by norm_num))
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  have hρtop : ρ ≠ ⊤ := ENNReal.coe_ne_top
  have hσtop : σ ≠ ⊤ := ENNReal.coe_ne_top
  have h2γ : 0 ≤ 2 * γ := by nlinarith [hγ0]
  have h4le16 : (4 : ENNReal) ^ (2 * γ) ≤ 16 := by
    calc
      (4 : ENNReal) ^ (2 * γ) ≤ (4 : ENNReal) ^ (2 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 4)
          (by nlinarith [hγ1])
      _ = 16 := by norm_num
  have hρ_le : ρ ^ (2 * γ) ≤ 16 * σ ^ (2 * γ) := by
    calc
      ρ ^ (2 * γ) ≤ (4 * σ) ^ (2 * γ) := by
        exact ENNReal.rpow_le_rpow hρσ4 h2γ
      _ = 4 ^ (2 * γ) * σ ^ (2 * γ) := by
        rw [ENNReal.mul_rpow_of_nonneg (4 : ENNReal) σ h2γ]
      _ ≤ 16 * σ ^ (2 * γ) := by
        exact mul_le_mul_left h4le16 (σ ^ (2 * γ))
  let a : ENNReal := σ ^ (2 * γ)
  let b : ENNReal := ρ ^ (2 * γ)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact ENNReal.rpow_pos hσpos hσtop
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have ha_top : a ≠ ⊤ := by
    dsimp [a]
    exact ENNReal.rpow_ne_top_of_ne_zero hσne hσtop
  have hb_pos : 0 < b := by
    dsimp [b]
    exact ENNReal.rpow_pos hρpos hρtop
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hb_top : b ≠ ⊤ := by
    dsimp [b]
    exact ENNReal.rpow_ne_top_of_ne_zero hρne hρtop
  have hρb : b ≤ 16 * a := by
    dsimp [a, b]
    exact hρ_le
  have haa : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha_ne ha_top
  have hbb : b * b⁻¹ = 1 := ENNReal.mul_inv_cancel hb_ne hb_top
  have hst : a⁻¹ * b ≤ 16 := by
    calc
      a⁻¹ * b ≤ a⁻¹ * (16 * a) := by exact mul_le_mul_right hρb (a⁻¹)
      _ = 16 := by
        rw [show a⁻¹ * (16 * a) = 16 * (a⁻¹ * a) by ring, haa, mul_one]
  have hgoal : a⁻¹ ≤ 16 * b⁻¹ := by
    calc
      a⁻¹ = (a⁻¹ * b) * b⁻¹ := by rw [mul_assoc, hbb, mul_one]
      _ ≤ 16 * b⁻¹ := by exact mul_le_mul_left hst (b⁻¹)
  calc
    σ ^ (-2 * γ) = (σ ^ (2 * γ))⁻¹ := by
      rw [show -2 * γ = -(2 * γ) by ring, ENNReal.rpow_neg]
    _ ≤ 16 * (ρ ^ (2 * γ))⁻¹ := by
      simpa [a, b] using hgoal
    _ = 16 * ρ ^ (-2 * γ) := by
      rw [show -2 * γ = -(2 * γ) by ring]
      rw [← ENNReal.rpow_neg]

-- The volume factor of the fine-factor bracket: since `σ ≤ ρ` and `1 - γ/2 ≥ 0`, the whole
-- power only decreases as it is read at `σ` rather than at `ρ`.
private lemma fineScale_vol_le {δ τ : NNReal} (hδτ : δ ≤ τ) (hτ : 0 < τ)
    {γ : ℝ} (hγ1 : γ ≤ 1) (m : ℕ) :
    ((m : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((m : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hσρ : ((fineScale δ τ : NNReal) : ENNReal) ≤ ((δ / τ : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (fineScale_bounds hδτ hτ).1
  have hsq : ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)
      ≤ ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ) := by
    simpa [pow_two] using
      mul_le_mul hσρ hσρ (zero_le) (zero_le)
  have hbase : (m : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)
      ≤ (m : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ) := by
    exact mul_le_mul_right hsq (m : ENNReal)
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  exact ENNReal.rpow_le_rpow hbase hpos

theorem fineScale_bracket_le {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ : 0 < τ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (m : ℕ) :
    ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((m : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ 16 * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((m : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hA : ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
      ≤ 16 * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ) :=
    fineScale_rpow_neg_le hδ hδτ hτ hγ0 hγ1
  have hB : ((m : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ ((m : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
    fineScale_vol_le hδτ hτ hγ1 m
  exact mul_le_mul hA hB (zero_le) (zero_le)

/-- **The auxiliary parameter is eventually at most `1/4`** (blueprint
`lem:ml1bootEventuallyLeQuarter`), which is the one smallness the truncated output scale asks
of `δ`: it is the hypothesis of `Kakeya.ml1Boot.le_fineScale`.  Every consumer of the fine
normalization already quantifies `δ` through `∀ᶠ δ in 𝓝[>] 0`, so nothing has to be added to
any statement to obtain it. -/
theorem eventually_le_quarter : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 / 4 := by
  exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Filter.eventually_of_mem (Iic_mem_nhds (by norm_num)) fun δ hδ => hδ)

/-- **The normalization loss `C_{lem:ml1bootFineNormalizeCore}(R)`** (blueprint
`def:ml1bootFineNormalizeCoreConstant`), at normalized ambient radius `R` and tilt factor `κ`.

`fineNormalize.C R κ = (4 R) ^ 12 * Tube.comparableReplacement.C 3 ((4 R) ^ 6)
+ Tube.essDistinctTubesInSelfDilate.C 3 (4 (κ + 2) R C_n)`, `C_n = Tube.tubeOverlapCoreClose.C 3`:
the total distortion incurred when a family of `δ`-tubes inside a `τ`-tube `T_τ` is carried to a
family of `Kakeya.ml1Boot.fineScale δ τ`-tubes in `B₁ ⊆ ℝ³`, given that the normalization
`Φ_{T_τ}` puts the containing body in `B_R`.  The first summand collects `Φ_{T_τ}` followed by
the homothety `z ↦ z / (4 R)`, the volume comparison between an image and the honest tube
covering it, and the ambient enlargement to `B₁` (powers of `4 R`), together with the selection
constant `Tube.comparableReplacement.C` at the comparability constant `(4 R) ^ 6`.

## The second summand, and where the tilt parameter comes from

`κ` is the tilt factor of the fine cores against the axis of `T_τ`: the hypothesis
`|f_i - ⟨e, f_i⟩ e| ≤ κ τ` of blueprint `lem:ml1bootFineNormalizeCore`, line 50 of
`section8_finenormalize_core.tex`.  The route that lemma takes selects *downstairs*, through
`Tube.exists_comparableReplacement_affine`, whose selection constant is
`Tube.essDistinctTubesInSelfDilate.C 3 (4 (κ + 2) R C_n)` — blueprint
`section8_finenormalize_core.tex` line 70, restated at line 291 and line 415 — and **not** the
`Tube.comparableReplacement.C 3 ((4 R) ^ 6)` of the abandoned inner-honest-tube route.  That
selection constant grows like `κ ^ 12`, so a value that does not see `κ` cannot dominate it for
all `κ`; this is what obligation `item:fineNormOwedConstant` (lines 411-441) had to discharge by
hand, at `κ ≤ 4`.

Carrying `κ` here and adding the selection constant as a summand is the enlargement that
obligation authorizes in writing at lines 449-452 ("`Kakeya.ml1Boot.fineNormalize.C` is enlarged
to accommodate `C₁`, which is harmless downstream because every consumer carries the symbol
opaquely"), and again at `def:ml1bootFineNormalizeCoreConstant` lines 84-87.  With it the
domination `C₁ ≤ fineNormalize.C R κ` is `le_add_self` at *every* `κ` and every `R`, not a
numerical check at `κ ≤ 4`: the `2 ≤ κ ≤ 4` hypothesis of blueprint
`lem:ml1bootFineNormalizeCore` is no longer needed *for the constant*.  The lower bound `2 ≤ κ`
is still what makes the two instances read the tilt clause as a weakening, and is why the
default value below is `2`.

The `.toNNReal` inside `Tube.essDistinctTubesInSelfDilate.C` is inert on the ratio written here:
`C_n > 1`, `R ≥ 1` and `κ + 2 ≥ 2` at both instances.

The homothety ratio is `4 R` and not `R`.  At ratio `R` the normalized parent fills `B₁` with
no room to spare (`Tube.normalization_distortion`, item `image_ambient_subset_closedBall`), and
the extension of an image core to the unit length that a `Kakeya.Tube` demands then protrudes
from `B₁`; at ratio `4 R` the image core lies in `B_{1/4}`, its unit-length extension in
`B_{3/4}`, and the output tube — of radius at most `1/4` by `Kakeya.ml1Boot.fineScale_bounds` —
in `B₁`.

The two instances used are `(R, κ) = (C_N, 2)` for `Kakeya.ml1Boot.exists_fineNormalization`,
where the tilt is `Tube.perp_norm_core_sub_le_of_subset`, and
`(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))` for
`Kakeya.ml1Boot.exists_fineNormalization_dilate` at dilation ratio `c`, where the tilt is
`Tube.perp_norm_core_sub_le_of_subset_dilate` at bound `2 c θ`; `C_N = Tube.normalization.C 3`,
and the factor `1 + 2 c` bounds the growth of the ambient ball under the `c`-dilate.  At `c = 2`
— the ratio the chain of `Kakeya.ml1Boot.reduceToTb_fine_factor_dilate` uses — the tilt is `4`,
which is the value blueprint `section8_finenormalize_core.tex` line 59 names for that instance.
It depends only on `R`, on `κ` and on the ambient dimension `3`; in particular not on `δ`, on
`τ`, on `θ`, on `γ`, on `j`, or on the family. -/
noncomputable abbrev fineNormalize.C (R : NNReal) (κ : NNReal := 2) : NNReal :=
  (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6)
    + _root_.Tube.essDistinctTubesInSelfDilate.C 3
        (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)

/-- **The selection summand of `Kakeya.ml1Boot.fineNormalize.C` is nondecreasing in its ratio.**

`Tube.essDistinctTubesInSelfDilate.C n` has no monotonicity lemma of its own in
`Kakeya/Tube/Rescale.lean`, and that file is not ours to extend; this is the instance the
comparisons below need.  Both summands of that constant are a fixed factor times a power of
`c.toNNReal`, so the statement is `Real.toNNReal_le_toNNReal` under `gcongr`. -/
private lemma essDistinctTubesInSelfDilate_C_le_of_le {n : ℕ} {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    _root_.Tube.essDistinctTubesInSelfDilate.C n c₁
      ≤ _root_.Tube.essDistinctTubesInSelfDilate.C n c₂ := by
  have h' : c₁.toNNReal ≤ c₂.toNNReal := Real.toNNReal_le_toNNReal h
  unfold _root_.Tube.essDistinctTubesInSelfDilate.C
    _root_.Tube.essDistinctTubesInSelfDilate.thinC
    _root_.Tube.essDistinctTubesInSelfDilate.fatC
  gcongr

/-- **`1 ≤ C_{lem:ml1bootFineNormalizeCore}(R)`** for `1 ≤ R` (blueprint
`lem:ml1bootFineNormalizeCoreConstantOneLe`): the first summand is already a product of a power
of `4 R ≥ 1` with a selection constant, both at least `1`.  No hypothesis on the tilt `κ` is
needed.  Stated so that consumers cite it instead of unfolding the constant, whose unfolded
numeral is far too large to evaluate. -/
theorem one_le_fineNormalize_C {R κ : NNReal} (hR : 1 ≤ R) :
    (1 : NNReal) ≤ fineNormalize.C R κ := by
  unfold fineNormalize.C
  refine le_trans ?_ le_self_add
  exact one_le_mul (one_le_pow₀ (one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hR))
    (_root_.Tube.comparableReplacement.one_le_C 3 ((4 * R) ^ 6))

/-- **The constant `C_{lem:ml1bootFineFactor}`** of `Kakeya.ml1Boot.multiplicity_le_fine`
(blueprint `def:ml1bootFineFactorConstant`).

`fineFactor.C = 16 * fineNormalize.C C_N`, with `C_N = Tube.normalization.C 3`: the loss of the
normalization `Kakeya.ml1Boot.exists_fineNormalization`, times the bracket factor `16` of
`Kakeya.ml1Boot.fineScale_bracket_le`.  The tilt argument of
`Kakeya.ml1Boot.fineNormalize.C` is left at its default `κ = 2`, which is the tilt the
undilated instance has from `Tube.perp_norm_core_sub_le_of_subset`.

The two constants are deliberately distinct, and the `16` sits on this one and not on the
normalization: the normalization meets its four conclusions at
`Kakeya.ml1Boot.fineNormalize.C C_N`, and the `16` is spent exactly once above it, in
`Kakeya.ml1Boot.fine_genKF`, when the estimate obtained at the truncated scale
`Kakeya.ml1Boot.fineScale δ τ` is rewritten at the scale `δ / τ` that every consumer names.
Writing the `16` into both would overshoot.  See blueprint
`note:ml1bootFineScaleWhyConstant`.

It depends only on the ambient dimension `3`; in particular not on `δ`, on `τ`, on `θ`, on
`γ`, on `j`, or on the family. -/
noncomputable abbrev fineFactor.C : NNReal := 16 * fineNormalize.C (_root_.Tube.normalization.C 3)

/-- **`1 ≤ C₂`** (blueprint `lem:ml1bootFineFactorConstantOneLe`), from
`Kakeya.ml1Boot.one_le_fineNormalize_C` and `Tube.normalization.one_le_C`. -/
theorem one_le_fineFactor_C : (1 : NNReal) ≤ fineFactor.C := by
  unfold fineFactor.C
  exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16)
    (one_le_fineNormalize_C (Tube.normalization.one_le_C 3))

/-- **The normalization loss is at most the fine-factor constant**
(blueprint `lem:ml1bootFineNormalizeCoreConstantLeFineFactor`): they differ by the factor
`16`.  This is the direction every consumer needs — a bound proved at the smaller constant is
usable where the larger one is stated — and it is not reversible. -/
theorem fineNormalize_C_le_fineFactor_C :
    fineNormalize.C (_root_.Tube.normalization.C 3) ≤ fineFactor.C := by
  rw [fineFactor.C]
  exact le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 16)

section Fine

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A fine fibre, as the three fine-factor lemmas consume it** (blueprint
`lem:ml1bootFineNormalize` and `lem:ml1bootFineFactor`, the hypotheses on `𝕋[T_τ]`).

`(T i)_{i ∈ u}` is a nonempty family of pairwise essentially distinct shaded `δ`-tubes sitting
inside a single `τ`-tube `T_τ ⊆ B₁`, with shading densities two-sidedly comparable to a common
`μ₀` with constant `Λ`, and with fullness at least `C Λ² δ ^ ηs`.

This is exactly the fibre `𝕋[T_{τ,k}]` over one parent, which is why the block is verbatim
the same in `Kakeya.ml1Boot.fine_genKF`,
`Kakeya.ml1Boot.multiplicity_le_fine_frostmanLoss` and `Kakeya.ml1Boot.multiplicity_le_fine`;
only the Frostman bound differs between them and so is not a field here.

The two-sided density bound is what `Kakeya.ml1Boot.exists_fineNormalization` needs to replace
each tube by a comparable honest one, and it is stated with the individual volumes
`|T i|` rather than the common volume of a `δ`-tube: all `δ`-tubes are isometric, so the two
readings agree, and the pointwise form is the one `Tube.exists_comparableReplacement`
consumes.  The fullness threshold carries the same `C Λ²` prefactor that
`Kakeya.ml1Boot.exists_fineNormalization` loses, so that it survives the normalization. -/
structure IsFineFibre {ι : Type*} {δ τ : NNReal} (Λ : NNReal) (μ₀ : ENNReal) (ηs : ℝ)
    (u : Finset ι) (Tτ : Tube τ E) (T : ι → ShadedTube δ E) : Prop where
  /-- The common density the shadings are compared to is nonzero. -/
  density_pos : 0 < μ₀
  /-- The fibre is nonempty. -/
  nonempty : u.Nonempty
  /-- The parent tube lies in the unit ball. -/
  parent_ball : Tτ.carrier ⊆ Metric.closedBall 0 1
  /-- Every member of the fibre lies in the parent tube. -/
  subset_parent : ∀ i ∈ u, (T i).carrier ⊆ Tτ.carrier
  /-- The members are pairwise essentially distinct. -/
  essDistinct : (u : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- The shading densities are two-sidedly comparable to `μ₀`, with constant `Λ`. -/
  shade_comparable : ∀ i ∈ u,
    (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier
  /-- The fibre is full, with the prefactor the normalization loses. -/
  fullness : (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
    ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)

/-! #### The scale obstruction, and why the output scale is truncated

The three declarations below record, in Lean, why
`Kakeya.ml1Boot.exists_fineNormalization` cannot ask for `δ / τ`-tubes in `B₁`: that demand is
*unsatisfiable* at the extreme scale `δ = τ` permitted by the hypotheses `0 < δ ≤ τ ≤ 1`,
since a `ρ`-tube with `ρ > 1/2` does not fit in any ball of radius `1`, its carrier having
diameter `1 + 2 ρ > 2`.

They are refutations of the *earlier* form of the two normalization lemmas, and are kept as
the reason the present form truncates its output scale to
`Kakeya.ml1Boot.fineScale δ τ = min (δ/τ) (1/4)`.  They do not apply to that form:
`fineScale δ τ ≤ 1/4 < 1/2`, the second clause of `Kakeya.ml1Boot.fineScale_bounds`.  See
blueprint
`note:ml1bootFineNormalizeScaleObstruction`. -/

/-- **A `ρ`-tube with `1/2 < ρ` fits in no ball of radius `1`.**

A `ρ`-tube is the closed `ρ`-neighbourhood of a segment `[x, y]` of length exactly `1`
(`Tube.carrier_eq`), so it contains the two points `x - ρ e` and `y + ρ e`, where
`e = y - x` is the unit direction; these are at distance `1 + 2 ρ`.  A ball of radius `1`
has diameter `2`, so `1 + 2 ρ ≤ 2`, i.e. `ρ ≤ 1/2`.

This is the obstruction behind `Kakeya.ml1Boot.not_exists_fineNormalization`. -/
theorem tube_not_subset_closedBall_of_half_lt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [ProperSpace F] {ρ : NNReal} (hρ : 1 / 2 < (ρ : ℝ))
    (T : _root_.Tube ρ F) (c : F) : ¬ T.carrier ⊆ Metric.closedBall c 1 := by
  intro hsub
  let e : F := T.direction
  let p : F := T.x - (ρ : ℝ) • e
  let q : F := T.y + (ρ : ℝ) • e
  have hρnonneg : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hp_mem : p ∈ T.carrier := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y, ?_⟩
    rw [Metric.mem_closedBall]
    have hpdist : dist p T.x = (ρ : ℝ) := by
      dsimp [p, e]
      rw [dist_eq_norm']
      have hv : T.x - (T.x - (ρ : ℝ) • (T.y - T.x)) = (ρ : ℝ) • (T.y - T.x) := by module
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρnonneg]
      rw [Tube.norm_direction]
      norm_num
    rw [hpdist]
  have hq_mem : q ∈ T.carrier := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y, ?_⟩
    rw [Metric.mem_closedBall]
    have hqdist : dist q T.y = (ρ : ℝ) := by
      dsimp [q, e]
      rw [dist_eq_norm]
      have hv : (T.y + (ρ : ℝ) • (T.y - T.x)) - T.y = (ρ : ℝ) • (T.y - T.x) := by module
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρnonneg]
      rw [Tube.norm_direction]
      norm_num
    rw [hqdist]
  have hpq : dist p q = 1 + 2 * (ρ : ℝ) := by
    rw [dist_eq_norm']
    have hvec : q - p = (1 + 2 * (ρ : ℝ)) • (T.y - T.x) := by
      dsimp [q, p, e]
      module
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
    · rw [Tube.norm_direction]
      norm_num
    · positivity
  have hpc : p ∈ Metric.closedBall c 1 := hsub hp_mem
  have hqc : q ∈ Metric.closedBall c 1 := hsub hq_mem
  have hpc' : dist p c ≤ 1 := Metric.mem_closedBall.mp hpc
  have hqc' : dist q c ≤ 1 := Metric.mem_closedBall.mp hqc
  have hcq : dist c q ≤ 1 := by simpa [dist_comm] using hqc'
  have hpq_le : dist p q ≤ 2 := by
    calc
      dist p q ≤ dist p c + dist c q := dist_triangle p c q
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  linarith

/-- **A `(1/2)`-tube inside the closed unit ball of `ℝ³`.**

The tube with core the segment from `-e/2` to `e/2`, where `e` is the first standard basis
vector: its core lies in the ball of radius `1/2` about the origin, so its closed
`(1/2)`-neighbourhood lies in `B₁`.  It witnesses that the hypotheses of
`Kakeya.ml1Boot.exists_fineNormalization` are satisfiable at `δ = τ = 1/2`. -/
theorem exists_halfTube_subset_closedBall :
    ∃ T : _root_.Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)),
      T.carrier ⊆ Metric.closedBall 0 1 := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ)
  let p : EuclideanSpace ℝ (Fin 3) := -(1 / 2 : ℝ) • e
  let q : EuclideanSpace ℝ (Fin 3) := (1 / 2 : ℝ) • e
  have hnorm_e : ‖e‖ = 1 := by
    simp [e]
  have hqp : q - p = e := by
    dsimp [q, p, e]
    rw [sub_eq_add_neg]
    simp only [neg_smul, neg_neg]
    rw [← add_smul]
    norm_num
  have hdist : dist p q = 1 := by
    rw [dist_eq_norm_sub' p q, hqp, hnorm_e]
  have hp_norm : ‖p‖ = 1 / 2 := by
    dsimp [p]
    rw [norm_smul, hnorm_e]
    norm_num
  have hq_norm : ‖q‖ = 1 / 2 := by
    dsimp [q]
    rw [norm_smul, hnorm_e]
    norm_num
  have hp_ball : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero, hp_norm]
  have hq_ball : q ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall]
    rw [dist_eq_norm, sub_zero, hq_norm]
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)) :=
    convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)
  have hseg : segment ℝ p q ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) :=
    Convex.segment_subset hconv hp_ball hq_ball
  let T : _root_.Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    _root_.Tube.mk' (1 / 2 : NNReal) (x := p) (y := q) hdist
  refine ⟨T, ?_⟩
  intro w hw
  dsimp [T] at hw
  change w ∈ ⋃ z ∈ segment ℝ p q, Metric.closedBall z ((1 / 2 : NNReal) : ℝ) at hw
  rw [Set.mem_iUnion₂] at hw
  rcases hw with ⟨z, hz, hwz⟩
  have hwz' : dist w z ≤ (1 / 2 : ℝ) := by
    have h := Metric.mem_closedBall.mp hwz
    norm_num at h ⊢
    exact h
  have hz_ball : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ) := hseg hz
  have hz0 : dist z 0 ≤ 1 / 2 := Metric.mem_closedBall.mp hz_ball
  have hw0 : dist w 0 ≤ 1 := by
    calc
      dist w 0 ≤ dist w z + dist z 0 := dist_triangle w z 0
      _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) := by gcongr
      _ = 1 := by norm_num
  exact Metric.mem_closedBall.mpr hw0

/-- **(negative result) the untruncated fine normalization is false.**

This refutes the *earlier* form of `Kakeya.ml1Boot.exists_fineNormalization`, the one whose
output family consisted of `δ / τ`-tubes in `B₁`.  The present form outputs
`Kakeya.ml1Boot.fineScale δ τ`-tubes, and `fineScale δ τ ≤ 1/4`, so the witness below says
nothing about it; the theorem is retained because it is the reason for the truncation.

Instantiate it at `δ = τ = 1/2`, `Λ = 1`, `μ₀ = 1`, `ι = Unit`, `u = {}`, `T_τ` the
`(1/2)`-tube of `Kakeya.ml1Boot.exists_halfTube_subset_closedBall`, and `T` the constant
family whose single member is `T_τ` shaded by its whole carrier.  All of
`hδ : 0 < δ`, `hδτ : δ ≤ τ`, `hτ1 : τ ≤ 1`, `hΛ : 1 ≤ Λ`, `hμ₀ : 0 < μ₀`, `hu`, `hTτ`,
`hsub`, `hED` (vacuous on a singleton) and `hdens` hold.  But `δ / τ = 1 > 1/2`, so by
`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt` no `δ / τ`-tube lies in `B₁`, while
the conclusion asks for a *nonempty* `u' ⊆ u` indexing such tubes.

Only the second conclusion clause of the earlier statement is retained here, which makes this
refutation stronger than the refutation of the full statement.

The repair taken is *not* a hypothesis bounding `δ / τ` — no such bound is available anywhere
in Section 8 — but a truncation of the output scale to `Kakeya.ml1Boot.fineScale δ τ`; see
blueprint `note:ml1bootFineNormalizeScaleObstruction`. -/
theorem not_exists_fineNormalization :
    ¬ ∀ {ι : Type} {u : Finset ι}
        (Tτ : _root_.Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)))
        (T : ι → ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3))),
        u.Nonempty →
        Tτ.carrier ⊆ Metric.closedBall 0 1 →
        (∀ i ∈ u, (T i).carrier ⊆ Tτ.carrier) →
        ((u : Set ι).Pairwise fun i j =>
          IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ u, ((1 : NNReal) : ENNReal)⁻¹ * 1 * volume (T i).carrier
            ≤ volume (T i).shade ∧
          volume (T i).shade ≤ ((1 : NNReal) : ENNReal) * 1 * volume (T i).carrier) →
        ∃ u' ⊆ u, u'.Nonempty ∧
          ∃ V : ι → ShadedTube ((1 / 2 : NNReal) / (1 / 2 : NNReal))
              (EuclideanSpace ℝ (Fin 3)),
            ∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1 := by
  intro h
  obtain ⟨Tτ, hTτ⟩ := exists_halfTube_subset_closedBall
  let S : ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    { toTube := Tτ
      shade := Tτ.carrier
      measurableSet_shade := Tτ.isCompact.measurableSet
      shade_subset := subset_rfl }
  let T : Unit → ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) := fun _ => S
  have hS_sub : ∀ i ∈ ({()} : Finset Unit), (T i).carrier ⊆ Tτ.carrier := by
    intro i hi
    exact subset_rfl
  have hS_dens : ∀ i ∈ ({()} : Finset Unit),
      ((1 : NNReal) : ENNReal)⁻¹ * 1 * volume (T i).carrier ≤ volume (T i).shade ∧
        volume (T i).shade ≤ ((1 : NNReal) : ENNReal) * 1 * volume (T i).carrier := by
    intro i hi
    simp [T, S]
  have hS_ED : (({()} : Finset Unit) : Set Unit).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier := by
    intro i hi j hj hij
    exact absurd (Subsingleton.elim i j) hij
  have hS_nonempty : ({()} : Finset Unit).Nonempty := ⟨(), by simp⟩
  rcases h (ι := Unit) (u := ({()} : Finset Unit)) Tτ T hS_nonempty hTτ hS_sub hS_ED hS_dens
    with ⟨u', _hu'sub, hu'ne, V, hV⟩
  rcases hu'ne with ⟨i, hi⟩
  exact tube_not_subset_closedBall_of_half_lt (ρ := (1 / 2 : NNReal) / (1 / 2 : NNReal))
    (by norm_num) (V i).toTube 0 (hV i hi)

/-- **(negative result) the untruncated fine normalization over a dilate is false.**

As with `Kakeya.ml1Boot.not_exists_fineNormalization`, this refutes the *earlier* form of
`Kakeya.ml1Boot.exists_fineNormalization_dilate`, whose output family consisted of
`δ / τ`-tubes in `B₁`, and says nothing about the present truncated form.

It is the same witness, transported along `Tube.subset_dilate`: a tube lies in its own
`2`-dilate, so the containment hypothesis `T i ≤ 2 · T_τ` is *weaker* than the containment
`T i ⊆ T_τ` the witness satisfies, and the refuted conclusion clause is verbatim the same.
See blueprint `note:ml1bootFineNormalizeScaleObstruction`. -/
theorem not_exists_fineNormalization_dilate :
    ¬ ∀ {ι : Type} {u : Finset ι}
        (Tτ : _root_.Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)))
        (T : ι → ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3))),
        u.Nonempty →
        Tτ.carrier ⊆ Metric.closedBall 0 1 →
        (∀ i ∈ u, (T i).toConvexSpaceBody ≤ Tube.dilate Tτ 2) →
        ((u : Set ι).Pairwise fun i j =>
          IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ u, ((1 : NNReal) : ENNReal)⁻¹ * 1 * volume (T i).carrier
            ≤ volume (T i).shade ∧
          volume (T i).shade ≤ ((1 : NNReal) : ENNReal) * 1 * volume (T i).carrier) →
        ∃ u' ⊆ u, u'.Nonempty ∧
          ∃ V : ι → ShadedTube ((1 / 2 : NNReal) / (1 / 2 : NNReal))
              (EuclideanSpace ℝ (Fin 3)),
            ∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1 := by
  intro h
  obtain ⟨Tτ, hTτ⟩ := exists_halfTube_subset_closedBall
  let S : ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    { toTube := Tτ
      shade := Tτ.carrier
      measurableSet_shade := Tτ.isCompact.measurableSet
      shade_subset := subset_rfl }
  let T : Unit → ShadedTube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) := fun _ => S
  have hS_sub : ∀ i ∈ ({()} : Finset Unit), (T i).toConvexSpaceBody ≤ Tube.dilate Tτ 2 := by
    intro i hi
    change Tτ.carrier ⊆ (Tube.dilate Tτ 2).carrier
    exact _root_.Tube.subset_dilate Tτ (by norm_num)
  have hS_dens : ∀ i ∈ ({()} : Finset Unit),
      ((1 : NNReal) : ENNReal)⁻¹ * 1 * volume (T i).carrier ≤ volume (T i).shade ∧
        volume (T i).shade ≤ ((1 : NNReal) : ENNReal) * 1 * volume (T i).carrier := by
    intro i hi
    simp [T, S]
  have hS_ED : (({()} : Finset Unit) : Set Unit).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier := by
    intro i hi j hj hij
    exact absurd (Subsingleton.elim i j) hij
  have hS_nonempty : ({()} : Finset Unit).Nonempty := ⟨(), by simp⟩
  rcases h (ι := Unit) (u := ({()} : Finset Unit)) Tτ T hS_nonempty hTτ hS_sub hS_ED hS_dens
    with ⟨u', _hu'sub, hu'ne, V, hV⟩
  rcases hu'ne with ⟨i, hi⟩
  exact tube_not_subset_closedBall_of_half_lt (ρ := (1 / 2 : NNReal) / (1 / 2 : NNReal))
    (by norm_num) (V i).toTube 0 (hV i hi)

/-- **The selection constant of the downstairs route is dominated by the normalization loss.**

The selection constant that `Tube.exists_comparableReplacement_affine` returns at tilt `κ = 2`
and normalized ambient radius `R = C_N` is
`c₁ = C_{lem:essDistinctTubesInSelfDilate}(3, 16 C_N C_n)`, `C_n = Tube.tubeOverlapCoreClose.C 3`,
and the three products of it that
`Kakeya.ml1Boot.exists_fineNormalization` has to pay — `c₁` for the multiplicity clause,
`(4 C_N) ^ 6 c₁` for the fullness clause (one volume comparison) and `(4 C_N) ^ 12 c₁` for the
Frostman clause (a volume comparison and the ambient enlargement to `B₁`) — all fit inside
`Kakeya.ml1Boot.fineNormalize.C C_N`.

The first is `le_add_self`.  For the other two, both summands of
`Tube.essDistinctTubesInSelfDilate.C` carry the *same* dimensional factors as the two summands
of `Tube.comparableReplacement.Kstar 3`, so `c₁ ≤ K_∗(3) (16 C_N C_n) ^ 12`, while the first
summand of `fineNormalize.C C_N` is at least `(4 C_N) ^ 12 K_∗(3) (4 C_N) ^ 36 C_n ^ 12`; the
comparison reduces to `16 ^ 12 ≤ (4 C_N) ^ 24`, which holds with enormous room at `C_N = 64`. -/
private lemma fineNormalize_C_dominates {c₁ : NNReal}
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((2 : ℝ) + 2) * ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C (_root_.Tube.normalization.C 3) ∧
      ((4 * _root_.Tube.normalization.C 3) ^ 6 : NNReal) * c₁
        ≤ fineNormalize.C (_root_.Tube.normalization.C 3) ∧
      ((4 * _root_.Tube.normalization.C 3) ^ 12 : NNReal) * c₁
        ≤ fineNormalize.C (_root_.Tube.normalization.C 3) := by
  let CN : NNReal := _root_.Tube.normalization.C 3
  let ratio : ℝ := 4 * ((2 : ℝ) + 2) * (CN : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  let D : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C 3).toNNReal
  let u : NNReal := (16 : NNReal) * CN * D
  have hCN1 : (1 : NNReal) ≤ CN := _root_.Tube.normalization.one_le_C 3
  have hD0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ))
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hD1 : (1 : NNReal) ≤ D := by
    dsimp [D]; rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hD0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hratio0 : (0 : ℝ) ≤ ratio := by
    dsimp [ratio]
    positivity
  have hu_re : ratio = (u : ℝ) := by
    dsimp [u, ratio, D]
    norm_num
    exact hD0
  have hu : ratio.toNNReal = u := by
    apply NNReal.coe_injective
    rw [Real.toNNReal_of_nonneg hratio0]
    exact hu_re
  have hu1 : (1 : NNReal) ≤ u :=
    one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 16) hCN1) hD1
  have hu6 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu1 (by norm_num)
  have hbase : (1 : NNReal) ≤ 4 * CN := one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hCN1
  have hpw6 : (4 * CN) ^ 6 ≤ (4 * CN) ^ 12 := pow_le_pow_right₀ hbase (by norm_num)
  have h16le : (16 : NNReal) ^ 12 ≤ (4 : NNReal) ^ 36 := by
    calc
      (16 : NNReal) ^ 12 = (4 : NNReal) ^ 24 := by norm_num
      _ ≤ (4 : NNReal) ^ 36 := pow_le_pow_right₀ (by norm_num : (1 : NNReal) ≤ 4) (by norm_num)
  have hu12 : u ^ 12 ≤ ((4 * CN) ^ 6) ^ 6 * D ^ 12 := by
    calc
      u ^ 12 = (16 : NNReal) ^ 12 * CN ^ 12 * D ^ 12 := by dsimp [u]; rw [mul_pow, mul_pow]
      _ ≤ (4 : NNReal) ^ 36 * CN ^ 36 * D ^ 12 := by
            exact mul_le_mul
              (mul_le_mul h16le (pow_le_pow_right₀ hCN1 (by norm_num))
                (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = ((4 * CN) ^ 6) ^ 6 * D ^ 12 := by rw [← mul_pow, ← pow_mul]
  have hkey : c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * CN) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : NNReal :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : NNReal)) ^ (2 * 3 - 1) with hA
    set B : NNReal := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3)
          = A * u ^ 6 + B * u ^ 12 := by rw [hu]
      _ ≤ A * u ^ 12 + B * u ^ 12 := by
            exact add_le_add (mul_le_mul le_rfl hu6 (by positivity) (by positivity)) le_rfl
      _ = (A + B) * u ^ 12 := by ring
      _ ≤ (A + B) * (((4 * CN) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12 (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * CN) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * CN) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  constructor
  · unfold fineNormalize.C
    rw [hc₁]
    exact le_add_self
  constructor
  · unfold fineNormalize.C
    exact le_trans
      (le_trans (mul_le_mul hpw6 le_rfl (by positivity) (by positivity))
        (mul_le_mul le_rfl hkey (by positivity) (by positivity)))
      le_self_add
  · unfold fineNormalize.C
    exact le_trans (mul_le_mul le_rfl hkey (by positivity) (by positivity)) le_self_add

/-- **Reading off the four conclusions from `Tube.IsComparableReplacementFree`.**

The package hands back the retained index set `u'`, and its four fields plus two generic
transport lemmas give the three quantitative clauses at the constants recorded here:
multiplicity is exact and pays only the selection constant `C₁`
(`ShadedBody.multiplicity_le_of_isCRefinement` against the refinement clause), fullness pays the
comparability constant `Cv` on top of it (`ShadedBody.IsCRefinement.coe_mul_fullness_le`), and
the Frostman constant pays `C₁` for the passage to the subfamily
(`ConvexSpaceBody.frostmanConstIn_subfamily_le`, applicable because all members of `𝕍` are
`σ`-tubes and hence of equal volume) and `Cv` for the comparability.  The factor `Λ ^ 2` is the
density spread, and enters through the refinement constant `(C₁ Λ ^ 2)⁻¹`. -/
private lemma of_comparableReplacementFree {ι : Type*} {u : Finset ι} {σ : NNReal}
    {𝕎 : ι → ShadedBody E} {𝕍 : ι → ShadedTube σ E} {K : ConvexSpaceBody E}
    {Cv Λ C₁ : NNReal} (hΛ : 1 ≤ Λ) (hCv : 1 ≤ Cv) (hC₁ : 1 ≤ C₁)
    (hVK : ∀ i ∈ u, (𝕍 i).toConvexSpaceBody ≤ K)
    (h : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍 K Cv Λ C₁) :
    ∃ u' ⊆ u, u'.Nonempty ∧
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
        ShadedBody.multiplicity u 𝕎
          ≤ (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) ∧
        (ShadedBody.fullness u 𝕎 : ENNReal)
          ≤ ((Cv : ENNReal) * (C₁ : ENNReal)) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ENNReal) * (Cv : ENNReal)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by
  rcases h.select with ⟨u', hu'sub, hu'ne, hpair, hu'card, hcref⟩
  let ce : ENNReal := ((C₁ * Λ ^ 2)⁻¹ : NNReal)
  have hL0 : Λ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ)
  have hC₁0 : C₁ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC₁)
  have hC₁Λ : (C₁ * Λ ^ 2 : NNReal) ≠ 0 := mul_ne_zero hC₁0 (pow_ne_zero 2 hL0)
  have hC₁ΛE0 : ((C₁ * Λ ^ 2 : NNReal) : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁Λ
  have hce0 : ce ≠ 0 := by
    dsimp [ce]
    rw [ENNReal.coe_inv hC₁Λ]
    intro hz
    have hcan := ENNReal.inv_mul_cancel hC₁ΛE0
      (ENNReal.coe_ne_top : ((C₁ * Λ ^ 2 : NNReal) : ENNReal) ≠ ⊤)
    rw [hz, zero_mul] at hcan
    exact zero_ne_one hcan
  have hce_top : ce ≠ ⊤ := by
    dsimp [ce]
    exact ENNReal.coe_ne_top
  have cRef_ne0 : (C₁ * Λ ^ 2 : NNReal)⁻¹ ≠ 0 :=
    ENNReal.coe_ne_zero.mp (by simpa [ce] using hce0)
  have hcoef : ce⁻¹ = (C₁ : ENNReal) * (Λ : ENNReal) ^ 2 := by
    change (((C₁ * Λ ^ 2)⁻¹ : NNReal) : ENNReal)⁻¹ = (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
    rw [ENNReal.coe_inv hC₁Λ]
    rw [InvolutiveInv.inv_inv]
    rw [ENNReal.coe_mul, ENNReal.coe_pow]
  refine ⟨u', hu'sub, hu'ne, hpair, ?_, ?_, ?_⟩
  · rw [← h.multiplicity]
    calc
      ShadedBody.multiplicity u (fun i => (𝕍 i).toShadedBody)
          ≤ ce⁻¹ * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            exact ShadedBody.multiplicity_le_of_isCRefinement (s := u)
              (V := fun i => (𝕍 i).toShadedBody) (s' := u')
              (V' := fun i => (𝕍 i).toShadedBody) (c := (C₁ * Λ ^ 2)⁻¹) cRef_ne0 hcref
      _ = (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
              * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            rw [hcoef]
  · have hfullNN : ShadedBody.fullness u 𝕎
        ≤ (Cv : NNReal) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
      have hCv0 : Cv ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCv)
      calc
        ShadedBody.fullness u 𝕎
            = (Cv : NNReal) * ((Cv : NNReal)⁻¹ * ShadedBody.fullness u 𝕎) := by
              rw [← mul_assoc, mul_inv_cancel₀ hCv0, one_mul]
        _ ≤ (Cv : NNReal) * ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) := by
              exact mul_le_mul_right h.fullness (Cv : NNReal)
    have hfull1 : (ShadedBody.fullness u 𝕎 : ENNReal)
        ≤ (Cv : ENNReal) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
      exact_mod_cast hfullNN
    have hcfull : ce * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal)
        ≤ (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
      simpa [ce] using (IsCRefinement.coe_mul_fullness_le hcref)
    have hfull2 : (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal)
        ≤ (C₁ : ENNReal) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
      have hmm := mul_le_mul_right hcfull ce⁻¹
      rwa [← mul_assoc, ENNReal.inv_mul_cancel hce0 hce_top, one_mul, hcoef] at hmm
    calc
      (ShadedBody.fullness u 𝕎 : ENNReal)
          ≤ (Cv : ENNReal) * (ShadedBody.fullness u (fun i => (𝕍 i).toShadedBody) : ENNReal) :=
            hfull1
      _ ≤ (Cv : ENNReal)
            * ((C₁ : ENNReal) * (Λ : ENNReal) ^ 2
                * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal)) := by
            gcongr
      _ = ((Cv : ENNReal) * (C₁ : ENNReal)) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by ring
  · rcases hu'ne with ⟨i₀, hi₀⟩
    have hu'ne_nonempty : u.Nonempty := ⟨i₀, hu'sub hi₀⟩
    let v : ENNReal := volume ((𝕍 i₀).toConvexSpaceBody).carrier
    have hvol : ∀ i ∈ u, volume ((𝕍 i).toConvexSpaceBody).carrier = v := by
      intro i hi
      dsimp [v]
      simpa using _root_.Tube.volume_carrier_eq_volume_carrier
        (by simpa using (𝕍 i).toTube) (by simpa using (𝕍 i₀).toTube)
    have hC₁E0 : (C₁ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC₁0
    have hC₁Etop : (C₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hcardκ : (C₁ : ENNReal)⁻¹ * (u.card : ENNReal) ≤ (u'.card : ENNReal) := by
      calc
        (C₁ : ENNReal)⁻¹ * (u.card : ENNReal)
            ≤ (C₁ : ENNReal)⁻¹ * ((C₁ : ENNReal) * (u'.card : ENNReal)) := by
              exact mul_le_mul_right hu'card _
        _ = (u'.card : ENNReal) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hC₁E0 hC₁Etop, one_mul]
    have hκ0 : (C₁ : ENNReal)⁻¹ ≠ 0 := by
      intro hz
      have hcan := ENNReal.inv_mul_cancel hC₁E0 hC₁Etop
      rw [hz, zero_mul] at hcan
      exact zero_ne_one hcan
    have hsubF := ConvexSpaceBody.frostmanConstIn_subfamily_le (s := u)
      (W := fun i => (𝕍 i).toConvexSpaceBody) (K := K)
      (v := v) (κ := (C₁ : ENNReal)⁻¹)
      hu'ne_nonempty hvol hVK hu'sub hκ0 hcardκ
    have hF1 : frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
        ≤ (C₁ : ENNReal) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := by
      simpa [InvolutiveInv.inv_inv] using hsubF
    calc
      frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody) K
          ≤ (C₁ : ENNReal) * frostmanConstIn u (fun i => (𝕍 i).toConvexSpaceBody) K := hF1
      _ ≤ (C₁ : ENNReal)
            * ((Cv : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K) := by
            exact mul_le_mul_right h.frostmanConstIn (C₁ : ENNReal)
      _ = (C₁ : ENNReal) * (Cv : ENNReal)
            * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K := by ring

/-- **The ambient enlargement to `B₁`**, in the form the fine normalization uses it: reading a
Frostman constant at the unit ball rather than at a smaller body `K'` containing every member
costs exactly the volume ratio `|B₁| / |K'|`
(`ConvexSpaceBody.frostmanConstIn_ambient_mono`), and `hratio` bounds that ratio by `Cv`. -/
private lemma frostmanConstIn_closedUnitBall_le_of_ambient
    {ι : Type*} {u : Finset ι} {𝕎 : ι → ShadedBody E} {K' : ConvexSpaceBody E} {Cv : NNReal}
    (hK' : K' ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
    (hK'vol : volume K'.carrier ≠ 0)
    (hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K')
    (hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cv : ENNReal) * volume K'.carrier) :
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cv : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
  have hmono := frostmanConstIn_ambient_mono hK' hK'vol hWK'
  have hK'voltop : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_ne_top
  have hdiv : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      / volume K'.carrier ≤ (Cv : ENNReal) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl hK'vol) (Or.inl hK'voltop)]
    exact hratio
  calc
    frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
        ≤ volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
          / volume K'.carrier
          * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := hmono
    _ ≤ (Cv : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' := by
          gcongr

-- All `δ`-tubes are isometric, so their affine images under one map have a common volume: this
-- is the hypothesis `hcommon` of `Tube.exists_comparableReplacement_affine`.
private lemma volume_affineImage_carrier_eq {δ : NNReal} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L) :
    volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  change volume (L.toAffineMap '' S.carrier) = volume (L.toAffineMap '' S'.carrier)
  rw [Kakeya.volume_affineImage L S.carrier, Kakeya.volume_affineImage L S'.carrier]
  rw [_root_.Tube.volume_carrier_eq_volume_carrier S.toTube S'.toTube]

-- An affine equivalence multiplies carrier and shade by the same Jacobian, so a two-sided
-- density bracket is carried over verbatim: the hypothesis `hZ` of
-- `Tube.exists_comparableReplacement_affine`, read at the common volume of the images.
private lemma affineImage_shade_bounds {δ : NNReal} (S S' : ShadedTube δ E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) (hemb : MeasurableEmbedding L)
    {Λ : NNReal} {μ₀ : ENNReal}
    (h₁ : (Λ : ENNReal)⁻¹ * μ₀ * volume S.carrier ≤ volume S.shade)
    (h₂ : volume S.shade ≤ (Λ : ENNReal) * μ₀ * volume S.carrier) :
    (Λ : ENNReal)⁻¹ * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
        ≤ volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade ∧
      volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
        ≤ (Λ : ENNReal) * μ₀
          * volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  -- An affine equivalence multiplies every volume by the same Jacobian `J`, so the two-sided
  -- density bracket carried over from `h₁` and `h₂` is unchanged.
  let J : ENNReal := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
  have hprimed : volume ((S'.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier :=
    (volume_affineImage_carrier_eq S S' L hcont hemb).symm
  have hcarrier : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier
      = J * volume S.carrier := by
    dsimp [J]
    change volume (L.toAffineMap '' S.carrier) = J * volume S.carrier
    exact Kakeya.volume_affineImage L S.carrier
  have hshade : volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).shade
      = J * volume S.shade := by
    dsimp [J]
    change volume (L.toAffineMap '' S.shade) = J * volume S.shade
    exact Kakeya.volume_affineImage L S.shade
  constructor
  · rw [hprimed, hcarrier, hshade]
    calc
      (Λ : ENNReal)⁻¹ * μ₀ * (J * volume S.carrier)
          = J * ((Λ : ENNReal)⁻¹ * μ₀ * volume S.carrier) := by ring
      _ ≤ J * volume S.shade := by
            exact mul_le_mul (le_rfl : J ≤ J) h₁ (by positivity) (by positivity)
  · rw [hshade, hprimed, hcarrier]
    calc
      J * volume S.shade ≤ J * ((Λ : ENNReal) * μ₀ * volume S.carrier) := by
            exact mul_le_mul (le_rfl : J ≤ J) h₂ (by positivity) (by positivity)
      _ = (Λ : ENNReal) * μ₀ * (J * volume S.carrier) := by ring

-- A `δ`-tube of positive scale has positive volume (`Tube.le_volume`), and an affine
-- equivalence has nonzero Jacobian: the hypothesis `hW` of
-- `Tube.exists_comparableReplacement_affine`.
private lemma volume_affineImage_carrier_pos [Nontrivial E] {δ : NNReal} (hδ : 0 < δ)
    (S : ShadedTube δ E) (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L)
    (hemb : MeasurableEmbedding L) :
    0 < volume ((S.toShadedBody).affineImage L.toAffineMap hcont hemb).carrier := by
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
  have hpow : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by positivity
  have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
    ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
  have hSpos : 0 < volume (S.toShadedBody).carrier := by
    calc
      0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^
          (Module.finrank ℝ E - 1) := by positivity
      _ ≤ volume (S.toShadedBody).carrier := by simpa using (_root_.Tube.le_volume S.toTube)
  have hdet : LinearMap.det (L.linear : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.linear).ne_zero
  have hJ : 0 < ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| := by
    rw [ENNReal.ofReal_pos]
    exact abs_pos.mpr hdet
  change 0 < volume (L.toAffineMap '' (S.toShadedBody).carrier)
  rw [Kakeya.volume_affineImage]
  positivity

/-- **`Tube.rescale_outer_tube` with the image-core length freed to the radius `R`.**

`Tube.rescale_outer_tube` consumes its packaged `Tube.IsNormalizationDistortion` at exactly two
fields: `image_subset_cthickening`, which is proved unconditionally by
`Tube.normalization_image_subset_cthickening` (no containment hypothesis at all), and
`dist_le_C`, which it uses only to run the chain
`dist (Ψ x) (Ψ y) = dist (Φ x) (Φ y) / (4 R) ≤ C_N / (4 R) ≤ R / (4 R) = 1/4 ≤ 1`.

So the packaged structure is stronger than the route needs: what the route needs is
`dist (Φ x) (Φ y) ≤ R`, and the packaged field supplies that only via `C_N ≤ R`.  The
distinction is invisible at `R = C_N` but decisive over a dilate: for `T ⊆ c · T₀` the image
core has length at most `√(1 + 4 c²)`, which exceeds the hardwired `C_N = 64` once
`c > 31.99…`, while the dilated instance runs at `R = (1 + 2 c) C_N` and so satisfies the
relaxed hypothesis for *every* `c`.  Freeing the field here is therefore what makes
`Kakeya.ml1Boot.exists_fineNormalization_dilate` provable at an unbounded dilation ratio.

`Kakeya/Tube/Rescale.lean` is not ours to extend, so this is the local restatement; the proof is
that of `Tube.rescale_outer_tube` with the two `hdist` projections replaced by `hcth` and
`hlen`. -/
private lemma rescale_outer_tube_of_dist_le [Nontrivial E] {θ ρ σ : NNReal} {R : ℝ}
    (hsit : _root_.Tube.IsRescalingSituation θ ρ σ R 3) (hn : Module.finrank ℝ E = 3)
    (hR : 0 < R) (hρσ : (ρ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube ρ E)
    (hcth : T₀.normalization '' T.carrier ⊆
      Metric.cthickening
        ((_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) * ((ρ : ℝ) / (θ : ℝ)))
        (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y)))
    (hlen : dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ R)
    (hball : T₀.normalization '' T.carrier ⊆ Metric.closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier ∧
      (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      volume (_root_.Tube.centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
  let τ : ℝ := (ρ : ℝ) / (θ : ℝ)
  let C0 : ℝ := (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ)
  have hθpos : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hsit.pos_ambient
  have hρ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    exact div_nonneg (by positivity) (le_of_lt hθpos)
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4R0 : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC0_le_R : C0 ≤ R := by
    dsimp [C0]
    simpa [hn] using hsit.normalizationConst_le_radius
  have hRdiv : R / (4 * R) = (1 : ℝ) / 4 := by
    field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
  -- (1) Thickness: `Ψ(T) ⊆ V`.
  have hth0 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (C0 * τ / (4 * R))
        (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact _root_.Tube.rescaleMap_image_subset_cthickening T₀ hR (r := C0 * τ)
      (A := T.carrier) (p := T.x) (q := T.y)
      (mul_nonneg hC0_nonneg hρ_nonneg) hcth
  have hrad : C0 * τ / (4 * R) ≤ (σ : ℝ) := by
    have h1 : C0 * τ ≤ R * τ := mul_le_mul_of_nonneg_right hC0_le_R hρ_nonneg
    have h2 : C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt h4Rpos)
    have h3 : (R * τ) / (4 * R) = τ / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    have h4 : τ / 4 ≤ (σ : ℝ) := by
      have : τ ≤ 4 * (σ : ℝ) := by simpa [τ] using hρσ
      linarith
    calc
      C0 * τ / (4 * R) ≤ (R * τ) / (4 * R) := h2
      _ = τ / 4 := h3
      _ ≤ (σ : ℝ) := h4
  have hth1 : T₀.rescaleMap R '' T.carrier ⊆
      Metric.cthickening (σ : ℝ) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact hth0.trans (Metric.cthickening_mono hrad
      (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)))
  have hlen1 : dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 := by
    calc
      dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)
          = dist (T₀.normalization T.x) (T₀.normalization T.y) / (4 * R) := by
            simpa [τ, C0] using _root_.Tube.dist_rescaleMap T₀ hR T.x T.y
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hlen (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
      _ ≤ 1 := by norm_num
  have hth2 : T₀.rescaleMap R '' T.carrier ⊆ (_root_.Tube.centredExtension σ hxy).carrier := by
    exact hth1.trans (_root_.Tube.cthickening_subset_centredExtension hxy hlen1)
  -- (2) Position: `V ⊆ B̄(0,1)`.
  have hpx : dist (T₀.normalization T.x) T₀.x ≤ R := by
    have hmem : T₀.normalization T.x ∈ T₀.normalization '' T.carrier :=
      ⟨T.x, _root_.Tube.x_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpy : dist (T₀.normalization T.y) T₀.x ≤ R := by
    have hmem : T₀.normalization T.y ∈ T₀.normalization '' T.carrier :=
      ⟨T.y, _root_.Tube.y_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpx0 : dist (T₀.rescaleMap R T.x) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.x) (0 : E)
          = dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.x) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.x T₀.x
      _ = dist (T₀.normalization T.x) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpx (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpy0 : dist (T₀.rescaleMap R T.y) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.y) (0 : E)
          = dist (T₀.rescaleMap R T.y) (T₀.rescaleMap R T₀.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.y) (T₀.normalization T₀.x) / (4 * R) :=
            _root_.Tube.dist_rescaleMap T₀ hR T.y T₀.x
      _ = dist (T₀.normalization T.y) T₀.x / (4 * R) := by rw [_root_.Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpy (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpos : (_root_.Tube.centredExtension σ hxy).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    exact _root_.Tube.centredExtension_subset_closedBall hxy hpx0 hpy0 hsit.out_le_quarter
  -- (3) Volume: `|V| ≤ (4R)^6 |W|`.
  have hvol0 : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal
            ((_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3)
          * volume (T₀.rescaleMap R '' T.carrier) := by
    simpa [hn] using _root_.Tube.volume_centredExtension_le_mul_volume_rescale_image
      (n := 3) hsit hR T₀ T hxy
  have hC64R : (64 : ℝ) ≤ R := by
    have hC : (64 : ℝ) ≤ (_root_.Tube.normalization.C 3 : ℝ) := by
      norm_num [_root_.Tube.normalization.C]
    exact le_trans hC hsit.normalizationConst_le_radius
  have hbig : (256 : ℝ) ≤ 4 * R := by linarith
  have hpow256 : (256 : ℝ) ^ 3 ≤ (4 * R) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) hbig 3
  have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by nlinarith
  have hcoef : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
      ≤ (4 * R) ^ 6 := by
    have hvp12 : (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) ≤ 12 :=
      _root_.Tube.volume_ratio_three_le_twelve
    calc
      (_root_.Tube.volume_le.C 3 : ℝ) / (_root_.Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
          ≤ 12 * (4 * R) ^ 3 := by gcongr
      _ ≤ (4 * R) ^ 3 * (4 * R) ^ 3 := by gcongr
      _ = (4 * R) ^ 6 := by ring
  have hvol : volume (_root_.Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
    exact hvol0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
  exact ⟨hth2, hpos, hvol⟩

/-- **The selection constant of the downstairs route is dominated by the normalization loss, at a
free normalized radius `R` and a free tilt `κ`.**

`Kakeya.ml1Boot.fineNormalize_C_dominates` is the same statement hardwired to the undilated
instance `(R, κ) = (C_N, 2)`, and the dilated half of the normalization runs at
`(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))`, so it needs the parametric form.  The coupling
hypothesis `κ + 2 ≤ R` holds at both instances — `4 ≤ 64` and `2 c + 4 ≤ 64 + 128 c` — and is
what keeps the selection ratio `4 (κ + 2) R C_n` below `4 R² C_n`.

The third clause carries a factor `125` that the undilated form does not.  It is the price of
descending the ambient volume comparison from `c · T_τ` to the sub-body `K`: the `c`-dilate has
volume `c³ |T_τ|`, and `c ≥ 1/5` — forced, not assumed, since a `δ`-tube fits inside `c · T_τ`
only if `1 ≤ c + 4 c τ` (`Kakeya.ml1Boot.volume_ambient_le_mul_volume_dilate`) — bounds `c⁻³` by
`125`.  There is room for it: the comparison reduces to `125 ≤ 4 ^ 24 R ^ 12`. -/
private lemma fineNormalize_C_dominates_gen {R κ c₁ : NNReal}
    (hCR : _root_.Tube.normalization.C 3 ≤ R) (hκR : κ + 2 ≤ R)
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C R κ ∧
      ((4 * R) ^ 6 : NNReal) * c₁ ≤ fineNormalize.C R κ ∧
      (125 : NNReal) * ((4 * R) ^ 12 : NNReal) * c₁ ≤ fineNormalize.C R κ := by
  let ratio : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  let D : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C 3).toNNReal
  let u : NNReal := 4 * (κ + 2) * R * D
  have hR1 : (1 : NNReal) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hCR
  have hκ1 : (1 : NNReal) ≤ κ + 2 := by
    exact le_trans (by norm_num : (1 : NNReal) ≤ 2)
      (le_add_of_nonneg_left (by positivity : (0 : NNReal) ≤ κ))
  have hD0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans (by norm_num : (0 : ℝ) < (1 : ℝ))
      (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hD1 : (1 : NNReal) ≤ D := by
    dsimp [D]; rw [← NNReal.coe_le_coe, Real.toNNReal_of_nonneg hD0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hratio0 : (0 : ℝ) ≤ ratio := by
    dsimp [ratio]
    positivity
  have hu_re : ratio = (u : ℝ) := by
    dsimp [u, ratio, D]
    norm_num
    exact Or.inl hD0
  have hu : ratio.toNNReal = u := by
    apply NNReal.coe_injective
    rw [Real.toNNReal_of_nonneg hratio0]
    exact hu_re
  have hu1 : (1 : NNReal) ≤ u :=
    one_le_mul (one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hκ1) hR1) hD1
  have hu6 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu1 (by norm_num)
  have hule : u ≤ 4 * R ^ 2 * D := by
    dsimp [u]
    calc
      4 * (κ + 2) * R * D
          ≤ 4 * R * R * D := by
            exact mul_le_mul
              (mul_le_mul (mul_le_mul le_rfl hκR (by positivity) (by positivity))
                le_rfl (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = 4 * R ^ 2 * D := by ring
  have hu12' : 125 * u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    calc
      125 * u ^ 12 ≤ 125 * (4 * R ^ 2 * D) ^ 12 := by
            exact mul_le_mul le_rfl (pow_le_pow_left₀ (by positivity : (0 : NNReal) ≤ u) hule 12)
              (by positivity) (by positivity)
      _ = 125 * 4 ^ 12 * R ^ 24 * D ^ 12 := by
            ring_nf
      _ ≤ (4 : NNReal) ^ 36 * R ^ 36 * D ^ 12 := by
            exact mul_le_mul
              (mul_le_mul (by norm_num : (125 * 4 ^ 12 : NNReal) ≤ 4 ^ 36)
                (pow_le_pow_right₀ hR1 (by norm_num)) (by positivity) (by positivity))
              le_rfl (by positivity) (by positivity)
      _ = ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
            ring_nf
  have hu12 : u ^ 12 ≤ ((4 * R) ^ 6) ^ 6 * D ^ 12 := by
    exact le_trans
      (le_mul_of_one_le_left (by positivity) (by norm_num : (1 : NNReal) ≤ 125))
      hu12'
  have hbase : (1 : NNReal) ≤ 4 * R := one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hR1
  have hpw6 : (4 * R) ^ 6 ≤ (4 * R) ^ 12 := pow_le_pow_right₀ hbase (by norm_num)
  have hkey : c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : NNReal :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : NNReal)) ^ (2 * 3 - 1) with hA
    set B : NNReal := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3)
          = A * u ^ 6 + B * u ^ 12 := by rw [hu]
      _ ≤ A * u ^ 12 + B * u ^ 12 := by
            exact add_le_add (mul_le_mul le_rfl hu6 (by positivity) (by positivity)) le_rfl
      _ = (A + B) * u ^ 12 := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12 (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  have hkey125 : 125 * c₁ ≤ _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
    rw [hc₁]
    unfold _root_.Tube.essDistinctTubesInSelfDilate.C
      _root_.Tube.essDistinctTubesInSelfDilate.thinC
      _root_.Tube.essDistinctTubesInSelfDilate.fatC
      _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
    set A : NNReal :=
      24 * (2 ^ (3 - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (3 - 1)) ^ 2
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * 3 - 1))⁻¹
        * (32 * (3 : NNReal)) ^ (2 * 3 - 1) with hA
    set B : NNReal := 6 ^ (2 * 3) * (Tube.card_le_of_EssDistinct.C 3).toNNReal with hB
    calc
      125 * (A * ratio.toNNReal ^ (2 * 3) + B * ratio.toNNReal ^ (4 * 3))
          = 125 * (A * u ^ 6 + B * u ^ 12) := by rw [hu]
      _ = 125 * (A * u ^ 6) + 125 * (B * u ^ 12) := by ring
      _ ≤ 125 * (A * u ^ 12) + 125 * (B * u ^ 12) := by
            exact add_le_add
              (mul_le_mul le_rfl (mul_le_mul le_rfl hu6 (by positivity) (by positivity))
                (by positivity) (by positivity))
              le_rfl
      _ = 125 * (A + B) * u ^ 12 := by ring
      _ = (A + B) * (125 * u ^ 12) := by ring
      _ ≤ (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := by
            exact mul_le_mul le_rfl hu12' (by positivity) (by positivity)
      _ ≤ 1 + (A + B) * (((4 * R) ^ 6) ^ 6 * D ^ 12) := le_add_self
      _ = _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            rw [hA, hB]
            unfold _root_.Tube.comparableReplacement.C _root_.Tube.comparableReplacement.Kstar
            norm_num
            ring
  constructor
  · unfold fineNormalize.C
    rw [hc₁]
    exact le_add_self
  constructor
  · unfold fineNormalize.C
    exact le_trans
      (le_trans (mul_le_mul hpw6 le_rfl (by positivity) (by positivity))
        (mul_le_mul le_rfl hkey (by positivity) (by positivity)))
      le_self_add
  · unfold fineNormalize.C
    calc
      (125 : NNReal) * ((4 * R) ^ 12 : NNReal) * c₁
          = (4 * R) ^ 12 * (125 * c₁) := by ring
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6) := by
            exact mul_le_mul le_rfl hkey125 (by positivity) (by positivity)
      _ ≤ (4 * R) ^ 12 * _root_.Tube.comparableReplacement.C 3 ((4 * R) ^ 6)
            + _root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) :=
            le_self_add

/-- **Normalizing a fine fibre to the unit ball, over an arbitrary ambient body** (blueprint
`lem:ml1bootFineNormalizeCore`).

This is the route shared by the two halves of the fine normalization, with the ambient body `P`
and the normalized ambient radius `R` left free.  Both halves are this lemma instantiated:
`Kakeya.ml1Boot.exists_fineNormalization` at `(P, R, κ) = (T_τ, C_N, 2)`, and
`Kakeya.ml1Boot.exists_fineNormalization_dilate` at
`(P, R, κ) = (K, (1 + 2 c) C_N, max 2 (2 c))` — see the "Not a corollary of the undilated half"
note at the latter for why neither is derivable from the other.

Everything the route needs from the ambient body is isolated into four hypotheses, and nothing
else here mentions `P`:

* `hsub`, the members sit in `P`;
* `hball`, the normalization `Φ_{T_τ}` carries `P` into `B̄(T_τ.x, R)` — this is what fixes `R`,
  and it is the *only* place the shape of `P` enters the geometry;
* `hlen`, each image core has length at most `R` — the relaxed form of
  `Tube.IsNormalizationDistortion.dist_le_C` discussed at
  `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le`;
* `hperp`, each member is tilted against the axis of `T_τ` by at most `κ τ`.

The remaining two, `hPvol` and `hratio`, are the ambient enlargement to `B₁`: `Cw` is the loss
of replacing the ambient body by the unit ball, and it is the *only* route by which a
volume-ratio parameter such as the `M` of the dilated half can reach the Frostman clause.  The
constants are returned raw — the selection constant `C₁`, the comparability constant `(4 R) ^ 6`
and `Cw`, in the combinations the four clauses actually pay — so that each instance does its own
domination against `Kakeya.ml1Boot.fineNormalize.C R κ`.

The output scale is `Kakeya.ml1Boot.fineScale δ τ` and not the bare ratio `δ / τ`; with `δ / τ`
this statement is false at both instances, refuted by
`Kakeya.ml1Boot.not_exists_fineNormalization` and
`Kakeya.ml1Boot.not_exists_fineNormalization_dilate`.

## The construction-visibility clauses

The last four clauses of the conclusion are not part of the blueprint lemma.  They expose the
data the route already builds, so that a consumer can see *which* family `V` is rather than only
that one exists.  Writing `Ψ = Tube.rescaleMap T_τ R` for the normalization-and-homothety of the
proof, they say that the intermediate family — the `Ψ`-image of the input — sits inside the
output with the same shade and comparable volume, and that `Ψ` carries the ambient body into
`B(0, 1/4)`:

* `Ψ(T i) ⊆ V i` for every `i ∈ u`;
* `(V i).shade = Ψ((T i).shade)` for every `i ∈ u`;
* `|V i| ≤ (4 R) ^ 6 |Ψ(T i)|` for every `i ∈ u`;
* `Ψ(P) ⊆ B(0, 1/4)`.

They cost nothing: they are the local hypotheses `hsub'`, `hshade`, `hvol` and `hK'c` that the
selection package `Tube.exists_comparableReplacement_affine` is fed with anyway, restated
through `hWcarrier` in terms of `Ψ` rather than of the local abbreviation `𝕎`.

What the proof does **not** have, and so what is deliberately absent here, is the `hdilate`
clause of `ConvexSpaceBody.frostmanConstIn_ge_of_comparable` — for every `K' ≤ K` a `L ≤ K`
with `K' ≤ L`, `|L| ≤ C |K'|` and `V i ≤ L` whenever `Ψ(T i) ≤ K'`.  `Tube.exists_comparableReplacement_affine`
never forms such an `L`; its Frostman item is the one-sided
`Tube.comparableTransport_oneSided`, which needs only `Ψ(T i) ⊆ V i ⊆ K` and the volume
bracket.  Also absent is any clause about indices outside `u`: `hsub`, `hlen` and `hperp` are
hypothesised on `u` alone, so nothing at all is known about `V i` for `i ∉ u`, even though `V`
is a total function. -/
theorem exists_fineNormalization_core [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {μ₀ : ENNReal} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (P : ConvexSpaceBody E) {R κ Cw : NNReal}
    (hR : _root_.Tube.normalization.C 3 ≤ R)
    (hu : u.Nonempty)
    (hsub : ∀ i ∈ u, (T i).carrier ⊆ P.carrier)
    (hball : Tτ.normalization '' P.carrier ⊆ Metric.closedBall Tτ.x (R : ℝ))
    (hlen : ∀ i ∈ u,
      dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ (R : ℝ))
    (hperp : ∀ i ∈ u, ‖(T i).toTube.direction
        - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ (κ : ℝ) * (τ : ℝ))
    (hPvol : volume P.carrier ≠ 0)
    (hratio : volume (Metric.closedBall (0 : E) 1)
      ≤ (Cw : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' P.carrier))
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * ((κ : ℝ) + 2) * (R : ℝ)
                * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ENNReal)
            * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          ≤ (((4 * R) ^ 6 : NNReal) : ENNReal)
            * (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ENNReal)
            * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * ((κ : ℝ) + 2) * (R : ℝ)
                  * Kakeya.Tube.tubeOverlapCoreClose.C 3) : ENNReal)
            * (((4 * R) ^ 6 : NNReal) : ENNReal) * (Cw : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P ∧
        -- the construction-visibility clauses: `V` is comparable to the image of `T` under the
        -- explicit rescaling map `Ψ = Tube.rescaleMap Tτ R`
        (∀ i ∈ u, Tτ.rescaleMap (R : ℝ) '' (T i).carrier ⊆ (V i).carrier) ∧
        (∀ i ∈ u, (V i).shade = Tτ.rescaleMap (R : ℝ) '' (T i).shade) ∧
        (∀ i ∈ u, volume (V i).carrier
          ≤ (((4 * R) ^ 6 : NNReal) : ENNReal)
            * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier)) ∧
        Tτ.rescaleMap (R : ℝ) '' P.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  have hδτ0 : 0 < (δ / τ : NNReal) := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ0)
  have hpos : 0 < fineScale δ τ := by
    dsimp [fineScale]
    exact lt_min hδτ0 (by norm_num)
  have hquarter : (fineScale δ τ : ℝ) ≤ 1 / 4 := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.1
  have hratioσ : (fineScale δ τ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).1
  have hρσ : (δ : ℝ) / (τ : ℝ) ≤ 4 * (fineScale δ τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.2
  have hR1n : (1 : NNReal) ≤ R := le_trans (_root_.Tube.normalization.one_le_C 3) hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1n
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR1
  have hsit : _root_.Tube.IsRescalingSituation τ δ (fineScale δ τ) (R : ℝ) 3 :=
    ⟨hτ0, hδτ, hτ1, hpos, hquarter, hratioσ, by exact_mod_cast hR⟩
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  have hxy : ∀ i : ι, Tτ.rescaleMap (R : ℝ) (T i).x ≠ Tτ.rescaleMap (R : ℝ) (T i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy => by
      have := (T i).toTube.dist_eq_one
      rw [hxy] at this
      simp at this)
  set 𝕎 : ι → ShadedBody E := fun i => ((T i).toShadedBody).affineImage L.toAffineMap hcont hemb
  set 𝕍 : ι → ShadedTube (fineScale δ τ) E := fun i =>
    { toTube := _root_.Tube.centredExtension (fineScale δ τ) (hxy i)
      shade := (𝕎 i).shade ∩ (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier
      measurableSet_shade :=
        (𝕎 i).measurableSet_shade.inter
          (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hballi : ∀ i ∈ u, Tτ.normalization '' (T i).carrier ⊆ Metric.closedBall Tτ.x (R : ℝ) := by
    intro i hi
    exact (Set.image_mono (hsub i hi)).trans hball
  have houter := fun i hi => rescale_outer_tube_of_dist_le
    (hsit := hsit) (hn := hdim) (hR := hR0) (hρσ := hρσ) (T₀ := Tτ)
    (T := (T i).toTube)
    (hcth := _root_.Tube.normalization_image_subset_cthickening hτ0 hτ1 Tτ (T i).toTube)
    (hlen := hlen i hi) (hball := hballi i hi) (hxy := hxy i)
  have hofR : ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (((4 * R) ^ 6 : NNReal) : ENNReal) := by
    have h4R : ENNReal.ofReal (4 * (R : ℝ)) = ((4 * R : NNReal) : ENNReal) := by
      rw [show (4 : ℝ) * (R : ℝ) = ((4 * R : NNReal) : ℝ) by
        rw [NNReal.coe_mul]
        norm_num]
      rw [ENNReal.ofReal_coe_nnreal]
    have hRnonneg : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
    calc
      ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (ENNReal.ofReal (4 * (R : ℝ))) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * R : NNReal) : ENNReal) ^ 6 := by rw [h4R]
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) := by
            rw [ENNReal.coe_pow]
  have hWcarrier : ∀ i ∈ u, (𝕎 i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier := by
    intro i hi
    dsimp [𝕎]
    change L.toAffineMap '' (T i).carrier = Tτ.rescaleMap (R : ℝ) '' (T i).carrier
    rw [← hL]
  have hsub' : ∀ i ∈ u, (𝕎 i).carrier ⊆ (𝕍 i).carrier := by
    intro i hi
    rw [hWcarrier i hi]
    simpa [𝕍] using (houter i hi).1
  have h𝕍ball : ∀ i ∈ u, (𝕍 i).toTube.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    simpa [𝕍] using (houter i hi).2.1
  have hshade : ∀ i ∈ u, (𝕍 i).shade = (𝕎 i).shade := by
    intro i hi
    dsimp [𝕍]
    exact (Set.inter_eq_left).mpr ((𝕎 i).shade_subset.trans (hsub' i hi))
  have hCv : 1 ≤ (4 * R) ^ 6 := by
    exact one_le_pow₀ (one_le_mul (by norm_num) hR1n)
  have hVK : ∀ i ∈ u,
      (𝕍 i).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    change (𝕍 i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    simpa [𝕍] using h𝕍ball i hi
  let c' : ℝ := 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hc'1 : (1 : ℝ) ≤ c' := by
    dsimp [c']
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) := NNReal.coe_nonneg κ
    have hRgr : (1 : ℝ) ≤ (R : ℝ) := hR1
    have hCnR : (1 : ℝ) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 : ℝ) := by
      exact_mod_cast (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
    have hk : (1 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := by
      nlinarith
    have hk0 : (0 : ℝ) ≤ 4 * ((κ : ℝ) + 2) := le_trans zero_le_one hk
    have hb1 : (1 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
              exact mul_le_mul hRgr hCnR (by norm_num) (by positivity)
    have hb10 : (0 : ℝ) ≤ (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := le_trans zero_le_one hb1
    calc
      1 ≤ 1 * 1 := by norm_num
      _ ≤ (4 * ((κ : ℝ) + 2)) * ((R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
            exact mul_le_mul hk hb1 (by positivity) hk0
      _ = 4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by ring
  let c₁ : NNReal := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  have hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((κ : ℝ) + 2) * (R : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
    rfl
  have hC₁ : (1 : NNReal) ≤ c₁ := by
    let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
    have hpw₀ : (({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι), (𝕋 j).carrier
        ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact _root_.Tube.subset_dilate (𝕋 i₀) hc'1
    have hcount : (({i₀} : Finset ι).card : ENNReal)
        ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ENNReal) :=
      _root_.Tube.essDistinctTubesInSelfDilate hc'1 hδ (le_trans hδτ hτ1 : δ ≤ 1) (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa [c₁, c', hdim] using hcount)
  have hVtube : ∀ i ∈ u, (𝕍 i).toTube = _root_.Tube.centredExtension (fineScale δ τ) (hxy i) := by
    intro i hi
    rfl
  have hvol : ∀ i ∈ u, volume (𝕍 i).carrier
      ≤ (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
    intro i hi
    calc
      volume (𝕍 i).carrier
          = volume (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier := by
            simp [𝕍]
      _ ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) :=
            (houter i hi).2.2
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' (T i).carrier) := by
            rw [hofR]
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
            rw [hWcarrier i hi]
  let W : ENNReal := volume (𝕎 i₀).carrier
  have hW : 0 < W := by
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_pos hδ (T i₀) L hcont hemb
  have hcommon : ∀ i ∈ u, volume (𝕎 i).carrier = W := by
    intro i hi
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_eq (T i) (T i₀) L hcont hemb
  have hZ : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ENNReal) * μ₀ * W := by
    intro i hi
    have hz := affineImage_shade_bounds (S := T i) (S' := T i₀) L hcont hemb
      (hdens i hi).1 (hdens i hi).2
    dsimp [W, 𝕎] at hz ⊢
    exact hz
  let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
  have himg : ∀ i ∈ u, (Tτ.rescaleMap (R : ℝ)) '' (T i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    simpa [𝕍] using (houter i hi).1
  have hpackage : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) ((4 * R) ^ 6) Λ c₁ := by
    simpa [hc₁, hdim] using
      (_root_.Tube.exists_comparableReplacement_affine (n := 3) (R := (R : ℝ))
      (κ := ((κ : NNReal) : ℝ)) (s := u) hu hsit (by exact NNReal.coe_nonneg κ)
      hδ (le_trans hδτ hτ1 : δ ≤ 1) Tτ
      𝕋 hxy 𝕎 𝕍
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (C := (4 * R) ^ 6) (Λ := Λ)
      (W := W) (μ₀ := μ₀) hCv hΛ hW hμ₀ hcommon hVtube hperp
      (by simpa [𝕋] using hED) himg hshade hsub' hVK hvol hZ)
  let K' : ConvexSpaceBody E := (P).affineImage L.toAffineMap hcont
  have hK'c : K'.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
    rintro _ ⟨z, hzP, rfl⟩
    have hz : Tτ.normalization z ∈ Metric.closedBall Tτ.x (R : ℝ) := by
      exact (hball ⟨z, hzP, rfl⟩)
    have hdistz : dist (Tτ.normalization z) Tτ.x ≤ (R : ℝ) := Metric.mem_closedBall.mp hz
    have h4Rpos : (0 : ℝ) < 4 * (R : ℝ) := by positivity
    have h4R0 : (4 : ℝ) * (R : ℝ) ≠ 0 := ne_of_gt h4Rpos
    have hRdiv : (R : ℝ) / (4 * (R : ℝ)) = (1 : ℝ) / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    rw [hL]
    calc
      dist (Tτ.rescaleMap (R : ℝ) z) (0 : E)
          = dist (Tτ.rescaleMap (R : ℝ) z) (Tτ.rescaleMap (R : ℝ) Tτ.x) := by
            rw [← _root_.Tube.rescaleMap_apply_x]
        _ = dist (Tτ.normalization z) (Tτ.normalization Tτ.x) / (4 * (R : ℝ)) :=
            _root_.Tube.dist_rescaleMap Tτ hR0 z Tτ.x
        _ = dist (Tτ.normalization z) Tτ.x / (4 * (R : ℝ)) := by
            rw [_root_.Tube.normalization_apply_x]
        _ ≤ (R : ℝ) / (4 * (R : ℝ)) := div_le_div_of_nonneg_right hdistz (le_of_lt h4Rpos)
        _ = (1 : ℝ) / 4 := hRdiv
        _ ≤ 1 / 4 := le_rfl
  have hK' : (K' : ConvexSpaceBody E) ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    change K'.carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hK'c.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    have h1 : volume ((P).affineImage L.toAffineMap hcont).carrier ≠ 0 := by
      rw [ConvexSpaceBody.volume_affineImage]
      have hA : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
        exact (ENNReal.ofReal_eq_zero.not).mpr
          (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
      have hB : volume P.carrier ≠ 0 := hPvol
      exact mul_ne_zero hA hB
    simpa [K'] using h1
  have hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K' := by
    intro i hi
    change (𝕎 i).carrier ⊆ K'.carrier
    rw [hWcarrier i hi]
    rw [← hL]
    exact Set.image_mono (hsub i hi)
  have hratio' : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (Cw : ENNReal) * volume K'.carrier := by
    simpa [K', ← hL, ConvexSpaceBody.closedUnitBall_carrier] using hratio
  have hfrodsman : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (Cw : ENNReal) * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' :=
    frostmanConstIn_closedUnitBall_le_of_ambient (u := u) (𝕎 := 𝕎) (K' := K')
      (Cv := Cw) hK' hK'vol hWK' hratio'
  have hF_rel : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K'
      = frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage u (fun i => (T i).toConvexSpaceBody)
      P L hcont
    dsimp [𝕎, K']
    exact h
  obtain ⟨u', hu'sub, hu'ne, hVD, hmult, hfull, hfrost⟩ :=
    of_comparableReplacementFree (u := u) (𝕎 := 𝕎) (𝕍 := 𝕍)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (Cv := (4 * R) ^ 6)
      (Λ := Λ) (C₁ := c₁) hΛ hCv hC₁ hVK hpackage
  refine ⟨u', hu'sub, hu'ne, 𝕍, ?_⟩
  constructor
  · simpa [𝕍] using hVD
  constructor
  · intro i hi
    simpa [𝕍] using h𝕍ball i (hu'sub hi)
  constructor
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          = ShadedBody.multiplicity u 𝕎 := by
            simpa [𝕎] using (ShadedBody.multiplicity_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := hmult
  constructor
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          = (ShadedBody.fullness u 𝕎 : ENNReal) := by
            simpa [𝕎] using (ShadedBody.fullness_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (((4 * R) ^ 6 : NNReal) : ENNReal) * (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := hfull
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
            ≤ (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
                  (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by simpa using hfrost
        _ ≤ (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal)
            * ((Cw : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K') := by
              exact mul_le_mul_right hfrodsman ((c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal))
        _ = (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal)
            * ((Cw : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P) := by
              rw [hF_rel]
        _ = (c₁ : ENNReal) * (((4 * R) ^ 6 : NNReal) : ENNReal) * (Cw : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) P := by ring
    · intro i hi
      rw [← hWcarrier i hi]
      exact hsub' i hi
    · intro i hi
      rw [hshade i hi]
      simp [𝕎, ← hL]
    · intro i hi
      simpa [hWcarrier i hi] using hvol i hi
    · simpa [K', ← hL] using hK'c

/-- **Normalizing the fine fibre to the unit ball** (blueprint `lem:ml1bootFineNormalize`).

Let `C = Kakeya.ml1Boot.fineNormalize.C C_N` be the normalization loss proper, `C_N` being
`Tube.normalization.C 3`, and let `0 < δ ≤ τ ≤ 1`.  Note that this is *not*
`Kakeya.ml1Boot.fineFactor.C`, which is `16 C`: the factor `16` belongs to
`Kakeya.ml1Boot.fine_genKF` and is not spent here.

Let `T_τ` be a `τ`-tube in `B₁ ⊆ ℝ³`, let `𝕌 = (T i)_{i ∈ u}` be a nonempty family of pairwise
essentially distinct shaded `δ`-tubes with `T i ⊆ T_τ`, and suppose the shading densities are
two-sidedly comparable to `μ₀`, with constant `Λ ≥ 1`.  Then there are a nonempty `u' ⊆ u` and
a family `Ṽ` of shaded `Kakeya.ml1Boot.fineScale δ τ`-tubes contained in `B₁` such that

* the tubes `(Ṽ i)_{i ∈ u'}` are pairwise essentially distinct;
* `μ(𝕌, Y) ≤ C Λ² μ(Ṽ, Z̃)`;
* `λ(𝕌, Y) ≤ C Λ² λ(Ṽ, Z̃)`, the blueprint's `λ(Ṽ, Z̃) ≥ (C Λ²)⁻¹ λ(𝕌, Y)`;
* `C_F(Ṽ, B₁) ≤ C · C_F(𝕌, T_τ)`.

Four further clauses, not in the blueprint lemma, expose the construction: writing
`Ψ = Tube.rescaleMap T_τ C_N`, they record `Ψ(T i) ⊆ Ṽ i`, `(Ṽ i).shade = Ψ((T i).shade)` and
`|Ṽ i| ≤ (4 C_N) ^ 6 |Ψ(T i)|` for `i ∈ un`, and `Ψ(T_τ) ⊆ B(0, 1/4)`.  See the same section of
`Kakeya.ml1Boot.exists_fineNormalization_core` for what they are for and, more importantly,
for the one thing they are *not*: there is no `hdilate` clause.

*The ambient index set `un`.*  The containment hypothesis is read at a second index set
`un ⊇ u`, and the four construction-visibility clauses are quantified over `un` rather than over
`u`, while essential distinctness, the density bracket and the multiplicity, fullness and
Frostman items stay on `u` and its refinement `u'`.  This costs nothing: the output family
`Ṽ` is the same total function either way — each `Ṽ i` is the centred extension of the
`Ψ`-image of the core of `T i`, which is defined for every `i : ι` — and the three pointwise
clauses need only the containment `T i ⊆ T_τ` and the resulting length bound, both of which
`hsubn` supplies on all of `un`.  The tilt bound, essential distinctness and the density
bracket are genuinely available on `u` alone and are used only there, inside the selection
package.  Taking `un = u` recovers the previous reading verbatim.

The point of the wider quantifier is that a consumer reading a Frostman constant at a family
indexed by an ambient set — `Kakeya.ml1Boot.exists_fineNormalization_lower`, whose item (iv)
reads `familyIn un Ṽ (2 · T_ρ)` — depends on `Ṽ i` for every `i ∈ un`, and `Ṽ` is a total
function that would otherwise be completely unconstrained off `u`.

## The output scale, and what was wrong with the earlier form

The output scale is `fineScale δ τ = min (δ/τ) (1/4)`, not the bare ratio `δ / τ`.  With
`δ / τ` the statement is **false**: the hypotheses permit `δ = τ`, and then it asks for a
nonempty family of `1`-tubes inside `B₁`, which
`Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt` rules out — that is
`Kakeya.ml1Boot.not_exists_fineNormalization`, which refutes the earlier form of this lemma
and is retained above as a record.  Truncating at `1/4` is what removes the obstruction, and
it changes nothing where the earlier form was sound: `fineScale δ τ = δ / τ` as soon as
`δ / τ ≤ 1/4`.  No hypothesis bounding `δ / τ` is added, and none is available: see
`Kakeya.ml1Boot.fineScale` and blueprint `note:ml1bootFineNormalizeScaleObstruction`.

The consumers are insensitive to the truncation because
`(δ/τ)/4 ≤ fineScale δ τ ≤ δ / τ` — the first and third clauses of the conjunction
`Kakeya.ml1Boot.fineScale_bounds` — so the fine-factor bracket changes by at most a factor
`16` (`Kakeya.ml1Boot.fineScale_bracket_le`).  That factor is paid out of the *constant*,
`Kakeya.ml1Boot.fineFactor.C = 16 * Kakeya.ml1Boot.fineNormalize.C C_N`, and is spent exactly
once, in `Kakeya.ml1Boot.fine_genKF`.  It is **not** absorbed into the subpolynomial loss:
that route is unsound in this development, for the reason recorded in blueprint
`note:ml1bootFineScaleWhyConstant`.

## Proof status

**Proved**, and `#print axioms` now gives `[propext, Classical.choice, Quot.sound]`: no
`sorryAx`.  An earlier revision of this paragraph recorded one, entering through
`Tube.exists_comparableReplacement_affine` at the private thin-regime packing count
`Tube.essDistinctTubesInSelfDilate.thin_bound` of `Kakeya/Tube/Rescale.lean`; `thin_bound` has
since been closed, so the debt is discharged rather than outstanding.

The route is the blueprint's — normalize by `Φ_{T_τ}`, apply the homothety `z ↦ z / (4 C_N)`,
replace each image by an honest `fineScale δ τ`-tube, and select an essentially distinct
subfamily — with the homothety ratio raised from `C_N` to `4 C_N` and the constant
`Kakeya.ml1Boot.fineNormalize.C` (not the `16`-times-larger `Kakeya.ml1Boot.fineFactor.C`)
enlarged accordingly.

The selection package it runs on is `Tube.exists_comparableReplacement_affine`
(blueprint `lem:comparableAffineImagesToTubes`), which makes the selection *downstairs* on the
honest `τ`-tubes and counts with `Tube.card_le_mul_card_of_dilateCover_affine`
(blueprint `lem:comparableAffineFibreBound`); the pullback of a dilate is placed inside a
dilate of `T i` of ratio `4 (κ + 2) R C_n` by `Tube.preimage_rescale_dilate_subset_dilate`,
and essential distinctness transfers both ways along the affine equivalence by
`isEssentiallyDistinct_affineImage_iff`.

## How the `7/8` deficit was avoided rather than defeated

Earlier revisions of this docstring recorded two obligations as blocking, both real at the
time: `Tube.normalization_distortion` delivers a sub-segment of length only `7/8` (the trimmed
core has length exactly `1 - 2 C_N⁻¹ ρ`, and **unit length is false** — blueprint
`note:tubeNormalizationNotTubes`), so an honest `Kakeya.Tube`, which needs a core of length
exactly `1`, cannot be fitted by `Tube.exists_comparableReplacement`.

That deficit is not repaired; it is *bypassed*.  The volume comparison the route actually needs
is `Tube.volume_centredExtension_le_mul_volume_rescale_image`
(blueprint `lem:rescaleImageVolumeRatio`), and because the Jacobian of the normalization is
exact, `Tube.le_volume` applied to `T` itself supplies the lower bound with **no sub-segment
required**.  The `7/8` therefore never enters.  It still blocks any route that tries to produce
an honest unit-core tube *inside* a homothetic image, so the statement of
`note:tubeNormalizationNotTubes` stands unaltered.

The blueprint's item (i) also records `|u'| ≤ |u|`, which is `Finset.card_le_card` applied to
`u' ⊆ u` and is therefore not a clause of the conclusion here.  The two-sided density bound
is stated with the individual volumes `|T i|` in place of the common volume `|T|` of a
`δ`-tube: all `δ`-tubes are isometric, so the two readings agree. -/
theorem exists_fineNormalization (hdim : Module.finrank ℝ E = 3)
    {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {μ₀ : ENNReal} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u un : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (hu : u.Nonempty) (hun : u ⊆ un)
    (_hTτ : Tτ.carrier ⊆ Metric.closedBall 0 1)
    (hsubn : ∀ i ∈ un, (T i).carrier ⊆ Tτ.carrier)
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody)
                Tτ.toConvexSpaceBody ∧
        -- the construction-visibility clauses: `V` is comparable to the image of `T` under the
        -- explicit rescaling map `Ψ = Tube.rescaleMap Tτ C_N`, on all of the ambient set `un`
        (∀ i ∈ un, Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' (T i).carrier
          ⊆ (V i).carrier) ∧
        (∀ i ∈ un, (V i).shade
          = Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' (T i).shade) ∧
        (∀ i ∈ un, volume (V i).carrier
          ≤ (((4 * _root_.Tube.normalization.C 3) ^ 6 : NNReal) : ENNReal)
            * volume (Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
                '' (T i).carrier)) ∧
        Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) '' Tτ.carrier
          ⊆ Metric.closedBall (0 : E) (1 / 4) ∧
        -- the fifth construction-visibility clause: the core data of the output tube, read on
        -- the `Ψ`-images of the source core endpoints.  It is `rfl` in the construction.
        (∀ i ∈ un, (V i).toTube.center
              = midpoint ℝ (Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).x)
                  (Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).y) ∧
            (V i).toTube.direction
              = ‖Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).y
                  - Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).x‖⁻¹
                • (Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).y
                  - Tτ.rescaleMap ((_root_.Tube.normalization.C 3 : NNReal) : ℝ) (T i).x)) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  set Cn : NNReal := _root_.Tube.normalization.C 3 with hCn
  set R : ℝ := (Cn : ℝ) with hRdef
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  have hδτ0 : 0 < (δ / τ : NNReal) := by
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    exact div_pos (by exact_mod_cast hδ) (by exact_mod_cast hτ0)
  have hpos : 0 < fineScale δ τ := by
    dsimp [fineScale]
    exact lt_min hδτ0 (by norm_num)
  have hquarter : (fineScale δ τ : ℝ) ≤ 1 / 4 := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.1
  have hratioσ : (fineScale δ τ : ℝ) ≤ (δ : ℝ) / (τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).1
  have hρσ : (δ : ℝ) / (τ : ℝ) ≤ 4 * (fineScale δ τ : ℝ) := by
    exact_mod_cast (fineScale_bounds hδτ hτ0).2.2
  have hCn1 : 1 ≤ Cn := _root_.Tube.normalization.one_le_C 3
  have hR1 : (1 : ℝ) ≤ R := by
    dsimp [R]
    exact_mod_cast hCn1
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hsit : _root_.Tube.IsRescalingSituation τ δ (fineScale δ τ) R 3 :=
    ⟨hτ0, hδτ, hτ1, hpos, hquarter, hratioσ, le_rfl⟩
  obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  have hxy : ∀ i : ι, Tτ.rescaleMap R (T i).x ≠ Tτ.rescaleMap R (T i).y := by
    intro i h
    rw [← hL] at h
    exact (fun hne => hne (L.injective h)) (fun hxy => by
      have := (T i).toTube.dist_eq_one
      rw [hxy] at this
      simp at this)
  set 𝕎 : ι → ShadedBody E := fun i => ((T i).toShadedBody).affineImage L.toAffineMap hcont hemb
  set 𝕍 : ι → ShadedTube (fineScale δ τ) E := fun i =>
    { toTube := _root_.Tube.centredExtension (fineScale δ τ) (hxy i)
      shade := (𝕎 i).shade ∩ (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier
      measurableSet_shade :=
        (𝕎 i).measurableSet_shade.inter
          (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hdist : ∀ i ∈ un, _root_.Tube.IsNormalizationDistortion Tτ (T i).toTube := fun i hi =>
    _root_.Tube.normalization_distortion hτ0 hδτ hτ1 Tτ (T i).toTube (hsubn i hi)
  have hball0 : Tτ.normalization '' Tτ.carrier ⊆ Metric.closedBall Tτ.x R := by
    have h := _root_.Tube.normalization_image_ambient_subset_closedBall hτ0 hτ1 Tτ
    rw [hdim] at h
    simpa [R, hCn] using h
  have hball : ∀ i ∈ un, Tτ.normalization '' (T i).carrier ⊆ Metric.closedBall Tτ.x R := by
    intro i hi
    exact (Set.image_mono (hsubn i hi)).trans hball0
  have houter := fun i hi => _root_.Tube.rescale_outer_tube
    (hsit := hsit) (hn := hdim) (hR := hR0) (hρσ := hρσ) (T₀ := Tτ)
    (T := (T i).toTube) (hdist := hdist i hi) (hball := hball i hi) (hxy := hxy i)
  have hofR : ENNReal.ofReal ((4 * R) ^ 6) = (((4 * Cn) ^ 6 : NNReal) : ENNReal) := by
    have hRnonneg : (0 : ℝ) ≤ 4 * R := by positivity
    calc
      ENNReal.ofReal ((4 * R) ^ 6) = (ENNReal.ofReal (4 * R)) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * Cn : NNReal) : ENNReal) ^ 6 := by
            congr 1
            rw [← ENNReal.ofReal_coe_nnreal]
            congr 1
      _ = (((4 * Cn) ^ 6 : NNReal) : ENNReal) := by
            rw [ENNReal.coe_pow]
  have hWcarrier : ∀ i ∈ un, (𝕎 i).carrier = Tτ.rescaleMap R '' (T i).carrier := by
    intro i hi
    dsimp [𝕎]
    change L.toAffineMap '' (T i).carrier = Tτ.rescaleMap R '' (T i).carrier
    rw [← hL]
  have hsub' : ∀ i ∈ un, (𝕎 i).carrier ⊆ (𝕍 i).carrier := by
    intro i hi
    rw [hWcarrier i hi]
    simpa [𝕍] using (houter i hi).1
  have h𝕍ball : ∀ i ∈ u, (𝕍 i).toTube.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    simpa [𝕍] using (houter i (hun hi)).2.1
  have hshade : ∀ i ∈ un, (𝕍 i).shade = (𝕎 i).shade := by
    intro i hi
    dsimp [𝕍]
    exact (Set.inter_eq_left).mpr ((𝕎 i).shade_subset.trans (hsub' i hi))
  have hCv : 1 ≤ (4 * Cn) ^ 6 := by
    exact one_le_pow₀ (one_le_mul (by norm_num) hCn1)
  have hVK : ∀ i ∈ u,
      (𝕍 i).toConvexSpaceBody ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    change (𝕍 i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    simpa [𝕍] using h𝕍ball i hi
  let c' : ℝ := 4 * ((2 : ℝ) + 2) * R * Kakeya.Tube.tubeOverlapCoreClose.C 3
  have hc'1 : (1 : ℝ) ≤ c' := by
    dsimp [c']
    have hRgr : (1 : ℝ) ≤ R := hR1
    have hCnR : (1 : ℝ) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 : ℝ) := by
      exact_mod_cast (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
    nlinarith
  let c₁ : NNReal := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * ((2 : ℝ) + 2) * ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
      * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  have hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * ((2 : ℝ) + 2) * ((_root_.Tube.normalization.C 3 : NNReal) : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C 3) := by
    rfl
  have hC₁ : (1 : NNReal) ≤ c₁ := by
    let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
    have hpw₀ : (({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι), (𝕋 j).carrier
        ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact _root_.Tube.subset_dilate (𝕋 i₀) hc'1
    have hcount : (({i₀} : Finset ι).card : ENNReal)
        ≤ (_root_.Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ENNReal) :=
      _root_.Tube.essDistinctTubesInSelfDilate hc'1 hδ (le_trans hδτ hτ1 : δ ≤ 1) (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa [c₁, c', R, hCn, hdim] using hcount)
  have hperp : ∀ i ∈ u, ‖(T i).toTube.direction
      - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ (2 : ℝ) * (τ : ℝ) := fun i hi =>
    _root_.Tube.perp_norm_direction_le_of_subset Tτ (T i).toTube (hsubn i (hun hi))
  have hVtube : ∀ i ∈ u, (𝕍 i).toTube = _root_.Tube.centredExtension (fineScale δ τ) (hxy i) := by
    intro i hi
    rfl
  have hvol : ∀ i ∈ un, volume (𝕍 i).carrier
      ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
    intro i hi
    calc
      volume (𝕍 i).carrier
          = volume (_root_.Tube.centredExtension (fineScale δ τ) (hxy i)).carrier := by
            simp [𝕍]
      _ ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (Tτ.rescaleMap R '' (T i).carrier) :=
            (houter i hi).2.2
      _ = (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume (Tτ.rescaleMap R '' (T i).carrier) := by
            rw [hofR]
      _ = (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume (𝕎 i).carrier := by
            rw [hWcarrier i hi]
  let W : ENNReal := volume (𝕎 i₀).carrier
  have hW : 0 < W := by
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_pos hδ (T i₀) L hcont hemb
  have hcommon : ∀ i ∈ u, volume (𝕎 i).carrier = W := by
    intro i hi
    dsimp [W]
    simpa [𝕎] using volume_affineImage_carrier_eq (T i) (T i₀) L hcont hemb
  have hZ : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ENNReal) * μ₀ * W := by
    intro i hi
    have hz := affineImage_shade_bounds (S := T i) (S' := T i₀) L hcont hemb
      (hdens i hi).1 (hdens i hi).2
    dsimp [W, 𝕎] at hz ⊢
    exact hz
  let 𝕋 : ι → Tube δ E := fun i => (T i).toTube
  have himg : ∀ i ∈ u, (Tτ.rescaleMap R) '' (T i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    simpa [𝕍] using (houter i (hun hi)).1
  have hpackage : _root_.Tube.IsComparableReplacementFree u 𝕎 𝕍
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) ((4 * Cn) ^ 6) Λ c₁ := by
    simpa [hc₁, hdim, R, hCn] using
      (_root_.Tube.exists_comparableReplacement_affine (n := 3) (R := R)
      (κ := (2 : ℝ)) (s := u) hu hsit (by norm_num) hδ (le_trans hδτ hτ1 : δ ≤ 1) Tτ
      𝕋 hxy 𝕎 𝕍
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (C := (4 * Cn) ^ 6) (Λ := Λ)
      (W := W) (μ₀ := μ₀) hCv hΛ hW hμ₀ hcommon hVtube hperp
      (by simpa [𝕋] using hED) himg (fun i hi => hshade i (hun hi))
      (fun i hi => hsub' i (hun hi)) hVK (fun i hi => hvol i (hun hi)) hZ)
  let K' : ConvexSpaceBody E := (Tτ.toConvexSpaceBody).affineImage L.toAffineMap hcont
  have hK'c : K'.carrier ⊆ Metric.closedBall (0 : E) (1 / 4) := by
    have h := _root_.Tube.rescale_image_ambient_subset_closedBall hτ0 hτ1 hR0 (by
      dsimp [R]
      rw [hdim]
      rfl) Tτ
    simpa [K', ← hL] using h
  have hK' : (K' : ConvexSpaceBody E) ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    change K'.carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hK'c.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hK'vol : volume K'.carrier ≠ 0 := by
    have h1 : volume ((Tτ.toConvexSpaceBody).affineImage L.toAffineMap hcont).carrier ≠ 0 := by
      rw [ConvexSpaceBody.volume_affineImage]
      have hA : ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)| ≠ 0 := by
        exact (ENNReal.ofReal_eq_zero.not).mpr
          (not_le.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.linear).ne_zero))
      have hB : volume (Tτ.toConvexSpaceBody).carrier ≠ 0 := by
        have hle : (_root_.Tube.le_volume.c 3 : ENNReal) * (τ : ENNReal) ^ 2
            ≤ volume (Tτ.toConvexSpaceBody).carrier := by
          simpa [hdim] using _root_.Tube.le_volume Tτ
        have hpos : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) * (τ : ENNReal) ^ 2 := by
          exact_mod_cast (mul_pos (_root_.Tube.le_volume.c_pos 3) (pow_pos hτ0 2))
        exact ne_of_gt (lt_of_lt_of_le hpos hle)
      exact mul_ne_zero hA hB
    simpa [K'] using h1
  have hWK' : ∀ i ∈ u, (𝕎 i).toConvexSpaceBody ≤ K' := by
    intro i hi
    change (𝕎 i).carrier ⊆ K'.carrier
    rw [hWcarrier i (hun hi)]
    rw [← hL]
    exact Set.image_mono (hsubn i (hun hi))
  have hratio : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal) * volume K'.carrier := by
    have h := _root_.Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient
      (E := E) hdim hτ0 hR1 Tτ
    rw [hofR] at h
    simpa [K', ← hL, ConvexSpaceBody.closedUnitBall_carrier] using h
  have hfrodsman : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal)
        * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K' :=
    frostmanConstIn_closedUnitBall_le_of_ambient (u := u) (𝕎 := 𝕎) (K' := K')
      (Cv := (4 * Cn) ^ 6) hK' hK'vol hWK' hratio
  have hF_rel : frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K'
      = frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody := by
    have h := ConvexSpaceBody.frostmanConstIn_affineImage u (fun i => (T i).toConvexSpaceBody)
      Tτ.toConvexSpaceBody L hcont
    dsimp [𝕎, K']
    exact h
  obtain ⟨u', hu'sub, hu'ne, hVD, hmult, hfull, hfrost⟩ :=
    of_comparableReplacementFree (u := u) (𝕎 := 𝕎) (𝕍 := 𝕍)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)) (Cv := (4 * Cn) ^ 6)
      (Λ := Λ) (C₁ := c₁) hΛ hCv hC₁ hVK hpackage
  refine ⟨u', hu'sub, hu'ne, 𝕍, ?_⟩
  constructor
  · simpa [𝕍] using hVD
  constructor
  · intro i hi
    simpa [𝕍] using h𝕍ball i (hu'sub hi)
  constructor
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          = ShadedBody.multiplicity u 𝕎 := by
            simpa [𝕎] using (ShadedBody.multiplicity_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := hmult
      _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (𝕍 i).toShadedBody) := by
            gcongr
            exact_mod_cast (fineNormalize_C_dominates hc₁).1
  constructor
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          = (ShadedBody.fullness u 𝕎 : ENNReal) := by
            simpa [𝕎] using (ShadedBody.fullness_affineImage u
              (fun i => (T i).toShadedBody) L hcont hemb).symm
      _ ≤ (((4 * Cn) ^ 6 : NNReal) : ENNReal) * (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := hfull
      _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (𝕍 i).toShadedBody) : ENNReal) := by
            gcongr
            exact_mod_cast (fineNormalize_C_dominates hc₁).2.1
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        frostmanConstIn u' (fun i => (𝕍 i).toConvexSpaceBody)
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
            ≤ (c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody)
                  (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := hfrost
        _ ≤ (c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal)
            * ((((4 * Cn) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (𝕎 i).toConvexSpaceBody) K') := by
              exact mul_le_mul_right hfrodsman
                ((c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal))
        _ = (c₁ : ENNReal) * (((4 * Cn) ^ 6 : NNReal) : ENNReal)
            * ((((4 * Cn) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody) := by
              rw [hF_rel]
        _ = ((c₁ * (4 * Cn) ^ 6 * (4 * Cn) ^ 6 : NNReal) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody := by
              simp [ENNReal.coe_mul]
              ring
        _ ≤ (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody := by
              have hdom : (c₁ * (4 * Cn) ^ 6 * (4 * Cn) ^ 6 : NNReal) ≤ fineNormalize.C Cn := by
                calc
                  (c₁ * (4 * Cn) ^ 6 * (4 * Cn) ^ 6 : NNReal)
                      = c₁ * ((4 * Cn) ^ 6 * (4 * Cn) ^ 6) := by
                        rw [← mul_assoc]
                  _ = c₁ * (4 * Cn) ^ 12 := by
                        rw [← pow_add]
                  _ = ((4 * Cn) ^ 12 : NNReal) * c₁ := by ring
                  _ ≤ fineNormalize.C Cn := (fineNormalize_C_dominates hc₁).2.2
              exact mul_le_mul (by exact_mod_cast hdom) le_rfl (by positivity) (by positivity)
    · intro i hi
      rw [← hWcarrier i hi]
      exact hsub' i hi
    · intro i hi
      rw [hshade i hi]
      simp [𝕎, hL]
    · intro i hi
      rw [← hWcarrier i hi]
      exact hvol i hi
    · simpa [K', ← hL] using hK'c
    · intro i _
      exact ⟨_root_.Tube.center_centredExtension (hxy i),
        _root_.Tube.direction_centredExtension (hxy i)⟩

/-- **The fine fibre satisfies the hypotheses of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`** (blueprint `lem:ml1bootFineGenKF`).

Write `C = Kakeya.ml1Boot.fineFactor.C`, let `γ ∈ [0, 1]` and suppose `K_F(γ)` holds in `ℝ³`.
For every loss exponent `εs > 0` there is a fullness threshold `ηs > 0` such that, for every
`Λ ≥ 1`, for all sufficiently small `δ > 0` and every Frostman constant `Cf ∈ [1, ∞)`: a fibre
in the sense of `Kakeya.ml1Boot.IsFineFibre` (nonempty, pairwise essentially distinct shaded
`δ`-tubes inside a `τ`-tube `T_τ ⊆ B₁`, two-sided shading densities `Λ, μ₀`, and
`λ(𝕌, Y) ≥ C Λ² δ ^ ηs`) with `C_F(𝕌, T_τ) ≤ Cf / C` satisfies

`μ(𝕌, Y) ≤ C Λ² δ ^ (-εs) Cf ^ (1 - γ/2) (δ/τ) ^ (-2γ) ((δ/τ)² |u|) ^ (1 - γ/2)`.

The quantifier order is the one of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn`, of which this is a
transport along `Kakeya.ml1Boot.exists_fineNormalization`: `ηs` depends only on `εs` and `γ`,
and the smallness threshold for `δ` depends only on `εs`, `γ` and `Λ`.  In particular `Cf` is
quantified *inside* the `∀ᶠ δ`, so it may be `δ`-dependent; this is what
`Kakeya.ml1Boot.multiplicity_le_fine` needs, applying the lemma at `Cf = C δ ^ (-a)`. -/
theorem fine_genKF (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hKF : FrostmanEstimate.{u} E γ) :
    ∀ εs > (0 : ℝ), ∃ ηs > (0 : ℝ), ∀ Λ : NNReal, 1 ≤ Λ →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ Cf : ENNReal, 1 ≤ Cf → Cf ≠ ⊤ →
    ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
        {μ₀ : ENNReal},
        IsFineFibre Λ μ₀ ηs u Tτ T →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody
          ≤ Cf / (fineFactor.C : ENNReal) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs)
            * Cf ^ (1 - γ / 2)
            * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro εs hεs
  have hn : 1 < Module.finrank ℝ E := by
    rw [hdim]
    norm_num
  obtain ⟨ηs, hηs_pos, hηs_ev⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn E hγ0 hγ1 hn hKF εs hεs
  refine ⟨ηs, hηs_pos, ?_⟩
  intro Λ hΛ1
  filter_upwards [hηs_ev, self_mem_nhdsWithin, eventually_le_quarter] with δ hδ_aux hδ_pos hδ4
  intro Cf hCf1 hCftop τ hδτ hτ1 ι u Tτ T μ₀ hfib hF
  obtain ⟨hμ₀, hu, hTτ, hsub, hED, hdens, hFull⟩ := hfib
  rcases exists_fineNormalization hdim hδ_pos hδτ hτ1 hΛ1 hμ₀ Tτ T hu (Finset.Subset.refl u)
    hTτ hsub hED hdens with
    ⟨u', hu'u, hu'_ne, V, hV_ED, hV_ball, hmult, hfull, hF', -, -, -, -⟩
  have hτ_pos : 0 < τ := lt_of_lt_of_le hδ_pos hδτ
  have hσ_le_one : fineScale δ τ ≤ 1 := by
    have hq : fineScale δ τ ≤ (1 / 4 : NNReal) := (fineScale_bounds hδτ hτ_pos).2.1
    exact hq.trans (by exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≤ (1 : ℝ)))
  have hδ_le_σ : δ ≤ fineScale δ τ :=
    le_fineScale hδ4 hτ1 hτ_pos
  let ι' : Type u := {i : ι // i ∈ u'}
  let s' : Finset ι' := u'.attach
  let V' : ι' → ShadedTube (fineScale δ τ) E := fun i => V i.1
  have hV'_ball : ∀ i ∈ s', (V' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    exact hV_ball i.1 i.2
  have hs'_ne : s'.Nonempty := by
    rcases hu'_ne with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩⟩
  have hV'_ED : (s' : Set ι').Pairwise
      (fun i j => IsEssentiallyDistinct (V' i).carrier (V' j).carrier) := by
    intro i hi j hj hij
    exact hV_ED i.2 j.2 (by
      intro h
      exact hij (Subtype.ext h))
  let C₀ : NNReal := fineNormalize.C (_root_.Tube.normalization.C 3)
  have hC0pos : (0 : NNReal) < C₀ := by
    exact lt_of_lt_of_le zero_lt_one (one_le_fineNormalize_C (Tube.normalization.one_le_C 3))
  have hC0 : (C₀ : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hC0pos)
  have hCtop : (C₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC0le : (C₀ : ENNReal) ≤ (fineFactor.C : ENNReal) := by
    exact_mod_cast (fineNormalize_C_le_fineFactor_C)
  have hCfine_pos : 0 < fineFactor.C := by
    exact lt_of_lt_of_le zero_lt_one one_le_fineFactor_C
  have hCfine0 : (fineFactor.C : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt hCfine_pos)
  have hCfinetop : (fineFactor.C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hΛ0 : (Λ : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ1))
  have hΛtop : (Λ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCΛ2 : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 ≠ 0 := by
    exact mul_ne_zero hC0 (pow_ne_zero 2 hΛ0)
  have hCΛ2top : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top hCtop (ENNReal.pow_ne_top hΛtop)
  have hFull_u' : (δ : ENNReal) ^ ηs
      ≤ (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
    have hFull0 : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
        ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := by
      calc
        (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
            ≤ (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs := by
              gcongr
        _ ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := hFull
    have hstep : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
        ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
      exact le_trans hFull0 hfull
    exact (ENNReal.mul_le_mul_iff_right hCΛ2 hCΛ2top).1 hstep
  have hfull_eq : (ShadedBody.fullness s' (fun i => (V' i).toShadedBody) : ENNReal)
      = (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
    rw [ShadedBody.fullness_def, ShadedBody.fullness_def]
    congr 1
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).shade)
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).carrier)
  have hV'_full : (δ : ENNReal) ^ ηs
      ≤ (ShadedBody.fullness s' (fun i => (V' i).toShadedBody) : ENNReal) := by
    rw [hfull_eq]
    exact hFull_u'
  have hFrost_u' : IsFrostmanIn u' (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall Cf := by
    apply isFrostmanIn_of_frostmanConstIn_le
    calc
      frostmanConstIn u' (fun i => (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
          ≤ (C₀ : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody)
                  Tτ.toConvexSpaceBody := hF'
      _ ≤ (C₀ : ENNReal) * (Cf / (fineFactor.C : ENNReal)) := by gcongr
      _ ≤ (fineFactor.C : ENNReal) * (Cf / (fineFactor.C : ENNReal)) := by gcongr
      _ = Cf := by rw [ENNReal.mul_div_cancel hCfine0 hCfinetop]
  have he : Set.BijOn (fun i : ι' => i.1) (s' : Set ι') (u' : Set ι) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact i.2
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro i hi
      exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩, rfl⟩
  have hFrost_s' : IsFrostmanIn s' (fun i => (V' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall Cf := by
    have h' : IsFrostmanIn s' (fun i => (V i.1).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall Cf :=
      (IsFrostmanIn.reindex (s := u') (t := s') (W := fun i => (V i).toConvexSpaceBody)
        (K := ConvexSpaceBody.closedUnitBall) (C := Cf) he).2 hFrost_u'
    simpa [V'] using h'
  have hmult' : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
        * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((s'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
            ^ (1 - γ / 2) := by
    exact hδ_aux Cf hCf1 hCftop (fineScale δ τ) hδ_le_σ hσ_le_one s' V' hs'_ne hV'_ball hV'_ED
      hV'_full hFrost_s'
  have hmult_eq : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
      = ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
    congr 1
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).shade)
    · apply congrArg volume
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨i, hi, hx⟩
        exact ⟨i.1, i.2, hx⟩
      · intro hx
        rw [Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨i, hi, hx⟩
        exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩, hx⟩
  have hcard_s' : s'.card = u'.card := by
    change (u'.attach).card = u'.card
    exact Finset.card_attach
  have hmult'_u' : ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
        * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    rw [← hmult_eq]
    calc
      ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((s'.card : ENNReal)
                * ((fineScale δ τ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
                ^ (1 - γ / 2) := hmult'
      _ = (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ))
                ^ (1 - γ / 2) := by
          rw [hcard_s', hdim]
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hcard_le : (u'.card : ENNReal) ≤ (u.card : ENNReal) := by
    exact_mod_cast (Finset.card_le_card hu'u)
  let A : ENNReal := (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
  let Bfs : ENNReal := ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
      * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  let Bd : ENNReal := (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
      * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  have hbr : Bfs ≤ 16 * Bd := by
    have h := fineScale_bracket_le (δ := δ) (τ := τ) hδ_pos hδτ hτ_pos hγ0 hγ1 u'.card
    simpa [Bfs, Bd, mul_assoc] using h
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := hmult
    _ ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
          * ((δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ))
              ^ (1 - γ / 2)) := by
          gcongr
    _ = A * Bfs := by
          dsimp [A, Bfs]
          ring
    _ ≤ A * (16 * Bd) := by
          exact mul_le_mul (le_rfl : A ≤ A) hbr (zero_le) (zero_le)
    _ = ((16 * C₀ : NNReal) : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs)
          * Cf ^ (1 - γ / 2) * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          dsimp [A, Bd]
          ring
    _ ≤ (fineFactor.C : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs)
          * Cf ^ (1 - γ / 2) * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr

/-- **(GWZ Lemma 8.1) The fine-scale factor `μ(𝕋[T_τ], Y)`, with the Frostman loss explicit**
(blueprint `lem:ml1bootFineFactor`, first bound of `eq:ml1bootFineFactor`).

Write `C = Kakeya.ml1Boot.fineFactor.C` and suppose `K_F(γ)` holds.  Take the loss exponent
`e` (the blueprint's `ε♯ = η₀`) and let `ηs` be the threshold supplied by
`Kakeya.ml1Boot.fine_genKF`.  Then for every `Λ ≥ 1` and every Frostman exponent `a ≥ 0`
(the blueprint's `η_{j-1}`), for all sufficiently small `δ > 0`: a fibre in the sense of
`Kakeya.ml1Boot.IsFineFibre` — which carries (b) `λ(𝕋[T_τ], Y) ≥ C Λ² δ ^ ηs` as its
`fullness` field — subject in addition to

* (a) `C_F(𝕋[T_τ], T_τ) ≤ δ ^ (-a)`,

satisfies `μ ≤ C² Λ² δ ^ (-e) δ ^ (-(1 - γ/2) a) (δ/τ) ^ (-2γ) (|u| (δ/τ)²) ^ (1 - γ/2)`.

This is the form in which `Kakeya.ml1Boot.fine_genKF` delivers the bound.  The absorbed form
that `Kakeya.ml1Boot.multiplicity_le_of_middle` consumes is
`Kakeya.ml1Boot.multiplicity_le_fine`, which is this bound together with the absorption
hypothesis (c).

See the module docstring for the replacement of the parameter package's exponents by the bare
reals `e`, `a` and `ηs`. -/
theorem multiplicity_le_fine_frostmanLoss (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ e > (0 : ℝ), ∃ ηs > (0 : ℝ), ∀ Λ : NNReal, 1 ≤ Λ → ∀ a : ℝ, 0 ≤ a →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
        {μ₀ : ENNReal},
        IsFineFibre Λ μ₀ ηs u Tτ T →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody
          ≤ (δ : ENNReal) ^ (-a) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
            ≤ (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
              * (δ : ENNReal) ^ (-(1 - γ / 2) * a)
              * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
              * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro e he
  rcases fine_genKF hdim hγ0 hγ1 hKF e he with ⟨ηs, hηs, h_genKF⟩
  refine ⟨ηs, hηs, ?_⟩
  intro Λ hΛ a ha
  let C : ENNReal := (fineFactor.C : ENNReal)
  have hC1 : 1 ≤ C := by
    have hCnn : 1 ≤ fineFactor.C := one_le_fineFactor_C
    change (1 : ENNReal) ≤ (fineFactor.C : ENNReal)
    exact_mod_cast hCnn
  have hC0 : C ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_fineFactor_C))
  have hCtop : C ≠ ⊤ := by exact ENNReal.coe_ne_top
  filter_upwards [h_genKF Λ hΛ, self_mem_nhdsWithin] with δ hδ_gen hδ_pos
  intro τ hδτ hτ1 ι u Tτ T μ₀ hfib hFa
  have hδ0 : 0 < δ := hδ_pos
  have hδ1 : δ ≤ 1 := le_trans hδτ hτ1
  have hδle : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ0
  have hδne : (δ : ENNReal) ≠ 0 := ne_of_gt hδpos
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  let Cf : ENNReal := C * (δ : ENNReal) ^ (-a)
  have hδpow1 : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-a) := by
    by_cases ha0 : a = 0
    · simp [ha0]
    · exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hδpos hδle
        (neg_lt_zero.mpr (lt_of_le_of_ne ha (Ne.symm ha0)))
  have hCf1 : 1 ≤ Cf := by
    dsimp [Cf]
    exact one_le_mul hC1 hδpow1
  have hCftop : Cf ≠ ⊤ := by
    dsimp [Cf]
    exact ENNReal.mul_ne_top hCtop (ENNReal.rpow_ne_top_of_ne_zero hδne hδtop)
  have hCf_div : Cf / C = (δ : ENNReal) ^ (-a) := by
    dsimp [Cf]
    rw [mul_comm]
    rw [ENNReal.mul_div_cancel_right hC0 hCtop]
  have hF_gen : frostmanConstIn u (fun i => (T i).toConvexSpaceBody)
      Tτ.toConvexSpaceBody ≤ Cf / C := by
    rw [hCf_div]
    exact hFa
  have hmult : ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
      ≤ C * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e) * Cf ^ (1 - γ / 2)
        * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    exact hδ_gen Cf hCf1 hCftop τ hδτ hτ1 (ι := ι) (u := u) Tτ T (μ₀ := μ₀) hfib hF_gen
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hCf_eq : Cf ^ (1 - γ / 2) = C ^ (1 - γ / 2) * (δ : ENNReal) ^ (-(1 - γ / 2) * a) := by
    dsimp [Cf]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpos]
    congr 1
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hCmono : C ^ (1 - γ / 2) ≤ C := by
    calc
      C ^ (1 - γ / 2) ≤ C ^ (1 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le hC1 (by nlinarith [hγ0])
      _ = C := by rw [ENNReal.rpow_one]
  have hCfpow : Cf ^ (1 - γ / 2) ≤ C * (δ : ENNReal) ^ (-(1 - γ / 2) * a) := by
    calc
      Cf ^ (1 - γ / 2) = C ^ (1 - γ / 2) * (δ : ENNReal) ^ (-(1 - γ / 2) * a) := hCf_eq
      _ ≤ C * (δ : ENNReal) ^ (-(1 - γ / 2) * a) := by
            exact mul_le_mul_left hCmono ((δ : ENNReal) ^ (-(1 - γ / 2) * a))
  have hδeadd : (δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-a) = (δ : ENNReal) ^ (-e - a) := by
    rw [show -e - a = (-e) + (-a) by ring]
    rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-e) (-a) hδne hδtop]
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ C * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e) * Cf ^ (1 - γ / 2)
          * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hmult
    _ ≤ C * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
          * (C * (δ : ENNReal) ^ (-(1 - γ / 2) * a))
          * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr
    _ = C ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
          * (δ : ENNReal) ^ (-(1 - γ / 2) * a)
          * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          ring

/-- **(GWZ Lemma 8.1) The fine-scale factor `μ(𝕋[T_τ], Y)`** (blueprint
`lem:ml1bootFineFactor`, second bound of `eq:ml1bootFineFactor`).

`Kakeya.ml1Boot.multiplicity_le_fine_frostmanLoss` with the absorption hypothesis

* (c) `C² Λ² δ ^ (-e - a) ≤ δ ^ (-4a)`

applied to it, giving `μ ≤ δ ^ (-4a) (δ/τ) ^ (-2γ) (|u| (δ/τ)²) ^ (1 - γ/2)`.  This is the
form `Kakeya.ml1Boot.multiplicity_le_of_middle` consumes.

Only the *constant* `C² Λ²` and the exponent `e` can be absorbed this way, and hypothesis (c)
is where that absorption is paid for explicitly rather than hidden in the `∀ᶠ δ in 𝓝[>] 0`;
compare hypothesis (g) of `Kakeya.ml1Boot.multiplicity_le_of_middle`. -/
theorem multiplicity_le_fine (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ e > (0 : ℝ), ∃ ηs > (0 : ℝ), ∀ Λ : NNReal, 1 ≤ Λ → ∀ a : ℝ, 0 ≤ a →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
        {μ₀ : ENNReal},
        IsFineFibre Λ μ₀ ηs u Tτ T →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) Tτ.toConvexSpaceBody
          ≤ (δ : ENNReal) ^ (-a) →
        (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e - a)
          ≤ (δ : ENNReal) ^ (-4 * a) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * a)
            * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro e he
  obtain ⟨ηs, hηs, hraw⟩ := multiplicity_le_fine_frostmanLoss hdim hγ0 hγ1 hKF e he
  refine ⟨ηs, hηs, ?_⟩
  intro Λ hΛ a ha
  filter_upwards [hraw Λ hΛ a ha, self_mem_nhdsWithin] with δ hδ_raw hδ_pos
  intro τ hδτ hτ1 ι u Tτ T μ₀ hfib hFa hFc
  have hδ0 : 0 < δ := hδ_pos
  have hδ1 : δ ≤ 1 := le_trans hδτ hτ1
  have hδle : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ0
  have hδne : (δ : ENNReal) ≠ 0 := ne_of_gt hδpos
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδeadd : (δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-a) = (δ : ENNReal) ^ (-e - a) := by
    rw [show -e - a = (-e) + (-a) by ring]
    rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-e) (-a) hδne hδtop]
  have hstep : (δ : ENNReal) ^ (-(1 - γ / 2) * a) ≤ (δ : ENNReal) ^ (-a) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδle (by nlinarith [ha, hγ0])
  have habs : (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
      * (δ : ENNReal) ^ (-(1 - γ / 2) * a) ≤ (δ : ENNReal) ^ (-4 * a) := by
    calc
      (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
          * (δ : ENNReal) ^ (-(1 - γ / 2) * a)
          ≤ (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
            * (δ : ENNReal) ^ (-a) := by gcongr
      _ = (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2
            * ((δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-a)) := by ring
      _ = (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e - a) := by
            rw [hδeadd]
      _ ≤ (δ : ENNReal) ^ (-4 * a) := hFc
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ (fineFactor.C : ENNReal) ^ 2 * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-e)
          * (δ : ENNReal) ^ (-(1 - γ / 2) * a)
          * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
        hδ_raw τ hδτ hτ1 (ι := ι) (u := u) Tτ T (μ₀ := μ₀) hfib hFa
    _ ≤ (δ : ENNReal) ^ (-4 * a)
          * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
        gcongr

end Fine

/-! ### Case (ii): the fine-scale factor over a `c`-dilate

The plank-in-tube chain of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean` does not put the
fine tubes inside an honest `b`-tube, only inside a dilate of one, and the Frostman
bound it supplies is taken in that dilate.  This subsection restates the two fine-factor
lemmas above under the weakened containment, at a free dilation ratio `c`.  Splitting the
dilate into honest tubes is *not* available (blueprint `note:ml1bootDilateSplitNotEnough`); the
repair is made at the normalization, which is affine and therefore commutes with the homothety
defining the dilate. -/

/-- **The constant `C_{lem:ml1bootFineNormalizeDilate}(c)`** of
`Kakeya.ml1Boot.exists_fineNormalization_dilate` (blueprint
`def:ml1bootFineNormalizeDilateConstant`), at a free dilation ratio `c`.

It is `Kakeya.ml1Boot.fineFactor.C` at the normalized ambient radius `(1 + 2 c) C_N` in place
of `C_N`, `C_N = Tube.normalization.C 3`: the normalization `Φ_{T_τ}` is affine, so it carries
`c · T_τ` to the `c`-dilate of `Φ_{T_τ}(T_τ)` about `Φ_{T_τ}(m)`, and every loss of the
normalization argument is a power of the ambient radius or of the selection constant
`Tube.comparableReplacement.C`.

## Why the radius factor is `1 + 2 c` and not `2 c - 1`

A `c`-dilate about a point of a body contained in `B_R` lands in `B_{(2c-1)R}`: for `|p| ≤ R`
and `|x| ≤ R`, `|p + c (x - p)| ≤ c |x| + |1 - c| |p| ≤ (2c-1) R` when `c ≥ 1`, and `≤ R` when
`0 ≤ c ≤ 1`.  Both are at most `(1 + 2c) R`, so `1 + 2 c` is a safe radius factor for **every**
`c ≥ 0`.  It is used in place of `2 c - 1` because the ratio is carried as an `NNReal`, where
subtraction truncates; and in place of `c + 1`, which is wrong for `c > 2`.

## The tilt factor is `max 2 (2 c)`

`Kakeya.ml1Boot.fineNormalize.C` now carries the tilt `κ` of the fine cores against the axis
of `T_τ`, because its selection summand does (see there).  On this route the available tilt is
`2 c θ`, from `Tube.perp_norm_core_sub_le_of_subset_dilate` at a free ratio, so the tilt to
instantiate at is `2 c` — `4` at the ratio `c = 2` the chain uses, matching blueprint
`section8_finenormalize_core.tex` line 59.

It is written `max 2 (2 c)` and not `2 c`, for one reason: `2` is the floor blueprint
`lem:ml1bootFineNormalizeCore` puts on `κ` (line 53, and lines 75-77 on why it costs nothing),
and at `c < 1` the bare `2 c` falls below it.  It would also make
`Kakeya.ml1Boot.fineFactor_C_le_fineNormalizeDilate_C` false: at `c = 0` the radius factor is
`1`, so the two constants would differ only in their selection summands, and that of
`Kakeya.ml1Boot.fineFactor.C` — read at `κ = 2` — would be the larger.  Since the tilt bound
`2 c θ ≤ max 2 (2 c) · θ` holds a fortiori, taking the maximum weakens nothing and keeps `κ ≥ 2`
and monotonicity in `c` at the same time.

As in the undilated case the factor `16` sits here and not on the normalization leaf
`Kakeya.ml1Boot.exists_fineNormalization_dilate`, which is stated at
`Kakeya.ml1Boot.fineNormalize.C ((1 + 2 c) C_N) (max 2 (2 c))`; the `16` is spent once, in
`Kakeya.ml1Boot.fine_genKF_dilate`.

Like `Kakeya.ml1Boot.fineFactor.C` it depends only on the ambient dimension `3` and on the
ratio `c`; in particular not on `δ`, on `τ`, on `θ`, on `γ`, on `j`, or on the family.  That it
dominates `Kakeya.ml1Boot.fineFactor.C` is
`Kakeya.ml1Boot.fineFactor_C_le_fineNormalizeDilate_C`, for every `c`; that clause is a
convenience and does **not** condition citing a lemma stated at the smaller constant at the
larger one (blueprint `note:ml1bootArithFreeConstant`).

At `c = 2` the radius factor is `5`, where the pinned-ratio predecessor of this definition had
`3`.  The constant is therefore *larger* than it used to be at the ratio the chain actually
uses; see `Kakeya.ml1Boot.fineFactor_C_le_fineNormalizeDilate_C` for the direction of the
monotonicity that makes this harmless on conclusion sides. -/
noncomputable abbrev fineNormalizeDilate.C (c : NNReal) : NNReal :=
  16 * fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c))

/-- **`1 ≤ C₃(c)`** (blueprint `lem:ml1bootFineNormalizeDilateConstantOneLe`), the analogue of
`Kakeya.ml1Boot.one_le_fineFactor_C`.  No lower bound on `c` is needed: `1 + 2 c ≥ 1` holds for
every `c : NNReal`. -/
theorem one_le_fineNormalizeDilate_C (c : NNReal) : (1 : NNReal) ≤ fineNormalizeDilate.C c := by
  unfold fineNormalizeDilate.C
  have h : (1 : NNReal) ≤ (1 + 2 * c) * _root_.Tube.normalization.C 3 := by
    exact one_le_mul (self_le_add_right 1 (2 * c)) (_root_.Tube.normalization.one_le_C 3)
  exact one_le_mul (by norm_num : (1 : NNReal) ≤ 16) (one_le_fineNormalize_C h)

/-- **`C₃(c) ≥ C₂`** (blueprint `def:ml1bootFineNormalizeDilateConstant`, the comparison
clause): both are `16 * Kakeya.ml1Boot.fineNormalize.C R κ`, at `(R, κ) = ((1 + 2 c) C_N,
max 2 (2 c))` and `(R, κ) = (C_N, 2)`, and `fineNormalize.C` is monotone in both arguments.
Again no lower bound on `c` is used, only `1 ≤ 1 + 2 c` and `2 ≤ max 2 (2 c)`; the second is
exactly why the tilt is taken with the maximum, and not bare `2 c`. -/
theorem fineFactor_C_le_fineNormalizeDilate_C (c : NNReal) :
    fineFactor.C ≤ fineNormalizeDilate.C c := by
  have hCN : Tube.normalization.C 3 ≤ (1 + 2 * c) * Tube.normalization.C 3 := by
    exact le_mul_of_one_le_left' (self_le_add_right 1 (2 * c))
  have hbase : 4 * Tube.normalization.C 3 ≤ 4 * ((1 + 2 * c) * Tube.normalization.C 3) := by
    exact mul_le_mul_right hCN 4
  have hpow12 : (4 * Tube.normalization.C 3) ^ 12
      ≤ (4 * ((1 + 2 * c) * Tube.normalization.C 3)) ^ 12 := by
    exact pow_le_pow_left₀ (by exact zero_le) hbase 12
  have hmono : Tube.comparableReplacement.C 3 ((4 * Tube.normalization.C 3) ^ 6)
      ≤ _root_.Tube.comparableReplacement.C 3
          ((4 * ((1 + 2 * c) * Tube.normalization.C 3)) ^ 6) := by
    unfold Tube.comparableReplacement.C
    gcongr
  -- The selection summand: its ratio `4 (κ + 2) R C_n` grows in both `κ` and `R`.
  have hCn0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    le_of_lt (lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3))
  have hκ : ((2 : NNReal) : ℝ) ≤ ((max 2 (2 * c) : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (le_max_left _ _)
  have hR : ((Tube.normalization.C 3 : NNReal) : ℝ)
      ≤ (((1 + 2 * c) * Tube.normalization.C 3 : NNReal) : ℝ) := NNReal.coe_le_coe.mpr hCN
  have hratio :
      4 * (((2 : NNReal) : ℝ) + 2) * ((Tube.normalization.C 3 : NNReal) : ℝ)
          * Kakeya.Tube.tubeOverlapCoreClose.C 3
        ≤ 4 * (((max 2 (2 * c) : NNReal) : ℝ) + 2)
            * (((1 + 2 * c) * Tube.normalization.C 3 : NNReal) : ℝ)
            * Kakeya.Tube.tubeOverlapCoreClose.C 3 := by
    have hb0 : (0 : ℝ) ≤ ((Tube.normalization.C 3 : NNReal) : ℝ) := NNReal.coe_nonneg _
    have ha0 : (0 : ℝ) ≤ ((2 : NNReal) : ℝ) := NNReal.coe_nonneg _
    gcongr
  have hmonoSel := essDistinctTubesInSelfDilate_C_le_of_le (n := 3) hratio
  have hmonoFN : fineNormalize.C (Tube.normalization.C 3)
      ≤ fineNormalize.C ((1 + 2 * c) * Tube.normalization.C 3) (max 2 (2 * c)) := by
    unfold fineNormalize.C
    exact add_le_add (mul_le_mul hpow12 hmono (by exact zero_le) (by exact zero_le)) hmonoSel
  unfold fineFactor.C fineNormalizeDilate.C
  exact mul_le_mul_right hmonoFN 16

/-- **The dilate normalization loss is at most the dilate fine-factor constant**
(blueprint `lem:ml1bootFineNormalizeCoreConstantLeFineFactor`, dilate half): they differ by
the factor `16`. -/
theorem fineNormalize_C_le_fineNormalizeDilate_C (c : NNReal) :
    fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c))
      ≤ fineNormalizeDilate.C c := by
  unfold fineNormalizeDilate.C
  exact le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 16)

section FineDilate

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **A fine fibre over a `c`-dilate**, as `Kakeya.ml1Boot.fine_genKF_dilate` consumes it
(blueprint `lem:ml1bootFineNormalizeDilate` and `lem:ml1bootFineGenKFDilate`, the hypotheses on
the fibre).

This is `Kakeya.ml1Boot.IsFineFibre` with two changes and no others: the containment clause is
`T i ⊆ K` for an ambient body `K ⊆ c · T_τ` instead of `T i ⊆ T_τ`, and the fullness prefactor
is `Kakeya.ml1Boot.fineNormalizeDilate.C c` instead of `Kakeya.ml1Boot.fineFactor.C`, that being
what the dilate normalization loses.

## The ambient body is a parameter, and the volume ratio `M` is the price

The containment is stated at a *named* convex body `K` rather than at the literal
`Kakeya.Tube.dilate Tτ (c : ℝ)`.  Two things are asked of it: `K ≤ c · T_τ`, and the reverse
volume comparison `|c · T_τ| ≤ M |K|` recorded in `ambient_fat`.  Taking `K = c · T_τ` and
`M = 1` recovers the previous form verbatim, so nothing is lost; what is gained is that a
caller holding the fine tubes inside something *smaller* than the dilate — a plank block's
convex hull, say — may name that body here and have the Frostman constant of
`Kakeya.ml1Boot.fine_genKF_dilate` read in it.  That matters because
`Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient` is monotone *increasing* in the ambient body:
a bound at the smaller body is the weaker hypothesis, and it cannot be recovered after the fact
from a bound at the dilate.

`K ≤ c · T_τ` keeps the tilt bound and the normalized ambient radius of
`Kakeya.ml1Boot.exists_fineNormalization_dilate` available, so the *geometric* loss
`Kakeya.ml1Boot.fineNormalizeDilate.C c` is unchanged and is still read at the ratio `c`.

`ambient_fat` is a separate and unavoidable obligation, and the field exists because an
earlier version of this structure omitted it and was thereby **false**.  A Frostman constant
is a ratio of densities, and `Kakeya.ConvexSpaceBody.densityIn s W K` divides by
`volume K.carrier`; the ambient therefore enters the numerator (which test bodies are
admissible) *and* the denominator (the normalizing volume).  The order clause `K ≤ c · T_τ`
controls only the first.  See the note at
`Kakeya.ml1Boot.exists_fineNormalization_dilate` for the explicit counterexample that an
`M`-free form admits.

`M` does not appear in `fullness`, and it does not appear in the multiplicity or fullness
conclusions of `Kakeya.ml1Boot.exists_fineNormalization_dilate`.  Those are ratios of sums of
volumes over the *family*, with no ambient body in either numerator or denominator, so they
are invariant under the affine normalization and blind to `|K|`.  Only the Frostman clause,
whose denominator is a volume of the ambient, sees the ratio.

The ratio is free.  It is carried as an `NNReal` because it is read twice: once as the ratio of
`Kakeya.Tube.dilate`, which takes a real, and once inside
`Kakeya.ml1Boot.fineNormalizeDilate.C`, whose radius argument is an `NNReal`.  Taking it
nonnegative by construction is what keeps `1 ≤ 1 + 2 c` — and hence
`Kakeya.ml1Boot.one_le_fineNormalizeDilate_C` — free of any side hypothesis.

The clause on the parent itself is deliberately unchanged, `T_τ ⊆ B₁`.  Asking
`c · T_τ ⊆ B₁` instead would make every statement under it vacuous for `c > 1`: a
`Kakeya.Tube` has a core of length exactly `1`, so `c · T_τ` has diameter
`c (2 + 4 τ) > 2 = diam B₁` and no `τ`-tube whatever satisfies it (blueprint
`note:ml1bootDilateInBallObligation`). -/
structure IsFineFibreDilate {ι : Type*} {δ τ : NNReal} (c : NNReal) (R : ℝ)
    (K : ConvexSpaceBody E)
    (M : NNReal) (Λ : NNReal) (μ₀ : ENNReal)
    (ηs : ℝ) (u : Finset ι) (Tτ : Tube τ E) (T : ι → ShadedTube δ E) : Prop where
  /-- The common density the shadings are compared to is nonzero. -/
  density_pos : 0 < μ₀
  /-- The fibre is nonempty. -/
  nonempty : u.Nonempty
  /-- The parent tube lies in the ball of radius `R`.  The *dilate* does not, and is not asked
  to.  `R` used to be pinned to `1`; it is free because the hypothesis is dead downstream (see
  `Kakeya.ml1Boot.exists_fineNormalization_dilate`, which does not read it). -/
  parent_ball : Tτ.carrier ⊆ Metric.closedBall 0 R
  /-- The ambient body lies in the `c`-dilate of the parent tube. -/
  ambient_le_parent_dilate : K ≤ Tube.dilate Tτ (c : ℝ)
  /-- The ambient body fills a definite fraction `1 / M` of that dilate.  This is the
  denominator half of the ambient hypothesis and is *not* implied by the order clause above. -/
  ambient_fat : volume (Tube.dilate Tτ (c : ℝ)).carrier ≤ (M : ENNReal) * volume K.carrier
  /-- Every member of the fibre lies in the ambient body. -/
  subset_ambient : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ K
  /-- The members are pairwise essentially distinct. -/
  essDistinct : (u : Set ι).Pairwise
    (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
  /-- The shading densities are two-sidedly comparable to `μ₀`, with constant `Λ`. -/
  shade_comparable : ∀ i ∈ u,
    (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier
  /-- The fibre is full, with the prefactor the dilate normalization loses. -/
  fullness : (fineNormalizeDilate.C c : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
    ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)

omit [Nontrivial E] in
/-- **The tilt of an inner core against the ambient axis, over a dilate** (blueprint
`lem:ml1bootFineNormalizeDilateTilt`, in the form the selection package consumes it).

`Tube.perp_norm_direction_le_of_subset_dilate` read at `T.direction = T.y - T.x` rather than at
`T.x - T.y`, exactly as `Tube.perp_norm_direction_le_of_subset` is
`Tube.perp_norm_core_sub_le_of_subset` so read.  This is the instance `κ = 2 c` of the `hperp`
hypothesis of `Tube.exists_comparableReplacement_affine`, and `max 2 (2 c)` covers it together
with the undilated `κ = 2`. -/
private lemma perp_norm_direction_le_of_subset_dilate {θ ρ : NNReal} {c : ℝ} (hc : 0 < c)
    (T₀ : Tube θ E) (T : Tube ρ E) (hT : T.carrier ⊆ (Tube.dilate T₀ c).carrier) :
    ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖
      ≤ 2 * c * (θ : ℝ) := by
  have h := (_root_.Tube.perp_norm_core_sub_le_of_subset_dilate hc T₀ T hT).2.2
  have hEq : T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction
      = -(T.x - T.y - (inner ℝ T₀.direction (T.x - T.y) : ℝ) • T₀.direction) := by
    simp only [Tube.direction]
    rw [show T.x - T.y = -(T.y - T.x) by abel, inner_neg_right, neg_smul]
    abel
  rw [hEq, norm_neg]
  exact h

omit [Nontrivial E] in
/-- **Length of the image core, over a dilate.**

`Tube.normalization_core_length` bounds `dist (Φ x) (Φ y)` for `T ⊆ T₀` by substituting the
tilt bound `‖perp‖ ≤ 2 θ` into the Pythagoras identity `Tube.norm_sq_normalization_sub`, which
gives `dist² ≤ 1 + 4`.  Over a dilate the tilt bound is `‖perp‖ ≤ 2 c θ`
(`Tube.perp_norm_core_sub_le_of_subset_dilate`) and the same substitution gives
`dist² ≤ 1 + 4 c² ≤ (1 + 2 c)²`.

The bound is stated as `1 + 2 c` and *not* against `C_N`: the packaged
`Tube.IsNormalizationDistortion.dist_le_C` asks for `C_N`, which at `C_N = 64` fails once
`c > 31.99…`, so the packaged form is unavailable at an unbounded dilation ratio.  What the
route needs is only `dist ≤ R` at its own radius `R = (1 + 2 c) C_N`, and `1 + 2 c ≤ R` since
`1 ≤ C_N`.  See `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le`.

The bound holds with no upper bound on `θ`: the Pythagoras identity divides the transverse part
by `θ` and the tilt bound carries a matching factor `θ`, so `θ ≤ 1` cancels out of the
computation and is retained only to keep the hypothesis block parallel to the undilated
`Tube.normalization_core_length`. -/
private lemma dist_normalization_core_le_of_subset_dilate {θ ρ : NNReal} (hθ : 0 < θ)
    (_hθ1 : θ ≤ 1) {c : ℝ} (hc : 0 < c) (T₀ : Tube θ E) (T : Tube ρ E)
    (hT : T.carrier ⊆ (Tube.dilate T₀ c).carrier) :
    dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ 1 + 2 * c := by
  rw [dist_eq_norm]
  let p : ℝ := inner ℝ T₀.direction (T.x - T.y)
  let perp : E := T.x - T.y - (inner ℝ T₀.direction (T.x - T.y)) • T₀.direction
  have hperp : ‖perp‖ ≤ 2 * c * (θ : ℝ) := by
    simpa [perp] using (_root_.Tube.perp_norm_core_sub_le_of_subset_dilate hc T₀ T hT).2.2
  have hp1 : |p| ≤ (1 : ℝ) := by
    dsimp [p]
    calc
      |inner ℝ T₀.direction (T.x - T.y)| ≤ ‖T₀.direction‖ * ‖T.x - T.y‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by
        rw [T₀.norm_direction]
        have hxy : ‖T.x - T.y‖ = (1 : ℝ) := by rw [← dist_eq_norm, T.dist_eq_one]
        rw [hxy]
        norm_num
  have hp : p ^ 2 ≤ (1 : ℝ) := by
    have hpm : |p| ≤ |(1 : ℝ)| := by simpa using hp1
    simpa using (sq_le_sq.mpr hpm)
  have hq2 : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (4 * c ^ 2 : ℝ) := by
    have hqsq : ‖perp‖ ^ 2 ≤ (2 * c * (θ : ℝ)) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c * (θ : ℝ))]
      exact hperp
    have hθinvsq : ((θ : ℝ)⁻¹) ^ 2 * (2 * c * (θ : ℝ)) ^ 2 = (4 * c ^ 2 : ℝ) := by
      have hnθ : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
      calc
        ((θ : ℝ)⁻¹) ^ 2 * (2 * c * (θ : ℝ)) ^ 2 = (2 * (c * ((θ : ℝ)⁻¹ * (θ : ℝ)))) ^ 2 := by ring
        _ = (2 * (c * 1)) ^ 2 := by rw [inv_mul_cancel₀ hnθ]
        _ = 4 * c ^ 2 := by ring
    have hmain : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (2 * c * (θ : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hqsq (sq_nonneg ((θ : ℝ)⁻¹))
    rw [hθinvsq] at hmain
    exact hmain
  have hnorm_sq : ‖T₀.normalization T.x - T₀.normalization T.y‖ ^ 2 ≤ (1 + 2 * c) ^ 2 := by
    rw [_root_.Tube.norm_sq_normalization_sub T₀ T.x T.y]
    change p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (1 + 2 * c) ^ 2
    have hsum : p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (1 + 4 * c ^ 2 : ℝ) := by
      nlinarith [hp, hq2]
    nlinarith [hsum, hc]
  have hs := sq_le_sq.mp hnorm_sq
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + 2 * c)]
    using hs

omit [Nontrivial E] in
/-- **The image of a dilate of the ambient tube is bounded** (the radius computation in the proof
of blueprint `lem:ml1bootFineNormalizeDilate`).

`Tube.normalization_image_ambient_subset_closedBall` puts `Φ_{T₀}(T₀)` inside `B̄(x, C_N)`, by
`‖Φ z - x‖ ≤ 3 ≤ C_N`.  For the `c`-dilate, `Tube.abs_inner_and_perp_le_of_mem_dilate` gives
`|⟪z - centre, e⟫| ≤ c/2 + c θ` and `‖perp (z - centre)‖ ≤ c θ`; shifting the base point from the
centre to the endpoint `x` costs a further `1/2` along the axis and nothing across it, so
Pythagoras gives `‖Φ z - x‖² ≤ (1/2 + 3 c/2)² + c²` for `θ ≤ 1`, and `3 (1 + 2 c)` dominates the
square root.  Hence the factor `1 + 2 c` in the radius, and hence in
`Kakeya.ml1Boot.fineNormalizeDilate.C`. -/
private lemma normalization_image_dilate_subset_closedBall {θ : NNReal} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) {c : ℝ} (hc : 0 < c) (T₀ : Tube θ E) :
    T₀.normalization '' (Tube.dilate T₀ c).carrier
      ⊆ Metric.closedBall T₀.x
          ((1 + 2 * c) * (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ)) := by
  rw [Set.image_subset_iff]
  intro z hz
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have hcnonneg : (0 : ℝ) ≤ c := le_of_lt hc
  have hθmod : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  -- centre-based bounds (at the centre of `T₀` rather than at the endpoint `T₀.x`)
  rcases Tube.abs_inner_and_perp_le_of_mem_dilate T₀ hc hz with ⟨hax, hperp⟩
  let u : E := z - T₀.center
  have he : (inner ℝ T₀.direction T₀.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, _root_.Tube.norm_direction T₀]; norm_num
  -- shift the base point from `T₀.center` to `T₀.x`
  have hu : z - T₀.x = u + (1 / 2 : ℝ) • T₀.direction := by
    dsimp [u]
    rw [_root_.Tube.x_eq_center_sub T₀]
    module
  let p : ℝ := inner ℝ T₀.direction (z - T₀.x)
  let q : E := z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction
  have hp_eq : p = inner ℝ T₀.direction u + (1 / 2 : ℝ) := by
    dsimp [p]
    rw [hu, inner_add_right, inner_smul_right, he]
    ring
  have hinc : |inner ℝ T₀.direction u| ≤ c / 2 + c * (θ : ℝ) := by
    simpa [u, real_inner_comm] using hax
  have hp_le : |p| ≤ (1 : ℝ) / 2 + (3 : ℝ) / 2 * c := by
    rw [hp_eq]
    have habs : |inner ℝ T₀.direction u + (1 / 2 : ℝ)|
        ≤ |inner ℝ T₀.direction u| + (1 : ℝ) / 2 := by
      calc
        |inner ℝ T₀.direction u + (1 / 2 : ℝ)| ≤ |inner ℝ T₀.direction u| + |1 / 2| :=
          abs_add_le _ _
        _ = |inner ℝ T₀.direction u| + (1 : ℝ) / 2 := by
          rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hlim : |inner ℝ T₀.direction u| + (1 : ℝ) / 2
        ≤ (1 : ℝ) / 2 + (3 : ℝ) / 2 * c := by
      nlinarith [hinc, hθmod, hcnonneg]
    exact le_trans habs hlim
  have hp2 : p ^ 2 ≤ ((1 : ℝ) / 2 + (3 : ℝ) / 2 * c) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 : ℝ) / 2 + (3 : ℝ) / 2 * c)]
    exact hp_le
  have hperpq : ‖q‖ ≤ c * (θ : ℝ) := by
    dsimp [q]
    rw [hu]
    have hvec : u + (1 / 2 : ℝ) • T₀.direction
        - (inner ℝ T₀.direction (u + (1 / 2 : ℝ) • T₀.direction)) • T₀.direction
        = u - (inner ℝ T₀.direction u) • T₀.direction := by
      rw [inner_add_right, inner_smul_right, he]
      module
    rw [hvec]
    simpa [u] using hperp
  have hcθ0 : (0 : ℝ) ≤ c * (θ : ℝ) := by positivity
  have hq2 : ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ c ^ 2 := by
    have hqsq : ‖q‖ ^ 2 ≤ (c * (θ : ℝ)) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hcθ0]
      exact hperpq
    have hθinvsq : ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 = 1 := by
      have hθne : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
      calc
        ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 = (((θ : ℝ)⁻¹) * (θ : ℝ)) ^ 2 := by ring
        _ = 1 ^ 2 := by rw [inv_mul_cancel₀ hθne]
        _ = 1 := by norm_num
    have hmain : ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (c * (θ : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hqsq (sq_nonneg ((θ : ℝ)⁻¹))
    calc
      ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (c * (θ : ℝ)) ^ 2 := hmain
      _ = c ^ 2 := by
        calc
          ((θ : ℝ)⁻¹) ^ 2 * (c * (θ : ℝ)) ^ 2 = c ^ 2 * (((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2) := by ring
          _ = c ^ 2 := by rw [hθinvsq]; ring
  have hqnorm : ‖T₀.normalization z - T₀.x‖ ≤ 3 * (1 + 2 * c) := by
    rw [← _root_.Tube.normalization_apply_x T₀]
    have hnorm_sq : ‖T₀.normalization z - T₀.normalization T₀.x‖ ^ 2 ≤ (3 * (1 + 2 * c)) ^ 2 := by
      rw [_root_.Tube.norm_sq_normalization_sub T₀ z T₀.x]
      change p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ (3 * (1 + 2 * c)) ^ 2
      have hsum : p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2
          ≤ ((1 : ℝ) / 2 + (3 : ℝ) / 2 * c) ^ 2 + c ^ 2 := by
        nlinarith [hp2, hq2]
      have hdom : ((1 : ℝ) / 2 + (3 : ℝ) / 2 * c) ^ 2 + c ^ 2 ≤ (3 * (1 + 2 * c)) ^ 2 := by
        nlinarith [hcnonneg, sq_nonneg c]
      nlinarith [hsum, hdom]
    have hs3 := sq_le_sq.mp hnorm_sq
    have hnn : (0 : ℝ) ≤ 3 * (1 + 2 * c) := by positivity
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hnn] using hs3
  refine le_trans hqnorm ?_
  have hC3 : (3 : ℝ) ≤ (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
    unfold _root_.Tube.normalization.C
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ Module.finrank ℝ E :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    calc
      (3 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      _ ≤ 1 * (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * (2 : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right hpow (by norm_num)
      _ = (2 : ℝ) ^ (Module.finrank ℝ E + 3) := by rw [pow_add]
      _ = ((2 ^ (Module.finrank ℝ E + 3) : NNReal) : ℝ) := by norm_num
  have hle : (3 : ℝ) * (1 + 2 * c)
      ≤ (1 + 2 * c) * (_root_.Tube.normalization.C (Module.finrank ℝ E) : ℝ) := by
    have h12 : (0 : ℝ) ≤ 1 + 2 * c := by positivity
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hC3 h12
  exact hle

omit [Nontrivial E] in
/-- **A dilate that contains a tube is not much smaller than the tube it dilates.**

The ambient enlargement to `B₁` needs the ambient body bounded *below* in volume, and over a
dilate that means bounding `|T_τ|` by `|c · T_τ| = c³ |T_τ|`, which is vacuous as `c → 0`.  It is
not vacuous here, because `c` cannot be small: a `ρ`-tube inside `c · T_τ` has two points at
distance `1`, and `Tube.dist_le_of_mem_dilate_of_mem_dilate` bounds that distance by
`c + 4 c τ ≤ 5 c`.  So `1/5 ≤ c` is *forced* by the hypotheses rather than assumed, and
`c⁻³ ≤ 125`.

This is why `Kakeya.ml1Boot.exists_fineNormalization_dilate` needs no lower bound on `c`, and
why the third clause of `Kakeya.ml1Boot.fineNormalize_C_dominates_gen` carries a `125`. -/
private lemma volume_ambient_le_mul_volume_dilate (hdim : Module.finrank ℝ E = 3)
    {τ ρ : NNReal} (hτ1 : τ ≤ 1) (Tτ : Tube τ E) {c : ℝ} (hc : 0 ≤ c) (S : Tube ρ E)
    (_hρτ : ρ ≤ τ) (hS : S.carrier ⊆ (Tube.dilate Tτ c).carrier) :
    (1 / 5 : ℝ) ≤ c ∧
      volume Tτ.carrier ≤ 125 * volume (Tube.dilate Tτ c).carrier := by
  have hx : S.x ∈ (Tube.dilate Tτ c).carrier := hS S.x_mem_carrier
  have hyy : S.y ∈ (Tube.dilate Tτ c).carrier := hS S.y_mem_carrier
  have hc_pos : 0 < c := by
    by_contra hc0
    -- if c = 0 the 0-dilate is constant at the centre, so S.x = S.y, contradicting dist = 1
    have hceq : c = 0 := le_antisymm (le_of_not_gt hc0) hc
    have hx0 : S.x ∈ (Tube.dilate Tτ (0 : ℝ)).carrier := by simpa [hceq] using hx
    have hy0 : S.y ∈ (Tube.dilate Tτ (0 : ℝ)).carrier := by simpa [hceq] using hyy
    have hcar : (Tube.dilate Tτ (0 : ℝ)).carrier =
        AffineMap.homothety Tτ.center (0 : ℝ) '' Tτ.carrier :=
      Kakeya.Tube.dilate_carrier Tτ (0 : ℝ)
    have hconst (p : E) : AffineMap.homothety Tτ.center (0 : ℝ) p = Tτ.center := by
      simp
    have hxcent : S.x = Tτ.center := by
      rw [hcar] at hx0
      rcases hx0 with ⟨p, hp, hpx⟩
      rw [← hpx, hconst p]
    have hycent : S.y = Tτ.center := by
      rw [hcar] at hy0
      rcases hy0 with ⟨p, hp, hpy⟩
      rw [← hpy, hconst p]
    have hzero : dist S.x S.y = 0 := by
      rw [hxcent, hycent, dist_self]
    have : (1 : ℝ) = 0 := by
      rw [← S.dist_eq_one, hzero]
    norm_num at this
  have hc_ge : (1 / 5 : ℝ) ≤ c := by
    have hτr : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
    have hd : dist S.x S.y ≤ (c + c) / 2 + 2 * (c + c) * (τ : ℝ) :=
      Tube.dist_le_of_mem_dilate_of_mem_dilate (T := Tτ) (c := c) (c' := c) hc_pos hc_pos hx hyy
    have hd' : (1 : ℝ) ≤ (c + c) / 2 + 2 * (c + c) * (τ : ℝ) := by
      simpa [S.dist_eq_one] using hd
    have hlen : (1 : ℝ) ≤ c + 4 * c * (τ : ℝ) := by
      have hsimp : (c + c) / 2 + 2 * (c + c) * (τ : ℝ) = c + 4 * c * (τ : ℝ) := by ring
      rw [hsimp] at hd'
      exact hd'
    have hτc : 4 * c * (τ : ℝ) ≤ 4 * c := by
      have h4c : 0 ≤ 4 * c := by positivity
      calc
        4 * c * (τ : ℝ) ≤ 4 * c * 1 := mul_le_mul_of_nonneg_left hτr h4c
        _ = 4 * c := by ring
    have hfive : c + 4 * c * (τ : ℝ) ≤ 5 * c := by nlinarith
    have hle5 : (1 : ℝ) ≤ 5 * c := le_trans hlen hfive
    nlinarith
  constructor
  · exact hc_ge
  · -- volume comparison: |T_τ| ≤ 125 · |c · T_τ|
    have hc1 : (1 / 125 : ℝ) ≤ c ^ 3 := by
      have hpk : (1 / 5 : ℝ) ^ 3 ≤ c ^ 3 :=
        pow_le_pow_left₀ (by norm_num : 0 ≤ (1 / 5 : ℝ)) hc_ge 3
      norm_num at hpk
      exact hpk
    have hlin : (1 : ℝ) ≤ 125 * c ^ 3 := by nlinarith
    have hK : (1 : ENNReal) ≤ 125 * ENNReal.ofReal (c ^ 3) := by
      have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (125 * c ^ 3) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hlin
      have hprod : ENNReal.ofReal (125 * c ^ 3) = 125 * ENNReal.ofReal (c ^ 3) := by
        rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (125 : ℝ))]
        norm_num
      simpa [hprod] using h1
    rw [Kakeya.Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety,
      abs_of_pos (pow_pos hc_pos (Module.finrank ℝ E))]
    rw [hdim]
    calc
      volume Tτ.carrier ≤ (125 * ENNReal.ofReal (c ^ 3)) * volume Tτ.carrier := by
        exact le_mul_of_one_le_left (by exact zero_le) hK
      _ = 125 * (ENNReal.ofReal (c ^ 3) * volume Tτ.carrier) := by
        rw [mul_assoc]

/-- **The ambient enlargement to `B₁`, over a dilate: this is where `M` is paid.**

`Kakeya.ml1Boot.exists_fineNormalization_core` asks for its ambient body to fill a definite
fraction of the unit ball after rescaling, and that is a lower bound on `|K|`.  Containment
`K ≤ c · T_τ` alone cannot supply one — take `K` to be a single fibre's own body — which is
exactly why the dilated normalization carries the volume-ratio parameter `M` and the hypothesis
`hKfat`, and why the earlier `M`-free form of that lemma was false.

The chain is: `Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient` compares `B₁` with
the rescaled `T_τ`; `Kakeya.ml1Boot.volume_ambient_le_mul_volume_dilate` descends from `T_τ` to
the `c`-dilate at cost `125`; and `hKfat` descends from the dilate to `K` at cost `M`.  The
rescaling is affine with a constant Jacobian, so it does not change the ratio. -/
private lemma volume_closedBall_one_le_mul_volume_rescale_image_of_dilate
    (hdim : Module.finrank ℝ E = 3) {τ δ : NNReal} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hδτ : δ ≤ τ)
    (Tτ : Tube τ E) {c : ℝ} (hc : 0 ≤ c) {M : NNReal} (K : ConvexSpaceBody E)
    (hK : K.carrier ⊆ (Tube.dilate Tτ c).carrier)
    (hKfat : volume (Tube.dilate Tτ c).carrier ≤ (M : ENNReal) * volume K.carrier)
    (S : Tube δ E) (hS : S.carrier ⊆ K.carrier)
    {R : NNReal} (hR1 : 1 ≤ R) :
    volume (Metric.closedBall (0 : E) 1)
      ≤ ((125 * M * (4 * R) ^ 6 : NNReal) : ENNReal)
        * volume (Tτ.rescaleMap ((R : NNReal) : ℝ) '' K.carrier) := by
  have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
  have hR0 : 0 < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR1'
  have hofR : ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (((4 * R) ^ 6 : NNReal) : ENNReal) := by
    have h4R : ENNReal.ofReal (4 * (R : ℝ)) = ((4 * R : NNReal) : ENNReal) := by
      rw [show (4 : ℝ) * (R : ℝ) = ((4 * R : NNReal) : ℝ) by
        rw [NNReal.coe_mul]
        norm_num]
      rw [ENNReal.ofReal_coe_nnreal]
    have hRnonneg : (0 : ℝ) ≤ 4 * (R : ℝ) := by positivity
    calc
      ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) = (ENNReal.ofReal (4 * (R : ℝ))) ^ 6 := by
            rw [ENNReal.ofReal_pow hRnonneg]
      _ = ((4 * R : NNReal) : ENNReal) ^ 6 := by rw [h4R]
      _ = (((4 * R) ^ 6 : NNReal) : ENNReal) := by
            rw [ENNReal.coe_pow]
  have h1 : volume (Metric.closedBall (0 : E) 1)
      ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) :=
    _root_.Tube.volume_closedBall_one_le_mul_volume_rescale_image_ambient
      (E := E) hdim hτ0 hR1' Tτ
  have hTτ : volume Tτ.carrier ≤ ((125 * M : NNReal) : ENNReal) * volume K.carrier := by
    have hvol := (volume_ambient_le_mul_volume_dilate hdim hτ1 Tτ hc S hδτ (hS.trans hK)).2
    calc
      volume Tτ.carrier ≤ 125 * volume (Tube.dilate Tτ c).carrier := hvol
      _ ≤ 125 * ((M : ENNReal) * volume K.carrier) := by
        gcongr
      _ = ((125 * M : NNReal) : ENNReal) * volume K.carrier := by
        simp [ENNReal.coe_mul, mul_assoc]
  have h2 : volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier)
      ≤ ((125 * M : NNReal) : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) := by
    obtain ⟨L, hL⟩ := _root_.Tube.exists_rescaleEquiv hτ0 hR0 Tτ
    let J : ENNReal := ENNReal.ofReal |LinearMap.det (L.linear : E →ₗ[ℝ] E)|
    have hA := Kakeya.volume_affineImage L Tτ.carrier
    have hB := Kakeya.volume_affineImage L K.carrier
    rw [hL] at hA
    rw [hL] at hB
    have hA' : volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) = J * volume Tτ.carrier := by
      simpa [J] using hA
    have hB' : volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) = J * volume K.carrier := by
      simpa [J] using hB
    calc
      volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) = J * volume Tτ.carrier := hA'
      _ ≤ J * (((125 * M : NNReal) : ENNReal) * volume K.carrier) := by
        exact mul_le_mul' le_rfl hTτ
      _ = (((125 * M : NNReal) : ENNReal) * (J * volume K.carrier)) := by
        rw [mul_left_comm]
      _ = ((125 * M : NNReal) : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) := by
        rw [← hB']
  calc
    volume (Metric.closedBall (0 : E) 1)
        ≤ ENNReal.ofReal ((4 * (R : ℝ)) ^ 6) * volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) := h1
    _ = (((4 * R) ^ 6 : NNReal) : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' Tτ.carrier) := by
      rw [hofR]
    _ ≤ (((4 * R) ^ 6 : NNReal) : ENNReal)
        * (((125 * M : NNReal) : ENNReal) * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier)) := by
      gcongr
    _ = ((125 * M * (4 * R) ^ 6 : NNReal) : ENNReal)
        * volume (Tτ.rescaleMap (R : ℝ) '' K.carrier) := by
      conv_rhs =>
        rw [ENNReal.coe_mul]
      rw [mul_assoc]
      rw [mul_left_comm]

/-- **`Kakeya.ml1Boot.fineNormalize_C_dominates_gen` at the dilated instance.**

The instance is `(R, κ) = ((1 + 2 c) C_N, max 2 (2 c))`, and its coupling hypothesis `κ + 2 ≤ R`
holds for every `c` with room to spare: `max 2 (2 c) + 2 ≤ 4 + 2 c`, while
`(1 + 2 c) C_N = 64 + 128 c`.  No lower bound on `c` is needed. -/
private lemma fineNormalize_C_dominates_dilate (c : NNReal) {c₁ : NNReal}
    (hc₁ : c₁ = _root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (((max 2 (2 * c) : NNReal) : ℝ) + 2)
        * (((1 + 2 * c) * _root_.Tube.normalization.C 3 : NNReal) : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C 3)) :
    c₁ ≤ fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c)) ∧
      ((4 * ((1 + 2 * c) * _root_.Tube.normalization.C 3)) ^ 6 : NNReal) * c₁
        ≤ fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c)) ∧
      (125 : NNReal) * ((4 * ((1 + 2 * c) * _root_.Tube.normalization.C 3)) ^ 12 : NNReal) * c₁
        ≤ fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3) (max 2 (2 * c)) := by
  have hCR : _root_.Tube.normalization.C 3 ≤ (1 + 2 * c) * _root_.Tube.normalization.C 3 := by
    exact le_mul_of_one_le_left' (self_le_add_right 1 (2 * c))
  have hC : _root_.Tube.normalization.C 3 = (64 : NNReal) := by
    norm_num [_root_.Tube.normalization.C]
  have hκ : max 2 (2 * c) ≤ 2 + 2 * c := by
    exact max_le (self_le_add_right 2 (2 * c)) (self_le_add_left (2 * c) 2)
  have hκ2 : max 2 (2 * c) + 2 ≤ 4 + 2 * c := by
    calc
      max 2 (2 * c) + 2 ≤ (2 + 2 * c) + 2 := add_le_add hκ (by norm_num)
      _ = 4 + 2 * c := by ring
  have hRHS : (1 + 2 * c) * _root_.Tube.normalization.C 3 = 64 + 128 * c := by
    rw [hC]
    ring
  have h45 : 4 + 2 * c ≤ 64 + 128 * c := by
    exact add_le_add (by norm_num : (4 : NNReal) ≤ 64)
      (mul_le_mul_left (by norm_num : (2 : NNReal) ≤ 128) c)
  have hκR : max 2 (2 * c) + 2 ≤ (1 + 2 * c) * _root_.Tube.normalization.C 3 := by
    rw [hRHS]
    exact le_trans hκ2 h45
  exact fineNormalize_C_dominates_gen (R := (1 + 2 * c) * _root_.Tube.normalization.C 3)
    (κ := max 2 (2 * c)) hCR hκR hc₁

/-- **Normalizing a fine fibre over a dilate** (blueprint `lem:ml1bootFineNormalizeDilate`).

This is `Kakeya.ml1Boot.exists_fineNormalization` with the containment of the fine tubes and
the ambient body of the Frostman constant both moved to a named body `K ⊆ c · T_τ`, and with
the normalization loss read at the ambient radius `(1 + 2 c) C_N` in place of `C_N` and at the
tilt `max 2 (2 c)` in place of `2`, i.e.
`Kakeya.ml1Boot.fineNormalize.C ((1 + 2 c) C_N) (max 2 (2 c))` in place of
`Kakeya.ml1Boot.fineNormalize.C C_N`.  The hypothesis on `T_τ` is unchanged, and so is the
output scale, which is `Kakeya.ml1Boot.fineScale δ τ` in both.

## The ambient body is a parameter, and `K = c · T_τ`, `M = 1` is the old statement

The fine tubes are asked to lie in `K`, and the Frostman constant on the right-hand side is
read in `K`.  Two things are asked of `K`: the order clause `hK : K ≤ c · T_τ` and the volume
clause `hKfat : |c · T_τ| ≤ M |K|`.  At `K = c · T_τ` and `M = 1` both hold by `le_rfl`, the
Frostman prefactor collapses to `Kakeya.ml1Boot.fineNormalize.C ((1 + 2 c) C_N) (max 2 (2 c))`,
and every clause is the previous one verbatim, so this is a strict generalization and not a
restatement.

It is a genuine strengthening, because `Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient` gives
`C_F(𝕌, K) ≤ C_F(𝕌, c · T_τ)` and never the reverse without paying the volume ratio of
`ConvexSpaceBody.frostmanConstIn_ambient_mono`.  That ratio is exactly what `M` names, and it
is the reason the prefactor of the Frostman clause is `M · C` and not `C`.

## note: why an `M`-free form of this lemma is false

An earlier version of this statement carried only the order clause `K ≤ c · T_τ` and read the
Frostman conclusion at the bare loss `C`.

Work in `E = EuclideanSpace ℝ (Fin 3)` at `c = 2`, `τ = 1/2`, `Λ = 1`, `μ₀ = 1`, `ι = Unit`,
`u = {}`.  Let `T_τ` be the witness of `Kakeya.ml1Boot.exists_halfTube_subset_closedBall`,
let `T ` be `T_τ.rescale δ` shaded by its own carrier, and — this is the point — let
`K := (T ).toConvexSpaceBody`, the single fibre member's own body.  Every hypothesis of the
`M`-free form holds: `hK` by `Tube.subset_dilate`, `hsub` by `le_rfl`, `hED` vacuously on a
singleton, `hdens` because shade equals carrier at `Λ = μ₀ = 1`.

The left side of the refuted conclusion is unbounded and the right side is not.

* `C_F(u, T, K) ≤ 1`.  For `K' ≤ K` either `T  ≰ K'`, and the filtered density is `0`, or
  `T  ≤ K'`, and then `K' = K` because `K` is `T `; so every density is at most
  `Δ(u, T, K) = 1` and `Kakeya.ConvexSpaceBody.frostmanConstIn_le` applies.  The right side is
  therefore at most `C`, a quantity depending only on `c`.
* `C_F(u', V, B₁) ≥ 1 / (8 σ²)` with `σ = Kakeya.ml1Boot.fineScale δ τ = min (δ/τ) (1/4)`.
  Here `u' = u` is forced, and testing at `K' = (V ).toConvexSpaceBody ≤ B₁` in
  `Kakeya.ConvexSpaceBody.le_frostmanConstIn_of_lt_densityIn` gives the ratio
  `|B₁| / |V |`, and `|V | ≤ C_v σ²` by `Kakeya.Tube.volume_le` with
  `Kakeya.Tube.volume_le.C 3 = 16`.

Since `σ ≤ δ/τ = 2 δ`, any `δ` below `min (1/8) (1 / (2 √(8 C)))` contradicts the conclusion.
The obstruction is a **volume ratio**, so no purely order-theoretic hypothesis on `K` can
repair it: the ambient enters `Kakeya.ConvexSpaceBody.densityIn` twice, once by selecting the
admissible test bodies and once as the dividing volume, and `K ≤ c · T_τ` governs only the
first.  Here `|c · T_τ| / |K| ≍ δ^(-2) → ∞`, which is precisely `M` blowing up, so the repaired
statement is *not* contradicted by the witness.

What survives from the earlier sketch is the numerator half, and only that: the route does push
a test body `K'' ⊆ B₁` back through the normalization and meet it with the ambient,
`Φ⁻¹(K'') ⊓ K ≤ K`, which is admissible in `C_F(𝕌, K)` and contains every member of the family
that `K''` sees — the step isolated as `ConvexSpaceBody.densityIn_le_densityIn_inter`, whose
hypothesis is exactly `hsub`.  It is also true that shrinking the ambient below the dilate only
shrinks the image whose radius `(1 + 2 c) C_N` bounds, so the tilt bound and the normalized
radius, and hence both summands of the *geometric* loss, are unchanged.  What that sketch
omitted is the denominator: the conclusion divides by `|B₁|` where the hypothesis divides by
`|K|`, and the affine normalization converts that mismatch into the factor `|c · T_τ| / |K|`.
The multiplicity and fullness clauses have no ambient volume anywhere and so carry no `M`.

The clause `K ≤ c · T_τ` cannot be dropped either: with an unrelated `K` the tilt bound
`Tube.perp_norm_core_sub_le_of_subset_dilate` and the ambient radius are both unavailable, and
the geometric loss would have nothing to be stated at.

## The dilation ratio is free

The ratio `c` is a parameter and no step of the argument pins it.  It enters in exactly three
places: as the name of the ambient body `c · T_τ` in the containment hypothesis and in the
Frostman conclusion, through the normalized ambient radius `(1 + 2 c) C_N` at which the
normalization loss is read, and through the tilt `max 2 (2 c)` at which that same loss is read.
The radius factor `1 + 2 c` and the tilt are both justified at
`Kakeya.ml1Boot.fineNormalizeDilate.C`, and both are safe for every `c ≥ 0`; the ratio-`2`
instance, which is the one the chain of `Kakeya.ml1Boot.reduceToTb_fine_factor_dilate` uses,
reads them at `5 C_N` and `4`.

Making the constant grow with `c` in the tilt as well as in the radius is what makes the
statement **self-consistent at free `c`**: the selection constant of the route it takes is
`Tube.essDistinctTubesInSelfDilate.C 3 (4 (κ + 2) R C_n)` at `κ = 2 c`, which grows like
`c ^ 12`, and until the tilt was threaded through
`Kakeya.ml1Boot.fineNormalize.C` the stated constant did not see `c` at all beyond the radius
— so for large `c` the conclusions could not have held at it.  This is blueprint
`section8_finenormalize_core.tex` lines 62-76 and obligation `item:fineNormOwedConstant`.

## The output scale

As in `Kakeya.ml1Boot.exists_fineNormalization`, the output scale is
`fineScale δ τ = min (δ/τ) (1/4)` and not the bare ratio `δ / τ`.  With `δ / τ` this statement
is **false**, refuted by `Kakeya.ml1Boot.not_exists_fineNormalization_dilate` on the same
witness at `δ = τ = 1/2`; the containment hypothesis there is the weaker one, so that
refutation is if anything easier than its twin.  The truncation is invisible downstream, for
the reasons given at `Kakeya.ml1Boot.exists_fineNormalization`.

## Proof status

**Proved**, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]`: no `sorryAx`.

The proof is an instantiation of `Kakeya.ml1Boot.exists_fineNormalization_core` at
`(P, R, κ) = (K, (1 + 2 c) C_N, max 2 (2 c))`, which is the reading of this lemma that the "not
a corollary" section below describes.  Its four ambient hypotheses are supplied by, in order,
`Kakeya.ml1Boot.normalization_image_dilate_subset_closedBall` (the radius
`Φ_{T_τ}(c · T_τ) ⊆ B̄(x, (1 + 2 c) C_N)`),
`Kakeya.ml1Boot.dist_normalization_core_le_of_subset_dilate` (the image-core length),
`Kakeya.ml1Boot.perp_norm_direction_le_of_subset_dilate` (the tilt, blueprint
`lem:ml1bootFineNormalizeDilateTilt`), and
`Kakeya.ml1Boot.volume_closedBall_one_le_mul_volume_rescale_image_of_dilate` (the ambient
enlargement to `B₁`, which is where `M` is paid).  The constants are then dominated by
`Kakeya.ml1Boot.fineNormalize_C_dominates_dilate`.

Two points in that list are worth keeping visible.

First, the tilt.  `Tube.normalization_distortion` bounds the tilt of the core of `T i` against
the axis of `T_τ` from containment *in `T_τ`*, and the corresponding bound for `T i ⊆ c · T_τ` —
a unit segment whose endpoints lie within `c τ` of the axis has `sin θ ≤ 2 c τ` against `2 τ` —
is a different computation.  It is `Tube.perp_norm_core_sub_le_of_subset_dilate`, proved at a
free dilation ratio with bound `2 c θ`, hence `4 τ` at `c = 2`, and it turned out to be a
two-line corollary of `Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate`, so the
tilt bound itself costs nothing.  What it does cost is the selection constant it feeds, which is
why `Kakeya.ml1Boot.fineNormalize.C` is read at `max 2 (2 c)` here.

Second, the packaged distortion structure is *unavailable* at large `c`, and that is why the
core lemma exists in the form it does.  `Tube.rescale_outer_tube` consumes
`Tube.IsNormalizationDistortion`, whose field `dist_le_C` asserts that the image core has length
at most `C_N = 64`; over a `c`-dilate that length is `√(1 + 4 c²)`, which exceeds `64` once
`c > 31.99…`, while `c` is unquantified here.  The route needs only `dist ≤ R` at its own radius
`R = (1 + 2 c) C_N`, so `Kakeya.ml1Boot.rescale_outer_tube_of_dist_le` restates
`Tube.rescale_outer_tube` with that field freed — the other field it uses,
`image_subset_cthickening`, is supplied unconditionally by
`Tube.normalization_image_subset_cthickening`.  No *restatement* of
`Tube.normalization_distortion` is owed: an earlier version of this paragraph recorded one, at a
unit-length sub-segment, and that reading is false (blueprint `note:tubeNormalizationNotTubes`).

The enlarged constant `Kakeya.ml1Boot.fineNormalizeDilate.C c` is a separate quantity:
its homothety ratio is `4 (1 + 2 c) C_N`, where the `4` is what the core lemma pays to keep the
unit-length extension of an image core inside `B₁` and the `1 + 2 c` is a bound for the growth
of the normalized ambient ball under the `c`-dilate; the selection ratio `4 (κ + 2) R C_n` at
`κ = max 2 (2 c)` is a different quantity and is carried by the second summand of
`Kakeya.ml1Boot.fineNormalize.C`.

## Not a corollary of the undilated half

Sharing its whole route with `Kakeya.ml1Boot.exists_fineNormalization` does *not* make this
lemma derivable from it.  The two are siblings, not parent and child: each is
`Kakeya.ml1Boot.exists_fineNormalization_core` (blueprint `lem:ml1bootFineNormalizeCore`)
instantiated at an ambient body `P` and a normalized ambient radius `R`, at `(T_τ, C_N)` there
and at `(K, (1 + 2 c) C_N)` here with `K ≤ c · T_τ`.

What blocks the derivation is the hypothesis pair `hsub`, `hTτ` of the undilated form (the
obstruction is written out at the ratio `2`, which is the instance the chain uses).  To
invoke it here one would need a scale `τ'` and an honest `τ'`-tube `T'` with `T i ⊆ T'` for
every `i ∈ u` and `T' ⊆ B₁`, and no such `T'` exists:

* a fine tube in `2 · T_τ` need not lie in `B₁` at all.  Take `T_τ` centred at the origin with
  unit core direction `v`, and `w` a unit vector orthogonal to `v`.  The `δ`-tube with core
  `[(2 τ - δ) • w, v + (2 τ - δ) • w]` lies in `2 · T_τ`, since its core runs parallel to the
  core `[-v, v]` of the dilate at transverse distance `2 τ - δ ≥ 0`; and it contains
  `v + 2 τ • w`, at distance `√(1 + 4 τ²) > 1` from the origin.  So `T' ⊆ B₁` fails already for
  a single member of the family, for every `0 < δ ≤ τ`;
* and even for families placed inside `B₁` the containment can span the dilate axially, forcing
  `T'` to have diameter `1 + 2 τ' ≥ 2 + 4 τ`, hence `τ' > 1/2`, which
  `Kakeya.ml1Boot.tube_not_subset_closedBall_of_half_lt` forbids inside `B₁`.  This is the
  "nor does enlarging the scale" paragraph of blueprint `note:ml1bootDilateSplitNotEnough`.

Dropping the members that leave `B₁` is not a repair: the multiplicity and fullness clauses are
read on all of `u`, and only the output family is selected.  Splitting `2 · T_τ` into honest
tubes is specified out by the same note, at a cost polynomial in the tube scale. -/
theorem exists_fineNormalization_dilate (hdim : Module.finrank ℝ E = 3) (c : NNReal)
    {δ τ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1)
    {Λ : NNReal} (hΛ : 1 ≤ Λ) {μ₀ : ENNReal} (hμ₀ : 0 < μ₀)
    {ι : Type*} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
    (K : ConvexSpaceBody E) (M : NNReal) (hM : 1 ≤ M)
    (hu : u.Nonempty)
    {R : ℝ} (hTτ : Tτ.carrier ⊆ Metric.closedBall 0 R)
    (hK : K ≤ Tube.dilate Tτ (c : ℝ))
    (hKfat : volume (Tube.dilate Tτ (c : ℝ)).carrier ≤ (M : ENNReal) * volume K.carrier)
    (hsub : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ K)
    (hED : (u : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hdens : ∀ i ∈ u, (Λ : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ (Λ : ENNReal) * μ₀ * volume (T i).carrier) :
    ∃ u' ⊆ u, u'.Nonempty ∧ ∃ V : ι → ShadedTube (fineScale δ τ) E,
      (u' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
        (∀ i ∈ u', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
              (max 2 (2 * c)) : ENNReal)
            * (Λ : ENNReal) ^ 2
            * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) ∧
        (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          ≤ (fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
              (max 2 (2 * c)) : ENNReal)
            * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) ∧
        frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (M : ENNReal)
            * (fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
              (max 2 (2 * c)) : ENNReal)
            * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := by
  classical
  have _ := hTτ -- `T_τ ⊆ B₁` is genuinely unused by the core (which no longer asks for it)
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  let i₀ : ι := Classical.choose hu
  have hi₀ : i₀ ∈ u := Classical.choose_spec hu
  set CN : NNReal := _root_.Tube.normalization.C 3 with hCN
  set Rd : NNReal := (1 + 2 * c) * CN with hRd
  have hCN1 : 1 ≤ CN := _root_.Tube.normalization.one_le_C 3
  have hCN1' : (1 : ℝ) ≤ (_root_.Tube.normalization.C 3 : ℝ) := by
    exact_mod_cast hCN1
  -- (1) containment
  have hsubK : ∀ i ∈ u, (T i).carrier ⊆ K.carrier := by
    intro i hi
    change (T i).toConvexSpaceBody ≤ K
    exact hsub i hi
  have hKc : K.carrier ⊆ (Tube.dilate Tτ (c : ℝ)).carrier := by
    change K ≤ Tube.dilate Tτ (c : ℝ)
    exact hK
  have hsubD : ∀ i ∈ u, (T i).carrier ⊆ (Tube.dilate Tτ (c : ℝ)).carrier := fun i hi =>
    (hsubK i hi).trans hKc
  -- (2) c is positive
  have hc0 : 0 < (c : ℝ) := by
    have h := (volume_ambient_le_mul_volume_dilate hdim hτ1 Tτ c.coe_nonneg (T i₀).toTube
      hδτ (hsubD i₀ hi₀)).1
    linarith
  -- (3) radius bounds
  have hR : _root_.Tube.normalization.C 3 ≤ Rd := by
    rw [hRd]
    exact le_mul_of_one_le_left' (self_le_add_right 1 (2 * c))
  have hRd1 : (1 : NNReal) ≤ Rd := le_trans hCN1 hR
  have hrad : (1 + 2 * (c : ℝ)) * (_root_.Tube.normalization.C 3 : ℝ) = (Rd : ℝ) := by
    rw [hRd, NNReal.coe_mul]
    have h1 : (1 + 2 * (c : ℝ)) = ↑(1 + 2 * c : NNReal) := by simp
    have h2 : (_root_.Tube.normalization.C 3 : ℝ) = (CN : ℝ) := by rfl
    rw [h1, h2]
  -- (4) ambient ball
  have hball : Tτ.normalization '' K.carrier ⊆ Metric.closedBall Tτ.x (Rd : ℝ) := by
    have h := normalization_image_dilate_subset_closedBall hτ0 hτ1 hc0 Tτ
    rw [hdim] at h
    rw [hrad] at h
    exact (Set.image_mono hKc).trans h
  -- (5) length
  have hlen : ∀ i ∈ u, dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ (Rd : ℝ) := by
    intro i hi
    have h := dist_normalization_core_le_of_subset_dilate hτ0 hτ1 hc0 Tτ (T i).toTube (hsubD i hi)
    calc
      dist (Tτ.normalization (T i).x) (Tτ.normalization (T i).y) ≤ 1 + 2 * (c : ℝ) := h
      _ ≤ (Rd : ℝ) := by
        rw [← hrad]
        exact le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ 1 + 2 * (c : ℝ)) hCN1'
  -- (6) tilt
  have hperp : ∀ i ∈ u, ‖(T i).toTube.direction
      - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
      ≤ ((max 2 (2 * c) : NNReal) : ℝ) * (τ : ℝ) := by
    intro i hi
    have h := perp_norm_direction_le_of_subset_dilate hc0 Tτ (T i).toTube (hsubD i hi)
    calc
      ‖(T i).toTube.direction
          - (inner ℝ Tτ.direction (T i).toTube.direction : ℝ) • Tτ.direction‖
          ≤ 2 * (c : ℝ) * (τ : ℝ) := h
      _ ≤ ((max 2 (2 * c) : NNReal) : ℝ) * (τ : ℝ) := by
        have h2c : (2 : ℝ) * (c : ℝ) ≤ ((max 2 (2 * c) : NNReal) : ℝ) := by
          have h : (2 * c : NNReal) ≤ max (2 : NNReal) (2 * c) :=
            le_max_right (2 : NNReal) (2 * c)
          exact_mod_cast h
        exact mul_le_mul_of_nonneg_right h2c (NNReal.coe_nonneg τ)
  -- (7) volume of K nonzero
  have hPvol : volume K.carrier ≠ 0 := by
    have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
    have hSpos : 0 < volume ((T i₀).toShadedBody).carrier := by
      have hprod : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
        exact ENNReal.mul_pos
          (ENNReal.coe_ne_zero.mpr (ne_of_gt (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))))
          (pow_ne_zero (Module.finrank ℝ E - 1) (ENNReal.coe_ne_zero.mpr (ne_of_gt hδ)))
      exact lt_of_lt_of_le hprod (by simpa using (_root_.Tube.le_volume (T i₀).toTube))
    have hmono : volume (T i₀).toShadedBody.carrier ≤ volume K.carrier := by
      exact measure_mono (by simpa using hsubK i₀ hi₀)
    exact ne_of_gt (lt_of_lt_of_le hSpos hmono)
  -- (8) ratio
  have hratio : volume (Metric.closedBall (0 : E) 1)
      ≤ ((125 * M * (4 * Rd) ^ 6 : NNReal) : ENNReal)
        * volume (Tτ.rescaleMap (Rd : ℝ) '' K.carrier) :=
    volume_closedBall_one_le_mul_volume_rescale_image_of_dilate
      hdim hτ0 hτ1 hδτ Tτ c.coe_nonneg K hKc hKfat (T i₀).toTube (hsubK i₀ hi₀) hRd1
  -- (9) core
  obtain ⟨u', hu'sub, hu'ne, V, hVD, hVball, hmult, hfull, hfrost, -, -, -, -⟩ :=
    exists_fineNormalization_core hdim hδ hδτ hτ1 hΛ hμ₀ Tτ T K
      (R := Rd) (κ := max 2 (2 * c)) (Cw := 125 * M * (4 * Rd) ^ 6)
      hR hu hsubK hball hlen hperp hPvol hratio hED hdens
  -- (10) the three clauses
  let c₁ : NNReal := _root_.Tube.essDistinctTubesInSelfDilate.C 3
    (4 * (((max 2 (2 * c) : NNReal) : ℝ) + 2) * ((Rd : NNReal) : ℝ)
      * Kakeya.Tube.tubeOverlapCoreClose.C 3)
  obtain ⟨hd1, hd2, hd3⟩ := fineNormalize_C_dominates_dilate c (c₁ := c₁) rfl
  refine ⟨u', hu'sub, hu'ne, V, hVD, hVball, ?_, ?_, ?_⟩
  · calc
      ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
              * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
            simpa [c₁] using hmult
      _ ≤ (fineNormalize.C Rd (max 2 (2 * c)) : ENNReal) * (Λ : ENNReal) ^ 2
              * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
            gcongr
  · calc
      (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal)
          ≤ (((4 * Rd) ^ 6 : NNReal) : ENNReal) * (c₁ : ENNReal) * (Λ : ENNReal) ^ 2
              * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
            simpa [c₁] using hfull
      _ ≤ (fineNormalize.C Rd (max 2 (2 * c)) : ENNReal) * (Λ : ENNReal) ^ 2
              * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
            gcongr
            exact_mod_cast hd2
  · calc
      frostmanConstIn u' (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
          ≤ (c₁ : ENNReal) * (((4 * Rd) ^ 6 : NNReal) : ENNReal)
              * ((125 * M * (4 * Rd) ^ 6 : NNReal) : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := by
            simpa [c₁] using hfrost
      _ ≤ (M : ENNReal) * (fineNormalize.C Rd (max 2 (2 * c)) : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := by
            have hcoeff : (c₁ : ENNReal) * (((4 * Rd) ^ 6 : NNReal) : ENNReal)
                * ((125 * M * (4 * Rd) ^ 6 : NNReal) : ENNReal)
                ≤ (M : ENNReal) * (fineNormalize.C Rd (max 2 (2 * c)) : ENNReal) := by
              rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
              have hdom : (c₁ * (4 * Rd) ^ 6 * (125 * M * (4 * Rd) ^ 6) : NNReal)
                  ≤ (M * fineNormalize.C Rd (max 2 (2 * c)) : NNReal) := by
                calc
                  (c₁ * (4 * Rd) ^ 6 * (125 * M * (4 * Rd) ^ 6) : NNReal)
                      = c₁ * ((4 * Rd) ^ 6 * (4 * Rd) ^ 6) * (125 * M) := by ring
                  _ = c₁ * (4 * Rd) ^ 12 * (125 * M) := by
                        have hcomb : (4 * Rd) ^ 6 * (4 * Rd) ^ 6 = (4 * Rd) ^ 12 := by
                          rw [← pow_add]
                        rw [hcomb]
                  _ = M * (125 * (4 * Rd) ^ 12 * c₁) := by ring
                  _ ≤ M * fineNormalize.C Rd (max 2 (2 * c)) := by
                        exact mul_le_mul_of_nonneg_left hd3 (by positivity : (0 : NNReal) ≤ M)
              exact_mod_cast hdom
            gcongr

/-- **The fine fibre over a dilate satisfies the hypotheses of
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`** (blueprint
`lem:ml1bootFineGenKFDilate`).

Word for word `Kakeya.ml1Boot.fine_genKF`, with
`Kakeya.ml1Boot.exists_fineNormalization_dilate` in place of
`Kakeya.ml1Boot.exists_fineNormalization` and `Kakeya.ml1Boot.fineNormalizeDilate.C c` in place
of `Kakeya.ml1Boot.fineFactor.C`.

The ambient body `K` is a parameter, exactly as in the normalization leaf: containment and the
Frostman hypothesis are both read in it, and `Kakeya.ml1Boot.IsFineFibreDilate` asks
`K ≤ c · T_τ` together with the volume clause `|c · T_τ| ≤ M |K|`.  Nothing in this proof looks
at `K` beyond forwarding it, and the conclusion does not mention it.  The fullness threshold
`ηs` is the *same* parameter as there: it is produced by `K_F(γ)` and does not see the family —
in particular it does not see the dilation ratio `c`, which is free here and is passed straight
to the normalization leaf.

## Where `M` goes

The normalization leaf returns its Frostman clause at `M · C₀`, not `C₀` (the reason is the
counterexample note at `Kakeya.ml1Boot.exists_fineNormalization_dilate`).  Rather than push `M`
into this lemma's conclusion, the hypothesis divides by `M · C₃(c)`: the caller is free in `Cf`
and simply names an `M` times larger one, which is why
`Kakeya.ml1Boot.reduceToTb_fine_bound_dilate` pays the ratio in its *loss prefactor* and not in
its Frostman hypothesis (a).  The conclusion of this lemma is therefore unchanged, `M` and all.
`1 ≤ M` is asked because the division must be by something nonzero; it costs a caller nothing,
being forced by `K ≤ c · T_τ` whenever `|K|` is positive and finite.

The quantifier order is unchanged, so `Cf` is quantified inside the `∀ᶠ δ` and may be
`δ`-dependent; `Kakeya.ml1Boot.reduceToTb_fine_bound_dilate` applies the lemma at
`Cf = 2 C_T M C₃ δ̃ ^ (-2 η')`.  The exponent in `Cf ^ (1 - γ/2)` must not be collapsed here:
it is bounded by `Cf` once, at the very end of that lemma's proof, for a `Cf` that no longer
depends on the family. -/
theorem fine_genKF_dilate (hdim : Module.finrank ℝ E = 3) (c : NNReal) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ εs > (0 : ℝ), ∃ ηs > (0 : ℝ), ∀ Λ : NNReal, 1 ≤ Λ →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ Cf : ENNReal, 1 ≤ Cf → Cf ≠ ⊤ →
    ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
      ∀ {ι : Type u} {u : Finset ι} (Tτ : Tube τ E) (T : ι → ShadedTube δ E)
        (K : ConvexSpaceBody E) (M : NNReal) {R : ℝ} {μ₀ : ENNReal}, 1 ≤ M →
        IsFineFibreDilate c R K M Λ μ₀ ηs u Tτ T →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
          ≤ Cf / ((M : ENNReal) * (fineNormalizeDilate.C c : ENNReal)) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (fineNormalizeDilate.C c : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs)
            * Cf ^ (1 - γ / 2)
            * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro εs hεs
  have hn : 1 < Module.finrank ℝ E := by
    rw [hdim]
    norm_num
  obtain ⟨ηs, hηs_pos, hηs_ev⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn E hγ0 hγ1 hn hKF εs hεs
  refine ⟨ηs, hηs_pos, ?_⟩
  intro Λ hΛ1
  filter_upwards [hηs_ev, self_mem_nhdsWithin, eventually_le_quarter] with δ hδ_aux hδ_pos hδ4
  intro Cf hCf1 hCftop τ hδτ hτ1 ι u Tτ T K M R μ₀ hM hfib hF
  obtain ⟨hμ₀, hu, hTτ, hKle, hKfat, hsub, hED, hdens, hFull⟩ := hfib
  rcases exists_fineNormalization_dilate hdim c hδ_pos hδτ hτ1 hΛ1 hμ₀ Tτ T K M hM hu hTτ hKle
    hKfat hsub hED hdens with ⟨u', hu'u, hu'_ne, V, hV_ED, hV_ball, hmult, hfull, hF'⟩
  have hτ_pos : 0 < τ := lt_of_lt_of_le hδ_pos hδτ
  have hσ_le_one : fineScale δ τ ≤ 1 := by
    exact le_trans ((fineScale_bounds hδτ hτ_pos).2.1) (by
      exact_mod_cast (by norm_num : (1 / 4 : ℝ) ≤ (1 : ℝ)))
  have hδ_le_σ : δ ≤ fineScale δ τ := le_fineScale hδ4 hτ1 hτ_pos
  let C₀ : NNReal := fineNormalize.C ((1 + 2 * c) * _root_.Tube.normalization.C 3)
    (max 2 (2 * c))
  let ι' : Type u := {i : ι // i ∈ u'}
  let s' : Finset ι' := u'.attach
  let V' : ι' → ShadedTube (fineScale δ τ) E := fun i => V i.1
  have hV'_ball : ∀ i ∈ s', (V' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    exact hV_ball i.1 i.2
  have hs'_ne : s'.Nonempty := by
    rcases hu'_ne with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩⟩
  have hV'_ED : (s' : Set ι').Pairwise
      (fun i j => IsEssentiallyDistinct (V' i).carrier (V' j).carrier) := by
    intro i hi j hj hij
    exact hV_ED i.2 j.2 (by
      intro h
      exact hij (Subtype.ext h))
  have hC0one : (1 : NNReal) ≤ C₀ := by
    exact one_le_fineNormalize_C (one_le_mul (self_le_add_right 1 (2 * c))
      (_root_.Tube.normalization.one_le_C 3))
  have hC0pos : 0 < (C₀ : ENNReal) := by
    exact ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one hC0one)
  have hC0 : (C₀ : ENNReal) ≠ 0 := ne_of_gt hC0pos
  have hC0top : (C₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hM0 : (M : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hM))
  have hC3_0 : (fineNormalizeDilate.C c : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_fineNormalizeDilate_C c)))
  have hD0 : (M : ENNReal) * (fineNormalizeDilate.C c : ENNReal) ≠ 0 := mul_ne_zero hM0 hC3_0
  have hDtop : (M : ENNReal) * (fineNormalizeDilate.C c : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hΛ0 : (Λ : ENNReal) ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ1))
  have hΛtop : (Λ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCΛ2 : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 ≠ 0 := by
    exact mul_ne_zero hC0 (pow_ne_zero 2 hΛ0)
  have hCΛ2top : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 ≠ ⊤ := by
    exact ENNReal.mul_ne_top hC0top (ENNReal.pow_ne_top hΛtop)
  have hFull_u' : (δ : ENNReal) ^ ηs
      ≤ (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
    have hstep : (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
        ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
          * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
      calc
        (C₀ : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
            ≤ (fineNormalizeDilate.C c : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs := by
            gcongr
            exact_mod_cast fineNormalize_C_le_fineNormalizeDilate_C c
        _ ≤ (ShadedBody.fullness u (fun i => (T i).toShadedBody) : ENNReal) := hFull
        _ ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
            * (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := hfull
    exact (ENNReal.mul_le_mul_iff_right hCΛ2 hCΛ2top).1 hstep
  have hfull_eq : (ShadedBody.fullness s' (fun i => (V' i).toShadedBody) : ENNReal)
      = (ShadedBody.fullness u' (fun i => (V i).toShadedBody) : ENNReal) := by
    rw [ShadedBody.fullness_def, ShadedBody.fullness_def]
    congr 1
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).shade)
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).carrier)
  have hV'_full : (δ : ENNReal) ^ ηs
      ≤ (ShadedBody.fullness s' (fun i => (V' i).toShadedBody) : ENNReal) := by
    rw [hfull_eq]
    exact hFull_u'
  have hCD : (C₀ : ENNReal) ≤ (fineNormalizeDilate.C c : ENNReal) := by
    exact_mod_cast fineNormalize_C_le_fineNormalizeDilate_C c
  have hMCD : (M : ENNReal) * (C₀ : ENNReal)
      ≤ (M : ENNReal) * (fineNormalizeDilate.C c : ENNReal) := by
    exact mul_le_mul_right hCD (M : ENNReal)
  have hFrost_u' : IsFrostmanIn u' (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall Cf := by
    apply isFrostmanIn_of_frostmanConstIn_le
    calc
      frostmanConstIn u' (fun i => (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
          ≤ (M : ENNReal) * (C₀ : ENNReal)
              * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := hF'
      _ ≤ (M : ENNReal) * (C₀ : ENNReal)
            * (Cf / ((M : ENNReal) * (fineNormalizeDilate.C c : ENNReal))) := by
          exact mul_le_mul_right hF ((M : ENNReal) * (C₀ : ENNReal))
      _ ≤ (M : ENNReal) * (fineNormalizeDilate.C c : ENNReal)
            * (Cf / ((M : ENNReal) * (fineNormalizeDilate.C c : ENNReal))) := by
          exact mul_le_mul_left hMCD
            (Cf / ((M : ENNReal) * (fineNormalizeDilate.C c : ENNReal)))
      _ = Cf := by rw [ENNReal.mul_div_cancel hD0 hDtop]
  have he : Set.BijOn (fun i : ι' => i.1) (s' : Set ι') (u' : Set ι) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact i.2
    · intro i hi j hj hij
      exact Subtype.ext hij
    · intro i hi
      exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩, rfl⟩
  have hFrost_s' : IsFrostmanIn s' (fun i => (V' i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall Cf := by
    have h' : IsFrostmanIn s' (fun i => (V i.1).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall Cf :=
      (IsFrostmanIn.reindex (s := u') (t := s') (W := fun i => (V i).toConvexSpaceBody)
        (K := ConvexSpaceBody.closedUnitBall) (C := Cf) he).2 hFrost_u'
    simpa [V'] using h'
  have hmult' : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
        * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((s'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
            ^ (1 - γ / 2) := by
    exact hδ_aux Cf hCf1 hCftop (fineScale δ τ) hδ_le_σ hσ_le_one s' V' hs'_ne hV'_ball hV'_ED
      hV'_full hFrost_s'
  have hmult_eq : ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
      = ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div]
    congr 1
    · simpa [s', V'] using Finset.sum_attach u' (fun i => volume ((V i).toShadedBody).shade)
    · apply congrArg volume
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨i, hi, hx⟩
        exact ⟨i.1, i.2, hx⟩
      · intro hx
        rw [Set.mem_iUnion₂] at hx ⊢
        rcases hx with ⟨i, hi, hx⟩
        exact ⟨⟨i, hi⟩, Finset.mem_attach u' ⟨i, hi⟩, hx⟩
  have hcard_s' : s'.card = u'.card := by
    change (u'.attach).card = u'.card
    exact Finset.card_attach
  have hmult'_u' : ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
        * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
        * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    rw [← hmult_eq]
    calc
      ShadedBody.multiplicity s' (fun i => (V' i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((s'.card : ENNReal)
                * ((fineScale δ τ : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1))
                ^ (1 - γ / 2) := hmult'
      _ = (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ))
                ^ (1 - γ / 2) := by
          rw [hcard_s', hdim]
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hcard_le : (u'.card : ENNReal) ≤ (u.card : ENNReal) := by
    exact_mod_cast (Finset.card_le_card hu'u)
  have hmult'' : ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
        * (16 * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
    calc
      ShadedBody.multiplicity u' (fun i => (V i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * ((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ))
                ^ (1 - γ / 2) := hmult'_u'
      _ = (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * (((fineScale δ τ : NNReal) : ENNReal) ^ (-2 * γ)
              * ((u'.card : ENNReal) * ((fineScale δ τ : NNReal) : ENNReal) ^ (2 : ℕ))
                ^ (1 - γ / 2)) := by
            ring
      _ ≤ (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * (16 * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
              * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ))
                ^ (1 - γ / 2)) := by
            exact mul_le_mul_right (fineScale_bracket_le hδ_pos hδτ hτ_pos hγ0 hγ1 u'.card)
              ((δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2))
  have h16 : (16 : ENNReal) * (C₀ : ENNReal) = (fineNormalizeDilate.C c : ENNReal) := by
    change ((16 : NNReal) : ENNReal) * (C₀ : ENNReal) = (fineNormalizeDilate.C c : ENNReal)
    rw [← ENNReal.coe_mul]
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
          * ShadedBody.multiplicity u' (fun i => (V i).toShadedBody) := hmult
    _ ≤ (C₀ : ENNReal) * (Λ : ENNReal) ^ 2
          * ((δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
            * (16 * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
              * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ))
                ^ (1 - γ / 2))) := by
          exact mul_le_mul_right hmult'' ((C₀ : ENNReal) * (Λ : ENNReal) ^ 2)
    _ = (16 * (C₀ : ENNReal)) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs) * Cf ^ (1 - γ / 2)
          * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          ring
    _ = (fineNormalizeDilate.C c : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs)
          * Cf ^ (1 - γ / 2) * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((u'.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          rw [h16]
    _ ≤ (fineNormalizeDilate.C c : ENNReal) * (Λ : ENNReal) ^ 2 * (δ : ENNReal) ^ (-εs)
          * Cf ^ (1 - γ / 2) * (((δ / τ : NNReal)) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * (((δ / τ : NNReal)) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr

end FineDilate

/-! ### Case (ii): the coarse-scale factor -/

section Coarse

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A parent family induces a finite partition** (blueprint `lem:parentFamilyFinpartition`).

If `(t, 𝕍_ρ, p)` is a parent family for `𝕍 = (V i)_{i ∈ s}` with `p` surjective from `s` onto
`t`, then the fibres `s[k] = Kakeya.ml1Boot.fibre s p k`, `k ∈ t`, are the parts of a
`Finpartition` of `s`, the map `k ↦ s[k]` is a bijection from `t` onto those parts, and
`V i ≤ V_{ρ,k}` for `i ∈ s[k]`.

This is the bookkeeping that lets `ConvexSpaceBody.IsFrostmanIn.inherited_upwards`, which
consumes a `Finpartition` and returns a family indexed by its *parts*, be applied to a parent
family, which is indexed by `t`.  The blueprint's scale ordering `0 < σ ≤ ρ ≤ 1` is inert
here, as it is for `Kakeya.ml1Boot.IsParentFamily` itself. -/
theorem IsParentFamily.finpartition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {σ ρ : NNReal} {s : Finset ι} {t : Finset κ} {V : ι → Tube σ E} {Vρ : κ → Tube ρ E}
    {p : ι → κ} (h : IsParentFamily s V t Vρ p) (hsurj : Set.SurjOn p s t) :
    ∃ P : Finpartition s,
      Set.BijOn (fun k => fibre s p k) t P.parts ∧
        (∀ k ∈ t, (fibre s p k).Nonempty) ∧
        ∀ k ∈ t, ∀ i ∈ fibre s p k,
          (V i).toConvexSpaceBody ≤ (Vρ k).toConvexSpaceBody := by
  let parts : Finset (Finset ι) := t.image fun k => fibre s p k
  let P : Finpartition s :=
    Finpartition.mk parts
      (by
        rw [Finset.supIndep_iff_pairwiseDisjoint]
        intro a ha b hb hab
        rcases Finset.mem_image.mp ha with ⟨ka, hka, rfl⟩
        rcases Finset.mem_image.mp hb with ⟨kb, hkb, rfl⟩
        change Disjoint (fibre s p ka) (fibre s p kb)
        rw [Finset.disjoint_left]
        intro i hi hikb
        have hka' : p i = ka := (Finset.mem_filter.mp hi).2
        have hkb' : p i = kb := (Finset.mem_filter.mp hikb).2
        exact hab (by rw [hka'.symm.trans hkb']))
      (by
        ext i
        constructor
        · intro hi
          rcases Finset.mem_sup.mp hi with ⟨a, ha, hia⟩
          rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
          exact (Finset.mem_filter.mp hia).1
        · intro his
          apply Finset.mem_sup.mpr
          refine ⟨fibre s p (p i), ?_, ?_⟩
          · apply Finset.mem_image.mpr
            exact ⟨p i, h.mapsTo i his, rfl⟩
          · exact Finset.mem_filter.mpr ⟨his, rfl⟩)
      (by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨k, hk, hke⟩
        rcases hsurj hk with ⟨i, his, hik⟩
        have hi : i ∈ fibre s p k := Finset.mem_filter.mpr ⟨his, hik⟩
        simp [hke] at hi)
  refine ⟨P, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · intro ka hka kb hkb hfib
      change fibre s p ka = fibre s p kb at hfib
      rcases hsurj hka with ⟨i, his, hik⟩
      have hikb : p i = kb := by
        have hi : i ∈ fibre s p kb := by
          rw [← hfib]
          exact Finset.mem_filter.mpr ⟨his, hik⟩
        exact (Finset.mem_filter.mp hi).2
      exact hik.symm.trans hikb
    · intro b hb
      rcases Finset.mem_image.mp hb with ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
  · intro k hk
    rcases hsurj hk with ⟨i, his, hik⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨his, hik⟩⟩
  · intro k hk i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have hik : p i = k := (Finset.mem_filter.mp hi).2
    simpa [hik] using h.le_parent i his

omit [MeasurableSpace E] [BorelSpace E] in
/-- The parent tubes read off the fibre partition of a parent family: the body attached to
the part `fibre s p k` of `Kakeya.ml1Boot.IsParentFamily.finpartition` is `T_{θ,k}`.

This is the shared setup of `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` and
`Kakeya.ml1Boot.frostmanConstIn_coarse_le_of_densityIn_comparable`: both feed a
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards`-style lemma, which is indexed by the *parts*
of a `Finpartition`, with a family indexed by the parent index set `t`. -/
private lemma exists_partitionBody {δ θ : NNReal}
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (T : ι → Tube δ E) (Tθ : κ → Tube θ E) (p : ι → κ)
    (hballθ : ∀ l ∈ t, (Tθ l).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily s T t Tθ p) (hsurj : Set.SurjOn p s t)
    [DecidableEq ι] :
    ∃ (P : Finpartition s) (W : Finset ι → ConvexSpaceBody E),
      Set.BijOn (fun k => fibre s p k) t P.parts ∧
      (∀ k ∈ t, W (fibre s p k) = (Tθ k).toConvexSpaceBody) ∧
      (∀ a ∈ P.parts, W a ≤ ConvexSpaceBody.closedUnitBall) ∧
      (∀ a ∈ P.parts, ∀ i ∈ a, (T i).toConvexSpaceBody ≤ W a) := by
  classical
  obtain ⟨P, hBij, _hne, _hle⟩ := IsParentFamily.finpartition hparent hsurj
  let W : Finset ι → ConvexSpaceBody E := fun a =>
    if ha : a ∈ P.parts then
      (Tθ (Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha)))).toConvexSpaceBody
    else ConvexSpaceBody.closedUnitBall
  have hW_fibre : ∀ k ∈ t, W (fibre s p k) = (Tθ k).toConvexSpaceBody := by
    intro k hk
    unfold W
    have hmem : fibre s p k ∈ P.parts :=
      Finset.mem_coe.mp (hBij.mapsTo (Finset.mem_coe.mpr hk))
    rw [dif_pos hmem]
    congr
    apply hBij.injOn (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr hmem))).1
    · exact Finset.mem_coe.mpr hk
    · exact (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr hmem))).2
  have hWK : ∀ a ∈ P.parts, W a ≤ ConvexSpaceBody.closedUnitBall := by
    intro a ha
    let k : κ := Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha))
    have hk : k ∈ t := (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))).1
    unfold W
    rw [dif_pos ha]
    exact SetLike.coe_subset_coe.mpr (hballθ k hk)
  have hVW : ∀ a ∈ P.parts, ∀ i ∈ a, (T i).toConvexSpaceBody ≤ W a := by
    intro a ha i hi
    let k : κ := Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha))
    have hk : k ∈ t := (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))).1
    have hfib : fibre s p k = a := (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))).2
    have hi_fib : i ∈ fibre s p k := by
      rw [hfib]
      exact hi
    have his : i ∈ s := (Finset.mem_filter.mp hi_fib).1
    have hik : p i = k := (Finset.mem_filter.mp hi_fib).2
    unfold W
    rw [dif_pos ha]
    simpa [hik] using hparent.le_parent i his
  exact ⟨P, W, hBij, hW_fibre, hWK, hVW⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The dilated parent tubes read off the fibre partition of a `c`-dilate parent family: the
body attached to the part `fibre s p k` is the dilate `c · T_{θ,k}`.

This is the `Kakeya.ml1Boot.IsParentFamilyDilate` analogue of
`Kakeya.ml1Boot.exists_partitionBody`.  The fibre partition itself does not see the containment
clause at all — it is built from `mapsTo` and surjectivity — so it is obtained from
`Kakeya.ml1Boot.IsParentFamily.finpartition` applied to the tautological parent family
`i ↦ T_{θ,p i}`, whose `le_parent` is reflexivity.

`hballθ` is taken at the *dilate*, and this is the one place where the dilate variant is
genuinely weaker than the undilated one rather than a transcription of it.  A `θ`-tube inside
the ball of radius `R` need not have its `c`-dilate inside that ball: a `Kakeya.Tube` has core
length `1`, so a parent whose carrier just fits has its `c`-dilate reaching radius about
`c / 2` past the centre.  Since `ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` requires every
part body to lie in the ambient body, the containment has to be hypothesised at the dilate and
cannot be recovered from `(T_θ l).carrier ⊆ B_R`.

**The radius `R` is a parameter, and that is what keeps the statement non-vacuous.**  At the
fixed radius `R = 1` the hypothesis is not merely strong but unsatisfiable once `c ≥ 2`:
`Kakeya.Tube.dilate` is the affine homothety of ratio `c` about `T.center` applied to the whole
carrier (Tube/IntersectionVolume.lean:600-602), the carrier of a `θ`-tube contains both core
endpoints, at distance exactly `1` by `Kakeya.Tube.dist_eq_one` (Tube/Basic.lean:39), together
with the closed `θ`-balls about them, so the dilate has diameter `c (1 + 2 θ) ≥ c`, while
`Metric.closedBall 0 1` has diameter `2`.  The route uses `c = 2`.  Conversely
`Kakeya.Tube.carrier_subset_closedBall_midpoint` (Tube/Basic.lean:1245) puts the carrier inside
`closedBall (T_θ l).center (1 / 2 + θ)`, and a homothety of ratio `c` about that same centre
sends it into `closedBall (T_θ l).center (c (1 / 2 + θ))`, so `hballθ` holds for every
`R ≥ ‖(T_θ l).center‖ + c (1 / 2 + θ)`.  The numerical range for the tubes this route supplies
is recorded on `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le_dilate`.

`R` is an explicit binder: it occurs in `hballθ` and in the conclusion only underneath the
coercion `NNReal.toReal`, so unification cannot recover it from the shape of an argument. -/
private lemma exists_partitionBody_dilate [Nontrivial E] {δ θ : NNReal} {c : ℝ} (R : NNReal)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (T : ι → Tube δ E) (Tθ : κ → Tube θ E) (p : ι → κ)
    (hballθ : ∀ l ∈ t, (Tube.dilate (Tθ l) c).carrier ⊆ Metric.closedBall 0 (R : ℝ))
    (hparent : IsParentFamilyDilate c s T t Tθ p) (hsurj : Set.SurjOn p s t)
    [DecidableEq ι] :
    ∃ (P : Finpartition s) (W : Finset ι → ConvexSpaceBody E),
      Set.BijOn (fun k => fibre s p k) t P.parts ∧
      (∀ k ∈ t, W (fibre s p k) = Tube.dilate (Tθ k) c) ∧
      (∀ a ∈ P.parts, W a ≤ ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ∧
      (∀ a ∈ P.parts, ∀ i ∈ a, (T i).toConvexSpaceBody ≤ W a) := by
  classical
  have hAux : IsParentFamily s (fun i => Tθ (p i)) t Tθ p :=
    { mapsTo := hparent.mapsTo
      injOn := hparent.injOn
      le_parent := fun i _ => le_rfl }
  obtain ⟨P, hBij, _hne, _hle⟩ := IsParentFamily.finpartition hAux hsurj
  let W : Finset ι → ConvexSpaceBody E := fun a =>
    if ha : a ∈ P.parts then
      Tube.dilate (Tθ (Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha)))) c
    else ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg
  have hW_fibre : ∀ k ∈ t, W (fibre s p k) = Tube.dilate (Tθ k) c := by
    intro k hk
    unfold W
    have hmem : fibre s p k ∈ P.parts :=
      Finset.mem_coe.mp (hBij.mapsTo (Finset.mem_coe.mpr hk))
    rw [dif_pos hmem]
    have hke : Classical.choose (hBij.surjOn (Finset.mem_coe.mpr hmem)) = k := by
      apply hBij.injOn (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr hmem))).1
      · exact Finset.mem_coe.mpr hk
      · exact (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr hmem))).2
    rw [hke]
  have hWK : ∀ a ∈ P.parts, W a ≤ ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg := by
    intro a ha
    let k : κ := Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha))
    have hk : k ∈ t := (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))).1
    unfold W
    rw [dif_pos ha]
    exact SetLike.coe_subset_coe.mpr (hballθ k hk)
  have hVW : ∀ a ∈ P.parts, ∀ i ∈ a, (T i).toConvexSpaceBody ≤ W a := by
    intro a ha i hi
    let k : κ := Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha))
    have hk : k ∈ t := (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))).1
    have hfib : fibre s p k = a := (Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))).2
    have hi_fib : i ∈ fibre s p k := by
      rw [hfib]
      exact hi
    have his : i ∈ s := (Finset.mem_filter.mp hi_fib).1
    have hik : p i = k := (Finset.mem_filter.mp hi_fib).2
    unfold W
    rw [dif_pos ha]
    simpa [hik] using hparent.le_parent_dilate i his
  exact ⟨P, W, hBij, hW_fibre, hWK, hVW⟩

/-- `ConvexSpaceBody.IsFrostmanIn` inside a fixed ambient body `K` is invariant under replacing
the family pointwise on its index set.

The ambient body is a parameter rather than `ConvexSpaceBody.closedUnitBall`: the dilate route
below reads its Frostman data inside a ball of radius `R`, and nothing in the argument — which
only ever rewrites `Kakeya.densityIn` along the pointwise equality — depends on the radius. -/
private lemma isFrostmanIn_congr {κ : Type*} {u : Finset κ} {K : ConvexSpaceBody E}
    {f g : κ → ConvexSpaceBody E} {C : ENNReal} (hfg : ∀ k ∈ u, f k = g k)
    (h : IsFrostmanIn u f K C) :
    IsFrostmanIn u g K C := by
  classical
  have hdens : ∀ {f' g' : κ → ConvexSpaceBody E}, (∀ k ∈ u, f' k = g' k) →
      ∀ K' : ConvexSpaceBody E, densityIn u f' K' = densityIn u g' K' := by
    intro f' g' hfg' K'
    have hsum : (∑ i ∈ u with f' i ≤ K', volume (f' i).carrier)
        = (∑ i ∈ u with g' i ≤ K', volume (g' i).carrier) := by
      apply Finset.sum_congr
      · ext i
        by_cases hiu : i ∈ u
        · simp [hiu, hfg' i hiu]
        · simp [hiu]
      · intro i hi
        rw [hfg' i (Finset.mem_filter.mp hi).1]
    unfold densityIn
    rw [hsum]
  intro K' hK'
  calc
    densityIn u g K' = densityIn u f K' :=
      hdens (f' := g) (g' := f) (fun k hk => (hfg k hk).symm) K'
    _ ≤ C * densityIn u f K := h K' hK'
    _ = C * densityIn u g K := by
      rw [hdens (f' := f) (g' := g) hfg K]

/-- **(GWZ Remark 3.3(A)) The Frostman constant of the coarse family** (blueprint
`lem:ml1bootCoarseFrostman`, first clause).

Let `0 < δ ≤ θ ≤ 1`, let `𝕋 = (T i)_{i ∈ s}` be a nonempty family of `δ`-tubes in
`B₁ ⊆ ℝ³` with `C_F(𝕋, B₁) ≤ δ ^ (-η)`, and let `(t, 𝕋_θ, p)` be a parent family for `𝕋` at
scale `θ` with `p` surjective and every `T_{θ,l} ⊆ B₁`.  Then there is `t' ⊆ t` with
`C_F(𝕋_θ|_{t'}, B₁) ≤ L(|s|, δ) δ ^ (-η)`, where
`L(m, δ) = ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 m δ` is the explicit
dyadic-pigeonhole factor in the ambient dimension `3` (written literally, per the module
docstring), which grows like `log (m / δ ^ 3)` and is therefore *not* a constant in the sense
Consumers that need a bound of the shape `C δ ^ (-a)` absorb `L` into an arbitrarily small
negative power of the scale: `Kakeya.ml1Boot.eventually_inheritedUpwards_C_card_le` does it for
a family of pairwise essentially distinct `δ`-tubes in `B₁`, where `Kakeya.ml1Boot.card_le`
bounds `m` by `C_card δ ^ (-4)`, and
`Kakeya.ml1Boot.frostmanConstIn_coarse_absorbed` is the arithmetic step that puts the result in
that shape.  Absorption needs positive exponent room, so it is the consumer's business and not
this lemma's; `Kakeya.ml1Boot.multiplicity_le_coarse` below instead takes `L` as a parameter
with the room as an explicit hypothesis.

The version that keeps *all* the parents, at the price of a comparability hypothesis on the
fibre densities, is `Kakeya.ml1Boot.frostmanConstIn_coarse_le_of_densityIn_comparable`; that
is the one the output of `Kakeya.ml1Boot.exists_factorTwoScales` satisfies. -/
theorem exists_frostmanConstIn_coarse_le (hdim : Module.finrank ℝ E = 3)
    {δ θ : NNReal} (hδ : 0 < δ) (_hδθ : δ ≤ θ) (_hθ1 : θ ≤ 1)
    {ι κ : Type*} {s : Finset ι} {t : Finset κ}
    (T : ι → Tube δ E) (Tθ : κ → Tube θ E) (p : ι → κ) {η : ℝ}
    (_hs : s.Nonempty)
    (_hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hballθ : ∀ l ∈ t, (Tθ l).carrier ⊆ Metric.closedBall 0 1)
    (hF : frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-η))
    (hparent : IsParentFamily s T t Tθ p) (hsurj : Set.SurjOn p s t) :
    ∃ t' ⊆ t,
      frostmanConstIn t' (fun l => (Tθ l).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
        ≤ ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C 3 s.card δ : NNReal) : ENNReal)
          * (δ : ENNReal) ^ (-η) := by
  classical
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  have hFr : IsFrostmanIn s (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ((δ : ENNReal) ^ (-η)) :=
    isFrostmanIn_of_frostmanConstIn_le hF
  obtain ⟨P, W, hBij, hW_fibre, hWK, hVW⟩ :=
    exists_partitionBody T Tθ p hballθ hparent hsurj
  have hV_scale : ∀ i ∈ s, δ ≤ Metric.ethickness.scale ℝ (T i).carrier := fun i hi => by
    rw [Metric.ethickness.scale_eq]
    exact (T i).le_ethickness_finrank_sub_one
  have hK : ConvexSpaceBody.closedUnitBall.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    exact subset_rfl
  · -- Pass to a subfamily of the parent index set.
    obtain ⟨parts', hparts'_sub, hparts'_Fr⟩ :=
      IsFrostmanIn.inherited_upwards (E := E) (ι := ι) (V := fun i => (T i).toConvexSpaceBody)
        (W := W) (K := ConvexSpaceBody.closedUnitBall) (P := P) (δ := δ)
        (C := (δ : ENNReal) ^ (-η)) hδ hFr
        (hV := fun i hi => hV_scale i hi) (hVW := hVW) (hWK := hWK) (hK := hK)
    let t' : Finset κ := t.filter fun k => fibre s p k ∈ parts'
    have ht'sub : t' ⊆ t := Finset.filter_subset _ _
    have hBij' : Set.BijOn (fun k => fibre s p k) t' parts' := by
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        exact Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2)
      · intro a ha b hb hfab
        exact hBij.injOn (Finset.mem_coe.mpr (ht'sub (Finset.mem_coe.mp ha)))
          (Finset.mem_coe.mpr (ht'sub (Finset.mem_coe.mp hb))) hfab
      · intro b hb
        have hsurj := hBij.surjOn (Finset.mem_coe.mpr (hparts'_sub (Finset.mem_coe.mp hb)))
        refine ⟨Classical.choose hsurj, ?_, (Classical.choose_spec hsurj).2⟩
        apply Finset.mem_coe.mpr
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_coe.mp (Classical.choose_spec hsurj).1
        · have hfib_b : fibre s p (Classical.choose hsurj) = b := by
            exact (Classical.choose_spec hsurj).2
          rw [hfib_b]
          exact Finset.mem_coe.mp hb
    have hFr' : IsFrostmanIn t' (fun k => W (fibre s p k)) ConvexSpaceBody.closedUnitBall
        (ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C (Module.finrank ℝ E) s.card δ
          * (δ : ENNReal) ^ (-η)) :=
      (IsFrostmanIn.reindex (s := parts') (W := W) (K := ConvexSpaceBody.closedUnitBall)
        (C := ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C (Module.finrank ℝ E) s.card δ
          * (δ : ENNReal) ^ (-η))
        (t := t') (e := fun k => fibre s p k) (he := hBij')).mpr hparts'_Fr
    have hFr'' : IsFrostmanIn t' (fun l => (Tθ l).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        (ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C (Module.finrank ℝ E) s.card δ
          * (δ : ENNReal) ^ (-η)) := by
      apply isFrostmanIn_congr (u := t') (f := fun k => W (fibre s p k))
        (g := fun l => (Tθ l).toConvexSpaceBody)
      · intro k hk
        exact hW_fibre k (Finset.mem_filter.mp hk).1
      · exact hFr'
    refine ⟨t', ht'sub, ?_⟩
    simpa [hdim] using frostmanConstIn_le hFr''

/-- **(GWZ Remark 3.3(A)) The Frostman constant of the coarse family, over a `c`-dilate**
(blueprint `lem:ml1bootCoarseFrostman`, first clause, dilate half).

This is `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` with the parent family weakened from
`Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate` at ratio `c`, and with
the ambient ball given a radius `R` instead of being fixed to `B₁`.  The weakened parent notion
is what the Section 8 route supplies: the tube attached to a plank by
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` contains the plank only after dilation, so
the parents there are `2`-dilate parents and no undilated parent family is available.

**The conclusion is about the dilated bodies `c · T_{θ,l}`, read inside the ball of radius `R`,
and is not a statement about the `T_{θ,l}` nor about `B₁`.**  The fine tubes are only known to lie
in the dilates, so the dilates are what the inherited Frostman bound is read in, and it must not be
transported back: `Kakeya.frostmanConstIn` is monotone in the ambient body in one direction only,
and in the index set in neither (see the docstring of
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass`), so a bridge from the dilate to the undilated
parent would be a wrong-direction inference.  For the same reason the hypothesis `hF` on the fine
family is read at radius `R` as well: `ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` needs the
family, the part bodies and the ambient body to live in one and the same `K`, and `K` here has to
be large enough to contain the dilates.  The loss is `inherited_upwards.C' 3 |s| δ R`, which is
`inherited_upwards.C 3 |s| δ` plus the additive `2 · 3 · logb 2 R` charged for the larger ball
(`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C_eq_C'_one` identifies the two at `R = 1`).

**Why `R` is a parameter: at `R = 1` this statement was vacuous.**  `hballθ` is a containment of
the *dilated* parents, and `Kakeya.Tube.dilate` is the affine homothety of ratio `c` about
`T.center` applied to the whole carrier (Tube/IntersectionVolume.lean:600-602).  A `θ`-tube
carries both core endpoints at distance exactly `1` (`Kakeya.Tube.dist_eq_one`,
Tube/Basic.lean:39) together with the closed `θ`-balls about them, so the dilate has diameter
`c (1 + 2 θ)`, while `Metric.closedBall 0 R` has diameter `2 R`.  At `R = 1` and `c = 2` — the
ratio this route uses — that already fails, for every `θ > 0`, and `0 < δ ≤ θ` forces `θ > 0`;
so the old unit-ball form of `hballθ` could not be witnessed and the lemma asserted nothing.

**The satisfiable range.**  `Kakeya.Tube.carrier_subset_closedBall_midpoint` (Tube/Basic.lean:1245)
puts `(T_θ l).carrier` inside `closedBall (T_θ l).center (1 / 2 + θ)`, and the homothety of ratio
`c` about that same centre sends that ball to `closedBall (T_θ l).center (c (1 / 2 + θ))`.  So
`hballθ` holds as soon as

  `R ≥ max_{l ∈ t} ‖(T_θ l).center‖ + c (1 / 2 + θ)`,

and the diameter computation above shows `R ≥ c (1 / 2 + θ)` is also necessary.  For the `b`-tubes
of the Section 8 route this is a bound with explicit numbers.  Their carriers lie in
`closedBall 0 (3 / 2 + √3 + C b)`, hence in `closedBall 0 (9 / 2)` under the side condition
`C b ≤ 1` that route already carries — `Kakeya.ml1Boot.plankTube_carrier_subset_closedBall` and
`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_of_le` (PlankTube.lean:736, PlankTube.lean:762)
— and their centres are `Kakeya.ml1Boot.outerPrism.center`, of norm at most `1 + √3` by
`Kakeya.ml1Boot.norm_outerPrism_center_le`.  At `c = 2` and `θ = b ≤ 1` the displayed condition is
therefore met by

  `R ≥ 2 + √3 + 2 b`, so any `R ≥ 4 + √3 ≈ 5.74`,

and even using only the exported containment radius `9 / 2` in place of the sharper centre bound —
the centre lies in the carrier — by `R ≥ 11 / 2 + 2 b`, so any `R ≥ 15 / 2`.  The round figure
`R = 9 = c · (9 / 2)` is thus comfortably inside the range, with the necessary lower bound at
`c = 2` being only `R ≥ 1 + 2 b`.  The statement is non-vacuous at the ratio the route uses.

**This lemma has no consumer at present, and neither does its undilated twin.**  Neither it nor
`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` (Cases.lean:2161) is applied anywhere in the
project: outside the two declarations themselves, every occurrence of either name is a docstring,
a comment, or a blueprint reference.  In particular the Section 8 seam does not hypothesise its
coarse Frostman data in this form:

* the seam's dilate clause (KatzTao.lean:3624-3628) is a *lower* bound on the Frostman constant
  of the **fine** family `𝕋̃` read inside `Kakeya.Tube.dilate (T_ρ m) 2`, whereas this lemma
  produces an *upper* bound on the **coarse** family: different family and opposite direction;
* what actually consumes a coarse Frostman bound is hypothesis (c) of
  `Kakeya.ml1Boot.multiplicity_coarse_le` (KatzTao.lean:632-634), and that reads the
  **undilated** `b`-tube bodies `fun l => (Tb l).toConvexSpaceBody` in `B₁`, not dilated ones.

**What still stands between this lemma and a consumer.**  Two things, neither of them the ball
condition any longer.  First, the downstream consumers read their data in `B₁` while this one
delivers it at radius `R`; moving them is the same relaxation performed here, not a new idea, but
it has not been done.  Second, a bridge in the *family* direction would be needed to reach the
undilated form, and the only sound one in the repository is
`ConvexSpaceBody.frostmanConstIn_ge_of_comparable` (Frostman.lean:834-842).  Its first conjunct
`C_F(𝕎, K) ≤ C ^ 2 * C_F(𝕍, K)` does have the right shape at `W = T_b`, `V = c · T_b`, and two of
its clauses are free there: `hWV` is `Kakeya.Tube.subset_dilate` (Tube/Dilate.lean:284) and `hvol`
is `Kakeya.Tube.tubeDilateVolume` (Tube/IntersectionVolume.lean:614), giving `|c · T| = c ^ 3 |T|`.
Its `hdilate` clause (Frostman.lean:839-840) demands, for every `K' ≤ K`, some `L ≤ K` containing
the `c`-dilates of all family members lying in `K'`; that is false at `K = closedUnitBall`, since a
thin tube tangent to the unit sphere has its dilate sticking out, but at an ambient radius large
enough to absorb the dilates — exactly the `R` of this statement — it is no longer obstructed by
the ball, not a consequence of the hypotheses.  Nothing else bridges: `Kakeya.ml1Boot.frostmanConstIn_le_of_le_ambient`
(DensityTransfer.lean:1303) shrinks the ambient body and leaves the family alone, and
`Kakeya.frostmanConstIn` is monotone in the index set in neither direction
(DensityTransfer.lean:1398).

Everything else — the dyadic pigeonhole factor, the passage to a subfamily `t' ⊆ t`, and the
absorption discussion — is as in the undilated statement, which stays available at `B₁` and is not
derived from this one. -/
theorem exists_frostmanConstIn_coarse_le_dilate [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {δ θ : NNReal} (hδ : 0 < δ) (_hδθ : δ ≤ θ) (_hθ1 : θ ≤ 1) {c : ℝ}
    (R : NNReal) (hR : 0 < R)
    {ι κ : Type*} {s : Finset ι} {t : Finset κ}
    (T : ι → Tube δ E) (Tθ : κ → Tube θ E) (p : ι → κ) {η : ℝ}
    (_hs : s.Nonempty)
    (_hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 (R : ℝ))
    (hballθ : ∀ l ∈ t, (Tube.dilate (Tθ l) c).carrier ⊆ Metric.closedBall 0 (R : ℝ))
    (hF : frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ≤ (δ : ENNReal) ^ (-η))
    (hparent : IsParentFamilyDilate c s T t Tθ p) (hsurj : Set.SurjOn p s t) :
    ∃ t' ⊆ t,
      frostmanConstIn t' (fun l => Tube.dilate (Tθ l) c)
          (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
        ≤ ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' 3 s.card δ R : NNReal) : ENNReal)
          * (δ : ENNReal) ^ (-η) := by
  classical
  have hFr : IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) ((δ : ENNReal) ^ (-η)) :=
    isFrostmanIn_of_frostmanConstIn_le hF
  obtain ⟨P, W, hBij, hW_fibre, hWK, hVW⟩ :=
    exists_partitionBody_dilate R T Tθ p hballθ hparent hsurj
  have hV_scale : ∀ i ∈ s, δ ≤ Metric.ethickness.scale ℝ (T i).carrier := fun i hi => by
    rw [Metric.ethickness.scale_eq]
    exact (T i).le_ethickness_finrank_sub_one
  have hK : (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg).carrier
      ⊆ Metric.closedBall (0 : E) (R : ℝ) := subset_rfl
  obtain ⟨parts', hparts'_sub, hparts'_Fr⟩ :=
    IsFrostmanIn.inherited_upwards' (E := E) (ι := ι) (V := fun i => (T i).toConvexSpaceBody)
      (W := W) (K := ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg) (P := P) (δ := δ)
      (R := R) (C := (δ : ENNReal) ^ (-η)) hδ hR hFr
      (hV := fun i hi => hV_scale i hi) (hVW := hVW) (hWK := hWK) (hK := hK)
  let t' : Finset κ := t.filter fun k => fibre s p k ∈ parts'
  have ht'sub : t' ⊆ t := Finset.filter_subset _ _
  have hBij' : Set.BijOn (fun k => fibre s p k) t' parts' := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact Finset.mem_coe.mpr ((Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2)
    · intro a ha b hb hfab
      exact hBij.injOn (Finset.mem_coe.mpr (ht'sub (Finset.mem_coe.mp ha)))
        (Finset.mem_coe.mpr (ht'sub (Finset.mem_coe.mp hb))) hfab
    · intro b hb
      have hsurj := hBij.surjOn (Finset.mem_coe.mpr (hparts'_sub (Finset.mem_coe.mp hb)))
      refine ⟨Classical.choose hsurj, ?_, (Classical.choose_spec hsurj).2⟩
      apply Finset.mem_coe.mpr
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_coe.mp (Classical.choose_spec hsurj).1
      · have hfib_b : fibre s p (Classical.choose hsurj) = b := (Classical.choose_spec hsurj).2
        rw [hfib_b]
        exact Finset.mem_coe.mp hb
  have hFr' : IsFrostmanIn t' (fun k => W (fibre s p k))
      (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
      (ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' (Module.finrank ℝ E) s.card δ R
        * (δ : ENNReal) ^ (-η)) :=
    (IsFrostmanIn.reindex (s := parts') (W := W)
      (K := ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
      (C := ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' (Module.finrank ℝ E) s.card δ R
        * (δ : ENNReal) ^ (-η))
      (t := t') (e := fun k => fibre s p k) (he := hBij')).mpr hparts'_Fr
  have hFr'' : IsFrostmanIn t' (fun l => Tube.dilate (Tθ l) c)
      (ConvexSpaceBody.closedBall (0 : E) (R : ℝ) R.coe_nonneg)
      (ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' (Module.finrank ℝ E) s.card δ R
        * (δ : ENNReal) ^ (-η)) := by
    apply isFrostmanIn_congr (u := t') (f := fun k => W (fibre s p k))
      (g := fun l => Tube.dilate (Tθ l) c)
    · intro k hk
      exact hW_fibre k (Finset.mem_filter.mp hk).1
    · exact hFr'
  refine ⟨t', ht'sub, ?_⟩
  simpa [hdim] using frostmanConstIn_le hFr''

/-- **(GWZ Remark 3.3(A)) The Frostman constant of the coarse family, with all parents kept**
(blueprint `lem:ml1bootCoarseFrostman`, second clause).

In the situation of `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le`, if moreover the fibre
densities `Δ(𝕋[T_{θ,l}], T_{θ,l})` are comparable with a constant `C' ≥ 1`, then no parent
has to be discarded and the subpolynomial factor `L(|s|, δ)` is replaced by `C'`:
`C_F(𝕋_θ, B₁) ≤ C' δ ^ (-η)`.

This is `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform`; it is the clause that
applies when the coarse family comes out of `Kakeya.ml1Boot.exists_factorTwoScales`, where the
comparison holds with `C' = 2`. -/
theorem frostmanConstIn_coarse_le_of_densityIn_comparable (hdim : Module.finrank ℝ E = 3)
    {δ θ : NNReal} (hδ : 0 < δ) (_hδθ : δ ≤ θ) (_hθ1 : θ ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (T : ι → Tube δ E) (Tθ : κ → Tube θ E) (p : ι → κ) {η : ℝ}
    (_hs : s.Nonempty)
    (_hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hballθ : ∀ l ∈ t, (Tθ l).carrier ⊆ Metric.closedBall 0 1)
    (hF : frostmanConstIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-η))
    (hparent : IsParentFamily s T t Tθ p) (hsurj : Set.SurjOn p s t)
    (C' : NNReal) (_hC'1 : 1 ≤ C')
    (hunifC' : ∀ l ∈ t, ∀ l' ∈ t,
      densityIn (fibre s p l) (fun i => (T i).toConvexSpaceBody) (Tθ l).toConvexSpaceBody
        ≤ (C' : ENNReal) * densityIn (fibre s p l')
            (fun i => (T i).toConvexSpaceBody) (Tθ l').toConvexSpaceBody) :
    frostmanConstIn t (fun l => (Tθ l).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ≤ (C' : ENNReal) * (δ : ENNReal) ^ (-η) := by
  classical
  haveI : Nontrivial E := Module.finrank_pos_iff.mp (by rw [hdim]; norm_num)
  have hFr : IsFrostmanIn s (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ((δ : ENNReal) ^ (-η)) :=
    isFrostmanIn_of_frostmanConstIn_le hF
  obtain ⟨P, W, hBij, hW_fibre, hWK, hVW⟩ :=
    exists_partitionBody T Tθ p hballθ hparent hsurj
  have hV_scale : ∀ i ∈ s, δ ≤ Metric.ethickness.scale ℝ (T i).carrier := fun i hi => by
    rw [Metric.ethickness.scale_eq]
    exact (T i).le_ethickness_finrank_sub_one
  have hVpos : ∀ i ∈ s, 0 < volume ((T i).toConvexSpaceBody).carrier := fun i hi => by
    apply (T i).convex.volume_pos_of_scale_ne_zero
    exact ne_bot_of_le_ne_bot (ENNReal.coe_ne_zero.mpr hδ.ne') (hV_scale i hi)
  have hUnif : IsFrostmanIn P.parts W ConvexSpaceBody.closedUnitBall
      ((C' : ENNReal) * (δ : ENNReal) ^ (-η)) := by
    apply IsFrostmanIn.inherited_upwards_uniform (P := P) (V := fun i => (T i).toConvexSpaceBody)
      (W := W) (K := ConvexSpaceBody.closedUnitBall) (C := (δ : ENNReal) ^ (-η))
      (C' := (C' : ENNReal))
    · exact hFr
    · exact hVpos
    · exact hWK
    · exact hVW
    · intro a ha b hb
      let k : κ := Classical.choose (hBij.surjOn (Finset.mem_coe.mpr ha))
      let k' : κ := Classical.choose (hBij.surjOn (Finset.mem_coe.mpr hb))
      have hk_spec := Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr ha))
      have hk'_spec := Classical.choose_spec (hBij.surjOn (Finset.mem_coe.mpr hb))
      have hka : k ∈ t := hk_spec.1
      have hkb : k' ∈ t := hk'_spec.1
      have hfa : fibre s p k = a := hk_spec.2
      have hfb : fibre s p k' = b := hk'_spec.2
      simpa [← hfa, ← hfb, hW_fibre k hka, hW_fibre k' hkb] using hunifC' k hka k' hkb
  have hFr2' : IsFrostmanIn t (fun k => W (fibre s p k)) ConvexSpaceBody.closedUnitBall
      ((C' : ENNReal) * (δ : ENNReal) ^ (-η)) :=
    (IsFrostmanIn.reindex (s := P.parts) (W := W) (K := ConvexSpaceBody.closedUnitBall)
      (C := (C' : ENNReal) * (δ : ENNReal) ^ (-η))
      (t := t) (e := fun k => fibre s p k) (he := hBij)).mpr hUnif
  have hFr2'' : IsFrostmanIn t (fun l => (Tθ l).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ((C' : ENNReal) * (δ : ENNReal) ^ (-η)) := by
    apply isFrostmanIn_congr (u := t) (f := fun k => W (fibre s p k))
      (g := fun l => (Tθ l).toConvexSpaceBody)
    · intro k hk
      exact hW_fibre k hk
    · exact hFr2'
  simpa using frostmanConstIn_le hFr2''

/-- **(GWZ Lemma 8.1) The coarse-scale factor `μ(𝕋_θ, Y_{𝕋_θ})`** (blueprint
`lem:ml1bootCoarseFactor`).

Suppose `K_F(γ)` holds in `ℝ³`.  Take the loss exponent `e` (the blueprint's `ε♯ = η₀`) and
let `ηs` be the threshold it supplies.  Then for every subpolynomial factor `L ≥ 1`, every
Frostman exponent `n₀ ≥ 0` (the blueprint's `η`) and every `a ≥ 0` (the blueprint's
`η_{j-1}`), for all sufficiently small `δ > 0`: a nonempty family of pairwise essentially
distinct shaded `θ`-tubes in `B₁` with

* (a) `C_F(𝕋_θ, B₁) ≤ L δ ^ (-n₀)`, as supplied by
  `Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le`,
* (b) `λ(𝕋_θ, Y_{𝕋_θ}) ≥ δ ^ ηs`,
* (c) `L δ ^ (-n₀ - e) ≤ δ ^ (-4a)`,

satisfies `μ(𝕋_θ, Y_{𝕋_θ}) ≤ δ ^ (-4a) θ ^ (-2γ) (θ² |t|) ^ (1 - γ/2)`, which is what
`Kakeya.ml1Boot.multiplicity_le_of_middle` consumes.

`L` is quantified before `δ`, and the intended value `L(|s|, δ)` of
`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le` depends on `δ`; the two are reconciled by
`Kakeya.FrostmanEstimate.multiplicity_bound_auxScale`, whose smallness threshold for `δ`
depends only on the loss exponent and on `γ`, the Frostman constant entering only as a
monotone factor in the conclusion (hypothesis (a) is substituted into that factor). -/
theorem multiplicity_le_coarse (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ e > (0 : ℝ), ∃ ηs > (0 : ℝ), ∀ L : NNReal, 1 ≤ L → ∀ n₀ a : ℝ, 0 ≤ n₀ → 0 ≤ a →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ θ : NNReal, δ ≤ θ → θ ≤ 1 →
      ∀ {κ : Type u} {t : Finset κ} (Tθ : κ → ShadedTube θ E),
        t.Nonempty →
        (∀ l ∈ t, (Tθ l).carrier ⊆ Metric.closedBall 0 1) →
        (t : Set κ).Pairwise
          (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
        frostmanConstIn t (fun l => (Tθ l).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall
          ≤ (L : ENNReal) * (δ : ENNReal) ^ (-n₀) →
        (δ : ENNReal) ^ ηs
          ≤ (ShadedBody.fullness t (fun l => (Tθ l).toShadedBody) : ENNReal) →
        (L : ENNReal) * (δ : ENNReal) ^ (-n₀ - e) ≤ (δ : ENNReal) ^ (-4 * a) →
        ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * a) * (θ : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro e he
  have hn : 1 < Module.finrank ℝ E := by
    rw [hdim]
    norm_num
  obtain ⟨ηs, hηs, hev⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn E hγ0 hγ1 hn hKF e he
  refine ⟨ηs, hηs, ?_⟩
  intro L hL n₀ a hn₀ ha
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ_aux hδ_pos
  intro θ hδθ hθ1 κ t Tθ htne hball hED hfrostman hfull hc
  let C : ENNReal := (L : ENNReal) * (δ : ENNReal) ^ (-n₀)
  have hL' : (1 : ENNReal) ≤ (L : ENNReal) := by exact_mod_cast hL
  have hδ1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast (le_trans hδθ hθ1)
  have hδpow_le_one : (δ : ENNReal) ^ n₀ ≤ 1 :=
    ENNReal.rpow_le_one hδ1 hn₀
  have h1_le_δinv : 1 ≤ (δ : ENNReal) ^ (-n₀) := by
    calc
      1 = (1 : ENNReal)⁻¹ := by simp
      _ ≤ ((δ : ENNReal) ^ n₀)⁻¹ := by
        exact ENNReal.inv_le_inv.mpr hδpow_le_one
      _ = (δ : ENNReal) ^ (-n₀) := by rw [ENNReal.rpow_neg]
  have hC1 : 1 ≤ C := by
    unfold C
    calc
      1 = (1 : ENNReal) * 1 := by simp
      _ ≤ (L : ENNReal) * (δ : ENNReal) ^ (-n₀) := by
        exact mul_le_mul hL' h1_le_δinv zero_le zero_le
  have hδ_ne0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCtop : C ≠ ⊤ := by
    unfold C
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hδ_ne0 hδ_ne_top)
  have hFrost : IsFrostmanIn t (fun l => (Tθ l).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall C :=
    isFrostmanIn_of_frostmanConstIn_le hfrostman
  have hmult' : ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2)
        * (θ : ENNReal) ^ (-2 * γ)
        * ((t.card : ENNReal) * (θ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - γ / 2) := by
    exact hδ_aux C hC1 hCtop θ hδθ hθ1 t Tθ htne hball hED hfull hFrost
  have hmult'_θ : ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2)
        * (θ : ENNReal) ^ (-2 * γ)
        * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    simpa [hdim] using hmult'
  have hCpow_le : C ^ (1 - γ / 2) ≤ C := by
    have hexp : (1 - γ / 2 : ℝ) ≤ 1 := by nlinarith [hγ0]
    calc
      C ^ (1 - γ / 2) ≤ C ^ (1 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le hC1 hexp
      _ = C := by rw [ENNReal.rpow_one]
  have hpre : (δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2) ≤ (δ : ENNReal) ^ (-4 * a) := by
    have hsum : (-e) + (-n₀) = -n₀ - e := by ring
    calc
      (δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2)
          ≤ (δ : ENNReal) ^ (-e) * C := by
            exact mul_le_mul_right hCpow_le ((δ : ENNReal) ^ (-e))
      _ = (δ : ENNReal) ^ (-e) * ((L : ENNReal) * (δ : ENNReal) ^ (-n₀)) := by rfl
      _ = (L : ENNReal) * ((δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-n₀)) := by ring
      _ = (L : ENNReal) * (δ : ENNReal) ^ (-n₀ - e) := by
            rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-e) (-n₀) hδ_ne0 hδ_ne_top, hsum]
      _ ≤ (δ : ENNReal) ^ (-4 * a) := hc
  calc
    ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
        ≤ (δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2)
          * (θ : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hmult'_θ
    _ ≤ (δ : ENNReal) ^ (-4 * a) * (θ : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
          gcongr

end Coarse

/-! ### Case (ii): reduction to the middle factor

The three arithmetic steps and the assembly are stated for bare `ENNReal` quantities, so that
they do not depend on the data produced by `Kakeya.ml1Boot.exists_factorTwoScales`; see
blueprint `note:ml1bootCaseNonStickyReading` for the intended reading of `X`, `M₁, M₂, M₃`
and `P₁, P₂, P₃` as multiplicities and cardinalities. -/

/-- **Collapsing the three scales** (blueprint `lem:ml1bootTripleCollapse`).

If `A B D = δ` with `A, B, D ∈ (0, 1]`, the three brackets
`F_r (A_r ^ (-2γ)) ((A_r² P_r) ^ (1 - γ/2))` multiply to
`(δ ^ (-2γ)) ((δ² M) ^ (1 - γ/2))` up to the loss `F₁ F₂ F₃ ≤ 1` and the count
`P₁ P₂ P₃ ≤ M`.

The blueprint writes `(A ^ (-2)) ^ γ`; here the two exponents are contracted to
`A ^ (-2 * γ)`.  The prefactor is called `E` after the blueprint; `δ ∈ (0, 1]` is not a
separate hypothesis, being forced by `hABD` together with `_hA0`–`_hD1`.

The scale and counting bounds `_hA0`–`_hD1`, `_hγ0`, `_hP₁`–`_hM` are part of the intended
interface but are not needed by the algebra, so they carry a leading underscore. -/
theorem tripleCollapse {δ A B D : NNReal}
    (_hA0 : 0 < A) (_hA1 : A ≤ 1) (_hB0 : 0 < B) (_hB1 : B ≤ 1) (_hD0 : 0 < D) (_hD1 : D ≤ 1)
    (hABD : A * B * D = δ) {γ : ℝ} (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    {X E F₁ F₂ F₃ P₁ P₂ P₃ M : ENNReal}
    (_hP₁ : 1 ≤ P₁) (_hP₂ : 1 ≤ P₂) (_hP₃ : 1 ≤ P₃) (_hM : 1 ≤ M)
    (hPM : P₁ * P₂ * P₃ ≤ M) (hF : F₁ * F₂ * F₃ ≤ 1)
    (hX : X ≤ E
      * (F₁ * (A : ENNReal) ^ (-2 * γ) * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * (F₂ * (B : ENNReal) ^ (-2 * γ) * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * (F₃ * (D : ENNReal) ^ (-2 * γ) * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))) :
    X ≤ E * (δ : ENNReal) ^ (-2 * γ)
      * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  have hpos : 0 ≤ (1 - γ / 2 : ℝ) := by nlinarith [hγ1]
  have hABDE : (A : ENNReal) * (B : ENNReal) * (D : ENNReal) = (δ : ENNReal) := by
    exact_mod_cast hABD
  have hABD' : ((A * B * D : NNReal) : ENNReal) = (δ : ENNReal) := by
    rw [hABD]
  have hneg :
      (A : ENNReal) ^ (-2 * γ) * (B : ENNReal) ^ (-2 * γ) * (D : ENNReal) ^ (-2 * γ)
        = (δ : ENNReal) ^ (-2 * γ) := by
    rw [← ENNReal.coe_mul_rpow]
    rw [← ENNReal.coe_mul]
    rw [← ENNReal.coe_mul_rpow]
    rw [← ENNReal.coe_mul]
    rw [hABD']
  have hBase :
      (P₁ * (A : ENNReal) ^ (2 : ℕ)) * (P₂ * (B : ENNReal) ^ (2 : ℕ))
          * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ≤ M * (δ : ENNReal) ^ (2 : ℕ) := by
    calc
      (P₁ * (A : ENNReal) ^ (2 : ℕ)) * (P₂ * (B : ENNReal) ^ (2 : ℕ))
          * (P₃ * (D : ENNReal) ^ (2 : ℕ))
          = (P₁ * P₂ * P₃) * ((A : ENNReal) ^ (2 : ℕ) * (B : ENNReal) ^ (2 : ℕ)
              * (D : ENNReal) ^ (2 : ℕ)) := by ring
      _ ≤ M * ((A : ENNReal) ^ (2 : ℕ) * (B : ENNReal) ^ (2 : ℕ)
              * (D : ENNReal) ^ (2 : ℕ)) := by gcongr
      _ = M * ((A : ENNReal) * (B : ENNReal) * (D : ENNReal)) ^ (2 : ℕ) := by
            rw [← mul_pow, ← mul_pow]
      _ = M * (δ : ENNReal) ^ (2 : ℕ) := by rw [hABDE]
  have hQ :
      (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
        = ((P₁ * (A : ENNReal) ^ (2 : ℕ)) * (P₂ * (B : ENNReal) ^ (2 : ℕ))
            * (P₃ * (D : ENNReal) ^ (2 : ℕ))) ^ (1 - γ / 2) := by
            rw [← ENNReal.mul_rpow_of_nonneg _ _ hpos,
              ← ENNReal.mul_rpow_of_nonneg _ _ hpos]
      _ ≤ (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
            exact ENNReal.rpow_le_rpow hBase hpos
  have hT :
      (F₁ * (A : ENNReal) ^ (-2 * γ)
          * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ENNReal) ^ (-2 * γ)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ENNReal) ^ (-2 * γ)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      ≤ (δ : ENNReal) ^ (-2 * γ) * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      (F₁ * (A : ENNReal) ^ (-2 * γ)
          * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ENNReal) ^ (-2 * γ)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ENNReal) ^ (-2 * γ)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        = (F₁ * F₂ * F₃) * ((A : ENNReal) ^ (-2 * γ) * (B : ENNReal) ^ (-2 * γ)
            * (D : ENNReal) ^ (-2 * γ))
          * ((P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by ring
      _ ≤ 1 * ((A : ENNReal) ^ (-2 * γ) * (B : ENNReal) ^ (-2 * γ)
            * (D : ENNReal) ^ (-2 * γ))
          * ((P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by gcongr
      _ = (A : ENNReal) ^ (-2 * γ) * (B : ENNReal) ^ (-2 * γ)
            * (D : ENNReal) ^ (-2 * γ)
          * ((P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by simp
      _ = (δ : ENNReal) ^ (-2 * γ)
          * ((P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by rw [hneg]
      _ ≤ (δ : ENNReal) ^ (-2 * γ) * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
            gcongr
  calc
    X ≤ E * (F₁ * (A : ENNReal) ^ (-2 * γ)
          * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ENNReal) ^ (-2 * γ)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ENNReal) ^ (-2 * γ)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := hX
    _ = E * ((F₁ * (A : ENNReal) ^ (-2 * γ)
          * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ENNReal) ^ (-2 * γ)
            * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ENNReal) ^ (-2 * γ)
            * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))) := by ring
    _ ≤ E * ((δ : ENNReal) ^ (-2 * γ) * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          gcongr
    _ = E * (δ : ENNReal) ^ (-2 * γ) * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring

/-- **Collapsing the three scales, carrying the gain** (blueprint `lem:ml1bootTripleCollapse`,
in the form the Case (ii) assembly consumes it).

This is `Kakeya.ml1Boot.tripleCollapse` specialized to the three loss factors
`δ ^ (-4 a')`, `δ ^ (10 a)`, `δ ^ (-4 a')` of the exponent contract, with their product
`δ ^ (10 a - 8 a')` *carried out* of the collapse rather than discarded through
`δ ^ (10 a - 8 a') ≤ 1`.  Carrying it is what funds the exponent shift of
`Kakeya.ml1Boot.multiplicity_le_of_middle`, and hence what decouples the step of blueprint
`def:ml1bootParams`(vi) from any loss allowance; see blueprint `note:auditUniformStep`.

It is `Kakeya.ml1Boot.tripleCollapse` applied with prefactor `E · δ ^ (10 a - 8 a')` and the
renormalized loss factors `δ ^ (-4a' - G/3)`, `δ ^ (10a - G/3)`, `δ ^ (-4a' - G/3)`, where
`G = 10 a - 8 a'`: their product is `δ ^ 0 = 1`, and the three factors `δ ^ (-G/3)` cancel
against the `δ ^ G` in the prefactor, so its hypothesis is the same real number as the one
supplied here.  No sign condition on `G` is needed. -/
theorem tripleCollapse_gain {δ A B D : NNReal} (hδ0 : 0 < δ)
    (hA0 : 0 < A) (hA1 : A ≤ 1) (hB0 : 0 < B) (hB1 : B ≤ 1) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hABD : A * B * D = δ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {a a' : ℝ}
    {X E P₁ P₂ P₃ M : ENNReal}
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) (hP₃ : 1 ≤ P₃) (hM : 1 ≤ M)
    (hPM : P₁ * P₂ * P₃ ≤ M)
    (hX : X ≤ E
      * ((δ : ENNReal) ^ (-4 * a') * (A : ENNReal) ^ (-2 * γ)
          * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * ((δ : ENNReal) ^ (10 * a) * (B : ENNReal) ^ (-2 * γ)
          * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * ((δ : ENNReal) ^ (-4 * a') * (D : ENNReal) ^ (-2 * γ)
          * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))) :
    X ≤ E * (δ : ENNReal) ^ (10 * a - 8 * a') * (δ : ENNReal) ^ (-2 * γ)
      * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  let G : ℝ := 10 * a - 8 * a'
  let E' : ENNReal := E * (δ : ENNReal) ^ G
  let F₁ : ENNReal := (δ : ENNReal) ^ (-4 * a' - G / 3)
  let F₂ : ENNReal := (δ : ENNReal) ^ (10 * a - G / 3)
  let F₃ : ENNReal := (δ : ENNReal) ^ (-4 * a' - G / 3)
  let B₁ : ENNReal := (A : ENNReal) ^ (-2 * γ) * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  let B₂ : ENNReal := (B : ENNReal) ^ (-2 * γ) * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  let B₃ : ENNReal := (D : ENNReal) ^ (-2 * γ) * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
  have hδp : 0 < (δ : ENNReal) := (ENNReal.coe_pos).mpr hδ0
  have hδne : (δ : ENNReal) ≠ 0 := ne_of_gt hδp
  have hδtop : (δ : ENNReal) ≠ ⊤ := ne_of_lt ENNReal.coe_lt_top
  have hδ : (δ : ENNReal) ^ G = (δ : ENNReal) ^ (10 * a - 8 * a') := by
    dsimp [G]
  have hF₁ : F₁ = (δ : ENNReal) ^ (-4 * a') * (δ : ENNReal) ^ (-(G / 3)) := by
    dsimp [F₁]
    calc
      (δ : ENNReal) ^ (-4 * a' - G / 3) = (δ : ENNReal) ^ ((-4 * a') + (-(G / 3))) := rfl
      _ = (δ : ENNReal) ^ (-4 * a') * (δ : ENNReal) ^ (-(G / 3)) :=
        ENNReal.rpow_add (x := (δ : ENNReal)) (-4 * a') (-(G / 3)) hδne hδtop
  have hF₂ : F₂ = (δ : ENNReal) ^ (10 * a) * (δ : ENNReal) ^ (-(G / 3)) := by
    dsimp [F₂]
    calc
      (δ : ENNReal) ^ (10 * a - G / 3) = (δ : ENNReal) ^ ((10 * a) + (-(G / 3))) := rfl
      _ = (δ : ENNReal) ^ (10 * a) * (δ : ENNReal) ^ (-(G / 3)) :=
        ENNReal.rpow_add (x := (δ : ENNReal)) (10 * a) (-(G / 3)) hδne hδtop
  have hF₃ : F₃ = (δ : ENNReal) ^ (-4 * a') * (δ : ENNReal) ^ (-(G / 3)) := by
    dsimp [F₃]
    calc
      (δ : ENNReal) ^ (-4 * a' - G / 3) = (δ : ENNReal) ^ ((-4 * a') + (-(G / 3))) := rfl
      _ = (δ : ENNReal) ^ (-4 * a') * (δ : ENNReal) ^ (-(G / 3)) :=
        ENNReal.rpow_add (x := (δ : ENNReal)) (-4 * a') (-(G / 3)) hδne hδtop
  have hcollect : ∀ (e1 e2 e3 : ℝ),
      (δ : ENNReal) ^ e1 * (δ : ENNReal) ^ e2 * (δ : ENNReal) ^ e3
        = (δ : ENNReal) ^ (e1 + e2 + e3) := by
    intro e1 e2 e3
    calc
      (δ : ENNReal) ^ e1 * (δ : ENNReal) ^ e2 * (δ : ENNReal) ^ e3
          = (δ : ENNReal) ^ (e1 + e2) * (δ : ENNReal) ^ e3 := by
            rw [← ENNReal.rpow_add (x := (δ : ENNReal)) e1 e2 hδne hδtop]
      _ = (δ : ENNReal) ^ (e1 + e2 + e3) := by
            rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (e1 + e2) e3 hδne hδtop]
  have hcd :
      (δ : ENNReal) ^ (-4 * a') * (δ : ENNReal) ^ (10 * a) * (δ : ENNReal) ^ (-4 * a') =
        (δ : ENNReal) ^ (10 * a - 8 * a') := by
    rw [hcollect (-4 * a') (10 * a) (-4 * a')]
    congr 1
    ring
  have hF123 : F₁ * F₂ * F₃ = 1 := by
    have hsum : (-4 * a' - G / 3) + (10 * a - G / 3) + (-4 * a' - G / 3) = 0 := by
      unfold G
      ring
    dsimp [F₁, F₂, F₃]
    rw [hcollect (-4 * a' - G / 3) (10 * a - G / 3) (-4 * a' - G / 3), hsum]
    exact ENNReal.rpow_zero
  have hF : F₁ * F₂ * F₃ ≤ 1 := by rw [hF123]
  have hEq :
      E' * (F₁ * B₁) * (F₂ * B₂) * (F₃ * B₃) =
        E * ((δ : ENNReal) ^ (-4 * a') * B₁) * ((δ : ENNReal) ^ (10 * a) * B₂)
          * ((δ : ENNReal) ^ (-4 * a') * B₃) := by
    calc
      E' * (F₁ * B₁) * (F₂ * B₂) * (F₃ * B₃)
          = E' * (F₁ * F₂ * F₃) * (B₁ * B₂ * B₃) := by ring
      _ = E' * (B₁ * B₂ * B₃) := by rw [hF123]; ring
      _ = E * ((δ : ENNReal) ^ (10 * a - 8 * a')) * (B₁ * B₂ * B₃) := by dsimp [E']
      _ = E * ((δ : ENNReal) ^ (-4 * a') * (δ : ENNReal) ^ (10 * a))
            * ((δ : ENNReal) ^ (-4 * a')) * (B₁ * B₂ * B₃) := by
            rw [← hcd]
            ring
      _ = E * ((δ : ENNReal) ^ (-4 * a') * B₁) * ((δ : ENNReal) ^ (10 * a) * B₂)
          * ((δ : ENNReal) ^ (-4 * a') * B₃) := by ring
  have hX' :
      X ≤ E' * (F₁ * (A : ENNReal) ^ (-2 * γ) * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₂ * (B : ENNReal) ^ (-2 * γ) * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * (F₃ * (D : ENNReal) ^ (-2 * γ) * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
    calc
      X ≤ E * ((δ : ENNReal) ^ (-4 * a') * (A : ENNReal) ^ (-2 * γ)
          * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * ((δ : ENNReal) ^ (10 * a) * (B : ENNReal) ^ (-2 * γ)
          * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
        * ((δ : ENNReal) ^ (-4 * a') * (D : ENNReal) ^ (-2 * γ)
          * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := hX
      _ = E * ((δ : ENNReal) ^ (-4 * a') * B₁) * ((δ : ENNReal) ^ (10 * a) * B₂)
          * ((δ : ENNReal) ^ (-4 * a') * B₃) := by
            dsimp [B₁, B₂, B₃]
            ring
      _ = E' * (F₁ * B₁) * (F₂ * B₂) * (F₃ * B₃) := by exact hEq.symm
      _ = E' * (F₁ * (A : ENNReal) ^ (-2 * γ) * (P₁ * (A : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (F₂ * (B : ENNReal) ^ (-2 * γ) * (P₂ * (B : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * (F₃ * (D : ENNReal) ^ (-2 * γ) * (P₃ * (D : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
            dsimp [B₁, B₂, B₃]
            ring
  calc
    X ≤ E' * (δ : ENNReal) ^ (-2 * γ)
        * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
          tripleCollapse hA0 hA1 hB0 hB1 hD0 hD1 hABD hγ0 hγ1 hP₁ hP₂ hP₃ hM hPM hF hX'
    _ = E * (δ : ENNReal) ^ (10 * a - 8 * a') * (δ : ENNReal) ^ (-2 * γ)
        * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by dsimp [E']

/-- **Shifting the exponent** (blueprint `lem:ml1bootExponentShift`).

For `0 < δ ≤ 1`, `γ ∈ [0, 1]`, `0 < a ≤ γ`, `η ≥ 0` and `V ≥ δ ^ η` with `V ≠ 0`,

`δ ^ (-2γ) V ^ (1 - γ/2) ≤ δ ^ (-2a - η a / 2) · δ ^ (-2 (γ - a)) V ^ (1 - (γ - a)/2)`.

This is the identity `δ ^ (-2γ) V ^ (1 - γ/2) = δ ^ (-2a) V ^ (-a/2) δ ^ (-2(γ-a))
V ^ (1 - (γ-a)/2)` together with the bound `V ^ (-a/2) ≤ δ ^ (-η a / 2)` coming from
`V ≥ δ ^ η`.

`V = ⊤` is not excluded: since `a ≤ γ ≤ 1`, both exponents `1 - γ/2` and `1 - (γ-a)/2` are at
least `1/2 > 0`, so both sides are `⊤` and the inequality holds. -/
theorem exponentShift {δ : NNReal} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) {γ a η : ℝ}
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (ha0 : 0 < a) (_haγ : a ≤ γ) (_hη : 0 ≤ η)
    {V : ENNReal} (hV0 : V ≠ 0) (hV : (δ : ENNReal) ^ η ≤ V) :
    (δ : ENNReal) ^ (-2 * γ) * V ^ (1 - γ / 2)
      ≤ (δ : ENNReal) ^ (-2 * a - η * a / 2) * (δ : ENNReal) ^ (-2 * (γ - a))
        * V ^ (1 - (γ - a) / 2) := by
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ0
  have hδe0 : (δ : ENNReal) ≠ 0 := ne_of_gt hδpos
  have hδtop : (δ : ENNReal) ≠ ⊤ := ne_of_lt ENNReal.coe_lt_top
  by_cases hVtop : V = ⊤
  · rw [hVtop]
    have hpos1 : 0 < 1 - γ / 2 := by nlinarith [hγ1]
    have hpos2 : 0 < 1 - (γ - a) / 2 := by nlinarith [hγ1, ha0]
    have hnn : ∀ e : ℝ, (δ : ENNReal) ^ e ≠ 0 := fun e =>
      ne_of_gt (ENNReal.rpow_pos hδpos hδtop)
    have hL : (δ : ENNReal) ^ (-2 * γ) * (⊤ : ENNReal) ^ (1 - γ / 2) = ⊤ := by
      rw [ENNReal.top_rpow_of_pos hpos1]
      exact ENNReal.mul_top (hnn (-2 * γ))
    have hR : (δ : ENNReal) ^ (-2 * a - η * a / 2) * (δ : ENNReal) ^ (-2 * (γ - a))
        * (⊤ : ENNReal) ^ (1 - (γ - a) / 2) = ⊤ := by
      rw [ENNReal.top_rpow_of_pos hpos2]
      rw [mul_assoc]
      rw [ENNReal.mul_top (hnn (-2 * (γ - a))), ENNReal.mul_top (hnn (-2 * a - η * a / 2))]
    rw [hL, hR]
  · have hsub : V ^ (-(a / 2)) ≤ (δ : ENNReal) ^ (-(η * a / 2)) := by
      have hmono' : ((δ : ENNReal) ^ η) ^ (a / 2) ≤ V ^ (a / 2) :=
        ENNReal.rpow_le_rpow hV (by positivity : 0 ≤ a / 2)
      have hmono : (δ : ENNReal) ^ (η * a / 2) ≤ V ^ (a / 2) := by
        calc
          (δ : ENNReal) ^ (η * a / 2) = (δ : ENNReal) ^ (η * (a / 2)) := by
            congr 1
            ring
          _ = ((δ : ENNReal) ^ η) ^ (a / 2) := by rw [ENNReal.rpow_mul]
          _ ≤ V ^ (a / 2) := hmono'
      calc
        V ^ (-(a / 2)) = (V ^ (a / 2))⁻¹ := by rw [ENNReal.rpow_neg]
        _ ≤ ((δ : ENNReal) ^ (η * a / 2))⁻¹ := ENNReal.inv_le_inv.mpr hmono
        _ = (δ : ENNReal) ^ (-(η * a / 2)) := by rw [← ENNReal.rpow_neg]
    have hDpow : (δ : ENNReal) ^ (-2 * γ)
        = (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-2 * (γ - a)) := by
      rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-2 * a) (-2 * (γ - a)) hδe0 hδtop]
      congr 1
      ring
    have hVpow : V ^ (1 - γ / 2) = V ^ (-(a / 2)) * V ^ (1 - (γ - a) / 2) := by
      rw [← ENNReal.rpow_add (x := V) (-(a / 2)) (1 - (γ - a) / 2) hV0 hVtop]
      congr 1
      ring
    calc
      (δ : ENNReal) ^ (-2 * γ) * V ^ (1 - γ / 2)
          = (δ : ENNReal) ^ (-2 * a) * V ^ (-(a / 2)) * (δ : ENNReal) ^ (-2 * (γ - a))
            * V ^ (1 - (γ - a) / 2) := by
              rw [hDpow, hVpow]
              ring
      _ ≤ (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-(η * a / 2))
            * (δ : ENNReal) ^ (-2 * (γ - a)) * V ^ (1 - (γ - a) / 2) := by
              have hfac : (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-2 * (γ - a))
                  * V ^ (1 - (γ - a) / 2) * V ^ (-(a / 2))
                ≤ (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-2 * (γ - a))
                  * V ^ (1 - (γ - a) / 2) * (δ : ENNReal) ^ (-(η * a / 2)) := by
                  exact mul_le_mul_right hsub
                    ((δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-2 * (γ - a))
                      * V ^ (1 - (γ - a) / 2))
              calc
                (δ : ENNReal) ^ (-2 * a) * V ^ (-(a / 2)) * (δ : ENNReal) ^ (-2 * (γ - a))
                    * V ^ (1 - (γ - a) / 2)
                    = (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-2 * (γ - a))
                      * V ^ (1 - (γ - a) / 2) * V ^ (-(a / 2)) := by ring
                _ ≤ (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-2 * (γ - a))
                    * V ^ (1 - (γ - a) / 2) * (δ : ENNReal) ^ (-(η * a / 2)) := hfac
                _ = (δ : ENNReal) ^ (-2 * a) * (δ : ENNReal) ^ (-(η * a / 2))
                    * (δ : ENNReal) ^ (-2 * (γ - a)) * V ^ (1 - (γ - a) / 2) := by ring
      _ = (δ : ENNReal) ^ (-2 * a - η * a / 2) * (δ : ENNReal) ^ (-2 * (γ - a))
            * V ^ (1 - (γ - a) / 2) := by
              rw [show -2 * a - η * a / 2 = (-2 * a) + (-(η * a / 2)) by ring]
              rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-2 * a) (-(η * a / 2)) hδe0 hδtop]

/-- **The step is funded by the gain** (blueprint `lem:ml1bootLossNumerics`).

Let `η₀ > 0` be the bottom rung of the ladder, `ηprev = η_{j-1} ≥ η₀` the rung the exponent
contract is run at, `ε' = η₀ / 16` the bookkeeping accuracy, `c ≤ η₀ / 4` the step and
`e ∈ [0, η₀]` the fullness exponent (intended value `η(γ)`).  Then

`ε' + 2 c + e c / 2 + 5 η₀ / 16 ≤ 10 ηprev - 8 (ηprev + 2 ε')`,

the right-hand side being the gain exponent `10 a - 8 a' = 2 η_{j-1} - 16 ε'` of the exponent
contract at `a = ηprev`, `a' = ηprev + 2 ε'`.  Consequently, for `0 < δ ≤ 1`,

`δ ^ (-ε') · δ ^ (10 a - 8 a') · δ ^ (-2 c - e c / 2) ≤ δ ^ (5 η₀ / 16)`,

so any fixed constant is absorbed by taking `δ` small — with a threshold depending on that
constant and on `(β, γ₀)` only, and *not* on the accuracy at which the conclusion of
`Kakeya.ml1Boot.multiplicity_le_of_middle` is required.

This replaces the earlier `2 η₁ + η η₁ / 2 ≤ ε / 2`, which funded a shift by the ladder entry
`η₁` out of half the package's own loss exponent `ε`; that is the coupling recorded at
blueprint `note:auditUniformStep`.  Here the shift is funded out of the *gain* of the exponent
contract, which no caller can shrink.  Numerically: `e c / 2 ≤ η₀ ² / 8 ≤ η₀ / 8`, so the left
side is at most `(1/16 + 1/2 + 1/8 + 5/16) η₀ = η₀`, while the right side is
`2 ηprev - η₀ ≥ η₀`. -/
theorem lossNumerics {η₀ ηprev ε' c e : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1)
    (hprev : η₀ ≤ ηprev) (hε' : ε' = η₀ / 16) (hc0 : 0 < c) (hc : c ≤ η₀ / 4)
    (he0 : 0 ≤ e) (he : e ≤ η₀) :
    ε' + 2 * c + e * c / 2 + 5 * η₀ / 16 ≤ 10 * ηprev - 8 * (ηprev + 2 * ε') := by
  subst ε'
  have hec : e * c ≤ η₀ * (η₀ / 4) := by
    exact mul_le_mul he hc (le_of_lt hc0) (le_of_lt hη₀)
  have hnonneg : 0 ≤ e := he0
  nlinarith

/-- **(GWZ Lemma 8.1) Case (ii) reduces to the middle factor** (blueprint
`lem:ml1bootCaseNonSticky`).

Given `0 < δ ≤ τ ≤ θ ≤ 1`, a **step** `ν` with `0 < ν ≤ γ`, a **target loss exponent**
`ℓ ≥ 0`, exponents `η ≥ 0`, `0 ≤ a ≤ a'` with `8 a' ≤ 10 a` and `ε' > 0`, an exponent
`γ ∈ [0, 1]`, a uniformity constant `Cu ≥ 1`, a cardinality `m > 0` and a constant
`c₃ ∈ (0, 1]`, the triple-product bound (a) together with the fine (b), middle (c) and coarse
(d) bounds, the uniformity count (e), the total-volume lower bound (f) and the absorption
inequality (g) give

`X ≤ δ ^ (-ℓ) δ ^ (-2 (γ - ν)) (δ² m) ^ (1 - (γ - ν)/2)`,

which is the multiplicity bound of `K_F(γ - ν)` with loss `δ ^ (-ℓ)`, since a `δ`-tube in
`ℝ³` has volume `δ²`.

## The step and the loss are free, and the gain is carried

Both the step `ν` and the target loss `ℓ` are now free parameters, and the gain
`δ ^ (10 a - 8 a')` of the three loss factors is *carried out of the collapse* rather than
discarded through `δ ^ (10 a - 8 a') ≤ 1`.  That is what hypothesis (g) spends: the linking
loss `δ ^ (-ε')`, the exponent shift `δ ^ (-2 ν - η ν / 2)` and the fixed constants are all
paid for out of the gain.  In the intended instantiation (blueprint
`lem:ml1bootCaseIIAssemble`) the step is the package's `Kakeya.ml1Boot.Params.c`, the loss is
`ℓ = 0`, and (g) is `Kakeya.ml1Boot.lossNumerics` together with the smallness of `δ`.

The earlier form fixed `ν = η₁`, a rung of the package's own ladder, and concluded with the
loss `δ ^ (-ε)` drawn from the package's own loss exponent, discarding the gain at the step
`hF` of the proof.  Both couplings are the defect recorded at blueprint
`note:auditUniformStep`; a caller entitled to shrink the accuracy could not do so without
shrinking the step.

## The two exponents `a` and `a'`

The middle factor (c) gains `δ ^ (10 a)` at the exponent `a = η_{j-1}`, whereas the fine (b)
and coarse (d) factors lose `δ ^ (-4 a')` at a *larger* exponent `a' ≥ a`.  This is forced:
the Frostman hypothesis (a) of `Kakeya.ml1Boot.multiplicity_le_fine` can only be supplied at
`a' = η_{j-1} + 2 ε'`, since the bound `δ ^ (-ε') (τ/δ) ^ η_{j-1}` of
`Kakeya.ml1Boot.exists_caseTwoData`(ii) picks up a second factor `δ ^ (-ε')` from
`Kakeya.ml1Boot.IsFactorTwoScales.frostman_fine` before the fine factor sees it.  With a single
exponent the chain has *negative* gain at `j = 1`.

The three loss factors then multiply to `δ ^ (10 a - 8 a')`, so the side condition
`8 a' ≤ 10 a` — equivalently `16 ε' ≤ 2 η_{j-1}`, i.e. `ε' ≤ η_{j-1} / 8` — is exactly what
makes the product at most `1`.  Since `η₀ ≤ η_{j-1}` for every `1 ≤ j ≤ N`, the uniform
choice `ε' = η₀ / 8` works for all `j` at once; see
`Kakeya.ml1Boot.multiplicity_le_caseTwo`.  The whole of the `δ ^ (-ε)` allowance is spent on
the constants, via (g), and on the exponent shift `γ ↦ γ - η₁`.

The total-volume lower bound (f) is stated with a constant `c₃ ≤ 1` in front of `δ ^ η`, and
not as the clean `δ ^ η ≤ m δ²`.  That is all that is available: it is supplied by
`ConvexSpaceBody.card_ge_of_frostmanConstIn_le`, whose constant
`ConvexSpaceBody.card_ge_of_frostmanConstIn_le.C 3 = |B₁| / 2 ^ 4` is strictly below `1`.
The resulting extra factor `c₃ ^ (-ν/2)` in the exponent shift — the exponent shift is applied
with step `ν`, so `V ^ (-ν/2) ≤ c₃ ^ (-ν/2) δ ^ (-η ν / 2)` — is paid for by the absorption
inequality (g), which carries it explicitly.  The constant is called `c₃` and no longer `c`,
which is now the step of blueprint `def:ml1bootParams`(vi).

## The factoring loss constant is a free parameter

`C_f` is carried as a free `NNReal` and not as `Kakeya.ml1Boot.factorTwoScales.C`, which now
depends on the two applications' inner cardinalities and inner tube scales — data this lemma
does not have, its `M₁`, `M₂`, `M₃` being bare extended reals.  Nothing here uses any property
of `C_f`, not even `1 ≤ C_f`: it enters (a) on the large side and (g) on the large side, and is
transported.  The caller
`Kakeya.ml1Boot.multiplicity_le_collapse_of_isFactorTwoScales` supplies
`C_f = factorTwoScales.C #s δ #t''τ τ`, read off
`Kakeya.ml1Boot.IsFactorTwoScales.product`.  See blueprint
`note:ml1bootArithFreeConstant`. -/
theorem multiplicity_le_of_middle {δ τ θ : NNReal} (hδ0 : 0 < δ) (hδτ : δ ≤ τ)
    (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1) {ν ℓ η a a' ε' : ℝ}
    (_hη0 : 0 ≤ η) (_ha : 0 ≤ a) (_haa' : a ≤ a')
    (_hgain : 8 * a' ≤ 10 * a) (_hε' : 0 < ε') (_hℓ : 0 ≤ ℓ)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hν0 : 0 < ν) (hνγ : ν ≤ γ)
    {Cu : NNReal} (hCu : 1 ≤ Cu) {m : ℕ} (hm : 0 < m)
    {c₃ : NNReal} (hc₃0 : 0 < c₃) (_hc₃1 : c₃ ≤ 1)
    {Cf : NNReal}
    {X M₁ M₂ M₃ P₁ P₂ P₃ : ENNReal}
    (hP₁ : 1 ≤ P₁) (hP₂ : 1 ≤ P₂) (hP₃ : 1 ≤ P₃)
    (htriple : X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * M₁ * M₂ * M₃)
    (hfine : M₁ ≤ (δ : ENNReal) ^ (-4 * a') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
      * (P₁ * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hmiddle : M₂ ≤ (δ : ENNReal) ^ (10 * a) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
      * (P₂ * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hcoarse : M₃ ≤ (δ : ENNReal) ^ (-4 * a') * (θ : ENNReal) ^ (-2 * γ)
      * (P₃ * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hunif : P₁ * P₂ * P₃ ≤ (Cu : ENNReal) ^ 4 * (m : ENNReal))
    (hvol : (c₃ : ENNReal) * (δ : ENNReal) ^ η ≤ (m : ENNReal) * (δ : ENNReal) ^ (2 : ℕ))
    (habsorb : (Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (c₃ : ENNReal) ^ (-ν / 2)
      * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (10 * a - 8 * a')
      * (δ : ENNReal) ^ (-2 * ν - η * ν / 2) ≤ (δ : ENNReal) ^ (-ℓ)) :
    X ≤ (δ : ENNReal) ^ (-ℓ) * (δ : ENNReal) ^ (-2 * (γ - ν))
      * ((m : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - ν) / 2) := by
  -- Elementary consequences of the scale order `0 < δ ≤ τ ≤ θ ≤ 1`.
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ0 hδτ
  have hθ0 : 0 < θ := lt_of_lt_of_le hτ0 hτθ
  have hδ1 : δ ≤ 1 := le_trans hδτ (le_trans hτθ hθ1)
  have hδle : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ0
  have hδne : (δ : ENNReal) ≠ 0 := ne_of_gt hδpos
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδne0 : (δ : NNReal) ≠ 0 := ne_of_gt hδ0
  have hτne : (τ : NNReal) ≠ 0 := ne_of_gt hτ0
  have hθne : (θ : NNReal) ≠ 0 := ne_of_gt hθ0
  let V : ENNReal := (m : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt hm)) (pow_ne_zero 2 hδne)
  have hVtop : V ≠ ⊤ := by
    dsimp [V]
    exact ENNReal.mul_ne_top (by exact ENNReal.coe_ne_top)
      (ne_of_lt (ENNReal.pow_lt_top ENNReal.coe_lt_top))
  -- The scale collapse `(δ/τ) * (τ/θ) * θ = δ`, with `A,B,D ∈ (0,1]`.
  have hA0 : 0 < δ / τ := div_pos hδ0 hτ0
  have hA1 : δ / τ ≤ 1 := div_le_one_of_le₀ hδτ (le_of_lt hτ0)
  have hB0 : 0 < τ / θ := div_pos hτ0 hθ0
  have hB1 : τ / θ ≤ 1 := div_le_one_of_le₀ hτθ (le_of_lt hθ0)
  have hABD : (δ / τ) * (τ / θ) * θ = δ := by
    field_simp [hτne, hθne]
  -- The uniformity count supplies `M = Cu ^ 4 * m`.
  have hCu4 : (1 : ENNReal) ≤ (Cu : ENNReal) ^ 4 := by
    calc
      (1 : ENNReal) = (1 : ENNReal) ^ 4 := by norm_num
      _ ≤ (Cu : ENNReal) ^ 4 := by
        exact pow_le_pow_left₀ zero_le (by exact_mod_cast hCu) 4
  have hm1 : (1 : ENNReal) ≤ (m : ENNReal) := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hM : (1 : ENNReal) ≤ (Cu : ENNReal) ^ 4 * (m : ENNReal) := one_le_mul hCu4 hm1
  -- The middle gain exponent `G = 10 a - 8 a'` is carried out of the collapse.
  set G : ℝ := 10 * a - 8 * a' with hG
  let E : ENNReal := (Cf : ENNReal) * (δ : ENNReal) ^ (-ε')
  let M : ENNReal := (Cu : ENNReal) ^ 4 * (m : ENNReal)
  -- The triple-product bound, in the form consumed by `tripleCollapse_gain`.
  have hX : X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε')
      * ((δ : ENNReal) ^ (-4 * a') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
          * (P₁ * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * ((δ : ENNReal) ^ (10 * a) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
          * (P₂ * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
      * ((δ : ENNReal) ^ (-4 * a') * (θ : ENNReal) ^ (-2 * γ)
          * (P₃ * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
    calc
      X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * M₁ * M₂ * M₃ := htriple
      _ ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε')
          * ((δ : ENNReal) ^ (-4 * a') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
              * (P₁ * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * ((δ : ENNReal) ^ (10 * a) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
              * (P₂ * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
          * ((δ : ENNReal) ^ (-4 * a') * (θ : ENNReal) ^ (-2 * γ)
              * (P₃ * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
            gcongr
  have htri : X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G
      * (δ : ENNReal) ^ (-2 * γ) * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    exact tripleCollapse_gain (A := δ / τ) (B := τ / θ) (D := θ) (E := E) (M := M)
      hδ0 hA0 hA1 hB0 hB1 hθ0 hθ1 hABD hγ0 hγ1 hP₁ hP₂ hP₃ hM hunif hX
  -- Pull the uniformity constant `Cu ^ 4` out of the bracket.
  have hCu_pow : ((Cu : ENNReal) ^ 4) ^ (1 - γ / 2) ≤ (Cu : ENNReal) ^ 4 := by
    calc
      ((Cu : ENNReal) ^ 4) ^ (1 - γ / 2) ≤ ((Cu : ENNReal) ^ 4) ^ (1 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le (x := (Cu : ENNReal) ^ 4)
          (y := 1 - γ / 2) (z := 1) hCu4 (by nlinarith [hγ0])
      _ = (Cu : ENNReal) ^ 4 := by rw [ENNReal.rpow_one]
  have hCu_out : ((Cu : ENNReal) ^ 4 * (m : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
      ≤ (Cu : ENNReal) ^ 4 * V ^ (1 - γ / 2) := by
    have hpos : 0 ≤ 1 - γ / 2 := by nlinarith [hγ1]
    calc
      ((Cu : ENNReal) ^ 4 * (m : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
          = ((Cu : ENNReal) ^ 4 * ((m : ENNReal) * (δ : ENNReal) ^ (2 : ℕ))) ^ (1 - γ / 2) := by
            rw [mul_assoc]
      _ = ((Cu : ENNReal) ^ 4) ^ (1 - γ / 2) * V ^ (1 - γ / 2) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hpos]
      _ ≤ (Cu : ENNReal) ^ 4 * V ^ (1 - γ / 2) := by
            gcongr
  have htri' : X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G
      * (δ : ENNReal) ^ (-2 * γ) * (Cu : ENNReal) ^ 4 * V ^ (1 - γ / 2) := by
    calc
      X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G
          * (δ : ENNReal) ^ (-2 * γ) * (M * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := htri
      _ ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G
          * (δ : ENNReal) ^ (-2 * γ) * ((Cu : ENNReal) ^ 4 * V ^ (1 - γ / 2)) := by
            exact mul_le_mul_right hCu_out ((Cf : ENNReal) * (δ : ENNReal) ^ (-ε')
              * (δ : ENNReal) ^ G * (δ : ENNReal) ^ (-2 * γ))
      _ = (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G
          * (δ : ENNReal) ^ (-2 * γ) * (Cu : ENNReal) ^ 4 * V ^ (1 - γ / 2) := by ring
  -- Shift the exponent with the free step `ν` (`0 < ν ≤ γ`), using `c₃`.
  have hν2 : 0 ≤ ν / 2 := by nlinarith [hν0]
  have hcpos : 0 < (c₃ : ENNReal) := ENNReal.coe_pos.mpr hc₃0
  have hctop : (c₃ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδpow_pos : 0 < (δ : ENNReal) ^ η := ENNReal.rpow_pos hδpos hδtop
  have hδpow_top : (δ : ENNReal) ^ η ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hδne hδtop
  have hcη_pos : 0 < (c₃ : ENNReal) ^ (ν / 2) := ENNReal.rpow_pos hcpos hctop
  have hδppos : 0 < ((δ : ENNReal) ^ η) ^ (ν / 2) := ENNReal.rpow_pos hδpow_pos hδpow_top
  have hprod : ((c₃ : ENNReal) * (δ : ENNReal) ^ η) ^ (-(ν / 2))
      = (c₃ : ENNReal) ^ (-(ν / 2)) * ((δ : ENNReal) ^ η) ^ (-(ν / 2)) := by
    calc
      ((c₃ : ENNReal) * (δ : ENNReal) ^ η) ^ (-(ν / 2))
          = (((c₃ : ENNReal) * (δ : ENNReal) ^ η) ^ (ν / 2))⁻¹ := by rw [ENNReal.rpow_neg]
      _ = ((c₃ : ENNReal) ^ (ν / 2) * ((δ : ENNReal) ^ η) ^ (ν / 2))⁻¹ := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hν2]
      _ = (c₃ : ENNReal) ^ (-(ν / 2)) * ((δ : ENNReal) ^ η) ^ (-(ν / 2)) := by
            rw [ENNReal.mul_inv (Or.inl (ne_of_gt hcη_pos)) (Or.inr (ne_of_gt hδppos))]
            rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg]
  have hmono2 : ((c₃ : ENNReal) * (δ : ENNReal) ^ η) ^ (ν / 2) ≤ V ^ (ν / 2) := by
    exact ENNReal.rpow_le_rpow hvol hν2
  have hVneg : V ^ (-(ν / 2))
      ≤ (c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2)) := by
    calc
      V ^ (-(ν / 2)) = (V ^ (ν / 2))⁻¹ := by rw [ENNReal.rpow_neg]
      _ ≤ (((c₃ : ENNReal) * (δ : ENNReal) ^ η) ^ (ν / 2))⁻¹ := by
            exact ENNReal.inv_le_inv.mpr hmono2
      _ = ((c₃ : ENNReal) * (δ : ENNReal) ^ η) ^ (-(ν / 2)) := by rw [← ENNReal.rpow_neg]
      _ = (c₃ : ENNReal) ^ (-(ν / 2)) * ((δ : ENNReal) ^ η) ^ (-(ν / 2)) := hprod
      _ = (c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2)) := by
            rw [← ENNReal.rpow_mul]
            rw [show η * -(ν / 2) = -(η * ν / 2) by ring]
  have hDpow : (δ : ENNReal) ^ (-2 * γ)
      = (δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-2 * (γ - ν)) := by
    rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-2 * ν) (-2 * (γ - ν)) hδne hδtop]
    congr 1
    ring
  have hVpow : V ^ (1 - γ / 2) = V ^ (-(ν / 2)) * V ^ (1 - (γ - ν) / 2) := by
    rw [← ENNReal.rpow_add (x := V) (-(ν / 2)) (1 - (γ - ν) / 2) hV0 hVtop]
    congr 1
    ring
  have hshift : (δ : ENNReal) ^ (-2 * γ) * V ^ (1 - γ / 2)
      ≤ (c₃ : ENNReal) ^ (-ν / 2) * (δ : ENNReal) ^ (-2 * ν - η * ν / 2)
        * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by
    have hstep : (δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-2 * (γ - ν))
          * V ^ (1 - (γ - ν) / 2) * V ^ (-(ν / 2))
        ≤ (δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-2 * (γ - ν))
          * V ^ (1 - (γ - ν) / 2)
          * ((c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2))) := by
          exact mul_le_mul_right hVneg
            ((δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2))
    calc
      (δ : ENNReal) ^ (-2 * γ) * V ^ (1 - γ / 2)
          = (δ : ENNReal) ^ (-2 * ν) * V ^ (-(ν / 2)) * (δ : ENNReal) ^ (-2 * (γ - ν))
            * V ^ (1 - (γ - ν) / 2) := by
            rw [hDpow, hVpow]
            ring
      _ ≤ (δ : ENNReal) ^ (-2 * ν)
            * ((c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2)))
            * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by
            calc
              (δ : ENNReal) ^ (-2 * ν) * V ^ (-(ν / 2)) * (δ : ENNReal) ^ (-2 * (γ - ν))
                  * V ^ (1 - (γ - ν) / 2)
                  = (δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-2 * (γ - ν))
                    * V ^ (1 - (γ - ν) / 2) * V ^ (-(ν / 2)) := by ring
              _ ≤ (δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-2 * (γ - ν))
                  * V ^ (1 - (γ - ν) / 2)
                  * ((c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2))) := hstep
              _ = (δ : ENNReal) ^ (-2 * ν)
                  * ((c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2)))
                  * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by ring
      _ = (c₃ : ENNReal) ^ (-ν / 2) * (δ : ENNReal) ^ (-2 * ν - η * ν / 2)
            * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by
            have hc_exp : (c₃ : ENNReal) ^ (-(ν / 2)) = (c₃ : ENNReal) ^ (-ν / 2) := by
              congr 1
              ring
            have hδcomb : (δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-(η * ν / 2))
                = (δ : ENNReal) ^ (-2 * ν - η * ν / 2) := by
              rw [← ENNReal.rpow_add (x := (δ : ENNReal)) (-2 * ν) (-(η * ν / 2)) hδne hδtop]
              congr 1
            calc
              (δ : ENNReal) ^ (-2 * ν)
                  * ((c₃ : ENNReal) ^ (-(ν / 2)) * (δ : ENNReal) ^ (-(η * ν / 2)))
                  * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2)
                  = (c₃ : ENNReal) ^ (-(ν / 2))
                    * ((δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-(η * ν / 2)))
                    * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by ring
              _ = (c₃ : ENNReal) ^ (-ν / 2)
                    * ((δ : ENNReal) ^ (-2 * ν) * (δ : ENNReal) ^ (-(η * ν / 2)))
                    * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by
                    rw [hc_exp]
              _ = (c₃ : ENNReal) ^ (-ν / 2) * (δ : ENNReal) ^ (-2 * ν - η * ν / 2)
                    * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by
                    rw [hδcomb]
  -- The whole prefactor is bounded by `δ ^ (-ℓ)` by the absorption hypothesis.
  have hpref : (Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (c₃ : ENNReal) ^ (-ν / 2)
        * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G * (δ : ENNReal) ^ (-2 * ν - η * ν / 2)
      ≤ (δ : ENNReal) ^ (-ℓ) := by
    simpa [hG] using habsorb
  calc
    X ≤ (Cf : ENNReal) * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G
        * (δ : ENNReal) ^ (-2 * γ) * (Cu : ENNReal) ^ 4 * V ^ (1 - γ / 2) := htri'
    _ = ((Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (δ : ENNReal) ^ (-ε')
          * (δ : ENNReal) ^ G) * ((δ : ENNReal) ^ (-2 * γ) * V ^ (1 - γ / 2)) := by ring
    _ ≤ ((Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (δ : ENNReal) ^ (-ε')
          * (δ : ENNReal) ^ G)
        * ((c₃ : ENNReal) ^ (-ν / 2) * (δ : ENNReal) ^ (-2 * ν - η * ν / 2)
          * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2)) := by
          exact mul_le_mul_right hshift ((Cf : ENNReal) * (Cu : ENNReal) ^ 4
            * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G)
    _ = ((Cf : ENNReal) * (Cu : ENNReal) ^ 4 * (c₃ : ENNReal) ^ (-ν / 2)
          * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ G * (δ : ENNReal) ^ (-2 * ν - η * ν / 2))
        * ((δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2)) := by ring
    _ ≤ (δ : ENNReal) ^ (-ℓ) * ((δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2)) := by
          gcongr
    _ = (δ : ENNReal) ^ (-ℓ) * (δ : ENNReal) ^ (-2 * (γ - ν)) * V ^ (1 - (γ - ν) / 2) := by ring

section FibreCount

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The fibre product count** (blueprint `lem:ml1bootFibreProductCount`).

For the output of `Kakeya.ml1Boot.exists_factorTwoScales` and any `k₀ ∈ t'_τ`,
`l₀ ∈ t'_θ`,

`|𝕋[T_{τ,k₀}]|_{s'}| · |𝕋_τ[T_{θ,l₀}]|_{t'_τ}| · |𝕋_θ|_{t'_θ}| ≤ 2² |s|`,

i.e. hypothesis (e) of `Kakeya.ml1Boot.multiplicity_le_of_middle` holds with `Cu = 2`.  The
proof counts `t'_τ` by its fibres over `t'_θ` and `s'` by its fibres over `t'_τ`, each fibre
having at least `N_θ`, resp. `N_τ`, elements. -/
theorem fibre_product_card_le {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {δ τ θ : NNReal} {ε' : ℝ} {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset l} {Tθ : l → Tube θ E} {pθ : κ → l}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset l}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : l → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ)
    {k₀ : κ} (hk₀ : k₀ ∈ t'τ) {l₀ : l} (hl₀ : l₀ ∈ t'θ) :
    (fibre s' pτ k₀).card * (fibre t'τ pθ l₀).card * t'θ.card ≤ 2 ^ 2 * s.card := by
  -- Upper bounds on the two fibre-product factors.
  have hP1_le : ((fibre s' pτ k₀).card : ENNReal) ≤ 2 * (Nτ : ENNReal) :=
    (h.branch_fine_card k₀ hk₀).2
  have hP2_le : ((fibre t'τ pθ l₀).card : ENNReal) ≤ 2 * (Nθ : ENNReal) :=
    (h.branch_mid_card l₀ hl₀).2
  -- Lower bounds on every fibre.
  have hNτ_le : ∀ k ∈ t'τ, (Nτ : ENNReal) ≤ ((fibre s' pτ k).card : ENNReal) :=
    fun k hk => (h.branch_fine_card k hk).1
  have hNθ_le : ∀ l' ∈ t'θ, (Nθ : ENNReal) ≤ ((fibre t'τ pθ l').card : ENNReal) :=
    fun l' hl' => (h.branch_mid_card l' hl').1
  -- The parent maps land in the retained index sets.
  have hmapτ : ∀ i ∈ s', pτ i ∈ t'τ := h.branch_fine_mapsTo
  have hmapθ : ∀ k ∈ t'τ, pθ k ∈ t'θ := h.branch_mid_mapsTo
  -- Count `t'τ` by its fibres over `t'θ`.
  have hsum_t'τ : (t'τ.card : ENNReal) = ∑ l' ∈ t'θ, ((fibre t'τ pθ l').card : ENNReal) := by
    have hnat : t'τ.card = ∑ l' ∈ t'θ, (fibre t'τ pθ l').card := by
      simpa [fibre] using
        (Finset.card_eq_sum_card_fiberwise (s := t'τ) (f := pθ) (t := t'θ) (H := hmapθ))
    exact_mod_cast hnat
  have hle_t'τ : (t'θ.card : ENNReal) * (Nθ : ENNReal) ≤ (t'τ.card : ENNReal) := by
    calc
      (t'θ.card : ENNReal) * (Nθ : ENNReal) = ∑ l' ∈ t'θ, (Nθ : ENNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ l' ∈ t'θ, ((fibre t'τ pθ l').card : ENNReal) := by
        exact Finset.sum_le_sum (fun l' hl' => hNθ_le l' hl')
      _ = (t'τ.card : ENNReal) := hsum_t'τ.symm
  -- Count `s'` by its fibres over `t'τ`.
  have hsum_s' : (s'.card : ENNReal) = ∑ k ∈ t'τ, ((fibre s' pτ k).card : ENNReal) := by
    have hnat : s'.card = ∑ k ∈ t'τ, (fibre s' pτ k).card := by
      simpa [fibre] using
        (Finset.card_eq_sum_card_fiberwise (s := s') (f := pτ) (t := t'τ) (H := hmapτ))
    exact_mod_cast hnat
  have hle_s' : (t'τ.card : ENNReal) * (Nτ : ENNReal) ≤ (s'.card : ENNReal) := by
    calc
      (t'τ.card : ENNReal) * (Nτ : ENNReal) = ∑ k ∈ t'τ, (Nτ : ENNReal) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ t'τ, ((fibre s' pτ k).card : ENNReal) := by
        exact Finset.sum_le_sum (fun k hk => hNτ_le k hk)
      _ = (s'.card : ENNReal) := hsum_s'.symm
  -- `s' ⊆ s`.
  have hs's : (s'.card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast (Finset.card_le_card h.fine_subset)
  -- `P₃ · Nθ · Nτ ≤ |s|`.
  have hchain : (t'θ.card : ENNReal) * (Nθ : ENNReal) * (Nτ : ENNReal) ≤ (s.card : ENNReal) := by
    calc
      (t'θ.card : ENNReal) * (Nθ : ENNReal) * (Nτ : ENNReal)
          ≤ (t'τ.card : ENNReal) * (Nτ : ENNReal) := by
            exact mul_le_mul_left hle_t'τ (Nτ : ENNReal)
      _ ≤ (s'.card : ENNReal) := hle_s'
      _ ≤ (s.card : ENNReal) := hs's
  -- The main inequality, in `ENNReal`.
  have hEN :
      ((fibre s' pτ k₀).card : ENNReal) * ((fibre t'τ pθ l₀).card : ENNReal)
        * (t'θ.card : ENNReal) ≤ (2 : ENNReal) ^ 2 * (s.card : ENNReal) := by
    calc
      ((fibre s' pτ k₀).card : ENNReal) * ((fibre t'τ pθ l₀).card : ENNReal)
          * (t'θ.card : ENNReal)
          ≤ (2 * (Nτ : ENNReal)) * (2 * (Nθ : ENNReal)) * (t'θ.card : ENNReal) := by
            gcongr
      _ = 4 * ((t'θ.card : ENNReal) * (Nθ : ENNReal) * (Nτ : ENNReal)) := by
            ring
      _ ≤ 4 * (s.card : ENNReal) := by
            exact mul_le_mul_right hchain (4 : ENNReal)
      _ = (2 : ENNReal) ^ 2 * (s.card : ENNReal) := by
            norm_num
  exact_mod_cast hEN

end FibreCount

section FineFibreFromFactorTwoScales

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A retained fine fibre of `Kakeya.ml1Boot.exists_factorTwoScales` is a fine fibre**
(blueprint `lem:ml1bootFineFactor`, the hypothesis block).

`Kakeya.ml1Boot.IsFineFibre` is the hypothesis package that
`Kakeya.ml1Boot.multiplicity_le_fine` consumes, and until now nothing produced it.  This is
its producer for the two-scale output: for a retained middle index `k ∈ t'_τ`, the fibre
`𝕋[T_{τ,k}]|_{s'}` shaded by `Y'` is a fine fibre at comparability constant `Λ = 2` and
common density `μ₀ = λ_δ`.

The seven fields come from the structure as follows.

* `density_pos` is the hypothesis `0 < λ_δ`; the structure records only the two-sided
  bracket `Kakeya.ml1Boot.IsFactorTwoScales.fine_dens`, not the positivity of the constant it
  brackets against, so that positivity — which is part of the output of
  `Kakeya.ml1Boot.exists_factorTwoScales` — has to be supplied.
* `nonempty` is `Kakeya.ml1Boot.IsFactorTwoScales.branch_fine_card` together with `0 < N_τ`.
* `parent_ball` is the hypothesis `hball`: no field of the structure locates the middle tubes
  in `B₁`.
* `subset_parent` is the parent family `hparent` at the fine scale, transported along the
  tube equality of `Kakeya.ml1Boot.IsFactorTwoScales.fine_shade`.
* `essDistinct` is `Kakeya.ml1Boot.IsFactorTwoScales.fine_essDistinct`, again along
  `fine_shade`.
* `shade_comparable` is `Kakeya.ml1Boot.IsFactorTwoScales.fine_dens`, whose bracket
  `λ_δ |T_i| ≤ |Y'_i| ≤ 2 λ_δ |T_i|` is the case `Λ = 2`, `μ₀ = λ_δ` of the two-sided form
  (the lower bound is *stronger* than the required `Λ⁻¹ μ₀ |T_i| ≤ |Y'_i|`).
* `fullness` is the hypothesis `hfull` together with
  `Kakeya.ml1Boot.le_fullness_of_dens_lower`: the termwise lower bound of `fine_dens` gives
  `λ_δ ≤ λ(𝕋[T_{τ,k}]|_{s'}, Y')`, and `hfull` is the fullness threshold at that constant.
  `Kakeya.ml1Boot.IsFactorTwoScales.fine_fullness` bounds `λ_δ` below only by
  `δ ^ (2 ε') λ(𝕋, Y)`, and the structure carries no lower bound on `λ(𝕋, Y)`, so the
  absolute threshold cannot be read off the structure alone. -/
theorem isFineFibre_of_isFactorTwoScales [Nontrivial E]
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : NNReal} (hδ : 0 < δ) {ε' ηs : ℝ}
    {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset lc} {Tθ : lc → Tube θ E} {pθ : κ → lc}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset lc}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : lc → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ)
    (hlamδ : 0 < lamδ) (hNτ : 0 < Nτ)
    (hparent : IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ)
    {k : κ} (hk : k ∈ t'τ)
    (hball : (Tτ k).carrier ⊆ Metric.closedBall 0 1)
    (hfull : (fineFactor.C : ENNReal) * (2 : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
      ≤ (lamδ : ENNReal)) :
    IsFineFibre 2 (lamδ : ENNReal) ηs (fibre s' pτ k) (Tτ k) Y' := by
  have hnonempty : (fibre s' pτ k).Nonempty := by
    have hNτ_pos : 0 < (Nτ : ENNReal) := ENNReal.coe_pos.mpr hNτ
    have hle : (Nτ : ENNReal) ≤ ((fibre s' pτ k).card : ENNReal) :=
      (h.branch_fine_card k hk).1
    have hcard0 : 0 < (fibre s' pτ k).card := by
      exact_mod_cast (lt_of_lt_of_le hNτ_pos hle)
    exact Finset.card_pos.mp hcard0
  have hdens_lower : ∀ i ∈ fibre s' pτ k,
      (lamδ : ENNReal) * volume (Y' i).carrier ≤ volume (Y' i).shade := by
    intro i hi
    have his' : i ∈ s' := (Finset.mem_filter.mp hi).1
    have hdens := (h.fine_dens i his').1
    have hcar : (Y' i).carrier = (T i).carrier := by
      exact congrArg (fun T : Tube δ E => T.carrier) (h.fine_shade i his').1
    simpa [hcar] using hdens
  refine ⟨?_, hnonempty, hball, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.coe_pos.mpr hlamδ
  · intro i hi
    have his' : i ∈ s' := (Finset.mem_filter.mp hi).1
    have hik : pτ i = k := (Finset.mem_filter.mp hi).2
    have his : i ∈ s := h.fine_subset his'
    have hle : (T i).toTube.toConvexSpaceBody ≤ (Tτ (pτ i)).toConvexSpaceBody :=
      hparent.le_parent i his
    have hle' : (T i).toTube.toConvexSpaceBody ≤ (Tτ k).toConvexSpaceBody := by
      simpa [hik] using hle
    have hcar : (Y' i).carrier = (T i).carrier := by
      exact congrArg (fun T : Tube δ E => T.carrier) (h.fine_shade i his').1
    rw [hcar]
    exact hle'
  · intro i hi j hj hij
    have his' : i ∈ s' := (Finset.mem_filter.mp hi).1
    have hjs' : j ∈ s' := (Finset.mem_filter.mp hj).1
    have hED : IsEssentiallyDistinct (T i).carrier (T j).carrier :=
      h.fine_essDistinct his' hjs' hij
    have hcar_i : (Y' i).carrier = (T i).carrier := by
      exact congrArg (fun T : Tube δ E => T.carrier) (h.fine_shade i his').1
    have hcar_j : (Y' j).carrier = (T j).carrier := by
      exact congrArg (fun T : Tube δ E => T.carrier) (h.fine_shade j hjs').1
    rw [hcar_i, hcar_j]
    exact hED
  · intro i hi
    have his' : i ∈ s' := (Finset.mem_filter.mp hi).1
    have hdens := h.fine_dens i his'
    have hcar : (Y' i).carrier = (T i).carrier := by
      exact congrArg (fun T : Tube δ E => T.carrier) (h.fine_shade i his').1
    constructor
    · calc
        (2 : ENNReal)⁻¹ * (lamδ : ENNReal) * volume (Y' i).carrier
            ≤ (1 : ENNReal) * (lamδ : ENNReal) * volume (Y' i).carrier := by
              exact mul_le_mul
                (mul_le_mul (by norm_num : (2 : ENNReal)⁻¹ ≤ (1 : ENNReal)) le_rfl zero_le zero_le)
                le_rfl zero_le zero_le
        _ = (lamδ : ENNReal) * volume (Y' i).carrier := by simp
        _ ≤ volume (Y' i).shade := by
              simpa [hcar] using hdens.1
    · simpa [hcar] using hdens.2
  · have hlam_le : (lamδ : ENNReal)
        ≤ (ShadedBody.fullness (fibre s' pτ k) (fun i => (Y' i).toShadedBody) : ENNReal) :=
      le_fullness_of_dens_lower hδ hnonempty Y' hdens_lower
    exact le_trans hfull hlam_le

/-- **A fixed constant times a higher power of `δ` is eventually below a lower power.**

For `y < x`, `C δ ^ x ≤ δ ^ y` for all small enough `δ > 0`, since the quotient is
`C δ ^ (x - y)` with a positive exponent.  The threshold depends on `C`, `x` and `y` only.

This is the shape in which the fixed constants of the fine factor
(`Kakeya.ml1Boot.multiplicity_le_fine`, hypothesis (c)) are paid for out of the smallness of
`δ` rather than out of a loss allowance. -/
theorem eventually_const_mul_rpow_le (C : NNReal) {x y : ℝ} (hxy : y < x) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (C : ENNReal) * (δ : ENNReal) ^ x ≤ (δ : ENNReal) ^ y := by
  by_cases hC0 : C = 0
  · filter_upwards [] with δ
    simp [hC0]
  · have hCpos : 0 < (C : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hC0)
    let c : NNReal := C⁻¹
    have hc : 0 < (c : ℝ) := by
      dsimp [c]
      exact inv_pos.mpr hCpos
    let a := x - y
    have ha : 0 < a := by
      dsimp [a]
      linarith
    have hreal : ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ), (δ : ℝ) ^ a ≤ (c : ℝ) := by
      apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (Real.rpow_pos_of_pos hc (1 / a)))
      intro δ hδ
      simp only [Set.mem_Ioo] at hδ
      calc
        (δ : ℝ) ^ a ≤ ((c : ℝ) ^ (1 / a) : ℝ) ^ a := by
          exact Real.rpow_le_rpow hδ.1.le hδ.2.le ha.le
        _ = c := by
          calc
            ((c : ℝ) ^ (1 / a)) ^ a = (c : ℝ) ^ ((1 / a) * a) :=
              (Real.rpow_mul hc.le (1 / a) a).symm
            _ = c := by
              rw [show (1 / a) * a = 1 by field_simp [ha.ne'], Real.rpow_one]
    have hnn : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), (δ : ℝ) ^ a ≤ (c : ℝ) :=
      Kakeya.nnreal_eventually_of_real_eventually hreal
    filter_upwards [hnn, self_mem_nhdsWithin] with δ hδc hδpos
    have hδpos_r : 0 < (δ : ℝ) := by exact_mod_cast hδpos
    have hδne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hδne0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδpos)
    have hδc_le : (δ : ENNReal) ^ a ≤ (c : ENNReal) := by
      calc
        (δ : ENNReal) ^ a = ENNReal.ofReal ((δ : ℝ) ^ a) :=
          Kakeya.ennreal_coe_nnreal_rpow hδpos_r a
        _ ≤ ENNReal.ofReal (c : ℝ) := ENNReal.ofReal_le_ofReal hδc
        _ = (c : ENNReal) := by exact ENNReal.ofReal_coe_nnreal
    have hle1 : (C : ENNReal) * (δ : ENNReal) ^ a ≤ 1 := by
      calc
        (C : ENNReal) * (δ : ENNReal) ^ a ≤ (C : ENNReal) * (c : ENNReal) := by gcongr
        _ = (C : ENNReal) * ((C⁻¹ : NNReal) : ENNReal) := by rfl
        _ = 1 := by
          rw [← ENNReal.coe_mul, mul_inv_cancel₀ hC0]
          norm_num
    have hδx_eq : (δ : ENNReal) ^ x = (δ : ENNReal) ^ a * (δ : ENNReal) ^ y := by
      rw [show x = a + y from by dsimp [a]; ring]
      rw [ENNReal.rpow_add a y hδne0 hδne_top]
    calc
      (C : ENNReal) * (δ : ENNReal) ^ x
          = (C : ENNReal) * (δ : ENNReal) ^ a * (δ : ENNReal) ^ y := by
            rw [hδx_eq, mul_assoc]
      _ ≤ 1 * (δ : ENNReal) ^ y := by gcongr
      _ = (δ : ENNReal) ^ y := by simp

/-- **The fine-fibre Frostman bound of the two-scale output** (blueprint
`lem:ml1bootFactorTwoScales`(f), as the fine factor consumes it).

`Kakeya.ml1Boot.IsFactorTwoScales.frostman_fine` compares the *refined* fine fibre against
the unrefined one at the cost of one `δ ^ (-ε')`.  Given the unrefined bound at `a + ε'` —
which is what `Kakeya.ml1Boot.exists_caseTwoData`(ii) supplies — the refined fibre satisfies
the bound at `a + 2 ε'`, stated for the shading `Y'` rather than for `𝕋`, which is the family
`Kakeya.ml1Boot.multiplicity_le_fine` is applied to.  The transport from `𝕋` to `Y'` is
`Kakeya.ml1Boot.frostmanConstIn_congr` along
`Kakeya.ml1Boot.IsFactorTwoScales.fine_shade`.

This is where the exponent `a' = η_{j-1} + 2 ε'` of the fine and coarse factors comes from. -/
theorem frostmanConstIn_fine_fibre_le_of_isFactorTwoScales
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : NNReal} (hδ : 0 < δ) {ε' a : ℝ}
    {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset lc} {Tθ : lc → Tube θ E} {pθ : κ → lc}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset lc}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : lc → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ)
    {k : κ} (hk : k ∈ t'τ)
    (hunref : frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody)
      (Tτ k).toConvexSpaceBody ≤ (δ : ENNReal) ^ (-(a + ε'))) :
    frostmanConstIn (fibre s' pτ k) (fun i => (Y' i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
      ≤ (δ : ENNReal) ^ (-(a + 2 * ε')) := by
  -- The body family on the left agrees with 𝕋 on the fibre of s'.
  have hmemo : ∀ i ∈ fibre s' pτ k, (Y' i).toConvexSpaceBody = (T i).toConvexSpaceBody := by
    intro i hi
    exact congrArg (fun T : Tube δ E => T.toConvexSpaceBody)
      (h.fine_shade i (Finset.mem_filter.mp hi).1).1
  calc
    frostmanConstIn (fibre s' pτ k) (fun i => (Y' i).toConvexSpaceBody)
        (Tτ k).toConvexSpaceBody
        = frostmanConstIn (fibre s' pτ k) (fun i => (T i).toConvexSpaceBody)
            (Tτ k).toConvexSpaceBody := by
            exact frostmanConstIn_congr (fibre s' pτ k) (K := (Tτ k).toConvexSpaceBody)
              (W := fun i => (Y' i).toConvexSpaceBody)
              (W' := fun i => (T i).toConvexSpaceBody) hmemo
    _ ≤ (δ : ENNReal) ^ (-ε') * frostmanConstIn (fibre s pτ k)
          (fun i => (T i).toConvexSpaceBody) (Tτ k).toConvexSpaceBody :=
          h.frostman_fine k hk
    _ ≤ (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-(a + ε')) := by
          exact mul_le_mul_right hunref _
    _ = (δ : ENNReal) ^ (-(a + 2 * ε')) := by
          have hδ0 : (δ : ENNReal) ≠ 0 := ne_of_gt (ENNReal.coe_pos.mpr hδ)
          have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
          rw [← ENNReal.rpow_add (-ε') (-(a + ε')) hδ0 hδtop]
          congr 1
          ring

/-- **The middle-fibre hypothesis block of the two-scale output** (blueprint
`lem:ml1bootFactorTwoScales`(b), (d), (e), (h), as the middle factor consumes it).

For a retained coarse index `l' ∈ t'_θ`, the six family hypotheses that
`Kakeya.ml1Boot.multiplicity_le_middle` asks of `u = 𝕋_τ[T_{θ,l'}]|_{t'_τ}` shaded by `Y_τ`,
at comparability constant `Λ = 2`, common density `μ₀ = λ_τ` and uniformity constant
`Kakeya.ml1Boot.uniformize.C 3`:

* nonemptiness, from `Kakeya.ml1Boot.IsFactorTwoScales.branch_mid_card` and `0 < N_θ`;
* uniformity of the *fibre*, in the one-sided reading `Kakeya.IsFlatPrismUniform`, which is the
  dedicated field `Kakeya.ml1Boot.IsFactorTwoScales.midFibreUnif` and not a consequence of
  `mid_unif`;
* containment in the coarse parent, from the middle-scale parent family together with
  `Kakeya.ml1Boot.IsFactorTwoScales.mid_tube` and `.mid_subset`;
* essential distinctness, from `.mid_essDistinct` along `.mid_tube`;
* the two-sided density bracket, from `.mid_dens` along `.mid_tube`;
* the fullness lower bound `λ_τ ≤ λ(u, Y_τ)`, from the termwise half of `.mid_dens` through
  `Kakeya.ml1Boot.le_fullness_of_dens_lower`.

The absolute fullness threshold `δ ^ η(γ) ≤ λ_τ` is *not* here: `mid_fullness` bounds `λ_τ`
below only by a multiple of `λ(𝕋, Y)`, so it is owed by the caller. -/
theorem midFibre_input_of_isFactorTwoScales [Nontrivial E]
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : NNReal} (hτ : 0 < τ) {ε' : ℝ}
    {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset lc} {Tθ : lc → Tube θ E} {pθ : κ → lc}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset lc}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : lc → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ)
    (hNθ : 0 < Nθ)
    (hparent : IsParentFamily tτ Tτ tθ Tθ pθ)
    {l' : lc} (hl' : l' ∈ t'θ) :
    (fibre t'τ pθ l').Nonempty ∧
      Nonempty (IsFlatPrismUniform (fibre t'τ pθ l') Yτ
        (Tube.ssfGridLen τ) (uniformize.C 3)) ∧
      (∀ k ∈ fibre t'τ pθ l', (Yτ k).carrier ⊆ (Tθ l').carrier) ∧
      ((fibre t'τ pθ l' : Set κ).Pairwise
        (fun k k' => IsEssentiallyDistinct (Yτ k).carrier (Yτ k').carrier)) ∧
      (∀ k ∈ fibre t'τ pθ l',
        ((2 : NNReal) : ENNReal)⁻¹ * (lamτ : ENNReal) * volume (Yτ k).carrier
            ≤ volume (Yτ k).shade ∧
          volume (Yτ k).shade
            ≤ ((2 : NNReal) : ENNReal) * (lamτ : ENNReal) * volume (Yτ k).carrier) ∧
      (lamτ : ENNReal)
        ≤ (ShadedBody.fullness (fibre t'τ pθ l') (fun k => (Yτ k).toShadedBody) : ENNReal) := by
  have hnonempty : (fibre t'τ pθ l').Nonempty := by
    have hNθ_pos : 0 < (Nθ : ENNReal) := ENNReal.coe_pos.mpr hNθ
    have hle : (Nθ : ENNReal) ≤ ((fibre t'τ pθ l').card : ENNReal) :=
      (h.branch_mid_card l' hl').1
    have hcard0 : 0 < (fibre t'τ pθ l').card := by
      exact_mod_cast (lt_of_lt_of_le hNθ_pos hle)
    exact Finset.card_pos.mp hcard0
  have hdens_lower : ∀ k ∈ fibre t'τ pθ l',
      (lamτ : ENNReal) * volume (Yτ k).carrier ≤ volume (Yτ k).shade := by
    intro k hk
    have hkt'τ : k ∈ t'τ := (Finset.mem_filter.mp hk).1
    have hdens := (h.mid_dens k hkt'τ).1
    have hcar : (Yτ k).carrier = (Tτ k).carrier := by
      exact congrArg (fun T : Tube τ E => T.carrier) (h.mid_tube k hkt'τ)
    simpa [hcar] using hdens
  refine ⟨hnonempty, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.midFibreUnif l' hl'
  · intro k hk
    have hkt'τ : k ∈ t'τ := (Finset.mem_filter.mp hk).1
    have hkpθ : pθ k = l' := (Finset.mem_filter.mp hk).2
    have hktτ : k ∈ tτ := h.mid_subset hkt'τ
    have hle : (Tτ k).toConvexSpaceBody ≤ (Tθ (pθ k)).toConvexSpaceBody :=
      hparent.le_parent k hktτ
    have hle' : (Tτ k).toConvexSpaceBody ≤ (Tθ l').toConvexSpaceBody := by
      simpa [hkpθ] using hle
    have hcar : (Yτ k).carrier = (Tτ k).carrier := by
      exact congrArg (fun T : Tube τ E => T.carrier) (h.mid_tube k hkt'τ)
    rw [hcar]
    exact hle'
  · intro k hk k' hk' hne'
    have hkt'τ : k ∈ t'τ := (Finset.mem_filter.mp hk).1
    have hkt'τ' : k' ∈ t'τ := (Finset.mem_filter.mp hk').1
    have hED : IsEssentiallyDistinct (Tτ k).carrier (Tτ k').carrier :=
      h.mid_essDistinct hkt'τ hkt'τ' hne'
    have hcar_k : (Yτ k).carrier = (Tτ k).carrier := by
      exact congrArg (fun T : Tube τ E => T.carrier) (h.mid_tube k hkt'τ)
    have hcar_k' : (Yτ k').carrier = (Tτ k').carrier := by
      exact congrArg (fun T : Tube τ E => T.carrier) (h.mid_tube k' hkt'τ')
    rw [hcar_k, hcar_k']
    exact hED
  · intro k hk
    have hkt'τ : k ∈ t'τ := (Finset.mem_filter.mp hk).1
    have hdens := h.mid_dens k hkt'τ
    have hcar : (Yτ k).carrier = (Tτ k).carrier := by
      exact congrArg (fun T : Tube τ E => T.carrier) (h.mid_tube k hkt'τ)
    constructor
    · calc
        ((2 : NNReal) : ENNReal)⁻¹ * (lamτ : ENNReal) * volume (Yτ k).carrier
            ≤ (1 : ENNReal) * (lamτ : ENNReal) * volume (Yτ k).carrier := by
              exact mul_le_mul
                (mul_le_mul (by norm_num : ((2 : NNReal) : ENNReal)⁻¹ ≤ (1 : ENNReal))
                  le_rfl zero_le zero_le)
                le_rfl zero_le zero_le
        _ = (lamτ : ENNReal) * volume (Yτ k).carrier := by simp
        _ ≤ volume (Yτ k).shade := by
              simpa [hcar] using hdens.1
    · simpa [hcar] using hdens.2
  · exact le_fullness_of_dens_lower hτ hnonempty Yτ hdens_lower

/-- **The coarse hypothesis block of the two-scale output** (blueprint
`lem:ml1bootFactorTwoScales`(c), as the coarse factor consumes it).

The three family hypotheses that `Kakeya.ml1Boot.multiplicity_le_coarse` asks of
`𝕋_θ|_{t'_θ}` shaded by `Y_θ`: the `B₁` containment, transported from the given coarse tubes
along `Kakeya.ml1Boot.IsFactorTwoScales.coarse_tube`; essential distinctness, from
`.coarse_essDistinct` along the same equality; and the fullness lower bound `λ_θ ≤ λ(t'_θ,
Y_θ)`, from the termwise half of `.coarse_dens` through
`Kakeya.ml1Boot.le_fullness_of_dens_lower`.

As on the middle side, the absolute threshold `δ ^ ηs ≤ λ_θ` is owed by the caller:
`coarse_fullness` bounds `λ_θ` below only by a multiple of `λ(𝕋, Y)`. -/
theorem coarse_input_of_isFactorTwoScales [Nontrivial E]
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {δ τ θ : NNReal} (hθ : 0 < θ) {ε' : ℝ}
    {s : Finset ι} {T : ι → ShadedTube δ E}
    {tτ : Finset κ} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {tθ : Finset lc} {Tθ : lc → Tube θ E} {pθ : κ → lc}
    {s' : Finset ι} {t''τ t'τ : Finset κ} {t'θ : Finset lc}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : lc → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ)
    (hne : t'θ.Nonempty)
    (hball : ∀ l' ∈ t'θ, (Tθ l').carrier ⊆ Metric.closedBall 0 1) :
    (∀ l' ∈ t'θ, (Yθ l').carrier ⊆ Metric.closedBall 0 1) ∧
      ((t'θ : Set lc).Pairwise
        (fun l₁ l₂ => IsEssentiallyDistinct (Yθ l₁).carrier (Yθ l₂).carrier)) ∧
      (lamθ : ENNReal)
        ≤ (ShadedBody.fullness t'θ (fun l' => (Yθ l').toShadedBody) : ENNReal) := by
  have hdens_lower : ∀ l' ∈ t'θ,
      (lamθ : ENNReal) * volume (Yθ l').carrier ≤ volume (Yθ l').shade := by
    intro l' hl'
    have hdens := (h.coarse_dens l' hl').1
    have hcar : (Yθ l').carrier = (Tθ l').carrier := by
      exact congrArg (fun T : Tube θ E => T.carrier) (h.coarse_tube l' hl')
    simpa [hcar] using hdens
  refine ⟨?_, ?_, ?_⟩
  · intro l' hl'
    have hcar : (Yθ l').carrier = (Tθ l').carrier := by
      exact congrArg (fun T : Tube θ E => T.carrier) (h.coarse_tube l' hl')
    rw [hcar]
    exact hball l' hl'
  · intro l₁ hl₁ l₂ hl₂ hne'
    have hED : IsEssentiallyDistinct (Tθ l₁).carrier (Tθ l₂).carrier :=
      h.coarse_essDistinct hl₁ hl₂ hne'
    have hcar₁ : (Yθ l₁).carrier = (Tθ l₁).carrier := by
      exact congrArg (fun T : Tube θ E => T.carrier) (h.coarse_tube l₁ hl₁)
    have hcar₂ : (Yθ l₂).carrier = (Tθ l₂).carrier := by
      exact congrArg (fun T : Tube θ E => T.carrier) (h.coarse_tube l₂ hl₂)
    rw [hcar₁, hcar₂]
    exact hED
  · exact le_fullness_of_dens_lower hθ hne Yθ hdens_lower

/-- **The fine factor, read off the two-scale output** (blueprint `lem:ml1bootFineFactor`
applied to `lem:ml1bootFactorTwoScales`).

`Kakeya.ml1Boot.multiplicity_le_fine` at `Λ = 2` and `a' = a + 2 ε'`, with its three
hypotheses supplied from a `Kakeya.ml1Boot.IsFactorTwoScales` package:
`Kakeya.ml1Boot.isFineFibre_of_isFactorTwoScales` for the fibre package,
`Kakeya.ml1Boot.frostmanConstIn_fine_fibre_le_of_isFactorTwoScales` for the Frostman bound —
which is why the unrefined bound is asked for at `a + ε'` and the conclusion is at
`a + 2 ε'` — and `Kakeya.ml1Boot.eventually_const_mul_rpow_le` for the absorption of the
fixed constant `C² Λ²`, which needs `e < 3 (a + 2 ε')`. -/
theorem multiplicity_le_fine_of_isFactorTwoScales [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hKF : FrostmanEstimate.{u} E γ) {e a ε' : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hε' : 0 < ε')
    (hgap : e < 3 * (a + 2 * ε')) :
    ∃ ηs > (0 : ℝ),
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ τ : NNReal, δ ≤ τ → τ ≤ 1 →
        ∀ {ι κ lc : Type u} [DecidableEq κ] [DecidableEq lc] {θ : NNReal}
          {s s' : Finset ι} {tτ t''τ t'τ : Finset κ} {tθ t'θ : Finset lc}
          (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
          (Tθ : lc → Tube θ E) (pθ : κ → lc)
          (Y' : ι → ShadedTube δ E) (Yτ : κ → ShadedTube τ E) (Yθ : lc → ShadedTube θ E)
          {lamδ lamτ lamθ Nτ Nθ : NNReal},
          IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
            lamδ lamτ lamθ Nτ Nθ →
          0 < lamδ → 0 < Nτ →
          IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
          ∀ k ∈ t'τ,
            (Tτ k).carrier ⊆ Metric.closedBall 0 1 →
            (fineFactor.C : ENNReal) * (2 : ENNReal) ^ 2 * (δ : ENNReal) ^ ηs
              ≤ (lamδ : ENNReal) →
            frostmanConstIn (fibre s pτ k) (fun i => (T i).toConvexSpaceBody)
                (Tτ k).toConvexSpaceBody ≤ (δ : ENNReal) ^ (-(a + ε')) →
            ShadedBody.multiplicity (fibre s' pτ k) (fun i => (Y' i).toShadedBody)
              ≤ (δ : ENNReal) ^ (-4 * (a + 2 * ε'))
                * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
                * (((fibre s' pτ k).card : ENNReal)
                    * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  obtain ⟨ηs, hηs, H⟩ := multiplicity_le_fine hdim hγ0 hγ1 hKF e he
  refine ⟨ηs, hηs, ?_⟩
  filter_upwards [H (2 : NNReal) (by norm_num) (a + 2 * ε') (by linarith),
    eventually_const_mul_rpow_le (fineFactor.C ^ 2 * 4)
      (show -4 * (a + 2 * ε') < -e - (a + 2 * ε') by linarith),
    self_mem_nhdsWithin] with δ hH habs hδpos
  intro τ hδτ hτ1 ι κ lc _ _ θ s s' tτ t''τ t'τ tθ t'θ T Tτ pτ Tθ pθ Y' Yτ Yθ
    lamδ lamτ lamθ Nτ Nθ h hlamδ hNτ hparent k hk hball hfull hfr
  have hfib := isFineFibre_of_isFactorTwoScales hδpos h hlamδ hNτ hparent hk hball hfull
  have hfr' := frostmanConstIn_fine_fibre_le_of_isFactorTwoScales hδpos h hk hfr
  have hconst : (fineFactor.C : ENNReal) ^ 2 * ((2 : NNReal) : ENNReal) ^ 2
      = ((fineFactor.C ^ 2 * 4 : NNReal) : ENNReal) := by
    norm_num [ENNReal.coe_pow, ENNReal.coe_mul]
  have habs' : (fineFactor.C : ENNReal) ^ 2 * ((2 : NNReal) : ENNReal) ^ 2
      * (δ : ENNReal) ^ (-e - (a + 2 * ε')) ≤ (δ : ENNReal) ^ (-4 * (a + 2 * ε')) := by
    rw [hconst]
    exact habs
  exact hH τ hδτ hτ1 (Tτ k) Y' hfib hfr' habs'

/-- **The coarse factor, read off the two-scale output** (blueprint
`lem:ml1bootCoarseFactor` applied to `lem:ml1bootFactorTwoScales`).

`Kakeya.ml1Boot.multiplicity_le_coarse` at `L = 1` and `n₀ = a' = a + 2 ε'`, with its family
hypotheses supplied by `Kakeya.ml1Boot.coarse_input_of_isFactorTwoScales`.  Its absorption
hypothesis is `δ ^ (-a' - e) ≤ δ ^ (-4 a')`, which for `δ ≤ 1` is just the exponent
inequality `e ≤ 3 a'`; no smallness of `δ` is needed, since `L = 1` carries no constant. -/
theorem multiplicity_le_coarse_of_isFactorTwoScales [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hKF : FrostmanEstimate.{u} E γ) {e a ε' : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hε' : 0 < ε')
    (hgap : e ≤ 3 * (a + 2 * ε')) :
    ∃ ηs > (0 : ℝ),
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ θ : NNReal, δ ≤ θ → θ ≤ 1 →
        ∀ {ι κ lc : Type u} [DecidableEq κ] [DecidableEq lc] {τ : NNReal}
          {s s' : Finset ι} {tτ t''τ t'τ : Finset κ} {tθ t'θ : Finset lc}
          (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
          (Tθ : lc → Tube θ E) (pθ : κ → lc)
          (Y' : ι → ShadedTube δ E) (Yτ : κ → ShadedTube τ E) (Yθ : lc → ShadedTube θ E)
          {lamδ lamτ lamθ Nτ Nθ : NNReal},
          IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
            lamδ lamτ lamθ Nτ Nθ →
          t'θ.Nonempty →
          (∀ l' ∈ t'θ, (Tθ l').carrier ⊆ Metric.closedBall 0 1) →
          (δ : ENNReal) ^ ηs ≤ (lamθ : ENNReal) →
          frostmanConstIn t'θ (fun l' => (Yθ l').toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            ≤ (δ : ENNReal) ^ (-(a + 2 * ε')) →
          ShadedBody.multiplicity t'θ (fun l' => (Yθ l').toShadedBody)
            ≤ (δ : ENNReal) ^ (-4 * (a + 2 * ε')) * (θ : ENNReal) ^ (-2 * γ)
              * ((t'θ.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  obtain ⟨ηs, hηs, H⟩ := multiplicity_le_coarse hdim hγ0 hγ1 hKF e he
  refine ⟨ηs, hηs, ?_⟩
  filter_upwards [H 1 le_rfl (a + 2 * ε') (a + 2 * ε') (by linarith) (by linarith),
    self_mem_nhdsWithin] with δ hH hδpos
  intro θ hδθ hθ1 ι κ lc _ _ τ s s' tτ t''τ t'τ tθ t'θ T Tτ pτ Tθ pθ Y' Yτ Yθ
    lamδ lamτ lamθ Nτ Nθ h hne hball hlam hfr
  obtain ⟨hballY, hED, hfullY⟩ :=
    coarse_input_of_isFactorTwoScales (lt_of_lt_of_le hδpos hδθ) h hne hball
  have habsorb : ((1 : NNReal) : ENNReal) * (δ : ENNReal) ^ (-(a + 2 * ε') - e)
      ≤ (δ : ENNReal) ^ (-4 * (a + 2 * ε')) := by
    have hδ1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast (le_trans hδθ hθ1)
    have hexp : -4 * (a + 2 * ε') ≤ -(a + 2 * ε') - e := by linarith [hgap]
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hexp
  exact hH θ hδθ hθ1 Yθ hne hballY hED (by simpa using hfr) (le_trans hlam hfullY) habsorb

/-- **The Case (ii) collapse, given the three factor bounds** (blueprint
`lem:ml1bootCaseNonSticky` applied to `lem:ml1bootFactorTwoScales`).

`Kakeya.ml1Boot.multiplicity_le_of_middle` at `C_u = 2`, `m = |s|` and `ℓ = 0`, with its
triple-product hypothesis taken from `Kakeya.ml1Boot.IsFactorTwoScales.product` and its
uniformity count from `Kakeya.ml1Boot.fibre_product_card_le` (which gives `2² |s|`, weakened
to the `2⁴ |s|` the lemma is stated with).  The absorption hypothesis is stated in the
`≤ 1` form that `ℓ = 0` forces, and the loss factor `δ ^ (-ℓ) = 1` is discharged here, so the
conclusion is loss-free. -/
theorem multiplicity_le_collapse_of_isFactorTwoScales
    {δ τ θ : NNReal} (hδ0 : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    {γ ν a a' ε' ηvol : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hν0 : 0 < ν) (hνγ : ν ≤ γ)
    (ha : 0 ≤ a) (haa' : a ≤ a') (hgain : 8 * a' ≤ 10 * a) (hε' : 0 < ε')
    (hηvol : 0 ≤ ηvol) {c₃ : NNReal} (hc₃0 : 0 < c₃) (hc₃1 : c₃ ≤ 1)
    {ι κ lc : Type*} [DecidableEq κ] [DecidableEq lc]
    {s s' : Finset ι} {tτ t''τ t'τ : Finset κ} {tθ t'θ : Finset lc}
    {T : ι → ShadedTube δ E} {Tτ : κ → Tube τ E} {pτ : ι → κ}
    {Tθ : lc → Tube θ E} {pθ : κ → lc}
    {Y' : ι → ShadedTube δ E} {Yτ : κ → ShadedTube τ E} {Yθ : lc → ShadedTube θ E}
    {lamδ lamτ lamθ Nτ Nθ : NNReal}
    (h : IsFactorTwoScales ε' s T tτ Tτ pτ tθ Tθ pθ s' t''τ t'τ t'θ Y' Yτ Yθ
      lamδ lamτ lamθ Nτ Nθ)
    {k₀ : κ} (hk₀ : k₀ ∈ t'τ) {l₀ : lc} (hl₀ : l₀ ∈ t'θ)
    (hscard : 0 < s.card)
    (hne₁ : (fibre s' pτ k₀).Nonempty) (hne₂ : (fibre t'τ pθ l₀).Nonempty)
    (hfine : ShadedBody.multiplicity (fibre s' pτ k₀) (fun i => (Y' i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-4 * a') * ((δ / τ : NNReal) : ENNReal) ^ (-2 * γ)
        * (((fibre s' pτ k₀).card : ENNReal)
            * ((δ / τ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hmiddle : ShadedBody.multiplicity (fibre t'τ pθ l₀) (fun k => (Yτ k).toShadedBody)
      ≤ (δ : ENNReal) ^ (10 * a) * ((τ / θ : NNReal) : ENNReal) ^ (-2 * γ)
        * (((fibre t'τ pθ l₀).card : ENNReal)
            * ((τ / θ : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hcoarse : ShadedBody.multiplicity t'θ (fun l' => (Yθ l').toShadedBody)
      ≤ (δ : ENNReal) ^ (-4 * a') * (θ : ENNReal) ^ (-2 * γ)
        * ((t'θ.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2))
    (hvol : (c₃ : ENNReal) * (δ : ENNReal) ^ ηvol
      ≤ (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ))
    (habsorb : (factorTwoScales.C s.card δ t''τ.card τ : ENNReal) * (2 : ENNReal) ^ 4
      * (c₃ : ENNReal) ^ (-ν / 2)
      * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (10 * a - 8 * a')
      * (δ : ENNReal) ^ (-2 * ν - ηvol * ν / 2) ≤ 1) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-2 * (γ - ν))
        * ((s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - ν) / 2) := by
  have hP₁ : (1 : ENNReal) ≤ ((fibre s' pτ k₀).card : ENNReal) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hne₁))
  have hP₂ : (1 : ENNReal) ≤ ((fibre t'τ pθ l₀).card : ENNReal) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hne₂))
  have hP₃ : (1 : ENNReal) ≤ (t'θ.card : ENNReal) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨l₀, hl₀⟩))
  have htriple : ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ (factorTwoScales.C s.card δ t''τ.card τ : ENNReal) * (δ : ENNReal) ^ (-ε')
        * ShadedBody.multiplicity (fibre s' pτ k₀) (fun i => (Y' i).toShadedBody)
        * ShadedBody.multiplicity (fibre t'τ pθ l₀) (fun k => (Yτ k).toShadedBody)
        * ShadedBody.multiplicity t'θ (fun l₂ => (Yθ l₂).toShadedBody) :=
    h.product k₀ hk₀ l₀ hl₀
  have hunif : ((fibre s' pτ k₀).card : ENNReal) * ((fibre t'τ pθ l₀).card : ENNReal)
        * (t'θ.card : ENNReal) ≤ (2 : ENNReal) ^ 4 * (s.card : ENNReal) := by
    have hpc : ((fibre s' pτ k₀).card : ENNReal) * ((fibre t'τ pθ l₀).card : ENNReal)
          * (t'θ.card : ENNReal) ≤ (2 : ENNReal) ^ 2 * (s.card : ENNReal) := by
      exact_mod_cast (fibre_product_card_le h hk₀ hl₀)
    have h24 : (2 : ENNReal) ^ 2 ≤ (2 : ENNReal) ^ 4 := by
      norm_num
    calc
      ((fibre s' pτ k₀).card : ENNReal) * ((fibre t'τ pθ l₀).card : ENNReal)
          * (t'θ.card : ENNReal) ≤ (2 : ENNReal) ^ 2 * (s.card : ENNReal) := hpc
      _ ≤ (2 : ENNReal) ^ 4 * (s.card : ENNReal) := by
        exact mul_le_mul h24 le_rfl zero_le zero_le
  have habsorb' :
      (factorTwoScales.C s.card δ t''τ.card τ : ENNReal) * (2 : ENNReal) ^ 4
        * (c₃ : ENNReal) ^ (-ν / 2)
        * (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (10 * a - 8 * a')
        * (δ : ENNReal) ^ (-2 * ν - ηvol * ν / 2) ≤ (δ : ENNReal) ^ (-(0 : ℝ)) := by
    simpa [neg_zero, ENNReal.rpow_zero] using habsorb
  have hres : ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-(0 : ℝ)) * (δ : ENNReal) ^ (-2 * (γ - ν))
        * ((s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - ν) / 2) :=
    multiplicity_le_of_middle hδ0 hδτ hτθ hθ1
      (ν := ν) (ℓ := 0) (η := ηvol) (a := a) (a' := a') (ε' := ε')
      hηvol ha haa' hgain hε' (by norm_num : 0 ≤ (0 : ℝ))
      hγ0 hγ1 hν0 hνγ
      (Cu := (2 : NNReal)) (by norm_num : (1 : NNReal) ≤ 2)
      (m := s.card) hscard
      (c₃ := c₃) hc₃0 hc₃1
      hP₁ hP₂ hP₃ htriple hfine hmiddle hcoarse hunif hvol habsorb'
  simpa [neg_zero, ENNReal.rpow_zero, one_mul] using hres

end FineFibreFromFactorTwoScales

end ml1Boot

end Kakeya
