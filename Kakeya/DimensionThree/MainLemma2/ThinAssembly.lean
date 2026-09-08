/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Combined
public import Kakeya.DimensionThree.MainLemma2.ThinEccentricity
public import Kakeya.DimensionThree.MainLemma2.ThinFactorFamily
public import Kakeya.DimensionThree.MainLemma2.ThinFibreDensity

/-!
# Assembling the data of the thin-case factoring step

`Kakeya.ThinCase.factoringApply` asserts the existence of a refined segment family, a retained
body family and two shadings satisfying thirteen conjuncts. This file builds that data and
discharges all thirteen, each at its own explicit constant
(`Kakeya.ThinCase.exists_factoringApplyData`).

**Why this file can exist at all.** `factoringApply` is *stated* in
`Kakeya.DimensionThree.MainLemma2.ThinSetup`, and until now every one of its ingredients lived in
a file that *imported* `ThinSetup` — so the statement was unreachable from its own machinery.
`ThinFactorFamily`'s import of `ThinSetup` turned out to be spurious: its only non-comment uses
are `factoringApplyCore`, `factoringApplyCore_spec` and `one_le_factoringApplyCore`, all of which
live in `ThinCore`. With that import corrected the whole stack sits below `ThinSetup`, which now
imports it.

**The envelope.** Every conjunct of `Kakeya.ThinCase.exists_factoringApplyData` has to be read
at `Kakeya.ThinCase.factoringApplyConstant CF Cfull Ccore`. Conjuncts (iii)(a) and (iii)(b) are
priced by `hCcore2`; conjunct (iv) by
`Kakeya.ThinCase.equalRadiusMultConstant_le_thinEnvelopeTerm`; conjunct (vi) — whose constant
carries the fibre-density band loss `Kakeya.ThinCase.fibreDensityBandLoss` — by
`Kakeya.ThinCase.inv_thinGlobalRetention_le_thinEnvelopeTerm`; and conjunct (i), at
`Kakeya.ThinCase.thinCellFullnessConstant` (GWZ's Item 2 constant
`CF · Cfull² · C · (N + 1) / θ²`, quadratic in the total retention loss), by
`Kakeya.ThinCase.thinCellFullnessConstant_le_mul_thinEnvelopeTerm`. All four are branches of the
single `hCcoreNet` term `Kakeya.ThinCase.thinEnvelopeTerm`, a function of the dimension, the two
cardinalities, `CF` and `w₁` only — the eccentricity exponent it needs is
`Kakeya.ThinCase.thinEccentricityExponent`, the value `Kakeya.ThinCase.thinVolumeRatio` gives it.
`Kakeya.ThinCase.factoringApply` (in `Kakeya.DimensionThree.MainLemma2.ThinSetup`) is
`exists_factoringApplyData` followed by this envelope.
-/

@[expose] public section

open MeasureTheory Metric Set ShadedBody Convexity
open scoped ENNReal NNReal

namespace Kakeya.ThinCase

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The mass a `Kakeya.ThinCase.exists_factoringApplyData` output may discard, after the
pipeline.** The three factors are the three pigeonholes that run on top of
`ShadedBody.outerFactoringFamily`: the inner dyadic band of
`ShadedBody.exists_constantMultiplicity_refinement_band` (a logarithm in the number of segments),
the ball net of `Kakeya.ThinCase.exists_comparableNet` at scale `r` inside a ball of radius `R`
(its own `Kakeya.ThinCase.ballNetLoss`, times `4` for the two conversions between the Lebesgue
measure of the shaded union and the sum of the shade volumes), and the cell pigeonhole of
`Kakeya.ThinCase.exists_cellOuterShading` (a logarithm in the number of bodies, times the `5 ^ n`
overlap of the net's own balls).

It is a *product*, not a sum. Conjunct (vi) is the only conjunct that sees all four losses at
once, which is why the `Ccore` binder that pays for it has to dominate the product and not the
terms: each pigeonhole discards a fraction of what the previous one left. -/
noncomputable def thinRetentionLoss (n ns nb : ℕ) (r R : ℝ) : NNReal :=
  ((Nat.log 2 ns + 1 : ℕ) : NNReal) * (4 * ballNetLoss n r R) *
    ((5 : NNReal) ^ n * ((Nat.log 2 nb + 1 : ℕ) : NNReal))

/-- **The pipeline's own retained fraction is positive.**

`ShadedBody.outerFactoringFamily_refinement.c` is a product of three inverses, and in `ℝ≥0` an
inverse vanishes exactly when its argument does, so this is the statement that none of the three
pipeline losses is infinite. Only the Step 1 factor needs the hypotheses: its
`Kakeya.factoringStep1FiberPigeonholeConstant` is `(1 + log₂ (b / a))⁺`, which vanishes once the
ratio drops below `1 / 2`, and `0 < N` together with `δ ≤ 1` is what keeps the ratio at least `1`.

Conjunct (vi) needs this because `Kakeya.ThinCase.thinRefinement_mass` states the pipeline's
retention as `c * (old mass) ≤ (new mass)`, and turning that into an upper bound for the old mass
divides by `c`. -/
lemma refinement_c_pos (n : ℕ) {N : ℕ} (hN : 0 < N) {δ : NNReal} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    0 < ShadedBody.outerFactoringFamily_refinement.c n N δ := by
  have hone : (1 : NNReal) ≤ ShadedBody.step5PackingRatio n N δ := by
    rw [ShadedBody.step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
    have hfact : (1 : NNReal) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hN : (1 : NNReal) ≤ max 1 N := by exact_mod_cast le_max_left 1 N
    have hinv : (1 : NNReal) ≤ (δ ^ n)⁻¹ := by
      rw [one_le_inv₀ (pow_pos hδ n)]
      exact pow_le_one₀ δ.coe_nonneg hδ1
    calc
      1 ≤ (2 : NNReal) ^ n := one_le_pow₀ (by norm_num)
      _ ≤ 2 ^ n * (2 ^ n * 1 * 1 * 1) := by
        simpa using le_mul_of_one_le_right (by positivity : (0 : NNReal) ≤ 2 ^ n)
          (one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2))
      _ ≤ 2 ^ n * (2 ^ n * n.factorial * max 1 N * (δ ^ n)⁻¹) := by gcongr
  have h5 : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
      (ShadedBody.step5PackingRatio n N δ) :=
    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant_pos hone
  have hratio : (1 : NNReal) ≤
      Kakeya.step1UpperBdAtScale n N / Kakeya.step1LowerBdAtScale n δ := by
    rw [Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n N hδ]
    have hfact : (1 : NNReal) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hNN : (1 : NNReal) ≤ (N : NNReal) := by exact_mod_cast hN
    have hinv : (1 : NNReal) ≤ (δ ^ n)⁻¹ := by
      rw [one_le_inv₀ (pow_pos hδ n)]
      exact pow_le_one₀ δ.coe_nonneg hδ1
    have h2n : (1 : NNReal) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    calc (1 : NNReal) = 1 * 1 * 1 * 1 := by ring
      _ ≤ 2 ^ n * (n.factorial : NNReal) * N * (δ ^ n)⁻¹ := by gcongr
  have h1 : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
    rw [Kakeya.factoringStep1AtScaleConstant_def, Kakeya.factoringStep1PigeonholeConstant_eq]
    have hcoe : (1 : ℝ) ≤ ((Kakeya.step1UpperBdAtScale n N : ℝ) /
        (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
      have := hratio
      rw [← NNReal.coe_le_coe] at this
      simpa using this
    have hlog : (0 : ℝ) ≤ Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
        (Kakeya.step1LowerBdAtScale n δ : ℝ)) :=
      Real.logb_nonneg (by norm_num) hcoe
    have : (0 : NNReal) < Kakeya.factoringStep1FiberPigeonholeConstant
        (Kakeya.step1LowerBdAtScale n δ) (Kakeya.step1UpperBdAtScale n N) := by
      rw [Kakeya.factoringStep1FiberPigeonholeConstant, ← NNReal.coe_lt_coe,
        Real.coe_toNNReal _ (by linarith)]
      push_cast
      linarith
    positivity
  have h23 : 0 < ((Kakeya.factoringStep2Step3Constant N : ℕ) : NNReal) := by
    rw [Kakeya.factoringStep2Step3Constant_eq]
    positivity
  rw [ShadedBody.outerFactoringFamily_refinement.c,
    ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant]
  exact mul_pos (mul_pos (inv_pos.mpr h1) (inv_pos.mpr h23)) (inv_pos.mpr h5)

/-- **The global retention of the whole cell construction.** The pipeline's uniform retained
fraction `ShadedBody.factoringCoreAtScaleUniformRefinementConstant`, divided by the product of
the four pigeonhole losses `Kakeya.ThinCase.thinRetentionLoss` and the fibre-density band loss
`Kakeya.ThinCase.fibreDensityBandLoss`: conjunct (vi) of
`Kakeya.ThinCase.exists_factoringApplyData` says that this fraction of the input shade mass
survives all five refinements, and it is the `θ` at which
`Kakeya.ThinCase.fullness_inducedShading_ge_of_globalRetention` is read for conjunct (i). -/
noncomputable def thinGlobalRetention (n ns nb : ℕ) (CF w₁ : NNReal) (N : ℕ) : NNReal :=
  ShadedBody.factoringCoreAtScaleUniformRefinementConstant n ns N w₁ *
    (thinRetentionLoss n ns nb ((w₁ : ℝ) / 8) 2 * (fibreDensityBandLoss n CF ns).toNNReal)⁻¹

/-- **The constant of conjunct (i) for the cell shading**: the induced-shading constant
`Kakeya.ThinCase.thinFibreDensityConstant` at the global retention
`Kakeya.ThinCase.thinGlobalRetention`, times the two dimensional constants of the bridge
`Kakeya.ThinCase.sum_volume_inducedShading_le_mul_sum_volume_cellShade` from the induced to the
cell shading — the collar comparison between the cell radius `2 · (w₁ / 8)` and the collar
radius `2 · τ₂(Wb j) ≤ 4 w₁`, and the cell-collar overlap `Kakeya.ThinCase.cellCollarConstant`. -/
noncomputable def thinCellFullnessConstant (n ns nb : ℕ) (CF Cfull w₁ : NNReal) (N : ℕ) :
    NNReal :=
  thinFibreDensityConstant CF Cfull (thinGlobalRetention n ns nb CF w₁ N) N *
    (collarCompareConstant n (2 * ((w₁ : ℝ) / 8)) (4 * w₁) * (cellCollarConstant n : NNReal))

/-- **The eccentricity exponent of the thin family**, as `Kakeya.ThinCase.thinVolumeRatio` sets
it: `⌊log₂ ⌈CF · |segs| · C_vol⌉₊⌋ + 1` (`Kakeya.ThinCase.twoPowExponent`), a function of the
dimension, the number of segments and the Frostman constant only
(`Kakeya.ThinCase.thinVolumeRatio_exponent`), and logarithmic in all three. It is the `N` at which every
`AtScale` loss constant of `Kakeya.ThinCase.exists_factoringApplyData` is read, and naming it is
what lets `Kakeya.ThinCase.thinEnvelopeTerm` mention those constants with no exponent binder. -/
noncomputable def thinEccentricityExponent (n ns : ℕ) (CF : NNReal) : ℕ :=
  twoPowExponent (CF * (ns : NNReal) * Metric.volume_comparison.C n)

/-- **The single term the strengthened `hCcoreNet` binder adds to `Ccore`.**

Four conjuncts of `Kakeya.ThinCase.factoringApply` are priced above what the other seven
`hCcore*` binders reach, and all four are priced here, as the maximum of four branches. Write
`N = thinEccentricityExponent n ns CF` for the eccentricity exponent,
`c = ShadedBody.factoringCoreAtScaleUniformRefinementConstant n ns N w₁` for the pipeline's
uniform retained fraction, `L = thinRetentionLoss n ns nb (w₁ / 8) 2` for the product of the
four pigeonhole losses, `B = fibreDensityBandLoss n CF ns` for the fibre-density band loss,
`θ = thinGlobalRetention n ns nb CF w₁ N = c / (L · B)` for the global retention, and
`Coll = collarCompareConstant n (w₁ / 4) (4 w₁)`, `Cell = cellCollarConstant n` for the two
dimensional constants of the induced-to-cell bridge.

* Conjunct **(iv)** needs `Kakeya.ThinCase.equalRadiusMultConstant n = 2 * 21 ^ n`, a purely
  dimensional constant that is not a pigeonhole loss at all — no other binder mentions anything of
  its size.
* Conjunct **(vi)** needs `θ⁻¹ = c⁻¹ · L · B`, because `exists_factoringApplyData` states (vi) as
  `c · (old mass) ≤ L · B · (new mass)` and `factoringApply` wants
  `Cfact⁻¹ · (old mass) ≤ (new mass)`. The band-free branch `c⁻¹ · L` — what this term carried
  before the fibre-density band was inserted into the construction — is kept as its own branch, so
  that `Kakeya.ThinCase.inv_mul_thinRetentionLoss_le_thinEnvelopeTerm` holds for every value of
  the parameters (`B ≥ 1` only when `ns · C_vol · CF ≥ 1`).
* Conjunct **(i)** needs the constant of GWZ's Item 2 accounting,
  `Kakeya.ThinCase.thinCellFullnessConstant`, i.e.
  `4 · CF · Cfull² · C_Córdoba · (N + 1) · Coll · Cell / θ²`, to be read at
  `factoringApplyConstant CF Cfull Ccore ≥ 2 · C_vol n · CF · Cfull² · Ccore`. The factor
  `CF · Cfull²` is the one `factoringApplyConstant` already carries, so the fourth branch is
  the quotient `2 · C_Córdoba · (N + 1) · Coll · Cell / (θ² · C_vol n)`
  (`Kakeya.ThinCase.thinCellFullnessConstant_le_mul_thinEnvelopeTerm`). It is *quadratic* in the
  total retention loss `L · B / c`, which is why no earlier binder — each linear in one loss —
  could dominate it.

The retained fraction is taken in its **uniform** form
`ShadedBody.factoringCoreAtScaleUniformRefinementConstant`, not the exact
`ShadedBody.factoringCoreAtScaleRefinementConstant`: the exact one depends on the cover cardinality
selected by the construction, which is not a function of anything `factoringApply` binds, while the
uniform one depends only on the dimension, `segs.card`, the eccentricity exponent and `w₁`. The
uniform one is the smaller (`ShadedBody.factoringCoreAtScaleUniformRefinementConstant_le`), so
dividing by it is the safe direction.

Like the other seven this is a **lower** bound on a parameter, so it can only shrink the set of
admissible `Ccore`; `Kakeya.VeryNotSticky.exists_thinConfig` discharges it by enlarging its `Ccore`
by this one term. It is a function of exactly `(n, ns, nb, CF, w₁)`, so strengthening it leaves the
statement of `factoringApply` untouched. -/
noncomputable def thinEnvelopeTerm (n ns nb : ℕ) (CF w₁ : NNReal) : NNReal :=
  max (equalRadiusMultConstant n)
    (max
      ((ShadedBody.factoringCoreAtScaleUniformRefinementConstant n ns
          (thinEccentricityExponent n ns CF) w₁)⁻¹ *
        thinRetentionLoss n ns nb ((w₁ : ℝ) / 8) 2)
      (max (thinGlobalRetention n ns nb CF w₁ (thinEccentricityExponent n ns CF))⁻¹
        (2 * ShadedBody.lambdaInducedSingleWUniform.C *
            ((thinEccentricityExponent n ns CF : NNReal) + 1) *
            (collarCompareConstant n (2 * ((w₁ : ℝ) / 8)) (4 * w₁) *
              (cellCollarConstant n : NNReal)) /
          (thinGlobalRetention n ns nb CF w₁ (thinEccentricityExponent n ns CF) ^ 2 *
            Metric.volume_comparison.C n))))

lemma equalRadiusMultConstant_le_thinEnvelopeTerm (n ns nb : ℕ) (CF w₁ : NNReal) :
    equalRadiusMultConstant n ≤ thinEnvelopeTerm n ns nb CF w₁ := le_max_left _ _

lemma inv_mul_thinRetentionLoss_le_thinEnvelopeTerm (n ns nb : ℕ) (CF w₁ : NNReal) :
    (ShadedBody.factoringCoreAtScaleUniformRefinementConstant n ns
        (twoPowExponent (CF * (ns : NNReal) * Metric.volume_comparison.C n)) w₁)⁻¹ *
      thinRetentionLoss n ns nb ((w₁ : ℝ) / 8) 2 ≤ thinEnvelopeTerm n ns nb CF w₁ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- Conjunct (vi)'s price: the inverse of the global retention is dominated by the envelope
term. -/
lemma inv_thinGlobalRetention_le_thinEnvelopeTerm (n ns nb : ℕ) (CF w₁ : NNReal) :
    (thinGlobalRetention n ns nb CF w₁ (thinEccentricityExponent n ns CF))⁻¹ ≤
      thinEnvelopeTerm n ns nb CF w₁ :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)

/-- Conjunct (i)'s price: the cell-fullness constant at the canonical eccentricity exponent is
dominated by the third branch of `Kakeya.ThinCase.factoringApplyConstant` read at the envelope
term. The factor `CF · Cfull²` is common to both sides; what the envelope pays for is
`2 · C_Córdoba · (N + 1) · Coll · Cell / θ²`, divided by the `C_vol n` that
`factoringApplyConstant` supplies. -/
lemma thinCellFullnessConstant_le_mul_thinEnvelopeTerm (n ns nb : ℕ) (CF Cfull w₁ : NNReal) :
    thinCellFullnessConstant n ns nb CF Cfull w₁ (thinEccentricityExponent n ns CF) ≤
      2 * Metric.volume_comparison.C n * CF * Cfull ^ 2 * thinEnvelopeTerm n ns nb CF w₁ := by
  have hbranch : 2 * ShadedBody.lambdaInducedSingleWUniform.C *
      ((thinEccentricityExponent n ns CF : NNReal) + 1) *
      (collarCompareConstant n (2 * ((w₁ : ℝ) / 8)) (4 * w₁) * (cellCollarConstant n : NNReal)) /
        (thinGlobalRetention n ns nb CF w₁ (thinEccentricityExponent n ns CF) ^ 2 *
          Metric.volume_comparison.C n) ≤ thinEnvelopeTerm n ns nb CF w₁ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine le_trans (le_of_eq ?_) (mul_le_mul_right hbranch _)
  rw [thinCellFullnessConstant, thinFibreDensityConstant]
  set N : ℕ := thinEccentricityExponent n ns CF with hN
  set θ : NNReal := thinGlobalRetention n ns nb CF w₁ N with hθ
  set X : NNReal := collarCompareConstant n (2 * ((w₁ : ℝ) / 8)) (4 * w₁) *
    (cellCollarConstant n : NNReal) with hX
  set K : NNReal := ShadedBody.lambdaInducedSingleWUniform.C with hK
  set V : NNReal := Metric.volume_comparison.C n with hV
  have hV0 : V ≠ 0 := (Metric.volume_comparison.C_pos n).ne'
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  calc 4 * CF * Cfull ^ 2 * K * ((N : NNReal) + 1) * (θ ^ 2)⁻¹ * X
      = (V * V⁻¹) * (4 * CF * Cfull ^ 2 * K * ((N : NNReal) + 1) * (θ ^ 2)⁻¹ * X) := by
        rw [mul_inv_cancel₀ hV0, one_mul]
    _ = 2 * V * CF * Cfull ^ 2 * (2 * K * ((N : NNReal) + 1) * X * ((θ ^ 2)⁻¹ * V⁻¹)) := by
        ring

/-- **The envelope arithmetic of conjunct (vi).** From a retention statement `a · S ≤ b · S'`
with `a ≠ 0` and `b` finite, and a bound `a⁻¹ · b ≤ K` on the total loss, the mass retention
`K⁻¹ · S ≤ S'` follows; if `b = 0` the hypothesis forces `S = 0`. -/
lemma inv_mul_le_of_mul_le_mul {a K : NNReal} {b S S' : ENNReal} (ha : a ≠ 0) (hb : b ≠ ⊤)
    (h : (a : ENNReal) * S ≤ b * S') (hK : (a : ENNReal)⁻¹ * b ≤ K) :
    (K : ENNReal)⁻¹ * S ≤ S' := by
  have ha' : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha
  by_cases hb0 : b = 0
  · rw [hb0, zero_mul] at h
    have hS : S = 0 := by
      rcases mul_eq_zero.mp (le_antisymm h zero_le) with h1 | h1
      · exact absurd h1 ha'
      · exact h1
    rw [hS, mul_zero]
    exact zero_le
  · have hK' : (K : ENNReal)⁻¹ ≤ ((a : ENNReal)⁻¹ * b)⁻¹ := ENNReal.inv_le_inv.mpr hK
    rw [ENNReal.mul_inv (Or.inr hb) (Or.inl (ENNReal.inv_ne_top.mpr ha')), inv_inv] at hK'
    calc (K : ENNReal)⁻¹ * S ≤ (a : ENNReal) * b⁻¹ * S := by gcongr
      _ = b⁻¹ * ((a : ENNReal) * S) := by ring
      _ ≤ b⁻¹ * (b * S') := by gcongr
      _ = S' := by rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hb, one_mul]

/-- **The pipeline's uniform retained fraction is positive when the input shade mass is.**
`ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos` asks for a non-empty productive
output, and `ShadedBody.outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos` gives
it from positive input mass; the translation by `-z` of
`Kakeya.ThinCase.thinFactorFamily` preserves the shade volumes. -/
lemma thinUniformRefinementConstant_pos [Nontrivial E] {σ ω : Type*}
    (segs : Finset σ) (Y : σ → ShadedBody E) (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E)
    (blk : σ → ω) (z : E) (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    {δ₀ w₁ : NNReal} (hδ₀ : 0 < δ₀) (hw₁ : 0 < w₁)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hmass : ∑ p ∈ segs, volume (Y p).shade ≠ 0) :
    0 < ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E) segs.card
      (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ := by
  classical
  have hne : (ShadedBody.outerThickFamilyAtScale
      (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁ hw₁).outerSet.Nonempty := by
    refine ShadedBody.outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos hδ₀ hdisc
      D w₁ hw₁ ?_
    change 0 < ∑ p ∈ segs, volume ((Y p).translate (-z)).shade
    rw [Finset.sum_congr rfl fun p _ => volume_shade_translate (Y p) (-z)]
    exact pos_iff_ne_zero.mpr hmass
  exact ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos hδ₀ hdisc D w₁ hw₁ hne

open Classical in
/-- **The data of `Kakeya.ThinCase.factoringApply`, assembled, with all thirteen conjuncts, each
at its own explicit constant.**

The five refinement steps, in the only order in which they compose:

1. `Kakeya.ThinCase.thinFactorFamily` and
   `Kakeya.ThinCase.thinFactorFamily_innerIsDiscretizedAtScale` — the family, translated so that
   the pipeline's `closedBall 0 1` is available, and its discretization at `δ₀`;
2. `ShadedBody.outerThickFamilyAtScale` through `Kakeya.ThinCase.thinSegs'` etc. — GWZ
   Proposition 5.1;
2'. `Kakeya.ThinCase.exists_fibreDensityBand` — the fibre-density band, a mass-weighted dyadic
   pigeonhole over the retained bodies (weight: the retained shade mass of the fibre), taken on
   the **original** fibres `{p ∈ segs | blk p = j}` and *before* the cell construction, where
   discarding a body is harmless. It is what conjunct (i) needs
   (`Kakeya.ThinCase.fullness_inducedShading_ge_of_globalRetention`), and it costs the factor
   `Kakeya.ThinCase.fibreDensityBandLoss` in conjunct (vi);
3. `ShadedBody.exists_constantMultiplicity_refinement` — the inner dyadic band, which
   `Kakeya.ThinCase.pointwiseMultiplicity_restrictShade` makes stable under both later
   restrictions, so it is taken once and never revisited;
4. `Kakeya.ThinCase.exists_comparableNet` at scale `w₁ / 8` — conjunct (iv) — and then
   `Kakeya.ThinCase.exists_cellOuterShading` at the inner-mass weight — conjuncts (ii), (iii)(a),
   (v).

The outer family is the **cell** shading, not the induced one: that is what conjunct (iv) forces.

Conjunct (i) is GWZ's Item 2 accounting,
`Kakeya.ThinCase.fullness_inducedShading_ge_of_globalRetention`, run on the **original** fibres
over the retained bodies `{p ∈ segs | blk p ∈ bodies'}` — so
that the Frostman hypothesis `hFr` applies verbatim — with the final shading extended by the
empty shade on every segment the pipeline or the band dropped, and with the global retention
(vi) as `θ = Kakeya.ThinCase.thinGlobalRetention`. The induced shading of that extended family
has the same shade as the induced shading of the retained fibres, and
`Kakeya.ThinCase.sum_volume_inducedShading_le_mul_sum_volume_cellShade` carries its fullness
across to the cell shading, at `Kakeya.ThinCase.thinCellFullnessConstant`. The exponent is `3 η`
because the accounting delivers `2 η` and `δ ≤ 1`, `0 ≤ η`.

The binders beyond the structural data are exactly binders of `factoringApply`: `hη`, `hCF` (as
`0 < CF`), `hdims`, `hFr`, `hdens`, `hfullness`. The carrier non-degeneracy `hVpos` that
`exists_fibreDensityBand` and the accounting need is *derived* from `hdisc` and `0 < δ₀`.

The inner family is `Y` outside the retained index set, so conjunct (c) — which quantifies over
all of `segs`, not only over `segs'` — holds on the nose.

Conjunct (v) is proved from the *defining equation* `hSheq` of the cell shades rather than from
the collar clause `hShcth`: a retained cell meets `A j` inside `closedBall c r`, and that
intersection point lies in the *retained* region, so it survives the final restriction. Using the
collar clause instead would only give the collar of the **unrestricted** block union, which is not
what the conjunct asks for. -/
theorem exists_factoringApplyData [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {σ ω : Type*} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω)
    {δ w₁ : NNReal} {δ₀ : NNReal} {η : ℝ} {CF Cfull : NNReal}
    (hδ : 0 < δ) (hδw₁ : δ ≤ w₁) (hw₁one : w₁ ≤ 1)
    (hη : (0 : ℝ) ≤ η) (hCF : 0 < CF)
    (hδ₀ : 0 < δ₀) (hδ₀w₁ : δ₀ ≤ w₁)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (z : E) (hzz : ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : ∀ j ∈ bodies,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
    (hdens : ∀ p ∈ segs,
      (δ : ENNReal) ^ η * volume (Y p).carrier ≤ (Cfull : ENNReal) * volume (Y p).shade)
    (hfullness : (δ : ENNReal) ^ η ≤
      (Cfull : ENNReal) * (ShadedBody.fullness segs Y : ENNReal)) :
    ∃ (segs' : Finset σ) (bodies' : Finset ω) (Y' : σ → ShadedBody E) (W : ω → ShadedBody E),
      segs' ⊆ segs ∧ bodies' ⊆ bodies ∧
      (∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody) ∧
      (∀ p ∈ segs', (Y' p).shade ⊆ (Y p).shade) ∧
      (∀ j ∈ bodies', Wb j ≤ (W j).toConvexSpaceBody) ∧
      (∀ j ∈ bodies', (W j).toConvexSpaceBody ≤ (Wb j).cthickening (Wb j).scale) ∧
      ((δ : ENNReal) ^ (3 * η) ≤
        (thinCellFullnessConstant (Module.finrank ℝ E) segs.card bodies.card CF Cfull w₁
            (ShadedBody.OuterInnerVolumeRatio.exponent D) : ENNReal) *
          (ShadedBody.fullness bodies' W : ENNReal)) ∧
      (∀ p ∈ segs', ∀ x ∈ (Y' p).shade, blk p ∈ bodies' ∧ x ∈ (W (blk p)).shade) ∧
      (∀ j ∈ bodies', (W j).shade ⊆
        Metric.cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
          (iUnionShade ({p ∈ segs' | blk p = j}) Y')) ∧
      ShadedBody.HasCConstantMultiplicity bodies' W 2 ∧
      (∃ μinner : NNReal, ∀ j ∈ bodies', ∀ x ∈ iUnionShade ({p ∈ segs' | blk p = j}) Y',
        (ShadedBody.pointwiseMultiplicity ({p ∈ segs' | blk p = j}) Y' x : NNReal) ≤ 2 * μinner ∧
          μinner ≤ 2 * (ShadedBody.pointwiseMultiplicity ({p ∈ segs' | blk p = j}) Y' x : NNReal))
        ∧
      (∀ x ∈ iUnionShade bodies' W, ∀ y ∈ iUnionShade bodies' W,
        volume (iUnionShade segs' Y' ∩ Metric.ball x (w₁ : ℝ)) ≤
          (equalRadiusMultConstant (Module.finrank ℝ E) : ENNReal) *
            volume (iUnionShade segs' Y' ∩ Metric.ball y (w₁ : ℝ))) ∧
      ((ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
            segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ENNReal)
          * ∑ p ∈ segs, volume (Y p).shade
        ≤ (thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
              ((w₁ : ℝ) / 8) 2 : ENNReal) *
            fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
            ∑ p ∈ segs', volume (Y' p).shade) := by
  classical
  have hw₁' : w₁ ∈ Set.Icc δ₀ 1 := ⟨hδ₀w₁, hw₁one⟩
  have hw₁pos : 0 < w₁ := thinPipeline_w₁_pos hδ₀ hw₁'
  -- the carriers are non-degenerate: `hdisc` puts every segment at scale `≥ δ₀ > 0`
  have hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0 := by
    intro p hp
    have h : (δ₀ : ENNReal) ≤ Metric.ethickness.scale ℝ (((-z) + ·) '' (Y p).carrier) :=
      hdisc.le_scale p hp
    rw [ethickness_scale_image_add_left] at h
    exact ((Y p).convex.volume_pos_of_scale_ne_zero
      (ne_bot_of_le_ne_bot (by simpa using hδ₀.ne') h)).ne'
  -- Step 2 : the pipeline output
  set s₀ : Finset σ := thinSegs' hδ₀ hdisc D hw₁' with hs₀
  set Y₁ : σ → ShadedBody E := thinY' hδ₀ hdisc D hw₁' with hY₁def
  set b₀ : Finset ω := thinBodies' hδ₀ hdisc D hw₁' with hb₀
  have hcar₁ : ∀ p : σ, (Y₁ p).toConvexSpaceBody = (Y p).toConvexSpaceBody :=
    fun p => thinY'_toConvexSpaceBody (hδ₀ := hδ₀) (hdisc := hdisc) (D := D) (hw₁ := hw₁') p
  have hs₀segs : s₀ ⊆ segs := thinSegs'_subset
  have hb₀bodies : b₀ ⊆ bodies := thinBodies'_subset
  have hparent₀ : ∀ p ∈ s₀, blk p ∈ b₀ := by
    intro p hp
    exact (thinShadingContainment (hδ₀ := hδ₀) (hdisc := hdisc) (D := D) (hw₁ := hw₁') hp).1
  -- every retained body has a retained segment, hence a non-empty original fibre
  have hne₀ : ∀ j ∈ b₀, ({p ∈ segs | blk p = j}).Nonempty := by
    intro j hj
    have h := ShadedBody.outerThickFamilyAtScale_fiber_volume_ne_zero
      (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁ hw₁pos hj
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply h
    have hfib : (thinPipeline hδ₀ hdisc D hw₁').fiber j = ∅ := by
      rw [thinPipeline_fiber]
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      obtain ⟨hps, hpj⟩ := Finset.mem_filter.mp hp
      have : p ∈ ({p ∈ segs | blk p = j}) := Finset.mem_filter.mpr ⟨hs₀segs hps, hpj⟩
      rw [hemp] at this
      exact Finset.notMem_empty p this
    change volume (iUnionShade ((thinPipeline hδ₀ hdisc D hw₁').fiber j)
      (thinPipeline hδ₀ hdisc D hw₁').innerBody) = 0
    rw [hfib]
    simp [iUnionShade]
  -- Step 2' : the fibre-density band on the retained bodies, weighted by the retained fibre
  -- shade mass. It runs *before* the cell construction, where discarding bodies is harmless,
  -- and it is what conjunct (i) needs
  -- (`Kakeya.ThinCase.fullness_inducedShading_ge_of_globalRetention`).
  obtain ⟨b₁, hb₁b₀, hpair, -, hbandmass⟩ :=
    exists_fibreDensityBand segs Y b₀ Wb blk hCF hle (fun j hj => hFr j (hb₀bodies hj)) hVpos
      hne₀ (fun j => ∑ p ∈ {p ∈ s₀ | blk p = j}, volume (Y₁ p).shade)
  set s₁ : Finset σ := {p ∈ s₀ | blk p ∈ b₁} with hs₁
  have hs₁s₀ : s₁ ⊆ s₀ := Finset.filter_subset _ _
  have hs₁segs : s₁ ⊆ segs := hs₁s₀.trans hs₀segs
  have hb₁bodies : b₁ ⊆ bodies := hb₁b₀.trans hb₀bodies
  have hparent : ∀ p ∈ s₁, blk p ∈ b₁ := fun p hp => (Finset.mem_filter.mp hp).2
  have hfib₁ : ∀ j ∈ b₁, ({p ∈ s₁ | blk p = j}) = ({p ∈ s₀ | blk p = j}) := by
    intro j hj
    ext p
    simp only [hs₁, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hps, -⟩, hpj⟩; exact ⟨hps, hpj⟩
    · rintro ⟨hps, hpj⟩; exact ⟨⟨hps, hpj ▸ hj⟩, hpj⟩
  -- the band's mass bound, read on the segments
  have hbandsegs : ∑ p ∈ s₀, volume (Y₁ p).shade ≤
      fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
        ∑ p ∈ s₁, volume (Y₁ p).shade := by
    rw [← Finset.sum_fiberwise_of_maps_to hparent₀ (fun p => volume (Y₁ p).shade),
      ← Finset.sum_fiberwise_of_maps_to hparent (fun p => volume (Y₁ p).shade)]
    refine hbandmass.trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun j hj => ?_))
    rw [hfib₁ j hj]
  -- Step 3 : the inner dyadic band; stable under every later common restriction
  obtain ⟨Y₂, Xb, hXbmeas, hXbeq, href₂, hmult₂, hmass₂⟩ :=
    ShadedBody.exists_constantMultiplicity_refinement_band s₁ Y₁
  -- the shaded union of the banded family, and where it lives
  have hUmeas : MeasurableSet (iUnionShade s₁ Y₂) :=
    Finset.measurableSet_biUnion _ fun i _ => (Y₂ i).measurableSet_shade
  have hUsub : iUnionShade s₁ Y₂ ⊆ Metric.ball z 2 := by
    refine Set.iUnion₂_subset fun p hp => ?_
    have h1 : (Y₂ p).shade ⊆ (Y₁ p).shade := (href₂.2 p hp).2
    have h2 : (Y₁ p).shade ⊆ (Y₁ p).carrier := (Y₁ p).shade_subset
    have h3 : (Y₁ p).carrier = (Y p).carrier := congrArg ConvexSpaceBody.carrier (hcar₁ p)
    have h4 : (Y p).carrier ⊆ (Wb (blk p)).carrier := hle p (hs₁segs hp)
    have h5 : (Wb (blk p)).carrier ⊆ Metric.closedBall z 1 :=
      hzz (blk p) (hblk p (hs₁segs hp))
    intro x hx
    have : x ∈ Metric.closedBall z 1 := h5 (h4 (h3 ▸ h2 (h1 hx)))
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]
    linarith
  -- Step 4 : the finer ball net at scale `w₁ / 8`
  have hr : (0 : NNReal) < w₁ / 8 := by
    have : (0 : NNReal) < w₁ := lt_of_lt_of_le hδ hδw₁
    positivity
  obtain ⟨T', hT'U, hT'sep, hT'comp, hT'mass⟩ :=
    exists_comparableNet hUmeas hr (by norm_num : (0:ℝ) ≤ 2) hUsub
  -- Step 5 : restrict every shade to the retained net region
  set rr : ℝ := ((w₁ / 8 : NNReal) : ℝ) with hrr
  set S' : Set E := ⋃ c ∈ T', Metric.closedBall c rr with hS'
  have hS'meas : MeasurableSet S' :=
    Finset.measurableSet_biUnion _ fun c _ => measurableSet_closedBall
  set Y₃ : σ → ShadedBody E := fun p => (Y₂ p).restrictShade S' hS'meas with hY₃
  -- Step 6 : the block unions of the restricted family, and the cell weight
  set A : ω → Set E := fun j => iUnionShade ({p ∈ s₁ | blk p = j}) Y₃ with hA
  set f : E → ENNReal :=
    fun c => ∑ p ∈ s₁, volume ((Y₃ p).shade ∩ Metric.closedBall c rr) with hf
  have hshA : ∀ p ∈ s₁, (Y₃ p).shade ⊆ A (blk p) := by
    intro p hp x hx
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hp, rfl⟩) hx
  have hf0 : ∀ c ∈ T', cellBlockCount b₁ A rr c = 0 → f c = 0 := by
    intro c _ hc0
    refine Finset.sum_eq_zero fun p hp => ?_
    have hempty : A (blk p) ∩ Metric.closedBall c rr = ∅ := by
      by_contra hne
      have hne' : (A (blk p) ∩ Metric.closedBall c rr).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hne
      have : blk p ∈ {j ∈ b₁ | (A j ∩ Metric.closedBall c rr).Nonempty} :=
        Finset.mem_filter.mpr ⟨hparent p hp, hne'⟩
      rw [cellBlockCount] at hc0
      exact absurd (Finset.card_ne_zero.mpr ⟨blk p, this⟩) (by simpa using hc0)
    have : (Y₃ p).shade ∩ Metric.closedBall c rr = ∅ := by
      rw [← Set.subset_empty_iff, ← hempty]
      exact Set.inter_subset_inter_left _ (hshA p hp)
    rw [this]
    simp
  -- Step 7 : the cell pigeonhole
  obtain ⟨T'', P, m, Sh, hT''T', hfmass, hPsub, hPmeas, hPdisj, hPunion, hband, hSheq,
      hShmeas, hShcth, hShsub, hShnet, hShmult⟩ :=
    exists_cellOuterShading b₁ A T' rr f hf0
  -- Step 8 : the final inner family
  set reg : Set E := ⋃ c ∈ T'', Metric.closedBall c rr with hreg
  have hregmeas : MeasurableSet reg :=
    Finset.measurableSet_biUnion _ fun c _ => measurableSet_closedBall
  set Y' : σ → ShadedBody E :=
    fun p => if p ∈ s₁ then (Y₃ p).restrictShade reg hregmeas else Y p with hY'
  -- the single common set every retained shade was cut down to, across all three restrictions:
  -- the inner dyadic band, the ball net, and the retained cells.  Conjunct (iii)(b) is exactly
  -- the statement that `Kakeya.ThinCase.thinInnerConstMult` survives this cut, and it does
  -- because the cut is by one set, the same for every index.
  set Sfin : Set E := Xb ∩ S' ∩ reg with hSfin
  have hY'shade : ∀ p ∈ s₁, (Y' p).shade = (Y₁ p).shade ∩ Sfin := by
    intro p hp
    simp only [hY', if_pos hp, ShadedBody.shade_restrictShade, hY₃, hSfin, hXbeq p]
    ext w; constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩
    · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  -- Step 9 : the final outer family
  have hscale_ge : ∀ j ∈ bodies, 2 * rr ≤ (Wb j).scale := by
    intro j hj
    have h := (hw₁ j hj).2
    have : (Wb j).scale = Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) := rfl
    rw [this, hrr]
    have hw0 : (0:ℝ) ≤ (w₁ : ℝ) := w₁.coe_nonneg
    push_cast
    linarith
  have hAsub : ∀ j ∈ b₁, A j ⊆ (Wb j).carrier := by
    intro j hj x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hps, hpj⟩ := Finset.mem_filter.mp hp
    have h1 : (Y₃ p).shade ⊆ (Y p).carrier := by
      intro w hw
      have h2 : w ∈ (Y₂ p).shade := hw.1
      have h3 : w ∈ (Y₁ p).shade := (href₂.2 p hps).2 h2
      have h4 : (Y₁ p).carrier = (Y p).carrier := congrArg ConvexSpaceBody.carrier (hcar₁ p)
      exact h4 ▸ (Y₁ p).shade_subset h3
    have := h1 hxp
    rw [← hpj]
    exact hle p (hs₁segs hps) this
  have hShcarr : ∀ j ∈ b₁, Sh j ⊆ ((Wb j).cthickening (Wb j).scale).carrier := by
    intro j hj
    refine (hShcth j hj).trans ?_
    show Metric.cthickening (2 * rr) (A j) ⊆ Metric.cthickening (Wb j).scale (Wb j).carrier
    refine (Metric.cthickening_mono ?_ (A j)).trans
      (Metric.cthickening_subset_of_subset _ (hAsub j hj))
    exact hscale_ge j (hb₁bodies hj)
  set W : ω → ShadedBody E := fun j =>
    { toConvexSpaceBody := (Wb j).cthickening (Wb j).scale
      shade := if hj : j ∈ b₁ then Sh j else ∅
      measurableSet_shade := by
        by_cases hj : j ∈ b₁ <;> simp [hj, hShmeas j]
      shade_subset := by
        by_cases hj : j ∈ b₁ <;> simp [hj]
        exact hShcarr j hj } with hW
  -- the collar of the *retained* block union, at the cell radius; both (v) and (iv) use it
  have hrr0 : (0:ℝ) ≤ rr := by rw [hrr]; positivity
  have hcollar : ∀ j ∈ b₁, Sh j ⊆
      Metric.cthickening (2 * rr) (iUnionShade ({p ∈ s₁ | blk p = j}) Y') := by
    intro j hj
    rw [hSheq j]
    refine Set.iUnion₂_subset fun c hc => ?_
    obtain ⟨hcT, hne⟩ := Finset.mem_filter.mp hc
    obtain ⟨a, haA, hac⟩ := hne
    have hareg : a ∈ reg := Set.mem_biUnion hcT hac
    have haY' : a ∈ iUnionShade ({p ∈ s₁ | blk p = j}) Y' := by
      obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.mp haA
      refine Set.mem_biUnion hp ?_
      simp only [hY', if_pos (Finset.mem_filter.mp hp).1]
      exact ⟨hap, hareg⟩
    intro x hx
    have hxc : dist x c ≤ rr := by simpa [Metric.mem_closedBall] using hPsub c hcT hx
    have hac' : dist a c ≤ rr := by simpa [Metric.mem_closedBall] using hac
    refine Metric.mem_cthickening_of_dist_le x a _ _ haY' ?_
    calc dist x a ≤ dist x c + dist c a := dist_triangle x c a
      _ ≤ rr + rr := by rw [dist_comm c a]; linarith
      _ = 2 * rr := by ring
  have hT''sep : Metric.IsSeparated ((w₁ / 8 : NNReal) : ENNReal) ((T'' : Set E)) :=
    hT'sep.subset (by exact_mod_cast hT''T')
  -- **The free shrink.**  A body whose block kept no cell mass has an empty outer shade, and
  -- every segment of its block has an empty final inner shade, so dropping it moves no count, no
  -- union and no sum.  It is what conjunct (i) needs (`hZne` of
  -- `Kakeya.ThinCase.sum_volume_inducedShading_le_mul_sum_volume_cellShade`).
  set b₂ : Finset ω := {j ∈ b₁ | (A j ∩ reg).Nonempty} with hb₂
  set s₂ : Finset σ := {p ∈ s₁ | blk p ∈ b₂} with hs₂
  have hb₂sub : b₂ ⊆ b₁ := Finset.filter_subset _ _
  have hs₂sub : s₂ ⊆ s₁ := Finset.filter_subset _ _
  have hballreg' : ∀ c ∈ T'', Metric.closedBall c rr ⊆ reg := fun c hc w hw =>
    Set.mem_biUnion hc hw
  -- a dropped body has an empty outer shade
  have hShempty : ∀ j, ¬ (A j ∩ reg).Nonempty → Sh j = ∅ := by
    intro j hj
    rw [hSheq j]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨c, hc, -⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hcT, hne⟩ := Finset.mem_filter.mp hc
    obtain ⟨a, haA, hac⟩ := hne
    exact hj ⟨a, haA, hballreg' c hcT hac⟩
  -- a segment of a dropped body has an empty final inner shade
  have hY'empty : ∀ p ∈ s₁, blk p ∉ b₂ → (Y' p).shade = ∅ := by
    intro p hp hpb
    have hnotne : ¬ (A (blk p) ∩ reg).Nonempty := by
      intro hne
      exact hpb (Finset.mem_filter.mpr ⟨hparent p hp, hne⟩)
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    simp only [hY', if_pos hp, ShadedBody.shade_restrictShade] at hx
    exact hnotne ⟨x, hshA p hp hx.1, hx.2⟩
  -- the four transfers
  have hWfil : ∀ x : E, ({j ∈ b₂ | x ∈ (W j).shade}) = ({j ∈ b₁ | x ∈ (W j).shade}) := by
    intro x
    apply Finset.Subset.antisymm
    · exact Finset.filter_subset_filter _ hb₂sub
    · intro j hj
      obtain ⟨hjb, hxj⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hjb, ?_⟩, hxj⟩
      by_contra hne
      have : (W j).shade = ∅ := by
        show (if _ : j ∈ b₁ then Sh j else ∅) = ∅
        rw [dif_pos hjb]; exact hShempty j hne
      rw [this] at hxj; exact hxj
  have hUW : (⋃ j ∈ b₂, (W j).shade) = ⋃ j ∈ b₁, (W j).shade := by
    show iUnionShade b₂ W = iUnionShade b₁ W
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun j hj => fun x hx =>
      Set.mem_biUnion (hb₂sub hj) hx) ?_
    refine Set.iUnion₂_subset fun j hj => fun x hx => ?_
    have hmem : j ∈ ({j ∈ b₂ | x ∈ (W j).shade}) := by
      rw [hWfil x]; exact Finset.mem_filter.mpr ⟨hj, hx⟩
    exact Set.mem_biUnion (Finset.mem_filter.mp hmem).1 hx
  -- the same fact in the folded shape the conjunct statements use
  have hUWf : iUnionShade b₂ W = iUnionShade b₁ W := hUW
  have hUY : iUnionShade s₂ Y' = iUnionShade s₁ Y' := by
    show iUnionShade s₂ Y' = iUnionShade s₁ Y'
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun p hp => fun x hx =>
      Set.mem_biUnion (hs₂sub hp) hx) ?_
    refine Set.iUnion₂_subset fun p hp => fun x hx => ?_
    by_cases hpb : blk p ∈ b₂
    · exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpb⟩) hx
    · rw [hY'empty p hp hpb] at hx; exact absurd hx (Set.notMem_empty x)
  have hsum : ∑ p ∈ s₂, volume (Y' p).shade = ∑ p ∈ s₁, volume (Y' p).shade := by
    refine Finset.sum_subset hs₂sub ?_
    intro p hp hpn
    have hpb : blk p ∉ b₂ := by
      intro hpb; exact hpn (Finset.mem_filter.mpr ⟨hp, hpb⟩)
    rw [hY'empty p hp hpb]
    simp
  have hblkfil : ∀ j ∈ b₂, ({p ∈ s₂ | blk p = j}) = ({p ∈ s₁ | blk p = j}) := by
    intro j hj
    ext p
    simp only [hs₂, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hps, -⟩, hpj⟩; exact ⟨hps, hpj⟩
    · rintro ⟨hps, hpj⟩; exact ⟨⟨hps, hpj ▸ hj⟩, hpj⟩
  -- (c) the carriers are unchanged
  have hcarY' : ∀ p, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody := by
    intro p
    by_cases hp : p ∈ s₁
    · simp only [hY', if_pos hp]
      rw [ShadedBody.toConvexSpaceBody_restrictShade]
      simp only [hY₃]
      rw [ShadedBody.toConvexSpaceBody_restrictShade, (href₂.2 p hp).1, hcar₁ p]
    · simp [hY', hp]
  -- (vi) the retained mass, through all five pigeonholes at once
  have hvi : (ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
          segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ENNReal)
        * ∑ p ∈ segs, volume (Y p).shade
      ≤ (thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
            ((w₁ : ℝ) / 8) 2 : ENNReal) *
          fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
          ∑ p ∈ s₂, volume (Y' p).shade := by
    rw [hsum]
    -- Step A : the pipeline's own retention, stated by `thinRefinement_mass`
    have hA : (ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
            segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ENNReal) *
          ∑ p ∈ segs, volume (Y p).shade
        ≤ ∑ p ∈ s₀, volume (Y₁ p).shade :=
      thinRefinement_mass (hδ₀ := hδ₀) (hdisc := hdisc) (D := D) (hw₁ := hw₁')
    -- Step B : the inner dyadic band
    have hB : ∑ p ∈ s₁, volume (Y₁ p).shade
        ≤ ((Nat.log 2 segs.card + 1 : ℕ) : ENNReal) * ∑ p ∈ s₁, volume (Y₂ p).shade := by
      refine le_trans hmass₂ ?_
      rw [nsmul_eq_mul]
      gcongr
    -- Step C : the ball net.  The net pigeonhole bounds the Lebesgue measure of the shaded
    -- *union*; the conjunct is about the *sum* of the shade volumes.  The band is what converts
    -- between them, at the cost of a factor `2` in each direction.
    obtain ⟨Mv, hMv⟩ := (ShadedBody.hasCConstantMultiplicity_iff_exists_hasCConstantMultiplicityWith
      s₁ Y₂ 2).mp hmult₂
    have hupper : ∑ p ∈ s₁, volume (Y₂ p).shade
        ≤ 2 * (Mv : ENNReal) * volume (iUnionShade s₁ Y₂) := by
      rw [ShadedBody.sum_volume_shade_eq_lintegral_pointwiseMultiplicity]
      calc ∫⁻ x, (ShadedBody.pointwiseMultiplicity s₁ Y₂ x : ENNReal)
          ≤ ∫⁻ x, (iUnionShade s₁ Y₂).indicator (fun _ => (2 * (Mv : ENNReal))) x := by
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ iUnionShade s₁ Y₂
            · rw [Set.indicator_apply, if_pos hx]
              rcases hMv x with h0 | ⟨-, h2⟩
              · exact absurd ((ShadedBody.pointwiseMultiplicity_pos_iff s₁ Y₂ x).2
                  (by obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx; exact ⟨i, hi, hxi⟩))
                  (by simp only [not_lt, Nat.le_zero]; exact_mod_cast h0)
              · have h3 : ((ShadedBody.pointwiseMultiplicity s₁ Y₂ x : ℕ) : NNReal) ≤ 2 * Mv := h2
                have := ENNReal.coe_le_coe.mpr h3
                push_cast at this ⊢
                exact this
            · rw [Set.indicator_apply, if_neg hx]
              have : ShadedBody.pointwiseMultiplicity s₁ Y₂ x = 0 := by
                by_contra hne
                exact hx (by
                  obtain ⟨i, hi, hxi⟩ := (ShadedBody.pointwiseMultiplicity_pos_iff s₁ Y₂ x).1
                    (Nat.pos_of_ne_zero hne)
                  exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
              simp [this]
        _ = 2 * (Mv : ENNReal) * volume (iUnionShade s₁ Y₂) :=
            lintegral_indicator_const hUmeas _
    have hmu₃ : ∀ x ∈ S', ShadedBody.pointwiseMultiplicity s₁ Y₃ x
        = ShadedBody.pointwiseMultiplicity s₁ Y₂ x :=
      fun x hx => pointwiseMultiplicity_restrictShade s₁ Y₂ S' hS'meas hx
    have hlower : (Mv : ENNReal) * volume (iUnionShade s₁ Y₂ ∩ S')
        ≤ 2 * ∑ p ∈ s₁, volume (Y₃ p).shade := by
      refine ShadedBody.mul_volume_le_mul_sum_volume_shade_of_le_mul_pointwiseMultiplicity
        s₁ Y₃ (hUmeas.inter hS'meas) ?_
      rintro x ⟨hxU, hxS⟩
      rw [hmu₃ x hxS]
      rcases hMv x with h0 | ⟨h1, -⟩
      · exact absurd ((ShadedBody.pointwiseMultiplicity_pos_iff s₁ Y₂ x).2
          (by obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxU; exact ⟨i, hi, hxi⟩))
          (by simp only [not_lt, Nat.le_zero]; exact_mod_cast h0)
      · calc (Mv : ENNReal) ≤ ((ShadedBody.pointwiseMultiplicity s₁ Y₂ x : ℕ) : ENNReal) := by
              exact_mod_cast ENNReal.coe_le_coe.mpr h1
          _ ≤ 2 * ((ShadedBody.pointwiseMultiplicity s₁ Y₂ x : ℕ) : ENNReal) := by
              nth_rewrite 1 [← one_mul (((ShadedBody.pointwiseMultiplicity s₁ Y₂ x : ℕ) : ENNReal))]
              gcongr <;> norm_num
    have hC : ∑ p ∈ s₁, volume (Y₂ p).shade
        ≤ 4 * (ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal)
            * ∑ p ∈ s₁, volume (Y₃ p).shade := by
      calc ∑ p ∈ s₁, volume (Y₂ p).shade
          ≤ 2 * (Mv : ENNReal) * volume (iUnionShade s₁ Y₂) := hupper
        _ ≤ 2 * (Mv : ENNReal) *
              ((ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal) *
                volume (iUnionShade s₁ Y₂ ∩ S')) := by gcongr
        _ = 2 * (ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal) *
              ((Mv : ENNReal) * volume (iUnionShade s₁ Y₂ ∩ S')) := by ring
        _ ≤ 2 * (ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal) *
              (2 * ∑ p ∈ s₁, volume (Y₃ p).shade) := by gcongr
        _ = 4 * (ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal)
              * ∑ p ∈ s₁, volume (Y₃ p).shade := by ring
    -- Step D : the cell pigeonhole, and the overlap of the net's own balls
    have hD1 : ∑ p ∈ s₁, volume (Y₃ p).shade ≤ ∑ c ∈ T', f c := by
      rw [hf, Finset.sum_comm]
      refine Finset.sum_le_sum fun p _ => ?_
      have hcov : (Y₃ p).shade ⊆ ⋃ c ∈ T', Metric.closedBall c rr := fun x hx => hx.2
      calc volume (Y₃ p).shade
          = volume (⋃ c ∈ T', ((Y₃ p).shade ∩ Metric.closedBall c rr)) := by
            congr 1
            rw [← Set.inter_iUnion₂]
            exact (Set.inter_eq_left.mpr hcov).symm
        _ ≤ ∑ c ∈ T', volume ((Y₃ p).shade ∩ Metric.closedBall c rr) :=
            measure_biUnion_finset_le _ _
    have hD2 : ∑ c ∈ T', f c ≤ ((Nat.log 2 bodies.card + 1 : ℕ) : ENNReal) * ∑ c ∈ T'', f c := by
      refine le_trans hfmass ?_
      gcongr
    have hD3 : ∑ c ∈ T'', f c
        ≤ (5 : ENNReal) ^ (Module.finrank ℝ E) * ∑ p ∈ s₁, volume (Y' p).shade := by
      rw [hf, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hsep := sum_volume_inter_closedBall_le_of_isSeparated (E := E) hr hT''sep
        (A := (Y₃ p).shade) (Y₃ p).measurableSet_shade
      rw [← hrr] at hsep
      refine le_trans hsep ?_
      have : (Y₃ p).shade ∩ (⋃ c ∈ T'', Metric.closedBall c rr) = (Y' p).shade := by
        simp only [hY', if_pos hp, ShadedBody.shade_restrictShade, hreg]
      rw [this]
    -- the five steps, composed
    calc (ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
            segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ENNReal)
          * ∑ p ∈ segs, volume (Y p).shade
        ≤ ∑ p ∈ s₀, volume (Y₁ p).shade := hA
      _ ≤ fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
            ∑ p ∈ s₁, volume (Y₁ p).shade := hbandsegs
      _ ≤ fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
            (((Nat.log 2 segs.card + 1 : ℕ) : ENNReal) * ∑ p ∈ s₁, volume (Y₂ p).shade) := by
            gcongr
      _ ≤ fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
            (((Nat.log 2 segs.card + 1 : ℕ) : ENNReal) *
              (4 * (ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal)
                * ∑ p ∈ s₁, volume (Y₃ p).shade)) := by gcongr
      _ ≤ fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
            (((Nat.log 2 segs.card + 1 : ℕ) : ENNReal) *
              (4 * (ballNetLoss (Module.finrank ℝ E) rr 2 : ENNReal)
                * (((Nat.log 2 bodies.card + 1 : ℕ) : ENNReal) *
                    ((5 : ENNReal) ^ (Module.finrank ℝ E)
                      * ∑ p ∈ s₁, volume (Y' p).shade)))) := by
            gcongr
            exact hD1.trans (hD2.trans (by gcongr))
      _ = (thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
              ((w₁ : ℝ) / 8) 2 : ENNReal) *
            fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
            ∑ p ∈ s₁, volume (Y' p).shade := by
            rw [thinRetentionLoss, hrr]
            push_cast
            ring
  -- (i) the fullness of the cell shading. GWZ's Item 2 accounting on the *original* fibres
  -- over the retained bodies, with the final shading extended by the empty shade on the dropped
  -- segments, then the bridge from the induced shading to the cell shading.
  have hi : (δ : ENNReal) ^ (3 * η) ≤
      (thinCellFullnessConstant (Module.finrank ℝ E) segs.card bodies.card CF Cfull w₁
          (ShadedBody.OuterInnerVolumeRatio.exponent D) : ENNReal) *
        (ShadedBody.fullness b₂ W : ENNReal) := by
    -- the input shade mass is positive, hence so is the pipeline's retained fraction
    have hδη : (0 : ENNReal) < (δ : ENNReal) ^ η :=
      ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ) ENNReal.coe_ne_top
    have hmass : ∑ p ∈ segs, volume (Y p).shade ≠ 0 := by
      intro h0
      have hf : (ShadedBody.fullness segs Y : ENNReal) = 0 := by
        rw [ShadedBody.fullness_def, h0, ENNReal.zero_div]
      rw [hf, mul_zero] at hfullness
      exact hδη.ne' (le_antisymm hfullness zero_le)
    have hCfull : 0 < Cfull := by
      rcases (zero_le : (0 : NNReal) ≤ Cfull).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, ENNReal.coe_zero, zero_mul] at hfullness
        exact hδη.ne' (le_antisymm hfullness zero_le)
    have hb₀ne : b₀.Nonempty := by
      refine ShadedBody.outerThickFamilyAtScale_outerSet_nonempty_of_sum_volume_shade_pos hδ₀
        hdisc D w₁ hw₁pos ?_
      change 0 < ∑ p ∈ segs, volume ((Y p).translate (-z)).shade
      rw [Finset.sum_congr rfl fun p _ => volume_shade_translate (Y p) (-z)]
      exact pos_iff_ne_zero.mpr hmass
    have hcpos : 0 < ShadedBody.factoringCoreAtScaleUniformRefinementConstant
        (Module.finrank ℝ E) segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ :=
      ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos hδ₀ hdisc D w₁ hw₁pos hb₀ne
    -- the total loss is finite and non-zero, by (vi) against the positive input mass
    have hBtop : fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hLB : (thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
        ((w₁ : ℝ) / 8) 2 : ENNReal) * fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card
          ≠ 0 := by
      intro h0
      have h := hvi
      rw [h0, zero_mul] at h
      rcases mul_eq_zero.mp (le_antisymm h zero_le) with h1 | h1
      · exact (ENNReal.coe_pos.mpr hcpos).ne' h1
      · exact hmass h1
    have hLBtop : (thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
        ((w₁ : ℝ) / 8) 2 : ENNReal) * fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card
          ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hBtop
    have hLB' : thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card ((w₁ : ℝ) / 8) 2 *
        (fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card).toNNReal ≠ 0 := by
      intro h0
      apply hLB
      rw [← ENNReal.coe_toNNReal hBtop, ← ENNReal.coe_mul, h0, ENNReal.coe_zero]
    -- the global retention, in `ℝ≥0`
    set θ : NNReal := thinGlobalRetention (Module.finrank ℝ E) segs.card bodies.card CF w₁
      (ShadedBody.OuterInnerVolumeRatio.exponent D) with hθ
    have hθpos : 0 < θ := by
      rw [hθ, thinGlobalRetention]
      exact mul_pos hcpos (inv_pos.mpr (pos_iff_ne_zero.mpr hLB'))
    have hθcoe : (θ : ENNReal) =
        (ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
            segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ENNReal) *
          ((thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
              ((w₁ : ℝ) / 8) 2 : ENNReal) *
            fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card)⁻¹ := by
      rw [hθ, thinGlobalRetention, ENNReal.coe_mul, ENNReal.coe_inv hLB', ENNReal.coe_mul,
        ENNReal.coe_toNNReal hBtop]
    -- the retained bodies are non-empty, by (vi) again
    have hb₂ne : b₂.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hs₂emp : s₂ = ∅ := by
        rw [hs₂, Finset.filter_eq_empty_iff]
        intro p _ hpb
        rw [hemp] at hpb
        exact Finset.notMem_empty _ hpb
      have h := hvi
      rw [hs₂emp, Finset.sum_empty, mul_zero] at h
      rcases mul_eq_zero.mp (le_antisymm h zero_le) with h1 | h1
      · exact (ENNReal.coe_pos.mpr hcpos).ne' h1
      · exact hmass h1
    -- the original fibres over the retained bodies, and the final shading extended by the
    -- empty shade on the segments the pipeline or the band dropped
    set segs₂ : Finset σ := {p ∈ segs | blk p ∈ b₂} with hsegs₂
    set Y'' : σ → ShadedBody E :=
      fun p => if p ∈ s₁ then Y' p else (Y p).restrictShade ∅ MeasurableSet.empty with hY''
    have hs₂segs₂ : s₂ ⊆ segs₂ := by
      intro p hp
      obtain ⟨hps, hpb⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hs₁segs hps, hpb⟩
    have hY''eq : ∀ p ∈ s₁, Y'' p = Y' p := fun p hp => by simp only [hY'', if_pos hp]
    have hY''empty : ∀ p, p ∉ s₁ → (Y'' p).shade = ∅ := fun p hp => by
      simp only [hY'', if_neg hp, ShadedBody.shade_restrictShade, Set.inter_empty]
    have hY''car : ∀ p, (Y'' p).toConvexSpaceBody = (Y p).toConvexSpaceBody := by
      intro p
      by_cases hp : p ∈ s₁
      · rw [hY''eq p hp]; exact hcarY' p
      · simp only [hY'', if_neg hp, ShadedBody.toConvexSpaceBody_restrictShade]
    have hfib₂ : ∀ j ∈ b₂, ({p ∈ segs₂ | blk p = j}) = ({p ∈ segs | blk p = j}) := by
      intro j hj
      ext p
      simp only [hsegs₂, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hps, -⟩, hpj⟩; exact ⟨hps, hpj⟩
      · rintro ⟨hps, hpj⟩; exact ⟨⟨hps, hpj ▸ hj⟩, hpj⟩
    -- the shaded union of an original fibre under `Y''` is that of the retained fibre under `Y'`
    have hU₂ : ∀ j ∈ b₂, iUnionShade ({p ∈ segs₂ | blk p = j}) Y''
        = iUnionShade ({p ∈ s₁ | blk p = j}) Y' := by
      intro j hj
      ext x
      constructor
      · intro hx
        obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
        by_cases hps₁ : p ∈ s₁
        · rw [hY''eq p hps₁] at hxp
          exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨hps₁, (Finset.mem_filter.mp hp).2⟩) hxp
        · rw [hY''empty p hps₁] at hxp
          exact absurd hxp (Set.notMem_empty x)
      · intro hx
        obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨hps₁, hpj⟩ := Finset.mem_filter.mp hp
        refine Set.mem_biUnion (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨hs₁segs hps₁, hpj ▸ hj⟩, hpj⟩) ?_
        rw [hY''eq p hps₁]
        exact hxp
    -- the hypotheses of the Item 2 accounting over `(segs₂, b₂)`
    have hne₂ : ∀ j ∈ b₂, ({p ∈ segs₂ | blk p = j}).Nonempty := by
      intro j hj
      obtain ⟨-, x, hxA, -⟩ := Finset.mem_filter.mp hj
      obtain ⟨p, hp, -⟩ := Set.mem_iUnion₂.mp hxA
      obtain ⟨hps₁, hpj⟩ := Finset.mem_filter.mp hp
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hs₁segs hps₁, hpj ▸ hj⟩, hpj⟩⟩
    have hb₂bodies : b₂ ⊆ bodies := hb₂sub.trans hb₁bodies
    have hecc₂ : ∀ j ∈ b₂, ∀ p ∈ ({p ∈ segs₂ | blk p = j}),
        volume (Wb j).carrier ≤
          2 ^ (ShadedBody.OuterInnerVolumeRatio.exponent D) * volume (Y p).carrier := by
      intro j hj p hp
      rw [hfib₂ j hj] at hp
      have h := D.volume_outer_le j (hb₂bodies hj) p (by rw [thinFactorFamily_fiber]; exact hp)
      have h' : volume ((Wb j).translate (-z)).carrier ≤
          2 ^ (ShadedBody.OuterInnerVolumeRatio.exponent D) *
            volume (((Y p).translate (-z)).toConvexSpaceBody).carrier := h
      rw [toConvexSpaceBody_translate, Kakeya.volume_translate, Kakeya.volume_translate] at h'
      exact h'
    have hret : (θ : ENNReal) * ∑ p ∈ segs₂, volume (Y p).shade ≤
        ∑ p ∈ segs₂, volume (Y'' p).shade := by
      have h1 : ∑ p ∈ segs₂, volume (Y'' p).shade = ∑ p ∈ s₂, volume (Y' p).shade := by
        rw [← Finset.sum_subset hs₂segs₂ (fun p hp hpn => ?_)]
        · exact Finset.sum_congr rfl fun p hp => by rw [hY''eq p (hs₂sub hp)]
        · have hps₁ : p ∉ s₁ := fun h =>
            hpn (Finset.mem_filter.mpr ⟨h, (Finset.mem_filter.mp hp).2⟩)
          rw [hY''empty p hps₁, measure_empty]
      have h2 : ∑ p ∈ segs₂, volume (Y p).shade ≤ ∑ p ∈ segs, volume (Y p).shade :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      rw [h1]
      calc (θ : ENNReal) * ∑ p ∈ segs₂, volume (Y p).shade
          ≤ (θ : ENNReal) * ∑ p ∈ segs, volume (Y p).shade := by gcongr
        _ = ((thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
                ((w₁ : ℝ) / 8) 2 : ENNReal) *
              fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card)⁻¹ *
              ((ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
                  segs.card (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : ENNReal) *
                ∑ p ∈ segs, volume (Y p).shade) := by
            rw [hθcoe]; ring
        _ ≤ ((thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
                ((w₁ : ℝ) / 8) 2 : ENNReal) *
              fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card)⁻¹ *
              ((thinRetentionLoss (Module.finrank ℝ E) segs.card bodies.card
                  ((w₁ : ℝ) / 8) 2 : ENNReal) *
                fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card *
                ∑ p ∈ s₂, volume (Y' p).shade) := by gcongr
        _ = ∑ p ∈ s₂, volume (Y' p).shade := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hLB hLBtop, one_mul]
    have hρ₂ : ∀ j ∈ b₂, ∀ k ∈ b₂,
        (∑ p ∈ {p ∈ segs₂ | blk p = j}, volume (Y p).carrier) *
            volume ((Wb k).cthickening (Wb k).scale).carrier ≤
          2 * ((∑ p ∈ {p ∈ segs₂ | blk p = k}, volume (Y p).carrier) *
            volume ((Wb j).cthickening (Wb j).scale).carrier) := by
      intro j hj k hk
      rw [hfib₂ j hj, hfib₂ k hk]
      exact hpair j (hb₂sub hj) k (hb₂sub hk)
    -- GWZ's Item 2, at the exponent `2 η`, for the induced shading of the extended family
    set Wind : ω → ShadedBody E :=
      fun j => ShadedBody.inducedShading ({p ∈ segs₂ | blk p = j}) Y'' (Wb j) with hWind
    have hT3 : (δ : ENNReal) ^ (2 * η) ≤
        (thinFibreDensityConstant CF Cfull θ (ShadedBody.OuterInnerVolumeRatio.exponent D) :
          ENNReal) * (ShadedBody.fullness b₂ Wind : ENNReal) :=
      fullness_inducedShading_ge_of_globalRetention hdim segs₂ Y Y'' b₂ Wb blk hδ hθpos hCF
        hCfull hb₂ne (fun p _ => hY''car p) (fun p hp => (Finset.mem_filter.mp hp).2)
        (fun p hp => hle p (Finset.mem_filter.mp hp).1)
        (fun p hp q hq => hdims p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1)
        (fun j hj => by rw [hfib₂ j hj]; exact hFr j (hb₂bodies hj))
        (fun p hp => hdens p (Finset.mem_filter.mp hp).1)
        (fun p hp => hVpos p (Finset.mem_filter.mp hp).1) hne₂ hecc₂ hret hρ₂
    -- the bridge from the induced shading to the cell shading
    have hband₂ : ∀ c ∈ T'', 2 ^ m ≤ cellBlockCount b₂ A rr c ∧
        cellBlockCount b₂ A rr c < 2 ^ (m + 1) := by
      intro c hc
      have hfil : cellBlockCount b₂ A rr c = cellBlockCount b₁ A rr c := by
        unfold cellBlockCount
        congr 1
        ext j
        simp only [Finset.mem_filter, hb₂]
        constructor
        · rintro ⟨⟨hjb, -⟩, hne⟩; exact ⟨hjb, hne⟩
        · rintro ⟨hjb, hne⟩
          refine ⟨⟨hjb, ?_⟩, hne⟩
          obtain ⟨x, hxA, hxc⟩ := hne
          exact ⟨x, hxA, hballreg' c hc hxc⟩
      rw [hfil]
      exact hband c hc
    have hZne₂ : ∀ j ∈ b₂, (A j ∩ ⋃ c ∈ T'', Metric.closedBall c rr).Nonempty :=
      fun j hj => (Finset.mem_filter.mp hj).2
    have hZbdd₂ : ∀ j ∈ b₂, Bornology.IsBounded (A j ∩ ⋃ c ∈ T'', Metric.closedBall c rr) :=
      fun j hj => ((Wb j).isCompact.isBounded.subset (hAsub j (hb₂sub hj))).subset
        Set.inter_subset_left
    have hZsub₂ : ∀ j ∈ b₂, iUnionShade ({p ∈ segs₂ | blk p = j}) Y'' ⊆
        A j ∩ ⋃ c ∈ T'', Metric.closedBall c rr := by
      intro j hj
      rw [hU₂ j hj]
      intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hps₁, hpj⟩ := Finset.mem_filter.mp hp
      simp only [hY', if_pos hps₁, ShadedBody.shade_restrictShade] at hxp
      refine ⟨?_, hxp.2⟩
      rw [← hpj]
      exact hshA p hps₁ hxp.1
    have hrK₂ : ∀ j ∈ b₂, 2 * rr ≤ 2 * (Wb j).scale := by
      intro j hj
      have h := hscale_ge j (hb₂bodies hj)
      have h0 : (0 : ℝ) ≤ (Wb j).scale := Metric.thickness_nonneg _ _
      linarith
    have hSbd₂ : ∀ j ∈ b₂, 2 * (Wb j).scale ≤ 4 * (w₁ : ℝ) := by
      intro j hj
      have h := (hw₁ j (hb₂bodies hj)).1
      have hs : (Wb j).scale = Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) := rfl
      rw [hs]
      linarith
    have hbridge := sum_volume_inducedShading_le_mul_sum_volume_cellShade b₂
      (fun j => {p ∈ segs₂ | blk p = j}) Y'' Wb T'' P m Sh hr A hT''sep hPmeas hPdisj hPunion
      hband₂ hSheq hZne₂ hZbdd₂ hZsub₂ hrK₂ hSbd₂
    have hShW : ∀ j ∈ b₂, volume (Sh j) = volume (W j).shade := by
      intro j hj
      have : (W j).shade = Sh j := by
        change (if hjj : j ∈ b₁ then Sh j else ∅) = Sh j
        rw [dif_pos (hb₂sub hj)]
      rw [this]
    have hshade₂ : ∑ j ∈ b₂, volume (Wind j).shade ≤
        ((collarCompareConstant (Module.finrank ℝ E) (2 * ((w₁ : ℝ) / 8)) (4 * w₁) *
          (cellCollarConstant (Module.finrank ℝ E) : NNReal) : NNReal) : ENNReal) *
          ∑ j ∈ b₂, volume (W j).shade := by
      rw [← Finset.sum_congr rfl hShW]
      refine hbridge.trans (le_of_eq ?_)
      push_cast
      ring
    have hcar₂ : ∀ j ∈ b₂, volume (Wind j).carrier = volume (W j).carrier := fun j _ => rfl
    have hfullW := fullness_le_mul_fullness_of_sum_shade_le b₂ W Wind hcar₂ hshade₂
    have hpow : (δ : ENNReal) ^ (3 * η) ≤ (δ : ENNReal) ^ (2 * η) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge
      · exact_mod_cast hδw₁.trans hw₁one
      · linarith
    calc (δ : ENNReal) ^ (3 * η) ≤ (δ : ENNReal) ^ (2 * η) := hpow
      _ ≤ (thinFibreDensityConstant CF Cfull θ (ShadedBody.OuterInnerVolumeRatio.exponent D) :
            ENNReal) * (ShadedBody.fullness b₂ Wind : ENNReal) := hT3
      _ ≤ (thinFibreDensityConstant CF Cfull θ (ShadedBody.OuterInnerVolumeRatio.exponent D) :
            ENNReal) *
          (((collarCompareConstant (Module.finrank ℝ E) (2 * ((w₁ : ℝ) / 8)) (4 * w₁) *
            (cellCollarConstant (Module.finrank ℝ E) : NNReal) : NNReal) : ENNReal) *
            (ShadedBody.fullness b₂ W : ENNReal)) := by gcongr
      _ = (thinCellFullnessConstant (Module.finrank ℝ E) segs.card bodies.card CF Cfull w₁
            (ShadedBody.OuterInnerVolumeRatio.exponent D) : ENNReal) *
          (ShadedBody.fullness b₂ W : ENNReal) := by
          rw [thinCellFullnessConstant, hθ]
          push_cast
          ring
  refine ⟨s₂, b₂, Y', W, hs₂sub.trans hs₁segs, hb₂sub.trans hb₁bodies, fun p _ => hcarY' p,
    ?_, ?_, ?_, hi, ?_, ?_, ?_, ?_, ?_, hvi⟩
  · -- (d) the shades shrink
    intro p hp₂
    have hp : p ∈ s₁ := hs₂sub hp₂
    simp only [hY', if_pos hp]
    intro x hx
    have h1 : x ∈ (Y₂ p).shade := hx.1.1
    have h2 : x ∈ (Y₁ p).shade := (href₂.2 p hp).2 h1
    exact thinY'_shade_subset (hδ₀ := hδ₀) (hdisc := hdisc) (D := D) (hw₁ := hw₁') (hs₁s₀ hp) h2
  · -- (e) the lower half of the sandwich
    intro j _
    show Wb j ≤ (Wb j).cthickening (Wb j).scale
    exact (Wb j).self_le_cthickening _
  · -- (f) the upper half of the sandwich
    intro j _
    exact le_rfl
  · -- (ii) the pointwise containment
    intro p hp₂ x hx
    have hp : p ∈ s₁ := hs₂sub hp₂
    refine ⟨(Finset.mem_filter.mp hp₂).2, ?_⟩
    simp only [hY', if_pos hp] at hx
    have hxA : x ∈ A (blk p) ∩ reg := ⟨hshA p hp hx.1, hx.2⟩
    have := hShsub (blk p) (hparent p hp) hxA
    show x ∈ (if hj : blk p ∈ b₁ then Sh (blk p) else ∅)
    rw [dif_pos (hparent p hp)]
    exact this
  · -- (v) the outer shade sits in the collar of the *retained* block union
    intro j hj₂
    have hj : j ∈ b₁ := hb₂sub hj₂
    rw [hblkfil j hj₂]
    show (if hjj : j ∈ b₁ then Sh j else ∅) ⊆ _
    rw [dif_pos hj]
    refine (hcollar j hj).trans (Metric.cthickening_mono ?_ _)
    have := hscale_ge j (hb₁bodies hj)
    have hs : (Wb j).scale = Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) := rfl
    rw [hs] at this
    linarith
  · -- (iii)(a) the outer family has 2-constant multiplicity
    intro x hx y hy
    rw [hUW] at hx hy
    have hxS : x ∈ ⋃ j ∈ b₁, Sh j := by
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      simp only [hW] at hxj
      rw [dif_pos hj] at hxj
      exact Set.mem_biUnion hj hxj
    have hyS : y ∈ ⋃ j ∈ b₁, Sh j := by
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      simp only [hW] at hyj
      rw [dif_pos hj] at hyj
      exact Set.mem_biUnion hj hyj
    have hfil : ∀ w : E, ({j ∈ b₁ | w ∈ (W j).shade}) = ({j ∈ b₁ | w ∈ Sh j}) := by
      intro w
      ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hj
      simp only [hW]
      rw [dif_pos hj]
    have := hShmult x hxS y hyS
    show ((({j ∈ b₂ | x ∈ (W j).shade}).card : ℕ) : NNReal)
      ≤ 2 * ((({j ∈ b₂ | y ∈ (W j).shade}).card : ℕ) : NNReal)
    rw [hWfil x, hWfil y, hfil x, hfil y]
    exact_mod_cast this
  · -- (iii)(b) the blockwise inner multiplicity, transported across all three restrictions
    obtain ⟨μ, hμ⟩ := thinInnerConstMult (hδ₀ := hδ₀) (hdisc := hdisc) (D := D) (hw₁ := hw₁')
    refine ⟨μ, fun j hj₂ x hx => ?_⟩
    have hj : j ∈ b₁ := hb₂sub hj₂
    rw [hblkfil j hj₂] at hx ⊢
    have hshade : ∀ p ∈ ({p ∈ s₁ | blk p = j}), (Y' p).shade = (Y₁ p).shade ∩ Sfin := by
      intro p hp; exact hY'shade p (Finset.mem_filter.mp hp).1
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    have hxS : x ∈ Sfin := (hshade p hp ▸ hxp).2
    have hxY₁ : x ∈ iUnionShade ({p ∈ s₁ | blk p = j}) Y₁ :=
      Set.mem_biUnion hp (hshade p hp ▸ hxp).1
    have heq := pointwiseMultiplicity_of_shade_inter ({p ∈ s₁ | blk p = j}) Y₁ Y' Sfin hshade hxS
    rw [heq, hfib₁ j hj]
    rw [hfib₁ j hj] at hxY₁
    exact hμ j (hb₁b₀ hj) x hxY₁
  · -- (iv) the equal-radius centred multiplicity at radius `w₁`
    have hVeq : iUnionShade s₁ Y' = iUnionShade s₁ Y₂ ∩ S' ∩ reg := by
      ext w
      constructor
      · rintro hw
        obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hw
        simp only [hY', if_pos hp] at hwp
        exact ⟨⟨Set.mem_biUnion hp hwp.1.1, hwp.1.2⟩, hwp.2⟩
      · rintro ⟨⟨hwU, hwS⟩, hwr⟩
        obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hwU
        refine Set.mem_biUnion hp ?_
        simp only [hY', if_pos hp]
        exact ⟨⟨hwp, hwS⟩, hwr⟩
    have hballreg : ∀ c ∈ T'', Metric.closedBall c rr ⊆ reg := fun c hc w hw =>
      Set.mem_biUnion hc hw
    have hballS' : ∀ c ∈ T'', Metric.closedBall c rr ⊆ S' := fun c hc w hw =>
      Set.mem_biUnion (hT''T' hc) hw
    have hVcov : iUnionShade s₁ Y' ⊆ ⋃ c ∈ T'', Metric.closedBall c rr := by
      rw [hVeq]; exact fun w hw => hw.2
    have hVinter : ∀ c ∈ T'', iUnionShade s₁ Y' ∩ Metric.closedBall c rr
        = iUnionShade s₁ Y₂ ∩ Metric.closedBall c rr := by
      intro c hc
      rw [hVeq]
      ext w
      constructor
      · rintro ⟨⟨⟨h1, -⟩, -⟩, h4⟩; exact ⟨h1, h4⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨⟨h1, hballS' c hc h2⟩, hballreg c hc h2⟩, h2⟩
    have hVcomp : ∀ c ∈ T'', ∀ c' ∈ T'',
        volume (iUnionShade s₁ Y' ∩ Metric.closedBall c rr) ≤
          2 * volume (iUnionShade s₁ Y' ∩ Metric.closedBall c' rr) := by
      intro c hc c' hc'
      rw [hVinter c hc, hVinter c' hc']
      exact hT'comp c (hT''T' hc) c' (hT''T' hc')
    intro x hx y hy
    rw [hUWf] at hx hy
    rw [hUY]
    have hycol : y ∈ Metric.cthickening (2 * rr) (iUnionShade s₁ Y') := by
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      simp only [hW] at hyj
      rw [dif_pos hj] at hyj
      refine Metric.cthickening_subset_of_subset _ ?_ (hcollar j hj hyj)
      exact fun w hw => by
        obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_biUnion (Finset.mem_filter.mp hp).1 hwp
    have hrad : (8 : ℝ) * rr = (w₁ : ℝ) := by rw [hrr]; push_cast; ring
    have := centredMult_of_separatedNet (V := iUnionShade s₁ Y') (T := T'')
      (r := w₁ / 8) hr hT''sep hVcov hVcomp x y (by rw [hrr] at hycol; exact hycol)
    rw [← hrr, hrad] at this
    exact this


/-! ### The corrected Proposition 5.1 interface, instantiated for the thin case

`ShadedBody.factoringAndMultPropCoreAtScale` (`Kakeya/Factoring/Combined.lean`) proves, for the
*weighted* pipeline family `ShadedBody.outerThickFamilyAtScale`, a bundle that already contains
most of what `Kakeya.ThinCase.factoringApply` asks for: `thick_fullness` is conjunct (i),
`inner_multiplicity` is conjunct (iii)(b), `outer_shade_subset` is conjunct (v),
`shading_containment` is conjunct (ii), `refinement` is conjunct (vi), and `inner_carrier` /
`outer_carrier` are the structural conjuncts. Its sibling
`ShadedBody.factoringAndMultPropCombined` adds `ball_comparison`, Item 7 corrected to open radius
`w₁` against **closed radius `2 w₁`** on the *inner* union — far better than the `7 * w₁` against
the *outer* union of `ShadedBody.outerFactoringFamily_avgMultOnBalls`, which is what the current
route to conjunct (iv) has to work around.

None of it was reachable. `Kakeya.Factoring.Combined` is not in `ThinSetup`'s import closure, and
the interface needs one datum the thin case had no producer for: `ShadedBody.OuterInnerVolumeRatio`,
a uniform dyadic bound of each outer carrier by each of its own inner carriers. That is *exactly*
`Kakeya.ThinCase.exists_eccentricity_exponent`.

The three declarations below are the whole bridge, and every hypothesis they need is already a
binder of `factoringApply`:

* `Kakeya.ThinCase.thinVolumeRatio` builds the missing datum from `hdims`, `hFr` and the
  carrier-nondegeneracy;
* `Kakeya.ThinCase.thinFactorFamily_outerIsAtScale` shows that `factoringApply`'s `hw₁` binder
  **is** `ShadedBody.FactorFamily.OuterIsAtScale 2 w₁`, verbatim, once the translation by `-z` is
  undone;
* `Kakeya.ThinCase.thinCoreAtScale` instantiates the interface.

`hdisc` is `Kakeya.ThinCase.thinFactorFamily_innerIsDiscretizedAtScale`, `hshape` is
`Kakeya.ThinCase.thinFactorFamily_innerHasSimilarShape` and `hFrostman` is
`Kakeya.ThinCase.thinFactorFamily_hasFrostmanFibers`, all of which already existed. -/

open Classical in
/-- The eccentricity datum the `AtScale` pipeline needs, built from the thin case's own
hypotheses. -/
noncomputable def thinVolumeRatio [Nontrivial E] {σ ω : Type*} [DecidableEq ω]
    (segs : Finset σ) (Y : σ → ShadedBody E) (bodies : Finset ω)
    (Wb : ω → ConvexSpaceBody E) (blk : σ → ω) (z : E)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    {CF : NNReal}
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0) :
    ShadedBody.OuterInnerVolumeRatio
      (thinFactorFamily segs Y bodies Wb blk z hblk hle) :=
  { exponent := twoPowExponent
      (CF * (segs.card : NNReal) * Metric.volume_comparison.C (Module.finrank ℝ E))
    volume_outer_le := by
      classical
      intro j hj i hi
      rw [thinFactorFamily_fiber] at hi
      obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
      have hmain := eccentricity_exponent_bound (CF := CF) segs Y bodies Wb blk hle hdims
        (fun j hj => by convert hFr j hj using 2) hVpos j hj i his hij
      show volume ((Wb j).translate (-z)).carrier
        ≤ 2 ^ twoPowExponent
            (CF * (segs.card : NNReal) * Metric.volume_comparison.C (Module.finrank ℝ E)) *
          volume (((Y i).translate (-z)).toConvexSpaceBody).carrier
      rw [toConvexSpaceBody_translate, Kakeya.volume_translate,
        Kakeya.volume_translate]
      exact hmain }

open Classical in
/-- The exponent `Kakeya.ThinCase.thinVolumeRatio` chooses is
`Kakeya.ThinCase.thinEccentricityExponent`, by definition. -/
@[simp] lemma thinVolumeRatio_exponent [Nontrivial E] {σ ω : Type*} [DecidableEq ω]
    (segs : Finset σ) (Y : σ → ShadedBody E) (bodies : Finset ω)
    (Wb : ω → ConvexSpaceBody E) (blk : σ → ω) (z : E)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    {CF : NNReal}
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0) :
    (thinVolumeRatio segs Y bodies Wb blk z hblk hle hdims hFr hVpos).exponent =
      thinEccentricityExponent (Module.finrank ℝ E) segs.card CF := rfl

open Classical in
/-- The whole corrected Proposition 5.1 interface, instantiated for the thin case's own family. -/
noncomputable def thinCoreAtScale [Nontrivial E] {σ ω : Type*} [DecidableEq ω]
    (segs : Finset σ) (Y : σ → ShadedBody E) (bodies : Finset ω)
    (Wb : ω → ConvexSpaceBody E) (blk : σ → ω) (z : E)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    {CF : NNReal} {δ₀ w₁ : NNReal} (hδ₀ : 0 < δ₀) (hw₁ : 0 < w₁)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0)
    (hscale : (thinFactorFamily segs Y bodies Wb blk z hblk hle).OuterIsAtScale 2 w₁)
    (hdim : Module.finrank ℝ E = 3)
    (hshape : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerHasSimilarShape 2)
    {C : ENNReal}
    (hFrost : (thinFactorFamily segs Y bodies Wb blk z hblk hle).HasFrostmanFibers C) :
    ShadedBody.FactoringAndMultPropCoreAtScale (C := C)
      (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc
      (thinVolumeRatio segs Y bodies Wb blk z hblk hle (CF := CF) hdims hFr hVpos) w₁ hw₁ :=
  ShadedBody.factoringAndMultPropCoreAtScale _ hδ₀ hdisc _ w₁ hw₁ hscale hdim hshape hFrost


/-- `factoringApply`'s `hw₁` binder **is** `OuterIsAtScale 2 w₁` for the thin family. -/
lemma thinFactorFamily_outerIsAtScale {σ ω : Type*} [DecidableEq ω]
    {segs : Finset σ} {Y : σ → ShadedBody E} {bodies : Finset ω}
    {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {z : E}
    {hblk : ∀ p ∈ segs, blk p ∈ bodies}
    {hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)} {w₁ : NNReal}
    (hw₁ : ∀ j ∈ bodies,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) ≤ 2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1)) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).OuterIsAtScale 2 w₁ := by
  intro j hj
  have h := hw₁ j hj
  have hs : Metric.thickness ℝ ((thinFactorFamily segs Y bodies Wb blk z hblk hle).outerBody
      j).carrier (Module.finrank ℝ E - 1)
      = Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) := by
    rw [thinFactorFamily_outerBody]
    exact scale_translate (Wb j) (-z)
  rw [hs]
  exact h



/-! ### Conjunct (i): what the reroute delivers, and the one binder it still needs

`Kakeya.ThinCase.thinFullness_sum` is conjunct (i)'s content, taken from the weighted pipeline's
aggregate Córdoba estimate `ShadedBody.outerThickFamilyAtScale_fullness`. With
`hfullness : δ ^ η ≤ Cfull * fullness segs Y` the squared inner fullness on its left becomes
`δ ^ (2 * η)`, so what the reroute proves is

```
δ ^ (2 * η) ≤ (Cfull ^ 2 * CF / K) * fullness bodies' W
```

and conjunct (i) asks for `δ ^ (3 * η)`, which is *weaker*. Deducing it needs
`δ ^ (3 * η) ≤ δ ^ (2 * η)`, i.e. `δ ^ η ≤ 1`, i.e. — since `δ ≤ w₁ ≤ 1` —

```
0 ≤ η
```

**That is not among `factoringApply`'s binders**, and it is not derivable from them: `hfullness`
and `hdens` both bound `δ ^ η` from above only, and for `η < 0` they are satisfied by taking
`Cfull` large. It is true at every call site (`Kakeya.VeryNotSticky.exists_thinConfig` builds `η`
as a `min` of positive quantities), so it costs nothing there.

The alternative that avoids the binder does not fit the constant. `fullness segs Y ≤ 1` turns
`hfullness` into `δ ^ η ≤ Cfull`, giving conjunct (i) at the constant `Cfull ^ 3 * CF / K`; but
`Kakeya.ThinCase.factoringApplyConstant CF Cfull Ccore` supplies only
`2 * volume_comparison.C 3 * CF * Cfull ^ 2 * Ccore`, and **no binder bounds `Cfull` in terms of
`Ccore`** — `hCcore2`, `hCcoreRef`, `hCcoreMult`, `hCcoreDyad`, `hCcoreFrost` and `hCcoreNet` all
bound `Ccore` from below by quantities built from `segs.card`, `bodies.card`, `δ` and `CF`, never
by `Cfull`. So the third power of `Cfull` cannot be paid for. -/


end Assembly

end ThinCase

end Kakeya
