/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform
public import Kakeya.MultiScaleLoss

/-!
# The displayed losses of the dividing-scales dichotomy

The two loss symbols `Kakeya.MultiScaleFac.gridLoss` and `Kakeya.MultiScaleFac.scaleGapLoss`, their
combination `Kakeya.MultiScaleFac.totalLoss`, the window rounding that decides which grid index a
real scale is read at, and the cardinality casts the dichotomy states its counting clause with.

This module is the merge of the former `MultiScaleLoss`, `MultiScaleWindow` and `SsfCardCast`.
Each former module keeps its own section, so its file-level `open`s and `variable`s stay confined
to it.

## The subpolynomial losses of the `⌈log log 1/δ⌉`-grid dichotomy

The two losses carried by the amended form of GWZ Lemma 7.7 (`Kakeya/MultiScaleFac/GapsA.lean`), and
the statement that each is subpolynomial.

Both are explicit functions of `δ` whose `δ`-independent parameters are quantified before `δ`.  They
are displayed in the conclusions of the dichotomy rather than converted into a power `δ^{-α}`, for
two reasons.  A fixed polylogarithmic exponent would be *wrong*: on a grid whose length is
`ssfGridLen δ = ⌈log log 1/δ⌉` each level is paid separately, so the exponent necessarily grows with
`δ`.  And committing to a power would be *less flexible*: it forces the smallness threshold to
depend on the consumer's accuracy, hence forces every intermediate lemma to carry that accuracy as a
parameter.  With the losses displayed, the threshold depends only on the dichotomy's own parameters,
and the consumer absorbs a loss where it needs to, by the three `exists_threshold_…` lemmas below.

The two losses have genuinely different sizes and neither bounds the other, which is why there are
two symbols and not one.  Writing `L = log 1/δ`, so that `ssfGridLen δ ≈ log L`:

* `gridLoss = e^{O((log L)^3)}` is the accumulation of one re-uniformization per *pair* of grid
  levels;
* `scaleGapLoss = e^{c L / log L}` is the cost of one transport across a grid gap;

and `L / log L` dwarfs `(log L)^3`.  Both exponents are `o(L)`, which is all subpolynomiality asks.

## The interior window of alternative (ii)-3 on the `⌈log log 1/δ⌉`-grid

The stopping test of the multiscale dichotomy refuses to cut within `⌈ε(b-a)⌉` grid indices of
either endpoint of a block `[a, b]`, so a statement about grid indices strictly inside the block
must place its indices inside that margin.  On the old grid, of length equal to the *step count*
`N`, a long block satisfies only `ε(b-a) ≥ ε²N = 1`, and absorbing the ceiling into a multiple of
`ε(b-a)` therefore costs a *fixed* factor: the window has to be widened from `ε` to `3ε` (see
`Kakeya.StickyKakeya.grid_window_admissible`, stated at `3 * ε`).

On the grid of length `M = ssfGridLen δ = ⌈log log 1/δ⌉` the same computation is much better.  A
long block now has `b - a ≥ εM`, hence

  `ε(b-a) ≥ ε²M = M/N`,

and `M → ∞` while the step count `N` stays fixed.  So `⌈ε(b-a)⌉ ≤ (1 + κ)ε(b-a)` already for
`κ = N/M`, and the widening factor tends to `1` as `δ → 0`.  The file proves this in
`ceil_le_mul_of_one_le_mul` and `grid_window_admissible`.

The residual is subpolynomial, which is the point.  Moving a window endpoint from exponent `ε` to
exponent `(1+κ)ε` multiplies it by `(σ_a/σ_b)^{κε} ≤ δ^{-κε(b-a)/M}`, and with `κ = N/M` and
`b - a ≤ M` that exponent is at most `εN/M = √N/M`: a factor `scaleGapLoss ⌈√N⌉ δ`, absorbed by
`totalLoss`.  This is `window_endpoint_le_scaleGapLoss_mul` below, and it is what makes the
`ε`-window form of the third bullet reachable from a `(1+κ)ε`-window supply.

## Reading a cardinality loss on natural-number coercions

The cardinality clauses of the amended dichotomies count in `ℝ≥0∞` on the coercions `(m : ℝ≥0∞)` of
the two cardinalities, whereas the loss lemmas that supply them are stated on `ENNReal.ofReal` of
the real coercions.  The two agree by `ENNReal.ofReal_natCast`; the transfer is isolated here so
that no consumer has to repeat it.

This is the direct counterpart of `Kakeya.MultiScaleFac.natCast_le_mul_natCast_of_ofReal_le`, which
performs the same transfer starting from a bound stated on the real line with an explicit real
coefficient.  Here the coefficient is already an element of `ℝ≥0∞`, so no coefficient hypothesis is
needed.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology
open Tube

namespace Kakeya


namespace MultiScaleFac

open _root_.StickyKakeya

/-! ### The accumulated per-level loss -/

/-- **The defining unfolding of `totalLoss`**, kept as a named lemma so that consumers never have to
`unfold` the definition to reach the real-valued product. -/
theorem totalLoss_eq_ofReal (A : NNReal) (K c : ℕ) (δ : NNReal) :
    totalLoss A K c δ = ENNReal.ofReal (gridLoss A K δ * scaleGapLoss c δ) := by
  rfl

/-- The real-valued product underlying `totalLoss` is at least `1`.  Isolated from
`one_le_totalLoss` and `totalLoss_toReal` so that the real estimate and the `ℝ≥0∞` coercion are
proved once each rather than interleaved. -/
theorem one_le_gridLoss_mul_scaleGapLoss (A : NNReal) (hA : 1 ≤ A) (K c : ℕ) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ gridLoss A K δ * scaleGapLoss c δ := by
  exact one_le_mul_of_one_le_of_one_le (one_le_gridLoss A hA K hδ1)
    (one_le_scaleGapLoss c hδ0 hδ1)

/-- **The real value carried by `totalLoss`.**  Below `δ = 1` the underlying product is at least
`1`, hence nonnegative, so `ENNReal.toReal` returns it unchanged.  This is the bridge a consumer
uses to move an `ℝ≥0∞` bound back to the real estimates `gridLoss`/`scaleGapLoss` are stated
with. -/
theorem totalLoss_toReal (A : NNReal) (hA : 1 ≤ A) (K c : ℕ) {δ : NNReal} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) : (totalLoss A K c δ).toReal = gridLoss A K δ * scaleGapLoss c δ := by
  rw [totalLoss_eq_ofReal, ENNReal.toReal_ofReal]
  exact le_trans zero_le_one (one_le_gridLoss_mul_scaleGapLoss A hA K c hδ0 hδ1)

/-- **A bounded number of passes costs one `gridLoss`.**  Both parameters of `gridLoss` are
quantified before `δ`, so raising the loss to a power that does not depend on `δ` returns a loss of
the same shape: `A` is replaced by `A^n` and the polylogarithmic degree by `n K`.  This makes it
free to perform a homogenizing pass at *every* step of the stopping time rather than once. -/
theorem gridLoss_pow (A : NNReal) (K n : ℕ) (δ : NNReal) :
    gridLoss A K δ ^ n = gridLoss (A ^ n) (n * K) δ := by
  unfold gridLoss
  push_cast
  rw [mul_pow, pow_mul]
  ring_nf



/-- **Two gap losses make one.**  The exponents add, since the loss is a power of `δ`. -/
theorem A.scaleGapLoss_add {δ : NNReal} (hδ : 0 < δ) (c₁ c₂ : ℕ) :
    scaleGapLoss c₁ δ * scaleGapLoss c₂ δ = scaleGapLoss (c₁ + c₂) δ := by
  unfold scaleGapLoss
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  rw [← Real.rpow_add hδ0]
  congr 1
  push_cast
  ring

/-- **A power of a gap loss is a gap loss.** -/
theorem A.scaleGapLoss_pow {δ : NNReal} (hδ : 0 < δ) (c k : ℕ) :
    scaleGapLoss c δ ^ k = scaleGapLoss (c * k) δ := by
  unfold scaleGapLoss
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast (le_of_lt hδ)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ0]
  congr 1
  push_cast
  ring


/-- **The gap loss is monotone in the number of gaps**, so a bound paying several gaps may be
raised to a bound paying a common larger number. -/
theorem A.scaleGapLoss_mono {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c₁ c₂ : ℕ}
    (hc : c₁ ≤ c₂) : scaleGapLoss c₁ δ ≤ scaleGapLoss c₂ δ := by
  unfold scaleGapLoss
  apply Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ) (by exact_mod_cast hδ1)
  apply neg_le_neg
  rcases Nat.eq_zero_or_pos (ssfGridLen δ) with hM | hM
  · rw [hM]
    simp
  · have hM0 : (0 : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast (Nat.zero_le _)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) hM0
/-- **The factor `δ^{-27/M}` of the terminal alternative is a gap loss.**  The stopping time
displays its coefficient as a power of `δ` with a rational exponent; on the grid of length
`ssfGridLen δ` that is `Kakeya.MultiScaleFac.scaleGapLoss 27 δ` on the nose. -/
theorem A.rpow_neg_div_eq_scaleGapLoss (δ : NNReal) (c : ℕ) :
    (δ : ℝ) ^ (-((c : ℝ) / (ssfGridLen δ : ℝ))) = scaleGapLoss c δ := by
  rfl

/-- **The displayed loss is monotone in all three of its parameters.**  Both factors are, and both
are nonnegative, so the product is.  Isolated from `MultiScaleFac.loss_raise` so that the
bare-constant factor that lemma also carries does not have to be re-derived wherever only the
loss is compared. -/
theorem totalLoss_mono {B C : NNReal} (hB : 1 ≤ B) (hBC : B ≤ C) {K K' c c' : ℕ}
    (hKK' : K ≤ K') (hcc' : c ≤ c') {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    totalLoss B K c δ ≤ totalLoss C K' c' δ := by
  have hgrid : gridLoss B K δ ≤ gridLoss C K' δ := gridLoss_mono hB hBC hKK' hδ1
  have hsg : (0 : ℝ) ≤ scaleGapLoss c δ := le_trans zero_le_one (one_le_scaleGapLoss c hδ hδ1)
  have hscl : scaleGapLoss c δ ≤ scaleGapLoss c' δ := A.scaleGapLoss_mono hδ hδ1 hcc'
  have hC : 1 ≤ C := le_trans hB hBC
  have hngrid : (0 : ℝ) ≤ gridLoss C K' δ := le_trans zero_le_one (one_le_gridLoss C hC K' hδ1)
  have hreal : gridLoss B K δ * scaleGapLoss c δ ≤ gridLoss C K' δ * scaleGapLoss c' δ :=
    mul_le_mul hgrid hscl hsg hngrid
  rw [totalLoss_eq_ofReal, totalLoss_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Raising a displayed loss to a larger one.**  Monotone in the base, in the polylogarithmic
degree and in the gap budget.  Shared by both halves of Lemma 7.7. -/
theorem loss_raise {B C : NNReal} (hB : 1 ≤ B) (hBC : B ≤ C) {K K' c c' : ℕ}
    (hKK' : K ≤ K') (hcc' : c ≤ c') {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (B : ENNReal) * totalLoss B K c δ ≤ (C : ENNReal) * totalLoss C K' c' δ :=
  mul_le_mul' (ENNReal.coe_le_coe.mpr hBC) (totalLoss_mono hB hBC hKK' hcc' hδ hδ1)

/-- **Two displayed losses make one**, at the product of the bases and the sums of the two
exponents.  The `ℝ≥0∞` reading of `Kakeya.MultiScaleFac.gridLoss_mul` together with
`A.scaleGapLoss_add`. -/
theorem totalLoss_mul {B₁ B₂ : NNReal} (hB₁ : 1 ≤ B₁) (_hB₂ : 1 ≤ B₂) (K₁ K₂ c₁ c₂ : ℕ)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    totalLoss B₁ K₁ c₁ δ * totalLoss B₂ K₂ c₂ δ
      = totalLoss (B₁ * B₂) (K₁ + K₂) (c₁ + c₂) δ := by
  have h1nn : (0 : ℝ) ≤ gridLoss B₁ K₁ δ * scaleGapLoss c₁ δ :=
    le_trans zero_le_one (one_le_gridLoss_mul_scaleGapLoss B₁ hB₁ K₁ c₁ hδ hδ1)
  rw [totalLoss_eq_ofReal, totalLoss_eq_ofReal, totalLoss_eq_ofReal, ← ENNReal.ofReal_mul h1nn]
  congr 1
  rw [mul_mul_mul_comm, gridLoss_mul B₁ B₂ K₁ K₂ δ, A.scaleGapLoss_add hδ c₁ c₂]
/-- **A real product bound against the loss transfers to `ℝ≥0∞`.**  The two nonnegativity side goals
that the coercion of a product creates are exactly the ones `one_le_gridLoss_mul_scaleGapLoss` and
`hy` settle; proving the transfer once here keeps each consumer to a single application. -/
theorem ofReal_le_totalLoss_mul_ofReal (A : NNReal) (_hA : 1 ≤ A) (K c : ℕ) {δ : NNReal}
    (_hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) {x y : ℝ} (_hy : 0 ≤ y)
    (h : x ≤ (totalLoss A K c δ).toReal * y) :
    ENNReal.ofReal x ≤ totalLoss A K c δ * ENNReal.ofReal y := by
  calc
    ENNReal.ofReal x ≤ ENNReal.ofReal ((totalLoss A K c δ).toReal * y) :=
      ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (totalLoss A K c δ).toReal * ENNReal.ofReal y := by
      rw [ENNReal.ofReal_mul (ENNReal.toReal_nonneg (a := totalLoss A K c δ))]
    _ = totalLoss A K c δ * ENNReal.ofReal y := by
      rw [ENNReal.ofReal_toReal (totalLoss_ne_top A K c δ)]

/-- **The generic transfer of a real product bound.**  An analytic estimate produces a real
multiplier `R`, a separate accounting lemma bounds `ENNReal.ofReal R` by a displayed loss `L`, and
the consumer gets the bound directly against `L`.  No sign hypothesis on `R` is needed: a negative
`R` forces `x ≤ 0`, where the conclusion is trivial. -/
private theorem ofReal_le_mul_ofReal_of_ofReal_le {L : ENNReal} {R : ℝ}
    (hRL : ENNReal.ofReal R ≤ L) {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ R * y) :
    ENNReal.ofReal x ≤ L * ENNReal.ofReal y := by
  by_cases hR : 0 ≤ R
  · calc
      ENNReal.ofReal x ≤ ENNReal.ofReal (R * y) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal R * ENNReal.ofReal y := by
        rw [ENNReal.ofReal_mul hR]
      _ ≤ L * ENNReal.ofReal y := by
        exact mul_le_mul_of_nonneg_right hRL zero_le
  · have hRneg : R ≤ 0 := le_of_not_ge hR
    have hRy : R * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hRneg hy
    have hx : x ≤ 0 := le_trans h hRy
    rw [ENNReal.ofReal_eq_zero.mpr hx]
    exact zero_le

/-- **The counting specialization of `ofReal_le_mul_ofReal_of_ofReal_le`**, in the shape every
cardinality clause downstream is stated in.  Both nonnegativity side goals are discharged inside, so
a consumer applies it to its real estimate with no further argument. -/
theorem natCast_le_mul_natCast_of_ofReal_le {L : ENNReal} {R : ℝ}
    (hRL : ENNReal.ofReal R ≤ L) {m n : ℕ} (h : (m : ℝ) ≤ R * (n : ℝ)) :
    (m : ENNReal) ≤ L * (n : ENNReal) := by
  have h' : ENNReal.ofReal (m : ℝ) ≤ L * ENNReal.ofReal (n : ℝ) :=
    ofReal_le_mul_ofReal_of_ofReal_le hRL (Nat.cast_nonneg n) h
  simpa [← ENNReal.ofReal_natCast] using h'

/-! ### Absorbing a ceiling into a multiplicative slack -/

/-- **A ceiling costs an arbitrarily small relative slack once the argument is large.**

`⌈x⌉ < x + 1`, so `⌈x⌉ ≤ (1 + κ)x` as soon as `1 ≤ κx`.  On the grid of length `ssfGridLen δ` the
argument `x = ε(b-a)` of the stopping margin grows like `M/N`, so `κ` may be taken as small as
`N/M`; on a grid whose length is the step count `N` one has only `x ≥ 1`, forcing `κ = 1`. -/
private theorem ceil_le_mul_of_one_le_mul {κ x : ℝ} (hx : 0 ≤ x) (h : 1 ≤ κ * x) :
    (⌈x⌉₊ : ℝ) ≤ (1 + κ) * x := by
  have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  nlinarith

/-! ### The window exponent `ε = 1/√N` -/

/-- The window exponent `ε = 1/√N` is positive. -/
private theorem eps_pos {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) : 0 < ε := by
  -- (extracted by Fuse golfer)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  exact hε ▸ div_pos zero_lt_one (Real.sqrt_pos_of_pos hN0)

/-- **The defining identity of the window exponent**: `ε = 1/√N` is exactly the exponent with
`ε²N = 1`, which is what turns a lower bound on the block length into a lower bound on the
stopping margin. -/
private theorem eps_mul_self_mul_natCast {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) : ε * ε * (N : ℝ) = 1 := by
  -- (extracted by Fuse golfer)
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos_of_pos hN0).ne'
  subst hε
  field_simp
  exact (Real.sq_sqrt hN0.le).symm

/-- **A long block is at least one margin wide.**  `⌈εM⌉ + a < b` gives `εM ≤ ⌈εM⌉ ≤ b - a`. -/
private theorem eps_mul_gridLen_le_sub {M : ℕ} {ε : ℝ} {a b : ℕ}
    (hlong : ⌈ε * (M : ℝ)⌉₊ + a < b) : ε * (M : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
  -- (extracted by Fuse golfer)
  have hcast : (⌈ε * (M : ℝ)⌉₊ : ℝ) + (a : ℝ) < (b : ℝ) := by exact_mod_cast hlong
  linarith [Nat.le_ceil (ε * (M : ℝ))]

/-- **The stopping margin of a long block absorbs a relative slack `κ` once `N ≤ κM`.**

`ε(b-a) ≥ ε²M ≥ ε²N/κ = 1/κ`, which is the hypothesis `ceil_le_mul_of_one_le_mul` asks for.  On
the grid of length `M = ssfGridLen δ` this holds at `κ = N/M`, tending to `0`. -/
private theorem one_le_mul_eps_mul_sub {M N : ℕ} (hN : 0 < N) {ε κ : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) (hκ : 0 < κ) (hNκM : (N : ℝ) ≤ κ * (M : ℝ))
    {a b : ℕ} (hlong : ⌈ε * (M : ℝ)⌉₊ + a < b) :
    (1 : ℝ) ≤ κ * (ε * ((b : ℝ) - (a : ℝ))) := by
  -- (extracted by Fuse golfer)
  have hεpos := eps_pos hN hε
  calc
    (1 : ℝ) = (ε * ε) * (N : ℝ) := (eps_mul_self_mul_natCast hN hε).symm
    _ ≤ (ε * ε) * (κ * (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hNκM (mul_nonneg hεpos.le hεpos.le)
    _ = κ * (ε * (ε * (M : ℝ))) := by ring
    _ ≤ κ * (ε * ((b : ℝ) - (a : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (eps_mul_gridLen_le_sub hlong) hεpos.le) hκ.le

/-! ### The sharpened window -/

/-- **The interior window of alternative (ii)-3 lands inside the stopping margin, with a widening
factor that tends to `1`.**  The sharp form of `Kakeya.StickyKakeya.grid_window_admissible`: the
grid length `M` and the step count `N` are separate parameters, and the window exponent is
`(1 + κ)ε` for any `κ` with `N ≤ κM`.  Taking `M = N` and `κ = 1` recovers a window of `2ε`. -/
theorem grid_window_admissible {δ : NNReal} {M N : ℕ} (hN : 0 < N) (hM : 0 < M) {ε κ : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) (hκ : 0 < κ) (hNκM : (N : ℝ) ≤ κ * (M : ℝ))
    (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) {a b c : ℕ}
    (hlong : ⌈ε * (M : ℝ)⌉₊ + a < b)
    (hl : (gridScale δ M b : ℝ)
            * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + κ) * ε)
          ≤ (gridScale δ M c : ℝ))
    (hr : (gridScale δ M c : ℝ)
          ≤ (gridScale δ M a : ℝ)
              * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ((1 + κ) * ε)) :
    a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧ c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b := by
  have hεpos : 0 < ε := eps_pos hN hε
  have hL : ε * (M : ℝ) ≤ (b : ℝ) - (a : ℝ) := eps_mul_gridLen_le_sub hlong
  have hbig : (1 : ℝ) ≤ κ * (ε * ((b : ℝ) - (a : ℝ))) :=
    one_le_mul_eps_mul_sub hN hε hκ hNκM hlong
  have hmargin : (⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℝ) ≤
      (1 + κ) * (ε * ((b : ℝ) - (a : ℝ))) := by
    have hεM : 0 < ε * (M : ℝ) := mul_pos hεpos (by exact_mod_cast hM)
    exact ceil_le_mul_of_one_le_mul (mul_pos hεpos (hεM.trans_le hL)).le hbig
  rw [gridScale_mul_ratio_rpow hδ M a b ((1 + κ) * ε), gridScale, NNReal.coe_rpow] at hl
  rw [gridScale_mul_ratio_rpow hδ M b a ((1 + κ) * ε), gridScale, NNReal.coe_rpow,
    show ((a : ℝ) - ((1 + κ) * ε) * ((a : ℝ) - (b : ℝ)))
      = (a : ℝ) + (1 + κ) * ε * ((b : ℝ) - (a : ℝ)) by ring] at hr
  have hcR := (rpow_div_le_rpow_div_iff hδ hδ1 hM
    ((b : ℝ) - (1 + κ) * ε * ((b : ℝ) - (a : ℝ))) (c : ℝ)).1 hl
  have haR := (rpow_div_le_rpow_div_iff hδ hδ1 hM
    (c : ℝ) ((a : ℝ) + (1 + κ) * ε * ((b : ℝ) - (a : ℝ)))).1 hr
  refine ⟨?_, ?_⟩
  · have hmc1 : ((a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℕ) : ℝ) ≤ (c : ℝ) := by
      push_cast
      linarith only [hmargin, haR]
    exact_mod_cast hmc1
  · have hmc2 : ((c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) := by
      push_cast
      linarith only [hmargin, hcR]
    exact_mod_cast hmc2

/-! ### The residual is one grid transport -/

/-- **Widening the window exponent costs a gap loss.**  The lower endpoint of the window at exponent
`e'` is at most `scaleGapLoss c δ` times the one at the smaller exponent `e`, provided
`(e' - e)(b-a) ≤ c`.  With `e = ε`, `e' = (1+κ)ε`, `κ = N/M` and `b - a ≤ M` this holds at
`c = ⌈εN⌉ = ⌈√N⌉`, so the sharpened window costs a single subpolynomial transport. -/
theorem window_endpoint_le_scaleGapLoss_mul {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hM : 0 < ssfGridLen δ) {a b c : ℕ} {e e' : ℝ}
    (hc : (e' - e) * ((b : ℝ) - (a : ℝ)) ≤ (c : ℝ)) :
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
      ≤ scaleGapLoss c δ
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              * ((gridScale δ (ssfGridLen δ) a : ℝ)
                  / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e) := by
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hM0 : (0 : ℝ) < (ssfGridLen δ : ℝ) := by exact_mod_cast hM
  rw [scaleGapLoss]
  rw [gridScale_mul_ratio_rpow hδ (ssfGridLen δ) a b e']
  rw [gridScale_mul_ratio_rpow hδ (ssfGridLen δ) a b e]
  rw [← Real.rpow_add hδ0]
  have hsum :
      -((c : ℝ) / (ssfGridLen δ : ℝ))
          + ((b : ℝ) - e * ((b : ℝ) - (a : ℝ))) / (ssfGridLen δ : ℝ)
        = (((b : ℝ) - e * ((b : ℝ) - (a : ℝ))) - (c : ℝ)) / (ssfGridLen δ : ℝ) := by
    field_simp [hM0.ne']
    ring
  rw [hsum]
  exact (rpow_div_le_rpow_div_iff hδ hδ1 hM
    ((b : ℝ) - e' * ((b : ℝ) - (a : ℝ)))
    (((b : ℝ) - e * ((b : ℝ) - (a : ℝ))) - (c : ℝ))).2 (by linarith only [hc])

/-! ### Rounding a real scale to a grid index -/

/-- **Every real scale inside a block is bracketed by two consecutive grid scales of that block.**
For `ρ` between the endpoints `σ_b ≤ ρ ≤ σ_a` of a block there is an index `c` of the block with
`σ_{c+1} ≤ ρ ≤ σ_c`, namely the largest index `c ≤ b` with `ρ ≤ σ_c`.  This is the rounding step
that the third bullet of both halves of the dichotomy needs. -/
theorem exists_gridIndex_of_mem_Icc {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M a b : ℕ}
    (hab : a ≤ b) {ρ : NNReal} (hlo : (gridScale δ M b : ℝ) ≤ (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ (gridScale δ M a : ℝ)) :
    ∃ c : ℕ, a ≤ c ∧ c ≤ b ∧ (gridScale δ M (c + 1) : ℝ) ≤ (ρ : ℝ)
      ∧ (ρ : ℝ) ≤ (gridScale δ M c : ℝ) := by
  classical
  let c : ℕ := Nat.findGreatest (fun k => (ρ : ℝ) ≤ (gridScale δ M k : ℝ)) b
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · exact Nat.le_findGreatest (P := fun k => (ρ : ℝ) ≤ (gridScale δ M k : ℝ)) hab hhi
  · exact Nat.findGreatest_le (P := fun k => (ρ : ℝ) ≤ (gridScale δ M k : ℝ)) b
  · rcases Nat.lt_or_eq_of_le
      (Nat.findGreatest_le (P := fun k => (ρ : ℝ) ≤ (gridScale δ M k : ℝ)) b) with hclt | hceq
    · have hnot : ¬ (ρ : ℝ) ≤ (gridScale δ M (c + 1) : ℝ) := by
        exact Nat.findGreatest_is_greatest (P := fun k => (ρ : ℝ) ≤ (gridScale δ M k : ℝ))
          (Nat.lt_succ_self c) (Nat.succ_le_of_lt hclt)
      exact le_of_lt (not_le.mp hnot)
    · dsimp [c] at hceq ⊢
      rw [hceq]
      exact le_trans (gridScale_antitone hδ hδ1 M (Nat.le_succ b)) hlo
  · exact Nat.findGreatest_spec (P := fun k => (ρ : ℝ) ≤ (gridScale δ M k : ℝ)) hab hhi

/-- **Rounding a real scale up to the neighbouring grid scale costs one gap loss.**  The coarser of
the two brackets of `exists_gridIndex_of_mem_Icc` exceeds `ρ` by at most
`σ_c / σ_{c+1} = δ^{-1/M} = scaleGapLoss 1 δ`.  This is the whole price of passing between a
statement at a grid index and the same statement at a real scale. -/
theorem gridScale_le_scaleGapLoss_mul {δ : NNReal} (hδ : 0 < δ) {c : ℕ} {ρ : NNReal}
    (hρ : (gridScale δ (ssfGridLen δ) (c + 1) : ℝ) ≤ (ρ : ℝ)) :
    (gridScale δ (ssfGridLen δ) c : ℝ) ≤ scaleGapLoss 1 δ * (ρ : ℝ) := by
  let M : ℝ := (ssfGridLen δ : ℝ)
  let d : ℝ := (δ : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast hδ
  have hpos : 0 < scaleGapLoss 1 δ := by
    rw [scaleGapLoss]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hδ) _
  calc
    (gridScale δ (ssfGridLen δ) c : ℝ) = d ^ ((c : ℝ) / M) := by
      rw [gridScale, NNReal.coe_rpow]
    _ = d ^ (-(1 / M)) * d ^ (((c : ℝ) + 1) / M) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    _ = scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) (c + 1) : ℝ) := by
      rw [scaleGapLoss, gridScale, NNReal.coe_rpow]
      rw [Nat.cast_add, Nat.cast_one]
    _ ≤ scaleGapLoss 1 δ * (ρ : ℝ) := by
      exact mul_le_mul_of_nonneg_left hρ (le_of_lt hpos)

/-- **A long block is at least three margins wide once the grid is three times the step count.**

`⌈εM⌉ + a < b` gives `ε(b-a) ≥ ε²M`, and `ε²N = 1`, so `ε²M ≥ 3` as soon as `3N ≤ M`.  This is what
makes the stopping margin `⌈ε(b-a)⌉` at least three grid steps, hence wide enough for the
three-step bracket `σ_c ≤ ρ ≤ σ_{c-3}` to sit inside the block. -/
private theorem three_le_eps_mul_sub_of_long {M N : ℕ} (hN : 0 < N)
    (hNM : (3 : ℝ) * (N : ℝ) ≤ (M : ℝ)) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ))
    {a b : ℕ} (hlong : ⌈ε * (M : ℝ)⌉₊ + a < b) :
    (3 : ℝ) ≤ ε * ((b : ℝ) - (a : ℝ)) := by
  have hεpos : 0 < ε := eps_pos hN hε
  calc
    (3 : ℝ) = 3 * ((ε * ε) * (N : ℝ)) := by rw [eps_mul_self_mul_natCast hN hε]; ring
    _ = (ε * ε) * (3 * (N : ℝ)) := by ring
    _ ≤ (ε * ε) * (M : ℝ) := mul_le_mul_of_nonneg_left hNM (mul_nonneg hεpos.le hεpos.le)
    _ = ε * (ε * (M : ℝ)) := by ring
    _ ≤ ε * ((b : ℝ) - (a : ℝ)) :=
      mul_le_mul_of_nonneg_left (eps_mul_gridLen_le_sub hlong) hεpos.le

/-- **Raising the window exponent shrinks the upper endpoint.**

The upper endpoint `σ_a (σ_b/σ_a)^e` has base `σ_b/σ_a ≤ 1`, so it is antitone in `e`.  Used to pass
from the window at exponent `(1+2κ)ε` to the wider admissibility window at `(1+κ)ε`. -/
theorem window_upper_antitone {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M a b : ℕ} (hab : a ≤ b)
    {e e' : ℝ} (_he : 0 ≤ e) (hee' : e ≤ e') :
    (gridScale δ M a : ℝ) * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ e'
      ≤ (gridScale δ M a : ℝ) * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ e := by
  have hposa : 0 < (gridScale δ M a : ℝ) := by
    exact_mod_cast gridScale_pos hδ M a
  have hposb : 0 < (gridScale δ M b : ℝ) := by
    exact_mod_cast gridScale_pos hδ M b
  have hbase : 0 < (gridScale δ M b : ℝ) / (gridScale δ M a : ℝ) :=
    div_pos hposb hposa
  have hbase_le_one : (gridScale δ M b : ℝ) / (gridScale δ M a : ℝ) ≤ 1 := by
    exact (div_le_one hposa).mpr (by exact_mod_cast gridScale_antitone hδ hδ1 M hab)
  have hrpow : ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ e'
      ≤ ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ e := by
    exact Real.rpow_le_rpow_of_exponent_ge hbase hbase_le_one hee'
  exact mul_le_mul_of_nonneg_left hrpow (le_of_lt hposa)

/-- **One grid step converts the `(1+2κ)ε` lower endpoint into the `(1+κ)ε` one.**  In exponents the
hypothesis reads `c ≤ b - (1+2κ)ε(b-a)` and the conclusion `c + 1 ≤ b - (1+κ)ε(b-a)`, so the whole
content is `κ·ε(b-a) ≥ 1` — on the grid of length `M = ⌈log log 1/δ⌉` with `κ = N/M` exactly
`ε²N = 1` combined with `b - a ≥ εM`. -/
private theorem window_lower_succ {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1) {M : ℕ}
    (hM : 0 < M) {ε κ : ℝ} {a b c : ℕ} (h1 : 1 ≤ κ * (ε * ((b : ℝ) - (a : ℝ))))
    (hprev : (gridScale δ M b : ℝ)
          * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + 2 * κ) * ε)
        ≤ (gridScale δ M c : ℝ)) :
    (gridScale δ M b : ℝ)
        * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + κ) * ε)
      ≤ (gridScale δ M (c + 1) : ℝ) := by
  rw [gridScale_mul_ratio_rpow hδ M a b ((1 + 2 * κ) * ε), gridScale, NNReal.coe_rpow] at hprev
  have hcR := (rpow_div_le_rpow_div_iff hδ hδ1 hM
    ((b : ℝ) - ((1 + 2 * κ) * ε) * ((b : ℝ) - (a : ℝ))) (c : ℝ)).1 hprev
  rw [gridScale_mul_ratio_rpow hδ M a b ((1 + κ) * ε), gridScale, NNReal.coe_rpow,
    Nat.cast_add, Nat.cast_one]
  exact (rpow_div_le_rpow_div_iff hδ hδ1 hM
    ((b : ℝ) - ((1 + κ) * ε) * ((b : ℝ) - (a : ℝ))) ((c : ℝ) + 1)).2 (by linarith only [hcR, h1])

/-- **An admissible cut index bracketing a real scale, on a window of exponent `(1+2κ)ε`.**  The
sharp form of `Kakeya.MultiScaleFac.exists_admissible_cut_index`, which needs the window `3ε`: for
`ρ` in the window at exponent `(1+2κ)ε` the index `c` is the successor of the one produced by
`exists_gridIndex_of_mem_Icc`, and its admissibility comes from `grid_window_admissible` at exponent
`(1+κ)ε`.  The hypothesis `3N ≤ M` makes the margin at least three grid steps. -/
theorem exists_admissible_cut_index_sharp {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (hNM : (3 : ℝ) * (N : ℝ) ≤ (M : ℝ))
    {ε κ : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ)) (hκ : 0 < κ) (hNκM : (N : ℝ) ≤ κ * (M : ℝ))
    {a b : ℕ} (_hbM : b ≤ M) (hlong : ⌈ε * (M : ℝ)⌉₊ + a < b)
    {ρ : NNReal} (_hρ : 0 < ρ)
    (hlo : (gridScale δ M b : ℝ)
        * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + 2 * κ) * ε) ≤ (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ (gridScale δ M a : ℝ)
        * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ((1 + 2 * κ) * ε)) :
    ∃ c : ℕ, 3 ≤ c ∧ c + 2 ≤ b ∧
      a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧ c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b ∧
      (gridScale δ M c : ℝ) ≤ (ρ : ℝ) ∧ (ρ : ℝ) ≤ (gridScale δ M (c - 3) : ℝ) := by
  have hεpos : 0 < ε := eps_pos hN hε
  have hbig : (1 : ℝ) ≤ κ * (ε * ((b : ℝ) - (a : ℝ))) :=
    one_le_mul_eps_mul_sub hN hε hκ hNκM hlong
  have hδ' : δ ≤ 1 := by exact_mod_cast (le_of_lt hδ1)
  have hab : a ≤ b := by omega
  have hσa : 0 < (gridScale δ M a : ℝ) := by exact_mod_cast gridScale_pos hδ M a
  have hσb : 0 < (gridScale δ M b : ℝ) := by exact_mod_cast gridScale_pos hδ M b
  have hσb_le_σa : (gridScale δ M b : ℝ) ≤ (gridScale δ M a : ℝ) := by
    exact_mod_cast (gridScale_antitone hδ hδ' M hab)
  have he0 : 0 ≤ (1 + 2 * κ) * ε := mul_nonneg (by positivity) hεpos.le
  have hlb : (gridScale δ M b : ℝ) ≤ (ρ : ℝ) :=
    (le_mul_of_one_le_right hσb.le
      (Real.one_le_rpow ((one_le_div hσb).mpr hσb_le_σa) he0)).trans hlo
  have hub : (ρ : ℝ) ≤ (gridScale δ M a : ℝ) :=
    hhi.trans (mul_le_of_le_one_right hσa.le
      (Real.rpow_le_one (div_nonneg hσb.le hσa.le) ((div_le_one hσa).mpr hσb_le_σa) he0))
  rcases exists_gridIndex_of_mem_Icc hδ hδ' hab hlb hub with ⟨c₀, hc₀a, hc₀b, hc₀lo, hc₀hi⟩
  have hbracket : (ρ : ℝ) ≤ (gridScale δ M ((c₀ + 1) - 3) : ℝ) :=
    hc₀hi.trans (by exact_mod_cast gridScale_antitone hδ hδ' M (by omega : (c₀ + 1) - 3 ≤ c₀))
  have hlower : (gridScale δ M b : ℝ)
        * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + κ) * ε)
      ≤ (gridScale δ M (c₀ + 1) : ℝ) :=
    window_lower_succ hδ hδ1 hM hbig (hlo.trans hc₀hi)
  have hupper_c : (gridScale δ M (c₀ + 1) : ℝ)
      ≤ (gridScale δ M a : ℝ)
          * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ((1 + κ) * ε) :=
    (hc₀lo.trans hhi).trans
      (window_upper_antitone hδ hδ' hab (e := (1 + κ) * ε) (e' := (1 + 2 * κ) * ε)
        (mul_nonneg (by positivity) hεpos.le)
        (mul_le_mul_of_nonneg_right (by linarith) hεpos.le))
  have hadm : a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c₀ + 1 ∧ c₀ + 1 + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b :=
    grid_window_admissible hN hM hε hκ hNκM hδ hδ1 hlong hlower hupper_c
  have hceil : 3 ≤ ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ := by
    exact_mod_cast (three_le_eps_mul_sub_of_long hN hNM hε hlong).trans (Nat.le_ceil _)
  exact ⟨c₀ + 1, by omega, by omega, hadm.1, hadm.2, hc₀lo, hbracket⟩

/-! ### Absorbing the grid length into the polylogarithmic factor -/

/-- **The grid length is dominated by the polylogarithmic factor of `gridLoss`.**  Since
`ssfGridLen δ = ⌈log log 1/δ⌉` and `log L ≤ L` at `L = -log δ`, the ceiling is at most `-log δ + 1`.
This lets a stopping-time loss carrying one factor of the *grid length* per level be charged to the
factor `(1 - log δ)` that `gridLoss` already carries, creating no new shape of loss. -/
private theorem ssfGridLen_le_one_sub_log {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (ssfGridLen δ : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
  let d : ℝ := (δ : ℝ)
  have hd : 0 < d := by exact_mod_cast hδ
  have hd1 : d ≤ 1 := by exact_mod_cast hδ1
  let L : ℝ := Real.log (1 / d)
  have hLdef : L = Real.log (1 / d) := rfl
  have hL : L = -Real.log d := by
    rw [hLdef, one_div, Real.log_inv]
  have hLnn : 0 ≤ L := by
    rw [hL]
    exact neg_nonneg.mpr (Real.log_nonpos hd.le hd1)
  have hrhs : 1 - Real.log d = 1 + L := by
    rw [sub_eq_add_neg, ← hL]
  rw [ssfGridLen]
  change (⌈Real.log (Real.log (1 / d))⌉₊ : ℝ) ≤ 1 - Real.log d
  rw [← hLdef, hrhs]
  by_cases h : 0 ≤ Real.log L
  · have hceil : (⌈Real.log L⌉₊ : ℝ) < Real.log L + 1 := Nat.ceil_lt_add_one h
    have hlog : Real.log L ≤ L := Real.log_le_self hLnn
    linarith
  · have hlogL : Real.log L < 0 := not_le.mp h
    have hceil0 : ⌈Real.log L⌉₊ = 0 := Nat.ceil_eq_zero.mpr hlogL.le
    rw [hceil0]
    norm_num
    exact le_trans zero_le_one (le_add_of_nonneg_right hLnn)

/-! ### The stopping-time loss is a `gridLoss` -/

/-! ### The hoisted stopping-time loss -/

/-- Twice the number of grid levels is dominated by the square of the polylogarithmic weight, once
the weight dominates the grid length and is at least `4`. -/
private theorem hoistedStopping_two_mul_succ_le_sq (M : ℕ) {W : ℝ} (hMW : (M : ℝ) ≤ W)
    (hW4 : (4 : ℝ) ≤ W) :
    2 * ((M : ℝ) + 1) ≤ W ^ 2 := by
  nlinarith [hMW, hW4, sq_nonneg W]

/-- The per-round base of the hoisted stopping-time loss is a single power of the weight: the
combinatorial factor costs the exponent `2`, the base `A₁` costs `M + 1`, and the polylogarithmic
factor already carries `K (M + 1)`. -/
private theorem hoistedStopping_base_le_pow (M K : ℕ) {A₁ W : ℝ} (hW : 1 ≤ W) (hA₁0 : 0 ≤ A₁)
    (hA₁W : A₁ ≤ W) (hsq : 2 * ((M : ℝ) + 1) ≤ W ^ 2) :
    2 * ((M : ℝ) + 1) * A₁ ^ (M + 1) * W ^ (K * (M + 1))
      ≤ W ^ (2 + (M + 1) + K * (M + 1)) := by
  calc 2 * ((M : ℝ) + 1) * A₁ ^ (M + 1) * W ^ (K * (M + 1))
      ≤ W ^ 2 * W ^ (M + 1) * W ^ (K * (M + 1)) := by
        gcongr
    _ = W ^ (2 + (M + 1) + K * (M + 1)) := by rw [← pow_add, ← pow_add]

/-- The exponent bookkeeping of the hoisted stopping-time loss: at most `M + 1` rounds, each costing
the exponent `2 + (M+1) + K(M+1)`, fit inside `(K+3)(M+1)^2`. -/
private theorem hoistedStopping_exponent_le (M K L : ℕ) (hL : L ≤ M + 1) :
    (2 + (M + 1) + K * (M + 1)) * L ≤ (K + 3) * (M + 1) ^ 2 := by
  have h1 : (2 + (M + 1) + K * (M + 1)) * L
      ≤ (2 + (M + 1) + K * (M + 1)) * (M + 1) :=
    Nat.mul_le_mul_left (2 + (M + 1) + K * (M + 1)) hL
  have h2 : (2 + (M + 1) + K * (M + 1)) * (M + 1)
      ≤ (K + 3) * (M + 1) ^ 2 := by
    have hle : 2 + (M + 1) + K * (M + 1) ≤ (K + 3) * (M + 1) := by
      nlinarith
    calc
      (2 + (M + 1) + K * (M + 1)) * (M + 1)
          ≤ (K + 3) * (M + 1) * (M + 1) := Nat.mul_le_mul_right (M + 1) hle
      _ = (K + 3) * (M + 1) ^ 2 := by ring_nf
  exact le_trans h1 h2

/-- The accumulated hoisted stopping-time loss is a single power of the weight. -/
private theorem hoistedStopping_pow_le_pow (M K L : ℕ) {A₁ W : ℝ} (hL : L ≤ M + 1) (hW : 1 ≤ W)
    (hA₁0 : 0 ≤ A₁) (hA₁W : A₁ ≤ W) (hsq : 2 * ((M : ℝ) + 1) ≤ W ^ 2) :
    (2 * ((M : ℝ) + 1) * A₁ ^ (M + 1) * W ^ (K * (M + 1))) ^ L
      ≤ W ^ ((K + 3) * (M + 1) ^ 2) := by
  have hW0 : (0 : ℝ) ≤ W := le_trans zero_le_one hW
  have hbase := hoistedStopping_base_le_pow M K hW hA₁0 hA₁W hsq
  have hnn : (0 : ℝ) ≤ 2 * ((M : ℝ) + 1) * A₁ ^ (M + 1) * W ^ (K * (M + 1)) :=
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hA₁0 _)) (pow_nonneg hW0 _)
  calc (2 * ((M : ℝ) + 1) * A₁ ^ (M + 1) * W ^ (K * (M + 1))) ^ L
      ≤ (W ^ (2 + (M + 1) + K * (M + 1))) ^ L := pow_le_pow_left₀ hnn hbase L
    _ = W ^ ((2 + (M + 1) + K * (M + 1)) * L) := by rw [← pow_mul]
    _ ≤ W ^ ((K + 3) * (M + 1) ^ 2) :=
        pow_le_pow_right₀ hW (hoistedStopping_exponent_le M K L hL)

/-- **The loss handed out by the *hoisted* multiscale stopping time is a `gridLoss`.**
The companion of `stoppingLoss_le_gridLoss` for the shape the refined cut actually produces: the
per-round cost carries the hoisted per-level base `A₁` raised to the number `M + 1` of levels, and a
polylogarithmic factor of exponent `K (M + 1)`.  The two shapes disagree at `N = ssfGridLen δ`. -/
theorem hoistedStoppingLoss_le_gridLoss (A₁ : NNReal) (hA₁ : 1 ≤ A₁) (K L : ℕ)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : L ≤ ssfGridLen δ + 1)
    (hA₁W : (A₁ : ℝ) ≤ 1 - Real.log (δ : ℝ))
    (hW4 : (4 : ℝ) ≤ 1 - Real.log (δ : ℝ))
    {A : NNReal} (hA : 1 ≤ A) :
    (2 * ((ssfGridLen δ : ℝ) + 1) * (A₁ : ℝ) ^ (ssfGridLen δ + 1)
        * (1 - Real.log (δ : ℝ)) ^ (K * (ssfGridLen δ + 1))) ^ L
      ≤ gridLoss A (K + 3) δ := by
  set M : ℕ := ssfGridLen δ with hM
  set W : ℝ := 1 - Real.log (δ : ℝ) with hWdef
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hW : (1 : ℝ) ≤ W := by
    rw [hWdef]
    have hlog : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos hδR.le hδ1R
    linarith
  have hMW : (M : ℝ) ≤ W := by
    rw [hM, hWdef]
    exact ssfGridLen_le_one_sub_log hδ hδ1
  have hsq := hoistedStopping_two_mul_succ_le_sq M hMW hW4
  have hA₁0 : (0 : ℝ) ≤ (A₁ : ℝ) := le_trans zero_le_one (by exact_mod_cast hA₁)
  have hmain := hoistedStopping_pow_le_pow M K L hL hW hA₁0 hA₁W hsq
  have hA1R : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hApow : (1 : ℝ) ≤ (A : ℝ) ^ (M + 1) := one_le_pow₀ hA1R
  calc
    (2 * ((M : ℝ) + 1) * (A₁ : ℝ) ^ (M + 1) * W ^ (K * (M + 1))) ^ L
        ≤ W ^ ((K + 3) * (M + 1) ^ 2) := hmain
    _ = 1 * W ^ ((K + 3) * (M + 1) ^ 2) := by ring
    _ ≤ (A : ℝ) ^ (M + 1) * W ^ ((K + 3) * (M + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hApow (pow_nonneg (le_trans zero_le_one hW) _)
    _ = gridLoss A (K + 3) δ := by rw [gridLoss]

/-- Below an explicit threshold the weight `1 - log δ` dominates both `A₁` and `4`. -/
private theorem hoistedStopping_threshold_bounds (A₁ : NNReal) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
      (A₁ : ℝ) ≤ 1 - Real.log (δ : ℝ) ∧ (4 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
  set t : ℝ := 1 - max 4 (A₁ : ℝ) with ht
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hcoe : ((Real.toNNReal (Real.exp t) : NNReal) : ℝ) = Real.exp t :=
    Real.coe_toNNReal _ hexp.le
  refine ⟨Real.toNNReal (Real.exp t), ?_, ?_, ?_⟩
  · exact Real.toNNReal_pos.mpr hexp
  · have h4 : (4 : ℝ) ≤ max 4 (A₁ : ℝ) := le_max_left _ _
    have ht0 : t ≤ 0 := by rw [ht]; linarith
    have : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht0
    rw [← NNReal.coe_le_coe, hcoe, NNReal.coe_one]
    exact this
  · intro δ hδ hδδ₀
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    have hδle : (δ : ℝ) ≤ Real.exp t := by
      have := hδδ₀
      rw [← NNReal.coe_le_coe, hcoe] at this
      exact this
    have hlog : Real.log (δ : ℝ) ≤ t := by
      have h := Real.log_le_log hδR hδle
      rwa [Real.log_exp] at h
    have hmax : max 4 (A₁ : ℝ) ≤ 1 - Real.log (δ : ℝ) := by rw [ht] at hlog; linarith
    exact ⟨le_trans (le_max_right _ _) hmax, le_trans (le_max_left _ _) hmax⟩

/-- **The two threshold hypotheses of `hoistedStoppingLoss_le_gridLoss` are automatic for small
`δ`.**  Since `1 - log δ → ∞` as `δ → 0⁺`, a threshold depending only on the hoisted per-level base
`A₁` discharges both `hA₁W` and `hW4`, so the loss of the hoisted stopping time is a `gridLoss`
outright, with no side conditions, below a threshold chosen before `δ`. -/
theorem exists_threshold_hoistedStoppingLoss_le_gridLoss (A₁ : NNReal) (hA₁ : 1 ≤ A₁) (K : ℕ)
    {A : NNReal} (hA : 1 ≤ A) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
      ∀ L ≤ ssfGridLen δ + 1,
        (2 * ((ssfGridLen δ : ℝ) + 1) * (A₁ : ℝ) ^ (ssfGridLen δ + 1)
            * (1 - Real.log (δ : ℝ)) ^ (K * (ssfGridLen δ + 1))) ^ L
          ≤ gridLoss A (K + 3) δ := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hbounds⟩ := hoistedStopping_threshold_bounds A₁
  refine ⟨δ₀, hδ₀, hδ₀1, ?_⟩
  intro δ hδ hδδ₀ L hL
  obtain ⟨hA₁W, hW4⟩ := hbounds δ hδ hδδ₀
  have hδ1 : δ ≤ 1 := le_trans hδδ₀ hδ₀1
  exact hoistedStoppingLoss_le_gridLoss A₁ hA₁ K L hδ hδ1 hL hA₁W hW4 hA

/-- **A cardinality bound moved from `ENNReal.ofReal` to the natural-number coercion.**

The loss factor `L` is arbitrary, so this applies to a `Kakeya.MultiScaleFac.totalLoss` as well as
to
any of the losses it is built from. -/
theorem natCast_le_mul_natCast_of_ofReal_natCast_le {L : ENNReal} {m n : ℕ}
    (h : ENNReal.ofReal (m : ℝ) ≤ L * ENNReal.ofReal (n : ℝ)) :
    (m : ENNReal) ≤ L * (n : ENNReal) := by
  simpa [← ENNReal.ofReal_natCast] using h

/-! ### The quadratic pass of the banded stopping time -/

/-- **A quadratic polylogarithmic power at a grid length below `ssfGridLen δ` is one `gridLoss`**
(blueprint `lem:polylogPowQuadLeGridLoss`).  The polylogarithmic exponent of
`Kakeya.MultiScaleFac.gridLoss` is `K (ssfGridLen δ + 1)^2`, so at the degree `3K` it absorbs
`K (Mg+2)(Mg+1)` for every `Mg ≤ ssfGridLen δ`.  The multiplier `2` of the paired pass is freed. -/
theorem polylog_pow_quad_le_gridLoss {Mg : ℕ} {δ : NNReal} (hδ1 : δ ≤ 1)
    (hMg : Mg ≤ ssfGridLen δ) (K : ℕ) {C : NNReal} (hC : 1 ≤ C) :
    (1 - Real.log (δ : ℝ)) ^ (K * ((Mg + 2) * (Mg + 1))) ≤ gridLoss C (3 * K) δ := by
  let M : ℕ := ssfGridLen δ
  let t : ℝ := 1 - Real.log (δ : ℝ)
  have hlog : Real.log (δ : ℝ) ≤ 0 :=
    Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
  have ht1 : 1 ≤ t := by
    dsimp [t]
    linarith
  have ht0 : 0 ≤ t := by linarith
  have hMgM : Mg ≤ M := by
    simpa [M] using hMg
  have hmul : (Mg + 2) * (Mg + 1) ≤ 3 * (M + 1) ^ 2 := by
    nlinarith
  have hexp : K * ((Mg + 2) * (Mg + 1)) ≤ (3 * K) * (M + 1) ^ 2 := by
    nlinarith [hmul]
  calc
    t ^ (K * ((Mg + 2) * (Mg + 1))) ≤ t ^ ((3 * K) * (M + 1) ^ 2) := by
      exact pow_le_pow_right₀ ht1 hexp
    _ ≤ (C : ℝ) ^ (M + 1) * t ^ ((3 * K) * (M + 1) ^ 2) := by
      have hCpow : (1 : ℝ) ≤ (C : ℝ) ^ (M + 1) := by
        simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by exact_mod_cast hC) (M + 1))
      exact le_mul_of_one_le_left (pow_nonneg ht0 _) hCpow
    _ = gridLoss C (3 * K) δ := by
      unfold gridLoss
      simp [M, t]

/-- **A `δ`-independent number of rounds of the quadratic pass is one `gridLoss`** (blueprint
`lem:polylogPowQuadPowLeGridLoss`).  The rounds are counted by the step budget `N`, fixed before
`δ`, so raising the one-round bound to the power `L ≤ N + 1` returns a loss of the same shape by
`Kakeya.MultiScaleFac.gridLoss_pow`.  Counting rounds by the grid length would make it cubic. -/
theorem polylog_pow_quad_pow_le_gridLoss {Mg L N : ℕ} {δ : NNReal} (hδ1 : δ ≤ 1)
    (hMg : Mg ≤ ssfGridLen δ) (hL : L ≤ N + 1) (K : ℕ) :
    ((1 - Real.log (δ : ℝ)) ^ (K * ((Mg + 2) * (Mg + 1)))) ^ L
      ≤ gridLoss 1 ((N + 1) * (3 * K)) δ := by
  have hY0 : (0 : ℝ) ≤ (1 - Real.log (δ : ℝ)) ^ (K * ((Mg + 2) * (Mg + 1))) := by
    have hlog : Real.log (δ : ℝ) ≤ 0 :=
      Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
    have ht0 : 0 ≤ 1 - Real.log (δ : ℝ) := by linarith
    exact pow_nonneg ht0 _
  have hYL : (1 - Real.log (δ : ℝ)) ^ (K * ((Mg + 2) * (Mg + 1))) ≤ gridLoss 1 (3 * K) δ := by
    simpa using polylog_pow_quad_le_gridLoss hδ1 hMg K (C := 1) (by norm_num)
  have hGL : (1 : ℝ) ≤ gridLoss 1 (3 * K) δ := one_le_gridLoss 1 (by norm_num) (3 * K) hδ1
  calc
    ((1 - Real.log (δ : ℝ)) ^ (K * ((Mg + 2) * (Mg + 1)))) ^ L ≤ (gridLoss 1 (3 * K) δ) ^ L :=
      pow_le_pow_left₀ hY0 hYL L
    _ ≤ (gridLoss 1 (3 * K) δ) ^ (N + 1) := pow_le_pow_right₀ hGL hL
    _ = gridLoss 1 ((N + 1) * (3 * K)) δ := by
      simpa [one_pow] using gridLoss_pow 1 (3 * K) (N + 1) δ

/-- **The terminal block constant of the self-banded stopping time, cast and bounded** (blueprint
`lem:selfBandCtLeOfReal`).  Pure cast arithmetic: the `NNReal`-valued bound of
`exists_maximal_cuts_banded_hoisted_selfBand` carries no combinatorial factor, whereas the
accumulated-loss bounds are real-valued and carry `2(Mg+1) ≥ 1`.  The majorant `G` is left free. -/
theorem selfBand_ct_le_ofReal {δ : NNReal} (hδ1 : δ ≤ 1) {Mg K1 L : ℕ} {C1 : NNReal} {G : ℝ}
    (hstep : (2 * ((Mg : ℝ) + 1) * (C1 : ℝ) ^ (Mg + 1)
        * (1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L ≤ G)
    {Ct : NNReal}
    (hCt : Ct ≤ (C1 ^ (Mg + 1)
        * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1))))) ^ L) :
    (Ct : ENNReal) ≤ ENNReal.ofReal G := by
  have hδnonneg : (0 : ℝ) ≤ (δ : ℝ) := by exact NNReal.coe_nonneg _
  have hδlog : Real.log (δ : ℝ) ≤ 0 := by
    exact Real.log_nonpos hδnonneg (by exact_mod_cast hδ1)
  let W := 1 - Real.log (δ : ℝ)
  have hW : (1 : ℝ) ≤ W := by dsimp [W]; linarith
  have hWnonneg : 0 ≤ W := by exact zero_le_one.trans hW
  have hWpow : 0 ≤ W ^ (K1 * ((Mg + 2) * (Mg + 1))) := by
    exact pow_nonneg hWnonneg _
  have hprod_coe :
      (((C1 ^ (Mg + 1) * Real.toNNReal (W ^ (K1 * ((Mg + 2) * (Mg + 1))))) ^ L : NNReal) : ℝ) =
        ((C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L := by
    rw [Real.toNNReal_of_nonneg]
    · rw [NNReal.coe_pow, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_mk]
    · exact hWpow
  have hCt_real : (Ct : ℝ) ≤ ((C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L := by
    have hm := NNReal.coe_le_coe.mpr hCt
    rwa [hprod_coe] at hm
  have hbase_nonneg : 0 ≤ (C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1))) := by
    exact mul_nonneg (by positivity) hWpow
  have hMfact : (1 : ℝ) ≤ 2 * ((Mg : ℝ) + 1) := by
    linarith
  have hle : (C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1)))
      ≤ 2 * ((Mg : ℝ) + 1) * (C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1))) := by
    simpa [mul_assoc] using (le_mul_of_one_le_left hbase_nonneg hMfact)
  have hpowle : ((C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L
      ≤ (2 * ((Mg : ℝ) + 1) * (C1 : ℝ) ^ (Mg + 1) * W ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L := by
    exact pow_le_pow_left₀ hbase_nonneg hle L
  have hCt_c : (Ct : ℝ) ≤ (2 * ((Mg : ℝ) + 1) * (C1 : ℝ) ^ (Mg + 1)
      * W ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L := by
    exact le_trans hCt_real hpowle
  have hstepW : (2 * ((Mg : ℝ) + 1) * (C1 : ℝ) ^ (Mg + 1)
      * W ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L ≤ G := by
    simpa [W] using hstep
  have hCt_G : (Ct : ℝ) ≤ G := by
    exact le_trans hCt_c hstepW
  calc
    (Ct : ENNReal) = ENNReal.ofReal (Ct : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal G := ENNReal.ofReal_le_ofReal hCt_G

/-- **The terminal block constant of the self-banded stopping time is a `gridLoss`**, the
`gridLoss`-valued reading of `Kakeya.MultiScaleFac.selfBand_ct_le_ofReal` (blueprint
`lem:selfBandCtLeOfReal`).  The quadratic counterpart of the `Ct`-clause step of
`Kakeya.MultiScaleFac.dividingScalesFrostman`, which is the form the dichotomy consumes. -/
theorem selfBand_ct_le_gridLoss {δ : NNReal} (hδ1 : δ ≤ 1) {Mg K1 L Kt : ℕ} {C1 A : NNReal}
    (hstep : (2 * ((Mg : ℝ) + 1) * (C1 : ℝ) ^ (Mg + 1)
        * (1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L ≤ gridLoss A Kt δ)
    {Ct : NNReal}
    (hCt : Ct ≤ (C1 ^ (Mg + 1)
        * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1))))) ^ L) :
    (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss A Kt δ) := by
  exact selfBand_ct_le_ofReal hδ1 hstep hCt

/-- **The cardinality loss of the self-banded stopping time, displayed at a common degree**
(blueprint `lem:selfBandCardLeTotalLoss`).

The accumulated bound is raised from the degree it is proved at to whatever common degree the
assembly displays, by `Kakeya.MultiScaleFac.gridLoss_mono`, and then to a `totalLoss`. -/
theorem selfBand_card_le_totalLoss {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {Mg K1 L : ℕ} {A : ℝ}
    {C : NNReal} (hC : 1 ≤ C) {Kt K c : ℕ} (hK : Kt ≤ K)
    (hstep : (2 * ((Mg : ℝ) + 1) * A ^ (Mg + 1)
        * (1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L ≤ gridLoss C Kt δ)
    {x y : ℝ} (hy : 0 ≤ y)
    (hxy : x ≤ (2 * ((Mg : ℝ) + 1) * A ^ (Mg + 1)
        * (1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L * y) :
    ENNReal.ofReal x ≤ totalLoss C K c δ * ENNReal.ofReal y := by
  have hmono : gridLoss C Kt δ ≤ gridLoss C K δ := gridLoss_mono hC le_rfl hK hδ1
  have hgnn : (0 : ℝ) ≤ gridLoss C K δ := le_trans zero_le_one (one_le_gridLoss C hC K hδ1)
  have hsc : (1 : ℝ) ≤ scaleGapLoss c δ := one_le_scaleGapLoss c hδ hδ1
  have hprod : gridLoss C K δ ≤ gridLoss C K δ * scaleGapLoss c δ :=
    le_mul_of_one_le_right hgnn hsc
  have htot : (2 * ((Mg : ℝ) + 1) * A ^ (Mg + 1)
      * (1 - Real.log (δ : ℝ)) ^ (K1 * ((Mg + 2) * (Mg + 1)))) ^ L
        ≤ (totalLoss C K c δ).toReal := by
    rw [totalLoss_toReal C hC K c hδ hδ1]
    exact le_trans hstep (le_trans hmono hprod)
  have hfin : x ≤ (totalLoss C K c δ).toReal * y :=
    le_trans hxy (mul_le_mul_of_nonneg_right htot hy)
  exact ofReal_le_totalLoss_mul_ofReal C hC K c hδ hδ1 hy hfin

end MultiScaleFac
end Kakeya

end
