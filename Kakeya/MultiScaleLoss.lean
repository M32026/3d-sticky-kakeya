/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform

/-!
# The subpolynomial losses of the `⌈log log 1/δ⌉`-grid dichotomy

The two losses carried by GWZ Lemma 7.7 (`Kakeya/MultiScaleFac.lean`), and the statement that each
is subpolynomial.  Writing `L = log 1/δ`, so that `ssfGridLen δ ≈ log L`:

* `gridLoss = e^{O((log L)^3)}` accumulates one re-uniformization per *pair* of grid levels;
* `scaleGapLoss = e^{c L / log L}` is the cost of one transport across a grid gap.

Neither bounds the other, so both are carried, as `totalLoss`.  They are displayed rather than
converted into a power `δ^{-α}` so that the smallness threshold depends only on the dichotomy's own
parameters, each consumer absorbing a loss at the accuracy it can afford by the three
`exists_threshold_…` lemmas below.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube
open scoped Topology

namespace StickyKakeya

/-! ### The accumulated per-level loss -/

/-- **The loss accumulated by one re-uniformization per grid level**, on the grid of length
`ssfGridLen δ = ⌈log log 1/δ⌉`.

The base `A` and the polylogarithmic exponent `K` are quantified before `δ`; only the exponents
built from `ssfGridLen δ + 1`, the number of levels, are functions of `δ`.  The expression is
subpolynomial (`exists_threshold_gridLoss_le`) but is left displayed, so that a consumer may absorb
it at whatever accuracy it can afford.

The polylogarithmic factor carries the *square* of the number of levels.  A homogenizing pass that
brackets a quantity attached to a single grid level performs one pigeonhole per level and needs only
`K (M + 1)`; a pass that brackets a quantity attached to a *pair* of levels, as the third bullet of
alternative (ii) requires on both halves of Lemma 7.7, performs one pigeonhole per pair and needs
`K (M + 1)^2`.  There is no way to charge the extra factor elsewhere: `A` and `K` are quantified
before `δ`, so neither can absorb a factor growing with `δ`, and `scaleGapLoss` is a different
shape.
Enlarging the exponent is safe for every consumer, `gridLoss` occurring only on the greater side of
upper bounds, and costs nothing asymptotically: the logarithm of the whole expression is
`O((log log 1/δ)^3)`, still `o(log 1/δ)`. -/
noncomputable def gridLoss (A : NNReal) (K : ℕ) (δ : NNReal) : ℝ :=
  (A : ℝ) ^ (ssfGridLen δ + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (ssfGridLen δ + 1) ^ 2)

/-- **The loss of one transport across a grid gap.**

Comparing a Frostman constant at a real scale with the one at the neighbouring grid scale costs the
ratio of two consecutive grid scales raised to a dimensional power, that is `δ^{-c/⌈log log 1/δ⌉}`.

This is *not* dominated by `gridLoss`, and the two must therefore be carried separately: writing
`L = log 1/δ`, so that `ssfGridLen δ ≈ log L`, one has `gridLoss = e^{O((log L)^3)}` whereas
`scaleGapLoss = e^{c L / log L}`, and `L / log L` dwarfs `(log L)^3`.  Both are subpolynomial, which
is all a consumer needs, but neither bounds the other. -/
noncomputable def scaleGapLoss (c : ℕ) (δ : NNReal) : ℝ :=
  (δ : ℝ) ^ (-((c : ℝ) / (ssfGridLen δ : ℝ)))

/-- **The two losses together.**  Used in every conclusion of
`StickyKakeya.dividingScalesFrostman`, so that one symbol covers both the per-level
re-uniformizations and the transports across grid gaps.  Valued in `ENNReal`, the type in which
those conclusions are stated, so that no consumer has to wrap it in `ENNReal.ofReal`. -/
noncomputable def totalLoss (A : NNReal) (K c : ℕ) (δ : NNReal) : ENNReal :=
  ENNReal.ofReal (gridLoss A K δ * scaleGapLoss c δ)

/-- The combined loss is finite, which is what lets it be moved across an `ENNReal` inequality. -/
theorem totalLoss_ne_top (A : NNReal) (K c : ℕ) (δ : NNReal) : totalLoss A K c δ ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The loss is at least `1`, so it may be inserted into any upper bound. -/
theorem one_le_gridLoss (A : NNReal) (hA : 1 ≤ A) (K : ℕ) {δ : NNReal} (hδ1 : δ ≤ 1) :
    1 ≤ gridLoss A K δ := by
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hA
  have hδ1' : (δ : ℝ) ≤ 1 := by
    exact_mod_cast hδ1
  have hδlog : Real.log (δ : ℝ) ≤ 0 := by
    exact Real.log_nonpos (by positivity) hδ1'
  have hbase : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by
    linarith
  unfold gridLoss
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA1) (one_le_pow₀ hbase)

/-- The gap loss is at least `1`. -/
theorem one_le_scaleGapLoss (c : ℕ) {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ scaleGapLoss c δ := by
  unfold scaleGapLoss
  apply one_le_rpow_of_pos_of_le_one_of_nonpos
  · exact_mod_cast hδ0
  · exact_mod_cast hδ1
  · rw [neg_nonpos]
    positivity

/-- Hence so is the combined loss. -/
theorem one_le_totalLoss (A : NNReal) (hA : 1 ≤ A) (K c : ℕ) {δ : NNReal} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) : 1 ≤ totalLoss A K c δ := by
  rw [totalLoss, ENNReal.one_le_ofReal]
  exact one_le_mul_of_one_le_of_one_le (one_le_gridLoss A hA K hδ1) (one_le_scaleGapLoss c hδ0 hδ1)

/-- The loss is monotone in both of its `δ`-independent parameters, which is what lets several
sources of loss be compared against a single common one. -/
theorem gridLoss_mono {A A' : NNReal} (hA : 1 ≤ A) (hAA' : A ≤ A') {K K' : ℕ} (hKK' : K ≤ K')
    {δ : NNReal} (hδ1 : δ ≤ 1) :
    gridLoss A K δ ≤ gridLoss A' K' δ := by
  let M := ssfGridLen δ
  unfold gridLoss
  have hlog : Real.log (δ : ℝ) ≤ 0 := by
    exact Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
  have hbase : 1 ≤ 1 - Real.log (δ : ℝ) := by
    linarith
  have hpowA : (A : ℝ) ^ (M + 1) ≤ (A' : ℝ) ^ (M + 1) := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hAA') (M + 1)
  have hKM : K * (M + 1) ^ 2 ≤ K' * (M + 1) ^ 2 := by
    exact Nat.mul_le_mul_right ((M + 1) ^ 2) hKK'
  have hpow2 : (1 - Real.log (δ : ℝ)) ^ (K * (M + 1) ^ 2) ≤
      (1 - Real.log (δ : ℝ)) ^ (K' * (M + 1) ^ 2) := by
    exact pow_le_pow_right₀ hbase hKM
  exact mul_le_mul hpowA hpow2 (by exact pow_nonneg (zero_le_one.trans hbase) _) (by positivity)

/-- **The loss is multiplicative in its parameters.**  Two independent sources of per-level loss
combine into one, at the product of the bases and the sum of the polylogarithmic exponents.  This is
what `gridLoss_mono` cannot do: monotonicity compares one loss with another, whereas what arises in
practice is a *product* of two.  The intended idiom is to multiply here and only then raise the
resulting pair to a common one by `gridLoss_mono`. -/
theorem gridLoss_mul (A A' : NNReal) (K K' : ℕ) (δ : NNReal) :
    gridLoss A K δ * gridLoss A' K' δ = gridLoss (A * A') (K + K') δ := by
  unfold gridLoss
  push_cast
  rw [mul_pow, add_mul, pow_add]
  ring

/-- **A cube of a logarithm is eventually dominated by a linear function.**

This is the analytic input behind the subpolynomiality of `gridLoss`.  The grid length is
`⌈log log 1/δ⌉`, so with `L = log 1/δ` the exponent `K (ssfGridLen δ + 1)^2` contributes a *cube* of
`log L` to the logarithm of the loss, to be compared with the linear `α L` on the other side.  An
absorption linear in the grid length would not be strong enough. -/
private theorem exists_threshold_logCube_le {c : ℝ} (hc : 0 < c) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → (Real.log L + 2) ^ 3 ≤ c * L := by
  have hlog3 : (fun L : ℝ => (Real.log L) ^ 3) =o[Filter.atTop] (fun L : ℝ => L) :=
    Real.isLittleO_pow_log_id_atTop (n := 3)
  have hc8 : (0 : ℝ) < c / 8 := by positivity
  have h1le_exp2 : (1 : ℝ) ≤ Real.exp (2 : ℝ) := by
    have h := Real.exp_monotone (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    rwa [Real.exp_zero] at h
  have hev : ∀ᶠ L in Filter.atTop,
      Real.exp (2 : ℝ) ≤ L ∧ (Real.log L) ^ 3 ≤ (c / 8) * L := by
    have h := Asymptotics.isLittleO_iff.mp hlog3 hc8
    filter_upwards [h, Filter.eventually_ge_atTop (Real.exp (2 : ℝ))] with L hb hLge
    have hLnn : 0 ≤ L := (Real.exp_pos (2 : ℝ)).le.trans hLge
    have hL1 : (1 : ℝ) ≤ L := h1le_exp2.trans hLge
    have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hfn : 0 ≤ (Real.log L) ^ 3 := pow_nonneg hlogL_nonneg 3
    rw [Real.norm_eq_abs, abs_of_nonneg hfn, Real.norm_eq_abs, abs_of_nonneg hLnn] at hb
    exact ⟨hLge, hb⟩
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ, ∀ L : ℝ, L₁ ≤ L →
      Real.exp (2 : ℝ) ≤ L ∧ (Real.log L) ^ 3 ≤ (c / 8) * L := by
    rcases Filter.eventually_atTop.mp hev with ⟨L₁, hL₁_all⟩
    exact ⟨L₁, hL₁_all⟩
  refine ⟨max 2 (max (Real.exp (2 : ℝ)) L₁), le_max_left 2 (max (Real.exp (2 : ℝ)) L₁), ?_⟩
  intro L hL
  have hmid : max (Real.exp (2 : ℝ)) L₁ ≤ max 2 (max (Real.exp (2 : ℝ)) L₁) :=
    le_max_right 2 (max (Real.exp (2 : ℝ)) L₁)
  have hLgeExp : Real.exp (2 : ℝ) ≤ L :=
    (le_max_left (Real.exp (2 : ℝ)) L₁).trans (hmid.trans hL)
  have hLgeL₁ : L₁ ≤ L :=
    (le_max_right (Real.exp (2 : ℝ)) L₁).trans (hmid.trans hL)
  have hLge2 : 2 ≤ L := (le_max_left 2 (max (Real.exp (2 : ℝ)) L₁)).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLge2
  have hL₁bundle := hL₁ L hLgeL₁
  have hlogcube : (Real.log L) ^ 3 ≤ (c / 8) * L := hL₁bundle.2
  have h2le_logL : 2 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).mpr hLgeExp
  have hcube : (Real.log L + 2) ^ 3 ≤ (2 * Real.log L) ^ 3 := by
    exact pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hmain : 8 * (Real.log L) ^ 3 ≤ c * L := by
    have hstep : 8 * (Real.log L) ^ 3 ≤ 8 * ((c / 8) * L) :=
      mul_le_mul_of_nonneg_left hlogcube (by norm_num : (0 : ℝ) ≤ 8)
    have hcancel : 8 * ((c / 8) * L) = c * L := by
      calc
        8 * ((c / 8) * L) = (c / 8 * 8) * L := by ring
        _ = c * L := by rw [div_mul_cancel₀ c (by norm_num : (8 : ℝ) ≠ 0)]
    rwa [hcancel] at hstep
  calc
    (Real.log L + 2) ^ 3 ≤ (2 * Real.log L) ^ 3 := hcube
    _ = 8 * (Real.log L) ^ 3 := by ring
    _ ≤ c * L := hmain

/-- **The loss is subpolynomial.**  Below a threshold depending only on `(A, K, α)` it is at most
`δ^{-α}`.  This is the form in which a consumer absorbs it.

With the exponent quadratic in the grid length, the logarithm of the loss is a *cube* of
`log log 1/δ`, so the absorption is `exists_threshold_logCube_le`. -/
theorem exists_threshold_gridLoss_le (A : NNReal) (hA : 1 ≤ A) (K : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → gridLoss A K δ ≤ (δ : ℝ) ^ (-α) := by
  have hARpos : (0 : ℝ) < (A : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hA)
  have hlogA_nonneg : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  set D : ℝ := Real.log (A : ℝ) + (K : ℝ) + 1 with hD_def
  have hDpos : 0 < D := by
    rw [hD_def]
    have hKnn : 0 ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
    linarith
  obtain ⟨L₀, hL₀ge2, hCube⟩ := exists_threshold_logCube_le (c := α / D) (div_pos hα hDpos)
  set δ₀ : NNReal := Real.toNNReal (Real.exp (-L₀)) with hδ₀_def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀_def]
    exact Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hδ₀le1 : δ₀ ≤ 1 := by
    have h : (δ₀ : ℝ) ≤ 1 := by
      rw [hδ₀_def]
      rw [Real.coe_toNNReal (Real.exp (-L₀)) (Real.exp_nonneg _)]
      exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (le_trans (by norm_num : (0 : ℝ) ≤ 2) hL₀ge2))
    exact NNReal.coe_le_coe.mp h
  refine ⟨δ₀, hδ₀pos, hδ₀le1, ?_⟩
  intro δ hδpos hδle
  set L : ℝ := -Real.log (δ : ℝ) with hL_def
  set M : ℕ := ssfGridLen δ with hM_def
  set Y : ℝ := Real.log L + 2 with hY_def
  have hδRpos : 0 < (δ : ℝ) := by exact_mod_cast hδpos
  have hδleexp : (δ : ℝ) ≤ Real.exp (-L₀) := by
    have h1 : (δ : ℝ) ≤ (δ₀ : ℝ) := NNReal.coe_le_coe.mp hδle
    have hδ₀val : (δ₀ : ℝ) = Real.exp (-L₀) := by
      rw [hδ₀_def]
      exact Real.coe_toNNReal (Real.exp (-L₀)) (Real.exp_nonneg _)
    rwa [hδ₀val] at h1
  have hlogδle : Real.log (δ : ℝ) ≤ -L₀ := by
    have h := Real.log_le_log hδRpos hδleexp
    rwa [Real.log_exp] at h
  have hL₀leL : L₀ ≤ L := by
    rw [hL_def]
    linarith
  have hLge2 : 2 ≤ L := le_trans hL₀ge2 hL₀leL
  have hLge1 : 1 ≤ L := le_trans (by norm_num : (1 : ℝ) ≤ 2) hLge2
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLge2
  have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hLge1
  have hMval : M = ⌈Real.log L⌉₊ := by
    rw [hM_def, ssfGridLen]
    apply congrArg Nat.ceil
    apply congrArg Real.log
    rw [hL_def, one_div]
    exact Real.log_inv (δ : ℝ)
  have hM1nonneg : 0 ≤ (M : ℝ) + 1 := by positivity
  have hM1leY : (M : ℝ) + 1 ≤ Y := by
    have hMle : (M : ℝ) ≤ Real.log L + 1 := by
      rw [hMval]
      have hceil : ((⌈Real.log L⌉₊ : ℕ) : ℝ) ≤ (⌊Real.log L⌋₊ : ℝ) + 1 := by
        exact_mod_cast (Nat.ceil_le_floor_add_one (Real.log L))
      have hfloor : (⌊Real.log L⌋₊ : ℝ) ≤ Real.log L :=
        Nat.floor_le hlogL_nonneg
      linarith
    rw [hY_def]
    linarith
  have hYge2 : 2 ≤ Y := by
    rw [hY_def]
    linarith
  have hYge1 : 1 ≤ Y := le_trans (by norm_num : (1 : ℝ) ≤ 2) hYge2
  have hY3nonneg : 0 ≤ Y ^ 3 := by positivity
  have hYleY3 : Y ≤ Y ^ 3 := by
    have hYsq : 1 ≤ Y ^ 2 := one_le_pow₀ hYge1
    have hYnonneg : 0 ≤ Y := by linarith
    calc
      Y = Y * 1 := by rw [mul_one]
      _ ≤ Y * Y ^ 2 := mul_le_mul_of_nonneg_left hYsq hYnonneg
      _ = Y ^ 3 := by ring
  have hlog1pL_nonneg : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
  have hlog1pL_le_Y : Real.log (1 + L) ≤ Y := by
    have hle : 1 + L ≤ 2 * L := by nlinarith
    have h₁ : Real.log (1 + L) ≤ Real.log (2 * L) := by
      exact Real.log_le_log (by linarith) hle
    have h₂ : Real.log (2 * L) = Real.log 2 + Real.log L := by
      exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hLpos)
    have h₃ : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h₄ : Real.log (1 + L) ≤ Real.log L + 1 := by
      calc
        Real.log (1 + L) ≤ Real.log (2 * L) := h₁
        _ = Real.log 2 + Real.log L := h₂
        _ ≤ Real.log L + 1 := by nlinarith
    rw [hY_def]
    linarith
  have hbase_eq : 1 - Real.log (δ : ℝ) = 1 + L := by
    rw [hL_def]
    ring
  have hGLpos : 0 < gridLoss A K δ := by
    unfold gridLoss
    have hbase_pos : 0 < 1 - Real.log (δ : ℝ) := by
      rw [hbase_eq]
      linarith
    exact mul_pos (pow_pos hARpos (ssfGridLen δ + 1))
      (pow_pos hbase_pos (K * (ssfGridLen δ + 1) ^ 2))
  have hlogGL' : Real.log (gridLoss A K δ) =
      ((M : ℝ) + 1) * Real.log (A : ℝ) + (K : ℝ) * ((M : ℝ) + 1) ^ 2 * Real.log (1 + L) := by
    unfold gridLoss
    rw [← hM_def]
    have h1pLpos : 0 < 1 + L := by linarith
    rw [hbase_eq]
    rw [Real.log_mul (ne_of_gt (pow_pos hARpos (M + 1)))
        (ne_of_gt (pow_pos h1pLpos (K * (M + 1) ^ 2)))]
    rw [Real.log_pow, Real.log_pow]
    norm_cast
  have hKnonneg : 0 ≤ (K : ℝ) := by exact_mod_cast (Nat.zero_le K)
  have hlogL : Real.log (gridLoss A K δ) ≤ α * L := by
    rw [hlogGL']
    have hX2leY2 : ((M : ℝ) + 1) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hM1nonneg hM1leY 2
    have hY2nonneg : 0 ≤ Y ^ 2 := sq_nonneg Y
    have hTerm1 : ((M : ℝ) + 1) * Real.log (A : ℝ) ≤ Y * Real.log (A : ℝ) :=
      mul_le_mul_of_nonneg_right hM1leY hlogA_nonneg
    have hTerm1' : Y * Real.log (A : ℝ) ≤ Y ^ 3 * Real.log (A : ℝ) :=
      mul_le_mul_of_nonneg_right hYleY3 hlogA_nonneg
    have hX2log : ((M : ℝ) + 1) ^ 2 * Real.log (1 + L) ≤ Y ^ 2 * Y := by
      have h₁ : ((M : ℝ) + 1) ^ 2 * Real.log (1 + L) ≤ Y ^ 2 * Real.log (1 + L) :=
        mul_le_mul_of_nonneg_right hX2leY2 hlog1pL_nonneg
      have h₂ : Y ^ 2 * Real.log (1 + L) ≤ Y ^ 2 * Y :=
        mul_le_mul_of_nonneg_left hlog1pL_le_Y hY2nonneg
      exact le_trans h₁ h₂
    have hY3_le : Y ^ 3 ≤ (α / D) * L := by
      rw [hY_def]
      exact hCube L hL₀leL
    have hY3D : Y ^ 3 * D ≤ α * L := by
      have h₁ : Y ^ 3 * D ≤ (α / D) * L * D := mul_le_mul_of_nonneg_right hY3_le hDpos.le
      have h₂ : (α / D) * L * D = α * L := by
        field_simp [ne_of_gt hDpos]
      rwa [h₂] at h₁
    calc
      ((M : ℝ) + 1) * Real.log (A : ℝ) + (K : ℝ) * ((M : ℝ) + 1) ^ 2 * Real.log (1 + L)
          ≤ Y * Real.log (A : ℝ) + (K : ℝ) * (Y ^ 2 * Y) := by
            nlinarith [hTerm1, hX2log, hKnonneg]
      _ ≤ Y * Real.log (A : ℝ) + (K : ℝ) * Y ^ 3 := by nlinarith
      _ ≤ Y ^ 3 * Real.log (A : ℝ) + Y ^ 3 * (K : ℝ) := by
            have hKcomm : (K : ℝ) * Y ^ 3 = Y ^ 3 * (K : ℝ) := by ring
            rw [hKcomm]
            exact add_le_add hTerm1' (le_rfl : Y ^ 3 * (K : ℝ) ≤ Y ^ 3 * (K : ℝ))
      _ ≤ Y ^ 3 * D := by
            rw [hD_def]
            calc
              Y ^ 3 * Real.log (A : ℝ) + Y ^ 3 * (K : ℝ)
                  = Y ^ 3 * (Real.log (A : ℝ) + (K : ℝ)) := by ring
              _ ≤ Y ^ 3 * (Real.log (A : ℝ) + (K : ℝ) + 1) := by
                    exact mul_le_mul_of_nonneg_left (by linarith) hY3nonneg
      _ ≤ α * L := hY3D
  have hrpow_log : Real.log ((δ : ℝ) ^ (-α)) = α * L := by
    rw [Real.log_rpow hδRpos (-α)]
    rw [hL_def]
    ring
  have hlog_comp : Real.log (gridLoss A K δ) ≤ Real.log ((δ : ℝ) ^ (-α)) := by
    rw [hrpow_log]
    exact hlogL
  exact (Real.log_le_log_iff hGLpos (Real.rpow_pos_of_pos hδRpos (-α))).mp hlog_comp

/-- **The gap loss is subpolynomial**, because `c / ⌈log log 1/δ⌉ → 0`.  This is the form in which
alternative (i)'s error `δ^{-5ε}` absorbs a transport across a grid gap. -/
theorem exists_threshold_scaleGapLoss_le (c : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → scaleGapLoss c δ ≤ (δ : ℝ) ^ (-α) := by
  set n : ℕ := ⌈(c : ℝ) / α⌉₊ + 1 with hn_def
  have hc_le_n : (c : ℝ) / α ≤ (n : ℝ) := by
    rw [hn_def]
    have h1 : (c : ℝ) / α ≤ (⌈(c : ℝ) / α⌉₊ : ℝ) := Nat.le_ceil ((c : ℝ) / α)
    have h2 : (⌈(c : ℝ) / α⌉₊ : ℝ) ≤ (((⌈(c : ℝ) / α⌉₊ : ℕ) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_succ (⌈(c : ℝ) / α⌉₊))
    exact le_trans h1 h2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    rw [hn_def]
    exact_mod_cast (Nat.succ_pos (⌈(c : ℝ) / α⌉₊))
  refine ⟨Real.toNNReal (Real.exp (-(Real.exp (n : ℝ)))), ?_, ?_, ?_⟩
  · exact Real.toNNReal_pos.mpr (Real.exp_pos _)
  · have h : (Real.toNNReal (Real.exp (-(Real.exp (n : ℝ)))) : ℝ) ≤ 1 := by
      rw [Real.coe_toNNReal (Real.exp (-(Real.exp (n : ℝ)))) (Real.exp_nonneg _)]
      exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (Real.exp_nonneg (n : ℝ)))
    exact NNReal.coe_le_coe.mp h
  · intro δ hδpos hδle
    set L : ℝ := Real.log (1 / (δ : ℝ)) with hL_def
    set M : ℕ := ssfGridLen δ with hM_def
    have hδRpos : 0 < (δ : ℝ) := by exact_mod_cast hδpos
    have hδleexp : (δ : ℝ) ≤ Real.exp (-(Real.exp (n : ℝ))) := by
      have h1 : (δ : ℝ) ≤ ((Real.toNNReal (Real.exp (-(Real.exp (n : ℝ)))) : NNReal) : ℝ) :=
        NNReal.coe_le_coe.mp hδle
      have hδ₀val : ((Real.toNNReal (Real.exp (-(Real.exp (n : ℝ)))) : NNReal) : ℝ) =
          Real.exp (-(Real.exp (n : ℝ))) := by
        exact Real.coe_toNNReal (Real.exp (-(Real.exp (n : ℝ)))) (Real.exp_nonneg _)
      rwa [hδ₀val] at h1
    have hδle1 : (δ : ℝ) ≤ 1 := by
      exact le_trans hδleexp (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg (n : ℝ))))
    have hlogδ : Real.log (δ : ℝ) ≤ -(Real.exp (n : ℝ)) := by
      have h := Real.log_le_log hδRpos hδleexp
      rwa [Real.log_exp] at h
    have hL : L = -Real.log (δ : ℝ) := by
      rw [hL_def, one_div]
      exact Real.log_inv (δ : ℝ)
    have hLge : Real.exp (n : ℝ) ≤ L := by
      rw [hL]
      linarith
    have hLpos : 0 < L := by
      have h := Real.exp_pos (n : ℝ)
      linarith
    have hn_le_logL : (n : ℝ) ≤ Real.log L := by
      have h := Real.log_le_log (Real.exp_pos (n : ℝ)) hLge
      rwa [Real.log_exp] at h
    have hMge : (n : ℝ) ≤ (M : ℝ) := by
      rw [hM_def, ssfGridLen, ← hL_def]
      exact le_trans hn_le_logL (Nat.le_ceil (Real.log L))
    have hMpos : 0 < (M : ℝ) := by
      have h1 : (1 : ℝ) ≤ (M : ℝ) := le_trans hn1 hMge
      linarith
    have hcM_le_α : (c : ℝ) / (M : ℝ) ≤ α := by
      rw [div_le_iff₀ hMpos]
      have hαM : α * (n : ℝ) ≤ α * (M : ℝ) :=
        mul_le_mul_of_nonneg_left hMge hα.le
      have hαn : α * ((c : ℝ) / α) ≤ α * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hc_le_n hα.le
      have hcancel : α * ((c : ℝ) / α) = (c : ℝ) := by
        rw [mul_comm, div_mul_cancel₀ (c : ℝ) (ne_of_gt hα)]
      nlinarith
    rw [scaleGapLoss, hM_def.symm]
    exact Real.rpow_le_rpow_of_exponent_ge hδRpos hδle1 (by linarith)

/-- **The combined loss is subpolynomial.**  Each factor is absorbed at `α / 2`. -/
theorem exists_threshold_totalLoss_le (A : NNReal) (hA : 1 ≤ A) (K c : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        totalLoss A K c δ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-α)) := by
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, h₁⟩ := exists_threshold_gridLoss_le A hA K (α / 2) (by linarith)
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, h₂⟩ := exists_threshold_scaleGapLoss_le c (α / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, (min_le_left _ _).trans hδ₁le1, ?_⟩
  intro δ hδpos hδle
  have hδle₁ : δ ≤ δ₁ := hδle.trans (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := hδle.trans (min_le_right _ _)
  have hδle1 : δ ≤ 1 := hδle₁.trans hδ₁le1
  have hδR : (0 : ℝ) < (δ : ℝ) := by
    exact_mod_cast hδpos
  have hg : gridLoss A K δ ≤ (δ : ℝ) ^ (-(α / 2)) := by
    exact h₁ hδpos hδle₁
  have hs : scaleGapLoss c δ ≤ (δ : ℝ) ^ (-(α / 2)) := by
    exact h₂ hδpos hδle₂
  have hsnn : 0 ≤ scaleGapLoss c δ := by
    have h := one_le_scaleGapLoss c hδpos hδle1
    linarith
  have hrnn : 0 ≤ (δ : ℝ) ^ (-(α / 2)) := by
    exact (Real.rpow_pos_of_pos hδR _).le
  have hreal : gridLoss A K δ * scaleGapLoss c δ ≤ (δ : ℝ) ^ (-α) := by
    calc
      gridLoss A K δ * scaleGapLoss c δ
          ≤ (δ : ℝ) ^ (-(α / 2)) * (δ : ℝ) ^ (-(α / 2)) := by
            exact mul_le_mul hg hs hsnn hrnn
        _ = (δ : ℝ) ^ (-(α / 2) + -(α / 2)) := by
            exact (Real.rpow_add hδR _ _).symm
        _ = (δ : ℝ) ^ (-α) := by
            congr 1
            ring
  rw [totalLoss]
  exact ENNReal.ofReal_le_ofReal hreal

end StickyKakeya
