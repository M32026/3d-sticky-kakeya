/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes

/-!
# The affine squeeze: `Kakeya.ML2Assembly.SmallCard`'s band is affinely vacuous

**VERDICT: the band restriction `|𝕋| < δ^{-1}` of `Kakeya.ML2Assembly.SmallCard` carries the
whole weight of the partial Katz--Tao estimate at the same exponent.**  The headline is

```
Kakeya.ML2BandSqz.smallCard_iff_katzTaoEstimate :
  0 ≤ γ → (Kakeya.ML2Assembly.SmallCard γ ↔ Kakeya.KatzTaoEstimate Space3 γ)
```

Consequently `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` — and hence
`Assembly.lean`'s `katzTaoEstimate_sub_of_frostmanEstimate_of_lemma91` — follows from its
`hsmall` slot **alone**: the dichotomy `hdich`, the gain budget `4c ≤ g`, the accuracy budget
`2c ≤ β`, GWZ Lemma 9.1 and the whole geometric core are unused.  This is
`Kakeya.ML2BandSqz.katzTaoEstimate_sub_of_smallCard_alone`, and the `example` beside it exhibits
the unused hypotheses in scope.  **The reduction as currently cut is circular.**

## The mechanism

`δ` is an *eccentricity* — thickness over length — and eccentricity is not affine invariant,
whereas `|𝕋|`, `Δ_max`, `λ` and the mass ratio all are (up to absolute constants).  The band
compares an affine invariant to a non-invariant, so it cannot be a real restriction.

Concretely: given a family of `ρ`-tubes in `B₁`, partition the index set by which of the three
coordinate directions the tube axis is closest to (`Kakeya.ML2BandSqz.exists_coord_abs_ge`:
every unit vector of `ℝ³` has `|u_k| ≥ 1/√3 > 1/2` for some `k`), keep the cap carrying the most
shaded mass (`Kakeya.ML2BandSqz.exists_max_fibre`, cost `3`), and apply

```
A = (1/4) · (identity along e_k, multiplication by σ on e_k^⊥),   σ = ρ^{1+2η}
```

(`Kakeya.ML2BandSqz.sqz`).  Then

| quantity | transport | loss |
|---|---|---|
| the image of a `ρ`-tube | `image_subset_centredExtension` | it is an honest `σρ`-tube |
| `∑\|Y\|` and `\|⋃ Y\|` | `mass_le_of_sqzFamily` | **none** (a ratio of volumes) |
| `\|𝕋\|` | the index set is unchanged | **none** |
| `Δ_max` | `sqzFamily_maxDensity_le` | `sqzLoss`, an absolute constant |
| `λ` | `sqzFamily_le_fullness` | `sqzLoss`, an absolute constant |
| `B₁` containment | `sqzFamily_carrier_subset_closedBall` | none (this is what the `1/4` buys) |

and the band threshold at the new scale is `δ^{-1} = ρ^{-2-2η}`, whereas the Katz--Tao
hypothesis caps `|𝕋| ≲ ρ^{-2-η}` (`Tube.card_le_of_densityIn_le`).  The image therefore lands
**strictly inside** the band, with `ρ^{-η}` to spare, and the conclusion pulls back exactly, at
the accuracy `ε/8` instead of `ε`.  Every constant is absolute and absorbed by
`Kakeya.ML2BandSqz.eventually_const_le_rpow`.

The `1/4` is what keeps the outer tube inside `B₁`: the image of `B₁` lies in `B_{1/4}`
(`norm_sqz_le`), and `Tube.centredExtension` extends the shortened image core back to unit
length inside `B_{3/4}`.  The transversality `|⟪e,u⟫| ≥ 1/2` is what keeps the image a *tube*:
the long axis `ρ` of the image ellipsoid then points essentially *along* the image axis, so the
transverse extent is `O(σρ)` and not `ρ` (`norm_sqzL_sub_proj_le`, the geometric heart).

## The asymmetry — the neighbouring threshold is NOT touched

The squeeze only ever *lowers* the scale, hence only ever *raises* the threshold `δ^{-1}`
(`Kakeya.ML2BandSqz.sqz_preserves_band`).  The reverse presentation — a `ρ`-tube family at a
coarser scale `δ' > ρ` — costs `(δ'/ρ)²` in `Δ_max` and `(ρ/δ')²` in fullness
(`Kakeya.ML2BandSqz.volume_coarser_ge`), and to move a threshold at all `δ'/ρ` must be a *power*
of `ρ`, so the loss is a power of `ρ` and no threshold absorbs it
(`Kakeya.ML2BandSqz.not_reverseSqueezeBudget`).  So `Kakeya.ML2Assembly.Dichotomy`'s conjunct
`δ⁻¹ ≤ |𝕋|` — Prof. Wang's `|𝕋| > δ^{-1}` — is a genuine hypothesis and is untouched by this
mechanism.

## The repair question, and its answer

`GWZAdapted/section9.tex`'s proof of Main Lemma 2 carries **no cardinality hypothesis at all**:
its branch (i) reads Theorem 7.3(B) at the *outer* `ε`, gets `μ ≤ δ^{-ε}` and closes because
`|𝕋|^{β-ν} ≥ 1`.  The condition `δ⁻¹ ≤ |𝕋|` is the price of the `ε`-free repair — reading
7.3(B) at an **absolute** `ε₀` — and it is charged in an affinely meaningless currency.

*What must `SmallCard` carry so that the squeeze cannot run?*  The answer is a dichotomy, and it
is the content of `Kakeya.ML2BandSqz.katzTaoEstimate_of_smallCardWith`:

> **No clause the case split can supply blocks the squeeze.**

The small-cardinality branch of `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` has exactly
four facts about the family — unit-ball containment, `Δ_max ≤ δ^{-η}`, `λ ≥ δ^η`, `|𝕋| < δ^{-1}`
— and the squeezed family satisfies all four.  So any clause implied by them
(`Kakeya.ML2BandSqz.CallSiteAvailable`) is inherited by the squeezed family, and
`SmallCardWith P γ → K_KT γ` survives.  Contrapositively, **a clause that blocks the squeeze is
a clause the branch cannot hand over.**

`Kakeya.ML2BandSqz.DirNonConcentrated` — the directions are not all in one `1/2`-cap, the formal
shadow of GWZ's "bilinear"/broad hypothesis — inhabits the blocking horn
(`sqzFamily_not_dirNonConcentrated`) and, as the calculus forces, fails the availability test
(`not_callSiteAvailable_dirNonConcentrated`, witnessed by a single fully shaded `δ`-tube).
Both halves are `Kakeya.ML2BandSqz.repair_blocks_but_is_unavailable`.

*Caveat, stated so it is not mistaken for more than it is.*  The blocking half is proved for the
single-frame squeeze of this file.  A three-frame variant — squeeze each coordinate cap with its
own map and take the union — also transports the mass (the three Jacobians are equal, and the
union of the three images has volume at most `3` times the transported union), so a clause with
a threshold weaker than `1/√3` would not survive it.  The `1/2` threshold does, but that is
luck, not structure.  **The load-bearing result is the calculus theorem, which is independent of
which clause is proposed.**
-/

@[expose] public section

open MeasureTheory Metric Set Topology Filter ShadedBody ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2BandSqz

universe u

/-! ## The squeeze map, as a linear map -/

section Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `sqzL e a c` is `a` times the anisotropic dilation which is the identity along `e` and
multiplication by `c` on `e^⊥`. -/
noncomputable def sqzL (e : E) (a c : ℝ) : E →L[ℝ] E :=
  (a * c) • ContinuousLinearMap.id ℝ E + (a * (1 - c)) • (innerSL ℝ e).smulRight e

theorem sqzL_apply (e : E) (a c : ℝ) (z : E) :
    sqzL e a c z = (a * c) • z + (a * (1 - c)) • (inner ℝ e z • e) := rfl

/-- The eigen-decomposition form: `a c` on `e^⊥` and `a` on `ℝ ∙ e`. -/
theorem sqzL_split (e : E) (a c : ℝ) (z : E) :
    sqzL e a c z = (a * c) • (z - (inner ℝ e z : ℝ) • e) + a • ((inner ℝ e z : ℝ) • e) := by
  rw [sqzL_apply]; module

theorem sqzL_comp (e : E) (he : ‖e‖ = 1) (a c a' c' : ℝ) (z : E) :
    sqzL e a c (sqzL e a' c' z) = sqzL e (a * a') (c * c') z := by
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [sqzL_apply, inner_add_right, inner_smul_right, hee]
  module

theorem sqzL_one (e : E) : sqzL e 1 1 = ContinuousLinearMap.id ℝ E := by
  ext z; simp [sqzL_apply]

/-- `‖sqzL e a c z‖² = (ac)²‖z^⊥‖² + a²⟪e,z⟫²`. -/
theorem norm_sq_sqzL (e : E) (he : ‖e‖ = 1) (a c : ℝ) (z : E) :
    ‖sqzL e a c z‖ ^ 2
      = (a * c) ^ 2 * ‖z - (inner ℝ e z : ℝ) • e‖ ^ 2 + a ^ 2 * (inner ℝ e z : ℝ) ^ 2 := by
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hwe : (inner ℝ (z - (inner ℝ e z : ℝ) • e) e : ℝ) = 0 := by
    rw [inner_sub_left, real_inner_smul_left, hee, real_inner_comm z e]
    ring
  have horth : (inner ℝ ((a * c) • (z - (inner ℝ e z : ℝ) • e))
      (a • ((inner ℝ e z : ℝ) • e)) : ℝ) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, hwe]
    ring
  rw [sqzL_split e a c z, norm_add_sq_real, horth, norm_smul, norm_smul, norm_smul, he]
  simp only [Real.norm_eq_abs, mul_one]
  rw [mul_pow, mul_pow, sq_abs, sq_abs, sq_abs]
  ring

/-- The orthogonal splitting of a norm along `e`. -/
theorem norm_sq_split (e : E) (he : ‖e‖ = 1) (z : E) :
    ‖z‖ ^ 2 = ‖z - (inner ℝ e z : ℝ) • e‖ ^ 2 + (inner ℝ e z : ℝ) ^ 2 := by
  have h := norm_sq_sqzL e he 1 1 z
  rw [sqzL_one e] at h
  simpa using h

/-- The squeeze with `|a| ≤ 1` and `|c| ≤ 1` is a contraction. -/
theorem norm_sqzL_le (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : |a| ≤ 1) (hc : |c| ≤ 1) (z : E) :
    ‖sqzL e a c z‖ ≤ ‖z‖ := by
  have h1 := norm_sq_sqzL e he a c z
  have h2 := norm_sq_split e he z
  set W : ℝ := ‖z - (inner ℝ e z : ℝ) • e‖ with hW
  set A : ℝ := (inner ℝ e z : ℝ) with hA
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have hac2 : (a * c) ^ 2 ≤ 1 := by
    have h : |a * c| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg c]
    nlinarith [abs_nonneg (a * c), sq_abs (a * c)]
  have hkey : ‖sqzL e a c z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h1, h2]
    have t1 : (a * c) ^ 2 * W ^ 2 ≤ 1 * W ^ 2 := mul_le_mul_of_nonneg_right hac2 (sq_nonneg W)
    have t2 : a ^ 2 * A ^ 2 ≤ 1 * A ^ 2 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg A)
    linarith
  nlinarith [hkey, norm_nonneg (sqzL e a c z), norm_nonneg z]

/-- The squeeze with `0 < c ≤ 1` and `0 < a` shrinks by at most the factor `a c`. -/
theorem le_norm_sqzL (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1)
    (z : E) : a * c * ‖z‖ ≤ ‖sqzL e a c z‖ := by
  have h1 := norm_sq_sqzL e he a c z
  have h2 := norm_sq_split e he z
  set W : ℝ := ‖z - (inner ℝ e z : ℝ) • e‖ with hW
  set A : ℝ := (inner ℝ e z : ℝ) with hA
  have hkey : (a * c * ‖z‖) ^ 2 ≤ ‖sqzL e a c z‖ ^ 2 := by
    rw [h1]
    have e1 : (a * c * ‖z‖) ^ 2 = (a * c) ^ 2 * W ^ 2 + a ^ 2 * c ^ 2 * A ^ 2 := by
      linear_combination (a ^ 2 * c ^ 2) * h2
    rw [e1]
    have hstep : 0 ≤ a ^ 2 * A ^ 2 * (1 - c ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg A)) (by nlinarith)
    nlinarith [hstep]
  nlinarith [hkey, norm_nonneg (sqzL e a c z), norm_nonneg z, mul_pos ha hc]

variable [FiniteDimensional ℝ E]

/-- **The determinant of the unscaled squeeze is `c^{n-1}`.**  The map is the identity on the
line `ℝ ∙ e` and the dilation by `c` on the `(n-1)`-dimensional quotient. -/
theorem det_sqzL_one (e : E) (he : ‖e‖ = 1) (c : ℝ) :
    LinearMap.det (sqzL e 1 c : E →ₗ[ℝ] E) = c ^ (Module.finrank ℝ E - 1) := by
  have hLapply : ∀ v : E, (sqzL e 1 c : E →ₗ[ℝ] E) v
      = c • v + (1 - c) • ((inner ℝ e v : ℝ) • e) := by
    intro v; simpa [one_mul] using sqzL_apply e 1 c v
  set Lm : E →ₗ[ℝ] E := (sqzL e 1 c : E →ₗ[ℝ] E) with hLmdef
  have hne : e ≠ 0 := by
    intro h; rw [h, norm_zero] at he; exact absurd he (by norm_num)
  have hmem : e ∈ (ℝ ∙ e : Submodule ℝ E) := Submodule.mem_span_singleton_self _
  have hLdir : Lm e = e := by
    rw [hLapply, real_inner_self_eq_norm_sq, he, one_pow, one_smul, ← add_smul,
      add_sub_cancel, one_smul]
  have hle : (ℝ ∙ e : Submodule ℝ E) ≤ (ℝ ∙ e).comap Lm := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hLdir]
    exact hmem
  have hrestrict : Lm.restrict hle = LinearMap.id := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp w.2
    simp only [LinearMap.restrict_apply, LinearMap.id_coe, id_eq, ← ht, map_smul, hLdir]
  have hmapQ : (ℝ ∙ e).mapQ (ℝ ∙ e) Lm hle = c • LinearMap.id := by
    refine LinearMap.ext fun q => Submodule.Quotient.induction_on _ q fun v => ?_
    rw [Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      show Lm v - c • v = (1 - c) • ((inner ℝ e v : ℝ) • e) from by
        rw [hLapply, add_sub_cancel_left]]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hmem)
  rw [LinearMap.det_eq_det_mul_det (ℝ ∙ e) Lm hle, hrestrict, LinearMap.det_id,
    one_mul, hmapQ, LinearMap.det_smul, LinearMap.det_id, mul_one]
  congr 1
  have hfin := Submodule.finrank_quotient_add_finrank (R := ℝ) (M := E) (ℝ ∙ e)
  rw [finrank_span_singleton hne] at hfin
  omega

/-- **The determinant of the squeeze is `a^n c^{n-1}`.** -/
theorem det_sqzL (e : E) (he : ‖e‖ = 1) (a c : ℝ) :
    LinearMap.det (sqzL e a c : E →ₗ[ℝ] E)
      = a ^ Module.finrank ℝ E * c ^ (Module.finrank ℝ E - 1) := by
  have h : ((sqzL e a c : E →L[ℝ] E) : E →ₗ[ℝ] E)
      = a • ((sqzL e 1 c : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, sqzL_apply, one_mul]
    module
  rw [h, LinearMap.det_smul, det_sqzL_one e he c]

end Linear


/-! ## The squeeze as an affine equivalence -/

section Equiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The squeeze as a continuous linear equivalence; the inverse is the squeeze with the
reciprocal parameters (`Kakeya.ML2BandSqz.sqzL_comp`). -/
noncomputable def sqzLE (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    E ≃L[ℝ] E where
  toLinearEquiv := LinearEquiv.ofLinear (sqzL e a c : E →ₗ[ℝ] E) (sqzL e a⁻¹ c⁻¹ : E →ₗ[ℝ] E)
    (by
      refine LinearMap.ext fun z => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        LinearMap.id_coe, id_eq]
      rw [sqzL_comp e he, mul_inv_cancel₀ ha, mul_inv_cancel₀ hc, sqzL_one e]
      simp)
    (by
      refine LinearMap.ext fun z => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
        LinearMap.id_coe, id_eq]
      rw [sqzL_comp e he, inv_mul_cancel₀ ha, inv_mul_cancel₀ hc, sqzL_one e]
      simp)
  continuous_toFun := (sqzL e a c).continuous
  continuous_invFun := (sqzL e a⁻¹ c⁻¹).continuous

/-- The squeeze as an affine equivalence: this is the change of variables the argument uses. -/
noncomputable def sqzA (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) : E ≃ᵃ[ℝ] E :=
  (sqzLE e he ha hc).toLinearEquiv.toAffineEquiv

@[simp]
theorem sqzA_apply (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (z : E) :
    sqzA e he ha hc z = sqzL e a c z := rfl

theorem sqzA_linear (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    (((sqzA e he ha hc).linear : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) = (sqzL e a c : E →ₗ[ℝ] E) := rfl

theorem sqzA_zero (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    sqzA e he ha hc 0 = 0 := by
  rw [sqzA_apply]
  simp [sqzL_apply]

/-- **The Jacobian of the squeeze.** -/
theorem affineJacobian_sqzA (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Kakeya.affineJacobian (sqzA e he ha hc)
      = ENNReal.ofReal |a ^ Module.finrank ℝ E * c ^ (Module.finrank ℝ E - 1)| := by
  rw [Kakeya.affineJacobian, sqzA_linear e he ha hc, det_sqzL e he]

end Equiv


/-! ## Orthogonal-projection helpers -/

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `sqzL e a c z = a • sqzL e 1 c z`. -/
theorem sqzL_smul_eq (e : E) (a c : ℝ) (z : E) : sqzL e a c z = a • (sqzL e 1 c z) := by
  rw [sqzL_apply, sqzL_apply]; module

/-- The squeeze shrinks by at least the factor `|a|`. -/
theorem norm_sqzL_le_abs (e : E) (he : ‖e‖ = 1) {a c : ℝ} (hc : |c| ≤ 1) (z : E) :
    ‖sqzL e a c z‖ ≤ |a| * ‖z‖ := by
  have h1 := norm_sq_sqzL e he a c z
  have h2 := norm_sq_split e he z
  set W : ℝ := ‖z - (inner ℝ e z : ℝ) • e‖ with hW
  set A : ℝ := (inner ℝ e z : ℝ) with hA
  have hc2 : c ^ 2 ≤ 1 := by nlinarith [abs_nonneg c, sq_abs c]
  have hkey : ‖sqzL e a c z‖ ^ 2 ≤ (|a| * ‖z‖) ^ 2 := by
    rw [h1]
    have e1 : (|a| * ‖z‖) ^ 2 = a ^ 2 * W ^ 2 + a ^ 2 * A ^ 2 := by
      have hab : |a| ^ 2 = a ^ 2 := sq_abs a
      calc (|a| * ‖z‖) ^ 2 = |a| ^ 2 * ‖z‖ ^ 2 := by ring
        _ = a ^ 2 * (W ^ 2 + A ^ 2) := by rw [hab, h2]
        _ = a ^ 2 * W ^ 2 + a ^ 2 * A ^ 2 := by ring
    rw [e1]
    have hstep : 0 ≤ a ^ 2 * W ^ 2 * (1 - c ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg W)) (by linarith)
    nlinarith [hstep]
  nlinarith [hkey, norm_nonneg (sqzL e a c z), mul_nonneg (abs_nonneg a) (norm_nonneg z)]

/-- The component of `z` orthogonal to a unit vector `e` is no longer than `z`. -/
theorem norm_perp_le (e : E) (he : ‖e‖ = 1) (z : E) :
    ‖z - (inner ℝ e z : ℝ) • e‖ ≤ ‖z‖ := by
  have h := norm_sq_split e he z
  nlinarith [norm_nonneg (z - (inner ℝ e z : ℝ) • e), norm_nonneg z,
    sq_nonneg (inner ℝ e z : ℝ)]

/-- **Orthogonal projection off a line minimises the distance to that line.** -/
theorem norm_sub_proj_le (g : E) (hg : g ≠ 0) (y : E) (β : ℝ) :
    ‖y - ((inner ℝ g y : ℝ) / ‖g‖ ^ 2) • g‖ ≤ ‖y - β • g‖ := by
  set μ : ℝ := (inner ℝ g y : ℝ) / ‖g‖ ^ 2 with hμ
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have horth : (inner ℝ (y - μ • g) g : ℝ) = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hμ,
      real_inner_comm g y]
    field_simp
    ring
  have hdec : y - β • g = (y - μ • g) + (μ - β) • g := by module
  have hsq : ‖y - μ • g‖ ^ 2 ≤ ‖y - β • g‖ ^ 2 := by
    rw [hdec, norm_add_sq_real, real_inner_smul_right, horth]
    nlinarith [sq_nonneg ‖(μ - β) • g‖]
  nlinarith [hsq, norm_nonneg (y - μ • g), norm_nonneg (y - β • g)]

/-- The projection written through the normalised direction. -/
theorem proj_eq_unit_proj (g : E) (hg : g ≠ 0) (y : E) :
    ((inner ℝ g y : ℝ) / ‖g‖ ^ 2) • g
      = ((inner ℝ g y : ℝ) / ‖g‖) • (‖g‖⁻¹ • g) := by
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  rw [smul_smul]
  congr 1
  field_simp

/-! ## Tube core coordinates -/

/-- A point within `δ` of a core point is in the carrier. -/
theorem mem_carrier_of_repr {δ : NNReal} (T : Tube δ E) {z : E} {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) ≤ t) (ht1 : t ≤ 1 / 2)
    (hz : dist z (T.midpoint + t • T.direction) ≤ (δ : ℝ)) : z ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.midpoint + t • T.direction,
    T.midpoint_add_smul_direction_mem_segment ht0 ht1, Metric.mem_closedBall.mpr hz⟩

/-- Every core point has a midpoint-plus-multiple-of-direction representation. -/
theorem exists_repr_of_mem_segment {δ : NNReal} (T : Tube δ E) {w : E}
    (hw : w ∈ segment ℝ T.x T.y) :
    ∃ t : ℝ, -(1 / 2 : ℝ) ≤ t ∧ t ≤ 1 / 2 ∧ w = T.midpoint + t • T.direction := by
  obtain ⟨t₁, t₂, h1, h2, hsum, hwe⟩ := hw
  refine ⟨t₂ - 1 / 2, by linarith, by linarith, ?_⟩
  have hθ : t₁ = 1 - t₂ := by linarith
  rw [← hwe, hθ]
  show (1 - t₂) • T.x + t₂ • T.y = (1 / 2 : ℝ) • (T.x + T.y) + (t₂ - 1 / 2) • (T.y - T.x)
  module

/-- `Tube.center` and `Tube.midpoint` agree. -/
theorem center_eq_midpoint {δ : NNReal} (T : Tube δ E) : T.center = T.midpoint := by
  show _root_.midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
  rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]

end Geometry


/-! ## The transverse extent of the squeezed ball -/

section Transverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The key geometric estimate.**  If the direction `u` is transverse to `e^⊥` (`|⟪e,u⟫| ≥ 1/2`),
then the component of `sqzL e a c p` orthogonal to the image axis `sqzL e a c u` is at most
`3 a c ‖p‖` — a factor `c` smaller than `‖p‖`.  This is why the image of a `ρ`-tube is a
`c ρ`-tube and not merely a `ρ`-tube: the long axis `ρ` of the image ellipsoid points *along*
the image axis. -/
theorem norm_sqzL_sub_proj_le (e : E) (he : ‖e‖ = 1) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hc1 : c ≤ 1) {u : E} (hu1 : ‖u‖ = 1) (hcap : (1 : ℝ) / 2 ≤ |(inner ℝ e u : ℝ)|) (p : E) :
    ‖sqzL e a c p
        - ((inner ℝ (sqzL e a c u) (sqzL e a c p) : ℝ) / ‖sqzL e a c u‖ ^ 2) • sqzL e a c u‖
      ≤ 3 * a * c * ‖p‖ := by
  have hgpos : 0 < ‖sqzL e a c u‖ := by
    have h := le_norm_sqzL e he ha hc hc1 u
    rw [hu1, mul_one] at h
    have : (0 : ℝ) < a * c := mul_pos ha hc
    linarith
  have hgne : sqzL e a c u ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hgpos)
  have hαu : (0 : ℝ) < |(inner ℝ e u : ℝ)| := by linarith
  have hαune : (inner ℝ e u : ℝ) ≠ 0 := abs_ne_zero.mp (ne_of_gt hαu)
  set β : ℝ := (inner ℝ e p : ℝ) / (inner ℝ e u : ℝ) with hβ
  have hβu : β * (inner ℝ e u : ℝ) = (inner ℝ e p : ℝ) := by
    rw [hβ]; field_simp
  have hident : sqzL e a c p - β • sqzL e a c u
      = (a * c) • ((p - (inner ℝ e p : ℝ) • e) - β • (u - (inner ℝ e u : ℝ) • e)) := by
    rw [sqzL_split e a c p, sqzL_split e a c u, ← hβu]
    module
  have h2 : ‖p - (inner ℝ e p : ℝ) • e‖ ≤ ‖p‖ := norm_perp_le e he p
  have h3 : ‖u - (inner ℝ e u : ℝ) • e‖ ≤ 1 := by
    rw [← hu1]; exact norm_perp_le e he u
  have hinnp : |(inner ℝ e p : ℝ)| ≤ ‖p‖ := by
    have h := abs_real_inner_le_norm e p
    rwa [he, one_mul] at h
  have h4 : |β| ≤ 2 * ‖p‖ := by
    rw [hβ, abs_div, div_le_iff₀ hαu]
    nlinarith [norm_nonneg p]
  have hbound : ‖sqzL e a c p - β • sqzL e a c u‖ ≤ 3 * a * c * ‖p‖ := by
    rw [hident, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ha hc)]
    have hV : ‖(p - (inner ℝ e p : ℝ) • e) - β • (u - (inner ℝ e u : ℝ) • e)‖
        ≤ ‖p‖ + 2 * ‖p‖ * 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs]
      have hnn : (0 : ℝ) ≤ ‖u - (inner ℝ e u : ℝ) • e‖ := norm_nonneg _
      nlinarith [abs_nonneg β, norm_nonneg p]
    nlinarith [mul_pos ha hc, norm_nonneg p]
  exact (norm_sub_proj_le _ hgne _ β).trans hbound

end Transverse

/-! ## The squeeze at the fixed scaling `1/4`, and the outer tube -/

section Squeeze

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The squeeze used throughout: the identity along `e`, multiplication by `σ` on `e^⊥`, the
whole scaled by `1/4` so that the image of `B₁` lands in `B_{1/4}`. -/
noncomputable def sqz (e : E) (he : ‖e‖ = 1) {σ : NNReal} (hσ : σ ≠ 0) : E ≃ᵃ[ℝ] E :=
  sqzA e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) (by norm_num)
    (by exact_mod_cast hσ)

theorem sqz_apply (e : E) (he : ‖e‖ = 1) {σ : NNReal} (hσ : σ ≠ 0) (z : E) :
    sqz e he hσ z = sqzL e (1 / 4 : ℝ) (σ : ℝ) z := rfl

/-- Linearity in the two-point form used for tube cores. -/
theorem map_add_smul (L : E →L[ℝ] E) (m d : E) (t : ℝ) : L (m + t • d) = L m + t • L d := by
  rw [map_add, map_smul]

/-- A linear map preserves midpoints, in the form the tube core needs. -/
theorem map_midpoint_eq (L : E →L[ℝ] E) (x y : E) :
    _root_.midpoint ℝ (L x) (L y) = L ((1 / 2 : ℝ) • (x + y)) := by
  rw [midpoint_eq_smul_add, invOf_eq_inv, map_smul, map_add]
  norm_num

/-- **The squeezed image of a `ρ`-tube whose axis is transverse to `e^⊥` sits inside a
`σρ`-tube.**  This is the geometric heart of the squeeze. -/
theorem image_subset_centredExtension
    (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (T : Tube ρ E) (hcap : (1 : ℝ) / 2 ≤ |(inner ℝ e T.direction : ℝ)|)
    (hpq : sqz e he hσ T.x ≠ sqz e he hσ T.y) :
    (sqz e he hσ) '' T.carrier ⊆ (Tube.centredExtension (σ * ρ) hpq).carrier := by
  have hσ0 : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hσ)
  have hσ1' : (σ : ℝ) ≤ 1 := by exact_mod_cast hσ1
  have hρ1' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  have habsσ : |(σ : ℝ)| ≤ 1 := by rw [abs_of_pos hσ0]; exact hσ1'
  have hAz : ∀ z : E, sqz e he hσ z = sqzL e (1 / 4 : ℝ) (σ : ℝ) z := fun z => rfl
  have hsub : sqz e he hσ T.y - sqz e he hσ T.x = sqzL e (1 / 4 : ℝ) (σ : ℝ) T.direction := by
    simp only [hAz]
    rw [← map_sub]
  have hgle : ‖sqzL e (1 / 4 : ℝ) (σ : ℝ) T.direction‖ ≤ 1 / 4 := by
    have h := norm_sqzL_le_abs e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) habsσ T.direction
    rw [T.norm_direction, mul_one] at h
    calc ‖sqzL e (1 / 4 : ℝ) (σ : ℝ) T.direction‖ ≤ |(1 / 4 : ℝ)| := h
      _ = 1 / 4 := by norm_num
  have hgpos : 0 < ‖sqzL e (1 / 4 : ℝ) (σ : ℝ) T.direction‖ := by
    have h := le_norm_sqzL e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) (by norm_num) hσ0 hσ1'
      T.direction
    rw [T.norm_direction, mul_one] at h
    have hp : (0 : ℝ) < 1 / 4 * (σ : ℝ) := by positivity
    linarith
  set L : E →L[ℝ] E := sqzL e (1 / 4 : ℝ) (σ : ℝ) with hLdef
  set g : E := L T.direction with hgdef
  set T' : Tube (σ * ρ) E := Tube.centredExtension (σ * ρ) hpq with hT'def
  have hgn : ‖g‖ ≠ 0 := ne_of_gt hgpos
  have hmid : T'.midpoint = L T.midpoint := by
    rw [← center_eq_midpoint, hT'def, Tube.center_centredExtension]
    simp only [hAz]
    exact map_midpoint_eq L T.x T.y
  have hdir : T'.direction = ‖g‖⁻¹ • g := by
    rw [hT'def, Tube.direction_centredExtension, hsub]
  have hdirnorm : ‖T'.direction‖ = 1 := T'.norm_direction
  intro y hy
  obtain ⟨z, hz, hyz⟩ := hy
  rw [← hyz, hAz]
  rw [T.carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t₀, ht₀0, ht₀1, hwrepr⟩ := exists_repr_of_mem_segment T hw
  have hpnorm : ‖z - w‖ ≤ (ρ : ℝ) := by
    rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hzw
  have hZ : L z - T'.midpoint = t₀ • g + L (z - w) := by
    have h2 : L w = L T.midpoint + t₀ • g := by
      rw [hwrepr, hgdef]
      exact map_add_smul L T.midpoint T.direction t₀
    have h1 : L (z - w) = L z - L w := map_sub L z w
    rw [hmid, h1, h2]
    module
  have hLp : ‖L (z - w)‖ ≤ 1 / 4 * (ρ : ℝ) := by
    have h := norm_sqzL_le_abs e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) habsσ (z - w)
    rw [← hLdef] at h
    calc ‖L (z - w)‖ ≤ |(1 / 4 : ℝ)| * ‖z - w‖ := h
      _ = 1 / 4 * ‖z - w‖ := by norm_num
      _ ≤ 1 / 4 * (ρ : ℝ) := by linarith
  have hZn : ‖L z - T'.midpoint‖ ≤ 3 / 8 := by
    rw [hZ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have habs : |t₀| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, ht₀1⟩
    nlinarith [norm_nonneg g, hgle, hLp, abs_nonneg t₀]
  have htabs : |(inner ℝ T'.direction (L z - T'.midpoint) : ℝ)| ≤ 3 / 8 := by
    have hbd := abs_real_inner_le_norm T'.direction (L z - T'.midpoint)
    rw [hdirnorm, one_mul] at hbd
    linarith
  refine mem_carrier_of_repr T'
    (t := (inner ℝ T'.direction (L z - T'.midpoint) : ℝ)) ?_ ?_ ?_
  · linarith [(abs_le.mp htabs).1]
  · linarith [(abs_le.mp htabs).2]
  · rw [dist_eq_norm]
    have hgg : (inner ℝ g g : ℝ) = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
    have hip : (inner ℝ T'.direction (L z - T'.midpoint) : ℝ)
        = ((inner ℝ g (L z - T'.midpoint) : ℝ)) / ‖g‖ := by
      rw [hdir, real_inner_smul_left]; field_simp
    have hZi : (inner ℝ g (L z - T'.midpoint) : ℝ)
        = t₀ * ‖g‖ ^ 2 + (inner ℝ g (L (z - w)) : ℝ) := by
      rw [hZ, inner_add_right, real_inner_smul_right, hgg]
    have hsmul : (inner ℝ T'.direction (L z - T'.midpoint) : ℝ) • T'.direction
        = (t₀ + (inner ℝ g (L (z - w)) : ℝ) / ‖g‖ ^ 2) • g := by
      rw [hip, hZi, hdir, smul_smul]
      congr 1
      field_simp
    have hLz : L z = T'.midpoint + (t₀ • g + L (z - w)) := by
      rw [← hZ]; abel
    have hproj : L z - (T'.midpoint + (inner ℝ T'.direction (L z - T'.midpoint) : ℝ)
          • T'.direction)
        = L (z - w) - ((inner ℝ g (L (z - w)) : ℝ) / ‖g‖ ^ 2) • g := by
      rw [hsmul, hLz]
      module
    rw [hproj, hgdef]
    have hkey := norm_sqzL_sub_proj_le e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) (by norm_num)
      hσ0 hσ1' (u := T.direction) T.norm_direction hcap (z - w)
    rw [← hLdef] at hkey
    calc ‖L (z - w) - ((inner ℝ (L T.direction) (L (z - w)) : ℝ) / ‖L T.direction‖ ^ 2)
            • L T.direction‖
        ≤ 3 * (1 / 4 : ℝ) * (σ : ℝ) * ‖z - w‖ := hkey
      _ ≤ 3 * (1 / 4 : ℝ) * (σ : ℝ) * (ρ : ℝ) := by
            have hnn : (0 : ℝ) ≤ 3 * (1 / 4 : ℝ) * (σ : ℝ) := by positivity
            nlinarith
      _ ≤ ((σ * ρ : NNReal) : ℝ) := by
            push_cast
            nlinarith [NNReal.coe_nonneg σ, NNReal.coe_nonneg ρ]

end Squeeze


/-! ## The outer tube: ball containment and volume comparability -/

section Outer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem sqz_x_ne_y (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0) (T : Tube ρ E) :
    sqz e he hσ T.x ≠ sqz e he hσ T.y := by
  intro h
  have hxy : T.x = T.y := (sqz e he hσ).injective h
  have h1 : dist T.x T.y = 1 := T.dist_eq_one
  rw [hxy, dist_self] at h1
  exact absurd h1 (by norm_num)

theorem x_mem_carrier {ρ : NNReal} (T : Tube ρ E) : T.x ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y,
    Metric.mem_closedBall_self ρ.coe_nonneg⟩

theorem y_mem_carrier {ρ : NNReal} (T : Tube ρ E) : T.y ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨T.y, right_mem_segment ℝ T.x T.y,
    Metric.mem_closedBall_self ρ.coe_nonneg⟩

/-- The squeezed image of the unit ball lies in `B_{1/4}`. -/
theorem norm_sqz_le (e : E) (he : ‖e‖ = 1) {σ : NNReal} (hσ : σ ≠ 0) (hσ1 : σ ≤ 1) {z : E}
    (hz : ‖z‖ ≤ 1) : ‖sqz e he hσ z‖ ≤ 1 / 4 := by
  have hσ0 : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hσ)
  have habsσ : |(σ : ℝ)| ≤ 1 := by
    rw [abs_of_pos hσ0]; exact_mod_cast hσ1
  have h := norm_sqzL_le_abs e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) habsσ z
  rw [sqz_apply]
  calc ‖sqzL e (1 / 4 : ℝ) (σ : ℝ) z‖ ≤ |(1 / 4 : ℝ)| * ‖z‖ := h
    _ ≤ 1 / 4 * 1 := by
        rw [abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
        exact mul_le_mul_of_nonneg_left hz (by norm_num)
    _ = 1 / 4 := by norm_num

/-- **The outer tube of the squeezed image lies in the unit ball.** -/
theorem centredExtension_subset_unitBall (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0)
    (hσ1 : σ ≤ 1) (T : Tube ρ E) (hball : T.carrier ⊆ Metric.closedBall (0 : E) 1)
    (hσρ : ((σ * ρ : NNReal) : ℝ) ≤ 1 / 4) :
    (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ T)).carrier
      ⊆ Metric.closedBall (0 : E) 1 := by
  refine Tube.centredExtension_subset_closedBall _ ?_ ?_ hσρ
  · rw [dist_zero_right]
    exact norm_sqz_le e he hσ hσ1 (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball (x_mem_carrier T))
  · rw [dist_zero_right]
    exact norm_sqz_le e he hσ hσ1 (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball (y_mem_carrier T))

/-- The Jacobian of the fixed squeeze. -/
theorem affineJacobian_sqz (e : E) (he : ‖e‖ = 1) {σ : NNReal} (hσ : σ ≠ 0) :
    Kakeya.affineJacobian (sqz e he hσ)
      = ENNReal.ofReal |(1 / 4 : ℝ) ^ Module.finrank ℝ E
          * (σ : ℝ) ^ (Module.finrank ℝ E - 1)| :=
  affineJacobian_sqzA e he _ _

/-- **The volume loss of replacing the squeezed image by its outer tube.** -/
noncomputable def sqzLoss : NNReal :=
  1 + 64 * Tube.volume_le.C 3 * (Tube.le_volume.c 3)⁻¹

theorem one_le_sqzLoss : 1 ≤ sqzLoss := le_self_add

theorem sqzLoss_ne_zero : sqzLoss ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_sqzLoss)

variable [Nontrivial E]

/-- **The outer tube is volume-comparable to the squeezed image.**  In dimension three the
image of a `ρ`-tube under the squeeze has volume `σ²ρ²/64` up to a dimensional constant, and
the outer `σρ`-tube has volume `≍ (σρ)²`; the ratio is absolute. -/
theorem volume_centredExtension_le (hn : Module.finrank ℝ E = 3) (e : E) (he : ‖e‖ = 1)
    {σ ρ : NNReal} (hσ : σ ≠ 0) (hσρ1 : σ * ρ ≤ 1) (T : Tube ρ E) :
    volume (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ T)).carrier
      ≤ (sqzLoss : ENNReal) * volume ((sqz e he hσ) '' T.carrier) := by
  have hc0 : Tube.le_volume.c 3 ≠ 0 := ne_of_gt (Tube.le_volume.c_pos 3)
  -- upper bound on the outer tube
  have hup : volume (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ T)).carrier
      ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal) * ((σ * ρ : NNReal) : ENNReal) ^ 2 := by
    have h := Tube.volume_le (E := E) hσρ1 (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ T))
    rw [hn] at h
    simpa using h
  -- lower bound on the image
  have hjac : Kakeya.affineJacobian (sqz e he hσ)
      = (((σ ^ 2 / 64 : NNReal)) : ENNReal) := by
    rw [affineJacobian_sqz e he hσ, hn]
    have hpos : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ 3 * (σ : ℝ) ^ 2 := by positivity
    rw [abs_of_nonneg hpos]
    rw [show ((σ ^ 2 / 64 : NNReal) : ENNReal) = ENNReal.ofReal ((σ ^ 2 / 64 : NNReal) : ℝ) from
      ENNReal.ofReal_coe_nnreal.symm]
    congr 1
    push_cast
    ring
  have hlow : (((σ ^ 2 / 64 : NNReal)) : ENNReal) * (((Tube.le_volume.c 3 : NNReal)) : ENNReal)
        * ((ρ : NNReal) : ENNReal) ^ 2
      ≤ volume ((sqz e he hσ) '' T.carrier) := by
    rw [Kakeya.volume_image_affineEquiv, hjac, mul_assoc]
    gcongr
    have h := Tube.le_volume (E := E) T
    rw [hn] at h
    simpa using h
  have keyN : Tube.volume_le.C 3 * (σ * ρ) ^ 2
      ≤ sqzLoss * (σ ^ 2 / 64 * Tube.le_volume.c 3 * ρ ^ 2) := by
    have key : Tube.volume_le.C 3 * (σ * ρ) ^ 2
        = (64 * Tube.volume_le.C 3 * (Tube.le_volume.c 3)⁻¹)
          * (σ ^ 2 / 64 * Tube.le_volume.c 3 * ρ ^ 2) := by
      field_simp
    rw [key, sqzLoss]
    gcongr
    exact le_add_self
  refine hup.trans (le_trans ?_ (mul_le_mul_left' hlow _))
  have h1 : ((Tube.volume_le.C 3 : NNReal) : ENNReal) * ((σ * ρ : NNReal) : ENNReal) ^ 2
      = ((Tube.volume_le.C 3 * (σ * ρ) ^ 2 : NNReal) : ENNReal) := by push_cast; ring
  have h2 : (sqzLoss : ENNReal) * (((σ ^ 2 / 64 : NNReal) : ENNReal)
        * ((Tube.le_volume.c 3 : NNReal) : ENNReal) * ((ρ : NNReal) : ENNReal) ^ 2)
      = ((sqzLoss * (σ ^ 2 / 64 * Tube.le_volume.c 3 * ρ ^ 2) : NNReal) : ENNReal) := by
    push_cast; ring
  rw [h1, h2]
  exact_mod_cast keyN

end Outer


/-! ## The squeezed family of honest tubes -/

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {ι : Type*}

/-- **The squeezed shaded tube, re-presented as an honest `σρ`-tube.**  The carrier is the
outer tube of the squeezed image; the shade is the squeezed shade, intersected with that
carrier so that the definition is total. -/
noncomputable def sqzShadedTube (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0)
    (S : ShadedTube ρ E) : ShadedTube (σ * ρ) E where
  toTube := Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ S.toTube)
  shade := (sqz e he hσ '' S.shade)
    ∩ (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ S.toTube)).carrier
  measurableSet_shade :=
    (Kakeya.measurableSet_affineEquiv_image _ S.measurableSet_shade).inter
      (Tube.centredExtension (σ * ρ)
        (sqz_x_ne_y e he hσ S.toTube)).isCompact'.isClosed.measurableSet
  shade_subset := Set.inter_subset_right

@[simp]
theorem sqzShadedTube_carrier (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0)
    (S : ShadedTube ρ E) :
    (sqzShadedTube e he hσ S).carrier
      = (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ S.toTube)).carrier := rfl

@[simp]
theorem sqzShadedTube_shade (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0)
    (S : ShadedTube ρ E) :
    (sqzShadedTube e he hσ S).shade
      = (sqz e he hσ '' S.shade)
        ∩ (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ S.toTube)).carrier := rfl

/-- The squeezed family. -/
noncomputable def sqzFamily (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0)
    (T : ι → ShadedTube ρ E) : ι → ShadedTube (σ * ρ) E :=
  fun i => sqzShadedTube e he hσ (T i)

@[simp]
theorem sqzFamily_apply (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0)
    (T : ι → ShadedTube ρ E) (i : ι) :
    sqzFamily e he hσ T i = sqzShadedTube e he hσ (T i) := rfl

variable {e : E} {he : ‖e‖ = 1} {σ ρ : NNReal} {hσ : σ ≠ 0} {s : Finset ι}
  {T : ι → ShadedTube ρ E}

/-- The squeezed shade is exactly the affine image of the shade. -/
theorem sqzShadedTube_shade_eq (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1) (S : ShadedTube ρ E)
    (hcapS : (1 : ℝ) / 2 ≤ |(inner ℝ e S.direction : ℝ)|) :
    (sqzShadedTube e he hσ S).shade = sqz e he hσ '' S.shade := by
  rw [sqzShadedTube_shade]
  refine Set.inter_eq_self_of_subset_left ?_
  exact (Set.image_mono S.shade_subset).trans
    (image_subset_centredExtension e he hσ hσ1 hρ1 S.toTube hcapS
      (sqz_x_ne_y e he hσ S.toTube))

/-- On the index set the squeezed shade is exactly the affine image of the shade. -/
theorem sqzFamily_shade_eq' (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    ∀ i ∈ s, (sqzFamily e he hσ T i).shade = sqz e he hσ '' (T i).shade :=
  fun i hi => sqzShadedTube_shade_eq hσ1 hρ1 (T i) (hcap i hi)

theorem sqzFamily_shade_eq (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    ∀ i ∈ s, (sqzFamily e he hσ T i).toShadedBody.shade
      = (Kakeya.ML2Reduction.spineFamily (sqz e he hσ) T i).shade := by
  intro i hi
  rw [Kakeya.ML2Reduction.spineFamily_apply, Kakeya.ML2Reduction.spineImage_shade]
  exact sqzShadedTube_shade_eq hσ1 hρ1 (T i) (hcap i hi)

/-- The bodies of the squeezed family contain the squeezed images. -/
theorem spineImage_le_sqzShadedTube (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    ∀ i ∈ s, (Kakeya.ML2Reduction.spineFamily (sqz e he hσ) T i).toConvexSpaceBody
      ≤ (sqzFamily e he hσ T i).toConvexSpaceBody := by
  intro i hi
  refine SetLike.coe_subset_coe.mp ?_
  exact image_subset_centredExtension e he hσ hσ1 hρ1 (T i).toTube (hcap i hi)
    (sqz_x_ne_y e he hσ (T i).toTube)

/-- The volume loss of the squeezed family. -/
theorem sqzFamily_volume_le (hn : Module.finrank ℝ E = 3) (hσρ1 : σ * ρ ≤ 1) :
    ∀ i ∈ s, volume (sqzFamily e he hσ T i).carrier
      ≤ (sqzLoss : ENNReal)
        * volume (Kakeya.ML2Reduction.spineFamily (sqz e he hσ) T i).carrier := by
  intro i _
  exact volume_centredExtension_le hn e he hσ hσρ1 (T i).toTube

/-- **Every member of the squeezed family lies in `B₁`.** -/
theorem sqzFamily_carrier_subset_closedBall (hσ1 : σ ≤ 1)
    (hσρ4 : ((σ * ρ : NNReal) : ℝ) ≤ 1 / 4)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∀ i ∈ s, (sqzFamily e he hσ T i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  intro i hi
  exact centredExtension_subset_unitBall e he hσ hσ1 (T i).toTube (hball i hi) hσρ4

/-- **`Δ_max` grows by at most `sqzLoss`.** -/
theorem sqzFamily_maxDensity_le (hn : Module.finrank ℝ E = 3) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hσρ1 : σ * ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    Kakeya.maxDensity s (fun i => (sqzFamily e he hσ T i).toConvexSpaceBody)
      ≤ (sqzLoss : ENNReal) * Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) := by
  have hmax := Kakeya.ML2Reduction.maxDensity_le_of_comparable (C := sqzLoss) one_le_sqzLoss s
    (fun i => (Kakeya.ML2Reduction.spineFamily (sqz e he hσ) T i).toConvexSpaceBody)
    (fun i => (sqzFamily e he hσ T i).toConvexSpaceBody)
    (spineImage_le_sqzShadedTube hσ1 hρ1 hcap)
    (sqzFamily_volume_le hn hσρ1)
  rwa [Kakeya.ML2Reduction.spineFamily_maxDensity (sqz e he hσ) s T] at hmax

/-- **Fullness drops by at most `sqzLoss`.** -/
theorem sqzFamily_le_fullness (hn : Module.finrank ℝ E = 3) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hσρ1 : σ * ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    (sqzLoss)⁻¹ * ShadedBody.fullness s (fun i => (T i).toShadedBody)
      ≤ ShadedBody.fullness s (fun i => (sqzFamily e he hσ T i).toShadedBody) := by
  have hfull := Tube.le_fullness_of_volume_le (C := sqzLoss) one_le_sqzLoss s
    (Kakeya.ML2Reduction.spineFamily (sqz e he hσ) T)
    (fun i => (sqzFamily e he hσ T i).toShadedBody)
    (sqzFamily_shade_eq hσ1 hρ1 hcap)
    (sqzFamily_volume_le hn hσρ1)
  rwa [Kakeya.ML2Reduction.spineFamily_fullness (sqz e he hσ) s T] at hfull

/-! ### The conclusion transports with no loss at all -/

theorem sqzFamily_sum_volume_shade (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    ∑ i ∈ s, volume (sqzFamily e he hσ T i).shade
      = Kakeya.affineJacobian (sqz e he hσ) * ∑ i ∈ s, volume (T i).shade := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [sqzFamily_shade_eq' hσ1 hρ1 hcap i hi, Kakeya.volume_image_affineEquiv]

theorem sqzFamily_volume_iUnionShade (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    volume (⋃ i ∈ s, (sqzFamily e he hσ T i).shade)
      = Kakeya.affineJacobian (sqz e he hσ) * volume (⋃ i ∈ s, (T i).shade) := by
  have hu : (⋃ i ∈ s, (sqzFamily e he hσ T i).shade)
      = (sqz e he hσ) '' (⋃ i ∈ s, (T i).shade) := by
    rw [Set.image_iUnion₂]
    refine Set.iUnion₂_congr fun i hi => ?_
    exact sqzFamily_shade_eq' hσ1 hρ1 hcap i hi
  rw [hu, Kakeya.volume_image_affineEquiv]

/-- **The mass inequality pulls back with no loss.** -/
theorem mass_le_of_sqzFamily (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) {K : ENNReal}
    (h : ∑ i ∈ s, volume (sqzFamily e he hσ T i).shade
      ≤ K * volume (⋃ i ∈ s, (sqzFamily e he hσ T i).shade)) :
    ∑ i ∈ s, volume (T i).shade ≤ K * volume (⋃ i ∈ s, (T i).shade) := by
  rw [sqzFamily_sum_volume_shade hσ1 hρ1 hcap,
    sqzFamily_volume_iUnionShade hσ1 hρ1 hcap] at h
  set J : ENNReal := Kakeya.affineJacobian (sqz e he hσ) with hJ
  have hJ0 : J ≠ 0 := Kakeya.affineJacobian_ne_zero _
  have hJt : J ≠ ⊤ := Kakeya.affineJacobian_ne_top _
  have h' : (∑ i ∈ s, volume (T i).shade) * J
      ≤ (K * volume (⋃ i ∈ s, (T i).shade)) * J := by
    calc (∑ i ∈ s, volume (T i).shade) * J = J * ∑ i ∈ s, volume (T i).shade := by ring
      _ ≤ K * (J * volume (⋃ i ∈ s, (T i).shade)) := h
      _ = (K * volume (⋃ i ∈ s, (T i).shade)) * J := by ring
  exact (ENNReal.mul_le_mul_iff_left hJ0 hJt).mp h'

end Family


/-! ## The three coordinate caps of `ℝ³` -/

/-- `Space3` is `EuclideanSpace ℝ (Fin 3)`, the ambient space of `Kakeya.ML2Assembly.SmallCard`. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

/-- The `k`-th coordinate unit vector. -/
noncomputable def capVec (k : Fin 3) : Space3 := EuclideanSpace.single k (1 : ℝ)

theorem norm_capVec (k : Fin 3) : ‖capVec k‖ = 1 := by
  rw [capVec, EuclideanSpace.norm_single]
  norm_num

theorem inner_capVec (k : Fin 3) (u : Space3) : (inner ℝ (capVec k) u : ℝ) = u k := by
  rw [capVec, EuclideanSpace.inner_single_left]
  norm_num

/-- **Every unit vector of `ℝ³` is `1/2`-transverse to one of the three coordinate
hyperplanes**: `max_k |u_k| ≥ 1/√3 > 1/2`.  This is the whole of the "cap decomposition" the
squeeze needs — three caps, not a sphere net. -/
theorem exists_coord_abs_ge (u : Space3) (hu : ‖u‖ = 1) :
    ∃ k : Fin 3, (1 : ℝ) / 2 ≤ |u k| := by
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ k : Fin 3, ‖u k‖ ^ 2 = 1 := by
    have h := EuclideanSpace.norm_eq u
    rw [hu] at h
    have hnn : (0 : ℝ) ≤ ∑ k : Fin 3, ‖u k‖ ^ 2 := by positivity
    have hs := Real.sq_sqrt hnn
    nlinarith [hs, h]
  have hlt : ∑ k : Fin 3, ‖u k‖ ^ 2 < ∑ _k : Fin 3, ((1 : ℝ) / 2) ^ 2 := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty ?_
    intro k _
    have h1 : ‖u k‖ = |u k| := Real.norm_eq_abs _
    have h2 := hcon k
    rw [h1]
    nlinarith [abs_nonneg (u k)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hlt
  rw [hsum] at hlt
  norm_num at hlt

/-! ## Two elementary bookkeeping lemmas -/

/-- **A constant is subpolynomial**: below an explicit threshold, `K ≤ ρ^{-t}`. -/
theorem eventually_const_le_rpow {K : NNReal} (hK : 1 ≤ K) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ ρ : NNReal in 𝓝[>] 0, K ≤ ρ ^ (-t) := by
  have hK0 : K ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK)
  have hinv0 : (0 : NNReal) < K⁻¹ := pos_of_ne_zero (inv_ne_zero hK0)
  have hmem : Set.Ioo (0 : NNReal) (K⁻¹ ^ (1 / t)) ∈ 𝓝[>] (0 : NNReal) :=
    Ioo_mem_nhdsGT (NNReal.rpow_pos hinv0)
  filter_upwards [hmem] with ρ hρ
  obtain ⟨hρ0, hρlt⟩ := hρ
  have hpow : ρ ^ t ≤ K⁻¹ := by
    calc ρ ^ t ≤ (K⁻¹ ^ (1 / t)) ^ t := NNReal.rpow_le_rpow hρlt.le ht.le
      _ = K⁻¹ ^ (1 / t * t) := (NNReal.rpow_mul _ _ _).symm
      _ = K⁻¹ := by rw [one_div, inv_mul_cancel₀ (ne_of_gt ht), NNReal.rpow_one]
  have hmul : ρ ^ t * K ≤ 1 := by
    calc ρ ^ t * K ≤ K⁻¹ * K := mul_le_mul_right' hpow _
      _ = 1 := inv_mul_cancel₀ hK0
  rw [NNReal.rpow_neg]
  exact Kakeya.ML2Reduction.le_inv_of_mul_le_one (ne_of_gt (NNReal.rpow_pos hρ0)) hmul

/-- **The heaviest of the three caps carries at least a third of the mass.** -/
theorem exists_max_fibre {ι : Type*} (s : Finset ι) (kf : ι → Fin 3) (f : ι → ENNReal) :
    ∃ m : Fin 3, ∑ i ∈ s, f i ≤ 3 * ∑ i ∈ s with kf i = m, f i := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3))
    (fun k => ∑ i ∈ s with kf i = k, f i) Finset.univ_nonempty
  refine ⟨m, ?_⟩
  calc ∑ i ∈ s, f i = ∑ k : Fin 3, ∑ i ∈ s with kf i = k, f i :=
        (Finset.sum_fiberwise s kf f).symm
    _ ≤ ∑ _k : Fin 3, ∑ i ∈ s with kf i = m, f i :=
        Finset.sum_le_sum fun k _ => hm k (Finset.mem_univ k)
    _ = 3 * ∑ i ∈ s with kf i = m, f i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- **A subfamily carrying a third of the shaded mass has at least a third of the fullness.** -/
theorem fullness_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (s t : Finset ι) (V : ι → ShadedBody E)
    (hts : t ⊆ s)
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ 3 * ∑ i ∈ t, volume (V i).shade) :
    (3 : NNReal)⁻¹ * ShadedBody.fullness s V ≤ ShadedBody.fullness t V := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_inv (by norm_num),
    ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  have hden : ∑ i ∈ t, volume (V i).carrier ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum_of_subset hts
  have hnum : (∑ i ∈ s, volume (V i).shade) / 3 ≤ ∑ i ∈ t, volume (V i).shade := by
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm]
    exact hmass
  show ((3 : ENNReal))⁻¹ * ((∑ i ∈ s, volume (V i).shade)
      / (∑ i ∈ s, volume (V i).carrier)) ≤ _
  calc ((3 : ENNReal))⁻¹ * ((∑ i ∈ s, volume (V i).shade)
        / (∑ i ∈ s, volume (V i).carrier))
      = ((∑ i ∈ s, volume (V i).shade) / 3) / (∑ i ∈ s, volume (V i).carrier) := by
        simp only [div_eq_mul_inv]; ring
    _ ≤ (∑ i ∈ t, volume (V i).shade) / (∑ i ∈ t, volume (V i).carrier) := by
        gcongr


/-! ## The squeeze at one scale -/

/-- **The squeeze at one scale.**  Given the body of `Kakeya.ML2Assembly.SmallCard` at the
squeezed scale `δ = σρ`, a family of `ρ`-tubes whose directions are all `1/2`-transverse to
`e^⊥` satisfies the *unsqueezed* mass bound with the very same constants: the conclusion comes
back with **no loss at all**, because it is a ratio of volumes and the squeeze is affine. -/
theorem mass_le_of_smallCardBody {γ ε₀ η' : ℝ}
    {σ ρ : NNReal} (hσ : σ ≠ 0) (hσ1 : σ ≤ 1) (hρ1 : ρ ≤ 1)
    (hσρ4 : ((σ * ρ : NNReal) : ℝ) ≤ 1 / 4)
    (e : Space3) (he : ‖e‖ = 1)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube ρ Space3)
    (hsm : ∀ (t : Finset ι) (S : ι → ShadedTube (σ * ρ) Space3),
        (∀ i ∈ t, (S i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao t (fun i ↦ (S i).toConvexSpaceBody)
          (((σ * ρ : NNReal) : ENNReal) ^ (-η')) →
        ShadedBody.fullness t (fun i ↦ (S i).toShadedBody) ≥ (σ * ρ) ^ η' →
        ((t.card : ℝ) < ((σ * ρ : NNReal) : ℝ)⁻¹) →
        ∑ i ∈ t, volume (S i).shade
          ≤ ((σ * ρ : NNReal) : ENNReal) ^ (-ε₀) * (t.card : ENNReal) ^ γ
            * volume (⋃ i ∈ t, (S i).shade))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|)
    (hKT : Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (sqzLoss : ENNReal)⁻¹ * ((σ * ρ : NNReal) : ENNReal) ^ (-η'))
    (hfull : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ sqzLoss * (σ * ρ) ^ η')
    (hcard : (s.card : ℝ) < ((σ * ρ : NNReal) : ℝ)⁻¹) :
    ∑ i ∈ s, volume (T i).shade
      ≤ ((σ * ρ : NNReal) : ENNReal) ^ (-ε₀) * (s.card : ENNReal) ^ γ
        * volume (⋃ i ∈ s, (T i).shade) := by
  have hn : Module.finrank ℝ Space3 = 3 := by simp
  have hσρ1 : σ * ρ ≤ 1 := by
    have h : ((σ * ρ : NNReal) : ℝ) ≤ 1 := by linarith
    exact_mod_cast h
  have hL0 : (sqzLoss : ENNReal) ≠ 0 := by
    simpa using sqzLoss_ne_zero
  have hLt : (sqzLoss : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  refine mass_le_of_sqzFamily (e := e) (he := he) (hσ := hσ) hσ1 hρ1 hcap ?_
  refine hsm s (sqzFamily e he hσ T)
    (sqzFamily_carrier_subset_closedBall hσ1 hσρ4 hball) ?_ ?_ hcard
  · rw [ConvexSpaceBody.IsKatzTao_def]
    refine le_trans (sqzFamily_maxDensity_le hn hσ1 hρ1 hσρ1 hcap) ?_
    calc (sqzLoss : ENNReal) * Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody)
        ≤ (sqzLoss : ENNReal) * ((sqzLoss : ENNReal)⁻¹
            * ((σ * ρ : NNReal) : ENNReal) ^ (-η')) := by gcongr
      _ = ((σ * ρ : NNReal) : ENNReal) ^ (-η') := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hL0 hLt, one_mul]
  · refine le_trans ?_ (sqzFamily_le_fullness hn hσ1 hρ1 hσρ1 hcap)
    calc (σ * ρ) ^ η' = sqzLoss⁻¹ * (sqzLoss * (σ * ρ) ^ η') := by
          rw [← mul_assoc, inv_mul_cancel₀ sqzLoss_ne_zero, one_mul]
      _ ≤ sqzLoss⁻¹ * ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) := by gcongr


/-! ## THE VERDICT: `SmallCard γ → K_KT γ` -/

/-- The constant of the sharp cardinality bound, made `≥ 1`. -/
noncomputable def cardConst : NNReal := 1 + Tube.card_le_of_densityIn_le.C 3

theorem one_le_cardConst : 1 ≤ cardConst := le_self_add

theorem one_le_three_sqzLoss : (1 : NNReal) ≤ 3 * sqzLoss := by
  calc (1 : NNReal) ≤ 3 := by norm_num
    _ = 3 * 1 := by ring
    _ ≤ 3 * sqzLoss := by gcongr; exact one_le_sqzLoss

/-- **The band restriction `|𝕋| < δ^{-1}` of `Kakeya.ML2Assembly.SmallCard` is affinely
vacuous.**  `SmallCard γ` implies the full partial Katz--Tao estimate `K_KT(γ)` for every
`γ ≥ 0`.

Given a family of `ρ`-tubes, split the directions into the three coordinate caps and apply the
anisotropic squeeze `(1/4)·diag(σ,σ,1)` in the frame of the heaviest cap, with
`σ = ρ^{1+2η}`.  The image is a family of honest `δ`-tubes at `δ = σρ = ρ^{2+2η}` with the
*same* index set; `Δ_max`, the fullness and the mass ratio are affine invariants up to absolute
constants, while the band threshold `δ^{-1} = ρ^{-2-2η}` has grown past the Katz--Tao
cardinality bound `|𝕋| ≲ ρ^{-2-η}`.  So the squeezed family lands strictly inside the band and
the conclusion pulls back with no loss. -/
theorem katzTaoEstimate_of_smallCard {γ : ℝ} (hγ : 0 ≤ γ)
    (h : Kakeya.ML2Assembly.SmallCard.{u} γ) :
    Kakeya.KatzTaoEstimate.{u} Space3 γ := by
  intro ε hε
  obtain ⟨η', hη'0, hη'1, hsmE⟩ := h (ε / 8) (by positivity)
  obtain ⟨δ₀, hδ₀0, hsm⟩ := Kakeya.ML2Reduction.exists_threshold_of_eventually_nhdsGT hsmE
  refine ⟨η' / 8, by linarith, ?_⟩
  set η : ℝ := η' / 8 with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have hη1 : η ≤ 1 / 8 := by rw [hηdef]; linarith
  have hbudget : η + η' ≤ (2 + 2 * η) * η' := by rw [hηdef]; nlinarith
  filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < min (1 / 8) δ₀ from
      lt_min (by norm_num) hδ₀0),
    eventually_const_le_rpow (K := sqzLoss) one_le_sqzLoss (t := η') hη'0,
    eventually_const_le_rpow (K := 3 * sqzLoss) one_le_three_sqzLoss (t := η') hη'0,
    eventually_const_le_rpow (K := cardConst) one_le_cardConst (t := η / 2) (by linarith),
    eventually_const_le_rpow (K := 3) (by norm_num) (t := ε / 2) (by linarith)]
    with ρ hρmem hL1 hL2 hL3 hL4
  obtain ⟨hρ0, hρlt⟩ := hρmem
  have hρ8 : ρ ≤ 1 / 8 := (lt_of_lt_of_le hρlt (min_le_left _ _)).le
  have hρδ₀ : ρ ≤ δ₀ := (lt_of_lt_of_le hρlt (min_le_right _ _)).le
  have hρ1 : ρ ≤ 1 := le_trans hρ8 (by rw [← NNReal.coe_le_coe]; norm_num)
  have hρ0' : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.mpr hρ0
  have hρ1' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  have hρlt1 : (ρ : ℝ) < 1 := by
    have h8 : ((1 : NNReal) / 8) < 1 := by norm_num
    exact_mod_cast lt_of_le_of_lt hρ8 h8
  have hρE0 : ((ρ : ENNReal)) ≠ 0 := by simpa using hρ0.ne'
  have hρE1 : ((ρ : ENNReal)) ≤ 1 := by exact_mod_cast hρ1
  have hL0 : (sqzLoss : ENNReal) ≠ 0 := by simpa using sqzLoss_ne_zero
  have hLt : (sqzLoss : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  intro ι s T hball hKT hfull
  set σ : NNReal := ρ ^ (1 + 2 * η) with hσdef
  have hσ0 : σ ≠ 0 := by rw [hσdef]; exact ne_of_gt (NNReal.rpow_pos hρ0)
  have hσ1 : σ ≤ 1 := by rw [hσdef]; exact NNReal.rpow_le_one hρ1 (by linarith)
  have hδeq : σ * ρ = ρ ^ (2 + 2 * η) := by
    have hx : ρ ^ (2 + 2 * η : ℝ) = ρ ^ (1 + 2 * η : ℝ) * ρ ^ (1 : ℝ) := by
      rw [← NNReal.rpow_add hρ0.ne']
      congr 1
      ring
    rw [hσdef, hx, NNReal.rpow_one]
  have hδ0 : 0 < σ * ρ := by rw [hδeq]; exact NNReal.rpow_pos hρ0
  have hδρ : σ * ρ ≤ ρ := by
    rw [hδeq]
    calc ρ ^ (2 + 2 * η : ℝ) ≤ ρ ^ (1 : ℝ) :=
          NNReal.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by linarith)
      _ = ρ := NNReal.rpow_one ρ
  have hδδ₀ : σ * ρ ≤ δ₀ := le_trans hδρ hρδ₀
  have hδ4 : ((σ * ρ : NNReal) : ℝ) ≤ 1 / 4 := by
    have h1 : ((σ * ρ : NNReal) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hδρ
    have h2 : (ρ : ℝ) ≤ 1 / 8 := by exact_mod_cast hρ8
    linarith
  have hcoeN : ∀ x : ℝ, ((σ * ρ : NNReal)) ^ x = ρ ^ ((2 + 2 * η) * x) := by
    intro x; rw [hδeq, ← NNReal.rpow_mul]
  have hcoeE : ∀ x : ℝ, (((σ * ρ : NNReal)) : ENNReal) ^ x
      = ((ρ : ENNReal)) ^ ((2 + 2 * η) * x) := by
    intro x
    rw [hδeq, ENNReal.coe_rpow_of_ne_zero hρ0.ne', ← ENNReal.rpow_mul]
  have hcoeER : ∀ x : ℝ, (((ρ ^ x : NNReal)) : ENNReal) = ((ρ : ENNReal)) ^ x :=
    fun x => ENNReal.coe_rpow_of_ne_zero hρ0.ne' x
  -- the cap decomposition: three coordinate caps
  obtain ⟨kf, hkf⟩ : ∃ kf : ι → Fin 3, ∀ i, (1 : ℝ) / 2 ≤ |((T i).direction) (kf i)| :=
    ⟨fun i => (exists_coord_abs_ge (T i).direction (T i).norm_direction).choose,
      fun i => (exists_coord_abs_ge (T i).direction (T i).norm_direction).choose_spec⟩
  obtain ⟨m, hm⟩ := exists_max_fibre s kf (fun i => volume (T i).shade)
  have hts : Finset.filter (fun i => kf i = m) s ⊆ s := Finset.filter_subset _ _
  have hcapt : ∀ i ∈ Finset.filter (fun i => kf i = m) s,
      (1 : ℝ) / 2 ≤ |(inner ℝ (capVec m) (T i).direction : ℝ)| := by
    intro i hi
    have hkm : kf i = m := (Finset.mem_filter.mp hi).2
    rw [inner_capVec, ← hkm]
    exact hkf i
  -- the sharp cardinality bound, and the band hypothesis
  have hcards : (s.card : ℝ) ≤ (ρ : ℝ) ^ (-(2 + 3 * η / 2) : ℝ) := by
    have hn : Module.finrank ℝ Space3 = 3 := by simp
    have hden : Kakeya.densityIn s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≤ ((ρ : ENNReal)) ^ (-η) :=
      (Kakeya.le_maxDensity s _ _).trans hKT
    have hraw := Tube.card_le_of_densityIn_le (E := Space3) (δ := ρ) (s := s)
      (T := fun i ↦ (T i).toTube) hρ0.ne' hball hden
    rw [hn] at hraw
    norm_num at hraw
    have hC : ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal)
        ≤ ((ρ : ENNReal)) ^ (-(η / 2)) := by
      refine le_trans (ENNReal.coe_le_coe.mpr (le_add_self : Tube.card_le_of_densityIn_le.C 3
        ≤ cardConst)) ?_
      exact le_trans (ENNReal.coe_le_coe.mpr hL3) (le_of_eq (hcoeER _))
    have hz : ((ρ : ENNReal)) ^ (-2 : ℤ) = ((ρ : ENNReal)) ^ (-2 : ℝ) := by
      rw [← ENNReal.rpow_intCast]
      norm_num
    have hkey : (s.card : ENNReal) ≤ ((ρ : ENNReal)) ^ (-(2 + 3 * η / 2) : ℝ) := by
      refine hraw.trans ?_
      rw [hz]
      calc ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal) * ((ρ : ENNReal)) ^ (-η)
              * ((ρ : ENNReal)) ^ (-2 : ℝ)
          ≤ ((ρ : ENNReal)) ^ (-(η / 2)) * ((ρ : ENNReal)) ^ (-η)
              * ((ρ : ENNReal)) ^ (-2 : ℝ) := by gcongr
        _ = ((ρ : ENNReal)) ^ (-(2 + 3 * η / 2) : ℝ) := by
            rw [← ENNReal.rpow_add _ _ hρE0 ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ hρE0 ENNReal.coe_ne_top]
            congr 1
            ring
    rw [← ENNReal.coe_rpow_of_ne_zero hρ0.ne',
      show ((s.card : ENNReal)) = ((s.card : NNReal) : ENNReal) by simp,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hkey
    simpa [NNReal.coe_rpow] using hkey
  have hcardlt : (s.card : ℝ) < ((σ * ρ : NNReal) : ℝ)⁻¹ := by
    have hinv : ((σ * ρ : NNReal) : ℝ)⁻¹ = (ρ : ℝ) ^ (-(2 + 2 * η) : ℝ) := by
      have h1 : ((σ * ρ : NNReal) : ℝ) = (ρ : ℝ) ^ (2 + 2 * η : ℝ) := by
        rw [hδeq]; push_cast [NNReal.coe_rpow]; ring
      rw [h1, ← Real.rpow_neg_one, ← Real.rpow_mul hρ0'.le]
      congr 1
      ring
    rw [hinv]
    refine lt_of_le_of_lt hcards ?_
    exact Real.rpow_lt_rpow_of_exponent_gt hρ0' hρlt1 (by linarith)
  have hcardt : ((Finset.filter (fun i => kf i = m) s).card : ℝ)
      < ((σ * ρ : NNReal) : ℝ)⁻¹ := by
    refine lt_of_le_of_lt ?_ hcardlt
    exact_mod_cast Finset.card_le_card hts
  -- the two transported hypotheses on the heaviest cap
  have hKTt : Kakeya.maxDensity (Finset.filter (fun i => kf i = m) s)
        (fun i ↦ (T i).toConvexSpaceBody)
      ≤ (sqzLoss : ENNReal)⁻¹ * (((σ * ρ : NNReal)) : ENNReal) ^ (-η') := by
    have hstep : (sqzLoss : ENNReal) * ((ρ : ENNReal)) ^ (-η)
        ≤ (((σ * ρ : NNReal)) : ENNReal) ^ (-η') := by
      rw [hcoeE]
      calc (sqzLoss : ENNReal) * ((ρ : ENNReal)) ^ (-η)
          ≤ ((ρ : ENNReal)) ^ (-η') * ((ρ : ENNReal)) ^ (-η) := by
            gcongr
            exact le_trans (ENNReal.coe_le_coe.mpr hL1) (le_of_eq (hcoeER _))
        _ = ((ρ : ENNReal)) ^ (-η' + -η) := by
            rw [← ENNReal.rpow_add _ _ hρE0 ENNReal.coe_ne_top]
        _ ≤ ((ρ : ENNReal)) ^ ((2 + 2 * η) * (-η')) := by
            refine ENNReal.rpow_le_rpow_of_exponent_ge hρE1 ?_
            nlinarith [hbudget]
    calc Kakeya.maxDensity (Finset.filter (fun i => kf i = m) s)
          (fun i ↦ (T i).toConvexSpaceBody)
        ≤ Kakeya.maxDensity s (fun i ↦ (T i).toConvexSpaceBody) :=
          Kakeya.maxDensity_mono _ hts
      _ ≤ ((ρ : ENNReal)) ^ (-η) := hKT
      _ = (sqzLoss : ENNReal)⁻¹ * ((sqzLoss : ENNReal) * ((ρ : ENNReal)) ^ (-η)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hL0 hLt, one_mul]
      _ ≤ (sqzLoss : ENNReal)⁻¹ * (((σ * ρ : NNReal)) : ENNReal) ^ (-η') := by gcongr
  have hfullt : ShadedBody.fullness (Finset.filter (fun i => kf i = m) s)
        (fun i ↦ (T i).toShadedBody) ≥ sqzLoss * (σ * ρ) ^ η' := by
    have hsub := fullness_sub_le s (Finset.filter (fun i => kf i = m) s)
      (fun i ↦ (T i).toShadedBody) hts hm
    have h3 : (3 : NNReal) * (sqzLoss * (σ * ρ) ^ η') ≤ ρ ^ η := by
      rw [hcoeN]
      calc (3 : NNReal) * (sqzLoss * ρ ^ ((2 + 2 * η) * η'))
          = (3 * sqzLoss) * ρ ^ ((2 + 2 * η) * η') := by ring
        _ ≤ ρ ^ (-η') * ρ ^ ((2 + 2 * η) * η') := by gcongr
        _ = ρ ^ (-η' + (2 + 2 * η) * η') := (NNReal.rpow_add hρ0.ne' _ _).symm
        _ ≤ ρ ^ η := NNReal.rpow_le_rpow_of_exponent_ge hρ0 hρ1 (by nlinarith [hbudget])
    have hf : sqzLoss * (σ * ρ) ^ η' ≤ (3 : NNReal)⁻¹ * ρ ^ η := by
      calc sqzLoss * (σ * ρ) ^ η'
          = (3 : NNReal)⁻¹ * (3 * (sqzLoss * (σ * ρ) ^ η')) := by
            rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (3 : NNReal) ≠ 0), one_mul]
        _ ≤ (3 : NNReal)⁻¹ * ρ ^ η := by gcongr
    refine le_trans hf (le_trans ?_ hsub)
    gcongr
  -- the squeeze at the scale `δ = σρ`
  have hmain := mass_le_of_smallCardBody (γ := γ) (ε₀ := ε / 8) (η' := η') hσ0 hσ1 hρ1 hδ4
    (capVec m) (norm_capVec m) (Finset.filter (fun i => kf i = m) s) T
    (fun t S h1 h2 h3 h4 => hsm (σ * ρ) hδ0 hδδ₀ t S h1 h2 h3 h4)
    (fun i hi => hball i (hts hi)) hcapt hKTt hfullt hcardt
  -- assemble
  have hunion : volume (⋃ i ∈ Finset.filter (fun i => kf i = m) s, (T i).shade)
      ≤ volume (⋃ i ∈ s, (T i).shade) := by
    refine measure_mono ?_
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨i, hts hi, hxi⟩
  have hcardpow : (((Finset.filter (fun i => kf i = m) s).card : ENNReal)) ^ γ
      ≤ ((s.card : ENNReal)) ^ γ := by
    refine ENNReal.rpow_le_rpow ?_ hγ
    exact_mod_cast Finset.card_le_card hts
  have h3E : (3 : ENNReal) ≤ ((ρ : ENNReal)) ^ (-(ε / 2)) := by
    have hc := ENNReal.coe_le_coe.mpr hL4
    rw [hcoeER] at hc
    simpa using hc
  have hfinal : (3 : ENNReal) * ((((σ * ρ : NNReal)) : ENNReal) ^ (-(ε / 8)))
      ≤ ((ρ : ENNReal)) ^ (-ε) := by
    rw [hcoeE]
    calc (3 : ENNReal) * ((ρ : ENNReal)) ^ ((2 + 2 * η) * (-(ε / 8)))
        ≤ ((ρ : ENNReal)) ^ (-(ε / 2)) * ((ρ : ENNReal)) ^ ((2 + 2 * η) * (-(ε / 8))) := by
          gcongr
      _ = ((ρ : ENNReal)) ^ (-(ε / 2) + (2 + 2 * η) * (-(ε / 8))) := by
          rw [← ENNReal.rpow_add _ _ hρE0 ENNReal.coe_ne_top]
      _ ≤ ((ρ : ENNReal)) ^ (-ε) := by
          refine ENNReal.rpow_le_rpow_of_exponent_ge hρE1 ?_
          nlinarith
  calc ∑ i ∈ s, volume (T i).shade
      ≤ 3 * ∑ i ∈ Finset.filter (fun i => kf i = m) s, volume (T i).shade := hm
    _ ≤ 3 * ((((σ * ρ : NNReal)) : ENNReal) ^ (-(ε / 8))
          * (((Finset.filter (fun i => kf i = m) s).card : ENNReal)) ^ γ
          * volume (⋃ i ∈ Finset.filter (fun i => kf i = m) s, (T i).shade)) := by
        gcongr
    _ ≤ 3 * ((((σ * ρ : NNReal)) : ENNReal) ^ (-(ε / 8)) * ((s.card : ENNReal)) ^ γ
          * volume (⋃ i ∈ s, (T i).shade)) := by gcongr
    _ = (3 * (((σ * ρ : NNReal)) : ENNReal) ^ (-(ε / 8))) * (((s.card : ENNReal)) ^ γ
          * volume (⋃ i ∈ s, (T i).shade)) := by ring
    _ ≤ ((ρ : ENNReal)) ^ (-ε) * (((s.card : ENNReal)) ^ γ
          * volume (⋃ i ∈ s, (T i).shade)) := by gcongr
    _ = ((ρ : ENNReal)) ^ (-ε) * ((s.card : ENNReal)) ^ γ
          * volume (⋃ i ∈ s, (T i).shade) := by ring


/-! ## The equivalence, the tripwires, and the circularity -/

/-- The easy direction: `SmallCard` is `K_KT` with the band hypothesis thrown away. -/
theorem smallCard_of_katzTaoEstimate {γ : ℝ} (h : Kakeya.KatzTaoEstimate.{u} Space3 γ) :
    Kakeya.ML2Assembly.SmallCard.{u} γ := by
  intro ε hε
  obtain ⟨η, hη0, hh⟩ := h ε hε
  refine ⟨min η 1, lt_min hη0 zero_lt_one, min_le_right _ _, ?_⟩
  filter_upwards [hh, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hδ hmem
  obtain ⟨hδ0, hδ1⟩ := hmem
  intro ι s T hball hKT hfull _
  refine hδ s T hball ?_ ?_
  · exact Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT
  · exact Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull

/-- **`SmallCard γ ⟺ K_KT γ`.**  The band restriction `|𝕋| < δ^{-1}` of
`Kakeya.ML2Assembly.SmallCard` carries the *entire* weight of the partial Katz--Tao estimate at
the same exponent: it is not a side condition but a restatement.  This is the fidelity compatibility —
if `Kakeya.ML2Assembly.SmallCard` or `Kakeya.KatzTaoEstimate` drifts, this `iff` stops
compiling. -/
theorem smallCard_iff_katzTaoEstimate {γ : ℝ} (hγ : 0 ≤ γ) :
    Kakeya.ML2Assembly.SmallCard.{u} γ ↔ Kakeya.KatzTaoEstimate.{u} Space3 γ :=
  ⟨katzTaoEstimate_of_smallCard hγ, smallCard_of_katzTaoEstimate⟩

/-- **The circularity,.**  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` takes
`hdich` (the geometric core, i.e. GWZ Lemma 9.1 plus the window branch) *and* `hsmall`.  Its
conclusion follows from `hsmall` alone: the dichotomy, the gain budget `4c ≤ g`, the accuracy
budget `2c ≤ β` and Lemma 9.1 are all unused.  The `example` below is the same statement with
*all* the hypotheses of that theorem in scope, so that the unused ones are visible. -/
theorem katzTaoEstimate_sub_of_smallCard_alone {β c : ℝ} (hβc : 0 ≤ β - c)
    (hsmall : Kakeya.ML2Assembly.SmallCard.{u} (β - c)) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  katzTaoEstimate_of_smallCard hβc hsmall

example {β g η c : ℝ} (_hc : 0 < c) (_hcβ : 2 * c ≤ β) (_hη0 : 0 < η) (_hη1 : η ≤ 1)
    (_hg : 4 * c ≤ g) (hβc : 0 ≤ β - c)
    (_hdich : Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2) g η)
    (hsmall : Kakeya.ML2Assembly.SmallCard.{u} (β - c)) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c) :=
  katzTaoEstimate_of_smallCard hβc hsmall

/-- **The decisive compatibility.**  Two proofs can be asserted equal only if they prove the *same*
proposition, and proof irrelevance then makes the equation `rfl`.  So this one line certifies
that `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` — the assembly's exponent-drop step,
which consumes the geometric core through `hdich` — and
`Kakeya.ML2BandSqz.katzTaoEstimate_of_smallCard`, which consumes only `hsmall`, prove *literally
the same statement*, at the same universe, with the same ambient space and the same exponent.

`hdich`, `hc`, `hcβ`, `hη0`, `hη1` and `hg` are therefore all redundant: **the geometric core and
GWZ Lemma 9.1 are not needed for the conclusion the assembly reaches.** -/
theorem dichotomy_route_is_redundant {β g η c : ℝ} (hc : 0 < c) (hcβ : 2 * c ≤ β)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hg : 4 * c ≤ g)
    (hdich : Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2) g η)
    (hsmall : Kakeya.ML2Assembly.SmallCard.{u} (β - c)) :
    Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy hc hcβ hη0 hη1 hg hdich hsmall
      = katzTaoEstimate_of_smallCard (by linarith : (0 : ℝ) ≤ β - c) hsmall := rfl

/-! ## The failed reverse squeeze, as a stated non-theorem

The squeeze is **asymmetric**, and this is why it vacates `Kakeya.ML2Assembly.SmallCard`'s band
`|𝕋| < δ^{-1}` but leaves `Kakeya.ML2Assembly.Dichotomy`'s conjunct `δ⁻¹ ≤ |𝕋|` alone.

* Shrinking `e^⊥` is free: `Kakeya.ML2BandSqz.norm_sqzL_le_abs` says the map is a contraction,
  the image of a `ρ`-tube is a genuine `σρ`-tube
  (`Kakeya.ML2BandSqz.image_subset_centredExtension`) and the whole cost is the *absolute*
  constant `Kakeya.ML2BandSqz.sqzLoss`, which `Kakeya.ML2BandSqz.eventually_const_le_rpow`
  absorbs.
* The reverse — presenting a `ρ`-tube family at a *coarser* scale `δ' > ρ` — costs `(δ'/ρ)²` in
  `Δ_max` and `(ρ/δ')²` in fullness (`Kakeya.ML2BandSqz.volume_coarser_ge`).  To move the
  threshold `δ^{-1}` at all, `δ'/ρ` must be a *power* of `ρ`; the loss is then a power of `ρ`,
  and `Kakeya.ML2BandSqz.not_reverseSqueezeBudget` says no threshold absorbs it.
-/

section Reverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **The squeeze only ever lowers the scale, so it only ever raises the band threshold.**
For every `σ ≤ 1` the squeezed scale is `σρ ≤ ρ`, hence a family already inside the band at `ρ`
is still inside the band at `σρ`.  **No squeeze of this shape can ever supply
`Kakeya.ML2Assembly.Dichotomy`'s hypothesis `δ⁻¹ ≤ |𝕋|`.** -/
theorem sqz_preserves_band {σ ρ : NNReal} (hσ0 : σ ≠ 0) (hσ1 : σ ≤ 1) (hρ0 : 0 < ρ) {n : ℕ}
    (hband : (n : ℝ) < (ρ : ℝ)⁻¹) : (n : ℝ) < ((σ * ρ : NNReal) : ℝ)⁻¹ := by
  have hσp : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hσ0)
  have hρp : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.mpr hρ0
  have hσ1' : (σ : ℝ) ≤ 1 := by exact_mod_cast hσ1
  have hdp : (0 : ℝ) < ((σ * ρ : NNReal) : ℝ) := by push_cast; positivity
  have hle : ((σ * ρ : NNReal) : ℝ) ≤ (ρ : ℝ) := by
    push_cast
    nlinarith [hσ1', hρp]
  have hinv : (ρ : ℝ)⁻¹ ≤ ((σ * ρ : NNReal) : ℝ)⁻¹ := by
    have h := one_div_le_one_div_of_le hdp hle
    rwa [one_div, one_div] at h
  exact lt_of_lt_of_le hband hinv

/-- **The reverse presentation is not free.**  In `ℝ³`, a `ρ`-tube inside a `δ'`-tube forces
`|T'| / |T| ≥ (c₃/C₃)·(δ'/ρ)²`: re-presenting a family at a coarser scale multiplies every
body's volume by `(δ'/ρ)²`, hence multiplies `Δ_max` by that factor and divides the fullness
by it. -/
theorem volume_coarser_ge (hn : Module.finrank ℝ E = 3) {ρ δ' : NNReal} (hρ1 : ρ ≤ 1)
    (T : Tube ρ E) (T' : Tube δ' E) :
    (Tube.le_volume.c 3 : ENNReal) * (δ' : ENNReal) ^ 2 * volume T.carrier
      ≤ (Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2 * volume T'.carrier := by
  have hT : volume T.carrier ≤ (Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2 := by
    have h := Tube.volume_le (E := E) hρ1 T
    rw [hn] at h
    simpa using h
  have hT' : (Tube.le_volume.c 3 : ENNReal) * (δ' : ENNReal) ^ 2 ≤ volume T'.carrier := by
    have h := Tube.le_volume (E := E) T'
    rw [hn] at h
    simpa using h
  calc (Tube.le_volume.c 3 : ENNReal) * (δ' : ENNReal) ^ 2 * volume T.carrier
      ≤ (Tube.le_volume.c 3 : ENNReal) * (δ' : ENNReal) ^ 2
          * ((Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2) := by gcongr
    _ = (Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2
          * ((Tube.le_volume.c 3 : ENNReal) * (δ' : ENNReal) ^ 2) := by ring
    _ ≤ (Tube.volume_le.C 3 : ENNReal) * (ρ : ENNReal) ^ 2 * volume T'.carrier := by gcongr

end Reverse

/-- **The reverse squeeze's budget, as a `Prop`.**  If the coarser presentation is to move the
band threshold, the coarsening ratio must be `δ'/ρ = ρ^{-θ}` for some `θ > 0`, so the loss is
`ρ^{-2θ}`.  This is the assertion that such a loss is absorbed by a subpolynomial budget
`ρ^{-κ}`. -/
def ReverseSqueezeBudget (θ κ : ℝ) : Prop :=
  ∀ ρ : NNReal, 0 < ρ → (ρ : ℝ) < 1 → (ρ : ℝ) ^ (-(2 * θ)) ≤ (ρ : ℝ) ^ (-κ)

/-- **THE REVERSE SQUEEZE FAILS.**  For every `κ < 2θ` the budget is violated at *every*
admissible scale: the loss of the coarser presentation is a fixed power of `ρ`, and the
threshold device `Kakeya.ML2BandSqz.eventually_const_le_rpow` — which absorbs *constants* —
does not touch it.  Contrast `Kakeya.ML2BandSqz.sqzLoss`, an absolute constant.

This is the guard the dispatch asked for: the mechanism that vacates
`Kakeya.ML2Assembly.SmallCard`'s band does **not** vacate
`Kakeya.ML2Assembly.Dichotomy`'s `δ⁻¹ ≤ |𝕋|`. -/
theorem not_reverseSqueezeBudget {θ κ : ℝ} (hθ : 0 < θ) (hκθ : κ < 2 * θ) :
    ¬ ReverseSqueezeBudget θ κ := by
  intro hbud
  have hρ0 : (0 : NNReal) < 1 / 2 := by norm_num
  have hρ1 : ((1 / 2 : NNReal) : ℝ) < 1 := by
    rw [show (((1 / 2 : NNReal)) : ℝ) = 1 / 2 by push_cast; ring]
    norm_num
  have h := hbud (1 / 2) hρ0 hρ1
  have hpos : (0 : ℝ) < (((1 / 2 : NNReal)) : ℝ) := by
    rw [show (((1 / 2 : NNReal)) : ℝ) = 1 / 2 by push_cast; ring]
    norm_num
  have hstrict : (((1 / 2 : NNReal)) : ℝ) ^ (-κ) < (((1 / 2 : NNReal)) : ℝ) ^ (-(2 * θ)) :=
    Real.rpow_lt_rpow_of_exponent_gt hpos hρ1 (by linarith [hθ])
  linarith


/-! ## What must `SmallCard` carry?  The clause calculus

GWZ `section9.tex` (the proof of Main Lemma 2) contains **no cardinality hypothesis at all**.
Its branch (i) reads Theorem 7.3(B) *at the outer `ε`*, obtains `μ(𝕋,Y) ≤ δ^{-ε}`, and closes
because `|𝕋|^{β-ν} ≥ 1`.  The condition `δ⁻¹ ≤ |𝕋|` is the price of Prof. Hong Wang's `ε`-free
repair — reading 7.3(B) at an **absolute** `ε₀` instead, which only gives `μ ≤ δ^{-ε₀}` and
therefore needs `|𝕋|^{β-ν} ≥ δ^{ε-ε₀}`.  The repair is charged in an affinely meaningless
currency: `|𝕋|` is an affine invariant, `δ` is not.

This section is the calculus of "what would have to be added".  A candidate clause is a
predicate on the family; the question is whether it (a) blocks the squeeze and (b) is supplied
by the case split at the call site.  `Kakeya.ML2BandSqz.katzTaoEstimate_of_smallCardWith` shows
**(a) and (b) are mutually exclusive**. -/

section Clauses

/-- An extra clause that a repaired `SmallCard` might carry on the family. -/
def Clause : Type (u + 1) :=
  ∀ (δ : NNReal) (ι : Type u), Finset ι → (ι → ShadedTube δ Space3) → Prop

/-- `Kakeya.ML2Assembly.SmallCard` with the extra clause `P` on the family. -/
def SmallCardWith (P : Clause.{u}) (γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (s.card : ℝ) < (δ : ℝ)⁻¹ →
        P δ ι s T →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ * volume (⋃ i ∈ s, (T i).shade)

/-- **The clause is supplied by the case split, at the exponent `η`.**  In
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` the small-cardinality branch has exactly
four facts about the family available: unit-ball containment, `Δ_max ≤ δ^{-η}`, `λ ≥ δ^η` and
`|𝕋| < δ^{-1}`.  A clause is *usable at `η`* precisely when those four imply it for every
small `δ`. -/
def CallSiteAvailableAt (η : ℝ) (P : Clause.{u}) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) ((δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (s.card : ℝ) < (δ : ℝ)⁻¹ →
      P δ ι s T

/-- **The clause is supplied by the case split.**  Availability at a *single* positive exponent
is enough, because the four facts get stronger as the exponent decreases. -/
def CallSiteAvailable (P : Clause.{u}) : Prop :=
  ∃ η₀ > (0 : ℝ), CallSiteAvailableAt.{u} η₀ P

/-- A usable clause adds nothing: `SmallCardWith P` collapses to `SmallCard`. -/
theorem smallCard_of_smallCardWith {P : Clause.{u}} (hP : CallSiteAvailable.{u} P) {γ : ℝ}
    (h : SmallCardWith.{u} P γ) : Kakeya.ML2Assembly.SmallCard.{u} γ := by
  obtain ⟨η₀, hη₀0, hav⟩ := hP
  intro ε hε
  obtain ⟨η, hη0, hη1, hbody⟩ := h ε hε
  refine ⟨min η η₀, lt_min hη0 hη₀0, le_trans (min_le_left _ _) hη1, ?_⟩
  filter_upwards [hbody, hav, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hb hAv hmem
  obtain ⟨hδ0, hδ1⟩ := hmem
  intro ι s T hball hKT hfull hcard
  -- weaken the two exponent hypotheses from `min η η₀` to each of `η` and `η₀`
  have hKTη : ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
      ((δ : ENNReal) ^ (-η)) :=
    Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_left _ _) hKT
  have hKTη₀ : ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
      ((δ : ENNReal) ^ (-η₀)) :=
    Kakeya.ML2Assembly.isKatzTao_of_exponent_le hδ1.le (min_le_right _ _) hKT
  have hfullη : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η :=
    Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_left _ _) hfull
  have hfullη₀ : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₀ :=
    Kakeya.ML2Assembly.le_of_rpow_exponent_le hδ0 hδ1.le (min_le_right _ _) hfull
  exact hb s T hball hKTη hfullη hcard (hAv s T hball hKTη₀ hfullη₀ hcard)

/-- **THE CLAUSE CALCULUS.**  *No clause the case split can supply blocks the squeeze.*

Strengthening `Kakeya.ML2Assembly.SmallCard` by any clause `P` that the small-cardinality branch
of `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` is able to hand over leaves the
circularity exactly where it was.  Contrapositively: **a clause that blocks the squeeze is a
clause the case split cannot supply**, so it cannot be added to `SmallCard` without also
changing what the *other* branch has to prove.  This is the load-bearing statement of the repair
question, and it is independent of which clause is proposed. -/
theorem katzTaoEstimate_of_smallCardWith {P : Clause.{u}} (hP : CallSiteAvailable.{u} P) {γ : ℝ}
    (hγ : 0 ≤ γ) (h : SmallCardWith.{u} P γ) : Kakeya.KatzTaoEstimate.{u} Space3 γ :=
  katzTaoEstimate_of_smallCard hγ (smallCard_of_smallCardWith hP h)

/-- The contrapositive, in the form the repair question asks for: if the repaired `SmallCard` is
*not* circular, then the repair is not obtainable at the call site. -/
theorem not_callSiteAvailable_of_not_circular {P : Clause.{u}} {γ : ℝ} (hγ : 0 ≤ γ)
    (hblocked : ¬ (SmallCardWith.{u} P γ → Kakeya.KatzTaoEstimate.{u} Space3 γ)) :
    ¬ CallSiteAvailable.{u} P :=
  fun hP => hblocked (katzTaoEstimate_of_smallCardWith hP hγ)

end Clauses

/-! ## The clause GWZ actually has: direction non-concentration ("bilinear"/broad) -/

/-- **Direction non-concentration.**  The formal shadow of the hypothesis Prof. Hong Wang names
when she says *"if `𝕋` is bilinear this is automatic; in the non-bilinear case broad--narrow
supplies the improvement"*: the tube directions are **not** all contained in a single `1/2`-cap.

This is the natural candidate the diagnosis points at — it is not affine invariant, and a
transverse compression destroys it, since the squeeze pushes every direction of a cap to within
angle `≍ σ` of the cap centre. -/
def DirNonConcentrated : Clause.{u} :=
  fun _δ _ι s T => ∀ e : Space3, ‖e‖ = 1 → ∃ i ∈ s, |(inner ℝ e (T i).direction : ℝ)| < 1 / 2

section Blocked

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `⟪e, sqzL e a c u⟫ = a ⟪e, u⟫`: the squeeze acts as the scalar `a` along `e`. -/
theorem inner_sqzL (e : E) (he : ‖e‖ = 1) (a c : ℝ) (u : E) :
    (inner ℝ e (sqzL e a c u) : ℝ) = a * (inner ℝ e u : ℝ) := by
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]; norm_num
  rw [sqzL_apply, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    real_inner_smul_right, hee]
  ring

/-- The image of a unit vector has `‖·‖² ≤ a²(c² + ⟪e,u⟫²)`. -/
theorem norm_sq_sqzL_le_of_unit (e : E) (he : ‖e‖ = 1) (a c : ℝ) {u : E} (hu : ‖u‖ = 1) :
    ‖sqzL e a c u‖ ^ 2 ≤ a ^ 2 * (c ^ 2 + (inner ℝ e u : ℝ) ^ 2) := by
  have hsplit := norm_sq_split e he u
  rw [hu] at hsplit
  have hperp : ‖u - (inner ℝ e u : ℝ) • e‖ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (inner ℝ e u : ℝ)]
  rw [norm_sq_sqzL e he a c u]
  have hnn : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  nlinarith [sq_nonneg (a * c), sq_nonneg c, hperp]

/-- The image core vector of the squeeze. -/
theorem sqz_sub_eq (e : E) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0) (T : Tube ρ E) :
    sqz e he hσ T.y - sqz e he hσ T.x = sqzL e (1 / 4 : ℝ) (σ : ℝ) T.direction := by
  have hAz : ∀ z : E, sqz e he hσ z = sqzL e (1 / 4 : ℝ) (σ : ℝ) z := fun z => rfl
  simp only [hAz]
  rw [← map_sub]

end Blocked

/-- **The squeezed family is cap-concentrated.**  Every tube of the squeezed family has its
direction within the `1/2`-cap of `e`.  This is the sense in which the squeeze
**cannot run** against `Kakeya.ML2BandSqz.DirNonConcentrated`. -/
theorem half_le_inner_sqz_direction (e : Space3) (he : ‖e‖ = 1) {σ ρ : NNReal}
    (hσ : σ ≠ 0) (hσ2 : (σ : ℝ) ≤ 1 / 2) (S : ShadedTube ρ Space3)
    (hcapS : (1 : ℝ) / 2 ≤ |(inner ℝ e S.direction : ℝ)|) :
    (1 : ℝ) / 2 ≤ |(inner ℝ e (sqzShadedTube e he hσ S).direction : ℝ)| := by
  have hσ0 : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hσ)
  set u : Space3 := S.direction with hu
  have hu1 : ‖u‖ = 1 := S.norm_direction
  set α : ℝ := (inner ℝ e u : ℝ) with hα
  set g : Space3 := sqzL e (1 / 4 : ℝ) (σ : ℝ) u with hg
  have hgpos : 0 < ‖g‖ := by
    have h := le_norm_sqzL e he (a := (1 / 4 : ℝ)) (c := (σ : ℝ)) (by norm_num) hσ0
      (by exact_mod_cast (le_trans hσ2 (by norm_num : (1:ℝ)/2 ≤ 1))) u
    rw [hu1, mul_one] at h
    have hp : (0 : ℝ) < 1 / 4 * (σ : ℝ) := by positivity
    rw [hg]; linarith
  have hdir : (sqzShadedTube e he hσ S).direction = ‖g‖⁻¹ • g := by
    show (Tube.centredExtension (σ * ρ) (sqz_x_ne_y e he hσ S.toTube)).direction = _
    rw [Tube.direction_centredExtension, sqz_sub_eq e he hσ S.toTube]
  have hinner : (inner ℝ e (sqzShadedTube e he hσ S).direction : ℝ)
      = ‖g‖⁻¹ * ((1 / 4 : ℝ) * α) := by
    rw [hdir, real_inner_smul_right, hg, inner_sqzL e he]
  have hnormsq : ‖g‖ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 * ((σ : ℝ) ^ 2 + α ^ 2) := by
    rw [hg]; exact norm_sq_sqzL_le_of_unit e he _ _ hu1
  have hα2 : (1 : ℝ) / 4 ≤ α ^ 2 := by nlinarith [abs_nonneg α, sq_abs α]
  have hkey : (1 / 4 : ℝ) ^ 2 * α ^ 2 ≥ (1 / 4 : ℝ) * ‖g‖ ^ 2 := by nlinarith [sq_nonneg (σ : ℝ)]
  rw [hinner, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hgpos))]
  rw [ge_iff_le, ← sub_nonneg] at hkey
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)] at *
  have habs : |(1 / 4 : ℝ) * α| = (1 / 4 : ℝ) * |α| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
  rw [habs]
  rw [inv_mul_eq_div, le_div_iff₀ hgpos]
  nlinarith [abs_nonneg α, sq_abs α, hgpos, hnormsq, hα2, sq_nonneg ((1/4 : ℝ) * |α| - ‖g‖)]


/-! ## (3): the clause is NOT obtainable at the call site -/

section Witness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A one-element family is `1`-Katz--Tao: the only nonempty test set is the body itself. -/
theorem maxDensity_singleton_le_one {ι : Type*} [DecidableEq ι] (i₀ : ι)
    (W : ι → ConvexSpaceBody E) : Kakeya.maxDensity {i₀} W ≤ 1 := by
  rw [Kakeya.maxDensity_le_iff]
  intro K
  rw [Kakeya.densityIn_le_iff, one_mul]
  by_cases h : W i₀ ≤ K
  · rw [Finset.filter_singleton, if_pos h, Finset.sum_singleton]
    exact measure_mono (SetLike.coe_subset_coe.mpr h)
  · rw [Finset.filter_singleton, if_neg h, Finset.sum_empty]
    simp

/-- A one-element fully shaded family has fullness `1`. -/
theorem fullness_singleton_full {ι : Type*} [DecidableEq ι] (i₀ : ι) (V : ι → ShadedBody E)
    (hsh : (V i₀).shade = (V i₀).carrier) (h0 : volume (V i₀).carrier ≠ 0)
    (ht : volume (V i₀).carrier ≠ ⊤) : ShadedBody.fullness {i₀} V = 1 := by
  have hf : ShadedBody.fullness' {i₀} V = 1 := by
    show (∑ i ∈ ({i₀} : Finset ι), volume (V i).shade)
      / (∑ i ∈ ({i₀} : Finset ι), volume (V i).carrier) = 1
    rw [Finset.sum_singleton, Finset.sum_singleton, hsh, ENNReal.div_self h0 ht]
  rw [← ENNReal.coe_inj, ShadedBody.coe_fullness, hf, ENNReal.coe_one]

end Witness

/-- **The fully shaded `δ`-tube through the origin in direction `e`.**  The witness family. -/
noncomputable def unitShadedTube (δ : NNReal) {e : Space3} (he : ‖e‖ = 1) :
    ShadedTube δ Space3 where
  toTube := Tube.ofMidpointDirection δ 0 e he
  shade := (Tube.ofMidpointDirection δ 0 e he).carrier
  measurableSet_shade :=
    (Tube.ofMidpointDirection δ 0 e he).isCompact'.isClosed.measurableSet
  shade_subset := subset_rfl

theorem unitShadedTube_direction (δ : NNReal) {e : Space3} (he : ‖e‖ = 1) :
    (unitShadedTube δ he).direction = e := by
  show (Tube.ofMidpointDirection δ 0 e he).y - (Tube.ofMidpointDirection δ 0 e he).x = e
  rw [Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
  module

theorem unitShadedTube_shade (δ : NNReal) {e : Space3} (he : ‖e‖ = 1) :
    (unitShadedTube δ he).shade = (unitShadedTube δ he).carrier := rfl

theorem unitShadedTube_subset_closedBall {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 2) {e : Space3}
    (he : ‖e‖ = 1) : (unitShadedTube δ he).carrier ⊆ Metric.closedBall (0 : Space3) 1 := by
  have hmid : _root_.midpoint ℝ (Tube.ofMidpointDirection δ (0 : Space3) e he).x
      (Tube.ofMidpointDirection δ (0 : Space3) e he).y = 0 := by
    rw [Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y, midpoint_eq_smul_add,
      invOf_eq_inv]
    module
  have h := Tube.carrier_subset_closedBall_midpoint
    (T := Tube.ofMidpointDirection δ (0 : Space3) e he)
  rw [hmid] at h
  show (Tube.ofMidpointDirection δ (0 : Space3) e he).carrier ⊆ Metric.closedBall (0 : Space3) 1
  refine h.trans (Metric.closedBall_subset_closedBall ?_)
  linarith

theorem volume_unitShadedTube_ne_zero {δ : NNReal} (hδ : δ ≠ 0) {e : Space3} (he : ‖e‖ = 1) :
    volume (unitShadedTube δ he).carrier ≠ 0 := by
  have hn : Module.finrank ℝ Space3 = 3 := by simp
  have h := Tube.le_volume (E := Space3) (Tube.ofMidpointDirection δ (0 : Space3) e he)
  rw [hn] at h
  intro hzero
  rw [show (unitShadedTube δ he).carrier
    = (Tube.ofMidpointDirection δ (0 : Space3) e he).carrier from rfl] at hzero
  rw [hzero] at h
  simp only [nonpos_iff_eq_zero, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
  · exact absurd (pow_eq_zero_iff (by norm_num)|>.mp h) (ENNReal.coe_ne_zero.mpr hδ)

theorem volume_unitShadedTube_ne_top {δ : NNReal} {e : Space3} (he : ‖e‖ = 1) :
    volume (unitShadedTube δ he).carrier ≠ ⊤ :=
  (Tube.ofMidpointDirection δ (0 : Space3) e he).isCompact'.measure_lt_top.ne

/-- **(3) FAILS: `DirNonConcentrated` is not obtainable at the call site.**  A single fully
shaded `δ`-tube is an entirely admissible family for the small-cardinality branch — it lies in
`B₁`, it is `1`-Katz--Tao, it is fully shaded and it has one element — and its single direction
is trivially concentrated in its own cap.  So the branch cannot hand the clause over, and
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`'s case split no longer covers the
complement of `δ⁻¹ ≤ |𝕋|`. -/
theorem not_callSiteAvailable_dirNonConcentrated :
    ¬ CallSiteAvailable.{u} DirNonConcentrated := by
  rintro ⟨η₀, hη₀0, hP⟩
  obtain ⟨δ₀, hδ₀0, hav⟩ := Kakeya.ML2Reduction.exists_threshold_of_eventually_nhdsGT hP
  classical
  set δ : NNReal := min δ₀ (1 / 4) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀0 (by norm_num)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδ4' : (δ : ℝ) ≤ 1 / 4 := by
    have h := NNReal.coe_le_coe.mpr hδ4
    simpa using h
  have hδ1 : δ ≤ 1 := le_trans hδ4 (by rw [← NNReal.coe_le_coe]; norm_num)
  set e : Space3 := capVec 0 with hedef
  have he : ‖e‖ = 1 := norm_capVec 0
  set T : PUnit.{u + 1} → ShadedTube δ Space3 := fun _ => unitShadedTube δ he with hTdef
  set s : Finset PUnit.{u + 1} := {PUnit.unit} with hsdef
  have hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1 :=
    fun _ _ => unitShadedTube_subset_closedBall (by linarith) he
  have hKT : ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
      ((δ : ENNReal) ^ (-η₀)) := by
    rw [ConvexSpaceBody.IsKatzTao_def]
    refine le_trans (maxDensity_singleton_le_one _ _) ?_
    rw [ENNReal.rpow_neg, ENNReal.one_le_inv]
    exact ENNReal.rpow_le_one (by exact_mod_cast hδ1) hη₀0.le
  have hfull : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η₀ := by
    rw [fullness_singleton_full PUnit.unit (fun i ↦ (T i).toShadedBody) rfl
      (volume_unitShadedTube_ne_zero hδ0.ne' he) (volume_unitShadedTube_ne_top he)]
    exact NNReal.rpow_le_one hδ1 hη₀0.le
  have hcard : (s.card : ℝ) < (δ : ℝ)⁻¹ := by
    rw [hsdef, Finset.card_singleton]
    have h1 : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
    rw [Nat.cast_one, lt_inv_comm₀ (by norm_num) h1]
    linarith
  have hgot := hav δ hδ0 hδle s T hball hKT hfull hcard
  obtain ⟨i, hi, hlt⟩ := hgot e he
  rw [hTdef] at hlt
  simp only [unitShadedTube_direction] at hlt
  rw [real_inner_self_eq_norm_sq, he] at hlt
  norm_num at hlt

/-- **The squeezed family is cap-concentrated, hence violates the clause.**  This is the mirror
of `Kakeya.ML2BandSqz.dichotomy_route_is_redundant`: against `DirNonConcentrated` the squeeze
**cannot run**, because the family it manufactures never satisfies the clause. -/
theorem sqzFamily_not_dirNonConcentrated (e : Space3) (he : ‖e‖ = 1) {σ ρ : NNReal}
    (hσ : σ ≠ 0) (hσ2 : (σ : ℝ) ≤ 1 / 2) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube ρ Space3)
    (hcap : ∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) :
    ¬ DirNonConcentrated (σ * ρ) ι s (sqzFamily e he hσ T) := by
  intro hd
  obtain ⟨i, hi, hlt⟩ := hd e he
  exact absurd (half_le_inner_sqz_direction e he hσ hσ2 (T i) (hcap i hi)) (not_le.mpr hlt)

/-- **The verdict on the repair, in one statement.**

*(1)* the clause is `Kakeya.ML2BandSqz.DirNonConcentrated`; *(2)* the squeeze cannot run against
it — every family it manufactures violates it; *(3)* it is **not** obtainable at the call site,
so the small-cardinality branch cannot hand it over.

By `Kakeya.ML2BandSqz.katzTaoEstimate_of_smallCardWith`, (2) and (3) are not independent: *any*
clause with property (2) must fail (3).  The repair therefore cannot be local to `SmallCard`;
the branch structure itself — a cardinality split — has to be replaced by a broad/narrow split,
which is exactly the machinery Prof. Hong Wang names for the non-bilinear case. -/
theorem repair_blocks_but_is_unavailable :
    (∀ (e : Space3) (he : ‖e‖ = 1) {σ ρ : NNReal} (hσ : σ ≠ 0), (σ : ℝ) ≤ 1 / 2 →
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube ρ Space3),
          (∀ i ∈ s, (1 : ℝ) / 2 ≤ |(inner ℝ e (T i).direction : ℝ)|) →
          ¬ DirNonConcentrated (σ * ρ) ι s (sqzFamily e he hσ T))
      ∧ ¬ CallSiteAvailable.{u} DirNonConcentrated := by
  refine ⟨?_, not_callSiteAvailable_dirNonConcentrated⟩
  intro e he σ ρ hσ hσ2 ι s T hcap
  exact sqzFamily_not_dirNonConcentrated e he hσ hσ2 s T hcap


/-! ## The narrower binder of `w08` (`SmallCardCore`): it changes nothing

`w08`'s `Reduction/Assembly.lean` carries a strictly weaker third binder,
`Kakeya.ML2Assembly.SmallCardCore`, which asks for `SmallCard` **only at the single exponent
`γ = β - ν` the assembly consumes**, instead of over a `β`-window.  The narrowing is real, but it
narrows the **Katz--Tao exponent** `γ`, and `γ` is exactly the parameter the squeeze leaves
alone: `Kakeya.ML2BandSqz.katzTaoEstimate_of_smallCard` maps `SmallCard γ` to `K_KT γ` at the
*same* `γ`, needing only `0 ≤ γ`.  So the squeeze runs against `SmallCardCore` verbatim, and it
runs harder: `SmallCardCore` already carries `K_KT β` and `K_F β`, so what it asserts is
literally *"`K_KT β` and `K_F β` imply `K_KT (β - ν)`"* — Main Lemma 2 itself.

The binder that the squeeze *does* move is the **accuracy** `ε` inside `SmallCard`, and that one
cannot be narrowed: `Kakeya.KatzTaoEstimate` is `∀ ε > 0`, so the assembly consumes `hsmall` at
every accuracy.  See `Kakeya.ML2BandSqz.accuracy_halved_of_scale_le_sq` for how much the squeeze
costs there.
-/

section CoreBinder

/-- **A faithful restatement of `w08`'s `Kakeya.ML2Assembly.SmallCardCore`.**  Not an import:
`w08` is a different worktree and its `Reduction/Assembly.lean` is not in this tree.  Every
binder, hypothesis and the conclusion are copied. -/
def SmallCardCoreCopy : Prop :=
  ∀ (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 → 0 < ϖ → 0 < ε₁ →
    (∀ ζ : ℝ, 0 < ζ → 0 < gain ζ) → (∀ ζ : ℝ, 0 < ζ → 0 < dens ζ) →
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    Kakeya.FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    Kakeya.ML2Assembly.SmallCard.{u} (β - Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens)

/-- **`SmallCardCore` is Main Lemma 2 itself.**  With the two standing hypotheses it already
carries, it asserts exactly `K_KT β → K_F β → K_KT (β - ν)`.  The narrower binder is therefore
**not** part of the repair. -/
theorem katzTaoEstimate_sub_of_smallCardCore (h : SmallCardCoreCopy.{u})
    (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ : ℝ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ : ℝ, 0 < ζ → 0 < dens ζ)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : Kakeya.FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3))
      (β - Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens) := by
  have hν : 0 < Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens :=
    Kakeya.ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens
  have h2ν : 2 * Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens ≤ β :=
    Kakeya.ML2Spine.two_spineNu_le hβ hβ1 hϖ hε₁ hgain hdens
  exact katzTaoEstimate_of_smallCard (by linarith)
    (h β ϖ ε₁ gain dens hβ hβ1 hϖ hε₁ hgain hdens hKT hKF)

/-- **The mirror of `Kakeya.ML2BandSqz.dichotomy_route_is_redundant` for `w08`'s interface.**
`w08`'s `exists_drop_of_geometricCore (hcore) (hsmall)` concludes `∃ d > 0, K_KT (β - d)`.  That
conclusion follows from `hsmall` alone: the geometric core `hcore` is still unused. -/
theorem exists_drop_of_smallCardCore (h : SmallCardCoreCopy.{u}) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hKF : Kakeya.FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ d : ℝ, 0 < d ∧ Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - d) := by
  refine ⟨Kakeya.ML2Spine.spineNu β 1 1 (fun _ => 1) (fun _ => 1),
    Kakeya.ML2Spine.spineNu_pos hβ one_pos one_pos (fun _ _ => one_pos) (fun _ _ => one_pos), ?_⟩
  exact katzTaoEstimate_sub_of_smallCardCore h β 1 1 (fun _ => 1) (fun _ => 1) hβ hβ1
    one_pos one_pos (fun _ _ => one_pos) (fun _ _ => one_pos) hKT hKF

end CoreBinder

/-! ## The one binder the squeeze does move: the accuracy, and it costs a factor two -/

/-- **The band forces the squeezed scale below `ρ²`.**  A family with `|𝕋| ≥ ρ^{-2}` — which the
Katz--Tao hypothesis permits, and which is the generic case — can only be squeezed into the band
at a scale `δ < ρ²`. -/
theorem scale_lt_sq_of_band {ρ δ : NNReal} (hρ0 : (0 : ℝ) < (ρ : ℝ)) {n : ℕ}
    (hn : ((ρ : ℝ)) ^ (-2 : ℝ) ≤ (n : ℝ)) (hband : (n : ℝ) < (δ : ℝ)⁻¹) :
    (δ : ℝ) < (ρ : ℝ) ^ (2 : ℝ) := by
  have hp : (0 : ℝ) < (ρ : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hρ0 2
  have hneg : ((ρ : ℝ)) ^ (-2 : ℝ) = ((ρ : ℝ) ^ (2 : ℝ))⁻¹ := Real.rpow_neg hρ0.le 2
  rw [hneg] at hn
  have hinvpos : (0 : ℝ) < (δ : ℝ)⁻¹ := lt_of_le_of_lt (by positivity) hband
  have hδpos : (0 : ℝ) < (δ : ℝ) := by
    rcases lt_or_eq_of_le (NNReal.coe_nonneg δ) with h | h
    · exact h
    · rw [← h] at hinvpos; simp at hinvpos
  have hlt : ((ρ : ℝ) ^ (2 : ℝ))⁻¹ < (δ : ℝ)⁻¹ := lt_of_le_of_lt hn hband
  exact (inv_lt_inv₀ hp hδpos).mp hlt

/-- **A squeeze into `δ ≤ ρ²` costs a factor `2` of accuracy.**  If the conclusion obtained at
the squeezed scale `δ` with accuracy `ε₀` is to pull back to accuracy `ε` at scale `ρ`, then
`2ε₀ ≤ ε`.  Combined with `Kakeya.ML2BandSqz.scale_lt_sq_of_band`, this is why the squeeze
consumes `SmallCard` at a *strictly finer* accuracy than the one it produces, and why the
accuracy binder of `SmallCard` cannot be narrowed to a single value. -/
theorem accuracy_halved_of_scale_le_sq {ρ δ : NNReal} (hρ0 : (0 : ℝ) < (ρ : ℝ))
    (hρ1 : (ρ : ℝ) < 1) (hδ0 : (0 : ℝ) < (δ : ℝ)) (hδ : (δ : ℝ) ≤ (ρ : ℝ) ^ (2 : ℝ))
    {ε ε₀ : ℝ} (hε₀ : 0 < ε₀) (h : (δ : ℝ) ^ (-ε₀) ≤ (ρ : ℝ) ^ (-ε)) : 2 * ε₀ ≤ ε := by
  have hp : (0 : ℝ) < (ρ : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hρ0 2
  have hmono : (δ : ℝ) ^ ε₀ ≤ ((ρ : ℝ) ^ (2 : ℝ)) ^ ε₀ :=
    Real.rpow_le_rpow hδ0.le hδ hε₀.le
  have hd1 : (δ : ℝ) ^ (-ε₀) = ((δ : ℝ) ^ ε₀)⁻¹ := Real.rpow_neg hδ0.le ε₀
  have hd2 : ((ρ : ℝ) ^ (2 : ℝ)) ^ (-ε₀) = (((ρ : ℝ) ^ (2 : ℝ)) ^ ε₀)⁻¹ :=
    Real.rpow_neg hp.le ε₀
  have hge : ((ρ : ℝ) ^ (2 : ℝ)) ^ (-ε₀) ≤ (δ : ℝ) ^ (-ε₀) := by
    rw [hd1, hd2]
    have hx := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hδ0 ε₀) hmono
    rwa [one_div, one_div] at hx
  have hcomp : ((ρ : ℝ) ^ (2 : ℝ)) ^ (-ε₀) = (ρ : ℝ) ^ (-(2 * ε₀)) := by
    rw [← Real.rpow_mul hρ0.le]
    congr 1
    ring
  rw [hcomp] at hge
  by_contra hcon
  push_neg at hcon
  have hstrict : (ρ : ℝ) ^ (-ε) < (ρ : ℝ) ^ (-(2 * ε₀)) :=
    Real.rpow_lt_rpow_of_exponent_gt hρ0 hρ1 (by linarith)
  linarith

end Kakeya.ML2BandSqz
