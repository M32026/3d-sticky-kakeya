/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.BroadNarrow
public import Kakeya.DimensionThree.MainLemma2.Cap.Arith
public import Kakeya.Tube.IntersectionVolume

/-!
# The bilinear broad bound of the Cap Lemma (band item A3)

This file is the *analytic* half of the broad case of the bilinear broad–narrow decomposition
used in the Cap Lemma `L(γ) ⇒ K_KT(γ)` (, band item A3). It
consumes the pointwise combinatorics of `Cap/BroadNarrow.lean` (band item A2) and the exponent
bookkeeping of `Cap/Arith.lean` (band item A1), and produces a bound on the *multiplicity* of a
shaded-tube family whose shade mass is concentrated on the broad set.

## The chain, in order

1. `lintegral_coe_mult` / `lintegral_coe_transverseCount` — the two counting functions of A2
   integrate to what they should: `∫⁻ m = ∑ |Y_i|` and
   `∫⁻ (transverse count) = ∑_{(i,j) transverse} |Y_i ∩ Y_j|`. Both go through
   `MeasureTheory.lintegral_finsetSum` on the indicator-sum definitions.
2. `setLIntegral_broad_sq_le_transverse` — integrate A2's pointwise bound
   `enn_broad_sq_le_two_mul_transverse_pairs` over the broad set.
3. `lintegral_broad_sq_le` — **the first contract statement.** Feed the two-tube intersection
   bound `Tube.volume_inter_le_of_angle` into step 2:
   `∫⁻_B m ^ 2 ≤ 2 · C · N ^ 2 · δ ^ (n-1) · (δ / t)`, `N = |𝕋|`, `t` the transversality
   threshold. In `n = 3` at `t = 2 θ` this is `C N² δ³ / θ` (`lintegral_broad_sq_le_three`),
   which is the `2 N² C₀ δ³ / θ` of the plan.
4. `sq_setLIntegral_le_measure_mul_setLIntegral_sq` — Cauchy–Schwarz in `ℝ≥0∞`
   (`ENNReal.lintegral_mul_le_Lp_mul_Lq` at `p = q = 2`): `(∫⁻_B f) ^ 2 ≤ |B| · ∫⁻_B f ^ 2`.
5. `mult_le_of_broad_dominated` — **the second contract statement.** If at least half the shade
   mass sits on the broad set then `μ ≤ 8 C N δ / (t λ c₀)` with `c₀ = Tube.le_volume.c n`.
6. `broad_level_mult_le` — **the level bound**, at `t = 2 θ`, `r = 4 θ`, `θ = δ ^ c`: apply
   `Kakeya.ML2Cap.Arith.broad_level` to get
   `μ ≤ (4 C / c₀) · N ^ γ · δ ^ (γ - c) · λ ^ (-2)`.
   `exists_broad_level_const` packages it with the constant existentially quantified, in the same
   shape as `Tube.volume_inter_le_of_angle` itself, so the constant is independent of the index
   type, the family and the scale.

## Where the gain comes from — read this before using `broad_level_mult_le`

`Arith.broad_level` **does not use its `c ≤ γ` binder** : the
inequality `N δ / (δ ^ c λ ^ 2) ≤ N ^ γ δ ^ (γ - c) λ ^ (-2)` is an identity-plus-`N ≤ δ⁻¹` fact
and is true for *every* `c`. What `c ≤ γ` buys is that the factor `δ ^ (γ - c)` is a **gain**
rather than a loss, and that is the separate lemma `Arith.gain_is_positive_power`.

Accordingly `broad_level_mult_le` keeps `δ ^ (γ - c)` **explicit** in its conclusion — that factor
is what the cap induction spends against the fullness loss `λ ^ (-2)` — and
`broad_level_mult_le_of_gain` is the corollary that *removes* it, its proof being exactly one
application of `Arith.gain_is_positive_power`. So the gain of this file is named, and it is named
there and nowhere else.

## Constants, and the corrected cap radius

 states the cap radius as `3 θ`. That is **wrong**: `Tube.sphere_sep_net`
covers the unit sphere only within `2 θ` , so A2's
statements take the cap radius `r` as a parameter under `t + 2 * θ ≤ r`, and the plan's
transversality threshold `t = 2 θ` forces `r = 4 θ`. Every statement here that fixes the radius
fixes it at `4 * θ`; the workhorse lemmas keep `t` and `r` as parameters with A2's side condition,
so no constant is baked in silently.

The multiplicity constant achieved is `8 C / c₀` at general `t` and `4 C / c₀` at `t = 2 θ`, where
`C` is the constant of `Tube.volume_inter_le_of_angle` and `c₀ = Tube.le_volume.c n` the lower
tube-volume constant. It is *sharper in the fullness* than the plan's `C₃ N δ / (λ ^ 2 θ)`: the
proof bounds `μ = ∑|Y| / |U|` by `8 Q / ∑|Y|` and uses the fullness lower bound on `∑|Y|` once, not
twice, so the honest exponent is `λ ^ (-1)`. The `λ ^ (-2)` of `broad_level_mult_le` appears only
because `Arith.broad_level` is stated with `λ ^ 2`, and `λ ≤ 1` makes that a weakening.

No `axiom`, `opaque` or `native_decide`; no dependence on the abandoned Wang–Zahl route.
-/

@[expose] public section

open MeasureTheory Kakeya.CapBroadNarrow

namespace Kakeya.CapBroadBound

universe u v

/-! ### Cauchy–Schwarz in `ℝ≥0∞` -/

/-- **Cauchy–Schwarz on a set, in `ℝ≥0∞`.** `(∫⁻_B f) ^ 2 ≤ μ B · ∫⁻_B f ^ 2`, obtained from
`ENNReal.lintegral_mul_le_Lp_mul_Lq` at `p = q = 2` with `g = 1`. No finiteness or integrability
hypothesis is needed — this is the `ℝ≥0∞` statement. -/
theorem sq_setLIntegral_le_measure_mul_setLIntegral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (B : Set α) {f : α → ENNReal} (hf : Measurable f) :
    (∫⁻ x in B, f x ∂μ) ^ 2 ≤ μ B * ∫⁻ x in B, f x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict B) Real.HolderConjugate.two_two
    (f := f) (g := fun _ => (1 : ENNReal)) hf.aemeasurable measurable_const.aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at h
  have h2 : ∀ x, f x ^ (2 : ℝ) = f x ^ (2 : ℕ) := fun x => by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  simp only [h2] at h
  calc (∫⁻ x in B, f x ∂μ) ^ 2
      ≤ ((∫⁻ x in B, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (μ B) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = μ B * ∫⁻ x in B, f x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ x in B, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ))) 2,
          ← ENNReal.rpow_natCast ((μ B) ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        ring

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type v} {δ : NNReal}

/-! ### The two counting functions integrate to the two sums -/

omit [BorelSpace E] in
/-- `m(x)` pushed into `ℝ≥0∞` is the sum of the `ℝ≥0∞`-valued shade indicators. -/
theorem coe_mult (s : Finset ι) (T : ι → ShadedTube δ E) (x : E) :
    ((mult s T x : ℕ) : ENNReal)
      = ∑ i ∈ s, ((T i).shade).indicator (fun _ => (1 : ENNReal)) x := by
  simp only [mult, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x ∈ (T i).shade <;> simp [h]

/-- `∫⁻ m = ∑ |Y_i|`: the total shade mass is the integral of the multiplicity function. -/
theorem lintegral_coe_mult (s : Finset ι) (T : ι → ShadedTube δ E) :
    ∫⁻ x, ((mult s T x : ℕ) : ENNReal) = ∑ i ∈ s, volume (T i).shade := by
  rw [funext fun x => coe_mult s T x,
    lintegral_finsetSum (f := fun i x => ((T i).shade).indicator (fun _ => (1 : ENNReal)) x)
      s fun i _ => measurable_const.indicator (T i).measurableSet_shade]
  exact Finset.sum_congr rfl fun i _ => by
    rw [lintegral_indicator_const (T i).measurableSet_shade, one_mul]

/-- `∫⁻ (transverse pair count) = ∑_{(i,j) transverse} |Y_i ∩ Y_j|`. This is the entry point for
`Tube.volume_inter_le_of_angle`. -/
theorem lintegral_coe_transverseCount (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) :
    ∫⁻ x, ((transverseCount s T t x : ℕ) : ENNReal)
      = ∑ q ∈ transverseSet s T t, volume ((T q.1).shade ∩ (T q.2).shade) := by
  rw [funext fun x => coe_transverseCount s T t x,
    lintegral_finsetSum
      (f := fun q x => ((T q.1).shade ∩ (T q.2).shade).indicator (fun _ => (1 : ENNReal)) x)
      (transverseSet s T t) fun q _ => measurable_const.indicator
        ((T q.1).measurableSet_shade.inter (T q.2).measurableSet_shade)]
  exact Finset.sum_congr rfl fun q _ => by
    rw [lintegral_indicator_const
      ((T q.1).measurableSet_shade.inter (T q.2).measurableSet_shade), one_mul]

omit [BorelSpace E] in
/-- A point of positive multiplicity lies in the shaded union. -/
theorem mem_iUnionShade_of_mult_pos (s : Finset ι) (T : ι → ShadedTube δ E) {x : E}
    (h : 0 < mult s T x) : x ∈ ⋃ i ∈ s, (T i).shade := by
  by_contra hx
  have h0 : mult s T x = 0 := by
    simp only [mult]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hni : x ∉ (T i).shade := fun hmem => hx (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩)
    simp [hni]
  omega

omit [BorelSpace E] in
/-- **The broad set sits inside the shaded union**, as soon as the net has at least one point:
broadness at a net point `p` forces `0 ≤ 2 m_p(x) < m(x)`. This is what lets Cauchy–Schwarz be
run against `|U|` rather than against `|B|`. -/
theorem broadSet_subset_iUnionShade {θ r : ℝ} (P : DirNet E θ) (hP : P.points.Nonempty)
    (s : Finset ι) (T : ι → ShadedTube δ E) :
    broadSet P.points s T r ⊆ ⋃ i ∈ s, (T i).shade := by
  intro x hx
  obtain ⟨p, hp⟩ := hP
  exact mem_iUnionShade_of_mult_pos s T
    (lt_of_le_of_lt (Nat.zero_le _) (mem_broadSet.mp hx p hp))

/-! ### The transverse-pair mass -/

/-- The angle-transversality bound of `Tube.volume_inter_le_of_angle`, read at a *fixed* scale
`δ`. Stated as an abbreviation so a caller can supply it from the tree lemma's existential and so
no lemma below repeats the shape. -/
abbrev IsAngleInterBound (δ : NNReal) (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (C : ℝ) : Prop :=
  ∀ T₁ T₂ : Tube δ E, volume.real (T₁.carrier ∩ T₂.carrier) ≤
    C * (δ : ℝ) ^ (Module.finrank ℝ E - 1) *
      min 1 ((δ : ℝ) / max (min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖)
        (δ : ℝ))

omit [BorelSpace E] in
/-- The transverse pairs are a sub-family of `s ×ˢ s`, so there are at most `N ^ 2` of them. -/
theorem card_transverseSet_le (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) :
    (transverseSet s T t).card ≤ s.card ^ 2 := by
  classical
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  rw [Finset.card_product, sq]

/-- A single transverse pair of shades has intersection volume `≤ C δ^(n-1) (δ / t)`: pass to the
carriers, then use the two-tube bound with `min 1 (δ / max ∠ δ) ≤ δ / ∠ ≤ δ / t`. -/
theorem volume_inter_shade_le_of_mem_transverseSet {C t : ℝ} (hC0 : 0 ≤ C) (ht : 0 < t)
    (hC : IsAngleInterBound δ E C) (s : Finset ι) (T : ι → ShadedTube δ E) {q : ι × ι}
    (hq : q ∈ transverseSet s T t) :
    volume ((T q.1).shade ∩ (T q.2).shade)
      ≤ ENNReal.ofReal (C * (δ : ℝ) ^ (Module.finrank ℝ E - 1) * ((δ : ℝ) / t)) := by
  have hne : volume ((T q.1).toTube.carrier ∩ (T q.2).toTube.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top (T q.1).toTube.isCompact.measure_ne_top
      (measure_mono Set.inter_subset_left)
  refine le_trans (measure_mono (Set.inter_subset_inter (T q.1).shade_subset
    (T q.2).shade_subset)) ?_
  rw [← ENNReal.ofReal_toReal hne]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (hC (T q.1).toTube (T q.2).toTube).trans ?_
  have hmax : t ≤ max (min ‖(T q.1).direction - (T q.2).direction‖
      ‖(T q.1).direction + (T q.2).direction‖) (δ : ℝ) :=
    le_trans (mem_transverseSet.mp hq).2 (le_max_left _ _)
  exact mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (div_le_div_of_nonneg_left (by positivity) ht hmax))
    (by positivity)

/-- The total transverse-pair mass: `∑_{(i,j) transverse} |Y_i ∩ Y_j| ≤ C N² δ^(n-1) (δ / t)`. -/
theorem sum_volume_transverse_le {C t : ℝ} (hC0 : 0 ≤ C) (ht : 0 < t)
    (hC : IsAngleInterBound δ E C) (s : Finset ι) (T : ι → ShadedTube δ E) :
    ∑ q ∈ transverseSet s T t, volume ((T q.1).shade ∩ (T q.2).shade)
      ≤ ENNReal.ofReal (C * (s.card : ℝ) ^ 2 * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
          * ((δ : ℝ) / t)) := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ _ fun q hq =>
    volume_inter_shade_le_of_mem_transverseSet hC0 ht hC s T hq) ?_
  rw [nsmul_eq_mul]
  have hcard : (((transverseSet s T t).card : ℕ) : ENNReal) ≤ ((s.card ^ 2 : ℕ) : ENNReal) :=
    Nat.cast_le.mpr (card_transverseSet_le s T t)
  have hcast : ((s.card ^ 2 : ℕ) : ENNReal) = ENNReal.ofReal ((s.card : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    ring_nf
  calc (((transverseSet s T t).card : ℕ) : ENNReal)
        * ENNReal.ofReal (C * (δ : ℝ) ^ (Module.finrank ℝ E - 1) * ((δ : ℝ) / t))
      ≤ ENNReal.ofReal ((s.card : ℝ) ^ 2)
        * ENNReal.ofReal (C * (δ : ℝ) ^ (Module.finrank ℝ E - 1) * ((δ : ℝ) / t)) := by
        rw [← hcast]; gcongr
    _ = ENNReal.ofReal (C * (s.card : ℝ) ^ 2 * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
          * ((δ : ℝ) / t)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The broad `L²` bound -/

/-- Integrating A2's pointwise broad inequality: `∫⁻_B m ^ 2 ≤ 2 ∑_{transverse} |Y_i ∩ Y_j|`.
The cap radius `r` and the transversality threshold `t` are parameters, with A2's side condition
`t + 2 θ ≤ r` (the net covers only within `2 θ`). -/
theorem setLIntegral_broad_sq_le_transverse {θ : ℝ} (P : DirNet E θ) (s : Finset ι)
    (T : ι → ShadedTube δ E) {t r : ℝ} (hr : t + 2 * θ ≤ r) :
    ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal) ^ 2
      ≤ 2 * ∑ q ∈ transverseSet s T t, volume ((T q.1).shade ∩ (T q.2).shade) := by
  calc ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal) ^ 2
      ≤ ∫⁻ x in broadSet P.points s T r, 2 * ((transverseCount s T t x : ℕ) : ENNReal) :=
        setLIntegral_mono' (measurableSet_broadSet P.points s T r)
          fun _ hx => enn_broad_sq_le_two_mul_transverse_pairs P hr hx
    _ ≤ ∫⁻ x, 2 * ((transverseCount s T t x : ℕ) : ENNReal) :=
        setLIntegral_le_lintegral _ _
    _ = 2 * ∫⁻ x, ((transverseCount s T t x : ℕ) : ENNReal) :=
        lintegral_const_mul 2 (measurable_coe_transverseCount s T t)
    _ = 2 * ∑ q ∈ transverseSet s T t, volume ((T q.1).shade ∩ (T q.2).shade) := by
        rw [lintegral_coe_transverseCount]

/-- **A3, contract statement 1.** `∫⁻_B m ^ 2 ≤ 2 C N² δ^(n-1) (δ / t)`: the bilinear `L²` bound
on the broad set, with `C` the constant of `Tube.volume_inter_le_of_angle`. -/
theorem lintegral_broad_sq_le {C θ t r : ℝ} (hC0 : 0 ≤ C) (ht : 0 < t)
    (hC : IsAngleInterBound δ E C) (P : DirNet E θ) (hr : t + 2 * θ ≤ r)
    (s : Finset ι) (T : ι → ShadedTube δ E) :
    ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal) ^ 2
      ≤ 2 * ENNReal.ofReal (C * (s.card : ℝ) ^ 2 * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
          * ((δ : ℝ) / t)) := by
  refine (setLIntegral_broad_sq_le_transverse P s T hr).trans ?_
  gcongr
  exact sum_volume_transverse_le hC0 ht hC s T

/-- The plan's shape of contract statement 1, in the ambient dimension `3` at the plan's
transversality threshold `t = 2 θ` and hence at the corrected cap radius `r = 4 θ`:
`∫⁻_B m ^ 2 ≤ C N² δ³ / θ`. -/
theorem lintegral_broad_sq_le_three {C θ : ℝ} (hC0 : 0 ≤ C) (hθ : 0 < θ)
    (hdim : Module.finrank ℝ E = 3) (hC : IsAngleInterBound δ E C) (P : DirNet E θ)
    (s : Finset ι) (T : ι → ShadedTube δ E) :
    ∫⁻ x in broadSet P.points s T (4 * θ), ((mult s T x : ℕ) : ENNReal) ^ 2
      ≤ ENNReal.ofReal (C * (s.card : ℝ) ^ 2 * (δ : ℝ) ^ 3 / θ) := by
  have h := lintegral_broad_sq_le (δ := δ) (C := C) (t := 2 * θ) (r := 4 * θ) hC0 (by linarith)
    hC P (by linarith) s T
  refine h.trans ?_
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hdim, show (3 : ℕ) - 1 = 2 from rfl]
  have hne : θ ≠ 0 := ne_of_gt hθ
  field_simp
  exact le_rfl

/-! ### From broad domination to a multiplicity bound -/

/-- **A3, contract statement 2.** If at least half the shade mass of the family sits on the broad
set — `∑ |Y_i| ≤ 2 ∫⁻_B m` — then

`μ ≤ 8 C N δ / (t λ c₀)`,  `c₀ = Tube.le_volume.c n`.

Proof: Cauchy–Schwarz against `|U|` (legitimate because `B ⊆ U`, `broadSet_subset_iUnionShade`)
turns the `L²` bound `lintegral_broad_sq_le` into `(∑|Y|)² ≤ 8 Q |U|`, and `μ = ∑|Y| / |U|` is
therefore `≤ 8 Q / ∑|Y|`; the fullness lower bound `λ N c₀ δ^(n-1) ≤ ∑|Y|`
(`ShadedBody.coe_fullness_mul_le_sum_volume_shade` with `Tube.le_volume`) finishes it.

Note the fullness enters **once**, giving `λ⁻¹` and not the plan's `λ⁻²`. -/
theorem mult_le_of_broad_dominated (hn : 1 < Module.finrank ℝ E)
    {C θ t r : ℝ} (hC0 : 0 ≤ C) (ht : 0 < t) (hC : IsAngleInterBound δ E C) (hδ0 : 0 < δ)
    (P : DirNet E θ) (hP : P.points.Nonempty) (hr : t + 2 * θ ≤ r)
    (s : Finset ι) (T : ι → ShadedTube δ E) (hs : 0 < s.card)
    {l : NNReal} (hl0 : 0 < l) (hl : l ≤ ShadedBody.fullness s fun i => (T i).toShadedBody)
    (hdom : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal)) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ ENNReal.ofReal (8 * C * (s.card : ℝ) * (δ : ℝ)
          / (t * (l : ℝ) * (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))) := by
  have hfr : 0 < Module.finrank ℝ E := by omega
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hfr
  set n := Module.finrank ℝ E with hn_def
  set c₀ : NNReal := Tube.le_volume.c n with hc₀
  have hc₀0 : (0 : ℝ) < (c₀ : ℝ) := by
    rw [hc₀]; exact_mod_cast Tube.le_volume.c_pos n
  have hδ0r : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hl0r : (0 : ℝ) < (l : ℝ) := NNReal.coe_pos.mpr hl0
  have hcard0 : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs
  set Qr : ℝ := C * (s.card : ℝ) ^ 2 * (δ : ℝ) ^ (n - 1) * ((δ : ℝ) / t) with hQr
  set Dr : ℝ := (l : ℝ) * ((s.card : ℝ) * ((c₀ : ℝ) * (δ : ℝ) ^ (n - 1))) with hDr
  set Kr : ℝ := 8 * C * (s.card : ℝ) * (δ : ℝ) / (t * (l : ℝ) * (c₀ : ℝ)) with hKr
  have hQr0 : 0 ≤ Qr := by rw [hQr]; positivity
  have hDr0 : 0 < Dr := by rw [hDr]; positivity
  have hKr0 : 0 ≤ Kr := by rw [hKr]; positivity
  -- the four analytic inputs
  have hCS : (∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal)) ^ 2
      ≤ volume (broadSet P.points s T r)
        * ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal) ^ 2 :=
    sq_setLIntegral_le_measure_mul_setLIntegral_sq _ _ (measurable_coe_mult s T)
  have hBU : volume (broadSet P.points s T r) ≤ volume (⋃ i ∈ s, (T i).shade) :=
    measure_mono (broadSet_subset_iUnionShade P hP s T)
  have hsq : ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal) ^ 2
      ≤ 2 * ENNReal.ofReal Qr := by
    rw [hQr, hn_def]; exact lintegral_broad_sq_le hC0 ht hC P hr s T
  have hD : ENNReal.ofReal Dr ≤ ∑ i ∈ s, volume (T i).shade := by
    have hlow := ShadedBody.coe_fullness_mul_le_sum_volume_shade s
      (fun i => (T i).toShadedBody) hl
      (c := ((c₀ : NNReal) : ENNReal) * (δ : ENNReal) ^ (n - 1))
      (fun i _ => by rw [hc₀, hn_def]; exact Tube.le_volume (T i).toTube)
    refine le_trans (le_of_eq ?_) hlow
    rw [hDr, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast]
    simp only [ENNReal.ofReal_coe_nnreal]
  -- square the domination hypothesis
  have hS2 : (∑ i ∈ s, volume (T i).shade) ^ 2
      ≤ 8 * ENNReal.ofReal Qr * volume (⋃ i ∈ s, (T i).shade) := by
    calc (∑ i ∈ s, volume (T i).shade) ^ 2
        ≤ (2 * ∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal)) ^ 2 := by gcongr
      _ = 4 * (∫⁻ x in broadSet P.points s T r, ((mult s T x : ℕ) : ENNReal)) ^ 2 := by ring
      _ ≤ 4 * (volume (⋃ i ∈ s, (T i).shade) * (2 * ENNReal.ofReal Qr)) := by
          gcongr
          exact hCS.trans (by gcongr)
      _ = 8 * ENNReal.ofReal Qr * volume (⋃ i ∈ s, (T i).shade) := by ring
  -- the constant identity
  have hkey : ENNReal.ofReal Kr * ENNReal.ofReal Dr = 8 * ENNReal.ofReal Qr := by
    rw [← ENNReal.ofReal_mul hKr0,
      show (8 : ENNReal) = ENNReal.ofReal 8 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [hKr, hDr, hQr]
    field_simp
  rw [ShadedBody.multiplicity_le_iff]
  have hcancel : ENNReal.ofReal Dr * (∑ i ∈ s, volume (T i).shade)
      ≤ ENNReal.ofReal Dr
        * (ENNReal.ofReal Kr * volume (⋃ i ∈ s, ((fun i => (T i).toShadedBody) i).shade)) := by
    calc ENNReal.ofReal Dr * (∑ i ∈ s, volume (T i).shade)
        ≤ (∑ i ∈ s, volume (T i).shade) * (∑ i ∈ s, volume (T i).shade) := by gcongr
      _ = (∑ i ∈ s, volume (T i).shade) ^ 2 := by ring
      _ ≤ 8 * ENNReal.ofReal Qr * volume (⋃ i ∈ s, (T i).shade) := hS2
      _ = (ENNReal.ofReal Kr * ENNReal.ofReal Dr) * volume (⋃ i ∈ s, (T i).shade) := by
          rw [hkey]
      _ = ENNReal.ofReal Dr * (ENNReal.ofReal Kr * volume (⋃ i ∈ s, (T i).shade)) := by ring
  exact (ENNReal.mul_le_mul_iff_right (by
    simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hDr0) ENNReal.ofReal_ne_top).mp hcancel

/-! ### The level bound -/

/-- **A3's endpoint: the broad case at one level.** At angular scale `θ = δ ^ c`, transversality
threshold `t = 2 θ` and cap radius `r = 4 θ` ,
broad domination gives

`μ ≤ (4 C / c₀) · N ^ γ · δ ^ (γ - c) · (λ ^ 2)⁻¹`.

The factor `δ ^ (γ - c)` is kept **explicit**: it is the *gain* the cap induction spends, and
`Kakeya.ML2Cap.Arith.broad_level` — which is what produces it — does **not** use its `c ≤ γ`
binder, so nothing in this inequality alone certifies that the factor is `≤ 1`. That is
`Arith.gain_is_positive_power`, applied in `broad_level_mult_le_of_gain`. -/
theorem broad_level_mult_le (hn : 1 < Module.finrank ℝ E)
    {C θ γ c : ℝ} (hC0 : 0 ≤ C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hc0 : 0 ≤ c) (hcγ : c ≤ γ) (hγ1 : γ ≤ 1) (hθ : θ = (δ : ℝ) ^ c)
    (hC : IsAngleInterBound δ E C) (P : DirNet E θ) (hP : P.points.Nonempty)
    (s : Finset ι) (T : ι → ShadedTube δ E)
    (hN1 : 1 ≤ (s.card : ℝ)) (hNδ : (s.card : ℝ) ≤ (δ : ℝ)⁻¹)
    {l : NNReal} (hl0 : 0 < l) (hl : l ≤ ShadedBody.fullness s fun i => (T i).toShadedBody)
    (hdom : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∫⁻ x in broadSet P.points s T (4 * θ), ((mult s T x : ℕ) : ENNReal)) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ ENNReal.ofReal (4 * C / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
          * ((s.card : ℝ) ^ γ * (δ : ℝ) ^ (γ - c) * (((l : ℝ) ^ 2)⁻¹))) := by
  have hδ0r : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hδ1r : (δ : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hδ1
  have hl0r : (0 : ℝ) < (l : ℝ) := NNReal.coe_pos.mpr hl0
  have hl1r : (l : ℝ) ≤ 1 := by
    have := hl.trans (ShadedBody.fullness_le_one s fun i => (T i).toShadedBody)
    exact_mod_cast this
  have hθ0 : 0 < θ := by rw [hθ]; exact Real.rpow_pos_of_pos hδ0r c
  have hcard : 0 < s.card := by
    by_contra hcon
    have : s.card = 0 := by omega
    rw [this] at hN1; norm_num at hN1
  have hc₀0 : (0 : ℝ) < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
  refine (mult_le_of_broad_dominated hn hC0 (by linarith : (0 : ℝ) < 2 * θ) hC hδ0 P hP
    (by linarith) s T hcard hl0 hl hdom).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  set N : ℝ := (s.card : ℝ) with hN
  set cc : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hcc
  -- `broad_level` at `θ = δ ^ c`, weakened from `λ` to `λ ^ 2`
  have hll : (l : ℝ) ^ 2 ≤ (l : ℝ) := by nlinarith
  have hstep : N * (δ : ℝ) / ((δ : ℝ) ^ c * (l : ℝ))
      ≤ N * (δ : ℝ) / ((δ : ℝ) ^ c * (l : ℝ) ^ 2) := by
    have hpc : (0 : ℝ) < (δ : ℝ) ^ c := Real.rpow_pos_of_pos hδ0r c
    refine div_le_div_of_nonneg_left (by rw [hN]; positivity) (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hll hpc.le
  have hbl := Kakeya.ML2Cap.Arith.broad_level (N := N) (δ := (δ : ℝ)) (γ := γ) (c := c)
    (l := (l : ℝ)) hN1 hNδ hδ0r hδ1r hc0 hcγ hγ1 hl0r
  have heq : 8 * C * N * (δ : ℝ) / (2 * θ * (l : ℝ) * cc)
      = 4 * C / cc * (N * (δ : ℝ) / ((δ : ℝ) ^ c * (l : ℝ))) := by
    rw [hθ]
    have hpc : (0 : ℝ) ≠ (δ : ℝ) ^ c := (Real.rpow_pos_of_pos hδ0r c).ne
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hstep.trans hbl) (by positivity)

/-- The gain, taken from where it lives. `Kakeya.ML2Cap.Arith.gain_is_positive_power` is the
statement that `δ ^ (γ - c) ≤ 1` under `c ≤ γ`; dropping that factor from
`broad_level_mult_le` therefore gives a level bound with **no** `δ`-loss at all:

`μ ≤ (4 C / c₀) · N ^ γ · (λ ^ 2)⁻¹`.

This is the only place a `c ≤ γ` hypothesis does any work in this file, and it is the point of
the broad case: the cardinality-weighted target `N ^ γ` pays the angular loss `θ⁻¹ = δ ^ (-c)`
outright. -/
theorem broad_level_mult_le_of_gain (hn : 1 < Module.finrank ℝ E)
    {C θ γ c : ℝ} (hC0 : 0 ≤ C) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hc0 : 0 ≤ c) (hcγ : c ≤ γ) (hγ1 : γ ≤ 1) (hθ : θ = (δ : ℝ) ^ c)
    (hC : IsAngleInterBound δ E C) (P : DirNet E θ) (hP : P.points.Nonempty)
    (s : Finset ι) (T : ι → ShadedTube δ E)
    (hN1 : 1 ≤ (s.card : ℝ)) (hNδ : (s.card : ℝ) ≤ (δ : ℝ)⁻¹)
    {l : NNReal} (hl0 : 0 < l) (hl : l ≤ ShadedBody.fullness s fun i => (T i).toShadedBody)
    (hdom : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∫⁻ x in broadSet P.points s T (4 * θ), ((mult s T x : ℕ) : ENNReal)) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ ENNReal.ofReal (4 * C / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
          * ((s.card : ℝ) ^ γ * (((l : ℝ) ^ 2)⁻¹))) := by
  have hδ0r : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hδ1r : (δ : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hδ1
  have hl0r : (0 : ℝ) < (l : ℝ) := NNReal.coe_pos.mpr hl0
  have hgain : (δ : ℝ) ^ (γ - c) ≤ 1 :=
    Kakeya.ML2Cap.Arith.gain_is_positive_power hδ0r hδ1r hcγ
  have hc₀0 : (0 : ℝ) < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
  refine (broad_level_mult_le hn hC0 hδ0 hδ1 hc0 hcγ hγ1 hθ hC P hP s T hN1 hNδ hl0 hl
    hdom).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hNγ : (0 : ℝ) ≤ (s.card : ℝ) ^ γ := Real.rpow_nonneg (by positivity) γ
  have : (s.card : ℝ) ^ γ * (δ : ℝ) ^ (γ - c) * (((l : ℝ) ^ 2)⁻¹)
      ≤ (s.card : ℝ) ^ γ * (((l : ℝ) ^ 2)⁻¹) := by
    have h1 : (s.card : ℝ) ^ γ * (δ : ℝ) ^ (γ - c) ≤ (s.card : ℝ) ^ γ := by
      nlinarith [Real.rpow_nonneg (le_of_lt hδ0r) (γ - c)]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **The broad level bound with the constant existentially quantified**, in exactly the shape of
`Tube.volume_inter_le_of_angle` itself: one constant `C₃ > 0`, depending only on the ambient
space, serving every scale `δ`, every index type, every family and every exponent pair. This is
the form the cap induction consumes. -/
theorem exists_broad_level_const (hn : 1 < Module.finrank ℝ E) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 → ∀ {θ γ c : ℝ}, 0 ≤ c → c ≤ γ → γ ≤ 1 →
      θ = (δ : ℝ) ^ c → ∀ (P : DirNet E θ), P.points.Nonempty →
      ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
        1 ≤ (s.card : ℝ) → (s.card : ℝ) ≤ (δ : ℝ)⁻¹ →
      ∀ {l : NNReal}, 0 < l → l ≤ ShadedBody.fullness s (fun i => (T i).toShadedBody) →
      (∑ i ∈ s, volume (T i).shade
        ≤ 2 * ∫⁻ x in broadSet P.points s T (4 * θ), ((mult s T x : ℕ) : ENNReal)) →
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        ≤ ENNReal.ofReal (C₃ * ((s.card : ℝ) ^ γ * (δ : ℝ) ^ (γ - c) * (((l : ℝ) ^ 2)⁻¹))) := by
  obtain ⟨C, hC0, hC⟩ := Tube.volume_inter_le_of_angle (E := E) hn
  have hc₀0 : (0 : ℝ) < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
  refine ⟨4 * C / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ), by positivity, ?_⟩
  intro δ hδ0 hδ1 θ γ c hc0 hcγ hγ1 hθ P hP ι s T hN1 hNδ l hl0 hl hdom
  exact broad_level_mult_le hn hC0.le hδ0 hδ1 hc0 hcγ hγ1 hθ
    (fun T₁ T₂ => hC hδ0 hδ1 T₁ T₂) P hP s T hN1 hNδ hl0 hl hdom

end Kakeya.CapBroadBound
