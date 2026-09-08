/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Pi.Interval
public import Kakeya.Mathlib.MeasureTheory.Lintegral

/-!
Pigeonholing.

Besides the abstract dyadic pigeonholing lemmas, this file contains the pigeonholing
steps for shaded families of convex bodies of a common volume that are used in the
uniformization step of Main Lemma 1:

* `ShadedBody.exists_isCRefinement_comparable_density`: pigeonholing the shading density
  into a dyadic class;
* `ShadedBody.card_le_iff_isCRefinement_of_comparable`: for families with comparable
  shading volumes, `c`-refinements and proportional subfamilies are interchangeable up to
  a factor `Λ²`.

The discard step that precedes them — keeping only the bodies whose shading is not much
thinner than average — is `ShadedBody.discardLowShading` and
`ShadedBody.isCRefinement_discardLowShading` in `Kakeya/Factoring/Pigeonhole.lean`, which
needs no common-volume hypothesis.
# Pigeonholing

The general pigeonholing lemmas of the development are collected here: plain averaging over a finite
index set, dyadic pigeonholing for real, extended-real and natural-number valued families, and the
pigeonholing of a lower integral over a finite cover. Nothing here mentions convex bodies, shadings
or the ambient dimension; the applications live in `Kakeya.Factoring.*`.
-/

open scoped ENNReal

@[expose] public section

variable
  {ι : Type*} {n : ℕ}
  (s : Finset ι)
  (w : ι → ℝ)

/- # Averaging over a finite index set

The pigeonhole principle in its plainest form: some term of a finite sum is at least the average.
This is the engine of every dyadic pigeonholing below. -/

/-- **A term of a finite sum above the average** (blueprint `lem:ennrealSumAverage`).

Over a nonempty finite set `T`, some `c ∈ T` satisfies `|T|⁻¹ ∑_{c' ∈ T} g c' ≤ g c`. No finiteness
of the values `g c'` is assumed.

This is a genuine `ℝ≥0∞` gap: the averaging lemmas of `Mathlib.Combinatorics.Pigeonhole` are stated
for cancellative ordered additive commutative monoids, which `ℝ≥0∞` is not. -/
theorem ENNReal.exists_card_inv_mul_sum_le {α : Type*} {T : Finset α} (hT : T.Nonempty)
    (g : α → ℝ≥0∞) :
    ∃ c ∈ T, (T.card : ℝ≥0∞)⁻¹ * ∑ c' ∈ T, g c' ≤ g c := by
  obtain ⟨c, hc_mem, hc⟩ := Finset.exists_max_image T g hT
  refine ⟨c, hc_mem, ?_⟩
  rw [ENNReal.inv_mul_le_iff (Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hc_mem))
    (ENNReal.natCast_ne_top _)]
  simpa using Finset.sum_le_card_nsmul T g (g c) hc

/- # Real and extended-real dyadic pigeonholing -/

/-- Dyadic pigeonholing with weights.
  (H.W.) Shall we name it according to Mathlib convention? -/
theorem Real.dyadic_pigeonhole (f : ι → Fin n → ℝ) {a b : ℝ} (ha : 0 < a) (hb : a ≤ b)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (Function.const _ a) (Function.const _ b)) :
    ∃ s', s' ⊆ s ∧ s.sum w ≤ (1 + logb 2 (b / a)) ^ n * s'.sum w ∧
      ∀ i ∈ s', ∀ j ∈ s', f i ≤ (2 : ℝ) • f j := by
  classical
  let f' i k : ℤ := ⌊logb 2 (f i k / a)⌋
  let t : Finset (Fin n → ℤ) := Finset.Icc (fun _ ↦ 0) (fun _ ↦ ⌊logb 2 (b / a)⌋)
  have hp {i : ι} (hi : i ∈ s) (k : Fin n) : 0 < f i k / a :=
    div_pos (ha.trans_le ((h i hi).1 k)) ha
  replace h : ∀ i ∈ s, f' i ∈ t := by
    intro i hi
    simp only [Finset.mem_Icc, Pi.le_def, t, f']
    refine ⟨fun k => Int.floor_nonneg.mpr
      (logb_nonneg one_lt_two ((one_le_div ha).mpr ((h i hi).1 k))), fun k => ?_⟩
    gcongr
    · norm_num
    · exact hp hi k
    · exact (h i hi).2 k
  set D := 1 + logb 2 (b / a) with hDdef
  have hlog : 0 ≤ logb 2 (b / a) := logb_nonneg one_lt_two ((one_le_div ha).mpr hb)
  have hfl : (0 : ℤ) ≤ ⌊logb 2 (b / a)⌋ := Int.floor_nonneg.mpr hlog
  have hD : 0 < D ^ n := by
    rw [hDdef]; exact pow_pos (add_pos_of_pos_of_nonneg one_pos hlog) n
  have htcard : (t.card : ℝ) ≤ D ^ n := by
    simp only [t, Pi.card_Icc, Int.card_Icc, sub_zero, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
    gcongr
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.le_add_one hfl), hDdef, Int.cast_add,
      Int.cast_one, add_comm (1 : ℝ) (logb 2 (b / a))]
    exact add_le_add_left (Int.floor_le _) 1
  have ht : t.Nonempty := Finset.nonempty_Icc.mpr fun _ ↦ hfl
  by_cases hsw : s.sum w ≤ 0
  · exact ⟨∅, by simpa⟩
  push Not at hsw
  have hv : t.card • (s.sum w / D ^ n) ≤ s.sum w := by
    rw [nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right htcard
      (div_nonneg hsw.le hD.le)).trans_eq (mul_div_cancel₀ _ hD.ne')
  obtain ⟨y, hy⟩ :=
    Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      h ht hv
  refine ⟨{i ∈ s | f' i = y},
    Finset.filter_subset _ _,
    by rw [mul_comm]; exact (div_le_iff₀ hD).mp hy.2, ?_⟩
  /- ∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 • f j -/
  intro i hi j hj k
  simp only [Finset.mem_filter] at hi hj
  simp only [Pi.smul_apply, smul_eq_mul]
  have heq : ⌊logb 2 (f i k / a)⌋ = ⌊logb 2 (f j k / a)⌋ := congrFun (hi.2.trans hj.2.symm) k
  have hle : f i k / a ≤ 2 * (f j k / a) :=
    (Real.logb_le_logb one_lt_two (hp hi.1 k) (mul_pos two_pos (hp hj.1 k))).mp <| by
      rw [Real.logb_mul two_ne_zero (hp hj.1 k).ne', Real.logb_self_eq_one one_lt_two]
      calc logb 2 (f i k / a) ≤ (⌊logb 2 (f i k / a)⌋ : ℝ) + 1 := (Int.lt_floor_add_one _).le
        _ = 1 + (⌊logb 2 (f i k / a)⌋ : ℝ) := add_comm _ _
        _ ≤ 1 + logb 2 (f j k / a) :=
            add_le_add_right (heq ▸ Int.floor_le (logb 2 (f j k / a))) 1
  rw [div_le_iff₀ ha] at hle
  rwa [mul_assoc, div_mul_cancel₀ _ ha.ne'] at hle

/-- This the one-dimensional special case of `dyadic_pigeonhole` -/
theorem Real.dyadic_pigeonhole₁ (f : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : a ≤ b)
    (h : ∀ i ∈ s, f i ∈ Set.Icc a b) : ∃ s', s' ⊆ s ∧
      s.sum w ≤ (1 + logb (2 : ℝ) (b / a)) * s'.sum w ∧
        ∀ i ∈ s', ∀ j ∈ s', f i ≤ (2 : ℝ) * f j := by
  simpa using Real.dyadic_pigeonhole s w (fun i => Function.const (Fin 1) (f i)) ha hb (by simpa)

/- # ENNReal variants -/

private lemma ENNReal.dyadic_pigeonhole.sum_toReal_eq {ι : Type*} {t : Finset ι}
    {w : ι → ENNReal} (ht : ∀ i ∈ t, w i ≠ ⊤) :
    t.sum w = ENNReal.ofReal (t.sum fun i => (w i).toReal) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  exact Finset.sum_congr rfl fun i hi => (ENNReal.ofReal_toReal (ht i hi)).symm

private lemma ENNReal.dyadic_pigeonhole.D_pos {a b : ℝ} (ha : 0 < a) (hb : a ≤ b) :
    (0 : ℝ) < 1 + Real.logb 2 (b / a) := by
  have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) ((one_le_div ha).mpr hb); linarith

private lemma ENNReal.dyadic_pigeonhole.D_pow_ne_zero {a b : ℝ} {n : ℕ}
    (ha : 0 < a) (hb : a ≤ b) :
    ENNReal.ofReal (1 + Real.logb 2 (b / a)) ^ n ≠ 0 :=
  pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr (ENNReal.dyadic_pigeonhole.D_pos ha hb))

private lemma ENNReal.dyadic_pigeonhole.top_sum_le {ι : Type*} {s : Finset ι} {w : ι → ENNReal}
    {C : ENNReal} (hC : C ≠ 0) {i₀ : ι} (hw₀ : w i₀ = ⊤) :
    s.sum w ≤ C * ({i₀} : Finset ι).sum w := by
  rw [Finset.sum_singleton, hw₀, ENNReal.mul_top hC]; exact le_top

private lemma ENNReal.dyadic_pigeonhole.weight_bound_transfer {ι : Type*} {n : ℕ}
    {s s' : Finset ι} (hs' : s' ⊆ s) {w : ι → ENNReal} (hw_ne : ∀ i ∈ s, w i ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (h : s.sum (fun i => (w i).toReal) ≤ C ^ n * s'.sum (fun i => (w i).toReal)) :
    s.sum w ≤ ENNReal.ofReal C ^ n * s'.sum w := by
  rw [ENNReal.dyadic_pigeonhole.sum_toReal_eq hw_ne,
    ENNReal.dyadic_pigeonhole.sum_toReal_eq (fun i hi => hw_ne i (hs' hi)),
    ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- This is an ENNReal version of `Real.dyadic_pigeonhole` with weight in ENNReal. -/
theorem ENNReal.dyadic_pigeonhole' (w : ι → ENNReal) (f : ι → Fin n → ℝ)
  {a b : ℝ} (ha : 0 < a) (hb : a ≤ b)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (Function.const _ a) (Function.const _ b)) :
    ∃ s', s' ⊆ s ∧ s.sum w ≤ ENNReal.ofReal (1 + Real.logb 2 (b / a)) ^ n * s'.sum w ∧
      ∀ i ∈ s', ∀ j ∈ s', f i ≤ (2 : ℝ) • f j := by
  classical
  by_cases hsw : s.sum w = ⊤
  · obtain ⟨i₀, hi₀s, hi₀w⟩ := ENNReal.sum_eq_top.mp hsw
    refine ⟨{i₀}, by simpa, ENNReal.dyadic_pigeonhole.top_sum_le
      (ENNReal.dyadic_pigeonhole.D_pow_ne_zero ha hb) hi₀w, ?_⟩
    rintro i hi j hj k
    simp only [Finset.mem_singleton] at hi hj; subst hi; subst hj
    simp only [Pi.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left (ha.le.trans ((h j hi₀s).1 k)) one_le_two
  have hw_ne : ∀ i ∈ s, w i ≠ ⊤ := ENNReal.sum_ne_top.mp hsw
  obtain ⟨s', hs'sub, hs'sum, hs'2⟩ :=
    Real.dyadic_pigeonhole s (fun i => (w i).toReal) f ha hb h
  exact ⟨s', hs'sub, ENNReal.dyadic_pigeonhole.weight_bound_transfer hs'sub hw_ne
    (ENNReal.dyadic_pigeonhole.D_pos ha hb).le hs'sum, hs'2⟩

/-- This is the ENNReal version of `Real.dyadic_pigeonhole`. -/
theorem ENNReal.dyadic_pigeonhole (w : ι → ENNReal) (f : ι → Fin n → ENNReal)
  {a b : ℝ} (ha : 0 < a) (hb : a ≤ b)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (Function.const _ (ENNReal.ofReal a))
      (Function.const _ (ENNReal.ofReal b))) :
    ∃ s', s' ⊆ s ∧ s.sum w ≤ ENNReal.ofReal (1 + Real.logb 2 (b / a)) ^ n * s'.sum w ∧
      ∀ i ∈ s', ∀ j ∈ s', f i ≤ (2 : ENNReal) • f j := by
  have hf_ne_top : ∀ i ∈ s, ∀ k, f i k ≠ ⊤ :=
    fun i hi k => ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((h i hi).2 k)
  set fR : ι → Fin n → ℝ := fun i k => (f i k).toReal
  have hR : ∀ i ∈ s, fR i ∈ Set.Icc (Function.const (Fin n) a) (Function.const (Fin n) b) :=
    fun i hi => ⟨fun k => (ENNReal.ofReal_le_iff_le_toReal (hf_ne_top i hi k)).mp ((h i hi).1 k),
      fun k => ENNReal.toReal_le_of_le_ofReal (ha.le.trans hb) ((h i hi).2 k)⟩
  obtain ⟨s', hs'sub, hs'sum, hs'f⟩ :=
    ENNReal.dyadic_pigeonhole' s w fR ha hb hR
  refine ⟨s', hs'sub, hs'sum, fun i hi j hj k => ?_⟩
  have hle := ENNReal.ofReal_le_ofReal (hs'f i hi j hj k)
  simp only [Pi.smul_apply, smul_eq_mul, fR] at hle
  rw [ENNReal.ofReal_toReal (hf_ne_top i (hs'sub hi) k),
    ENNReal.ofReal_mul zero_le_two,
    ENNReal.ofReal_toReal (hf_ne_top j (hs'sub hj) k)] at hle
  simpa using hle

/-- This is the ENNReal version of `Real.dyadic_pigeonhole₁`. -/
theorem ENNReal.dyadic_pigeonhole₁ (w : ι → ENNReal) (f : ι → ENNReal)
    {a b : ℝ} (ha : 0 < a) (hb : a ≤ b)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (ENNReal.ofReal a) (ENNReal.ofReal b)) : ∃ s', s' ⊆ s ∧
      s.sum w ≤ ENNReal.ofReal (1 + Real.logb (2 : ℝ) (b / a)) * s'.sum w ∧
        ∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 * f j := by
  simpa using ENNReal.dyadic_pigeonhole s w (fun i => Function.const (Fin 1) (f i)) ha hb
    (by simpa)

/-- A variant of `ENNReal.dyadic_pigeonhole₁` that does not require an explicit `a ≤ b`
hypothesis: when `s` is nonempty, this is derived from the `Icc` membership; when `s` is
empty, the conclusion is trivial. -/
theorem ENNReal.dyadic_pigeonhole₁' (w : ι → ENNReal) (f : ι → ENNReal)
    {a b : ℝ} (ha : 0 < a)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (ENNReal.ofReal a) (ENNReal.ofReal b)) : ∃ s', s' ⊆ s ∧
      s.sum w ≤ ENNReal.ofReal (1 + Real.logb (2 : ℝ) (b / a)) * s'.sum w ∧
        ∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 * f j := by
  rcases s.eq_empty_or_nonempty with hs | ⟨i, hi⟩
  · exact ⟨∅, by simp, by simp [hs], by simp⟩
  have hab : a ≤ b := by
    have hle : ENNReal.ofReal a ≤ ENNReal.ofReal b := (h i hi).1.trans (h i hi).2
    have hb_pos : 0 < b :=
      ENNReal.ofReal_pos.mp ((ENNReal.ofReal_pos.mpr ha).trans_le hle)
    exact (ENNReal.ofReal_le_ofReal_iff hb_pos.le).mp hle
  exact ENNReal.dyadic_pigeonhole₁ s w f ha hab h

/-- Blueprint `lem:onePlusLogbBounds`: every dyadic pigeonholing loss `1 + log₂ x` produced by
`ENNReal.dyadic_pigeonhole₁` from an admissible range ratio `x ≥ 1` is at least `1` in `[0, ∞]`.
(Finiteness is `ENNReal.ofReal_lt_top`.) -/
theorem ENNReal.one_le_ofReal_one_add_logb {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ ENNReal.ofReal (1 + Real.logb 2 x) := by
  rw [ENNReal.one_le_ofReal]
  have hlogb : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hx
  linarith

/-- An `NNReal`-valued version of `ENNReal.dyadic_pigeonhole₁'`. The bounds `a` and `b` are
taken as `NNReal`, so the `Set.Icc` membership uses the canonical `NNReal → ENNReal` coercion. -/
theorem ENNReal.dyadic_pigeonhole₁'' (w : ι → ENNReal) (f : ι → ENNReal)
    {a b : NNReal} (ha : 0 < a)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (a : ENNReal) (b : ENNReal)) : ∃ s', s' ⊆ s ∧
      s.sum w ≤ ENNReal.ofReal (1 + Real.logb (2 : ℝ) ((b : ℝ) / a)) * s'.sum w ∧
        ∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 * f j :=
  ENNReal.dyadic_pigeonhole₁' s w f (a := (a : ℝ)) (b := (b : ℝ)) (mod_cast ha)
    (by simpa [ENNReal.ofReal_coe_nnreal] using h)

/- # Pigeonholing shaded families of convex bodies -/

namespace ShadedBody

open MeasureTheory

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {s s' : Finset ι} {V : ι → ShadedBody E}

/-- **A weighted-sum inequality is exactly a `D⁻¹`-refinement** (blueprint
`lem:isCRefinementOfSumLe`).

If `s' ⊆ s` and the total shading volume over `s` is at most `D` times the total shading
volume over `s'`, then the subfamily indexed by `s'` — with the *same* bodies and the *same*
shadings — is a `D⁻¹`-refinement of the family indexed by `s`.

This is the standard exit step of every dyadic pigeonhole in this development: the pigeonhole
returns a multiplicative loss `D` on a weighted sum, and `Kakeya.ShadedBody.IsCRefinement`
wants the reciprocal.  The `Kakeya.ShadedBody.IsRefinement` half is free because the
subfamily is a restriction of the same family, so no shrinking of the bodies or of the
shadings occurs.

`D ≠ 0` is needed for `ENNReal.coe_inv`; no upper bound on `D` is required. -/
theorem isCRefinement_of_sum_le (hs' : s' ⊆ s) {D : NNReal} (hD : D ≠ 0)
    (hsum : ∑ i ∈ s, volume (V i).shade ≤ (D : ENNReal) * ∑ i ∈ s', volume (V i).shade) :
    IsCRefinement s' V s V D⁻¹ := by
  constructor
  · exact ⟨hs', fun i hi => ⟨rfl, subset_rfl⟩⟩
  · calc
      ((D⁻¹ : NNReal) : ENNReal) * ∑ i ∈ s, volume (V i).shade
          = (D : ENNReal)⁻¹ * ∑ i ∈ s, volume (V i).shade := by
              rw [ENNReal.coe_inv hD]
      _ ≤ (D : ENNReal)⁻¹ * ((D : ENNReal) * ∑ i ∈ s', volume (V i).shade) := by
              exact mul_le_mul_right hsum (D : ENNReal)⁻¹
      _ = ((D : ENNReal)⁻¹ * (D : ENNReal)) * ∑ i ∈ s', volume (V i).shade := by
              rw [mul_assoc]
      _ = 1 * ∑ i ∈ s', volume (V i).shade := by
              rw [ENNReal.inv_mul_cancel (by exact_mod_cast hD) ENNReal.coe_ne_top]
      _ = ∑ i ∈ s', volume (V i).shade := by simp

/-- **Pigeonholing the shading density.**  Let `V` be a nonempty finite family of convex
bodies of common volume `v ≠ 0` whose shading densities are at least `a ∈ (0, 1]`.  Then a
`(1 + log₂ (1 / a))⁻¹`-refinement can be chosen on which the shading densities all lie in a
single dyadic interval `[lam, 2 * lam]`, with `a ≤ lam` and `fullness s₂ V ≤ 2 * lam`. -/
theorem exists_isCRefinement_comparable_density {v : ENNReal} {a : NNReal}
    (hs : s.Nonempty) (hvol : ∀ i ∈ s, volume (V i).carrier = v) (hv : v ≠ 0)
    (ha₀ : 0 < a) (ha₁ : a ≤ 1)
    (hZ : ∀ i ∈ s, (a : ENNReal) * volume (V i).carrier ≤ volume (V i).shade) :
    ∃ s₂ ⊆ s, ∃ lam : NNReal, 0 < lam ∧
      IsCRefinement s₂ V s V ((1 + Real.logb 2 ((a : ℝ))⁻¹).toNNReal)⁻¹ ∧
      (∀ i ∈ s₂, (lam : ENNReal) * volume (V i).carrier ≤ volume (V i).shade ∧
        volume (V i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier) ∧
      a ≤ lam ∧ fullness s₂ V ≤ 2 * lam := by
  classical
  have hvpos : 0 < v := pos_iff_ne_zero.mpr hv
  have hvt : v ≠ ⊤ := by
    rcases hs with ⟨i₀, hi₀⟩
    rw [← hvol i₀ hi₀]
    exact (V i₀).isCompact.measure_ne_top
  have ha_enn_pos : (0 : ENNReal) < (a : ENNReal) := by exact_mod_cast ha₀
  let Z : ι → ENNReal := fun i => volume (V i).shade
  let f : ι → ENNReal := fun i => Z i / v
  have hZle : ∀ i ∈ s, Z i ≤ v := fun i hi => by
    dsimp [Z]
    exact (measure_mono (V i).shade_subset :
        volume (V i).shade ≤ volume (V i).carrier).trans_eq (hvol i hi)
  have hfIcc : ∀ i ∈ s, f i ∈ Set.Icc (a : ENNReal) (1 : ENNReal) := by
    intro i hi
    have hZm : (a : ENNReal) * v ≤ Z i := by
      simpa [hvol i hi] using hZ i hi
    constructor
    · dsimp [f]
      exact (ENNReal.le_div_iff_mul_le (Or.inl hv) (Or.inl hvt)).2 hZm
    · dsimp [f]
      exact ENNReal.div_le_of_le_mul (by simpa using hZle i hi)
  obtain ⟨s₂, hs₂sub, hsum, hrel⟩ :=
    ENNReal.dyadic_pigeonhole₁'' (s := s) Z f (a := a) (b := 1) ha₀ hfIcc
  have hs₂ne : s₂.Nonempty := by
    cases s₂.eq_empty_or_nonempty with
    | inl hs₂empty =>
      have hpos : (0 : ENNReal) < s.sum Z := by
        rcases hs with ⟨i₀, hi₀⟩
        have hZi : (0 : ENNReal) < Z i₀ := by
          exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (ne_of_gt ha₀)) hv)
            (by simpa [Z, hvol i₀ hi₀] using hZ i₀ hi₀)
        exact lt_of_lt_of_le hZi (Finset.single_le_sum (fun i hi => (zero_le : 0 ≤ Z i)) hi₀)
      exact False.elim ((not_le_of_gt hpos) (by simpa [hs₂empty] using hsum))
    | inr hne => exact hne
  let d : ι → NNReal := fun i => (f i).toNNReal
  let t : Finset NNReal := s₂.image d
  have htne : t.Nonempty := by
    simpa [t] using hs₂ne.image d
  let lam : NNReal := t.min' htne
  have hf_ne_top : ∀ i ∈ s₂, f i ≠ ⊤ := fun i hi =>
    ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) (hfIcc i (hs₂sub hi)).2
  have hd_eq : ∀ i ∈ s₂, (d i : ENNReal) = f i := fun i hi => by
    exact ENNReal.coe_toNNReal (hf_ne_top i hi)
  have hlam_mem : ∃ j₀ ∈ s₂, d j₀ = lam := by
    have hmem : lam ∈ s₂.image d := by
      simpa [lam, t] using (Finset.min'_mem t htne)
    exact Finset.mem_image.mp hmem
  rcases hlam_mem with ⟨j₀, hj₀s, hj₀d⟩
  have hjam : f j₀ = (lam : ENNReal) := by
    calc
      f j₀ = (d j₀ : ENNReal) := (hd_eq j₀ hj₀s).symm
      _ = (lam : ENNReal) := by rw [hj₀d]
  have hlam_min : ∀ i ∈ s₂, lam ≤ d i := fun i hi => by
    have hle : (s₂.image d).min' ⟨d i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩ ≤ d i :=
      Finset.min'_le (s₂.image d) (d i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    simpa [lam, t] using hle
  have hlam_min_enn : ∀ i ∈ s₂, (lam : ENNReal) ≤ f i := fun i hi => by
    calc
      (lam : ENNReal) ≤ (d i : ENNReal) := ENNReal.coe_le_coe.mpr (hlam_min i hi)
      _ = f i := hd_eq i hi
  have hup_enn : ∀ i ∈ s₂, f i ≤ 2 * (lam : ENNReal) := fun i hi => by
    calc
      f i ≤ 2 * f j₀ := hrel i hi j₀ hj₀s
      _ = 2 * (lam : ENNReal) := by rw [hjam]
  have hlam_ge_a : a ≤ lam := by
    refine Finset.le_min' t htne a ?_
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hle_enn : (a : ENNReal) ≤ f i := (hfIcc i (hs₂sub hi)).1
    simpa using (ENNReal.toNNReal_mono (hf_ne_top i hi) hle_enn)
  have hlam_pos : 0 < lam := lt_of_lt_of_le ha₀ hlam_ge_a
  have hden : ∀ i ∈ s₂, (lam : ENNReal) * volume (V i).carrier ≤ volume (V i).shade ∧
      volume (V i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier := by
    intro i hi
    constructor
    · have hle : (lam : ENNReal) ≤ f i := hlam_min_enn i hi
      have hconv : (lam : ENNReal) * v ≤ Z i :=
        (ENNReal.le_div_iff_mul_le (Or.inl hv) (Or.inl hvt)).1 (by simpa [f] using hle)
      simpa [Z, hvol i (hs₂sub hi)] using hconv
    · have hle : f i ≤ 2 * (lam : ENNReal) := hup_enn i hi
      have hconv : Z i ≤ (2 * (lam : ENNReal)) * v :=
        (ENNReal.div_le_iff_le_mul (Or.inl hv) (Or.inl hvt)).1 (by simpa [f] using hle)
      simpa [Z, hvol i (hs₂sub hi)] using hconv
  have hfull' : fullness' s₂ V ≤ 2 * (lam : ENNReal) := by
    apply ENNReal.div_le_of_le_mul
    calc
      s₂.sum Z ≤ ∑ i ∈ s₂, (2 * (lam : ENNReal) * v) := by
        exact Finset.sum_le_sum (fun i hi => by
          simpa [Z, hvol i (hs₂sub hi)] using (hden i hi).2)
      _ = (s₂.card : ENNReal) * (2 * (lam : ENNReal) * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (lam : ENNReal)) * ((s₂.card : ENNReal) * v) := by ring
      _ = (2 * (lam : ENNReal)) * ∑ i ∈ s₂, volume (V i).carrier := by
        congr 1
        calc
          (s₂.card : ENNReal) * v = ∑ i ∈ s₂, v := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = ∑ i ∈ s₂, volume (V i).carrier := by
            exact Finset.sum_congr rfl (fun i hi => (hvol i (hs₂sub hi)).symm)
  have hfull : fullness s₂ V ≤ 2 * lam := by
    rw [← ENNReal.coe_le_coe]
    rw [coe_fullness]
    simpa using hfull'
  let D : ℝ := 1 + Real.logb 2 ((a : ℝ)⁻¹)
  have hDpos : (0 : ℝ) < D := by
    dsimp [D]
    have hlog : 0 ≤ Real.logb 2 ((a : ℝ)⁻¹) := by
      apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      rw [one_le_inv₀ (by exact_mod_cast ha₀ : (0 : ℝ) < (a : ℝ))]
      exact_mod_cast ha₁
    linarith
  have hDmatch :
      ENNReal.ofReal (1 + Real.logb (2 : ℝ) ((1 : ℝ) / (a : ℝ))) = ENNReal.ofReal D := by
    congr 1
    change 1 + Real.logb (2 : ℝ) ((1 : ℝ) / (a : ℝ)) = 1 + Real.logb 2 ((a : ℝ)⁻¹)
    congr 1
    rw [one_div]
  have hsumD : s.sum Z ≤ (D.toNNReal : ENNReal) * s₂.sum Z := by
    rw [show (D.toNNReal : ENNReal) = ENNReal.ofReal D by rfl]
    rw [← hDmatch]
    simpa using hsum
  have hD_ne : D.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hDpos)
  have hcref : IsCRefinement s₂ V s V ((1 + Real.logb 2 ((a : ℝ))⁻¹).toNNReal)⁻¹ := by
    constructor
    · exact ⟨hs₂sub, fun i hi => ⟨rfl, by intro x hx; exact hx⟩⟩
    · calc
        (((D.toNNReal)⁻¹ : NNReal) : ENNReal) * s.sum Z
            = (D.toNNReal : ENNReal)⁻¹ * s.sum Z := by
              rw [ENNReal.coe_inv hD_ne]
        _ ≤ (D.toNNReal : ENNReal)⁻¹ * ((D.toNNReal : ENNReal) * s₂.sum Z) := by
              exact mul_le_mul_right hsumD _
        _ = ((D.toNNReal : ENNReal)⁻¹ * (D.toNNReal : ENNReal)) * s₂.sum Z := by
              rw [mul_assoc]
        _ = 1 * s₂.sum Z := by
              rw [ENNReal.inv_mul_cancel (by exact_mod_cast hD_ne) ENNReal.coe_ne_top]
        _ = s₂.sum Z := by simp
  exact ⟨s₂, hs₂sub, lam, hlam_pos, hcref, hden, hlam_ge_a, hfull⟩

/-- **Cardinality and refinement for comparable shading densities.**  Suppose the shading
volumes of a nonempty family of convex bodies of common volume `v ≠ 0` all lie in
`[Λ⁻¹ * μ₀ * v, Λ * μ₀ * v]` for some `Λ ≥ 1` and `μ₀ ≠ 0`.  Then, for a nonempty subfamily
indexed by `s' ⊆ s`, being a `c`-refinement forces `|s'| ≥ c * Λ⁻² * |s|`, and conversely
`|s'| ≥ κ * |s|` forces the subfamily to be a `κ * Λ⁻²`-refinement. -/
theorem card_le_iff_isCRefinement_of_comparable {v μ₀ : ENNReal} {Λ : NNReal}
    (hs : s.Nonempty) (hvol : ∀ i ∈ s, volume (V i).carrier = v) (hv : v ≠ 0)
    (hΛ : 1 ≤ Λ) (hμ₀ : μ₀ ≠ 0) (hμ₀' : μ₀ ≠ ⊤)
    (hlow : ∀ i ∈ s, ((Λ : ENNReal))⁻¹ * μ₀ * v ≤ volume (V i).shade)
    (hupp : ∀ i ∈ s, volume (V i).shade ≤ (Λ : ENNReal) * μ₀ * v)
    (hs' : s' ⊆ s) (hs'ne : s'.Nonempty) :
    (∀ c : NNReal, 0 < c → c ≤ 1 → IsCRefinement s' V s V c →
        c * (Λ ^ 2)⁻¹ * s.card ≤ s'.card) ∧
    (∀ κ : NNReal, 0 < κ → κ ≤ 1 → κ * s.card ≤ (s'.card : NNReal) →
        IsCRefinement s' V s V (κ * (Λ ^ 2)⁻¹)) := by
  classical
  let Z : ι → ENNReal := fun i => volume (V i).shade
  let S : ENNReal := ∑ i ∈ s, Z i
  let T : ENNReal := ∑ i ∈ s', Z i
  let Λe : ENNReal := (Λ : ENNReal)
  have hvt : v ≠ ⊤ := by
    rcases hs with ⟨i₀, hi₀⟩
    rw [← hvol i₀ hi₀]
    exact (V i₀).isCompact.measure_ne_top
  have hΛne0 : (Λ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ))
  have hΛne : (Λ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hΛ2_0 : (Λ ^ 2 : NNReal) ≠ 0 := pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ))
  have hxv : μ₀ * v ≠ 0 := mul_ne_zero hμ₀ hv
  have hxv' : μ₀ * v ≠ ⊤ := ENNReal.mul_ne_top hμ₀' hvt
  have hcoepow : (Λe : ENNReal) ^ 2 = ((Λ ^ 2 : NNReal) : ENNReal) := by
    dsimp [Λe]
  have hΛinv2 : ((Λ ^ 2 : NNReal) : ENNReal)⁻¹ = (Λe : ENNReal)⁻¹ * (Λe : ENNReal)⁻¹ := by
    rw [← hcoepow, ENNReal.inv_pow, pow_two]
  have hA : (s.card : ENNReal) * (Λe⁻¹ * μ₀ * v) ≤ S := by
    calc
      (s.card : ENNReal) * (Λe⁻¹ * μ₀ * v) = ∑ i ∈ s, (Λe⁻¹ * μ₀ * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ S := by
        dsimp [S, Z]
        exact Finset.sum_le_sum (fun i hi => hlow i hi)
  have hB : S ≤ (s.card : ENNReal) * (Λe * μ₀ * v) := by
    calc
      S ≤ ∑ i ∈ s, (Λe * μ₀ * v) := by
        dsimp [S, Z]
        exact Finset.sum_le_sum (fun i hi => hupp i hi)
      _ = (s.card : ENNReal) * (Λe * μ₀ * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hC : (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * v) ≤ T := by
    calc
      (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * v) = ∑ i ∈ s', (Λe⁻¹ * μ₀ * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T := by
        dsimp [T, Z]
        exact Finset.sum_le_sum (fun i hi => hlow i (hs' hi))
  have hD : T ≤ (s'.card : ENNReal) * (Λe * μ₀ * v) := by
    calc
      T ≤ ∑ i ∈ s', (Λe * μ₀ * v) := by
        dsimp [T, Z]
        exact Finset.sum_le_sum (fun i hi => hupp i (hs' hi))
      _ = (s'.card : ENNReal) * (Λe * μ₀ * v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  constructor
  · intro c hc0 hc1 hcref
    have hcsum : (c : ENNReal) * S ≤ T := by simpa [S, Z] using hcref.2
    have h1 : (c : ENNReal) * (s.card : ENNReal) * (Λe : ENNReal)⁻¹ * (μ₀ * v)
        ≤ (s'.card : ENNReal) * (Λe : ENNReal) * (μ₀ * v) := by
      calc
        (c : ENNReal) * (s.card : ENNReal) * (Λe : ENNReal)⁻¹ * (μ₀ * v)
            = (c : ENNReal) * ((s.card : ENNReal) * (Λe⁻¹ * μ₀ * v)) := by ring
        _ ≤ (c : ENNReal) * S := by gcongr
        _ ≤ T := hcsum
        _ ≤ (s'.card : ENNReal) * (Λe * μ₀ * v) := by exact hD
        _ = (s'.card : ENNReal) * (Λe : ENNReal) * (μ₀ * v) := by ring
    have hcancel : (c : ENNReal) * (s.card : ENNReal) * (Λe : ENNReal)⁻¹
        ≤ (s'.card : ENNReal) * (Λe : ENNReal) :=
      (ENNReal.mul_le_mul_iff_left hxv hxv').mp h1
    have h2 : (c : ENNReal) * (s.card : ENNReal) * (Λe : ENNReal)⁻¹ * (Λe : ENNReal)⁻¹
        ≤ (s'.card : ENNReal) * (Λe : ENNReal) * (Λe : ENNReal)⁻¹ := by
      exact mul_le_mul' hcancel (le_refl (Λe : ENNReal)⁻¹)
    have hfin : (c : ENNReal) * (s.card : ENNReal) * ((Λ ^ 2 : NNReal) : ENNReal)⁻¹
        ≤ (s'.card : ENNReal) := by
      calc
        (c : ENNReal) * (s.card : ENNReal) * ((Λ ^ 2 : NNReal) : ENNReal)⁻¹
            = (c : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * Λe⁻¹) := by rw [hΛinv2]
        _ = (c : ENNReal) * (s.card : ENNReal) * Λe⁻¹ * Λe⁻¹ := by ring
        _ ≤ (s'.card : ENNReal) * Λe * Λe⁻¹ := by exact h2
        _ = (s'.card : ENNReal) := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hΛne0 hΛne, mul_one]
    have hfin' : ((c * (Λ ^ 2)⁻¹ * s.card : NNReal) : ENNReal) ≤ (s'.card : NNReal) := by
      simpa [mul_assoc, mul_comm, mul_left_comm, ENNReal.coe_inv hΛ2_0] using hfin
    exact (ENNReal.coe_le_coe).1 hfin'
  · intro κ hκ0 hκ1 hκnn
    constructor
    · exact ⟨hs', fun i hi => ⟨rfl, by intro x hx; exact hx⟩⟩
    · have hcoecard : (κ : ENNReal) * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
        simpa [mul_assoc] using (ENNReal.coe_le_coe.mpr hκnn)
      have hmid : (κ : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * v)
          ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * v) := by
        calc
          (κ : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * v)
              = (κ : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (Λe * μ₀ * v) := by ring
          _ = (κ : ENNReal) * (s.card : ENNReal) * ((Λe⁻¹ * Λe⁻¹) * Λe) * μ₀ * v := by ring
          _ = (κ : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * (Λe⁻¹ * Λe)) * μ₀ * v := by ring
          _ = (κ : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * 1) * μ₀ * v := by
            rw [show (Λe : ENNReal)⁻¹ * (Λe : ENNReal) = 1 by
              exact ENNReal.inv_mul_cancel hΛne0 hΛne]
          _ = (κ : ENNReal) * (s.card : ENNReal) * Λe⁻¹ * μ₀ * v := by ring
          _ = (κ : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * μ₀ * v) := by ring
          _ ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * v) := by gcongr
      have hgoal : (κ : ENNReal) * ((Λ ^ 2 : NNReal) : ENNReal)⁻¹ * S ≤ T := by
        calc
          (κ : ENNReal) * ((Λ ^ 2 : NNReal) : ENNReal)⁻¹ * S
              = (κ : ENNReal) * (Λe⁻¹ * Λe⁻¹) * S := by rw [hΛinv2]
          _ ≤ (κ : ENNReal) * (Λe⁻¹ * Λe⁻¹) * ((s.card : ENNReal) * (Λe * μ₀ * v)) := by gcongr
          _ = (κ : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * v) := by ring
          _ ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * v) := hmid
          _ ≤ T := hC
      simpa [S, T, Z, mul_assoc, ENNReal.coe_inv hΛ2_0] using hgoal

end ShadedBody
/- # Natural-number valued variants

The multiplicity functions of `ShadedBody.pointwiseMultiplicity` are natural-number valued, so for
them the dyadic classes can be taken to be genuine dyadic blocks `[2 ^ k, 2 ^ (k + 1))` and the
pigeonholed scale to be exactly the power of two `2 ^ k`. The logarithmic loss is then the exact
class count `Nat.log 2 N + 1 = Kakeya.dyadicPigeonholeNatConstant N`, a natural number, rather than
the real number `1 + Real.logb 2 (b / a)` of `Real.dyadic_pigeonhole`.

These variants live in the `Nat` namespace, which records the type of the pigeonholed function; the
type of the *weight* is the suffix, so the `ℝ≥0∞`-weight version is `Nat.dyadic_pigeonhole_ennreal`
and the `ℕ`-weight version is `Nat.dyadic_pigeonhole`. (The `Real` and `ENNReal` namespaces above
record the weight type instead, since there the pigeonholed function is real valued throughout.) -/

/-- **The dyadic block is a fiber of `Nat.log 2`** (blueprint `lem:natDyadicBlockFiber`).

For a family of positive natural numbers, the fiber of `i ↦ Nat.log 2 (f i)` over `k` is exactly the
`k`-th dyadic class `{i ∈ s | 2 ^ k ≤ f i < 2 ^ (k + 1)}`. This is the bridge between the
`Nat.log`-fiber description consumed by `Mathlib.Combinatorics.Pigeonhole` and the dyadic-block
description used downstream. -/
theorem Nat.filter_log_eq_eq_filter_dyadic {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 1 ≤ f i) (k : ℕ) :
    {i ∈ s | Nat.log 2 (f i) = k} = {i ∈ s | 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)} := by
  apply Finset.filter_congr
  intro i hi
  constructor
  · intro hlog
    have hpos : f i ≠ 0 := Nat.one_le_iff_ne_zero.mp (hf i hi)
    have hle' : 2 ^ (Nat.log 2 (f i)) ≤ f i := Nat.pow_log_le_self 2 hpos
    have hlt' : f i < 2 ^ ((Nat.log 2 (f i)).succ) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (f i)
    have hle : 2 ^ k ≤ f i := by
      rw [hlog] at hle'
      exact hle'
    have hlt : f i < 2 ^ (k + 1) := by
      rw [hlog] at hlt'
      simpa [Nat.succ_eq_add_one] using hlt'
    exact ⟨hle, hlt⟩
  · intro ⟨hle, hlt⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow hle hlt

namespace Kakeya

/-- **Constant in `Nat.dyadic_pigeonhole_ennreal`** (blueprint
`def:dyadicPigeonholeNatConstant`): `C(N) = Nat.log 2 N + 1`, the exact number of dyadic classes
meeting the interval `[1, N]`.

The constant is a natural number; it enters `ℝ≥0∞`-valued inequalities through the canonical
coercion. It depends only on the upper bound `N`; in particular it does *not* depend on the index
set, on the weights, or on the ambient dimension. It is sharper than the constant
`1 + Real.logb 2 N` of `Real.dyadic_pigeonhole₁`, and it is what allows the conclusion of
`Nat.dyadic_pigeonhole` to be an inequality of natural numbers. -/
def dyadicPigeonholeNatConstant (N : ℕ) : ℕ := Nat.log 2 N + 1

end Kakeya

/-- **Dyadic pigeonholing, natural-number valued** (blueprint `lem:dyadicPigeonholeNat`).

If `1 ≤ f i ≤ N` on `s`, some dyadic class `{i ∈ s | 2 ^ k ≤ f i < 2 ^ (k + 1)}` with
`k ≤ Nat.log 2 N` carries at least a `Kakeya.dyadicPigeonholeNatConstant N`-th of the total weight.
The scale `2 ^ k` is an exact power of two, not merely a quantity comparable to the values on the
class. If `s = ∅` then `k = 0` works vacuously. -/
theorem Nat.dyadic_pigeonhole_ennreal {ι : Type*} (s : Finset ι) (w : ι → ENNReal) (f : ι → ℕ)
    {N : ℕ} (hf : ∀ i ∈ s, 1 ≤ f i ∧ f i ≤ N) :
    ∃ k ≤ Nat.log 2 N,
      ∑ i ∈ s, w i
        ≤ (Kakeya.dyadicPigeonholeNatConstant N : ENNReal)
            * ∑ i ∈ {i ∈ s | 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)}, w i := by
  classical
  -- Pigeonhole the total weight over the fibers of `i ↦ Nat.log 2 (f i)`.
  have h_map : ∀ i ∈ s, Nat.log 2 (f i) ∈ Finset.range (Nat.log 2 N + 1) := fun i hi =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hf i hi).2))
  obtain ⟨k, hkT, hk⟩ :=
    ENNReal.exists_card_inv_mul_sum_le (T := Finset.range (Nat.log 2 N + 1))
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
      fun k => ∑ i ∈ {i ∈ s | Nat.log 2 (f i) = k}, w i
  rw [Finset.sum_fiberwise_of_maps_to h_map w, Finset.card_range,
    ENNReal.inv_mul_le_iff (by simp) (ENNReal.natCast_ne_top _),
    Nat.filter_log_eq_eq_filter_dyadic s f (fun i hi => (hf i hi).1) k] at hk
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hkT), hk⟩

/-- **Dyadic pigeonholing with natural-number weights** (blueprint
`lem:dyadicPigeonholeNatWeights`): the variant of `Nat.dyadic_pigeonhole_ennreal` in which the
weight is `ℕ`-valued, so that the conclusion is an inequality of natural numbers. -/
theorem Nat.dyadic_pigeonhole {ι : Type*} (s : Finset ι) (w : ι → ℕ) (f : ι → ℕ)
    {N : ℕ} (hf : ∀ i ∈ s, 1 ≤ f i ∧ f i ≤ N) :
    ∃ k ≤ Nat.log 2 N,
      ∑ i ∈ s, w i
        ≤ Kakeya.dyadicPigeonholeNatConstant N
            * ∑ i ∈ {i ∈ s | 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)}, w i := by
  -- Apply `Nat.dyadic_pigeonhole_ennreal` to the coerced weight, then cast back
  have h := Nat.dyadic_pigeonhole_ennreal s (fun i => (w i : ENNReal)) f hf
  rcases h with ⟨k, hk, h⟩
  refine ⟨k, hk, ?_⟩
  exact_mod_cast h

/-- **Discarding the vanishing indices does not change a dyadic class** (blueprint
`lem:dyadicClassFilterOneLe`): the extra conjunct `1 ≤ f i` is implied by `2 ^ k ≤ f i`. -/
theorem Nat.filter_dyadic_filter_one_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (k : ℕ) :
    {i ∈ {i ∈ s | 1 ≤ f i} | 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)}
      = {i ∈ s | 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)} := by
  ext i
  simp only [Finset.mem_filter, and_assoc]
  constructor
  · rintro ⟨hs, h1, h2, h3⟩
    exact ⟨hs, h2, h3⟩
  · rintro ⟨hs, h2, h3⟩
    have h1 : 1 ≤ f i := Nat.one_le_two_pow.trans h2
    exact ⟨hs, h1, h2, h3⟩

/-- **Dyadic pigeonholing with the values as weights** (blueprint
`lem:dyadicPigeonholeNatSelfWeight`): the form of `Nat.dyadic_pigeonhole` in which the family to be
pigeonholed and the weight coincide.

*No lower bound on `f` is assumed: the value `0` is allowed*, which is what lets the pigeonholing be
performed over all of `s`. -/
theorem Nat.dyadic_pigeonhole_self {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    {N : ℕ} (hf : ∀ i ∈ s, f i ≤ N) :
    ∃ k ≤ Nat.log 2 N,
      ∑ i ∈ s, f i
        ≤ Kakeya.dyadicPigeonholeNatConstant N
            * ∑ i ∈ {i ∈ s | 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)}, f i := by
  -- Pigeonhole over the indices where `f i ≥ 1`; the ones where `f i = 0` contribute nothing.
  obtain ⟨k, hk, hineq⟩ := Nat.dyadic_pigeonhole {i ∈ s | 1 ≤ f i} f f
    (fun i hi => ⟨(Finset.mem_filter.mp hi).2, hf i (Finset.mem_filter.mp hi).1⟩)
  -- The total sum over `s` equals the sum over the filtered set, and the dyadic classes agree.
  rw [Nat.filter_dyadic_filter_one_le,
    Finset.sum_subset (Finset.filter_subset _ s)
      (fun i hi hi' => by simp only [Finset.mem_filter, hi, true_and] at hi'; omega)] at hineq
  exact ⟨k, hk, hineq⟩

open Classical in
/-- Dyadic pigeonholing of the fibres of a classification map. -/
theorem Nat.dyadic_pigeonhole_fibre {ι κ : Type*} (s : Finset ι) (f : ι → κ) :
    ∃ (k : ℕ) (S : Finset ι),
      S ⊆ s ∧
      (∀ i ∈ S, 2 ^ k ≤ (s.filter (fun i' => f i' = f i)).card ∧
        (s.filter (fun i' => f i' = f i)).card < 2 ^ (k + 1)) ∧
      (∀ i ∈ s, 2 ^ k ≤ (s.filter (fun i' => f i' = f i)).card ∧
        (s.filter (fun i' => f i' = f i)).card < 2 ^ (k + 1) → i ∈ S) ∧
      (s.card : ℝ) / ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ)) ≤ (S.card : ℝ) ∧
      k ≤ Nat.log 2 s.card := by
  obtain ⟨k, hk, hsum⟩ :=
    Nat.dyadic_pigeonhole s (fun _ => 1) (fun i => (s.filter (fun i' => f i' = f i)).card)
      (fun i hi => ⟨Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩,
        Finset.card_le_card (Finset.filter_subset _ _)⟩)
  have hnat : s.card ≤ (Nat.log 2 s.card + 1) *
      ({i ∈ s | 2 ^ k ≤ (s.filter (fun i' => f i' = f i)).card ∧
        (s.filter (fun i' => f i' = f i)).card < 2 ^ (k + 1)}).card := by
    simpa [Kakeya.dyadicPigeonholeNatConstant] using hsum
  refine ⟨k, {i ∈ s | 2 ^ k ≤ (s.filter (fun i' => f i' = f i)).card ∧
      (s.filter (fun i' => f i' = f i)).card < 2 ^ (k + 1)},
    Finset.filter_subset _ _, fun i hi => (Finset.mem_filter.mp hi).2,
    fun i hi h => Finset.mem_filter.mpr ⟨hi, h⟩, ?_, hk⟩
  have hfloor : ⌊Real.logb 2 (s.card : ℝ)⌋₊ = Nat.log 2 s.card := by
    simpa using Real.natFloor_logb_natCast 2 s.card
  rw [hfloor, div_le_iff₀ (by positivity)]
  calc
    (s.card : ℝ) ≤ ((Nat.log 2 s.card : ℝ) + 1) *
        (({i ∈ s | 2 ^ k ≤ (s.filter (fun i' => f i' = f i)).card ∧
          (s.filter (fun i' => f i' = f i)).card < 2 ^ (k + 1)}).card : ℝ) := by
      exact_mod_cast hnat
    _ = _ := by ring

/-- **The class sum is comparable to the class cardinality** (blueprint
`lem:dyadicClassCardSandwich`): on a set where `f` lies in the dyadic block `[2 ^ k, 2 ^ (k + 1))`,
the sum of `f` is between `2 ^ k` and `2 ^ (k + 1)` times the cardinality.

This is the step that converts a statement about the *values* on a dyadic class into a statement
about the *size* of the class. -/
theorem Nat.dyadic_class_card_sandwich {ι : Type*} (u : Finset ι) (f : ι → ℕ) (k : ℕ)
    (h : ∀ j ∈ u, 2 ^ k ≤ f j ∧ f j < 2 ^ (k + 1)) :
    2 ^ k * u.card ≤ ∑ j ∈ u, f j ∧ ∑ j ∈ u, f j ≤ 2 ^ (k + 1) * u.card := by
  refine ⟨?_, ?_⟩
  · simpa [nsmul_eq_mul, mul_comm] using
      Finset.card_nsmul_le_sum u f (2 ^ k) fun j hj => (h j hj).1
  · simpa [nsmul_eq_mul, mul_comm] using
      Finset.sum_le_card_nsmul u f (2 ^ (k + 1)) fun j hj => (h j hj).2.le

/-- **Arithmetic of the scale product** (blueprint `lem:step2ScaleProduct`).

If a quantity `a` is sandwiched between `2 ^ k * N` and `C * 2 ^ (k + 1) * N`, and `N` itself lies
in the dyadic block of `2 ^ l`, then `a` is sandwiched between the product of the two scales and
`4 * C` times it. A statement about natural numbers only; no positivity of `C`, `a` or `N` is
assumed.

This is what turns a bound in terms of a dyadic class and its cardinality into a bound in terms of
the two dyadic scales, and the two factors of `2` it loses are the reason for the `4`. -/
theorem Nat.scale_product_sandwich {C k l a N : ℕ} (hlow : 2 ^ k * N ≤ a)
    (hhigh : a ≤ C * 2 ^ (k + 1) * N) (hNlow : 2 ^ l ≤ N) (hNhigh : N < 2 ^ (l + 1)) :
    2 ^ k * 2 ^ l ≤ a ∧ a ≤ 4 * C * (2 ^ k * 2 ^ l) := by
  refine ⟨(Nat.mul_le_mul_left _ hNlow).trans hlow, hhigh.trans ?_⟩
  calc C * 2 ^ (k + 1) * N ≤ C * 2 ^ (k + 1) * 2 ^ (l + 1) :=
        Nat.mul_le_mul_left _ hNhigh.le
    _ = 4 * C * (2 ^ k * 2 ^ l) := by ring

/- # Pigeonholing a lower integral over a finite cover

The measure-theoretic form of the averaging lemma above: the finite index set indexes a cover of the
domain of integration rather than the terms of a sum. -/

namespace MeasureTheory

/-- **Pigeonholing a lower integral over a finite cover** (blueprint
`lem:lintegralCoverPigeonhole`).

If `S` is covered by the finitely many sets `A c`, `c ∈ T`, with `T` nonempty, then some `A c`
carries at least the average `|T|⁻¹ ∫_S f` of the integral over `S`. No measurability and no
disjointness hypotheses are needed: the two inputs are `MeasureTheory.lintegral_mono_set` and
`MeasureTheory.lintegral_biUnion_finset_le`, both hypothesis-free. -/
theorem exists_card_inv_mul_setLIntegral_le {X : Type*} [MeasurableSpace X] {ι : Type*}
    (μ : Measure X) {T : Finset ι} (hT : T.Nonempty)
    (A : ι → Set X) (f : X → ℝ≥0∞) {S : Set X} (hS : S ⊆ ⋃ c ∈ T, A c) :
    ∃ c ∈ T, (T.card : ℝ≥0∞)⁻¹ * ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in A c, f x ∂μ := by
  have hS_le_union : ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in ⋃ c ∈ T, A c, f x ∂μ :=
    lintegral_mono_set hS
  have hunion_le_sum : ∫⁻ x in ⋃ c ∈ T, A c, f x ∂μ ≤ ∑ c ∈ T, ∫⁻ x in A c, f x ∂μ :=
    lintegral_biUnion_finset_le μ T A f
  have hS_le_sum : ∫⁻ x in S, f x ∂μ ≤ ∑ c ∈ T, ∫⁻ x in A c, f x ∂μ :=
    le_trans hS_le_union hunion_le_sum
  obtain ⟨c, hc, h_avg⟩ :=
    ENNReal.exists_card_inv_mul_sum_le hT (fun c' => ∫⁻ x in A c', f x ∂μ)
  refine ⟨c, hc, ?_⟩
  calc
    (T.card : ℝ≥0∞)⁻¹ * ∫⁻ x in S, f x ∂μ
        ≤ (T.card : ℝ≥0∞)⁻¹ * ∑ c ∈ T, ∫⁻ x in A c, f x ∂μ :=
      mul_le_mul_right hS_le_sum _
    _ ≤ ∫⁻ x in A c, f x ∂μ := h_avg

end MeasureTheory

/-- A finite level decomposition has a level carrying at least the average weight. -/
theorem ENNReal.exists_heavy_level {ι : Type*} (s : Finset ι) (w : ι → ENNReal) (g : ι → ℕ)
    (J : ℕ) (hg : ∀ i ∈ s, g i ≤ J) :
    ∃ j ≤ J, (∑ i ∈ s, w i) ≤ ((J : ENNReal) + 1) * ∑ i ∈ s.filter (fun i => g i = j), w i := by
  classical
  set h : ℕ → ENNReal := fun j => ∑ i ∈ s.filter (fun i => g i = j), w i with hh
  have hmaps : ∀ i ∈ s, g i ∈ Finset.range (J + 1) := fun i hi =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hg i hi))
  have hsum : (∑ i ∈ s, w i) = ∑ j ∈ Finset.range (J + 1), h j :=
    (Finset.sum_fiberwise_of_maps_to hmaps w).symm
  have hne : (Finset.range (J + 1)).Nonempty := Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero J)
  obtain ⟨j₀, hj₀mem, hj₀max⟩ := Finset.exists_max_image (Finset.range (J + 1)) h hne
  refine ⟨j₀, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₀mem), ?_⟩
  rw [hsum]
  calc ∑ j ∈ Finset.range (J + 1), h j
      ≤ (Finset.range (J + 1)).card • h j₀ :=
        Finset.sum_le_card_nsmul _ _ _ (fun j hj => hj₀max j hj)
    _ = ((J : ENNReal) + 1) * h j₀ := by
        rw [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- **Discarding the light members of a weighted family loses less than half its weight.**

Call `i ∈ s` *light* when `2 |s| · w i < ∑_{s} w`, that is when it carries less than half the
average weight.  Then the light members together carry at most half the total, so the retained
set keeps at least half — and every retained member carries at least half the average, which is
the negation of the filter and comes free from `Finset.mem_filter`.

This is the "keep only the heavy ones" companion of `ENNReal.exists_heavy_level`, which produces
a single heavy level instead of a retained set all of whose members are heavy.  The retained
form is what a route needs when it must run over *every* surviving index rather than pick one. -/
theorem ENNReal.two_mul_sum_filter_light_le {ι : Type*} (s : Finset ι) (w : ι → ENNReal) :
    2 * ∑ i ∈ s.filter (fun i => 2 * (s.card : ENNReal) * w i < ∑ j ∈ s, w j), w i
      ≤ ∑ i ∈ s, w i := by
  classical
  by_cases h_top : (∑ j ∈ s, w j) = ⊤
  · simp [h_top]
  · by_cases h_empty : s = ∅
    · simp [h_empty]
    · let D : Finset ι := s.filter (fun i => 2 * (s.card : ENNReal) * w i < ∑ j ∈ s, w j)
      change 2 * ∑ i ∈ D, w i ≤ ∑ j ∈ s, w j
      have hne_nat : s.card ≠ 0 := by
        intro hzero
        exact h_empty (Finset.card_eq_zero.mp hzero)
      have hne : (s.card : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr hne_nat
      have hnt : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hD_sub : D ⊆ s := by
        simp [D]
      have hpoint : ∀ i ∈ D, 2 * (s.card : ENNReal) * w i ≤ ∑ j ∈ s, w j := by
        intro i hi
        exact le_of_lt (Finset.mem_filter.mp hi).2
      have hone : 2 * (s.card : ENNReal) * ∑ i ∈ D, w i
          ≤ (s.card : ENNReal) * ∑ j ∈ s, w j := by
        calc
          2 * (s.card : ENNReal) * ∑ i ∈ D, w i = ∑ i ∈ D, 2 * (s.card : ENNReal) * w i := by
            rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ D, ∑ j ∈ s, w j := Finset.sum_le_sum hpoint
          _ = (D.card : ENNReal) * ∑ j ∈ s, w j := by
            rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (s.card : ENNReal) * ∑ j ∈ s, w j := by
            have hcard : (D.card : ENNReal) ≤ (s.card : ENNReal) := by
              exact_mod_cast (Finset.card_le_card hD_sub)
            simpa [mul_comm] using (mul_le_mul_right hcard (∑ j ∈ s, w j))
      have htwo : (2 * ∑ i ∈ D, w i) * (s.card : ENNReal)
          ≤ (∑ j ∈ s, w j) * (s.card : ENNReal) := by
        calc
          (2 * ∑ i ∈ D, w i) * (s.card : ENNReal) = 2 * (s.card : ENNReal) * ∑ i ∈ D, w i := by
            ring
          _ ≤ (s.card : ENNReal) * (∑ j ∈ s, w j) := hone
          _ = (∑ j ∈ s, w j) * (s.card : ENNReal) := by
            ring
      exact (ENNReal.mul_le_mul_iff_left hne hnt).mp htwo

namespace Kakeya

/-- **Pigeonhole on Finset sums.** If `s : Finset ι` is mapped via `f : ι → κ`
into a non-empty finite set `xs : Finset κ`, then for any weights `w : ι → ℝ`
there is some block `k ∈ xs` whose fiber sum is at least the average, i.e.
`xs.card · Σ_{i ∈ {i ∈ s | f i = k}} w i ≥ Σ_{i ∈ s} w i`. -/
lemma exists_block_sum_ge {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (f : ι → κ) (xs : Finset κ) (w : ι → ℝ)
    (hxs : xs.Nonempty)
    (hcov : ∀ i ∈ s, f i ∈ xs) :
    ∃ k ∈ xs, ∑ i ∈ s, w i ≤ xs.card * ∑ i ∈ {i ∈ s | f i = k}, w i := by
  set S : κ → ℝ := fun k ↦ ∑ i ∈ {i ∈ s | f i = k}, w i with hS
  obtain ⟨k₀, hk₀_mem, hk₀_max⟩ := xs.exists_max_image S hxs
  refine ⟨k₀, hk₀_mem, ?_⟩
  have hdecomp : (∑ i ∈ s, w i) = ∑ k ∈ xs, S k := by
    rw [← Finset.sum_fiberwise_of_maps_to hcov w]
  rw [hdecomp]
  calc ∑ k ∈ xs, S k
      ≤ ∑ _k ∈ xs, S k₀ := Finset.sum_le_sum (fun k hk ↦ hk₀_max k hk)
    _ = xs.card • S k₀ := by rw [Finset.sum_const]
    _ = (xs.card : ℝ) * S k₀ := by rw [nsmul_eq_mul]

end Kakeya

namespace MeasureTheory

/-- **Measure pigeonhole** (combinatorial core of the shade-measure dyadic-band refinement of the
shaded uniformization): among `m+1` sets covering `U`, one captures a `1/(m+1)` share of
`volume U`.  Applied with `A k = {x | localCount x ∈ [2ᵏ, 2ᵏ⁺¹)}` it picks the dominant dyadic band
of the per-point local branching, preserving the fullness `λ` up to the factor `m+1`. -/
lemma exists_dominant_band {E : Type*} [MeasureSpace E] {m : ℕ}
    (U : Set E) (A : Fin (m + 1) → Set E)
    (hcover : U ⊆ ⋃ k, A k) :
    ∃ k : Fin (m + 1), volume U ≤ (m + 1) • volume (U ∩ A k) := by
  classical
  have hUeq : ⋃ k, U ∩ A k = U := by
    rw [← Set.inter_iUnion]; exact Set.inter_eq_left.mpr hcover
  have hsum : volume U ≤ ∑ k, volume (U ∩ A k) := by
    calc volume U = volume (⋃ k, U ∩ A k) := by rw [hUeq]
      _ ≤ ∑' k, volume (U ∩ A k) := measure_iUnion_le _
      _ = ∑ k, volume (U ∩ A k) := tsum_fintype _
  obtain ⟨k, -, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun k => volume (U ∩ A k))
      ⟨0, Finset.mem_univ 0⟩
  refine ⟨k, hsum.trans ?_⟩
  calc ∑ j, volume (U ∩ A j)
      ≤ ∑ _j : Fin (m + 1), volume (U ∩ A k) :=
        Finset.sum_le_sum (fun j _ => hk j (Finset.mem_univ j))
    _ = (m + 1) • volume (U ∩ A k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Measure pigeonhole, `Finset`-indexed** (R4): among the sets `A a` for `a`
in a nonempty `Finset T` covering `U`, one captures a `1/|T|` share of `volume U`.
Used to pigeonhole the finitely-many fiber *profiles*. -/
lemma exists_dominant_band_finset {E : Type*} [MeasureSpace E] {κ : Type*}
    (T : Finset κ) (hT : T.Nonempty)
    (U : Set E) (A : κ → Set E) (hcover : U ⊆ ⋃ a ∈ T, A a) :
    ∃ a ∈ T, volume U ≤ T.card • volume (U ∩ A a) := by
  classical
  have hUeq : ⋃ a ∈ T, U ∩ A a = U := by
    rw [← Set.inter_iUnion₂]; exact Set.inter_eq_left.mpr hcover
  have hsum : volume U ≤ ∑ a ∈ T, volume (U ∩ A a) := by
    calc volume U = volume (⋃ a ∈ T, U ∩ A a) := by rw [hUeq]
      _ ≤ ∑ a ∈ T, volume (U ∩ A a) := measure_biUnion_finset_le T _
  obtain ⟨a, ha, hamax⟩ := T.exists_max_image (fun a => volume (U ∩ A a)) hT
  refine ⟨a, ha, hsum.trans ?_⟩
  calc ∑ b ∈ T, volume (U ∩ A b)
      ≤ ∑ _b ∈ T, volume (U ∩ A a) := Finset.sum_le_sum (fun b hb => hamax b hb)
    _ = T.card • volume (U ∩ A a) := by rw [Finset.sum_const]

end MeasureTheory
