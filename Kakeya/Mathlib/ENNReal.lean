/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.ENNReal.Action
public import Mathlib.Data.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# ENNReal
-/

@[expose] public section

open scoped ENNReal NNReal

namespace ENNReal

lemma sum_pos_of_pos {α : Type*} {s : Finset α} (i : α) (hi1 : i ∈ s) {f : α → ℝ≥0∞}
    (hi2 : 0 < f i) : 0 < ∑ i ∈ s, f i :=
  hi2.trans_le <| Finset.single_le_sum_of_canonicallyOrdered hi1

theorem sum_pos_of_nonempty {α : Type u_1} {s : Finset α} (hs : s.Nonempty)
    {g : α → ENNReal} (Hpos : ∀ i ∈ s, 0 < g i) :
    0 < ∑ i ∈ s, g i := sum_pos_of_pos _ hs.choose_spec (Hpos _ hs.choose_spec)

/-- If `c < a * b` in `ℝ≥0∞`, there is `a' < a` with `c < a' * b`. -/
lemma exists_lt_mul_left {a b c : ENNReal} (hc : c < a * b) :
    ∃ a' < a, c < a' * b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (ENNReal.div_lt_of_lt_mul hc)
  exact ⟨_, ha', (ENNReal.div_lt_iff (.inl <| fun hb ↦ by simp [hb] at hc)
    (.inr <| by rintro rfl; simp at hc)).1 hc'⟩

/-- If `c < a * b` in `ℝ≥0∞`, there is `b' < b` with `c < a * b'`. -/
lemma exists_lt_mul_right {a b c : ENNReal} (hc : c < a * b) :
    ∃ b' < b, c < a * b' := by
  rw [mul_comm] at hc
  obtain ⟨b', hb', hc'⟩ := exists_lt_mul_left hc
  exact ⟨b', hb', by rw [mul_comm]; exact hc'⟩

/-- If `b` is strictly less than a finite product of `ℝ≥0∞` values, we can pointwise
lower the factors strictly and still keep the product strictly greater than `b`. -/
lemma exists_lt_prod_of_lt_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (b : ℝ≥0∞)
    (hb : b < (∏ i ∈ s, f i)) : ∃ r : ι → ENNReal, (∀ i ∈ s, r i < f i) ∧ b < ∏ i ∈ s, r i := by
  classical induction s using Finset.cons_induction_on generalizing b with
  | empty => simpa using hb
  | cons a s' ha ih =>
    rw [Finset.prod_cons ha] at hb
    obtain ⟨α, hα_lt, hα⟩ := exists_lt_mul_left hb
    obtain ⟨β, hβ_lt, hβ⟩ := exists_lt_mul_right hα
    obtain ⟨r', hr'_lt, hr'⟩ := ih β hβ_lt
    refine ⟨Function.update r' a α, fun i hi ↦ (Finset.mem_cons.mp hi).casesOn (by
      simp +contextual [hα_lt]) fun hi' ↦ ?_, ?_⟩
    · simpa [Function.update, Finset.prod_insert ha, Finset.prod_ite_of_false (fun _ hx ha' ↦
        ha (ha' ▸ hx) : ∀ x ∈ s', x ≠ a)] using lt_of_lt_of_le hβ (mul_le_mul_right hr'.le _)
    · rw [Function.update_of_ne (fun h ↦ ha (h ▸ hi') : i ≠ a)]
      exact hr'_lt i hi'

/-- A strict, finite product inequality in `ENNReal`: if every factor strictly increases and the
upper factors are positive and finite, then the products are strictly ordered. -/
theorem prod_lt_prod_of_lt {ι : Type*} [Fintype ι] [Nonempty ι]
    {f g : ι → ENNReal} (hlt : ∀ i, f i < g i) (hg0 : ∀ i, g i ≠ 0) (hgtop : ∀ i, g i ≠ ⊤) :
    ∏ i, f i < ∏ i, g i := by
  classical
  obtain ⟨i0⟩ := ‹Nonempty ι›
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0),
      ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i0)]
  refine lt_of_le_of_lt (mul_le_mul_right (Finset.prod_le_prod' fun i _ => (hlt i).le) (f i0))
    (ENNReal.mul_lt_mul_left ?_ ?_ (hlt i0))
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => hg0 i
  · exact ENNReal.prod_ne_top fun i _ => hgtop i

/-- **Dyadic decomposition of a finite sum.**
For nonnegative quantities `a : ι → ℝ≥0∞` and a threshold `t`, if every term `a j` (`j ∈ s`) is
below `2 ^ N * t`, the sum splits into the contribution of the *small* terms `a j < t` plus the
contributions of the `N` dyadic shells `2 ^ n * t ≤ a j < 2 ^ (n + 1) * t`, `n < N`.  The cutoff
`t` and the number of shells `N` are free parameters; choosing `t` controls the size of the small
part and `N` only has to be large enough to dominate every term. -/
theorem sum_eq_sum_filter_lt_add_sum_range_dyadic {ι : Type*}
    (a : ι → ℝ≥0∞) (t : ℝ≥0∞) :
    ∀ (N : ℕ) (s : Finset ι), (∀ j ∈ s, a j < 2 ^ N * t) →
      ∑ j ∈ s, a j
        = (∑ j ∈ {j ∈ s | a j < t}, a j)
          + ∑ n ∈ Finset.range N,
              ∑ j ∈ {j ∈ s | 2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t}, a j := by
  classical
  have hpow : ∀ (m k : ℕ), m ≤ k → (2 : ℝ≥0∞) ^ m * t ≤ 2 ^ k * t := fun m k h =>
    mul_le_mul' (pow_le_pow_right₀ (by norm_num) h) le_rfl
  intro N
  induction N with
  | zero =>
    intro s hs
    simp only [pow_zero, one_mul] at hs
    rw [Finset.range_zero, Finset.sum_empty, add_zero,
        Finset.filter_true_of_mem (fun j hj => hs j hj)]
  | succ N ih =>
    intro s hs
    have key := Finset.sum_filter_add_sum_filter_not s (fun j => a j < 2 ^ N * t) a
    have hih := ih {j ∈ s | a j < 2 ^ N * t}
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have htN : t ≤ (2 : ℝ≥0∞) ^ N * t := by simpa using hpow 0 N (Nat.zero_le N)
    have hsmall : {j ∈ {j ∈ s | a j < 2 ^ N * t} | a j < t}
        = {j ∈ s | a j < t} := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun j _ =>
        ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h htN, h⟩⟩
    have hshell : ∀ n ∈ Finset.range N,
        {j ∈ {j ∈ s | a j < 2 ^ N * t} |
            2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t}
          = {j ∈ s | 2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t} := by
      intro n hn
      rw [Finset.filter_filter]
      have hle : (2 : ℝ≥0∞) ^ (n + 1) * t ≤ 2 ^ N * t := hpow (n + 1) N (Finset.mem_range.mp hn)
      exact Finset.filter_congr fun j _ =>
        ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le h.2 hle, h⟩⟩
    have hnot : {j ∈ s | ¬ a j < 2 ^ N * t}
        = {j ∈ s | 2 ^ N * t ≤ a j ∧ a j < 2 ^ (N + 1) * t} :=
      Finset.filter_congr fun j hj =>
        ⟨fun h => ⟨not_lt.mp h, hs j hj⟩, fun h => not_lt.mpr h.1⟩
    have hrange : ∑ n ∈ Finset.range N,
          ∑ j ∈ {j ∈ {j ∈ s | a j < 2 ^ N * t} |
              2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t}, a j
        = ∑ n ∈ Finset.range N,
            ∑ j ∈ {j ∈ s | 2 ^ n * t ≤ a j ∧ a j < 2 ^ (n + 1) * t}, a j :=
      Finset.sum_congr rfl fun n hn => by rw [hshell n hn]
    rw [← key, hih, hrange, hsmall, hnot, Finset.sum_range_succ, add_assoc]

lemma ofReal_smul_le_ofReal_iff {x y : ℝ} (hy : 0 ≤ y) (a : NNReal) :
    ENNReal.ofReal x ≤ a • ENNReal.ofReal y ↔ x ≤ a • y := by
  have ha : 0 ≤ (a : ℝ) := a.coe_nonneg
  have hy' : 0 ≤ a • y := by
    positivity
  have h_smul_eq : a • ENNReal.ofReal y = ENNReal.ofReal (a • y) := by
    rw [NNReal.smul_def, smul_eq_mul, ENNReal.ofReal_mul, ENNReal.ofReal_coe_nnreal]
    · rfl
    · exact ha
  rw [h_smul_eq]
  exact ENNReal.ofReal_le_ofReal_iff hy'

/-- Blueprint `lem:rpowVolumeRatio`: in `[0, ∞]`, `x ^ ϖ * y ^ (-ϖ) = (x / y) ^ ϖ` for `ϖ > 0`. -/
theorem rpow_mul_inv_rpow_eq_div_rpow {ϖ : ℝ} (hϖ : 0 ≤ ϖ) (x y : ENNReal) :
    x ^ ϖ * y ^ (-ϖ) = (x / y) ^ ϖ := by
  calc
    x ^ ϖ * y ^ (-ϖ) = x ^ ϖ * (y ^ ϖ)⁻¹ := by rw [rpow_neg]
    _ = x ^ ϖ / y ^ ϖ := by rw [← div_eq_mul_inv]
    _ = (x / y) ^ ϖ := by rw [← div_rpow_of_nonneg x y hϖ]

/-- **A mass bound survives enlarging its constant** (blueprint `lem:massBoundConstantWeaken`):
if `C ≤ C'` and `C⁻¹ * A ≤ B`, then `C'⁻¹ * A ≤ B`, the constants being natural numbers coerced
into `ℝ≥0∞` and inverted there. -/
theorem inv_natCast_mul_le_of_le {C C' : ℕ} (hC : C ≤ C') {A B : ℝ≥0∞}
    (h : ((C : ℝ≥0∞))⁻¹ * A ≤ B) : ((C' : ℝ≥0∞))⁻¹ * A ≤ B := by
  have h_inv : ((C' : ℝ≥0∞))⁻¹ ≤ ((C : ℝ≥0∞))⁻¹ :=
    ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr hC)
  have h_mul : ((C' : ℝ≥0∞))⁻¹ * A ≤ ((C : ℝ≥0∞))⁻¹ * A :=
    mul_le_mul_of_nonneg_right h_inv (zero_le (α := ℝ≥0∞) (a := A))
  exact le_trans h_mul h

/-- **Chaining two mass bounds whose constants are inverted in different places** (blueprint
`lem:factoringStep1Step2MassChain`): `C₁ : ℝ≥0` is inverted *before* coercing and `C₂ : ℕ` *after*,
and the conclusion inverts their product in `ℝ≥0`. Reconciling the two placements of the inverse is
the only use of `C₂ ≠ 0`. -/
theorem coe_inv_mul_le_of_coe_inv_mul_le_of_inv_natCast_mul_le {C₁ : ℝ≥0} {C₂ : ℕ}
    (hC₂ : C₂ ≠ 0) {A B I : ℝ≥0∞} (h₁ : ((C₁⁻¹ : ℝ≥0) : ℝ≥0∞) * A ≤ B)
    (h₂ : ((C₂ : ℝ≥0∞))⁻¹ * B ≤ I) :
    ((((C₁ * (C₂ : ℝ≥0))⁻¹ : ℝ≥0)) : ℝ≥0∞) * A ≤ I := by
  have hC₂' : (C₂ : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hC₂
  have hkey : ((C₂ : ℝ≥0∞))⁻¹ * ((C₁⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (((C₁ * (C₂ : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    simp [hC₂]
  have h_mul : ((C₂ : ℝ≥0∞))⁻¹ * (((C₁⁻¹ : ℝ≥0) : ℝ≥0∞) * A) ≤
      ((C₂ : ℝ≥0∞))⁻¹ * B := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_right h₁ ((C₂ : ℝ≥0∞))⁻¹
  have h0 : (((C₂ : ℝ≥0∞))⁻¹ * ((C₁⁻¹ : ℝ≥0) : ℝ≥0∞)) * A ≤
      ((C₂ : ℝ≥0∞))⁻¹ * B := by
    simpa [mul_assoc] using h_mul
  have h1 : ((((C₁ * (C₂ : ℝ≥0))⁻¹ : ℝ≥0)) : ℝ≥0∞) * A ≤
      ((C₂ : ℝ≥0∞))⁻¹ * B := by
    rw [← hkey]
    exact h0
  exact le_trans h1 h₂

/-- **Dividing by a quotient in `[0, ∞]`** (blueprint `lem:ennrealDivQuotient`).

`A / (X / Y) = A · Y / X`, at the two disjunctive side conditions `X ≠ 0 ∨ Y ≠ 0` and
`X ≠ ∞ ∨ Y ≠ ∞`.

**The two side conditions are exactly what the failure of cancellativity in `[0, ∞]` costs**: they
are what `ENNReal.div_mul` asks, and the identity genuinely fails at `X = Y = 0` and at
`X = Y = ∞`.  The proof is one appeal to `ENNReal.div_mul` — the remaining rearrangement
`A · Y / X = (A / X) · Y` is commutativity and associativity of multiplication and needs no
hypothesis at all.

**It is read at two sites, which is what makes it worth a name.**  At `A = U`, `X = D` and
`Y = C_fact` it is the step `hUdiv` of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_factorization`, licensed there by `C_fact ≠ 0` and
`D ≠ ∞`; and at `A = C_fact · U`, `X = c (N_a/N_b) τ ²` and `Y = |B|` it is the step `hUdiv` of
`Kakeya.ml1Boot.frostmanConstIn_anchor_le_of_count`, licensed there by `|B| ≠ 0` and by the
finiteness of `Kakeya.ml1Boot.anchorCountAtTestedBody.coe_numerator_ne_top`.  It is about five lines
in each, and it is the step that turns `C_fact U / D` into `C_fact U |B| / (c (N_a/N_b) τ ²)`. -/
theorem div_div_eq_mul_div {A X Y : ℝ≥0∞} (h0 : X ≠ 0 ∨ Y ≠ 0) (htop : X ≠ ⊤ ∨ Y ≠ ⊤) :
    A / (X / Y) = A * Y / X := by
  rw [← ENNReal.div_mul (a := A) (b := X) (c := Y) (h0 := h0) (htop := htop)]
  simp [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm]

end ENNReal

namespace NNReal

/-- **The normalization identity** (blueprint `lem:ennrealNormalizationIdentity`, first display).

`(c / C) · p · (τ / θ) ² = (c · p · τ ²) / (C · θ ²)` for nonnegative reals, **with no hypothesis
at all**.  At `C ≠ 0` and `θ ≠ 0` the denominators `C`, `θ ²` and `C θ ²` are all nonzero, so
multiplying through and cancelling reduces the identity to a reordering of the factors of
`c p τ ² C θ ²`; the nonnegative reals being a semifield, this is one `field_simp`.

**The two nonvanishing hypotheses the blueprint attaches to this display are absent here, and their
absence is a strengthening.**  `ℝ≥0` is a `DivisionSemiring` with the junk value `x / 0 = 0`, so at
`C = 0` both sides are `0` — the left because `c / C = 0`, the right because its denominator
vanishes — and likewise at `θ = 0`, where the left has the factor `(τ / 0) ² = 0` and the right the
denominator `C · 0 = 0`.  So the degenerate cases are equalities too and the identity is
unconditional.  **This is the one respect in which it differs from
`ENNReal.coe_div_mul_coe_div_sq_eq`**, whose two hypotheses are genuinely needed: in `[0, ∞]` the
right-hand side at `C = 0` is `c p τ ² / 0 = ∞` whenever the numerator is nonzero, while the left is
still `0`.

It is the step `hident_nn` of `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share_normalized`, read
there at `c = Kakeya.ml1Boot.anchorCountAtTestedBody.c 3 Cu κ`, `C = Tube.volume_le.C 3`,
`p = N_a/N_b`, `τ = ρ_b` and `θ = Λ ρ_a`, where the nonvanishing that the `[0, ∞]` form needs is
`Tube.volume_le.C_pos` at `C` and the half `0 < Λθ` of that lemma's extra hypothesis at `θ`.
**Neither `τ` nor `p` nor `c` is asked to be nonzero**, and no upper bound occurs anywhere in it. -/
theorem div_mul_div_sq_eq (c C p τ θ : ℝ≥0) :
    c / C * p * (τ / θ) ^ 2 = c * p * τ ^ 2 / (C * θ ^ 2) := by
  rw [div_pow, div_mul_eq_mul_div₀, div_mul_div_comm]

end NNReal

namespace ENNReal

/-- **The normalization identity in `[0, ∞]`** (blueprint `lem:ennrealNormalizationIdentity`,
second display).

The image of `NNReal.div_mul_div_sq_eq` under the coercion `[0, ∞) → [0, ∞]`, which commutes with
products and with powers (`ENNReal.coe_mul`, `ENNReal.coe_pow`) and, at a nonzero denominator, with
quotients (`ENNReal.coe_div`, whose hypothesis is exactly that nonvanishing, read at `C`, at `θ` and
at `C θ ²`).

**Here the two nonvanishing hypotheses are genuinely binders**, unlike at `NNReal.div_mul_div_sq_eq`,
which needs neither: `[0, ∞]` has `x / 0 = ∞` for `x ≠ 0`, so at `C = 0` or `θ = 0` the right-hand
side is `∞` while the left is still `0`, and the identity fails.

**It is elementary in `[0, ∞)` and the whole Lean cost is the transport across the coercion**, which
is why naming it once is worth it: it is the step `hident` of
`Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share_normalized`, about twenty of that proof's
forty-five lines, after which that proof is the volume upper bound of
`Kakeya.ml1Boot.volume_testedBody_bracket`, one monotonicity of division in the denominator and one
appeal to `Kakeya.ml1Boot.densityIn_ge_of_completedFibre_share`. -/
theorem coe_div_mul_coe_div_sq_eq {c C p τ θ : ℝ≥0} (hC : C ≠ 0) (hθ : θ ≠ 0) :
    ((c / C : ℝ≥0) : ℝ≥0∞) * (p : ℝ≥0∞) * (((τ / θ : ℝ≥0) : ℝ≥0∞)) ^ 2
      = (c : ℝ≥0∞) * (p : ℝ≥0∞) * (τ : ℝ≥0∞) ^ 2 / ((C : ℝ≥0∞) * (θ : ℝ≥0∞) ^ 2) := by
  have h := NNReal.div_mul_div_sq_eq c C p τ θ
  have hden : C * θ ^ 2 ≠ 0 := mul_ne_zero hC (pow_ne_zero 2 hθ)
  have hlhs :
      ((c / C : ℝ≥0) : ℝ≥0∞) * (p : ℝ≥0∞) * (((τ / θ : ℝ≥0) : ℝ≥0∞)) ^ 2
        = ((c / C * p * (τ / θ) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    push_cast
    rfl
  rw [hlhs]
  rw [h]
  rw [ENNReal.coe_div hden]
  push_cast
  ring
/-- Two sub-polynomial bounds multiply: if `C ^ 2 ≤ δ ^ (-η)` and `M ≤ δ ^ (-(e - η))`, then
`C ^ 2 * M ≤ δ ^ (-e)`, the exponents `η` and `e - η` summing to `e`.

No positivity of `e` and no finiteness of `M` is needed: `mul_le_mul'` holds in `ℝ≥0∞`
unconditionally, and `0 < δ` is what makes `ENNReal.rpow_add` available. -/
theorem sq_mul_le_rpow_neg {δ : ℝ≥0} (hδ : 0 < δ) {C M : ℝ≥0∞} {e η : ℝ}
    (hC : C ^ 2 ≤ (δ : ℝ≥0∞) ^ (-η)) (hM : M ≤ (δ : ℝ≥0∞) ^ (-(e - η))) :
    C ^ 2 * M ≤ (δ : ℝ≥0∞) ^ (-e) := by
  have h0 : (δ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
  have hTop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc C ^ 2 * M ≤ (δ : ℝ≥0∞) ^ (-η) * (δ : ℝ≥0∞) ^ (-(e - η)) := mul_le_mul' hC hM
    _ = (δ : ℝ≥0∞) ^ ((-η) + (-(e - η))) := (ENNReal.rpow_add _ _ h0 hTop).symm
    _ = (δ : ℝ≥0∞) ^ (-e) := by congr 1; ring

end ENNReal

namespace Kakeya

open scoped NNReal Real

/-- For a finite sum of `ENNReal`-valued measure quantities that are each `≠ ⊤`,
the sum equals `ENNReal.ofReal` of the sum of `.toReal`s. -/
lemma sum_volume_ofReal_eq
    {α ι : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (s : Finset ι) (f : ι → Set α) (hfin : ∀ i ∈ s, μ (f i) ≠ ⊤) :
    (∑ i ∈ s, μ (f i)) = ENNReal.ofReal (∑ i ∈ s, (μ (f i)).toReal) := by
  rw [← ENNReal.ofReal_toReal
      (a := ∑ i ∈ s, μ (f i))
      (ENNReal.sum_ne_top.mpr fun i hi => hfin i hi),
    ENNReal.toReal_sum (fun i hi => hfin i hi)]

/-- `((M : ENNReal) + 1) = ENNReal.ofReal ((M : ℝ) + 1)` for a natural `M`. -/
lemma enn_natAdd_one_eq_ofReal (M : ℕ) :
    ((M : ENNReal) + 1) = ENNReal.ofReal ((M : ℝ) + 1) := by
  rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- Rewrite a product of a natural cardinality and a positive `NNReal` power as an
`ENNReal.ofReal`. -/
lemma card_mul_δ_pow_ofReal {δ : NNReal} (hδ_pos : 0 < (δ : ℝ))
    (s_card n : ℕ) :
    ((s_card : ENNReal) * (δ : ENNReal) ^ (n - 1)) =
      ENNReal.ofReal ((s_card : ℝ) * (δ : ℝ) ^ (n - 1)) := by
  rw [show (s_card : ENNReal) = ENNReal.ofReal (s_card : ℝ) from
        (ENNReal.ofReal_natCast _).symm,
      show (δ : ENNReal) ^ (n - 1) = ENNReal.ofReal ((δ : ℝ) ^ (n - 1)) from by
        rw [ENNReal.ofReal_pow hδ_pos.le, ENNReal.ofReal_coe_nnreal],
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

/-! ### Pigeonhole and refinement-loss arithmetic -/

/-- A pigeonhole mass bound over `N` cells: if `S ≤ N • T` then `N⁻¹ · S ≤ T` in `ℝ≥0∞`. -/
lemma ennreal_natinv_mul_le {N : ℕ} (hN : N ≠ 0) {S T : ENNReal}
    (h : S ≤ (N : ENNReal) * T) : (N : ENNReal)⁻¹ * S ≤ T := by
  have hne : (N : ENNReal) ≠ 0 := by exact_mod_cast hN
  calc (N : ENNReal)⁻¹ * S ≤ (N : ENNReal)⁻¹ * ((N : ENNReal) * T) := by gcongr
    _ = T := by rw [← mul_assoc, ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top N), one_mul]

/-- Composition of three successive refinement losses `k⁻¹`, `l` and `c` into the single retained
fraction `c · l · k⁻¹`. -/
lemma coe_mul_le_of_three_step {c l : NNReal} {k : ℕ} (hk : 0 < k) {u v w z : ENNReal}
    (h1 : u ≤ (k : ENNReal) * v) (h2 : (l : ENNReal) * v ≤ w) (h3 : (c : ENNReal) * w ≤ z) :
    ((c * l * (k : NNReal)⁻¹ : NNReal) : ENNReal) * u ≤ z := by
  have hknn : (0 : NNReal) < (k : NNReal) := by exact_mod_cast hk
  have hkey : ((c * l * (k : NNReal)⁻¹ : NNReal) : ENNReal) * (k : ENNReal)
      = (c : ENNReal) * (l : ENNReal) := by
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hknn.ne', ENNReal.coe_natCast,
      mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hk.ne') (by simp), mul_one]
  calc ((c * l * (k : NNReal)⁻¹ : NNReal) : ENNReal) * u
      ≤ ((c * l * (k : NNReal)⁻¹ : NNReal) : ENNReal) * ((k : ENNReal) * v) := by gcongr
    _ = (c : ENNReal) * ((l : ENNReal) * v) := by rw [← mul_assoc, hkey, mul_assoc]
    _ ≤ (c : ENNReal) * w := by gcongr
    _ ≤ z := h3

/-- Transport of a sub-polynomial bound `B ≤ Cc · a ^ (-ε)` from the `a`-scale to the smaller
`δ`-scale, in `ℝ≥0`. -/
lemma toNNReal_le_toNNReal_mul_rpow_neg {B Cc : ℝ} {a δ : NNReal} (hB : 0 < B) (hCc : 0 < Cc)
    (hδ : 0 < δ) (hδa : δ ≤ a) {ε : ℝ} (hε : 0 < ε) (h : B ≤ Cc * (a : ℝ) ^ (-ε)) :
    B.toNNReal ≤ Cc.toNNReal * δ ^ (-ε) := by
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ hCc.le, NNReal.coe_rpow,
    Real.coe_toNNReal _ hB.le]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast hδ) (by exact_mod_cast hδa) (by linarith)) hCc.le)

/-- The retained fraction `c · S⁻¹ · k⁻¹` dominates `C⁻¹ · δ ^ ε` as soon as its reciprocal
`c⁻¹ · S · k` is bounded by `C · δ ^ (-ε)`. -/
lemma inv_mul_rpow_le_frac {ε : ℝ} {δ c C : NNReal} {S : ℝ} {k : ℕ}
    (hδ : 0 < δ) (hc : 0 < c) (hS : 0 < S) (hk : 0 < k) (hC : 0 < C)
    (hbd : (δ : ℝ) ^ ε * ((c : ℝ)⁻¹ * S * ((k : ℕ) : ℝ)) ≤ (C : ℝ)) :
    C⁻¹ * δ ^ ε ≤ c * (Real.toNNReal S)⁻¹ * ((k : ℕ) : NNReal)⁻¹ := by
  have hknn : (0 : NNReal) < ((k : ℕ) : NNReal) := by exact_mod_cast hk
  have hSnn : (0 : NNReal) < Real.toNNReal S := Real.toNNReal_pos.mpr hS
  set f : NNReal := c * (Real.toNNReal S)⁻¹ * ((k : ℕ) : NNReal)⁻¹ with hf
  have hfpos : 0 < f := mul_pos (mul_pos hc (inv_pos.mpr hSnn)) (inv_pos.mpr hknn)
  have hle : δ ^ ε * f⁻¹ ≤ C := by
    have h : (f : ℝ) = (c : ℝ) * S⁻¹ * ((k : ℕ) : ℝ)⁻¹ := by
      rw [hf]; push_cast [Real.coe_toNNReal _ hS.le]; ring
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_inv, h, mul_inv, mul_inv,
      inv_inv, inv_inv]
    exact hbd
  have hδmul : δ ^ (-ε) * δ ^ ε = 1 := by
    rw [← NNReal.rpow_add hδ.ne', neg_add_cancel, NNReal.rpow_zero]
  have h1 : C⁻¹ ≤ (δ ^ ε * f⁻¹)⁻¹ :=
    (inv_le_inv₀ hC (mul_pos (NNReal.rpow_pos hδ) (inv_pos.mpr hfpos))).mpr hle
  calc C⁻¹ * δ ^ ε ≤ (δ ^ ε * f⁻¹)⁻¹ * δ ^ ε := by gcongr
    _ = f := by
        rw [mul_inv, inv_inv, mul_comm (δ ^ ε)⁻¹ f, mul_assoc, ← NNReal.rpow_neg, hδmul, mul_one]

end Kakeya
