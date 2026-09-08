/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# The stable refinement, and its compatibility with the selection

The saturated Item 2 route runs on shadings carrying two *global* angular data: the one-sided angle
upper bound `Kakeya.HasMaxPlankAngleBound` and a global angular stability clause.  Those are the two
hypotheses of `Plank.localAngleConcentration_of_saturated_scaled`, from which hypothesis (5) of the
dense-box chain follows for every saturated box-local family.

This file supplies them.  There is nothing to construct: they are two of the conclusions of GWZ
Lemma 6.11, taken in the reserve form `Kakeya.findingTypicalAngleOfIntersection_stable_reserve`,
whose stability clause is already at the sub-polynomial scale `Kakeya.plankAngleScaleB a`.
What this file does is repackage that output in the exact shape the route consumes, and record
honestly what
the repackaging costs:

* the stability scale is `2 · Kakeya.plankAngleScaleB a`, not `Kakeya.plankAngleScaleB a`.  The
  factor `2` is genuine: the global `θ` is selected by a dyadic pigeonhole across fibres and so
  agrees with the fibre-local typical angle only up to the constant `2` of the angle comparison.
  This is why `Plank.localAngleConcentration_of_saturated_scaled` exists;
* the fibre-retention scale is the output scale `Aout(a) = max 2 (Kakeya.plankAngleScaleA a)`, at
  which `2 ≤ Aout(a)` holds by `le_max_left` for every `a`.  Delivering the clause at the *constant*
  `2` instead would need `2 ≤ Kakeya.plankAngleScaleA a`, which fails as `a → 1⁻`; that is where the
  old smallness threshold came from, and taking the clause from the reserve-scale producer removes
  it;
* the refinement loss is `c_stb · a^ε`, **not** a uniform constant.  `c_stb = C⁻¹` with
  `C = C(ε, C₀, N_exp)` fixed before the configuration, but the `a^ε` is the retained-fraction of
  Lemma 6.11 and cannot be removed.  Every downstream constant of the Item 2 ledger therefore
  carries `a^ε` as well as `c_stb`, exactly as `c_P` and `c_λ` of `Kakeya.plankReduction` do.

Compatibility with the selection layer is free: the refinement returns equal carriers and smaller
shades, so the coherence `(Y' i).carrier = (V i).carrier` and any containment of the shades in a
representative prism are inherited, and `Plank.exists_shift_halfBox_capture_of_fullness` applied to
`(s, Y')` returns its shift and window at the same absolute constants.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-- **A `c`-refinement transports a fullness lower bound.**  The `c`-mass bound lower-bounds the
shade numerator while `s' ⊆ s` with equal carriers on `s'` shrinks the carrier denominator, so
`c · λ(s,V) ≤ λ(s',V')`. -/
theorem fullness_ge_of_isCRefinement
    {s' s : Finset ι} {V' V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : ℝ≥0}
    (h : ShadedBody.IsCRefinement s' V' s V c) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V' := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.coe_fullness s V,
    ShadedBody.coe_fullness s' V']
  dsimp [ShadedBody.fullness']
  rcases h with ⟨⟨hsub, hbody⟩, hmass⟩
  have hDS' : ∑ i ∈ s', volume (V' i).carrier ≤ ∑ i ∈ s, volume (V i).carrier := by
    calc
      ∑ i ∈ s', volume (V' i).carrier = ∑ i ∈ s', volume (V i).carrier := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [congrArg (fun (cb : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) =>
          volume (ConvexSpaceBody.carrier cb)) (hbody i hi).1]
      _ ≤ ∑ i ∈ s, volume (V i).carrier := Finset.sum_le_sum_of_subset hsub
  calc
    (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / ∑ i ∈ s, volume (V i).carrier)
        = ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) / ∑ i ∈ s, volume (V i).carrier := by
      rw [mul_div_assoc]
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / ∑ i ∈ s, volume (V i).carrier :=
      ENNReal.div_le_div_right hmass (∑ i ∈ s, volume (V i).carrier)
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / ∑ i ∈ s', volume (V' i).carrier :=
      ENNReal.div_le_div_left hDS' (∑ i ∈ s', volume (V' i).shade)

/-- **`2 ≤ Aout(a)`, with no hypothesis at all.**  The output scale
`Aout(a) = max 2 (Kakeya.plankAngleScaleA a)` satisfies the `2 ≤ A` requirement of every consumer of
the stability clause by `le_max_left`, for every `a`.  This is what replaces the smallness threshold
`a < exp(-(log 2)^2)` that the earlier form of `Plank.exists_stableRefinement_compatible` needed in
order to weaken `Kakeya.plankAngleScaleA a` down to `2`: since `Kakeya.plankAngleScaleA a → 1` as
`a → 1⁻`, that weakening is genuinely unavailable near `1`, whereas `Aout` is above `2` by
construction. -/
theorem two_le_max_two_plankAngleScaleA (a : ℝ≥0) :
    (2 : ℝ) ≤ max 2 (Kakeya.plankAngleScaleA a) :=
  le_max_left _ _

/-- **The output scale fits inside the reserve scale, at every `a`.**  For `κ ≥ 2` and
`0 < a < 1`, writing `A = Kakeya.plankAngleScaleA a ≥ 1`,

`Aout(a) = max 2 A ≤ 2 ≤ κ·A²` and `Aout(a) = max 2 A ≤ 2·A ≤ κ·A²`,

so `max 2 (Kakeya.plankAngleScaleA a) ≤ Kakeya.plankReserveScale κ a`.  Since the stability
clause is *stronger* at the larger scale, this is exactly what lets a producer at the reserve
scale — namely
`Kakeya.findingTypicalAngleOfIntersection_stable_reserve`, which is threshold-free — deliver the
clause at `Aout(a)`.

Nothing here compares `Kakeya.plankAngleScaleA a` with `Kakeya.plankAngleScaleB a`: the false
inequality `A(a)² ≤ B(a)` (valid only for `a ≤ e^{-16}`) is itself a smallness threshold and is
never used. -/
theorem max_two_plankAngleScaleA_le_plankReserveScale {kappa : ℝ} (hkappa : 2 ≤ kappa)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    max 2 (Kakeya.plankAngleScaleA a) ≤ Kakeya.plankReserveScale kappa a := by
  rw [Kakeya.plankReserveScale]
  have hA : 1 < Kakeya.plankAngleScaleA a := Kakeya.one_lt_plankAngleScaleA ha ha1
  have hA_nonneg : 0 ≤ Kakeya.plankAngleScaleA a := by linarith
  have hA_sq_nonneg : 0 ≤ Kakeya.plankAngleScaleA a * Kakeya.plankAngleScaleA a := by nlinarith
  apply max_le
  · -- 2 ≤ kappa * (A * A)
    nlinarith
  · -- A ≤ kappa * (A * A)
    nlinarith

/-- **The stable refinement, and its compatibility with the selection.**  Fix an angle constant
`Cang ≥ 1`, a refinement exponent `ε > 0` and the plank-count data `(C₀, Nexp)`.  There is a
`c_stb ∈ (0,1]`, quantified before every geometric datum, such that every configuration satisfying
the hypotheses of GWZ Lemma 6.11 — for **every** `0 < a < 1`, with no smallness threshold — together
with the global fullness bound `a^η ≤ λ(s,Y)` admits shadings `Y'` and a typical angle
`θ ∈ [a/b, 1]` with

1. equal carriers and smaller shades, `(Y' i).carrier = (Y i).carrier` and
   `(Y' i).shade ⊆ (Y i).shade` — whence the coherence and the representative containment of the
   selection layer are inherited verbatim;
2. the angle upper bound `Kakeya.HasMaxPlankAngleBound s Y' V θ Cang`;
3. the global stability clause at
   `(θ, 2 · Kakeya.plankAngleScaleB a, Aout(a))` with the *output scale*
   `Aout(a) = max 2 (Kakeya.plankAngleScaleA a)`;
4. the retained fullness `c_stb · a^ε · a^η ≤ λ(s,Y')`.

Items 2 and 3 are exactly the two global data that
`Plank.localAngleConcentration_of_saturated_scaled` consumes at `K = 2`, so composing this with that
lemma discharges hypothesis (5) for every saturated box-local family of the route.  That consumer
asks `2 ≤ A`, which `Plank.two_le_max_two_plankAngleScaleA` supplies at `A = Aout(a)` with no
hypothesis.

**Why `Aout(a)` and not `2`.**  The `2 ≤ A` hypothesis downstream is load-bearing — it is what turns
`A⁻¹ ≤ 1/2` into the "at least half the pairs sit at angle ≥ ρ" pair count — so it cannot be
weakened.  Delivering the clause at the *constant* `2` is what forced the old threshold: GWZ
Lemma 6.11 produces the clause at `Kakeya.plankAngleScaleA a`, the clause is stronger at larger
scales, and `2 ≤ Kakeya.plankAngleScaleA a` fails as `a → 1⁻`.  The repair is to produce at the
reserve scale instead: `Kakeya.findingTypicalAngleOfIntersection_stable_reserve` delivers the clause
at `Kakeya.plankReserveScale 2 a = 2 · plankAngleScaleA a ²` with no threshold, and
`Plank.max_two_plankAngleScaleA_le_plankReserveScale` shows `Aout(a)` sits below that scale
for every `0 < a < 1`.  This is the same pattern as
`Kakeya.representativeWitness_strong_uniform`, which already delivers its two-sided
typical-angle conclusion at `Aout(a)`.

The `a^ε` in item 4 is honest and unavoidable: it is the retained fraction of GWZ Lemma 6.11, whose
angular selection is what makes the stable set large in the first place.  A statement of item 4 with
a uniform constant and no `a^ε` would not follow from Lemma 6.11 and is not claimed. -/
theorem exists_stableRefinement_compatible (Cang : ℝ≥0) (hCang : 1 ≤ Cang)
    {ε : ℝ} (hε : 0 < ε) (C₀ : ℝ≥0) (Nexp : ℝ) :
    ∃ cStb : ℝ≥0, 0 < cStb ∧ cStb ≤ 1 ∧
      ∀ {ι : Type*} (s : Finset ι) {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {η : ℝ},
        0 < a → a < 1 → 0 < b → 0 < η →
        (∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
        (s.card : ℝ≥0) ≤ C₀ * a ^ (-Nexp) →
        a ^ η ≤ ShadedBody.fullness s Y →
        ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
          (∀ i ∈ s, (Y' i).carrier = (Y i).carrier) ∧
          (∀ i ∈ s, (Y' i).shade ⊆ (Y i).shade) ∧
          a / b ≤ θ ∧ θ ≤ 1 ∧
          Kakeya.HasMaxPlankAngleBound s Y' V θ Cang ∧
          (∀ x ∈ ⋃ i ∈ s, (Y' i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y' x,
            (max 2 (Kakeya.plankAngleScaleA a))⁻¹ * ((Kakeya.shadeFibre s Y' x).card : ℝ)
                ≤ (t.card : ℝ) →
              (θ : ℝ) / (2 * Kakeya.plankAngleScaleB a)
                ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) ∧
          cStb * a ^ ε * a ^ η ≤ ShadedBody.fullness s Y' := by
  -- Apply the reserve-scale producer.
  have hkappa : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
  obtain ⟨C, hC2le, hC⟩ :=
    Kakeya.findingTypicalAngleOfIntersection_stable_reserve (kappa := 2) hkappa hε C₀ Nexp
  have hCpos : 0 < (C : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)) hC2le
  have hC1le : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast le_trans (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hC2le
  set cStb : ℝ≥0 := C⁻¹ with hcStb
  have hcStb_pos : 0 < cStb := by
    rw [hcStb]
    have hCpos' : 0 < (C : ℝ≥0) := by exact_mod_cast hCpos
    exact inv_pos.mpr hCpos'
  have hcStb_le_one : cStb ≤ 1 := by
    have hCpos' : 0 < (C : ℝ≥0) := by exact_mod_cast hCpos
    have : (cStb : ℝ) ≤ 1 := by
      rw [hcStb, NNReal.coe_inv C]
      exact (inv_le_one₀ hCpos).mpr hC1le
    exact_mod_cast this
  refine ⟨cStb, hcStb_pos, hcStb_le_one, ?_⟩
  intro ι s a b hab hb1 V Y η ha ha1 hb hη hYP _hed hμ hcard hfull
  have hproducer := hC s Y (a := a) (b := b) ha ha1 hab hb1 V hYP (η := η) hη hμ hcard
  rcases hproducer with ⟨Y', θ, hRef, hθlb, hθub, hConst, hTwoSided, hStab, hAngleBoundPair⟩
  rcases hAngleBoundPair with ⟨hStab2B, hAngleBound⟩
  -- hRef : ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * a ^ ε)
  -- hθlb : a / b ≤ θ,  hθub : θ ≤ 1
  -- hAngleBound : HasMaxPlankAngleBound s Y' V θ 1
  -- hStab2B : ∀ x ∈ ⋃ i ∈ s, (Y' i).shade, ∀ t ⊆ shadeFibre s Y' x,
  --            (plankReserveScale 2 a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
  --            (θ : ℝ) ≤ 2 * plankAngleScaleB a * ((maxPlankAngle V t : ℝ≥0) : ℝ)
  -- Extract the refinement data.
  rcases hRef with ⟨⟨hsub, hbody⟩, hmass⟩
  have hcarrier : ∀ i ∈ s, (Y' i).carrier = (Y i).carrier := by
    intro i hi
    exact congrArg (fun (cb : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) => cb.carrier) (hbody
        i hi).1
  have hshade : ∀ i ∈ s, (Y' i).shade ⊆ (Y i).shade := by
    intro i hi
    exact (hbody i hi).2
  -- Item (c): HasMaxPlankAngleBound s Y' V θ Cang, weakened from C = 1.
  have hAngleBoundCang : Kakeya.HasMaxPlankAngleBound s Y' V θ Cang := by
    intro x hx
    have hx' : Kakeya.maxPlankAngle V (Kakeya.shadeFibre s Y' x) ≤ (1 : ℝ≥0) * θ := hAngleBound x hx
    have hθ_nonneg' : (0 : ℝ≥0) ≤ θ := by
      have h0_div : (0 : ℝ≥0) ≤ a / b := by positivity
      have : a / b ≤ θ := hθlb
      exact le_trans h0_div this
    calc
      Kakeya.maxPlankAngle V (Kakeya.shadeFibre s Y' x) ≤ (1 : ℝ≥0) * θ := hx'
      _ = θ := by simp
      _ ≤ Cang * θ := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right hCang hθ_nonneg'
  -- Item (d): the stability clause at (max 2 (plankAngleScaleA a))⁻¹ retention scale.
  have hStabClause : ∀ x ∈ ⋃ i ∈ s, (Y' i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y' x,
      (max 2 (Kakeya.plankAngleScaleA a))⁻¹ * ((Kakeya.shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
      (θ : ℝ) / (2 * Kakeya.plankAngleScaleB a) ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := by
    intro x hx t ht hcard
    have hreserveScale_pos : 0 < Kakeya.plankReserveScale (2 : ℝ) a := by
      have h_one_lt : 1 < Kakeya.plankReserveScale (2 : ℝ) a :=
        Kakeya.one_lt_plankReserveScale (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) ha ha1
      exact by linarith
    have hmax_pos : 0 < max 2 (Kakeya.plankAngleScaleA a) := by
      have : (2 : ℝ) ≤ max 2 (Kakeya.plankAngleScaleA a) := le_max_left _ _
      nlinarith
    have hscale_le : max 2 (Kakeya.plankAngleScaleA a) ≤ Kakeya.plankReserveScale (2 : ℝ) a :=
      max_two_plankAngleScaleA_le_plankReserveScale (by norm_num : (2 : ℝ) ≤ (2 : ℝ)) ha ha1
    have hreserve_inv_le : (Kakeya.plankReserveScale (2 : ℝ) a)⁻¹ ≤ (max 2
        (Kakeya.plankAngleScaleA a))⁻¹ :=
      inv_anti₀ hmax_pos hscale_le
    have hcard' : (Kakeya.plankReserveScale (2 : ℝ) a)⁻¹ * ((Kakeya.shadeFibre s Y' x).card : ℝ)
        ≤ (t.card : ℝ) := by
      calc
        (Kakeya.plankReserveScale (2 : ℝ) a)⁻¹ * ((Kakeya.shadeFibre s Y' x).card : ℝ)
            ≤ (max 2 (Kakeya.plankAngleScaleA a))⁻¹ * ((Kakeya.shadeFibre s Y' x).card : ℝ) := by
              nlinarith
        _ ≤ (t.card : ℝ) := hcard
    have hθ_le : (θ : ℝ) ≤ 2 * Kakeya.plankAngleScaleB a * ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) :=
      hStab2B x hx t ht hcard'
    have hBpos : 0 < Kakeya.plankAngleScaleB a := by
      have hB1 : 1 < Kakeya.plankAngleScaleB a := Kakeya.one_lt_plankAngleScaleB ha ha1
      linarith
    have hpos_prod : 0 < 2 * Kakeya.plankAngleScaleB a := by nlinarith
    rw [div_le_iff₀ hpos_prod]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hθ_le
  -- Item (e): retained fullness.
  have hfullness : cStb * a ^ ε * a ^ η ≤ ShadedBody.fullness s Y' := by
    have hRef' : ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * a ^ ε) := by
      refine ⟨⟨hsub, hbody⟩, ?_⟩
      simpa [hcStb] using hmass
    calc
      cStb * a ^ ε * a ^ η = (C⁻¹ * a ^ ε) * (a ^ η : ℝ≥0) := by
        simp [hcStb, mul_assoc]
      _ ≤ (C⁻¹ * a ^ ε) * ShadedBody.fullness s Y := by
        gcongr
      _ ≤ ShadedBody.fullness s Y' := fullness_ge_of_isCRefinement hRef'
  -- Assemble the conclusion.
  refine ⟨Y', θ, hcarrier, hshade, hθlb, hθub, hAngleBoundCang, hStabClause, hfullness⟩

end Plank

end
