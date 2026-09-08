/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCover

/-!
# The `Δ_max` floor on a `ρ`-tube family in the unit ball, and the count budget it kills

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.  This file answers one question left open by the canonical-cover
row: **what is the exponent `a` in `Δ_max ≤ ρ^{-a}`, and does the count budget `a + c ≤ ζ' - ζ`
close?**

## The two `Δ_max`s, and why only one of them is small

GWZ's non-eccentric case carries *two* different maximal densities, and they behave oppositely.

* **The fine family.**  `upperBdDeltaMaxTildeTT` bounds `Δ_max(𝕋̃)` from **above**; in the Lean
  hierarchy this is `Kakeya.ML2Reduction.IsKatzTaoDividingWindow.middle_maxDensity_le`,
  `Δ_max(𝕋̃) ≤ C_⋆ δ̃^{-η_{j-1}}`.  Read at a scale `ρ ≤ δ̃^w` of the window this is
  `C_⋆ ρ^{-η_{j-1}/w}`, so for that family **`a = η_{j-1}/w`**, and on the parameter spine
  `a ≤ η_j/240` — a factor-`60` margin inside the budget `ζ' - ζ = η_j/4`
  (`spine_windowExponent_le`, `spine_count_budget_closes`).  This is the `Δ_max` that Lemma 9.1's
  *density* binder consumes, and it is already budgeted by `Kakeya.ML2Spine.IsSpine.dens_budget`.

* **The `ρ`-cover.**  The essential-distinctness refinement
  `Kakeya.Tube.refineToEssDistinctLeaves` divides by the maximal density of the family it
  refines — here the *pushed-down* `ρ`-tube family `outerTube … ρ (W k)`.  That quantity is
  bounded **below**, not above.  Every `ρ`-tube has volume at least `c₃ ρ²` and the whole family
  lies in the unit ball, whose volume is exactly `3 c₃`
  (`Kakeya.Tube.card_le_of_densityIn_le.C = 3`, `card_le_of_densityIn_le_C_eq_three`), so

  ```
  Δ_max ≥ |t| ρ² / 3    (`card_mul_sq_le_three_mul_maxDensity`)
  ```

  and the count clause `ρ^{-2-ζ'} ≤ |t|` upgrades this to `Δ_max ≥ ρ^{-ζ'}/3`
  (`rpow_neg_le_three_mul_maxDensity`).  Hence **`a ≥ ζ'`**, quantitatively
  `1/3 ≤ ρ^{ζ' - a}` (`one_third_le_rpow_sub_of_maxDensity_le`).  This is GWZ's own
  `tildeDeltaLargeDeltamax`, `Δ_max(𝕋̃_ρ) ≥ ρ^{-η_j}`, seen from the Lean side: the cardinality
  the count clause asserts *is* the density, so dividing by the density gives it all back.

## The consequence

The count budget of the canonical-cover route asks for `Δ_max ≤ ρ^{-a}` with `a + c ≤ ζ' - ζ`,
`c ≥ 0`.  Since `a ≥ ζ'` and `ζ ≥ 0`, that is impossible, and the contradiction is *unconditional*
in `ρ ∈ (0,1]`: `refineToEssDistinctLeaves.C 3 ≥ 4 > 3`
(`four_le_refineToEssDistinctLeaves_C_three`, which needs `Tube.le_volume.c 3 = 4π/9`,
`le_volume_c_three_coe`) while the chain forces
`refineToEssDistinctLeaves.C 3 ≤ 3`.  `not_count_budget_of_unitBall` is that refutation;
`not_upstairs_bundle_at` and `not_upstairs_bundle` are it at the exact hypothesis interface of the
canonical-cover row, at one scale and over Lemma 9.1's window respectively.  Five of the seven
clauses of the interface suffice — `0 < Ced` and "all used" are never touched.

At `ζ = 0` this specialises to the earlier observation that the budget does not fit at an equal
reading exponent; the content here is that **the exponent gap `ζ' - ζ` does not rescue it**, for
any `ζ ≥ 0`.

## What is still owed

`canonicalCover_of_essDistinct_pushdown` isolates it: every clause of the canonical-cover datum
except pairwise essential distinctness of the *pushed-down* family is already available, and the
datum follows from that clause alone.  So essential distinctness has to come from the construction
of the cover — the way GWZ's `𝕋_ρ` is essentially distinct by definition — and not be bought from
a maximal-density bound.  The tree's own substitute for essential distinctness at constant loss is
`Kakeya.Tube.UniformTubeSet.boundedOverlap`, whose docstring already records that essential
distinctness of the *nodes* "is unsatisfiable while preserving cardinality".

## Main declarations

* `Kakeya.ML2Reduction.card_le_of_densityIn_le_C_eq_three` — the constant of
  `Kakeya.Tube.card_le_of_densityIn_le` is the numeral `3` (a follow-up its docstring records).
* `Kakeya.ML2Reduction.le_volume_c_three_coe` — `Tube.le_volume.c 3 = 4π/9`.
* `Kakeya.ML2Reduction.four_le_refineToEssDistinctLeaves_C_three` — a lower bound for the
  essential-distinctness refinement constant in dimension `3`.
* `Kakeya.ML2Reduction.card_mul_sq_le_three_mul_maxDensity`,
  `Kakeya.ML2Reduction.rpow_neg_le_three_mul_maxDensity` — the `Δ_max` floor.
* `Kakeya.ML2Reduction.one_third_le_rpow_sub_of_maxDensity_le` — the exponent `a`, pinned below.
* `Kakeya.ML2Reduction.not_count_budget_of_unitBall`,
  `Kakeya.ML2Reduction.not_upstairs_bundle_at`, `Kakeya.ML2Reduction.not_upstairs_bundle` — the
  refutation of the count budget, abstractly and at the interface.
* `Kakeya.ML2Reduction.isRescalingSituation_scaledUp`, `Kakeya.ML2Reduction.ratio_scaledUp` — the
  rescaling situation at the forced upstairs scale `ρ_up = ρ θ`.
* `Kakeya.ML2Reduction.canonicalCover_of_essDistinct_pushdown` — the datum from essential
  distinctness alone.
* `Kakeya.ML2Reduction.rpow_neg_le_rpow_neg_div`,
  `Kakeya.ML2Reduction.le_rpow_neg_div_of_le_rpow_neg` — the window exponent conversion
  `a = a₀ / w`.
* `Kakeya.ML2Reduction.spine_windowExponent_le`,
  `Kakeya.ML2Reduction.spine_count_budget_closes` — the fine family's `a` on the parameter spine,
  and the budget it does close.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The constant of `Kakeya.Tube.card_le_of_densityIn_le` is the numeral `3`, in every
dimension. -/
theorem card_le_of_densityIn_le_C_eq_three (n : ℕ) :
    Kakeya.Tube.card_le_of_densityIn_le.C n = 3 := by
  have hx : (0 : ℝ) < Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) := by positivity
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_div]
  change (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))
      / (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1) / 3) = 3
  field_simp

/-- The essential-distinctness refinement constant in dimension `3` exceeds `4`. -/
theorem four_le_refineToEssDistinctLeaves_C_three :
    (4 : ENNReal) ≤ Kakeya.Tube.refineToEssDistinctLeaves.C 3 := by
  have hc : ((Tube.le_volume.c 3 : NNReal) : ℝ) = 4 * Real.pi / 9 := le_volume_c_three_coe
  have hcle : (Tube.le_volume.c 3 : NNReal) ≤ 2 := by
    rw [← NNReal.coe_le_coe, hc]
    push_cast
    nlinarith [Real.pi_le_four]
  have hK : (9 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 := by
    have h0 : (0 : ℝ) ≤ 2 * 4 ^ 3 / (Tube.le_volume.c 3 : ℝ) := by positivity
    unfold Tube.tubeOverlapCoreClose.C
    linarith
  have hK3 : (729 : ℝ) ≤ Tube.tubeOverlapCoreClose.C 3 ^ 3 := by
    calc (729 : ℝ) = 9 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hK 3
  have hc0 : ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≠ 0 := by
    simp [(Tube.le_volume.c_pos 3).ne']
  unfold Kakeya.Tube.refineToEssDistinctLeaves.C
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.coe_ne_top)]
  have hleft : (4 : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal) ≤ 8 := by
    calc (4 : ENNReal) * ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        ≤ 4 * ((2 : NNReal) : ENNReal) := by gcongr
      _ = 8 := by norm_num
  refine hleft.trans ?_
  have hright : ENNReal.ofReal (729 : ℝ) * ((Tube.volume_le.C 3 : NNReal) : ENNReal)
      ≤ Tube.overlapContainment.C 3 * ((Tube.volume_le.C 3 : NNReal) : ENNReal) := by
    gcongr
    unfold Tube.overlapContainment.C Tube.tubeDilateVolume.C'
    exact ENNReal.ofReal_le_ofReal hK3
  refine le_trans ?_ hright
  have hvc : (Tube.volume_le.C 3 : NNReal) = 16 := by
    unfold Tube.volume_le.C; norm_num
  rw [hvc]
  rw [show ENNReal.ofReal (729 : ℝ) = ((729 : NNReal) : ENNReal) by
    rw [ENNReal.ofReal]; norm_num]
  norm_num

/-! ### The floor -/

/-- **The `Δ_max` floor.**  A family of `ρ`-tubes inside the unit ball of a `3`-dimensional space
has maximal density at least `|t| ρ² / 3`. -/
theorem card_mul_sq_le_three_mul_maxDensity [Nontrivial E] (hn : Module.finrank ℝ E = 3)
    {ι : Type*} {t : Finset ι} {ρ : NNReal} (hρ : ρ ≠ 0) (V : ι → Tube ρ E)
    (hball : ∀ i ∈ t, (V i).carrier ⊆ Metric.closedBall 0 1) :
    (t.card : ENNReal) * (ρ : ENNReal) ^ (2 : ℕ)
      ≤ 3 * Kakeya.maxDensity t (fun i ↦ (V i).toConvexSpaceBody) := by
  have h := Kakeya.Tube.card_le_of_densityIn_le (E := E) (s := t) hρ (T := V) hball
    (Kakeya.le_maxDensity t (fun i ↦ (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall)
  rw [card_le_of_densityIn_le_C_eq_three, hn] at h
  have hz : ((ρ : ENNReal)) ≠ 0 := by simpa using hρ
  have h2z : ((ρ : ENNReal) ^ (2 : ℕ)) ≠ 0 := pow_ne_zero _ hz
  have h2t : ((ρ : ENNReal) ^ (2 : ℕ)) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hexp : (ρ : ENNReal) ^ (-(((3 : ℕ) : ℤ) - 1)) = ((ρ : ENNReal) ^ (2 : ℕ))⁻¹ := by
    rw [show -(((3 : ℕ) : ℤ) - 1) = -((2 : ℕ) : ℤ) by norm_num,
      ENNReal.zpow_neg (ρ : ENNReal) ((2 : ℕ) : ℤ), zpow_natCast]
  rw [hexp] at h
  have h' : (t.card : ENNReal) ≤ (3 * Kakeya.maxDensity t (fun i ↦ (V i).toConvexSpaceBody))
      / ((ρ : ENNReal) ^ (2 : ℕ)) := by
    rw [div_eq_mul_inv]
    exact_mod_cast h
  exact (ENNReal.le_div_iff_mul_le (Or.inl h2z) (Or.inl h2t)).mp h'

/-! ### The count budget of the canonical-cover route -/

/-- **The `ρ^{-ζ'}` floor**: if the family carries the count clause `ρ^{-2-ζ'} ≤ |t|` and lives in
the unit ball, its maximal density is at least `ρ^{-ζ'}/3`. -/
theorem rpow_neg_le_three_mul_maxDensity [Nontrivial E] (hn : Module.finrank ℝ E = 3)
    {ι : Type*} {t : Finset ι} {ρ : NNReal} (hρ0 : 0 < ρ) (V : ι → Tube ρ E)
    (hball : ∀ i ∈ t, (V i).carrier ⊆ Metric.closedBall 0 1)
    {ζ' : ℝ} (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ENNReal.ofReal ((ρ : ℝ) ^ (-ζ'))
      ≤ 3 * Kakeya.maxDensity t (fun i ↦ (V i).toConvexSpaceBody) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hfloor := card_mul_sq_le_three_mul_maxDensity hn hρ0.ne' V hball
  have hcard' : ENNReal.ofReal ((ρ : ℝ) ^ (-2 - ζ')) ≤ (t.card : ENNReal) := by
    calc ENNReal.ofReal ((ρ : ℝ) ^ (-2 - ζ'))
        ≤ ENNReal.ofReal ((t.card : ℝ)) := ENNReal.ofReal_le_ofReal hcard
      _ = (t.card : ENNReal) := by
          rw [ENNReal.ofReal_natCast]
  have hsq : ((ρ : ENNReal)) ^ (2 : ℕ) = ENNReal.ofReal ((ρ : ℝ) ^ (2 : ℝ)) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ENNReal.ofReal_pow hρR.le, ENNReal.ofReal_coe_nnreal]
  have hmul : ENNReal.ofReal ((ρ : ℝ) ^ (-2 - ζ')) * ENNReal.ofReal ((ρ : ℝ) ^ (2 : ℝ))
      = ENNReal.ofReal ((ρ : ℝ) ^ (-ζ')) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hρR.le _), ← Real.rpow_add hρR]
    ring_nf
  calc ENNReal.ofReal ((ρ : ℝ) ^ (-ζ'))
      = ENNReal.ofReal ((ρ : ℝ) ^ (-2 - ζ')) * ENNReal.ofReal ((ρ : ℝ) ^ (2 : ℝ)) := hmul.symm
    _ ≤ (t.card : ENNReal) * (ρ : ENNReal) ^ (2 : ℕ) := by rw [hsq]; gcongr
    _ ≤ _ := hfloor

/-- **The exponent `a` of `Δ_max ≤ ρ^{-a}`, pinned from below.**

For a family of `ρ`-tubes inside the unit ball carrying the count clause `ρ^{-2-ζ'} ≤ |t|`, any
bound `Δ_max ≤ ρ^{-a}` forces `1/3 ≤ ρ^{ζ' - a}`.  So `a < ζ'` is possible only at scales bounded
away from `0` (`ρ ≥ 3^{-1/(ζ'-a)}`): asymptotically `a ≥ ζ'`, and there is no room at all for the
`a ≤ ζ' - ζ` that the canonical-cover count budget asks for. -/
theorem one_third_le_rpow_sub_of_maxDensity_le [Nontrivial E] (hn : Module.finrank ℝ E = 3)
    {ι : Type*} {t : Finset ι} {ρ : NNReal} (hρ0 : 0 < ρ) (V : ι → Tube ρ E)
    (hball : ∀ i ∈ t, (V i).carrier ⊆ Metric.closedBall 0 1)
    {ζ' a : ℝ} (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hD : Kakeya.maxDensity t (fun i ↦ (V i).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((ρ : ℝ) ^ (-a))) :
    (1 : ℝ) / 3 ≤ (ρ : ℝ) ^ (ζ' - a) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hstep : ENNReal.ofReal ((ρ : ℝ) ^ (-ζ')) ≤ ENNReal.ofReal (3 * (ρ : ℝ) ^ (-a)) := by
    refine (rpow_neg_le_three_mul_maxDensity hn hρ0 V hball hcard).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    gcongr
    exact_mod_cast (by norm_num : ENNReal.ofReal (3 : ℝ) = (3 : ENNReal)).ge
  have hR : (ρ : ℝ) ^ (-ζ') ≤ 3 * (ρ : ℝ) ^ (-a) := by
    have h0 : (0 : ℝ) ≤ 3 * (ρ : ℝ) ^ (-a) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h0).mp hstep
  have h1 : (ρ : ℝ) ^ (-ζ') * (ρ : ℝ) ^ ζ' = 1 := by
    rw [← Real.rpow_add hρR]; simp
  have h2 : (ρ : ℝ) ^ (-a) * (ρ : ℝ) ^ ζ' = (ρ : ℝ) ^ (ζ' - a) := by
    rw [← Real.rpow_add hρR]; ring_nf
  nlinarith [mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg hρR.le ζ'), h1, h2]

/-- **The canonical-cover count budget is unsatisfiable.**

This is the residue `a + c ≤ ζ' - ζ` of, refuted.  The `Δ_max` that the
essential-distinctness refinement divides by is the maximal density of the *pushed-down*
`ρ`-tube family, and that quantity is bounded **below** by `ρ^{-ζ'}/3` as soon as the family
carries the count clause `ρ^{-2-ζ'} ≤ |t|` and sits in the unit ball.  So the price
`refineToEssDistinctLeaves.C 3 · Δ_max` is at least `(4/3) ρ^{-ζ'}`, while the budget allows only
`ρ^{-(ζ'-ζ)}`.  For `ζ ≥ 0` and `ρ ≤ 1` this is a contradiction, with no threshold on `ρ`. -/
theorem not_count_budget_of_unitBall [Nontrivial E] (hn : Module.finrank ℝ E = 3)
    {ι : Type*} {t : Finset ι} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (V : ι → Tube ρ E)
    (hball : ∀ i ∈ t, (V i).carrier ⊆ Metric.closedBall 0 1)
    {ζ ζ' : ℝ} (hζ : 0 ≤ ζ)
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    {D : ENNReal} {Ced : NNReal} {Lam : ℝ}
    (hD : Kakeya.maxDensity t (fun i ↦ (V i).toConvexSpaceBody) ≤ D)
    (hedloss : Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal))
    (hLam : 1 ≤ Lam)
    (hslack : (Ced : ℝ) * Lam ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) :
    False := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hρR1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  set X : ENNReal := ENNReal.ofReal ((ρ : ℝ) ^ (-ζ')) with hXdef
  have hX0 : X ≠ 0 := by
    rw [hXdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos hρR _
  have hXt : X ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the floor
  have hfloor : X ≤ 3 * D :=
    (rpow_neg_le_three_mul_maxDensity hn hρ0 V hball hcard).trans (by gcongr)
  -- the slack, in `ENNReal`
  have hCedR : (Ced : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) := by
    nlinarith [Ced.coe_nonneg, hslack, hLam]
  have hCedE : (Ced : ENNReal) ≤ ENNReal.ofReal ((ρ : ℝ) ^ (-(ζ' - ζ))) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hCedR
  -- the right-hand side, factored
  have hsplit : ENNReal.ofReal ((ρ : ℝ) ^ (-(ζ' - ζ))) = X * ENNReal.ofReal ((ρ : ℝ) ^ ζ) := by
    rw [hXdef, ← ENNReal.ofReal_mul (Real.rpow_nonneg hρR.le _), ← Real.rpow_add hρR]
    ring_nf
  have hle1 : ENNReal.ofReal ((ρ : ℝ) ^ ζ) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hρR.le hρR1 hζ)
  -- assemble
  have hchain : Kakeya.Tube.refineToEssDistinctLeaves.C 3 * X ≤ 3 * X :=
    calc Kakeya.Tube.refineToEssDistinctLeaves.C 3 * X
        ≤ Kakeya.Tube.refineToEssDistinctLeaves.C 3 * (3 * D) := by gcongr
      _ = 3 * (Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D) := by ring
      _ ≤ 3 * (Ced : ENNReal) := by gcongr
      _ ≤ 3 * (X * ENNReal.ofReal ((ρ : ℝ) ^ ζ)) := by rw [← hsplit]; gcongr
      _ ≤ 3 * (X * 1) := by gcongr
      _ = 3 * X := by rw [mul_one]
  have hfinal : Kakeya.Tube.refineToEssDistinctLeaves.C 3 ≤ 3 :=
    (ENNReal.mul_le_mul_iff_left hX0 hXt).mp hchain
  have h4 := four_le_refineToEssDistinctLeaves_C_three
  exact absurd (h4.trans hfinal) (by norm_num)

/-! ### The  bundle, refuted -/

variable {θ τ σ : NNReal}

/-- **The  bundle is contradictory at every scale `ρ ∈ (0, 1/4]`.**

Five of the bundle's clauses suffice — the density bound `hD`, the essential-distinctness price
`hedloss`, the slack `hslack`, the count `hcard` and the parent containment `hsubW`.  The clauses
`0 < Ced` and "all used" are not needed, which makes the refutation strictly stronger than the
bundle it refutes. -/
theorem not_upstairs_bundle_at {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4) (hζ : 0 ≤ ζ)
    {κ₀ : Type u} {t : Finset κ₀} (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    {D : ENNReal} {Ced : NNReal}
    (hD : Kakeya.maxDensity t
      (fun k ↦ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody) ≤ D)
    (hedloss : Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal))
    (hslack : (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    False := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hball : ∀ k ∈ t,
      (outerTube hsit.pos_ambient T₀ hR ρ (W k)).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk
    exact (outerTube_spec hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ) T₀ (W k)
      (hsubW k hk)).2.1
  exact not_count_budget_of_unitBall hfr hρ0 hρ1
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hball hζ hcard hD hedloss
    (one_le_spineOuterCountLoss R) hslack

/-- **The  bundle is contradictory over Lemma 9.1's window.**

Instantiating at the right endpoint `ρ = σ^ϖ` of the window is enough. -/
theorem not_upstairs_bundle {R ϖ ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hϖ2 : ϖ ≤ 1 - ϖ) (hζ : 0 ≤ ζ)
    (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
        (D : ENNReal) (Ced : NNReal),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        Kakeya.maxDensity t
          (fun k ↦ (outerTube hsit.pos_ambient T₀ hR ρ (W k)).toConvexSpaceBody) ≤ D ∧
        Kakeya.Tube.refineToEssDistinctLeaves.C 3 * D ≤ (Ced : ENNReal) ∧
        (Ced : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    False := by
  have hmem : (σ ^ ϖ : NNReal) ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) :=
    ⟨NNReal.rpow_le_rpow_of_exponent_ge hσ0 hσ1 hϖ2, le_rfl⟩
  obtain ⟨κ₀, t, W, D, Ced, hsubW, hD, hedloss, hslack, hcard⟩ := hup (σ ^ ϖ) hmem
  exact not_upstairs_bundle_at hsit hR T₀ (NNReal.rpow_pos hσ0) hwin4 hζ W hsubW hD hedloss
    hslack hcard

/-! ### What the datum still needs, isolated -/

/-- **The canonical-cover datum, from essential distinctness alone.**

Every clause of `hcanon` other than pairwise essential distinctness of the *pushed-down*
`ρ`-tube family is already in hand: "used" transports for free
(`Kakeya.ML2Reduction.outerTube_used_of_used`) and the count is
`Kakeya.ML2Spine.spine_tube_card_lower`.  This records that the datum follows immediately once
the pushed-down family is essentially distinct — and
`Kakeya.ML2Reduction.not_upstairs_bundle_at` shows that essential distinctness cannot be *bought*
from a maximal-density bound at this cardinality. -/
theorem canonicalCover_of_essDistinct_pushdown {R ζ : ℝ} (hθ : 0 < θ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) (hR : 0 < R)
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} {κ₀ : Type u} (t : Finset κ₀)
    (V : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hED : (t : Set κ₀).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody ≤ (V j).toConvexSpaceBody)
    (hlow : (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) :=
  ⟨κ₀, t, V, hED, hused, hlow⟩

/-! ### The other `Δ_max`: the exponent `a` of `upperBdDeltaMaxTildeTT` on the window -/

/-- **The window exponent conversion.**  A bound `δ̃^{-a}` read at a scale `ρ ≤ δ̃^w` of the window
is a bound `ρ^{-a/w}`.  This is where the exponent `a` of `Δ_max ≤ ρ^{-a}` comes from for the
*fine* family: `a = η_{j-1} / w`. -/
theorem rpow_neg_le_rpow_neg_div {d r w a : ℝ} (hd : 0 < d) (hr : 0 < r) (hw : 0 < w)
    (ha : 0 ≤ a) (hrd : r ≤ d ^ w) : d ^ (-a) ≤ r ^ (-(a / w)) := by
  have haw : 0 ≤ a / w := by positivity
  have hcancel : w * (a / w) = a := by field_simp
  have h1 : r ^ (a / w) ≤ (d ^ w) ^ (a / w) := Real.rpow_le_rpow hr.le hrd haw
  have h2 : (d ^ w) ^ (a / w) = d ^ a := by rw [← Real.rpow_mul hd.le, hcancel]
  rw [Real.rpow_neg hd.le, Real.rpow_neg hr.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hr _) (by rw [← h2]; exact h1)

/-- **The transported density bound.**  Any quantity bounded by `C δ̃^{-a}` is bounded by
`C ρ^{-a/w}` at every scale `ρ` of the window `ρ ≤ δ̃^w`. -/
theorem le_rpow_neg_div_of_le_rpow_neg {δt ρ : NNReal} {Cst X : ENNReal} {a w : ℝ}
    (hδ0 : 0 < δt) (hρ0 : 0 < ρ) (hw : 0 < w) (ha : 0 ≤ a)
    (hρδ : (ρ : ℝ) ≤ (δt : ℝ) ^ w)
    (hX : X ≤ Cst * ENNReal.ofReal ((δt : ℝ) ^ (-a))) :
    X ≤ Cst * ENNReal.ofReal ((ρ : ℝ) ^ (-(a / w))) := by
  have hδR : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast hδ0
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  refine hX.trans ?_
  gcongr
  exact rpow_neg_le_rpow_neg_div hδR hρR hw ha hρδ

/-- **The value of `a` on the spine.**  With the window exponent `w = ϖ (1 - ε₂)` — the largest
`w` for which `ρ ≤ (δ')^ϖ` and `δ' ≤ δ̃^{1-ε₂}` give `ρ ≤ δ̃^w` — the exponent
`a = η_{j-1} / w` of `Δ_max(𝕋̃) ≤ ρ^{-a}` is at most `η_j / 240`. -/
theorem spine_windowExponent_le {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) :
    η k / (ϖ * (1 - ε₂)) ≤ η (k + 1) / 240 := by
  have he : 0 < e := h.div_pos
  have he5 : e ≤ ε₂ / 5 := h.div_le
  have hε2 : 0 < ε₂ := h.eps₂_pos
  have hεh : ε₂ ≤ 1 / 2 := h.eps₂_le_half
  have hϖ : ε₂ ≤ ϖ / 2 := h.eps₂_le_vnsWindow
  have hsep : 12 * η k / (e * β) ≤ e * η (k + 1) / 4 := h.sep_le k hk
  have hk0 : 0 < η k := h.rung_pos k
  have hk10 : 0 < η (k + 1) := h.rung_pos (k + 1)
  have heb : 0 < e * β := mul_pos he hβ0
  have hA : η k ≤ e ^ 2 * β * η (k + 1) / 48 := by
    have h' := (div_le_iff₀ heb).mp hsep
    nlinarith [h']
  have hB : 5 * e ≤ ϖ * (1 - ε₂) := by nlinarith [hϖ, hεh, hε2, he5, he]
  have hstep1 : η k / (ϖ * (1 - ε₂)) ≤ η k / (5 * e) :=
    div_le_div_of_nonneg_left hk0.le (by positivity) hB
  refine hstep1.trans ?_
  have heb1 : e * β ≤ 1 := by nlinarith [he5, hεh, hβ1, hβ0, he]
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 240)]
  nlinarith [hA, hk10, he, hβ0, heb1, mul_pos he hk10]

/-- **The count budget closes for the fine family's `Δ_max`.**  At `ζ' = η_j/2` and `ζ = η_j/4`
the budget `a + c ≤ ζ' - ζ` holds with `a = η_{j-1}/(ϖ(1-ε₂))` and any constant exponent
`c ≤ 59 η_j / 240` — a factor-`60` margin. -/
theorem spine_count_budget_closes {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) {c : ℝ} (hc : c ≤ 59 * η (k + 1) / 240) :
    η k / (ϖ * (1 - ε₂)) + c ≤ η (k + 1) / 2 - η (k + 1) / 4 := by
  have := spine_windowExponent_le h hβ0 hβ1 hk
  linarith

end Kakeya.ML2Reduction

end
