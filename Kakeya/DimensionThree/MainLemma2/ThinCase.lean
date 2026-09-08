/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SlabCase
public import Kakeya.DimensionThree.MainLemma2.NonSlabCase

/-!
# The thin case of Main Lemma 2

This file assembles the slab and non-slab branches of the thin case. The density and transfer
estimates used by their eventual proofs live separately in
`Kakeya.DimensionThree.MainLemma2.ThinEstimates`, avoiding an import cycle through this
assembly.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

/-- **Exponent in Lemma `lem:ml2thin`** (blueprint `def:ml2thinExponent`).

The blueprint value is `ν_thin(β, ζ) = min(β/2, ν_nonslab(β, ζ))`, where `β/2` is the gain
supplied by the slab case (blueprint `lem:ml2slab`, Lean `Kakeya.goalMult_of_b_ge`) and
`ν_nonslab` is the exponent of the non-slab case (blueprint `def:ml2nonslabExponent`, Lean
`Kakeya.VeryNotSticky.nonslabExponent`).

The Lean `nonslabExponent` carries, besides `β` and `ζ`, the two further parameters of
Definition `hyp:ml2params` that the blueprint leaves implicit in its notation — the scale
exponent `exscal` and the angular threshold exponent `τ'` — so `thinExponent` carries them
too. As in the blueprint, the exponent depends on the parameters of Definition
`hyp:ml2params` only, and is fixed before `δ` and `𝕋`. -/
noncomputable def thinExponent (β ζ exscal τ' : ℝ) : ℝ :=
  min (β / 2) (nonslabExponent β ζ exscal τ')

lemma thinExponent_pos {β ζ exscal τ' : ℝ} (hβ : 0 < β) (hζ : 0 < ζ)
    (hexscal : 0 < exscal) (hτ' : 0 < τ') : 0 < thinExponent β ζ exscal τ' :=
  lt_min (by positivity) (nonslabExponent_pos hβ hζ hexscal hτ')

end Kakeya.VeryNotSticky

namespace Kakeya

open MeasureTheory Topology Filter ShadedBody in
/-- **Main Lemma 2, thin case** (blueprint `lem:ml2thin`).

In the configuration `cfg` of Subsection `subsecproofoverview`, suppose we are in the
*thin case*, i.e. the smallest affine thickness of the factoring bodies satisfies
`a ≤ δ^{1-τ}`. Then the goal `μ(𝕋, Y) ≤ δ^ν |𝕋|^β` holds with the explicit gain
`ν = Kakeya.VeryNotSticky.thinExponent cfg.β cfg.ζ cfg.exscal τ'`, i.e.
`min(β/2, ν_nonslab)`, which is positive by `Kakeya.VeryNotSticky.thinExponent_pos`.

The middle affine thickness `b` satisfies either `b ≥ δ^{exscal} r₁ = δ^{2·exscal}`, and we
are in the slab case (`Kakeya.goalMult_of_b_ge`, which supplies the gain `β/2` in the
volume currency `eqgoalUT`, converted to the multiplicity currency by blueprint
`lem:ml2goalUTequiv`(i)), or `b ≤ δ^{2·exscal}`, and we are in the non-slab case
(`Kakeya.VeryNotSticky.goalMult_of_b_le`, blueprint `lem:ml2nonslab`, with gain
`nonslabExponent cfg.β cfg.ζ cfg.exscal τ'`). In either case the goal holds with an exponent
at least `ν`, and since `0 < δ ≤ 1` the map `s ↦ δ^s` is antitone
(`ENNReal.rpow_le_rpow_of_exponent_ge`), so the estimate with the larger exponent implies
the estimate with `ν`.

Both branches are stated relative to Configuration `hyp:ml2thinsetup`, so this lemma takes
the bundle `tc : Kakeya.VeryNotSticky.ThinConfig cfg bd` and threads it to both. It is supplied
to the top-level case split by `Kakeya.VeryNotSticky.exists_thinConfig`.

The bundle `scale : VeryNotSticky.CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr` is threaded
to the non-slab branch. Its first field controls `ρ₂*`; the next three are consumed inside
`Kakeya.VeryNotSticky.exists_isTypicalAnglePlank`; the fifth, seventh and eighth are spent in
the transverse chain; the remaining ones are threaded to the leaves that will consume them.
The slab branch does not use it.

Its three indices beyond `τ` and `τ'` are threaded unchanged: the gain at which blueprint
`lem:ml2aScaleData` is invoked, which is the transverse gain `τ'β/2` because
`Kakeya.VeryNotSticky.goalMult_of_theta_ge` is what consumes the eighth clause; the constant
`tc.C` of Configuration `hyp:ml2thinsetup` that its seventh clause mentions — which is why
the bundle is read at `tc.C` and not at a free constant, `tc` being bound before it — and the
by-choice thresholds `thr`.

The bundle `ss : VeryNotSticky.SlabScale cfg bd tc τ` is threaded to the slab branch, where
`Kakeya.goalMult_of_b_ge` turns it into the inputs of the slab case through
`Kakeya.VeryNotSticky.slabInputs`. It is the `tc`-aware companion of `CaseScale`: two of its
thresholds mention `tc.C`, so they cannot be stated before the thin-case data exists, which is
why they travel in a second bundle rather than in `scale`. The non-slab branch does not use it.

`hβ1 : cfg.β ≤ 1` is threaded to the non-slab branch, where the Katz–Tao bound
`Kakeya.VeryNotSticky.nonslabKKT` needs it. It is not implied by `cfg.hβ` and
`Kakeya.VeryNotSticky.CaseParams` carries no such budget, so it travels as an explicit
hypothesis from `Kakeya.VeryNotSticky.exists_goalMult`, which already carried it for the
thick branch. The slab branch does not use it.

`tin : VeryNotSticky.TangentialInputs cfg tc τ'` is items (a)–(c) of blueprint
`lem:ml2tangential`, threaded by the same remedy and for the same reason: none of them is
implied by `params`, by `scale` or by `cfg`, and the tangential leaf
`Kakeya.VeryNotSticky.goalMult_of_theta_lt` is the only consumer. Like `ss`, it mentions the
thin-case data, so it is read at this `tc` and arrives packaged with it from
`Kakeya.VeryNotSticky.exists_goalMult`. The slab branch does not use it. -/
theorem goalMult_of_a_le (cfg : VeryNotSticky) {τ τ' : ℝ}
    (params : VeryNotSticky.CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (hβ1 : cfg.β ≤ 1)
    (hthin : cfg.a ≤ cfg.δ ^ (1 - τ))
    {bd : VeryNotSticky.BallData cfg} (tc : VeryNotSticky.ThinConfig cfg bd)
    {thr : VeryNotSticky.ScaleThresholds}
    (scale : VeryNotSticky.CaseScale cfg bd τ τ' (τ' * cfg.β / 2) tc.C thr)
    (ss : VeryNotSticky.SlabScale cfg bd tc τ)
    (tin : cfg.a ≤ cfg.δ ^ (1 - τ) → cfg.b ≤ cfg.δ ^ (2 * cfg.exscal) → VeryNotSticky.TangentialInputs cfg tc τ') :
    cfg.goalMult (VeryNotSticky.thinExponent cfg.β cfg.ζ cfg.exscal τ') := by
  rcases le_total (cfg.δ ^ (2 * cfg.exscal)) cfg.b with (hslab | hnotslab)
  · have hslab_res : cfg.goalMult (cfg.β / 2) :=
      Kakeya.goalMult_of_b_ge cfg params hthin hslab tc ss
    have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := VeryNotSticky.thinExponent cfg.β cfg.ζ cfg.exscal τ' with hν_def
    have hν_le : ν ≤ cfg.β / 2 := min_le_left _ _
    have hpow : (cfg.δ : ENNReal) ^ (cfg.β / 2) ≤ (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν_le
    have h_mul : (cfg.δ : ENNReal) ^ (cfg.β / 2) * (cfg.s.card : ENNReal) ^ cfg.β ≤
        (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans hslab_res h_mul
  · have hnotslab_res :
        cfg.goalMult (VeryNotSticky.nonslabExponent cfg.β cfg.ζ cfg.exscal τ') :=
      Kakeya.VeryNotSticky.goalMult_of_b_le cfg params hβ1 hthin hnotslab tc scale
        (tin hthin hnotslab)
    have hδ1 : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
    set ν := VeryNotSticky.thinExponent cfg.β cfg.ζ cfg.exscal τ' with hν_def
    have hν_le : ν ≤ VeryNotSticky.nonslabExponent cfg.β cfg.ζ cfg.exscal τ' := min_le_right _ _
    have hpow : (cfg.δ : ENNReal) ^
        (VeryNotSticky.nonslabExponent cfg.β cfg.ζ cfg.exscal τ') ≤
        (cfg.δ : ENNReal) ^ ν :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hν_le
    have h_mul : (cfg.δ : ENNReal) ^
        (VeryNotSticky.nonslabExponent cfg.β cfg.ζ cfg.exscal τ') *
        (cfg.s.card : ENNReal) ^ cfg.β ≤
        (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β := by
      gcongr
    exact le_trans hnotslab_res h_mul

end Kakeya
