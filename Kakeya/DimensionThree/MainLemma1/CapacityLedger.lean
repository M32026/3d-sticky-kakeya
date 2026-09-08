/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FrostmanConstant
public import Kakeya.Multiplicity

/-!
# Main Lemma 1, Step 6: the local Frostman capacity and the exponent ledger

This module is the numeric spine of the Main Lemma 1 repair blueprint, §5, §6.1, §6.2, §6.4
and §6.5.  Nothing here is geometric beyond the one place it has to be: `Kakeya.frostmanConstant`
is bounded from below by the reciprocal of the *relative capacity* of a tube family inside its
container.  Everything downstream of that is an inequality between exponents.

## What is proved here

* `Kakeya.ml1Ledger.volume_le_frostmanConstant_mul_sum` — bound (C) of §5.1 in division-free
  form: for a family with a member of positive finite volume,
  `|P| ≤ C_F(𝓕, P) · ∑_{T ∈ 𝓕} |T|`.  Taking `T₀ ∈ 𝓕` as the Frostman test object gives
  `Δ_max ≥ 1`, which is the whole content.
* `Kakeya.ml1Ledger.one_le_capacity_mul_frostmanConstant` — the same statement in the `q` form
  `1 ≤ q · C_F`, where `q = |𝓕| (r/R)²` enters through the volume comparison
  `∑ |T| ≤ q · |P|`.
* `Kakeya.ml1Ledger.capacity_lower_bound` — (CLB): a *negative-exponent* upper bound on `C_F`
  forces `q ≥ δ^{κ_F} ρ^{a_F}`, and
  `Kakeya.ml1Ledger.card_lower_bound_of_capacity` turns that into the small-family exclusion
  `|𝓕| ≥ δ^{κ_F} ρ^{a_F - 2}`.  Note that this is a *lower* bound on the cardinality: `ρ^{-2}` is
  the normalised Kakeya cardinality scale, never an absolute maximum for an arbitrary family.
* `Kakeya.ml1Ledger.CapSpec` and `Kakeya.ml1Ledger.CapSpec.target_ge` — (CAP) of §5.2, together
  with the conclusion it exists to buy: the middle target right-hand side is at least
  `δ^{-s}` for a slack `s > 0`, hence in particular at least `1`.
* `Kakeya.ml1Ledger.uniformSlack` and `Kakeya.ml1Ledger.abs_of_lt_uniformSlack` — (ABS) of §6.1
  with the **non-circular** parameter order: the uniform slack `S_*` is a `Finset.inf'` over the
  finite rung/branch index set and is proved positive *before* any rung is selected, so the
  extra-loss budget is fixed before `j` and before `δ`.
* `Kakeya.ml1Ledger.ImpSpec.improvement` — (IMP) of §6.2.
* `Kakeya.ml1Ledger.multiplicity_le_one_of_card_le_one`,
  `Kakeya.ml1Ledger.product_collapse_fine`, `Kakeya.ml1Ledger.product_collapse_coarse` — the
  `τ = δ` and `θ = 1` endpoints of §6.5, each independent of the interior scale lemmas.
* `Kakeya.ml1Ledger.conv_upper`, `Kakeya.ml1Ledger.conv_lower` — the term-by-term scale
  conversion rules of §6.5.
* `Kakeya.ml1Ledger.appError_coarsen` and `Kakeya.ml1Ledger.eq60_appError_uniform`,
  `Kakeya.ml1Ledger.eq61_appError_uniform` — §6.4, covering the `j = 1` rung for **both** GWZ
  equation (60) and equation (61).

## GWZ v1 errata recorded as checkable statements

* `Kakeya.ml1Ledger.eq64_positive_exponent_false` — equation (64)'s positive-exponent upper bound
  on `C_F(𝕋̃)` is refutable against `C_F ≥ 1`.
* `Kakeya.ml1Ledger.prop66_sign_error_false` — the `λ ⪆ δ^{-η}` of the Proposition 6.6 proof is
  refutable for a density `λ ≤ 1`.
* `Kakeya.ml1Ledger.gain_at_eq66` and `Kakeya.ml1Ledger.gain_at_eq66_shortfall` — the gain from
  `b ≤ δ̃^{1-ε}` is `2(1-ε)(γ-β)`, and the shortfall `2ε(γ-β)` is charged to the ledger.
* `Kakeya.ml1Ledger.ladder_bound` — the corrected form of §8's "`η_{j-1} ≤ N`".

## The losses are kept separate

`a_F` (local Frostman exponent), `a_G` (target gain), `κ_F` (Frostman constant loss),
`κ_card` (carrier/cardinality loss) and `ℓ_μ` (multiplicity/refinement loss) are distinct
parameters.  `ℓ_μ` appears only through the extra-loss budget of
`Kakeya.ml1Ledger.abs_of_lt_uniformSlack`, never in `Kakeya.ml1Ledger.CapSpec`; this is the
separation the blueprint's errata table demands.  No lemma here identifies `a_F` with the formal
`a_lambda` or with any `η_{j-1}`: a bridge theorem would be needed and none is claimed.

## Satisfiability

Every inequality ledger in this file is accompanied by an explicit numeric instance
(`Kakeya.ml1Ledger.capWitness`, `Kakeya.ml1Ledger.absWitness`, `Kakeya.ml1Ledger.impWitness`).
An unsatisfiable ledger compiles green and is worthless, and `#print axioms` cannot see the
difference.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya

namespace ml1Ledger

/-! ## §6.5 The scale-conversion rules

Every exponent argument below needs these, and, as the blueprint insists, the direction has to be
checked term by term.  Both rules take the relative-scale hypothesis `r ≤ δ ^ ε_scale`. -/

/-- **Conversion rule I** (§6.5).  Converting a `δ`-power *upper* bound on a constant into an
`r`-power upper bound costs the exponent inequality `α_δ ≤ ε_scale · α_r`.

From `C ≤ δ ^ (-α_δ)` and `r ≤ δ ^ ε_scale` we get `C ≤ r ^ (-α_r)` — in this direction only,
and only when that budget is respected. -/
theorem conv_upper {δ r C αδ αr εs : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hr0 : 0 < r)
    (hrδ : r ≤ δ ^ εs) (hαr : 0 ≤ αr) (hα : αδ ≤ εs * αr)
    (hC : C ≤ δ ^ (-αδ)) : C ≤ r ^ (-αr) := by
  have hstep1 : δ ^ (-αδ) ≤ δ ^ (-(εs * αr)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hstep2 : δ ^ (-(εs * αr)) = (δ ^ εs) ^ (-αr) := by
    rw [← Real.rpow_mul hδ0.le]
    ring_nf
  have hpos : (0:ℝ) < δ ^ εs := Real.rpow_pos_of_pos hδ0 _
  have hstep3 : (δ ^ εs) ^ (-αr) ≤ r ^ (-αr) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
      (Set.mem_Ioi.mpr hr0) (Set.mem_Ioi.mpr hpos) hrδ
  calc C ≤ δ ^ (-αδ) := hC
    _ ≤ δ ^ (-(εs * αr)) := hstep1
    _ = (δ ^ εs) ^ (-αr) := hstep2
    _ ≤ r ^ (-αr) := hstep3

/-- **Conversion rule II** (§6.5).  Converting a `δ`-power *lower* bound on a density into an
`r`-power lower bound costs `A ≤ ε_scale · η`.

From `δ ^ A ≤ λ` and `r ≤ δ ^ ε_scale` we get `r ^ η ≤ λ`. -/
theorem conv_lower {δ r lam A η εs : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hr0 : 0 < r)
    (hrδ : r ≤ δ ^ εs) (hη : 0 ≤ η) (hA : A ≤ εs * η)
    (hlam : δ ^ A ≤ lam) : r ^ η ≤ lam := by
  have hpos : (0:ℝ) < δ ^ εs := Real.rpow_pos_of_pos hδ0 _
  have hstep1 : r ^ η ≤ (δ ^ εs) ^ η := Real.rpow_le_rpow hr0.le hrδ hη
  have hstep2 : (δ ^ εs) ^ η = δ ^ (εs * η) := (Real.rpow_mul hδ0.le _ _).symm
  have hstep3 : δ ^ (εs * η) ≤ δ ^ A :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hA
  calc r ^ η ≤ (δ ^ εs) ^ η := hstep1
    _ = δ ^ (εs * η) := hstep2
    _ ≤ δ ^ A := hstep3
    _ ≤ lam := hlam

/-! ## §5.1 Local Frostman capacity: the bound (C)

The Frostman constant of `Kakeya.frostmanConstant` is `Δ_max(𝕎) · |K| / ∑ |W i|`.  Taking a
member `W i₀` of the family as the test body in `Δ_max` gives `Δ_max ≥ 1`, and (C) follows by
clearing the denominator. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The Frostman test object.**  A member of the family, used as its own test body, already
witnesses `Δ_max ≥ 1`.  This is `Δ(𝓕, T₀) ≥ 1` of §5.1. -/
theorem one_le_maxDensity_of_mem {s : Finset ι} {W : ι → ConvexSpaceBody E} {i₀ : ι}
    (hi₀ : i₀ ∈ s) (hpos : volume (W i₀).carrier ≠ 0) :
    1 ≤ maxDensity s W := by
  classical
  refine le_trans ?_ (le_maxDensity s W (W i₀))
  have htop : volume (W i₀).carrier ≠ ⊤ := (W i₀).isCompact.measure_ne_top
  have hmem : i₀ ∈ {i ∈ s | W i ≤ W i₀} := Finset.mem_filter.mpr ⟨hi₀, le_rfl⟩
  have hsum : volume (W i₀).carrier ≤ ∑ i ∈ s with W i ≤ W i₀, volume (W i).carrier :=
    Finset.single_le_sum (f := fun i => volume (W i).carrier) (fun _ _ => bot_le) hmem
  rw [show (densityIn s W (W i₀)) =
      (∑ i ∈ s with W i ≤ W i₀, volume (W i).carrier) / volume (W i₀).carrier from rfl,
    ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl htop), one_mul]
  exact hsum

/-- **§5.1, bound (C), division-free form.**  For a family containing a body of positive finite
volume inside the container `K`,

`|K| ≤ C_F(𝓕, K) · ∑_{T ∈ 𝓕} |T|`.

Dividing, this is `C_F(𝓕, K) ≳ 1 / (|𝓕| (r/R)²)` once the volume ratio is inserted; see
`Kakeya.ml1Ledger.one_le_capacity_mul_frostmanConstant`. -/
theorem volume_le_frostmanConstant_mul_sum {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : volume (W i₀).carrier ≠ 0)
    (hmass : ∑ i ∈ s, volume (W i).carrier ≠ 0) :
    volume K.carrier ≤ frostmanConstant s W K * ∑ i ∈ s, volume (W i).carrier := by
  have hsum_top : (∑ i ∈ s, volume (W i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => (W i).isCompact.measure_ne_top
  have hcancel : frostmanConstant s W K * ∑ i ∈ s, volume (W i).carrier
      = maxDensity s W * volume K.carrier := by
    unfold frostmanConstant
    exact ENNReal.div_mul_cancel hmass hsum_top
  rw [hcancel]
  calc volume K.carrier = 1 * volume K.carrier := (one_mul _).symm
    _ ≤ maxDensity s W * volume K.carrier :=
        mul_le_mul_right' (one_le_maxDensity_of_mem hi₀ hpos) _

/-- **§5.1, bound (C) in the `q` form.**  Here `q` is any bound for the relative capacity
`∑_{T ∈ 𝓕} |T| / |K|`; for an equal-length family of `r`-tubes inside an `R`-tube it is
`≍ |𝓕| (r/R)²`.  The conclusion `1 ≤ q · C_F` is exactly `C_F ≳ 1/q`. -/
theorem one_le_capacity_mul_frostmanConstant {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : volume (W i₀).carrier ≠ 0)
    (hmass : ∑ i ∈ s, volume (W i).carrier ≠ 0)
    (hK0 : volume K.carrier ≠ 0) (hKtop : volume K.carrier ≠ ⊤)
    {q : ENNReal} (hq : ∑ i ∈ s, volume (W i).carrier ≤ q * volume K.carrier) :
    1 ≤ q * frostmanConstant s W K := by
  have hC := volume_le_frostmanConstant_mul_sum (K := K) hi₀ hpos hmass
  have hchain : 1 * volume K.carrier
      ≤ (q * frostmanConstant s W K) * volume K.carrier := by
    calc 1 * volume K.carrier = volume K.carrier := one_mul _
      _ ≤ frostmanConstant s W K * ∑ i ∈ s, volume (W i).carrier := hC
      _ ≤ frostmanConstant s W K * (q * volume K.carrier) := by
          exact mul_le_mul_left' hq _
      _ = (q * frostmanConstant s W K) * volume K.carrier := by ring
  exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp hchain

end

/-- **Satisfiability witness for (C).**  The hypotheses of
`Kakeya.ml1Ledger.volume_le_frostmanConstant_mul_sum` are non-vacuous: the one-element family
consisting of the closed unit ball of `EuclideanSpace ℝ (Fin 3)`, tested against itself, meets
all of them. -/
theorem capacityWitness :
    ∃ (s : Finset ℕ) (W : ℕ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (i₀ : ℕ),
      i₀ ∈ s ∧ volume (W i₀).carrier ≠ 0 ∧ (∑ i ∈ s, volume (W i).carrier) ≠ 0 := by
  refine ⟨{0}, fun _ => ConvexSpaceBody.closedUnitBall, 0, Finset.mem_singleton_self 0, ?_, ?_⟩
  · rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact (Metric.measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin 3)) one_pos).ne'
  · rw [Finset.sum_singleton, ConvexSpaceBody.closedUnitBall_carrier]
    exact (Metric.measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin 3)) one_pos).ne'

/-! ## §5.1 The bound (CLB)

`q ≥ δ^{κ_F} ρ^{a_F}` is *derived* from (C) plus a negative-exponent upper bound on `C_F`.  It is
not an extra analytic hypothesis.  Note the exponent on `ρ` in the hypothesis is `-a_F`: GWZ
equation (64)'s positive-exponent upper bound on `C_F(𝕋̃)` contradicts `C_F ≥ 1` and is not used
here. -/

/-- **§5.1, bound (CLB).**  From the capacity bound `1 ≤ q · C_F`, a local Frostman upper bound
`C_F ≤ C₀ ρ^{-a_F}` and a constant bound `C₀ ≤ δ^{-κ_F}`, we get `q ≥ δ^{κ_F} ρ^{a_F}`. -/
theorem capacity_lower_bound {δ ρ q CF C₀ aF κF : ℝ}
    (hδ0 : 0 < δ) (hρ0 : 0 < ρ) (hq0 : 0 < q)
    (hcap : 1 ≤ q * CF)
    (_hC₀0 : 0 ≤ C₀) (hCF : CF ≤ C₀ * ρ ^ (-aF)) (hC₀ : C₀ ≤ δ ^ (-κF)) :
    δ ^ κF * ρ ^ aF ≤ q := by
  have hρpow : (0:ℝ) < ρ ^ (-aF) := Real.rpow_pos_of_pos hρ0 _
  have hδpow : (0:ℝ) < δ ^ κF := Real.rpow_pos_of_pos hδ0 _
  have hρpow' : (0:ℝ) < ρ ^ aF := Real.rpow_pos_of_pos hρ0 _
  have h1 : 1 ≤ q * (δ ^ (-κF) * ρ ^ (-aF)) := by
    refine hcap.trans ?_
    have : CF ≤ δ ^ (-κF) * ρ ^ (-aF) :=
      hCF.trans (by nlinarith [hρpow.le])
    nlinarith [hq0.le]
  have hkey : δ ^ κF * ρ ^ aF ≤ (q * (δ ^ (-κF) * ρ ^ (-aF))) * (δ ^ κF * ρ ^ aF) := by
    nlinarith [mul_pos hδpow hρpow']
  have hcollapse : (q * (δ ^ (-κF) * ρ ^ (-aF))) * (δ ^ κF * ρ ^ aF) = q := by
    have hδ' : δ ^ (-κF) * δ ^ κF = 1 := by
      rw [← Real.rpow_add hδ0]; simp
    have hρ' : ρ ^ (-aF) * ρ ^ aF = 1 := by
      rw [← Real.rpow_add hρ0]; simp
    calc (q * (δ ^ (-κF) * ρ ^ (-aF))) * (δ ^ κF * ρ ^ aF)
        = q * ((δ ^ (-κF) * δ ^ κF) * (ρ ^ (-aF) * ρ ^ aF)) := by ring
      _ = q := by rw [hδ', hρ']; ring
  rw [hcollapse] at hkey
  exact hkey

/-- **Small-family exclusion comes from §5, not from a cardinality ceiling.**  With
`q = n · ρ²`, (CLB) is a *lower* bound `n ≥ δ^{κ_F} ρ^{a_F - 2}` on the cardinality.  `ρ^{-2}` is
the normalised Kakeya cardinality scale, not an absolute maximum for an arbitrary family. -/
theorem card_lower_bound_of_capacity {δ ρ n aF κF : ℝ}
    (hρ0 : 0 < ρ)
    (hq : δ ^ κF * ρ ^ aF ≤ n * ρ ^ (2:ℝ)) :
    δ ^ κF * ρ ^ (aF - 2) ≤ n := by
  have hρ2 : (0:ℝ) < ρ ^ (2:ℝ) := Real.rpow_pos_of_pos hρ0 _
  have hsplit : ρ ^ aF = ρ ^ (aF - 2) * ρ ^ (2:ℝ) := by
    rw [← Real.rpow_add hρ0]; ring_nf
  rw [hsplit] at hq
  have : (δ ^ κF * ρ ^ (aF - 2)) * ρ ^ (2:ℝ) ≤ n * ρ ^ (2:ℝ) := by
    calc (δ ^ κF * ρ ^ (aF - 2)) * ρ ^ (2:ℝ)
        = δ ^ κF * (ρ ^ (aF - 2) * ρ ^ (2:ℝ)) := by ring
      _ ≤ n * ρ ^ (2:ℝ) := hq
  exact le_of_mul_le_mul_right this hρ2

/-- **Satisfiability witness for (C) and (CLB).**  `δ = ρ = 1/2`, `a_F = 2`, `κ_F = 0`,
`C₀ = 1`, `C_F = 4 = ρ^{-a_F}`, `q = 1/4`.  All hypotheses hold and the conclusion
`δ^{κ_F} ρ^{a_F} = 1/4 ≤ q` is attained with equality, so the ledger is tight, not vacuous. -/
theorem clbWitness :
    ((1:ℝ)/2) ^ (0:ℝ) * ((1:ℝ)/2) ^ (2:ℝ) ≤ 1/4 := by
  have hrpow : ((1:ℝ)/2) ^ (-(2:ℝ)) = 4 := by
    rw [Real.rpow_neg (by norm_num), show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    norm_num
  refine capacity_lower_bound (δ := 1/2) (ρ := 1/2) (q := 1/4) (CF := 4) (C₀ := 1)
    (aF := 2) (κF := 0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_
  · rw [hrpow]; norm_num
  · rw [Real.rpow_neg (by norm_num)]; norm_num

/-! ## §5.2 The capacity inequality (CAP)

The five losses stay apart.  `ℓ_μ` — the multiplicity/refinement loss — is deliberately *not* a
field of `Kakeya.ml1Ledger.CapSpec`: it enters the global budget of §6.1 only. -/

/-- The exponent data of the §5.2 capacity inequality.  `p = 1 - γ/2`.

Fields, and what each is: `aF` is the local Frostman exponent of §5.1, `aG` the gain exponent of
the middle target, `kappaF` the Frostman-constant loss, `kappaCard` the carrier/cardinality loss
(typically `0` for a fixed skeleton), `gamma` the Kakeya exponent under improvement, `epsScale`
the relative-scale exponent from `r ≤ δ ^ epsScale`.

There is intentionally no `ℓ_μ` field and no identification of `aF` with `a_lambda` or with any
`η_{j-1}`. -/
structure CapSpec where
  /-- The local Frostman exponent of §5.1. -/
  aF : ℝ
  /-- The gain exponent of the middle target. -/
  aG : ℝ
  /-- The Frostman-constant loss. -/
  kappaF : ℝ
  /-- The carrier/cardinality loss; `0` for a fixed skeleton. -/
  kappaCard : ℝ
  /-- The Kakeya exponent. -/
  gamma : ℝ
  /-- The relative-scale exponent: `r ≤ δ ^ epsScale`. -/
  epsScale : ℝ
  aF_nonneg : 0 ≤ aF
  aG_nonneg : 0 ≤ aG
  kappaF_nonneg : 0 ≤ kappaF
  kappaCard_nonneg : 0 ≤ kappaCard
  gamma_pos : 0 < gamma
  gamma_lt_two : gamma < 2
  epsScale_pos : 0 < epsScale
  /-- `2γ > a_F p`. -/
  dominates : aF * (1 - gamma / 2) < 2 * gamma
  /-- **(CAP)**: `10 a_G + (κ_F + κ_card) p < ε_scale (2γ - a_F p)`. -/
  cap : 10 * aG + (kappaF + kappaCard) * (1 - gamma / 2)
      < epsScale * (2 * gamma - aF * (1 - gamma / 2))

/-- **What `dominates` really asks of `γ`.**  `2γ > a_F p` with `p = 1 - γ/2` is equivalent to
`γ > 2 a_F / (4 + a_F)`.  In particular the natural local exponent `a_F = 2` forces `γ > 2/3`:
the capacity inequality is *not* available at every `γ`, and this constraint has to be carried
along rather than assumed away. -/
theorem dominates_iff {aF gamma : ℝ} (haF : 0 ≤ aF) :
    aF * (1 - gamma / 2) < 2 * gamma ↔ 2 * aF / (4 + aF) < gamma := by
  have h4 : (0:ℝ) < 4 + aF := by linarith
  rw [div_lt_iff₀ h4]
  constructor <;> intro h <;> linarith

/-- The `a_F = 2` instance of `Kakeya.ml1Ledger.dominates_iff`: `γ > 2/3`. -/
theorem dominates_two_iff {gamma : ℝ} :
    (2:ℝ) * (1 - gamma / 2) < 2 * gamma ↔ 2 / 3 < gamma := by
  constructor <;> intro h <;> linarith

namespace CapSpec

variable (c : CapSpec)

/-- `p = 1 - γ/2`. -/
noncomputable def p : ℝ := 1 - c.gamma / 2

theorem p_pos : 0 < c.p := by
  have := c.gamma_lt_two
  unfold p; linarith

/-- The slack in (CAP): `ε_scale (2γ - a_F p) - (10 a_G + (κ_F + κ_card) p)`. -/
noncomputable def slack : ℝ :=
  c.epsScale * (2 * c.gamma - c.aF * c.p) - (10 * c.aG + (c.kappaF + c.kappaCard) * c.p)

theorem slack_pos : 0 < c.slack := by
  have := c.cap
  unfold slack p
  linarith

/-- **§5.2 (CAP) delivers a polynomial margin.**  If the target carrier obeys the (CLB)-derived
lower bound `q ≥ δ^{κ_F + κ_card} r^{a_F}` and the relative scale obeys `r ≤ δ^{ε_scale}`, then
the middle target right-hand side `δ^{10 a_G} r^{-2γ} q^p` is at least `δ^{-slack}` — a positive
power of `1/δ`, hence in particular at least `1`, so the target is never vacuous. -/
theorem target_ge (c : CapSpec) {δ r q : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (hr0 : 0 < r)
    (hrδ : r ≤ δ ^ c.epsScale)
    (hq : δ ^ (c.kappaF + c.kappaCard) * r ^ c.aF ≤ q) :
    δ ^ (-c.slack) ≤ δ ^ (10 * c.aG) * r ^ (-2 * c.gamma) * q ^ c.p := by
  have hp := c.p_pos
  have hδpow : (0:ℝ) < δ ^ (c.kappaF + c.kappaCard) := Real.rpow_pos_of_pos hδ0 _
  have hrpow : (0:ℝ) < r ^ c.aF := Real.rpow_pos_of_pos hr0 _
  have hbase : (0:ℝ) < δ ^ (c.kappaF + c.kappaCard) * r ^ c.aF := mul_pos hδpow hrpow
  -- (1) push `p` through the (CLB) bound on `q`
  have h1 : (δ ^ (c.kappaF + c.kappaCard) * r ^ c.aF) ^ c.p ≤ q ^ c.p :=
    Real.rpow_le_rpow hbase.le hq hp.le
  have h2 : (δ ^ (c.kappaF + c.kappaCard) * r ^ c.aF) ^ c.p
      = δ ^ ((c.kappaF + c.kappaCard) * c.p) * r ^ (c.aF * c.p) := by
    rw [Real.mul_rpow hδpow.le hrpow.le, ← Real.rpow_mul hδ0.le, ← Real.rpow_mul hr0.le]
  -- (2) the `r`-power collects to a single negative exponent
  have hneg : c.aF * c.p - 2 * c.gamma < 0 := by
    have := c.dominates
    unfold p
    linarith
  have hrcollect : r ^ (-2 * c.gamma) * r ^ (c.aF * c.p)
      = r ^ (c.aF * c.p - 2 * c.gamma) := by
    rw [← Real.rpow_add hr0]; ring_nf
  have hrδpow : (0:ℝ) < δ ^ c.epsScale := Real.rpow_pos_of_pos hδ0 _
  have h3 : δ ^ (c.epsScale * (c.aF * c.p - 2 * c.gamma))
      ≤ r ^ (c.aF * c.p - 2 * c.gamma) := by
    have hthis : (δ ^ c.epsScale) ^ (c.aF * c.p - 2 * c.gamma)
        ≤ r ^ (c.aF * c.p - 2 * c.gamma) :=
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (r := c.aF * c.p - 2 * c.gamma)
        hneg.le (Set.mem_Ioi.mpr hr0) (Set.mem_Ioi.mpr hrδpow) hrδ
    rwa [← Real.rpow_mul hδ0.le] at hthis
  -- (3) assemble
  have hgoalpow : δ ^ (-c.slack)
      = δ ^ (10 * c.aG) * (δ ^ (c.epsScale * (c.aF * c.p - 2 * c.gamma))
          * δ ^ ((c.kappaF + c.kappaCard) * c.p)) := by
    rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
    congr 1
    unfold slack
    ring
  rw [hgoalpow]
  have hA : (0:ℝ) < δ ^ (10 * c.aG) := Real.rpow_pos_of_pos hδ0 _
  have hB : (0:ℝ) < δ ^ ((c.kappaF + c.kappaCard) * c.p) := Real.rpow_pos_of_pos hδ0 _
  have hC : (0:ℝ) < δ ^ (c.epsScale * (c.aF * c.p - 2 * c.gamma)) :=
    Real.rpow_pos_of_pos hδ0 _
  have hstep : δ ^ (10 * c.aG) * (δ ^ (c.epsScale * (c.aF * c.p - 2 * c.gamma))
        * δ ^ ((c.kappaF + c.kappaCard) * c.p))
      ≤ δ ^ (10 * c.aG) * (r ^ (c.aF * c.p - 2 * c.gamma)
        * δ ^ ((c.kappaF + c.kappaCard) * c.p)) := by
    have := mul_le_mul_of_nonneg_right h3 hB.le
    exact mul_le_mul_of_nonneg_left this hA.le
  refine hstep.trans ?_
  have hrewrite : δ ^ (10 * c.aG) * (r ^ (c.aF * c.p - 2 * c.gamma)
        * δ ^ ((c.kappaF + c.kappaCard) * c.p))
      = δ ^ (10 * c.aG) * r ^ (-2 * c.gamma)
        * (δ ^ ((c.kappaF + c.kappaCard) * c.p) * r ^ (c.aF * c.p)) := by
    rw [← hrcollect]; ring
  rw [hrewrite, ← h2]
  have hpos : (0:ℝ) ≤ δ ^ (10 * c.aG) * r ^ (-2 * c.gamma) := by positivity
  exact mul_le_mul_of_nonneg_left h1 hpos

/-- The target is never vacuous: it always dominates `μ ≥ 1`. -/
theorem one_le_target (c : CapSpec) {δ r q : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hr0 : 0 < r)
    (hrδ : r ≤ δ ^ c.epsScale)
    (hq : δ ^ (c.kappaF + c.kappaCard) * r ^ c.aF ≤ q) :
    1 ≤ δ ^ (10 * c.aG) * r ^ (-2 * c.gamma) * q ^ c.p := by
  refine le_trans ?_ (c.target_ge hδ0 hδ1 hr0 hrδ hq)
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1 (by linarith [c.slack_pos])

end CapSpec

/-- **Satisfiability witness for (CAP).**  `γ = 1`, `a_F = 2`, `a_G = 1/100`, `κ_F = 1/100`,
`κ_card = 0` (fixed skeleton), `ε_scale = 1/2`.  Then `p = 1/2`, `2γ - a_F p = 1`, and
`10 a_G + (κ_F + κ_card) p = 0.105 < 0.5 = ε_scale (2γ - a_F p)`. -/
noncomputable def capWitness : CapSpec where
  aF := 2
  aG := 1 / 100
  kappaF := 1 / 100
  kappaCard := 0
  gamma := 1
  epsScale := 1 / 2
  aF_nonneg := by norm_num
  aG_nonneg := by norm_num
  kappaF_nonneg := by norm_num
  kappaCard_nonneg := by norm_num
  gamma_pos := by norm_num
  gamma_lt_two := by norm_num
  epsScale_pos := by norm_num
  dominates := by norm_num
  cap := by norm_num

theorem capWitness_slack : capWitness.slack = 79 / 200 := by
  unfold CapSpec.slack CapSpec.p capWitness
  norm_num

/-! ## §6.1 The absolute budget (ABS), with a non-circular parameter order

`8 a' ≤ 10 a` gives only non-negativity; it never gives strict slack.  The fix is to take the
minimum over the *finite* set of rung/branch choices before `δ` (and before `j`) is chosen, and
to allocate the extra losses out of that number. -/

/-- `8 a' ≤ 10 a` gives only `G_str ≥ 0`. -/
theorem gStr_nonneg {a a' : ℝ} (h : 8 * a' ≤ 10 * a) : 0 ≤ 10 * a - 8 * a' := by linarith

/-- **`8 a' ≤ 10 a` is not enough.**  A concrete triple with `8 a' ≤ 10 a` and `B₀ > 0` for which
(ABS) fails.  This is why the blueprint forbids deriving slack from non-negativity. -/
theorem gStr_nonneg_insufficient :
    ∃ a a' B₀ : ℝ, 8 * a' ≤ 10 * a ∧ 0 < B₀ ∧ ¬ (B₀ < 10 * a - 8 * a') :=
  ⟨0, 0, 1, by norm_num, by norm_num, by norm_num⟩

variable {ι : Type*}

/-- `B₀ = ε' + 2c + η_vol c / 2` of §6.1. -/
noncomputable def bZero (epsPrime cStep etaVol : ℝ) : ℝ := epsPrime + 2 * cStep + etaVol * cStep / 2

/-- **`S_*` of §6.1.**  The uniform slack over the finite rung/branch index set `J`, formed
*before* `δ` is chosen and before any rung is selected. -/
noncomputable def uniformSlack (J : Finset ι) (hJ : J.Nonempty) (aLam aLamP B₀ : ι → ℝ) : ℝ :=
  J.inf' hJ (fun j => 10 * aLam j - 8 * aLamP j - B₀ j)

theorem uniformSlack_le {J : Finset ι} {hJ : J.Nonempty} {aLam aLamP B₀ : ι → ℝ} {j : ι}
    (hj : j ∈ J) : uniformSlack J hJ aLam aLamP B₀ ≤ 10 * aLam j - 8 * aLamP j - B₀ j :=
  Finset.inf'_le _ hj

/-- **The slack is positive before `δ` is chosen.**  Only a rung-wise strict inequality is
needed, and the minimum is over a finite set, so no rung has to be selected first. -/
theorem uniformSlack_pos {J : Finset ι} {hJ : J.Nonempty} {aLam aLamP B₀ : ι → ℝ}
    (h : ∀ j ∈ J, B₀ j < 10 * aLam j - 8 * aLamP j) : 0 < uniformSlack J hJ aLam aLamP B₀ := by
  unfold uniformSlack
  rw [Finset.lt_inf'_iff]
  intro j hj
  have := h j hj
  linarith

/-- **§6.1 (ABS).**  Any total extra loss strictly below the uniform slack — chosen *before* the
rung `j`, hence non-circularly — leaves `10 a_λ(j) - 8 a'_λ(j) > B₀(j) + B_extra` at every rung
the ladder can select. -/
theorem abs_of_lt_uniformSlack {J : Finset ι} {hJ : J.Nonempty} {aLam aLamP B₀ : ι → ℝ}
    {Bextra : ℝ} (hB : Bextra < uniformSlack J hJ aLam aLamP B₀) {j : ι} (hj : j ∈ J) :
    B₀ j + Bextra < 10 * aLam j - 8 * aLamP j := by
  have := uniformSlack_le (hJ := hJ) (aLam := aLam) (aLamP := aLamP) (B₀ := B₀) hj
  linarith

/-! ### Counting a loss at its true multiplicity

A constant appearing `w i` times, or raised to a power, must be charged `w i` times. -/

/-- The ledger total: entry `i` charged at multiplicity `w i`. -/
noncomputable def totalLoss (s : Finset ι) (w : ι → ℕ) (e : ι → ℝ) : ℝ := ∑ i ∈ s, (w i : ℝ) * e i

/-- **A ledger that charges each entry at its true multiplicity dominates any actual usage.** -/
theorem loss_le_totalLoss {s : Finset ι} {u w : ι → ℕ} {e : ι → ℝ}
    (he : ∀ i ∈ s, 0 ≤ e i) (hu : ∀ i ∈ s, u i ≤ w i) :
    totalLoss s u e ≤ totalLoss s w e := by
  unfold totalLoss
  refine Finset.sum_le_sum fun i hi => ?_
  have : ((u i : ℝ)) ≤ (w i : ℝ) := by exact_mod_cast hu i hi
  exact mul_le_mul_of_nonneg_right this (he i hi)

/-- **A loss raised to the power `p` is charged `p` times.**  `(δ^{-e})^p = δ^{-(p e)}`. -/
theorem rpow_loss_pow {δ : ℝ} (hδ0 : 0 < δ) (e p : ℝ) :
    (δ ^ (-e)) ^ p = δ ^ (-(p * e)) := by
  rw [← Real.rpow_mul hδ0.le]
  ring_nf

/-- The uniform slack of the (ABS) witness: two rungs, `a_λ = 1/10`, `a'_λ = 1/100`,
`B₀ = 1/100`, so `S_* = 91/100`. -/
theorem absWitness_slack :
    uniformSlack ({0, 1} : Finset ℕ) ⟨0, by decide⟩
      (fun _ => (1:ℝ)/10) (fun _ => (1:ℝ)/100) (fun _ => (1:ℝ)/100) = 91 / 100 := by
  simp only [uniformSlack, Finset.inf'_const]
  norm_num

/-- **Satisfiability witness for (ABS).**  The slack `91/100` is fixed before the rung is
selected, a total extra loss `B_extra = 1/2` is allocated out of it, and (ABS) then holds at
every rung of the finite index set. -/
theorem absWitness : ∀ j ∈ ({0, 1} : Finset ℕ),
    (1:ℝ)/100 + 1/2 < 10 * ((1:ℝ)/10) - 8 * ((1:ℝ)/100) := fun _ hj =>
  abs_of_lt_uniformSlack (Bextra := 1/2) (by rw [absWitness_slack]; norm_num) hj

/-! ## §6.2 The improvement inequality (IMP)

`G` is the **net** gain after every factoring, normalisation, fixed-constant and endpoint loss;
`ν` is a free parameter of the improvement, never hardcoded to `η₁`. -/

/-- The exponent data of the §6.2 improvement inequality. -/
structure ImpSpec where
  /-- The Kakeya exponent being improved. -/
  gamma : ℝ
  /-- The floor exponent. -/
  beta : ℝ
  /-- The improvement step; a free parameter, **not** hardcoded to `η₁`. -/
  nu : ℝ
  /-- The global Frostman exponent: `Q ≥ δ^{η₀}`. -/
  eta0 : ℝ
  /-- The **net** gain, after every factoring, normalisation, fixed-constant and endpoint loss. -/
  G : ℝ
  nu_pos : 0 < nu
  nu_lt_gap : nu < gamma - beta
  eta0_nonneg : 0 ≤ eta0
  /-- **(IMP)**: `G > 2ν + η₀ ν / 2`. -/
  imp : 2 * nu + eta0 * nu / 2 < G

namespace ImpSpec

/-- **§6.2 (IMP).**  From `μ ≤ δ^G δ^{-2γ} Q^{1-γ/2}` and the global Frostman lower bound
`Q ≥ δ^{η₀}`, the inequality `G > 2ν + η₀ν/2` upgrades the estimate to the `K_F(γ - ν)` shape
`μ ≤ δ^{-2(γ-ν)} Q^{1-(γ-ν)/2}`. -/
theorem improvement (c : ImpSpec) {δ Q mu : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hQ0 : 0 < Q)
    (hQfr : δ ^ c.eta0 ≤ Q)
    (hmu : mu ≤ δ ^ c.G * δ ^ (-2 * c.gamma) * Q ^ (1 - c.gamma / 2)) :
    mu ≤ δ ^ (-2 * (c.gamma - c.nu)) * Q ^ (1 - (c.gamma - c.nu) / 2) := by
  refine hmu.trans ?_
  have hnu := c.nu_pos
  have hQhalf : (0:ℝ) < Q ^ (1 - c.gamma / 2) := Real.rpow_pos_of_pos hQ0 _
  -- split the RHS `Q`-power
  have hQsplit : Q ^ (1 - (c.gamma - c.nu) / 2)
      = Q ^ (1 - c.gamma / 2) * Q ^ (c.nu / 2) := by
    rw [← Real.rpow_add hQ0]; ring_nf
  -- the Frostman lower bound on the extra `Q`-power
  have hQpow : δ ^ (c.eta0 * c.nu / 2) ≤ Q ^ (c.nu / 2) := by
    have h := Real.rpow_le_rpow (Real.rpow_pos_of_pos hδ0 c.eta0).le hQfr (by linarith : (0:ℝ) ≤ c.nu / 2)
    rwa [← Real.rpow_mul hδ0.le, show c.eta0 * (c.nu / 2) = c.eta0 * c.nu / 2 by ring] at h
  -- the `δ`-power comparison
  have hδcmp : δ ^ c.G * δ ^ (-2 * c.gamma)
      ≤ δ ^ (-2 * (c.gamma - c.nu)) * δ ^ (c.eta0 * c.nu / 2) := by
    rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
    refine Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_
    have := c.imp
    linarith
  have hL : δ ^ c.G * δ ^ (-2 * c.gamma) * Q ^ (1 - c.gamma / 2)
      ≤ (δ ^ (-2 * (c.gamma - c.nu)) * δ ^ (c.eta0 * c.nu / 2)) * Q ^ (1 - c.gamma / 2) :=
    mul_le_mul_of_nonneg_right hδcmp hQhalf.le
  refine hL.trans ?_
  rw [hQsplit]
  have hA : (0:ℝ) < δ ^ (-2 * (c.gamma - c.nu)) := Real.rpow_pos_of_pos hδ0 _
  have : (δ ^ (-2 * (c.gamma - c.nu)) * Q ^ (1 - c.gamma / 2)) * δ ^ (c.eta0 * c.nu / 2)
      ≤ (δ ^ (-2 * (c.gamma - c.nu)) * Q ^ (1 - c.gamma / 2)) * Q ^ (c.nu / 2) :=
    mul_le_mul_of_nonneg_left hQpow (by positivity)
  calc (δ ^ (-2 * (c.gamma - c.nu)) * δ ^ (c.eta0 * c.nu / 2)) * Q ^ (1 - c.gamma / 2)
      = (δ ^ (-2 * (c.gamma - c.nu)) * Q ^ (1 - c.gamma / 2)) * δ ^ (c.eta0 * c.nu / 2) := by
        ring
    _ ≤ (δ ^ (-2 * (c.gamma - c.nu)) * Q ^ (1 - c.gamma / 2)) * Q ^ (c.nu / 2) := this
    _ = δ ^ (-2 * (c.gamma - c.nu)) * (Q ^ (1 - c.gamma / 2) * Q ^ (c.nu / 2)) := by ring

end ImpSpec

/-- **Satisfiability witness for (IMP).**  `γ = 1`, `β = 1/2`, `ν = 1/4`, `η₀ = 1/100`,
`G = 51/100`: `2ν + η₀ν/2 = 1/2 + 1/800 = 401/800 < 51/100 = 408/800`. -/
noncomputable def impWitness : ImpSpec where
  gamma := 1
  beta := 1 / 2
  nu := 1 / 4
  eta0 := 1 / 100
  G := 51 / 100
  nu_pos := by norm_num
  nu_lt_gap := by norm_num
  eta0_nonneg := by norm_num
  imp := by norm_num

/-! ## §6.5 The two endpoints

Neither is allowed to be forced through the interior scale lemmas. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **A one-element (or empty) family has multiplicity at most `1`.**  This is the engine of both
endpoints: no analytic estimate is invoked. -/
theorem multiplicity_le_one_of_card_le_one {s : Finset ι} {V : ι → ShadedBody E}
    (h : s.card ≤ 1) : multiplicity s V ≤ 1 := by
  refine (multiplicity_le_card s V).trans ?_
  exact_mod_cast (by exact_mod_cast h : (s.card : ENNReal) ≤ (1 : ℕ))

end

/-- **Endpoint `τ = δ`: the fine relative scale is `1`.** -/
theorem fine_relative_scale_eq_one {τ δ : ℝ} (hδ0 : 0 < δ) (h : τ = δ) : δ / τ = 1 := by
  rw [h]; field_simp

/-- **Endpoint `τ = δ`: the fine scalar factor collapses to `O(1)`.**  At relative scale `1` and
singleton fibre cardinality the interior right-hand side
`δ^{10 a} ρ^{-2γ} (n ρ²)^{1-γ/2}` is exactly `δ^{10 a} ≤ 1`.  The small-scale Lemma 3.9 is not
invoked. -/
theorem fine_factor_collapse {δ a gamma : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) :
    δ ^ (10 * a) * (1:ℝ) ^ (-2 * gamma) * ((1:ℝ) * (1:ℝ) ^ (2:ℝ)) ^ (1 - gamma / 2)
      ≤ 1 := by
  simp only [Real.one_rpow, mul_one]
  exact Real.rpow_le_one hδ0.le hδ1 (by linarith)

/-- **Endpoint `τ = δ`: only the middle and coarse factors survive in (F).**  Once the fine
scalar factor is `≤ 1` it may simply be deleted from the three-factor product. -/
theorem product_collapse_fine {L muT muf mum muc : ENNReal} (hf : muf ≤ 1)
    (h : muT ≤ L * muf * mum * muc) : muT ≤ L * mum * muc := by
  refine h.trans ?_
  have : L * muf ≤ L := by
    calc L * muf ≤ L * 1 := mul_le_mul_left' hf L
      _ = L := mul_one L
  exact mul_le_mul_right' (mul_le_mul_right' this mum) muc

/-- **Endpoint `θ = 1`: the root/coarse family is a singleton, the coarse scalar collapses to
`1`, and only the first factorisation survives.**  The root middle Frostman facts still need
separate verification; nothing here supplies them. -/
theorem product_collapse_coarse {L muT muf mum muc : ENNReal} (hc : muc ≤ 1)
    (h : muT ≤ L * muf * mum * muc) : muT ≤ L * muf * mum := by
  refine h.trans ?_
  calc L * muf * mum * muc ≤ L * muf * mum * 1 := mul_le_mul_left' hc _
    _ = L * muf * mum := mul_one _

/-! ### The endpoint form of the three-factor inequality (F) -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **Endpoint `τ = δ`, applied to (F).**  When the fine fibre is a singleton its multiplicity
factor is `≤ 1` and drops out of the three-factor product with no analytic input at all. -/
theorem factorisation_at_tau_eq_delta {L muT mum muc : ENNReal} {s : Finset ι}
    {V : ι → ShadedBody E} (hcard : s.card ≤ 1)
    (h : muT ≤ L * multiplicity s V * mum * muc) : muT ≤ L * mum * muc :=
  product_collapse_fine (multiplicity_le_one_of_card_le_one hcard) h

/-- **Endpoint `θ = 1`, applied to (F).**  The root/coarse family is a singleton, so its
multiplicity factor is `≤ 1` and only the first factorisation survives.  The root middle Frostman
facts are *not* supplied here and still need separate verification. -/
theorem factorisation_at_theta_eq_one {L muT muf : ENNReal} {s : Finset ι}
    {V : ι → ShadedBody E} (hcard : s.card ≤ 1) {mum : ENNReal}
    (h : muT ≤ L * muf * mum * multiplicity s V) : muT ≤ L * muf * mum :=
  product_collapse_coarse (multiplicity_le_one_of_card_le_one hcard) h

end

/-! ## GWZ v1 errata, as checkable statements

Three of the source's printed inequalities are not merely imprecise, they are refutable as
printed.  Each is recorded here as a Lean `False`-conclusion or as the corrected form, so that no
later step can quietly re-import the broken version. -/

/-- **Errata at GWZ equation (64).**  The printed upper bound on `C_F(𝕋̃)` carries a *positive*
exponent, `C_F ≤ δ̃^α` with `α > 0`.  That is inconsistent with `C_F ≥ 1`, which
`ConvexSpaceBody.one_le_frostmanConstant` supplies whenever the family has positive density.  Any
usable form of (64) must be of negative-exponent type. -/
theorem eq64_positive_exponent_false {δt CF α : ℝ} (hδt0 : 0 < δt) (hδt1 : δt < 1)
    (hα : 0 < α) (hCF : 1 ≤ CF) (hub : CF ≤ δt ^ α) : False := by
  have h : δt ^ α < 1 := Real.rpow_lt_one hδt0.le hδt1 hα
  linarith

/-- **Errata in the proof of GWZ Proposition 6.6.**  The printed `λ ⪆ δ^{-η}` is impossible for a
density `λ ≤ 1`: with `0 < δ < 1` and `η > 0` the right-hand side already exceeds `1`.  The
intended inequality is `λ ⪆ δ^{η}`. -/
theorem prop66_sign_error_false {δ lam η : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η)
    (hlam : lam ≤ 1) (hbad : δ ^ (-η) ≤ lam) : False := by
  have h : (1:ℝ) < δ ^ (-η) := Real.one_lt_rpow_iff_of_pos hδ0 |>.mpr (Or.inr ⟨hδ1, by linarith⟩)
  linarith

/-- **Errata at GWZ equation (66).**  From `b ≤ δ̃^{1-ε}` the gain in the exponent is
`2(1-ε)(γ-β)`, not `2(γ-β)`. -/
theorem gain_at_eq66 {δt b gamma beta eps : ℝ} (hδt0 : 0 < δt) (hb0 : 0 < b)
    (hb : b ≤ δt ^ (1 - eps)) (hgap : beta ≤ gamma) :
    b ^ (2 * (gamma - beta)) ≤ δt ^ (2 * (1 - eps) * (gamma - beta)) := by
  have hexp : (0:ℝ) ≤ 2 * (gamma - beta) := by linarith
  have h := Real.rpow_le_rpow hb0.le hb hexp
  rwa [← Real.rpow_mul hδt0.le, show (1 - eps) * (2 * (gamma - beta))
    = 2 * (1 - eps) * (gamma - beta) by ring] at h

/-- The shortfall that equation (66) hides, `2ε(γ-β)`, which must be charged to the error
ledger. -/
theorem gain_at_eq66_shortfall (gamma beta eps : ℝ) :
    2 * (gamma - beta) - 2 * (1 - eps) * (gamma - beta) = 2 * eps * (gamma - beta) := by ring

/-- **Errata at the end of GWZ §8.**  "`η_{j-1} ≤ N`" compares an exponent with a rung count and
is a type error.  The intended statement is a ladder bound, `η_{j-1} ≤ η_N`, and the primed
exponent has to be controlled by the same ladder rather than left free. -/
theorem ladder_bound {N j : ℕ} {eta etaPrime : ℕ → ℝ}
    (hmono : ∀ k l, k ≤ l → l ≤ N → eta k ≤ eta l)
    (hprime : ∀ k, k ≤ N → etaPrime k ≤ eta N) (hj : j ≤ N) :
    eta j ≤ eta N ∧ etaPrime j ≤ eta N :=
  ⟨hmono j N hj le_rfl, hprime j hj⟩

/-! ## §6.4 The application error at equations (60) and (61)

Coarsening a loss to `δ^{-η_{j-1}}` needs an explicit inequality; `ε_app ≤ (1 + γ/2) η_{j-1}` is
what GWZ equation (60) actually requires.  Equation (61) has the same `j = 1` problem, so both
are covered below. -/

/-- **The coarsening step of §6.4.**  `ε_app ≤ (1 + γ/2) η` is exactly what licenses replacing
the loss `δ^{-ε_app}` by the coarser `δ^{-(1+γ/2)η}`. -/
theorem appError_coarsen {δ epsApp eta gamma : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : epsApp ≤ (1 + gamma / 2) * eta) :
    δ ^ (-epsApp) ≤ δ ^ (-((1 + gamma / 2) * eta)) :=
  Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)

/-- **`ε_app ≤ η₀/16` is a sufficient interior choice — and it also covers `j = 1`.**  On the
ladder `η` is smallest at `0`, so `η₀ ≤ η_{j-1}` for every admissible `j`, including `j = 1`
where `η_{j-1} = η₀` and the hypothesis is reflexive. -/
theorem appError_admissible {epsApp eta0 etaPrev gamma : ℝ}
    (hgamma : 0 ≤ gamma) (heta0 : 0 ≤ eta0) (hladder : eta0 ≤ etaPrev)
    (h : epsApp ≤ eta0 / 16) :
    epsApp ≤ (1 + gamma / 2) * etaPrev := by
  have hprev : 0 ≤ etaPrev := le_trans heta0 hladder
  nlinarith

/-- **§6.4 for GWZ equation (60), uniformly in `j`, including `j = 1`.**  With `η` bottoming out
at `η 0` on the ladder, the single choice `ε_app ≤ η 0 / 16` is admissible at every rung; at
`j = 1` the ladder hypothesis is applied at index `0`. -/
theorem eq60_appError_uniform {N : ℕ} {eta : ℕ → ℝ} {epsApp gamma : ℝ}
    (hgamma : 0 ≤ gamma) (heta0 : 0 ≤ eta 0) (hladder : ∀ k, k ≤ N → eta 0 ≤ eta k)
    (h : epsApp ≤ eta 0 / 16) {j : ℕ} (_hj1 : 1 ≤ j) (hjN : j ≤ N) :
    epsApp ≤ (1 + gamma / 2) * eta (j - 1) :=
  appError_admissible hgamma heta0 (hladder (j - 1) (le_trans (Nat.sub_le j 1) hjN)) h

/-- **§6.4 for GWZ equation (61), uniformly in `j`, including `j = 1`.**  Equation (61) carries
the same `j = 1` application-error problem as (60), and fixing (60) alone is not enough; here the
coarsened loss inequality is delivered directly. -/
theorem eq61_appError_uniform {N : ℕ} {eta : ℕ → ℝ} {epsApp gamma δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hgamma : 0 ≤ gamma) (heta0 : 0 ≤ eta 0) (hladder : ∀ k, k ≤ N → eta 0 ≤ eta k)
    (h : epsApp ≤ eta 0 / 16) {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    δ ^ (-epsApp) ≤ δ ^ (-((1 + gamma / 2) * eta (j - 1))) :=
  appError_coarsen hδ0 hδ1 (eq60_appError_uniform hgamma heta0 hladder h hj1 hjN)

end ml1Ledger

end Kakeya

end
