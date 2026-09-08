/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

/-!
# Density regularization on a fixed tree (`B1`, `PO-1`)

This file is Step 2 of the checked Main Lemma 1 repair blueprint, the interface `B1`
(`regularizeOnFixedTree`).

The blueprint's central structural decision is that the carrier hierarchy is uniformized
**once** and then **fixed**: after that point no step may choose a new subfamily and hope to
recover Definition 2.1/2.2 uniformity, new balanced-parent witnesses or local Frostman
certificates on it, because none of those transfers downward for free.  What a later step *is*
allowed to do is thin the *active support* inside the already-prescribed fibres, keeping the
ambient family and the parent maps literally unchanged.  This file is that operation.

## The construction is not new; the fixed-tree layer and the bridge clause are

The blueprint prescribes the construction order "discard the tubes of density below `λ / 2`,
then dyadic-pigeonhole what survives", and both moves are already in this development, composed
by `Kakeya.ml1Boot.exists_internalDensityNormalization`, which returns the bracket at the
*fixed*, `δ`-independent constant `Λ = 2` together with three retention certificates.  So
`regularizeOnFixedTree` does not re-derive any of that.  What it adds is

* the layer `B1` asks for: the operation is performed against a **prescribed** parent map, and
  the certificates come back in *tree-relative* form; and
* the **multiplicity bridge** `mult_bridge`, the certificate
  `Kakeya.ml1Boot.exists_internalDensityNormalization` already proves and which the two-scale
  composition `Kakeya.ml1Boot.isTwoScaleFactors_of_two` consumes as its hypothesis `hbridge`.
  Carrying it in `δ`-power form is what removes `hbridge` from that composition's binder; see
  `Kakeya.ml1Boot.isTwoScaleFactors_of_two_regularized`.

## Why `Λ = 2` and not `Λ = 2 / λ`

A single density threshold cut gives a two-sided bracket at `Λ = 2 / λ`, which depends on `δ`.
That is unusable downstream: the rescaled family's uniformity constant is instantiated *before*
`δ`, `τ`, `θ` and the family are quantified, so a `δ`-dependent `Λ` arrives too late — and
this, not any failure of uniformity heredity, is the real quantifier obstruction.  Pigeonholing
into a single dyadic band instead fixes `Λ = 2`, keeping the constant `δ`-independent and
pushing all the `δ`-dependence into retention losses, which are consumed *after* `δ` is fixed.

## Why the polynomial fullness lower bound is not optional

The dyadic pigeonhole's retention is `(1 + log₂ (1 / λ))⁻¹`.  That is `O(log (1 / δ))` — hence
absorbable into a `δ`-power ledger — **only** if `λ` is bounded below by a fixed power of `δ`.
If `λ` were smaller than every `δ ^ A` the bin count would not be controlled by
`O(log (1 / δ))`.  The hypothesis `hpoly : δ ^ a₀ ≤ λ` is therefore carried in the statement,
and it is what lets the conclusion state its retentions as plain `δ`-powers.

## What this file does not produce

`regularizeOnFixedTree` does **not** output GWZ Definition 2.2 shaded uniformity, and does not
claim that a uniform subfamily survives zero-extension as a witness for the original tree.  The
only uniformity-flavoured data it returns is tree-relative: the incidence with the prescribed
parent set, and the fibrewise decomposition of the retained shade mass, both of which the fixed
tree already certifies and neither of which passing to a subset can invent.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

section Regularize

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`B1`, `regularizeOnFixedTree`** (blueprint §3, §9 Step 2).

Thin the active support of a shaded tube family, *inside* a carrier tree whose parent map `p`
and parent index set `t` are already prescribed, until the shading density is pinned to the
fixed constant `Λ = 2` — while keeping `δ`-power retention, the multiplicity bridge, and every
tree-relative certificate.

Input, matching the blueprint:

* a fixed finite carrier tree: the ambient family, the parent map `p` and the parent set `t`,
  with `hp` the prescribed incidence.  None of these is an output, so there is nothing for the
  conclusion to have to preserve;
* an active support `active ⊆ ambient` with its shaded tubes `U`, and `hne` its nonemptiness —
  the non-degenerate branch of `B0` in the form the construction consumes, and what forbids an
  all-empty input from producing a positive density;
* an average fullness lower bound `hfull`, `λ ≤ λ(active, U)`, with `λ > 0`;
* the **polynomial** fullness lower bound `hpoly`, `δ ^ a₀ ≤ λ`.

Output:

* `active' ⊆ active` nonempty, with the ambient family, the parent map and the parent set
  literally unchanged;
* a `μ₀ > 0` with the two-sided bracket at the fixed, `δ`-independent constant `2`;
* the **multiplicity bridge** `μ(active, U) ≤ 16 · δ ^ (-a₀) · μ(active', U)`;
* retention as plain `δ`-powers: the surviving average fullness and the surviving cardinality
  are both at least `δ ^ (2 a₀) / 16` of what they were.  Cardinality retention is what
  transports a local Frostman constant, via
  `ConvexSpaceBody.frostmanConstIn_subfamily_le`;
* the tree-relative certificates: the retained tubes still map into the prescribed `t`, and the
  retained shade mass decomposes over the prescribed fibres.

The proof is a wrapper: `Kakeya.ml1Boot.exists_internalDensityNormalization` does the discard
and the dyadic pigeonhole, and the only work here is converting its `λ`-shaped retentions into
`δ`-power form using `hpoly`, and reading off the two fixed-tree facts. -/
theorem regularizeOnFixedTree [Nontrivial E] {ι κ : Type*} [DecidableEq κ]
    {τ : NNReal} (hτ0 : 0 < τ)
    {ambient active : Finset ι} (hact : active ⊆ ambient)
    (p : ι → κ) (t : Finset κ) (hp : ∀ i ∈ ambient, p i ∈ t)
    (U : ι → ShadedTube τ E) (hne : active.Nonempty)
    {lam : NNReal} (hlam0 : 0 < lam)
    (hfull : (lam : ENNReal)
      ≤ (ShadedBody.fullness active (fun i => (U i).toShadedBody) : ENNReal))
    {a₀ : ℝ} {δ : NNReal}
    (hpoly : (δ : ENNReal) ^ a₀ ≤ (lam : ENNReal)) :
    ∃ active' ⊆ active, active'.Nonempty ∧ ∃ mu0 : ENNReal, 0 < mu0 ∧
      (∀ i ∈ active', ((2 : NNReal) : ENNReal)⁻¹ * mu0 * volume (U i).carrier
            ≤ volume (U i).shade ∧
          volume (U i).shade ≤ ((2 : NNReal) : ENNReal) * mu0 * volume (U i).carrier) ∧
      ShadedBody.multiplicity active (fun i => (U i).toShadedBody)
          ≤ 16 * (δ : ENNReal) ^ (-a₀)
            * ShadedBody.multiplicity active' (fun i => (U i).toShadedBody) ∧
      (δ : ENNReal) ^ (2 * a₀) / 16
          ≤ (ShadedBody.fullness active' (fun i => (U i).toShadedBody) : ENNReal) ∧
      (δ : ENNReal) ^ (2 * a₀) / 16 * (active.card : ENNReal) ≤ (active'.card : ENNReal) ∧
      (∀ i ∈ active', p i ∈ t) ∧
      ∑ k ∈ t, ∑ i ∈ active' with p i = k, volume (U i).shade
        = ∑ i ∈ active', volume (U i).shade := by
  classical
  obtain ⟨u₂, hu₂sub, hu₂ne, mu0, hmu0, hbracket, hmult, hfull₂, hcard₂⟩ :=
    exists_internalDensityNormalization hτ0 U hne hlam0 hfull
  -- the polynomial fullness lower bound turns the retention certificates into `δ`-powers
  have hsq : (δ : ENNReal) ^ (2 * a₀) ≤ (lam : ENNReal) ^ 2 := by
    have hrw : (δ : ENNReal) ^ (2 * a₀) = ((δ : ENNReal) ^ a₀) ^ (2 : ℕ) := by
      rw [← ENNReal.rpow_natCast ((δ : ENNReal) ^ a₀) 2, ← ENNReal.rpow_mul]
      congr 1
      push_cast
      ring
    rw [hrw]
    exact pow_le_pow_left' hpoly 2
  have hret : (δ : ENNReal) ^ (2 * a₀) / 16 ≤ (lam : ENNReal) ^ 2 / 16 :=
    ENNReal.div_le_div_right hsq 16
  -- and the same bound turns the multiplicity bridge into a `δ`-power
  have hbridge : (16 : ENNReal) / (lam : ENNReal) ≤ 16 * (δ : ENNReal) ^ (-a₀) := by
    have hinv : ((lam : ENNReal))⁻¹ ≤ ((δ : ENNReal) ^ a₀)⁻¹ := ENNReal.inv_le_inv.mpr hpoly
    have hrw : ((δ : ENNReal) ^ a₀)⁻¹ = (δ : ENNReal) ^ (-a₀) := by
      rw [← ENNReal.rpow_neg]
    rw [ENNReal.div_eq_inv_mul, mul_comm ((lam : ENNReal))⁻¹ 16]
    calc (16 : ENNReal) * ((lam : ENNReal))⁻¹
        ≤ 16 * ((δ : ENNReal) ^ a₀)⁻¹ := by gcongr
      _ = 16 * (δ : ENNReal) ^ (-a₀) := by rw [hrw]
  refine ⟨u₂, hu₂sub, hu₂ne, mu0, hmu0, hbracket, ?_, hret.trans hfull₂, ?_, ?_, ?_⟩
  · exact hmult.trans (by gcongr)
  · exact le_trans (mul_le_mul_left hret _) hcard₂
  · exact fun i hi => hp _ (hact (hu₂sub hi))
  · exact Finset.sum_fiberwise_of_maps_to (fun i hi => hp _ (hact (hu₂sub hi))) _

/-! ## The bridge: `B1` supplies exactly the hypothesis `hbridge` of `B3`

`Kakeya.ml1Boot.isTwoScaleFactors_of_two` consumes a hypothesis

```
hbridge : μ(tAct₁, Zτ) ≤ Lreg * μ(mid, Zτ)     with     mid ⊆ tAct₁
```

on a **fixed tree with prescribed parent maps** — the one clause blueprint `B3` left open.
The corollary below discharges it: applied to the active parent family of a
`Kakeya.ml1Boot.IsOneScaleSelected` bundle, `Kakeya.ml1Boot.regularizeOnFixedTree` returns the
`mid` *together with* the multiplicity bridge at `Lreg = 16 δ ^ (-a₀)`, plus the density
bracket and the fullness/cardinality retentions the second Lemma 5.11 application needs, and
plus the tree-relative incidence with the prescribed coarse parent set.

Note where the loss comes from.  The bridge is not a refinement retention paid twice
(blueprint §2.3): it is `Kakeya.ml1Boot.exists_internalDensityNormalization`'s own multiplicity
comparison, which holds because thinning shrinks the shade-mass numerator by at most the
retention factor while shrinking the shaded-union denominator too.  The polynomial fullness
lower bound `hpoly` is what turns its `16 / λ` into the `δ`-power `16 δ ^ (-a₀)`. -/
section Bridge

variable {ι κ lc : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]
  {σ ρ : NNReal}

/-- **`B1` discharges `B3`'s `hbridge`.**

From a one-scale selected bundle `h` whose active parent family `tAct` has average fullness
`lamP ≥ δ ^ a₀`, regularizing on the *fixed* tree `(tAmb, pθ, tθAmb)` returns an active middle
support `mid ⊆ tAct` carrying:

* the factor-two density bracket at a single `μ₀ > 0`;
* **the bridge** `μ(tAct, Zρ) ≤ 16 δ ^ (-a₀) · μ(mid, Zρ)`, which is verbatim the `hbridge`
  binder of `Kakeya.ml1Boot.isTwoScaleFactors_of_two` at `Lreg = 16 δ ^ (-a₀)`;
* `δ`-power fullness and cardinality retention;
* the prescribed coarse incidence `∀ k ∈ mid, pθ k ∈ tθAmb`.

Nothing about the ambient skeleton, `pτ`, `pθ`, `tAmb` or `tθAmb` moves. -/
theorem exists_regularizedMid_bridge [Nontrivial E] (hρ0 : 0 < ρ)
    {c L : ENNReal} {amb act : Finset ι} {V : ι → ShadedTube σ E}
    {tAmb : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
    {act' : Finset ι} {Z' : ι → ShadedTube σ E}
    {tAct : Finset κ} {Zρ : κ → ShadedTube ρ E} {k₀ : κ} {lamP lamF : NNReal}
    (h : IsOneScaleSelected c L amb act V tAmb Vρ p act' Z' tAct Zρ k₀ lamP lamF)
    (pθ : κ → lc) (tθAmb : Finset lc) (hsk : ∀ k ∈ tAmb, pθ k ∈ tθAmb)
    (hlamP0 : 0 < lamP) {a₀ : ℝ} {δ : NNReal}
    (hpoly : (δ : ENNReal) ^ a₀ ≤ (lamP : ENNReal)) :
    ∃ mid ⊆ tAct, mid.Nonempty ∧ ∃ mu0 : ENNReal, 0 < mu0 ∧
      (∀ k ∈ mid, ((2 : NNReal) : ENNReal)⁻¹ * mu0 * volume (Zρ k).carrier
            ≤ volume (Zρ k).shade ∧
          volume (Zρ k).shade ≤ ((2 : NNReal) : ENNReal) * mu0 * volume (Zρ k).carrier) ∧
      ShadedBody.multiplicity tAct (fun k => (Zρ k).toShadedBody)
          ≤ 16 * (δ : ENNReal) ^ (-a₀)
            * ShadedBody.multiplicity mid (fun k => (Zρ k).toShadedBody) ∧
      (δ : ENNReal) ^ (2 * a₀) / 16
          ≤ (ShadedBody.fullness mid (fun k => (Zρ k).toShadedBody) : ENNReal) ∧
      (δ : ENNReal) ^ (2 * a₀) / 16 * (tAct.card : ENNReal) ≤ (mid.card : ENNReal) ∧
      (∀ k ∈ mid, pθ k ∈ tθAmb) := by
  classical
  obtain ⟨mid, hmid, hne, mu0, hmu0, hbr, hbridge, hfull₂, hcard₂, hinc, -⟩ :=
    regularizeOnFixedTree (E := E) hρ0 h.parent_subset pθ tθAmb hsk Zρ ⟨k₀, h.sel_mem⟩
      hlamP0 h.parent_fullness (a₀ := a₀) (δ := δ) hpoly
  exact ⟨mid, hmid, hne, mu0, hmu0, hbr, hbridge, hfull₂, hcard₂, hinc⟩

/-- **`B1` + `B3`: the two-scale factorization with the bridge discharged internally.**

This is `Kakeya.ml1Boot.isTwoScaleFactors_of_two` with its `hbridge` binder *removed*: the
middle active support is produced here by `Kakeya.ml1Boot.regularizeOnFixedTree`, and the
multiplicity bridge that the composition needs is that regularization's own certificate.

The second Lemma 5.11 application is supplied as `h₂`, quantified over the regularized middle
support — which is the correct order: the construction, not the caller, chooses `mid`, and the
second application is itself an existence theorem over families.  Feeding `mid` (and not the
zero-extended ambient middle family) into `h₂` is invariant §2.1: no empty zero-extended tube
enters a density-normalized step.

The total loss is `L₁ · (16 δ ^ (-a₀)) · L₂`, paid once. -/
theorem exists_isTwoScaleFactors_of_regularized [Nontrivial E] {τ θ : NNReal} (hτ0 : 0 < τ)
    {c₁ L₁ : ENNReal} {amb act : Finset ι} {V : ι → ShadedTube σ E}
    {tτAmb : Finset κ} {Vτ : κ → Tube τ E} {pτ : ι → κ}
    {act' : Finset ι} {Z' : ι → ShadedTube σ E}
    {tAct₁ : Finset κ} {Zτ : κ → ShadedTube τ E} {kF : κ} {lamP₁ lamF : NNReal}
    {tθAmb : Finset lc} {Vθ : lc → Tube θ E} {pθ : κ → lc}
    (hsk₁ : ∀ i ∈ amb, pτ i ∈ tτAmb) (hsk₂ : ∀ k ∈ tτAmb, pθ k ∈ tθAmb)
    (h₁ : IsOneScaleSelected c₁ L₁ amb act V tτAmb Vτ pτ act' Z' tAct₁ Zτ kF lamP₁ lamF)
    (hlamP0 : 0 < lamP₁) {a₀ : ℝ} {δ : NNReal}
    (hpoly : (δ : ENNReal) ^ a₀ ≤ (lamP₁ : ENNReal))
    (h₂ : ∀ mid ⊆ tAct₁, mid.Nonempty →
      (δ : ENNReal) ^ (2 * a₀) / 16
          ≤ (ShadedBody.fullness mid (fun k => (Zτ k).toShadedBody) : ENNReal) →
      (∀ k ∈ mid, pθ k ∈ tθAmb) →
      ∃ (c₂ L₂ : ENNReal) (mid' : Finset κ) (Zτ' : κ → ShadedTube τ E)
        (tAct₂ : Finset lc) (Zθ : lc → ShadedTube θ E) (lM : lc) (lamP₂ lamM : NNReal),
        IsOneScaleSelected c₂ L₂ tτAmb mid (zeroExtend mid Vτ Zτ) tθAmb Vθ pθ
          mid' Zτ' tAct₂ Zθ lM lamP₂ lamM) :
    ∃ (Lfact Lcard : ENNReal) (Ym : κ → ShadedTube τ E) (lamM : NNReal)
      (lM : lc) (tAct₂ : Finset lc) (Zθ : lc → ShadedTube θ E) (lamP₂ : NNReal),
      IsTwoScaleFactors Lfact Lcard amb V tτAmb Vτ pτ tθAmb Vθ pθ
        kF (selectedShade act' V Z') lamF lM Ym lamM tAct₂ Zθ lamP₂ := by
  classical
  obtain ⟨mid, hmid, hne, mu0, hmu0, -, hbridge, hfull₂, -, hinc⟩ :=
    exists_regularizedMid_bridge (E := E) hτ0 h₁ pθ tθAmb hsk₂ hlamP0 hpoly
  obtain ⟨c₂, L₂, mid', Zτ', tAct₂, Zθ, lM, lamP₂, lamM, h₂'⟩ :=
    h₂ mid hmid hne hfull₂ hinc
  refine ⟨L₁ * (16 * (δ : ENNReal) ^ (-a₀)) * L₂,
    ((fibre amb pτ kF).card : ENNReal) * ((fibre tτAmb pθ lM).card : ENNReal)
      * (tAct₂.card : ENNReal),
    selectedShade mid' (zeroExtend mid Vτ Zτ) Zτ', lamM, lM, tAct₂, Zθ, lamP₂, ?_⟩
  refine isTwoScaleFactors_of_two hsk₁ hsk₂ h₁ hmid hbridge h₂' ?_
  have hamb : 1 ≤ (amb.card : ENNReal) := by
    obtain ⟨i, hi⟩ := h₁.sel_nonempty
    have : (1 : ℕ) ≤ amb.card :=
      Finset.card_pos.mpr ⟨i, (Finset.mem_filter.mp hi).1⟩
    exact_mod_cast this
  calc ((fibre amb pτ kF).card : ENNReal) * ((fibre tτAmb pθ lM).card : ENNReal)
        * (tAct₂.card : ENNReal)
      = (((fibre amb pτ kF).card : ENNReal) * ((fibre tτAmb pθ lM).card : ENNReal)
          * (tAct₂.card : ENNReal)) * 1 := (mul_one _).symm
    _ ≤ (((fibre amb pτ kF).card : ENNReal) * ((fibre tτAmb pθ lM).card : ENNReal)
          * (tAct₂.card : ENNReal)) * (amb.card : ENNReal) := by gcongr

/-- **The bridge, with the density parameter as an `ℝ≥0`.**

`Kakeya.ml1Boot.exists_regularizedMid_bridge` returns its density parameter in `ℝ≥0∞`, whereas
the one-scale step `Kakeya.ml1Boot.exists_isOneScaleSelected_of_dens` takes it in `ℝ≥0`.  The
conversion is not bookkeeping: it needs the *upper* half of the bracket to see that the
parameter is finite.  Since a shading is contained in its carrier and a tube has positive
finite carrier volume, `2⁻¹ μ₀ |T| ≤ |Y(T)| ≤ |T|` forces `μ₀ ≤ 2`.

The output is stated in exactly the shape the next one-scale step consumes, at `C_d = 2`. -/
theorem exists_regularizedMid_bridge_nnreal [Nontrivial E] (hρ0 : 0 < ρ)
    {c L : ENNReal} {amb act : Finset ι} {V : ι → ShadedTube σ E}
    {tAmb : Finset κ} {Vρ : κ → Tube ρ E} {p : ι → κ}
    {act' : Finset ι} {Z' : ι → ShadedTube σ E}
    {tAct : Finset κ} {Zρ : κ → ShadedTube ρ E} {k₀ : κ} {lamP lamF : NNReal}
    (h : IsOneScaleSelected c L amb act V tAmb Vρ p act' Z' tAct Zρ k₀ lamP lamF)
    (pθ : κ → lc) (tθAmb : Finset lc) (hsk : ∀ k ∈ tAmb, pθ k ∈ tθAmb)
    (hlamP0 : 0 < lamP) {a₀ : ℝ} {δ : NNReal}
    (hpoly : (δ : ENNReal) ^ a₀ ≤ (lamP : ENNReal)) :
    ∃ mid ⊆ tAct, mid.Nonempty ∧ ∃ mu0 : NNReal,
      (∀ k ∈ mid, ((2 : NNReal) : ENNReal)⁻¹ * (mu0 : ENNReal) * volume (Zρ k).carrier
          ≤ volume (Zρ k).shade) ∧
      ShadedBody.multiplicity tAct (fun k => (Zρ k).toShadedBody)
          ≤ 16 * (δ : ENNReal) ^ (-a₀)
            * ShadedBody.multiplicity mid (fun k => (Zρ k).toShadedBody) ∧
      (δ : ENNReal) ^ (2 * a₀) / 16
          ≤ (ShadedBody.fullness mid (fun k => (Zρ k).toShadedBody) : ENNReal) ∧
      (∀ k ∈ mid, pθ k ∈ tθAmb) := by
  classical
  obtain ⟨mid, hmid, hne, mu0, hmu0, hbr, hbridge, hfull₂, -, hinc⟩ :=
    exists_regularizedMid_bridge (E := E) hρ0 h pθ tθAmb hsk hlamP0 hpoly
  -- the upper half of the bracket makes `mu0` finite
  obtain ⟨k, hk⟩ := hne
  have hvol := tube_volume_pos_ne_top (E := E) hρ0 (Zρ k).toTube
  have hshade : volume (Zρ k).shade ≤ volume (Zρ k).carrier :=
    measure_mono (Zρ k).shade_subset
  have hle1 : ((2 : NNReal) : ENNReal)⁻¹ * mu0 ≤ 1 := by
    have hmul : ((2 : NNReal) : ENNReal)⁻¹ * mu0 * volume (Zρ k).carrier
        ≤ 1 * volume (Zρ k).carrier := by
      simpa [one_mul] using ((hbr k hk).1.trans hshade)
    have := ENNReal.div_le_div_right hmul (volume (Zρ k).carrier)
    rwa [ENNReal.mul_div_cancel_right hvol.1.ne' hvol.2,
      ENNReal.mul_div_cancel_right hvol.1.ne' hvol.2] at this
  have hmu0top : mu0 ≠ ⊤ := by
    intro htop
    rw [htop] at hle1
    simp at hle1
  refine ⟨mid, hmid, ⟨k, hk⟩, mu0.toNNReal, ?_, hbridge, hfull₂, hinc⟩
  intro k' hk'
  simpa [ENNReal.coe_toNNReal hmu0top] using (hbr k' hk').1


end Bridge

end Regularize

end ml1Boot

end Kakeya

end
