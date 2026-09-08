/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef

/-!
# The `ε`-budget of `Kakeya.plankReduction`

`Kakeya.plankReduction` states all of its sub-polynomial losses as powers `a ^ (± ε)` of the single
public exponent `ε`, and its internal chain runs several independent sub-polynomial arguments.
The bookkeeping needed before that chain can be assembled is quantified after `η` and `ε` but
**before** the configuration.

* `Kakeya.exponent_budget` is the arithmetic of the `ε`-split.  The public `ε` is divided
  into six named positive pieces, one per sub-polynomial argument, and their sum is at most `ε`.

* `Kakeya.absorb_const_of_eps_split` replaces the small-scale threshold the chain used to need.
  Rather than dominating the uniform constant of GWZ Lemma 6.11 by a power of `a` — which forces
  `a ≤ a₀` for a threshold depending on that constant — the constant is carried as the witness's
  own uniform constant, and only the monotonicity of `x ↦ a ^ x` for `a < 1` is used.  The chain
  therefore holds for every `0 < a < 1`, with no threshold and no coarse branch.

`Kakeya.IsTypicalPlankAngle.mono_const`, `Kakeya.HasMaxPlankAngleBound.mono_const` and
`Kakeya.reserveStability_mono_const` are the monotonicities in the *constant* of the three angular
predicates; `Kakeya.IsTypicalPlankAngle.mono_scale` moves the stability scale and does not move
the constant.
-/

@[expose] public section

open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- The typical-angle constant is monotone: enlarging `C` weakens `ComparableScalars C x y`
in both directions, so it weakens the whole fibre predicate. -/
theorem IsTypicalPlankFibre.mono_const {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {P : ι → Plank a b hab hb1} {theta C₁ C₂ A : ℝ≥0} {F : Finset ι}
    (hC : C₁ ≤ C₂) (h : IsTypicalPlankFibre P theta C₁ A F) :
    IsTypicalPlankFibre P theta C₂ A F := by
  refine ⟨⟨h.1.1.trans (mul_le_mul_left hC (maxPlankAngle P F)),
    h.1.2.trans (mul_le_mul_left hC theta)⟩, ?_⟩
  intro t ht hcard
  exact ⟨(h.2 t ht hcard).1.trans (mul_le_mul_left hC (maxPlankAngle P t)),
    (h.2 t ht hcard).2.trans (mul_le_mul_left hC theta)⟩

/-- The one-sided angle bound is monotone in its constant: it says
`maxPlankAngle ≤ C · theta`, so enlarging `C` weakens it. -/
theorem HasMaxPlankAngleBound.mono_const {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {theta C₁ C₂ : ℝ≥0}
    (hC : C₁ ≤ C₂) (h : HasMaxPlankAngleBound s Y P theta C₁) :
    HasMaxPlankAngleBound s Y P theta C₂ := by
  intro x hx
  exact (h x hx).trans (mul_le_mul_left hC theta)

/-- The family-level form of `Kakeya.IsTypicalPlankFibre.mono_const`. -/
theorem IsTypicalPlankAngle.mono_const {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {theta C₁ C₂ A : ℝ≥0}
    (hC : C₁ ≤ C₂) (h : IsTypicalPlankAngle s Y P theta C₁ A) :
    IsTypicalPlankAngle s Y P theta C₂ A :=
  fun x hx => (h x hx).mono_const hC

/-- Both absorptions of a uniform constant `C` against the `ε`-split `ew = ea + er`, for
`0 < a < 1`.  No threshold on `a` is involved: the constant is carried along rather than
dominated by a power of `a`. -/
theorem absorb_const_of_eps_split (C : ℝ≥0) {a : ℝ≥0} (ha0 : 0 < a) (ha1 : a < 1)
    {ea er ew : ℝ} (her : 0 < er) (hew : ew = ea + er) :
    C⁻¹ * a ^ ew ≤ C⁻¹ * a ^ ea ∧ C * a ^ (-ea) ≤ C * a ^ (-ew) := by
  have h1 : a ^ ew ≤ a ^ ea := by
    refine NNReal.rpow_le_rpow_of_exponent_ge ha0 (le_of_lt ha1) ?_
    rw [hew]
    linarith
  have h2 : a ^ (-ea) ≤ a ^ (-ew) := by
    refine NNReal.rpow_le_rpow_of_exponent_ge ha0 (le_of_lt ha1) ?_
    linarith
  exact ⟨mul_le_mul_right h1 (C⁻¹), mul_le_mul_right h2 C⟩

/-- The constant of the reserve-scale fibre-stability clause is monotone: the clause is a
two-sided comparison `θ ≈_C maxPlankAngle`, so enlarging `C` weakens it. -/
theorem reserveStability_mono_const {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {θ C D : ℝ≥0} {kappa : ℝ} (hCD : C ≤ D)
    (h : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ shadeFibre s Y x,
      (plankReserveScale kappa a)⁻¹ * ((shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ C * maxPlankAngle P t ∧ maxPlankAngle P t ≤ C * θ) :
    ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ shadeFibre s Y x,
      (plankReserveScale kappa a)⁻¹ * ((shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ D * maxPlankAngle P t ∧ maxPlankAngle P t ≤ D * θ := by
  intro x hx t ht hcard
  exact ⟨(h x hx t ht hcard).1.trans (mul_le_mul_left hCD (maxPlankAngle P t)),
    (h x hx t ht hcard).2.trans (mul_le_mul_left hCD θ)⟩

/-- **The `ε`-budget of `Kakeya.plankReduction`.**

The public sub-polynomial exponent `ε` is split into six named positive pieces, one for each
independent sub-polynomial argument of the assembly: the typical-angle selection (`εangle`), the
constant-absorption gap of the representative step (`εrepr`), the good-cover box step (`εbox`),
the dense-ball step (`εball`), the Item 2 assembly (`εitem2`), and the sharp pigeonhole absorption
(`εsharp`).  Their sum is `3 * ε / 4 ≤ ε`, and the two partial sums the refinement outputs
actually consume are recorded as well. -/
theorem exponent_budget {ε εangle εrepr εbox εball εitem2 εsharp : ℝ} (hε : 0 < ε)
    (hangle : εangle = ε / 8) (hrepr : εrepr = ε / 8) (hbox : εbox = ε / 8)
    (hball : εball = ε / 8) (hitem2 : εitem2 = ε / 8) (hsharp : εsharp = ε / 8) :
    0 < εangle ∧ 0 < εrepr ∧ 0 < εbox ∧ 0 < εball ∧ 0 < εitem2 ∧ 0 < εsharp ∧
      εangle + εrepr + εbox + εball + εitem2 + εsharp ≤ ε ∧
      0 < εangle + εrepr ∧
      εangle + εrepr ≤ ε ∧
      εsharp + (εangle + εrepr) ≤ ε := by
  subst hangle; subst hrepr; subst hbox; subst hball; subst hitem2; subst hsharp
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

/-- **The dense-ball exponent ledger of Item 1.**

The arithmetic that fits the good-box/dense-box/dense-ball layer inside Item 1's budget
`a^{4η} · a^{ε}`.  Every quantity is read off the code.

Run `Kakeya.plankReduction_preassembly` at the shrunk rate `ε'`, so its internal rate satisfies
`4 * εint = ε'`, i.e. `εint = ε'/4`.  Then:

* the refined family's fullness is `lamLower = cLam · a^{ε'} · a^{η}` (the public fullness clause),
  so `exp(lamLower) = η + ε'`;
* the good-box threshold multiplies it by the discard rate `a^{εint}`, giving
  `exp(lamScale) = η + ε' + εint = η + 5ε'/4 =: ηL`;
* `Plank.denseBoxUnionEstimate_shiftedBox` contributes `a^{2 ηL} · lam` and `lam` is itself bounded
  below by `cLamBox · a^{ηL}`, so the total exponent is `3 · ηL`;
* the ball step of `Plank.denseBallCapture_of_denseBoxEstimate` costs only an absolute constant, no
  power of `a`.

So Item 1 needs `3 · (η + 5εwork/4) ≤ 4η + εwork`, which is exactly `11εwork/4 ≤ η`.

There is a **second** constraint, invisible to Item 1 but binding on the fullness and multiplicity
outputs: the final common restriction to the retained set `Gtot` costs one further factor `a^{εint}`
on top of the preassembly's own `a^{εwork}`, so those clauses come out at `εwork + εint = 5εwork/4`
and must still fit inside the public budget `a^{ε}`.  Hence `5εwork/4 ≤ ε` as well, which
`εwork = min ε (η/4)` does **not** give.

There is a **third** constraint, from Item 2.  The glued-index-set Item 2 endpoint outputs
`c2 · a^{4η} · a^{5 ε₂}`, i.e. it spends `5 ε₂` where `ε₂` is the rate it is run at, and
its input `Cuni⁻¹ · a^{ε₂} ≤ cAngle` forces `ε₂` to be at least the exponent of the available
`cAngle`.  The preassembly supplies `a^{εint} ≤ cAngle`; running the pipeline on the *restricted*
family `Yfinal` multiplies that by the Item 1 refinement coefficient, whose own rate is again
`a^{εint}`, so the usable angle constant is `≳ a^{2 εint}` and `ε₂ = 2 εint = εwork/2` is forced.
Item 2 therefore lands at `a^{4η} · a^{5εwork/2}` and needs `5εwork/2 ≤ ε`.

`εwork = min (2ε/5) (η/4)` gives all three: `5εwork/2 ≤ ε` (hence also `5εwork/4 ≤ ε`) from the
first argument, and `11εwork/4 ≤ 11η/16 ≤ η` from the second.

Shrinking `ε` is legitimate because every clause of `Kakeya.plankReduction`'s conclusion is
weakening in `ε`, and its constants are existentially bound after `η` and `ε`; the assembly
proves everything at `εwork` and then weakens, using `0 < a ≤ 1`. -/
theorem denseBall_exponent_budget {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ εwork : ℝ, 0 < εwork ∧ εwork ≤ ε ∧ εwork ≤ η / 4 ∧
      5 * εwork / 4 ≤ ε ∧ 5 * εwork / 2 ≤ ε ∧ 11 * εwork / 4 ≤ η ∧
      0 < η + 5 * εwork / 4 ∧
      3 * (η + 5 * εwork / 4) ≤ 4 * η + εwork := by
  have hle1 : min (2 * ε / 5) (η / 4) ≤ 2 * ε / 5 := min_le_left _ _
  have hle2 : min (2 * ε / 5) (η / 4) ≤ η / 4 := min_le_right _ _
  have hpos : 0 < min (2 * ε / 5) (η / 4) := lt_min (by linarith) (by linarith)
  exact ⟨min (2 * ε / 5) (η / 4), hpos, by linarith, hle2, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

/-- **The good-box threshold, in closed form.**

The threshold `Plank.goodBoxes_unionLocal_capture_of_trimmedSlabFamilies` selects at is

`lamScale = (2 C_mult)⁻¹ · a^{εint} · lamLower / (512 · Nov · c_tan)`,

and at the public fullness value `lamLower = cLamPre · a^{η + ε'}` with `4 · εint = ε'` it is
exactly `cLamBox · a^{η + 5ε'/4}` for the configuration-free constant

`cLamBox = (2 C_mult)⁻¹ · cLamPre / (512 · Nov · c_tan)`.

This is the `cLam · a^{ηL} ≤ lam` input of `Plank.denseBoxUnionEstimate_shiftedBox` at
`ηL = η + 5ε'/4`, and it holds with equality, so no slack is spent here. -/
theorem lamScale_eq {a Cmult cLamPre cTan : ℝ≥0} {Nov : ℕ} {η ε' εint : ℝ}
    (ha : 0 < a) (hεint : 4 * εint = ε') :
    (2 * Cmult)⁻¹ * a ^ εint * (cLamPre * a ^ (η + ε')) / (512 * (Nov : ℝ≥0) * cTan)
      = ((2 * Cmult)⁻¹ * cLamPre / (512 * (Nov : ℝ≥0) * cTan)) * a ^ (η + 5 * ε' / 4) := by
  have hexp : εint + (η + ε') = η + 5 * ε' / 4 := by
    have : εint = ε' / 4 := by linarith
    rw [this]; ring
  have hrpow : a ^ εint * a ^ (η + ε') = a ^ (η + 5 * ε' / 4) := by
    rw [← NNReal.rpow_add ha.ne', hexp]
  calc
    (2 * Cmult)⁻¹ * a ^ εint * (cLamPre * a ^ (η + ε')) / (512 * (Nov : ℝ≥0) * cTan)
        = ((2 * Cmult)⁻¹ * cLamPre / (512 * (Nov : ℝ≥0) * cTan)) *
            (a ^ εint * a ^ (η + ε')) := by
          field_simp
    _ = ((2 * Cmult)⁻¹ * cLamPre / (512 * (Nov : ℝ≥0) * cTan)) * a ^ (η + 5 * ε' / 4) := by
          rw [hrpow]

/-- The constant of `Kakeya.lamScale_eq` is positive, and is fixed before every
geometric datum: it involves only the preassembly constants `C_mult`, `cLamPre`, the slab overlap
`Nov` and the tangency constant `c_tan`. -/
theorem cLamBox_pos {Cmult cLamPre cTan : ℝ≥0} {Nov : ℕ}
    (hCmult : 0 < Cmult) (hcLamPre : 0 < cLamPre) (hNov : 1 ≤ Nov) (hcTan : 1 ≤ cTan) :
    0 < (2 * Cmult)⁻¹ * cLamPre / (512 * (Nov : ℝ≥0) * cTan) := by
  have hNov0 : (0 : ℝ≥0) < (Nov : ℝ≥0) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hNov
  have hcTan0 : (0 : ℝ≥0) < cTan := lt_of_lt_of_le zero_lt_one hcTan
  have hden : (0 : ℝ≥0) < 512 * (Nov : ℝ≥0) * cTan := by positivity
  have hnum : (0 : ℝ≥0) < (2 * Cmult)⁻¹ * cLamPre := by
    have h2C : (0 : ℝ≥0) < 2 * Cmult := by positivity
    have : (0 : ℝ≥0) < (2 * Cmult)⁻¹ := by
      simpa using inv_pos.mpr h2C
    exact mul_pos this hcLamPre
  exact div_pos hnum hden

end Kakeya

end
