/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.WindowPacking

/-!
# The ball-density reduction for `ShadedPlank.reduction_to_slab_atTypicalAngle`

Two independent increments, both aimed at the same leaf.

## 1. The final assembly (`reduction_to_slab_atTypicalAngle_of_ballDensity`)

The target statement verbatim, plus **one** hypothesis, proved: *there is a refinement `Y'` of
`Y''` on the unchanged index set `s`, with retention coefficient `r` and ball-density threshold
`t`, such that*

```
δ ^ ε' * a ^ ε * C ≤ r        and        δ ^ ε' * a ^ (4 η) * a ^ ε ≤ t.
```

No smallness threshold on `δ` is needed (`δthr = 1`) and `128 * ε ≤ ε'` is not used.

The point of this shape is that it is **literally the output shape of the tree's already proved
Step-3 machinery**: `Plank.slabwiseDensity_of_preassembly` returns a measurable `Gtot` with

* `ShadedBody.IsCRefinement s' (fun i => (Y' i).restrictShade Gtot) s' Y' ((256 Nov Cmult)⁻¹ a^εint)`
* the arbitrary-centre ball density at threshold `cBall · cLamBox² · a^(4η+εwork)` and dilation
  `Kakeya.plankReduction.ballDilation = 3 = redPlankTube.ballDilation`,

and `Plank.localDensity_of_denseBalls` returns the same pair.  So the residue of the leaf is
exactly *"run GWZ Step 3 at the prescribed angle `θ`"*, with the two numeric targets above.

## 2. The `δ`-to-`a` conversion (`exists_rpow_le_of_multiplicity`)

Every constant in the target is a power of the *auxiliary* scale `δ`, whereas every constant in
the Step-3 machinery is a power of the *plank* scale `a`, and only `δ ≤ a` is assumed.  That
mismatch is what earlier notes recorded as blocking the machinery route.  It is **not** a
mismatch: the multiplicity hypothesis bounds it.  Since

```
δ ^ (-η) ≤ µ(s, bodies Y) ≤ |s| ≤ Cwin · a ^ (-Dwin)
```

(the last step is `Plank.card_le_of_windowed_essentiallyDistinct_shaded`, whose constants are
absolute), one gets both

```
a ^ Dwin ≤ Cwin · δ ^ η                          (so `a` is small once `δ` is)
δ ^ (-ε) ≤ Cwin ^ (ε/η) · a ^ (-(Dwin · ε / η))   (so `C ≤ δ^(-ε)` is a *fixed* power of `a`)
```

with `Cwin = Plank.windowPackingConst = 1538 ^ 12` and `Dwin = Plank.windowPackingExp = 12`, both
absolute and both **explicit**.  Both conclusions are proved here.  The exponent `Dwin · ε / η` and
the constant `Cwin ^ (ε/η)` depend only on `ε`, `η` and absolute data, hence may be chosen *before*
the configuration — which is exactly the quantifier position the machinery's angle constant
occupies (`Cstab0` and `εs` of `Plank.localAngleConcentration_of_preassemblyData`).

With the explicit numbers, `a ^ 12 ≤ 1538 ^ 12 · δ ^ η`, i.e. `a ≤ 1538 · δ ^ (η/12)`, and
`C ≤ 1538 ^ (12 ε / η) · a ^ (-(12 ε / η))`.  So the machinery's angular exponent is forced to be
`εs = 12 ε / η`, and its budget `3 · ηL ≤ 4 η + εwork` (with `εs < ηL` and `εwork ≤ ε`) admits that
exactly when `12 ε / η < (4 η + ε)/3`, i.e. essentially when `ε < η ^ 2 / 9`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-! ## The `δ`-to-`a` conversion -/

/-- **The auxiliary scale `δ` is a bounded power of the plank scale `a`.**

The multiplicity hypothesis `δ ^ (-η) ≤ µ(s, bodies Y)` of
`ShadedPlank.reduction_to_slab_atTypicalAngle` is not just a lower bound on the multiplicity: since
the multiplicity of a family never exceeds its cardinality
(`ShadedBody.multiplicity_le_card`) and the cardinality of a windowed essentially distinct plank
family is at most `Cwin · a ^ (-Dwin)`
(`Plank.card_le_of_windowed_essentiallyDistinct_shaded`, absolute constants), it forces

```
δ ^ (-η) ≤ Cwin · a ^ (-Dwin),
```

whence the two displayed conclusions.  The first says `a → 0` as `δ → 0`, so a smallness threshold
on `δ` buys a smallness threshold on `a`.  The second says that the target's constant bound
`C ≤ δ ^ (-ε)` implies the *`a`-polynomial* bound `C ≤ Cwin ^ (ε/η) · a ^ (-(Dwin ε / η))`, in
which the exponent depends only on `ε`, `η` and the absolute `Dwin`.

`Cwin` and `Dwin` are the outermost existentials of
`Plank.card_le_of_windowed_essentiallyDistinct_shaded`; they see neither `η`, `ε` nor the
configuration. -/
theorem rpow_le_of_multiplicity
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1) {δ : ℝ≥0} {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ) (ha : 0 < a)
    (hwin : Plank.IsWindowedFamily s (ShadedPlank.planks Y))
    (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier))
    (hmult : (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y)) :
    a ^ Plank.windowPackingExp ≤ Plank.windowPackingConst * δ ^ η ∧
      (δ : ℝ≥0) ^ (-ε) ≤ Plank.windowPackingConst ^ (ε / η)
        * a ^ (-(Plank.windowPackingExp * ε / η)) := by
  -- Step 1: the ENNReal chain `δ ^ (-η) ≤ µ ≤ |s| ≤ Cwin · a ^ (-Dwin)`
  have hED' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      PrismNDim.IsEssentiallyDistinct (ShadedPlank.planks Y i).toPrismNDim
        (ShadedPlank.planks Y j).toPrismNDim := by
    intro i hi j hj hne
    have h := hED (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hne
    simpa [PrismNDim.IsEssentiallyDistinct, ShadedPlank.planks_carrier] using h
  have hcard : (s.card : ℝ≥0)
      ≤ Plank.windowPackingConst * a ^ (-Plank.windowPackingExp) :=
    Plank.card_le_windowPackingConst s (ShadedPlank.planks Y) ha hwin hED'
  have hchain : ((δ ^ (-η) : ℝ≥0) : ENNReal)
      ≤ ((Plank.windowPackingConst * a ^ (-Plank.windowPackingExp) : ℝ≥0) : ENNReal) := by
    have hcoe : ((δ ^ (-η) : ℝ≥0) : ENNReal) = (δ : ENNReal) ^ (-η) :=
      ENNReal.coe_rpow_of_ne_zero hδ.ne' _
    rw [hcoe]
    refine hmult.trans (le_trans (ShadedBody.multiplicity_le_card s _) ?_)
    exact_mod_cast hcard
  have hkey : (δ : ℝ≥0) ^ (-η)
      ≤ Plank.windowPackingConst * a ^ (-Plank.windowPackingExp) :=
    ENNReal.coe_le_coe.mp hchain
  -- Step 2: invert the two negative powers
  have hδη : (0 : ℝ≥0) < δ ^ η := NNReal.rpow_pos hδ
  have haD : (0 : ℝ≥0) < a ^ Plank.windowPackingExp := NNReal.rpow_pos ha
  have hkey' : ((δ : ℝ≥0) ^ η)⁻¹
      ≤ Plank.windowPackingConst * ((a : ℝ≥0) ^ Plank.windowPackingExp)⁻¹ := by
    rw [← NNReal.rpow_neg, ← NNReal.rpow_neg]
    exact hkey
  refine ⟨?_, ?_⟩
  · calc (a : ℝ≥0) ^ Plank.windowPackingExp
        = ((δ : ℝ≥0) ^ η) * ((((δ : ℝ≥0) ^ η)⁻¹) * a ^ Plank.windowPackingExp) := by
          field_simp
      _ ≤ ((δ : ℝ≥0) ^ η) * ((Plank.windowPackingConst
            * ((a : ℝ≥0) ^ Plank.windowPackingExp)⁻¹) * a ^ Plank.windowPackingExp) := by
          gcongr
      _ = Plank.windowPackingConst * δ ^ η := by
          field_simp
  · -- Step 3: raise `hkey` to the power `ε / η > 0`
    have hpow : ((δ : ℝ≥0) ^ (-η)) ^ (ε / η)
        ≤ (Plank.windowPackingConst * (a : ℝ≥0) ^ (-Plank.windowPackingExp)) ^ (ε / η) :=
      NNReal.rpow_le_rpow hkey (by positivity)
    have hlhs : ((δ : ℝ≥0) ^ (-η)) ^ (ε / η) = (δ : ℝ≥0) ^ (-ε) := by
      rw [← NNReal.rpow_mul]
      congr 1
      field_simp
    have hrhs : (Plank.windowPackingConst * (a : ℝ≥0) ^ (-Plank.windowPackingExp)) ^ (ε / η)
        = Plank.windowPackingConst ^ (ε / η)
          * a ^ (-(Plank.windowPackingExp * ε / η)) := by
      rw [NNReal.mul_rpow, ← NNReal.rpow_mul]
      congr 2
      field_simp
    rw [hlhs, hrhs] at hpow
    exact hpow

/-- The `∃`-packaged form of `ShadedPlank.rpow_le_of_multiplicity`, matching the shape of
`Plank.card_le_of_windowed_essentiallyDistinct_shaded`.  Both constants are the explicit
`Plank.windowPackingConst = 1538 ^ 12` and `Plank.windowPackingExp = 12`. -/
theorem exists_rpow_le_of_multiplicity :
    ∃ (Cwin : ℝ≥0) (Dwin : ℝ), 0 < Cwin ∧ 0 ≤ Dwin ∧
      ∀ {ι : Type*} (s : Finset ι) {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (Y : ι → ShadedPlank a b hab hb1) {η ε : ℝ}, 0 < η → 0 < ε →
        0 < δ → 0 < a →
        Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) →
        (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
        a ^ Dwin ≤ Cwin * δ ^ η ∧
          (δ : ℝ≥0) ^ (-ε) ≤ Cwin ^ (ε / η) * a ^ (-(Dwin * ε / η)) := by
  refine ⟨Plank.windowPackingConst, Plank.windowPackingExp, Plank.windowPackingConst_pos,
    Plank.windowPackingExp_nonneg, ?_⟩
  intro ι s δ a b hab hb1 Y η ε hη hε hδ ha hwin hED hmult
  exact rpow_le_of_multiplicity s Y hη hε hδ ha hwin hED hmult

/-- **The target's constant bound `C ≤ δ ^ (-ε)` is an `a`-polynomial bound whose exponent is
fixed before the configuration.**

`ShadedPlank.exists_rpow_le_of_multiplicity` composed with the target's own hypothesis
`C ≤ δ ^ (-ε)`.  The point is the quantifier position: `Cwin ^ (ε/η)` and `Dwin * ε / η` depend only
on `ε`, `η` and the two absolute constants of
`Plank.card_le_of_windowed_essentiallyDistinct_shaded`, so they may be chosen **before** the index
type, `a`, `b`, `δ`, `θ` and `C`.

That is exactly the quantifier position occupied by the angular constants of the tree's Step-3
engine — `Cθ` and `εs` of `Plank.localAngleConcentration_of_preassemblyData`, and `Cθ` of
`Kakeya.slabwiseDensity_of_outputs`, all of which sit before the `∃` that produces the Item 1
coefficient.  So the received account that the target's `δ`-polynomial constants "are not derivable"
from the machinery's `a`-polynomial ones is wrong in that direction: the *bound* is derivable, with
`εs := Dwin * ε / η`.  What remains is the size of that exponent, which must fit under the
`3 * ηL ≤ 4 * η + εwork` budget of `Kakeya.slabwiseDensity_of_outputs`. -/
theorem typicalAngleConst_le_rpow
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1) (C : ℝ≥0) {δ : ℝ≥0} {η ε : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (hδ : 0 < δ) (ha : 0 < a)
    (hwin : Plank.IsWindowedFamily s (ShadedPlank.planks Y))
    (hED : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier))
    (hmult : (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y))
    (hCδ : C ≤ δ ^ (-ε)) :
    C ≤ Plank.windowPackingConst ^ (ε / η)
      * a ^ (-(Plank.windowPackingExp * ε / η)) :=
  hCδ.trans (rpow_le_of_multiplicity s Y hη hε hδ ha hwin hED hmult).2

/-! ## The bridge to the tree's Step-3 output spelling -/

/-- **The obligation of `ShadedPlank.reduction_to_slab_atTypicalAngle_of_ballDensity`, from the
literal output spelling of the tree's Step-3 machinery.**

`Plank.localDensity_of_denseBalls` and `Plank.slabwiseDensity_of_preassembly` state Item 1 with the
ball radius written `((θ * b : ℝ≥0) : ℝ)` and the outer dilation
`Kakeya.plankReduction.ballDilation`, whereas `Section6Compat.lean` writes the radius
`((θ : ℝ) * (b : ℝ))` and the dilation `redPlankTube.ballDilation`.  Both spellings denote the same
real number and both dilations are `3`; this lemma does that conversion once, so that a producer
can discharge the obligation of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_ballDensity` by a single `exact`.

Nothing mathematical happens here. -/
theorem ballDensity_of_localDensityOutput
    (s : Finset ι) (Y'' Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ C r t δ' : ℝ≥0) {η ε ε' : ℝ}
    (hr : δ' ^ ε' * a ^ ε * C ≤ r)
    (ht : δ' ^ ε' * a ^ (4 * η) * a ^ ε ≤ t)
    (hCr : ShadedBody.IsCRefinement s Y' s Y'' r)
    (hitem : ∀ x : EuclideanSpace ℝ (Fin 3),
      ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
      (t : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)) ≤
        volume ((⋃ i ∈ s, (Y' i).shade) ∩
          Metric.closedBall x
            ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ)))) :
    ∃ (Y'0 : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (r0 t0 : ℝ≥0),
      ShadedBody.IsCRefinement s Y'0 s Y'' r0 ∧
      δ' ^ ε' * a ^ ε * C ≤ r0 ∧
      δ' ^ ε' * a ^ (4 * η) * a ^ ε ≤ t0 ∧
      (∀ x,
        ((⋃ i ∈ s, (Y'0 i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (t0 : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s, (Y'0 i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) := by
  refine ⟨Y', r, t, hCr, hr, ht, ?_⟩
  have hrad : ((θ * b : ℝ≥0) : ℝ) = ((θ : ℝ) * (b : ℝ)) := by push_cast; ring
  have hdil : ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))
      = ((redPlankTube.ballDilation : ℝ) * (θ : ℝ) * (b : ℝ)) := by
    simp [Kakeya.plankReduction.ballDilation, redPlankTube.ballDilation]
    ring
  intro x hmeet
  have h := hitem x (by rw [hrad]; exact hmeet)
  rw [hdil, hrad] at h
  exact h

/-! ## The final assembly -/

/-- **`ShadedPlank.reduction_to_slab_atTypicalAngle` modulo one refinement-with-ball-density.**

The target statement of `Section6Compat.lean` verbatim — same binders, same hypotheses, same
`128 * ε ≤ ε'`, same conclusion — with exactly one hypothesis inserted just before the conclusion,
and proved.  The inserted hypothesis asks for a refinement `Y'` of `Y''` on the unchanged index
set `s`, at retention coefficient `r` and with the arbitrary-centre ball density at threshold `t`,
subject to the two scalar inequalities

```
δ ^ ε' * a ^ ε * C ≤ r,        δ ^ ε' * a ^ (4 * η) * a ^ ε ≤ t.
```

`δthr = 1`: no smallness threshold is used, and neither is `128 * ε ≤ ε'`, the pairwise essential
distinctness, the windowedness, the cardinality bound, the multiplicity hypotheses or the
typical-angle hypothesis.  Those are precisely the hypotheses a producer of the inserted clause
needs; nothing is spent here.

The output takes `s' := s`, `Y' := Y'` and `c1 := δ ^ ε'`, which is the smallest value the clause
`c1⁻¹ ≤ δ ^ (-ε')` permits — every other clause is hardest there, so no generality is lost.

The two inequalities are exactly matched by the tree's proved Step-3 outputs: with
`r = (256 · Nov · Cmult)⁻¹ · a ^ εint` and `t = cBall · cLamBox ^ 2 · a ^ (4η + εwork)`, as
returned by `Plank.slabwiseDensity_of_preassembly` and `Plank.localDensity_of_denseBalls`, both of
which are stated with *all* of `Cmult, cLamBox, Nov, η, εwork, εint` bound after the
configuration. -/
theorem reduction_to_slab_atTypicalAngle_of_ballDensity :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (r t : ℝ≥0),
        ShadedBody.IsCRefinement s Y' s Y'' r ∧
        δ ^ ε' * a ^ ε * C ≤ r ∧
        δ ^ ε' * a ^ (4 * η) * a ^ ε ≤ t ∧
        (∀ x,
          ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
          (t : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ))) ≤
            volume ((⋃ i ∈ s, (Y' i).shade) ∩
              Metric.closedBall x (redPlankTube.ballDilation * θ * b)))) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' _hgap Ccard D
  classical
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro ι s δ a b hab hb1 Y θ _hθ1 C Y'' hδ hδa ha1 _hδthr _hwin hfull _hma _hmd _h2 _hcard
    hθlb hC1 _hCδ hYref _hYmult _htyp hmaxA hdata
  obtain ⟨Y', r, t, hCr, hr, ht, hitem⟩ := hdata
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hC0 : (C : ℝ≥0) ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  -- the index set is nonempty, because the fullness of the empty family is `0`
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · exfalso
      have hz : ShadedBody.fullness s (ShadedPlank.bodies Y) = 0 := by simp [hs]
      rw [hz] at hfull
      exact absurd (le_antisymm hfull bot_le) (NNReal.rpow_pos ha).ne'
    · exact hs
  have hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier := by
    obtain ⟨i0, hi0⟩ := hsne
    have hpos : 0 < volume ((ShadedPlank.bodies Y i0).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [show ((ShadedPlank.bodies Y i0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Y i0).carrier from rfl, ShadedPlank.volume_carrier (Y i0)]
      refine ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) (ENNReal.coe_pos.mpr ha).ne').ne'
        (ENNReal.coe_pos.mpr hb).ne'
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i =>
      volume ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (fun i _ => bot_le) hi0)
  refine ⟨s, Y', δ ^ ε', NNReal.rpow_pos hδ, hCr.1.trans hYref.1, hCr.1, ?_, ?_, ?_⟩
  · -- fullness retention: compose the two `c`-refinements and weaken the coefficient
    have hcomp : ShadedBody.IsCRefinement s Y' s (ShadedPlank.bodies Y) (C⁻¹ * r) :=
      hCr.trans hYref
    have hcoeff : (δ : ℝ≥0) ^ ε' * a ^ ε ≤ C⁻¹ * r := by
      calc (δ : ℝ≥0) ^ ε' * a ^ ε
          = C⁻¹ * ((δ : ℝ≥0) ^ ε' * a ^ ε * C) := by field_simp
        _ ≤ C⁻¹ * r := by gcongr
    exact ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcar (hcomp.mono hcoeff)
  · -- Item 1: the threshold `t` dominates `δ ^ ε' * a ^ (4η) * a ^ ε`
    intro x hmeet
    have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
    have hcoe : (((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
        = (((δ : ℝ≥0) ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η)
            * (a : ENNReal) ^ ε := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_ne_zero hane (4 * η), ENNReal.coe_rpow_of_ne_zero hane ε]
    have hle : (((δ : ℝ≥0) ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η)
        * (a : ENNReal) ^ ε ≤ (t : ENNReal) := by
      rw [← hcoe]
      exact ENNReal.coe_le_coe.mpr ht
    calc (((δ : ℝ≥0) ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ)))
        ≤ (t : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ))) := by gcongr
      _ ≤ _ := hitem x hmeet
  · rw [← NNReal.rpow_neg]

/-- **Drift tripwire: the ball-density obligation really does close
`ShadedPlank.reduction_to_slab_atTypicalAngle`.**

The hypothesis `H` is the target statement with its conclusion replaced by the ball-density
obligation, and the conclusion of this theorem is the target statement *verbatim* — copied from
`Section6Compat.lean`, with only `Type*` written as `Type u` so that the two occurrences share a
universe.

The obligation is allowed its own `δ`-threshold, exactly as the target is; the two thresholds are
combined with `min` (here the second one is `1`, since
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_ballDensity` needs none). -/
theorem reduction_to_slab_atTypicalAngle_of_ballDensityObligation.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    (∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (r t : ℝ≥0),
      ShadedBody.IsCRefinement s Y' s Y'' r ∧
      δ ^ ε' * a ^ ε * C ≤ r ∧
      δ ^ ε' * a ^ (4 * η) * a ^ ε ≤ t ∧
      (∀ x,
        ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (t : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s, (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))))) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * a ^ (4 * η) * a ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δthr₁, hpos₁, hle₁, hH⟩ := H hη hε hε' hgap Ccard D
  obtain ⟨δthr₂, hpos₂, hle₂, hmain⟩ :=
    reduction_to_slab_atTypicalAngle_of_ballDensity hη hε hε' hgap Ccard D
  refine ⟨min δthr₁ δthr₂, lt_min hpos₁ hpos₂, (min_le_left _ _).trans hle₁, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  exact hmain s Y θ hθ1 C Y'' hδ hδa ha1 (hthr.trans (min_le_right _ _)) hwin hfull hma hmd
    h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA
    (hH s Y θ hθ1 C Y'' hδ hδa ha1 (hthr.trans (min_le_left _ _)) hwin hfull hma hmd
      h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA)

end ShadedPlank

end
