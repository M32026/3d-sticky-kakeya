/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.RestrictShadeTransport

/-!
# Pinning a fibre-valued statistic by one common restriction

Two constants that the Step-3 slab layer requires to be **absolute** are, in
`ShadedPlank.reduction_to_slab_atTypicalAngle`, only bounded by the configuration-dependent `C`:

* the one-sided angle constant of `Kakeya.HasMaxPlankAngleBound`, which
  `Plank.slabMassDecomposition` and `Plank.localAngleConcentration_of_preassemblyData` both bind
  *before* the plank scale `a`;
* the constant-multiplicity constant `Cmult` of
  `Plank.slabwiseDensity_of_preassembly`'s
  `ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint))`.

Both are pinned by the same move: **restrict every shade to one common measurable set on which a
chosen statistic of the shade fibre is constant.**  A common restriction is not a lossy refinement
— `Plank.shadeFibre_restrictShade` says the fibre at a point of the restricting set is literally
unchanged — so the two-sided `Kakeya.IsTypicalPlankAngle` survives at the same constant and the same
stability scale (`Plank.isTypicalPlankAngle_restrictShade`), and only shade *mass* is spent.

This file supplies the missing half: the pigeonhole that produces the set, and the two
instantiations.

## The three declarations

* `Plank.exists_fibreClass_restriction` — for any `c : Finset ι → ℕ` whose value on every shade
  fibre of the union is `< N`, some level set `Plank.fibreClassSet s Y c j` retains at least a
  `1 / N` fraction of the total shade mass, and on the restricted union `c` is constantly `j`.
  The retention is stated multiplicatively, `∑ |Y i| ≤ N * ∑ |Y i ∩ E_j|`, which is the shape
  `ShadedBody.isCRefinement_of_isRefinement_of_sum_le` consumes.
* `Plank.exists_restriction_hasCConstantMultiplicity_two` — at `c F = Nat.log 2 F.card` and
  `N = Nat.log 2 s.card + 1` this gives a restricted family with
  `ShadedBody.HasCConstantMultiplicity s _ 2`: **the multiplicity constant becomes absolute.**
* `Plank.exists_restriction_maxPlankAngle_pinned` — at
  `c F = Nat.log 2 ⌊(b / a) * maxPlankAngle P F⌋₊` and `N = Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1` this
  gives an explicit angle `θ'` with `θ' ≤ maxPlankAngle P (fibre x) ≤ 4 * θ'` on the restricted
  union: **the one-sided angle constant becomes the absolute `4`**, at a dyadic angle `θ'`
  comparable to the original within the same factor.  No inverse and no division by an angle
  appears: the statistic is `(b / a) * θmax`, which lies in `[1, b / a]` because
  `Kakeya.maxPlankAngle_mem_Icc` floors the angle at `a / b` and caps it at `1`.

## What the retention costs, and why it is affordable

`N` is `Nat.log 2` of a cardinality, so the retained fraction is `1 / (log₂ |s| + 1)` in the
multiplicity case and `1 / (log₂ ⌊b/a⌋ + 1)` in the angle case.  Both are **sub-polynomial**: the
first because `Plank.card_le_of_windowed_essentiallyDistinct_shaded` bounds `|s|` by an absolute
power of `a⁻¹`, the second because `a ≤ b ≤ 1`.  A sub-polynomial loss is free against any positive
power of the scale, which is exactly the room
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallThickening` and
`Plank.routeAffordsCPower_of_strict` provide.

Nothing here depends on the value of the exponents `ε`, `ε'`, or on the field
`Kakeya.VeryNotSticky.TypicalAngleData.hCtyp`; the two statements are field-independent.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## The level sets of a fibre-valued statistic -/

/-- The set of points at which the chosen statistic `c` of the shade fibre takes the value `j`. -/
def fibreClassSet (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (c : Finset ι → ℕ) (j : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | c (Kakeya.shadeFibre s Y x) = j}

theorem mem_fibreClassSet {s : Finset ι} {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {c : Finset ι → ℕ} {j : ℕ} {x : EuclideanSpace ℝ (Fin 3)} :
    x ∈ fibreClassSet s Y c j ↔ c (Kakeya.shadeFibre s Y x) = j := Iff.rfl

/-- The level sets are measurable, because the shade-fibre map takes finitely many values with
measurable level sets (`Kakeya.measurable_fibreComp`). -/
theorem measurableSet_fibreClassSet (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (c : Finset ι → ℕ) (j : ℕ) :
    MeasurableSet (fibreClassSet s Y c j) :=
  Kakeya.measurable_fibreComp s Y c (measurableSet_singleton j)

/-- Every point of a restricted shading union has the pinned statistic. -/
theorem fibreClass_eq_of_mem_biUnion_restrict (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (c : Finset ι → ℕ) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ s, (ShadedBody.restrictShade (Y i)
      (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)).shade) :
    c (Kakeya.shadeFibre s Y x) = j :=
  mem_of_mem_biUnion_restrictShade hx

/-! ## The pigeonhole -/

/-- **One common restriction pins any fibre-valued statistic, at a `1 / N` mass cost.**

If `c` takes values `< N` on every shade fibre of the union, then some level set
`Plank.fibreClassSet s Y c j` retains at least a `1 / N` fraction of the total shade mass.  The
retention is stated as `∑ |Y i| ≤ N * ∑ |Y i ∩ E_j|`, the hypothesis shape of
`ShadedBody.isCRefinement_of_isRefinement_of_sum_le`. -/
theorem exists_fibreClass_restriction (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (c : Finset ι → ℕ) (N : ℕ) (hN : 0 < N)
    (hc : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, c (Kakeya.shadeFibre s Y x) < N) :
    ∃ j < N,
      (∑ i ∈ s, volume (Y i).shade) ≤ (N : ENNReal) *
        ∑ i ∈ s, volume (ShadedBody.restrictShade (Y i)
          (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)).shade := by
  classical
  -- each shade is covered by the `N` level sets
  have hcover : ∀ i ∈ s, volume (Y i).shade
      ≤ ∑ j ∈ Finset.range N, volume ((Y i).shade ∩ fibreClassSet s Y c j) := by
    intro i hi
    refine le_trans (measure_mono ?_) (measure_biUnion_finset_le (Finset.range N) _)
    intro x hx
    have hxU : x ∈ ⋃ i ∈ s, (Y i).shade := Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
    exact Set.mem_iUnion₂.mpr ⟨c (Kakeya.shadeFibre s Y x),
      Finset.mem_range.mpr (hc x hxU), hx, rfl⟩
  -- so the total mass is at most the sum over levels of the level masses
  set g : ℕ → ENNReal :=
    fun j => ∑ i ∈ s, volume ((Y i).shade ∩ fibreClassSet s Y c j) with hg
  have htot : (∑ i ∈ s, volume (Y i).shade) ≤ ∑ j ∈ Finset.range N, g j := by
    calc (∑ i ∈ s, volume (Y i).shade)
        ≤ ∑ i ∈ s, ∑ j ∈ Finset.range N, volume ((Y i).shade ∩ fibreClassSet s Y c j) :=
          Finset.sum_le_sum hcover
      _ = ∑ j ∈ Finset.range N, g j := Finset.sum_comm
  -- pick a level of maximal mass
  obtain ⟨j, hjmem, hjmax⟩ :=
    Finset.exists_max_image (Finset.range N) g ⟨0, Finset.mem_range.mpr hN⟩
  refine ⟨j, Finset.mem_range.mp hjmem, ?_⟩
  have hsum : ∑ j' ∈ Finset.range N, g j' ≤ (N : ENNReal) * g j := by
    have h := Finset.sum_le_card_nsmul (Finset.range N) g (g j) hjmax
    simpa [nsmul_eq_mul] using h
  refine htot.trans (hsum.trans (le_of_eq ?_))
  congr 1


/-! ## Instantiation 1: the multiplicity constant becomes absolute -/

/-- **One common restriction makes the constant-multiplicity constant absolute.**

Pigeonholing on the dyadic class `Nat.log 2` of the fibre cardinality gives a level set on which
the pointwise multiplicity varies by a factor `< 2`, hence a restricted family with
`ShadedBody.HasCConstantMultiplicity s _ 2`, at a mass cost of `Nat.log 2 s.card + 1`.

This is what `Plank.slabwiseDensity_of_preassembly`'s
`ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint))` wants with `Cmult` absolute and
`εint = 0`: the incoming `C` of `ShadedPlank.reduction_to_slab_atTypicalAngle` is not used at all,
so the `C`-power the route pays for `Cmult` drops to `C ^ 0`.

The hypothesis `ShadedBody.HasCConstantMultiplicity s Y C` is *not* needed: the pigeonhole is
unconditional, and the incoming constant only affects how much mass a *sharper* choice of `N` would
save. -/
theorem exists_restriction_hasCConstantMultiplicity_two (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∃ (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G),
      (∑ i ∈ s, volume (Y i).shade)
          ≤ ((Nat.log 2 s.card + 1 : ℕ) : ENNReal) *
            ∑ i ∈ s, volume (ShadedBody.restrictShade (Y i) G hG).shade ∧
        ShadedBody.HasCConstantMultiplicity s
          (fun i => ShadedBody.restrictShade (Y i) G hG) 2 := by
  classical
  set c : Finset ι → ℕ := fun F => Nat.log 2 F.card with hc_def
  set N : ℕ := Nat.log 2 s.card + 1 with hN_def
  have hN : 0 < N := Nat.succ_pos _
  have hclt : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, c (Kakeya.shadeFibre s Y x) < N := by
    intro x _
    have hsub : (Kakeya.shadeFibre s Y x).card ≤ s.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact Nat.lt_succ_of_le (Nat.log_mono_right hsub)
  obtain ⟨j, _hj, hmass⟩ := exists_fibreClass_restriction s Y c N hN hclt
  refine ⟨fibreClassSet s Y c j, measurableSet_fibreClassSet s Y c j, hmass, ?_⟩
  -- on the restricted union every fibre has the same dyadic class, so multiplicities differ by < 2
  intro x hx y hy
  have hxG : x ∈ fibreClassSet s Y c j := mem_of_mem_biUnion_restrictShade hx
  have hyG : y ∈ fibreClassSet s Y c j := mem_of_mem_biUnion_restrictShade hy
  have hxf : Kakeya.shadeFibre s (fun i => ShadedBody.restrictShade (Y i)
      (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)) x
      = Kakeya.shadeFibre s Y x :=
    shadeFibre_restrictShade s Y _ _ hxG
  have hyf : Kakeya.shadeFibre s (fun i => ShadedBody.restrictShade (Y i)
      (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)) y
      = Kakeya.shadeFibre s Y y :=
    shadeFibre_restrictShade s Y _ _ hyG
  -- both fibres are nonempty
  have hxne : (Kakeya.shadeFibre s Y x).card ≠ 0 := by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    refine Finset.card_ne_zero_of_mem (a := i) ?_
    exact (Kakeya.mem_shadeFibre s Y x i).mpr ⟨hi, hxi.1⟩
  have hyne : (Kakeya.shadeFibre s Y y).card ≠ 0 := by
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
    refine Finset.card_ne_zero_of_mem (a := i) ?_
    exact (Kakeya.mem_shadeFibre s Y y i).mpr ⟨hi, hyi.1⟩
  -- `2 ^ j ≤ card ≤ 2 ^ (j+1) - 1` on both sides
  have hxlt : (Kakeya.shadeFibre s Y x).card < 2 ^ (j + 1) := by
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Kakeya.shadeFibre s Y x).card
    rwa [show Nat.log 2 (Kakeya.shadeFibre s Y x).card = j from hxG] at h
  have hyge : 2 ^ j ≤ (Kakeya.shadeFibre s Y y).card := by
    have h := Nat.pow_log_le_self 2 hyne
    rwa [show Nat.log 2 (Kakeya.shadeFibre s Y y).card = j from hyG] at h
  have hnat : (Kakeya.shadeFibre s Y x).card ≤ 2 * (Kakeya.shadeFibre s Y y).card := by
    calc (Kakeya.shadeFibre s Y x).card ≤ 2 ^ (j + 1) - 1 := Nat.le_sub_one_of_lt hxlt
      _ ≤ 2 ^ (j + 1) := Nat.sub_le _ _
      _ = 2 * 2 ^ j := by ring
      _ ≤ 2 * (Kakeya.shadeFibre s Y y).card := Nat.mul_le_mul_left 2 hyge
  have : (ShadedBody.pointwiseMultiplicity s
      (fun i => ShadedBody.restrictShade (Y i)
        (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)) x : ℝ≥0)
      ≤ 2 * (ShadedBody.pointwiseMultiplicity s
        (fun i => ShadedBody.restrictShade (Y i)
          (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)) y : ℝ≥0) := by
    have hxc : ShadedBody.pointwiseMultiplicity s
        (fun i => ShadedBody.restrictShade (Y i)
          (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)) x
        = (Kakeya.shadeFibre s Y x).card := by
      rw [← hxf]; rfl
    have hyc : ShadedBody.pointwiseMultiplicity s
        (fun i => ShadedBody.restrictShade (Y i)
          (fibreClassSet s Y c j) (measurableSet_fibreClassSet s Y c j)) y
        = (Kakeya.shadeFibre s Y y).card := by
      rw [← hyf]; rfl
    rw [hxc, hyc]
    exact_mod_cast hnat
  exact this

/-! ## Instantiation 2: the one-sided angle constant becomes absolute -/

/-- **One common restriction pins the maximal plank angle to a dyadic value, at the absolute
constant `2`.**

Pigeonholing on the dyadic class of the *dimensionless* statistic `(b / a) * maxPlankAngle P F` —
which lies in `[1, b / a]` because `Kakeya.maxPlankAngle_mem_Icc` floors the angle at `a / b` and
caps it at `1`, so no inverse and no division by an angle is ever formed — produces an explicit
angle `θ' = (a / b) * 2 ^ j` with

```
θ' ≤ maxPlankAngle P (fibre x) ≤ 2 * θ'
```

at every point of the restricted union.  In particular
`Kakeya.HasMaxPlankAngleBound s _ P θ' 2` holds with the **absolute** constant `2`, which is the
form `Plank.slabMassDecomposition` and `Plank.localAngleConcentration_of_preassemblyData` need,
both of them binding that constant before the plank scale `a`.

The mass cost is `Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1`, sub-polynomial in `a⁻¹`.

The lower bound `θ' ≤ maxPlankAngle` is returned as well: it is what a consumer needs to know that
the dyadic angle is not smaller than the original by more than the same factor `2`, so that the
radius `θ' * b` is comparable to `θ * b`. -/
theorem exists_restriction_maxPlankAngle_pinned {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha : 0 < a) (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) :
    ∃ (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G) (θ' : ℝ≥0),
      0 < θ' ∧
      (∑ i ∈ s, volume (Y i).shade)
          ≤ ((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1 : ℕ) : ENNReal) *
            ∑ i ∈ s, volume (ShadedBody.restrictShade (Y i) G hG).shade ∧
        Kakeya.HasMaxPlankAngleBound s (fun i => ShadedBody.restrictShade (Y i) G hG) P θ' 2 ∧
        (∀ x ∈ ⋃ i ∈ s, (ShadedBody.restrictShade (Y i) G hG).shade,
          θ' ≤ Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)) := by
  classical
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hbne : (b : ℝ≥0) ≠ 0 := hb.ne'
  set R : ℝ≥0 := b / a with hR_def
  have hRinv : R * (a / b) = 1 := by rw [hR_def]; field_simp
  set c : Finset ι → ℕ := fun F => Nat.log 2 ⌊R * Kakeya.maxPlankAngle P F⌋₊ with hc_def
  set N : ℕ := Nat.log 2 ⌊(R : ℝ≥0)⌋₊ + 1 with hN_def
  have hN : 0 < N := Nat.succ_pos _
  have hfibre_ne : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, (Kakeya.shadeFibre s Y x).Nonempty := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨i, (Kakeya.mem_shadeFibre s Y x i).mpr ⟨hi, hxi⟩⟩
  have hclt : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, c (Kakeya.shadeFibre s Y x) < N := by
    intro x hx
    obtain ⟨_, hle1⟩ := Kakeya.maxPlankAngle_mem_Icc P (hfibre_ne x hx)
    have hmul : R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) ≤ R := by
      calc R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) ≤ R * 1 := by gcongr
        _ = R := mul_one R
    rw [hc_def, hN_def]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_mono hmul))
  obtain ⟨j, _hj, hmass⟩ := exists_fibreClass_restriction s Y c N hN hclt
  set G : Set (EuclideanSpace ℝ (Fin 3)) := fibreClassSet s Y c j with hG_def
  set hG : MeasurableSet G := measurableSet_fibreClassSet s Y c j with hhG
  set θ' : ℝ≥0 := (a / b) * 2 ^ j with hθ'_def
  -- the two-sided pinning, proved once
  have key : ∀ x ∈ ⋃ i ∈ s, (ShadedBody.restrictShade (Y i) G hG).shade,
      θ' ≤ Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) ∧
        Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) ≤ 2 * θ' := by
    intro x hx
    have hxG : x ∈ G := mem_of_mem_biUnion_restrictShade hx
    have hxU : x ∈ ⋃ i ∈ s, (Y i).shade := mem_biUnion_of_mem_biUnion_restrictShade hx
    obtain ⟨hlow, hhigh⟩ := Kakeya.maxPlankAngle_mem_Icc P (hfibre_ne x hxU)
    have hlogeq : Nat.log 2 ⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ = j := hxG
    have hone : (1 : ℝ≥0) ≤ R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) := by
      calc (1 : ℝ≥0) = R * (a / b) := hRinv.symm
        _ ≤ R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) := by gcongr
    have hfne : ⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ ≠ 0 := by
      have h1 : (1 : ℕ) ≤ ⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ :=
        Nat.le_floor (by exact_mod_cast hone)
      omega
    constructor
    · -- `θ' ≤ maxPlankAngle`
      have h := Nat.pow_log_le_self 2 hfne
      rw [hlogeq] at h
      have h' : ((2 : ℝ≥0)) ^ j
          ≤ (⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ : ℝ≥0) := by
        have : ((2 ^ j : ℕ) : ℝ≥0)
            ≤ (⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ : ℝ≥0) := by
          exact_mod_cast h
        simpa using this
      have hge : ((2 : ℝ≥0)) ^ j ≤ R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) :=
        h'.trans (Nat.floor_le (bot_le))
      calc θ' = (a / b) * (2 : ℝ≥0) ^ j := hθ'_def
        _ ≤ (a / b) * (R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)) := by gcongr
        _ = Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) := by
            rw [← mul_assoc, mul_comm (a / b) R, hRinv, one_mul]
    · -- `maxPlankAngle ≤ 2 * θ'`
      have hfl : ⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ < 2 ^ (j + 1) := by
        have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num)
          ⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊
        rwa [hlogeq] at h
      have hlt : R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x) ≤ (2 : ℝ≥0) ^ (j + 1) := by
        refine le_of_lt (lt_of_lt_of_le (Nat.lt_floor_add_one _) ?_)
        have hnat : (⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ : ℕ) + 1
            ≤ 2 ^ (j + 1) := hfl
        have : (((⌊R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)⌋₊ + 1 : ℕ)) : ℝ≥0)
            ≤ ((2 ^ (j + 1) : ℕ) : ℝ≥0) := by exact_mod_cast hnat
        simpa using this
      calc Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)
          = (a / b) * (R * Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)) := by
            rw [← mul_assoc, mul_comm (a / b) R, hRinv, one_mul]
        _ ≤ (a / b) * (2 : ℝ≥0) ^ (j + 1) := by gcongr
        _ = 2 * θ' := by rw [hθ'_def]; ring
  refine ⟨G, hG, θ', by rw [hθ'_def]; positivity, hmass, ?_, fun x hx => (key x hx).1⟩
  intro x hx
  have hxG : x ∈ G := mem_of_mem_biUnion_restrictShade hx
  have hxf : Kakeya.shadeFibre s (fun i => ShadedBody.restrictShade (Y i) G hG) x
      = Kakeya.shadeFibre s Y x := shadeFibre_restrictShade s Y G hG hxG
  rw [hxf]
  exact (key x hx).2


/-! ## Both pigeonholes at once -/

/-- **Both constants the Step-3 slab layer needs absolute, from one pair of common restrictions.**

Composing `Plank.exists_restriction_maxPlankAngle_pinned` with
`Plank.exists_restriction_hasCConstantMultiplicity_two` on the already-restricted family produces a
single family `Z` — every shade cut by the same two sets — with

* an explicit dyadic angle `θ'`, positive, with `Kakeya.HasMaxPlankAngleBound s Z P θ' 2` and
  `θ' ≤ Kakeya.maxPlankAngle P (fibre x)` at every point of the union of `Z`: the angle constant is
  the **absolute** `2` and the new angle is within a factor `2` of the old maximal angle;
* `ShadedBody.HasCConstantMultiplicity s Z 2`: the multiplicity constant is **absolute**;
* the mass retention `∑ |Y i| ≤ Nmass * ∑ |Z i|` with
  `Nmass = (Nat.log 2 ⌊b/a⌋₊ + 1) * (Nat.log 2 s.card + 1)`, which is sub-polynomial in `a⁻¹`;
* and, by `Plank.isTypicalPlankAngle_restrictShade` applied twice, the two-sided
  `Kakeya.IsTypicalPlankAngle` transported at the **same** constant and the **same** stability
  scale — the clause a lossy refinement would destroy.

Together these are items (a) and (b) of the Step-3 construction: after this, the only
configuration-dependent constant left in
`Plank.slabwiseDensity_of_preassembly`'s hypothesis block is the fullness `lamLower`, whose `C⁻¹`
is forced by the leaf's own `ShadedBody.IsCRefinement s Y'' s (bodies Y) C⁻¹` and is the
irreducible part of `Plank.routePower_floor`.

Nothing here mentions `ε`, `ε'` or `Kakeya.VeryNotSticky.TypicalAngleData.hCtyp`. -/
theorem exists_restriction_absoluteConstants {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (ha : 0 < a) (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) :
    ∃ (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ' : ℝ≥0),
      0 < θ' ∧
      (∀ i, (Z i).shade ⊆ (Y i).shade) ∧
      (∀ i, (Z i).toConvexSpaceBody = (Y i).toConvexSpaceBody) ∧
      (∑ i ∈ s, volume (Y i).shade)
          ≤ (((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1) * (Nat.log 2 s.card + 1) : ℕ) : ENNReal) *
            ∑ i ∈ s, volume (Z i).shade ∧
        Kakeya.HasMaxPlankAngleBound s Z P θ' 2 ∧
        (∀ x ∈ ⋃ i ∈ s, (Z i).shade, θ' ≤ Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Y x)) ∧
        ShadedBody.HasCConstantMultiplicity s Z 2 ∧
        (∀ {θ Cθ A : ℝ≥0}, Kakeya.IsTypicalPlankAngle s Y P θ Cθ A →
          Kakeya.IsTypicalPlankAngle s Z P θ Cθ A) := by
  classical
  obtain ⟨G₁, hG₁, θ', hθ'pos, hmass₁, hangle, hlow⟩ :=
    exists_restriction_maxPlankAngle_pinned ha s Y P
  set Y₁ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => ShadedBody.restrictShade (Y i) G₁ hG₁ with hY₁
  obtain ⟨G₂, hG₂, hmass₂, hmult⟩ := exists_restriction_hasCConstantMultiplicity_two s Y₁
  refine ⟨fun i => ShadedBody.restrictShade (Y₁ i) G₂ hG₂, θ', hθ'pos, ?_, fun _ => rfl, ?_, ?_,
    ?_, hmult, ?_⟩
  · exact fun i => (Set.inter_subset_left).trans Set.inter_subset_left
  · -- mass: compose the two retentions
    calc (∑ i ∈ s, volume (Y i).shade)
        ≤ ((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1 : ℕ) : ENNReal) * ∑ i ∈ s, volume (Y₁ i).shade :=
          hmass₁
      _ ≤ ((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1 : ℕ) : ENNReal) *
            (((Nat.log 2 s.card + 1 : ℕ) : ENNReal) *
              ∑ i ∈ s, volume (ShadedBody.restrictShade (Y₁ i) G₂ hG₂).shade) := by
          gcongr
      _ = (((Nat.log 2 ⌊(b / a : ℝ≥0)⌋₊ + 1) * (Nat.log 2 s.card + 1) : ℕ) : ENNReal) *
            ∑ i ∈ s, volume (ShadedBody.restrictShade (Y₁ i) G₂ hG₂).shade := by
          rw [← mul_assoc]; push_cast; ring
  · -- the one-sided angle bound survives an arbitrary shrinking
    exact Kakeya.HasMaxPlankAngleBound.mono (Finset.Subset.refl s)
      (fun i _ => Set.inter_subset_left) hangle
  · -- the lower bound transports because the union only shrinks
    intro x hx
    exact hlow x (Set.iUnion₂_mono (fun i _ => Set.inter_subset_left) hx)
  · -- two-sided typicality survives both common restrictions
    intro θ Cθ A hty
    exact isTypicalPlankAngle_restrictShade s Y₁ P G₂ hG₂
      (isTypicalPlankAngle_restrictShade s Y P G₁ hG₁ hty)

end Plank

end
