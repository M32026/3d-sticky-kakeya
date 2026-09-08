/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PolynomialStabilityConcentration
public import Kakeya.DimensionThree.Plank.LocalDensity

/-!
# Item 1 of GWZ Lemma 6.13, instantiated on the preassembly data

`Plank.localDensity_of_denseBalls` is abstract in the per-box selection `(Dg, Gbox)`.  This module
supplies that selection from data of the shape `Kakeya.plankReduction_preassembly` returns,
using the concrete slab-local objects of the trimmed slab-local shading section below:

```
Small S = inSlabFamilyC Cset  Cang  s' P S
Large S = inSlabFamilyC Cset' Cang' s' P S
YS S i  = trimmedSlabShading Cset Cang s' P Y' S i
Uloc S  = smallSlabUnion Cset Cang s' P Y' S      (= ⋃ i ∈ Large S, (YS S i).shade)
```

The good-box layer is run at the *enlarged* constants: `Plank.goodBoxes_unionLocal_capture_of_
trimmedSlabFamilies` is instantiated with its `Cset`/`Cang` slots taken to be `Cset'`/`Cang'`, which
is what `Plank.mem_inSlabFamilyC_self` discharges, and consequently the grid window is
`Plank.slabBoxIndexFor b ⌈Cset'⌉₊`.

## The common overlap constant

Two different uniform overlap bounds meet here — the preassembly's *pointwise* bound on the small
slab unions and the *index* bound of `Plank.slab_index_overlap_le` on the enlarged families.  Both
hypotheses have the shape `….card ≤ Nov`, so the caller passes the single constant
`Nov = max Nov_pt Nov_idx` and weakens each by `Nat.le_max_left` / `Nat.le_max_right`.  Only an
absolute constant grows; no exponent is spent and no `#𝒮` appears.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## The trimmed slab-local shading

The Item 1 pipeline of GWZ Lemma 6.13 runs, slab by slab, on the *enlarged* controlled slab family
with its shades trimmed to the shading union of the *small* one.  This section names those two
objects and proves the handful of identities the instantiation needs, so that they are not
re-derived at each use site.

For a slab `S`:

* `Plank.smallSlabUnion Cset Cang s' P Y' S = ⋃ i ∈ inSlabFamilyC Cset Cang s' P S, (Y' i).shade`
  — this is the set the preassembly's pointwise slab-overlap clause is stated for;
* `Plank.trimmedSlabShading Cset Cang s' P Y' S i =`
  `ShadedBody.restrictShade (Y' i) (smallSlabUnion …)`
  — the trimmed shading, with the carrier untouched.

The two facts that make the trimming free where it matters are
`Plank.trimmedSlabShading_shade_eq_of_mem_small` (a small-family shade is unchanged) and
`Plank.biUnion_trimmed_eq_smallSlabUnion` (the trimmed *enlarged*-family union is again the small
union), the latter being `Plank.biUnion_trimmed_eq_smallUnion` specialised along
`Plank.inSlabFamilyC_mono`.

### The two slab-overlap constants

The Item 1 instantiation meets two genuinely different uniform overlap bounds:

* `Nov_pt`, from `Kakeya.plankReduction_preassembly`, bounds the *pointwise* overlap of the small
  slab-local shading unions — i.e. of `Plank.smallSlabUnion`, which by
  `Plank.biUnion_trimmed_eq_smallSlabUnion` is exactly the `Uloc S` of the pipeline.  It is what
  `Plank.volume_le_mul_volume_inter_of_localCapture` and `Plank.localDensity_of_denseBalls` consume.
* `Nov_idx`, from `Plank.slab_index_overlap_le Cset' Cang'`, bounds the *index* overlap of the
  enlarged families `Plank.inSlabFamilyC Cset' Cang'`.  It is what
  `Plank.goodBoxes_unionLocal_capture_of_trimmedSlabFamilies` consumes.

Both are fixed before the configuration, and both hypotheses have the shape `….card ≤ Nov`, which
is monotone in `Nov`.  So the assembly may run with the single constant `Nov := max Nov_pt Nov_idx`,
weakening each bound by `Nat.le_max_left` / `Nat.le_max_right`; no separate lemma is needed and no
`#𝒮` enters.  The capture constant is then `256 * Nov` with that common `Nov`.
-/

/-- **The shading union of the small controlled slab family.**  This is exactly the set whose
pointwise overlap `Kakeya.plankReduction_preassembly` bounds by `Nov`. -/
def smallSlabUnion {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ i ∈ inSlabFamilyC Cset Cang s' P S, (Y' i).shade

theorem measurableSet_smallSlabUnion {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1) :
    MeasurableSet (smallSlabUnion Cset Cang s' P Y' S) :=
  measurableSet_biUnion_shade _ Y'

/-- A member of the small family has its whole shade inside the small union. -/
theorem shade_subset_smallSlabUnion {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {Cset Cang : ℝ≥0} {s' : Finset ι} {P : ι → Plank a b hab hb1}
    {Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {S : Slab θ hθ1} {i : ι}
    (hi : i ∈ inSlabFamilyC Cset Cang s' P S) :
    (Y' i).shade ⊆ smallSlabUnion Cset Cang s' P Y' S := by
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩

/-- **The trimmed slab-local shading.**  Same carrier, shade cut to the small family's union. -/
def trimmedSlabShading {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1) (i : ι) :
    ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
  ShadedBody.restrictShade (Y' i) (smallSlabUnion Cset Cang s' P Y' S)
    (measurableSet_smallSlabUnion Cset Cang s' P Y' S)

@[simp] theorem trimmedSlabShading_shade {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1) (i : ι) :
    (trimmedSlabShading Cset Cang s' P Y' S i).shade
      = (Y' i).shade ∩ smallSlabUnion Cset Cang s' P Y' S := rfl

@[simp] theorem trimmedSlabShading_carrier {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1) (i : ι) :
    ((trimmedSlabShading Cset Cang s' P Y' S i).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
      = ((Y' i).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

/-- Trimming is invisible on the small family. -/
theorem trimmedSlabShading_shade_eq_of_mem_small
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {Cset Cang : ℝ≥0} {s' : Finset ι} {P : ι → Plank a b hab hb1}
    {Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {S : Slab θ hθ1} {i : ι}
    (hi : i ∈ inSlabFamilyC Cset Cang s' P S) :
    (trimmedSlabShading Cset Cang s' P Y' S i).shade = (Y' i).shade := by
  rw [trimmedSlabShading_shade]
  exact Set.inter_eq_left.mpr (shade_subset_smallSlabUnion hi)

/-- **The trimmed enlarged-family union is the small union.**  `Plank.biUnion_trimmed_eq_smallUnion`
specialised along `Plank.inSlabFamilyC_mono`; this is the `Uloc S` of the Item 1 pipeline. -/
theorem biUnion_trimmed_eq_smallSlabUnion
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang Cset' Cang' : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1)
    (hCset : Cset ≤ Cset') (hCang : Cang ≤ Cang') :
    (⋃ i ∈ inSlabFamilyC Cset' Cang' s' P S,
        (trimmedSlabShading Cset Cang s' P Y' S i).shade)
      = smallSlabUnion Cset Cang s' P Y' S :=
  biUnion_trimmed_eq_smallUnion (inSlabFamilyC Cset Cang s' P S)
    (inSlabFamilyC Cset' Cang' s' P S) Y'
    (trimmedSlabShading Cset Cang s' P Y' S)
    (smallSlabUnion Cset Cang s' P Y' S)
    (inSlabFamilyC_mono hCset hCang) rfl
    (fun i => trimmedSlabShading_shade Cset Cang s' P Y' S i)

/-- **A controlled slab family is a controlled slab family of itself.**

`Plank.inSlabFamilyC` conjoins membership of the ambient index set with two purely geometric
conditions on `V i` and `S`, so restricting the ambient set to the family itself changes nothing.
This is the `hfam` hypothesis of the good-box layer, which asks for membership relative to the
slab-local index set rather than to `s'`. -/
theorem mem_inSlabFamilyC_self {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    {Cset Cang : ℝ≥0} {s : Finset ι} {V : ι → Plank a b hab hb1} {S : Slab θ hθ1} {i : ι}
    (hi : i ∈ inSlabFamilyC Cset Cang s V S) :
    i ∈ inSlabFamilyC Cset Cang (inSlabFamilyC Cset Cang s V S) V S := by
  obtain ⟨-, hcar, hang⟩ := mem_inSlabFamilyC.mp hi
  exact mem_inSlabFamilyC.mpr ⟨hi, hcar, hang⟩

/-- **The carrier-volume hypothesis of the good-box layer, from carrier coherence.**

The refined shadings of `Kakeya.plankReduction_preassembly` have the plank carriers as their
carriers, and a plank carrier has volume exactly `8ab`; so the lower bound `8ab ≤ |carrier|`
the fullness step
needs holds with equality. -/
theorem eight_mul_le_volume_carrier_of_carrier_eq {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s' : Finset ι) (V : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hcar : ∀ i ∈ s', ((Y' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ∀ i ∈ s', 8 * (a : ENNReal) * (b : ENNReal) ≤ volume (Y' i).carrier := by
  intro i hi
  rw [hcar i hi, Prism3D.volume_carrier (V i)]
  simp

/-- The small union sits inside the global shading union. -/
theorem smallSlabUnion_subset {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ1) :
    smallSlabUnion Cset Cang s' P Y' S ⊆ ⋃ i ∈ s', (Y' i).shade := by
  refine Set.iUnion₂_subset fun i hi => ?_
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨i, inSlabFamilyC_subset hi, hx⟩

/-! ## Item 1 instantiated on the preassembly data -/

open scoped Classical in
/-- **The tangentiality hypothesis, on the concrete preassembly-shaped slab-local data.**

Every plank of the saturated family `T S sh q` has a point of its (trimmed) shade in the *middle
half* `Plank.halfSlabBox S b sh q`, and on the middle half tangential comparability is automatic:
`Plank.comparableScalars_of_mem_halfBox`.  So no tangential filter on the grid is needed, and the
`htan` hypothesis threaded through `Plank.goodBoxes_of_preassemblyData`,
`Plank.denseBallRegions_of_goodBoxes` and `Plank.slabwiseDensity_of_preassembly` is discharged here.

The only geometric input is the enlarged-family angle bound, which is part of
`Plank.mem_inSlabFamilyC`; `cTan` depends only on `Cang'` and is fixed before every geometric
datum. -/
theorem tangentiality_of_trimmedSlabFamilies (Cang' : ℝ≥0) (hCang' : 1 ≤ Cang') :
    ∃ cTan : ℝ≥0, 1 ≤ cTan ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (Cset Cang Cset' : ℝ≥0)
        (s' : Finset ι) (P : ι → Plank a b hab hb1)
        (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι),
        0 < a → 0 < b → a ≤ θ * b →
        (∀ i ∈ s', (Y' i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ S sh q, T S sh q = (inSlabFamilyC Cset' Cang' s' P S).filter
          (fun i => ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
            halfSlabBox S b sh q).Nonempty)) →
        ∀ S sh q, ∀ i ∈ T S sh q, Kakeya.ComparableScalars cTan
          (volume (((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2) := by
  obtain ⟨cTan, hcTan, htanlem⟩ := comparableScalars_of_mem_halfBox Cang' hCang'
  refine ⟨cTan, hcTan, ?_⟩
  intro a b θ hab hb1 hθ1 ι Cset Cang Cset' s' P Y' T ha hb haθb hshV hT S sh q i hi
  have hi_filter : i ∈ (inSlabFamilyC Cset' Cang' s' P S).filter
      (fun i => ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
        halfSlabBox S b sh q).Nonempty) := by
    simpa [hT S sh q] using hi
  have hi₁ : i ∈ inSlabFamilyC Cset' Cang' s' P S := (Finset.mem_filter.mp hi_filter).1
  have hx_ex : ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ halfSlabBox S b sh q).Nonempty :=
    (Finset.mem_filter.mp hi_filter).2
  obtain ⟨x, hxshade, hxhalf⟩ := hx_ex
  have hxYi : x ∈ (Y' i).shade := hxshade.1
  have hxVcar : x ∈ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    hshV i (inSlabFamilyC_subset hi₁) hxYi
  have hx_mid : x ∈ (((shiftedSlabBox S b sh q).toPrismNDim.dilation 2⁻¹).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa [halfSlabBox] using hxhalf
  exact htanlem (P i) hθ1 S sh q ha hb haθb
    (((mem_inSlabFamilyC (Cset := Cset') (Cang := Cang') (s := s') (V := P) (S := S)).mp hi₁).2.2)
    ⟨x, hxVcar, hx_mid⟩

open scoped Classical in
/-- **The angular concentration hypothesis, on the concrete preassembly-shaped slab-local data.**

`Plank.localAngleConcentration_trimmed_of_slabLocal_poly` instantiated at the trimmed shadings
`Plank.trimmedSlabShading` of every used slab, with its angular-stability input taken from the
*two-sided* typical-angle clause that `Kakeya.plankReduction_preassembly` returns, via
`Plank.localStability_of_isTypicalPlankAngle`.

This is the `hLAC` hypothesis of `Plank.slabwiseDensity_of_preassembly`, uniformly in the slab, the
shift, the box and in the good-box selection `Dg` (the concentration predicate does not constrain
`Dg` beyond the boxes it names, so it holds for every selection).

The stability constant is polynomial, `Cstab0 · a ^ (-ε_s)`, not the stop scale
`Kakeya.plankAngleScaleB a`; the exponent condition is `ε_s < ηL`, which the ledger satisfies with
room to spare (`ε_s = ε_int = ε_work/4` against `ηL = η + 5ε_work/4`).  `Ceta` depends only on `C`,
`Cstab0`, `ε_s` and `ηL`. -/
theorem localAngleConcentration_of_preassemblyData (C Cstab0 : ℝ≥0) (hC : 1 ≤ C)
    (hCstab0 : 1 ≤ Cstab0) {εs ηL : ℝ} (hεs : 0 < εs) (hlt : εs < ηL) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (Cset Cang Cset' Cang' A : ℝ≥0)
        (s' : Finset ι) (P : ι → Plank a b hab hb1)
        (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
        (Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι →
          ShadedBody (EuclideanSpace ℝ (Fin 3))),
        0 < a → a < 1 → 0 < b → 0 < θ → a ≤ θ * b → 2 ≤ A →
        Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset' →
        2 * Cang + 4 * C ≤ Cang' →
        (∀ i ∈ s', (Y' i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        Kakeya.HasMaxPlankAngleBound s' Y' P θ C →
        Kakeya.IsTypicalPlankAngle s' Y' P θ (Cstab0 * a ^ (-εs)) A →
        (∀ S sh q, T S sh q = (inSlabFamilyC Cset' Cang' s' P S).filter
          (fun i => ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
            halfSlabBox S b sh q).Nonempty)) →
        (∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).shade
          = (trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ halfSlabBox S b sh q) →
        ∀ (S : Slab θ hθ1) (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)),
          LocalAngleConcentration P θ gridShiftSet (Dg S) (T S) (Z S) Ceta ηL := by
  classical
  obtain ⟨Ceta, hCetapos, hLAC⟩ :=
    localAngleConcentration_trimmed_of_slabLocal_poly C Cstab0 hC hCstab0 hεs hlt
  refine ⟨Ceta, hCetapos, ?_⟩
  intro a b θ hab hb1 hθ1 ι Cset Cang Cset' Cang' A s' P Y' T Z
    ha ha1 hb hθ haθb hA hCset' hCang' hshV hmax htyp hT hZsh
  have hCstab0pos : (0 : ℝ≥0) < Cstab0 := lt_of_lt_of_le zero_lt_one hCstab0
  have ha_rpow : (0 : ℝ≥0) < a ^ (-εs) := NNReal.rpow_pos ha
  have hCstabpos : (0 : ℝ≥0) < Cstab0 * a ^ (-εs) := mul_pos hCstab0pos ha_rpow
  have hden : ((Cstab0 * a ^ (-εs : ℝ) : ℝ≥0) : ℝ) = (Cstab0 : ℝ) * (a : ℝ) ^ (-εs) := by
    rw [NNReal.coe_mul, NNReal.coe_rpow]
  intro S Dg
  refine hLAC (Cset := Cset) (Cang := Cang) (Cset' := Cset') (Cang' := Cang') (S := S)
    (s' := s') (V := P) (Y' := Y')
    (YS := trimmedSlabShading Cset Cang s' P Y' S)
    (T := T S) (Z := Z S) (Dg := Dg S) (A := (A : ℝ))
    ha ha1 hb hθ haθb ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact_mod_cast hA
  · exact hCset'
  · exact hCang'
  · exact hshV
  · exact hmax
  · intro x hx t ht hcard
    rw [← hden]
    exact localStability_of_isTypicalPlankAngle hCstabpos htyp x hx t ht hcard
  · intro i
    rw [trimmedSlabShading_shade]
    rfl
  · intro sh q
    exact hT S sh q
  · intro sh q i hi
    exact hZsh S sh q i hi

open scoped Classical in
/-- **The good-box selection, on the concrete preassembly-shaped slab-local data.**

`Plank.goodBoxes_unionLocal_capture_of_trimmedSlabFamilies` with every hypothesis discharged from
the preassembly outputs.  The threshold is unchanged,

`lamScale = (2 C_mult)⁻¹ a^{ε_int} · lamLower / (512 · Nov · c_tan)`,

and the returned capture is against the localized set
`Plank.goodBoxUnionLocal 𝒮 b (Plank.smallSlabUnion …) Dg`. -/
theorem goodBoxes_of_preassemblyData
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan Cset Cang Cset' Cang' Cmult lamLower : ℝ≥0) (εint : ℝ) (Nov : ℕ)
    (hcTan : 1 ≤ cTan) (hCset' : 1 ≤ Cset') (hCmult : 0 < Cmult) (hNov : 1 ≤ Nov)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hb1' : b ≤ 1)
    (hCsetLe : Cset ≤ Cset') (hCangLe : Cang ≤ Cang')
    (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒮 : Finset (Slab θ hθ1))
    (T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
    (Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ i ∈ s', ∃ S ∈ 𝒮, i ∈ inSlabFamilyC Cset Cang s' P S)
    (hoverlap : ∀ i ∈ s', (𝒮.filter fun S => i ∈ inSlabFamilyC Cset' Cang' s' P S).card ≤ Nov)
    (hshV : ∀ i ∈ s', (Y' i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hcarEq : ∀ i ∈ s', ((Y' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hT : ∀ S sh q, T S sh q = (inSlabFamilyC Cset' Cang' s' P S).filter
      (fun i => ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
        halfSlabBox S b sh q).Nonempty))
    (hZsh : ∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).shade
      = (trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ halfSlabBox S b sh q)
    (hZcar : ∀ S sh q, ∀ i ∈ T S sh q,
      ((Z S sh q i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ S sh q, ∀ i ∈ T S sh q, Kakeya.ComparableScalars cTan
      (volume (((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hfull : lamLower ≤ ShadedBody.fullness s' Y')
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint))) :
    ∃ Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ),
      (∀ S sh, Dg S sh ⊆ slabBoxIndexFor b ⌈(Cset' : ℝ)⌉₊) ∧
      (∀ S sh, ∀ q ∈ Dg S sh,
        b * ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan))
          ≤ ShadedBody.fullness (T S sh q) (Z S sh q)) ∧
      volume (⋃ i ∈ s', (Y' i).shade)
        ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩
            goodBoxUnionLocal 𝒮 b (smallSlabUnion Cset Cang s' P Y') Dg) := by
  classical
  obtain ⟨Dg, hDgsub, hDgfull, -, hcap⟩ :=
    goodBoxes_unionLocal_capture_of_trimmedSlabFamilies cTan Cset' Cang' Cmult lamLower εint Nov
      hcTan hCset' hCmult hNov ha hb hθ hb1' s' P Y'
      (trimmedSlabShading Cset Cang s' P Y') 𝒮
      (fun S => inSlabFamilyC Cset Cang s' P S)
      (fun S => inSlabFamilyC Cset' Cang' s' P S)
      (smallSlabUnion Cset Cang s' P Y') T Z
      (fun S _ => measurableSet_smallSlabUnion Cset Cang s' P Y' S)
      (fun S _ => inSlabFamilyC_subset)
      hcover
      (fun S _ => inSlabFamilyC_mono hCsetLe hCangLe)
      (fun S _ => inSlabFamilyC_subset)
      hoverlap
      (fun S _ i hi => shade_subset_smallSlabUnion hi)
      (fun S _ i hi => (trimmedSlabShading_shade_eq_of_mem_small hi).symm)
      (fun S _ i hi => by
        refine Set.Subset.trans ?_ (hshV i (inSlabFamilyC_subset hi))
        rw [trimmedSlabShading_shade]
        exact Set.inter_subset_left)
      (eight_mul_le_volume_carrier_of_carrier_eq s' P Y' hcarEq)
      (fun S _ i hi => mem_inSlabFamilyC_self hi)
      hT hZsh hZcar htan hfull hC
      (ShadedBody.volume_iUnion_shade_ne_top s' Y')
  exact ⟨Dg, hDgsub, hDgfull, hcap⟩

open scoped Classical in
/-- **The per-box dense-ball regions, chosen simultaneously for every selected good box.**

The angular concentration is supplied per slab as a hypothesis (the caller obtains it once from
`Plank.localAngleConcentration_trimmed_of_slabLocal` at the exponent `ηL`); its `θ0`, `Cstar`,
`Mtyp` are unpacked and fed box by box into `Plank.denseBall_of_goodBox`.

Off the selected triples the choice is `∅`, so the selection statement is a plain
`∀ S sh q, ∃ G, …` and `choose` applies.  The density threshold is
`cBall * cLamBox * cLamBox * a^(4η + εwork)`; no further power of `a` is spent. -/
theorem denseBallRegions_of_goodBoxes (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cBall : ℝ≥0, 0 < cBall ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (Cset Cang Cset' Cang' cLamBox lamScale : ℝ≥0) (η εwork ηL : ℝ)
        (s' : Finset ι) (P : ι → Plank a b hab hb1)
        (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒮 : Finset (Slab θ hθ1))
        (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
        (T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
        (Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι →
          ShadedBody (EuclideanSpace ℝ (Fin 3))),
        0 < a → a ≤ 1 → 0 < b → 0 < θ → 0 < ηL → 0 < cLamBox → a / b ≤ θ →
        3 * ηL ≤ 4 * η + εwork →
        cLamBox * a ^ ηL ≤ lamScale →
        Cset ≤ Cset' → Cang ≤ Cang' →
        (∀ S : Slab θ hθ1,
          LocalAngleConcentration P θ gridShiftSet (Dg S) (T S) (Z S) Ceta ηL) →
        (∀ i ∈ s', (Y' i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ S sh q, T S sh q = (inSlabFamilyC Cset' Cang' s' P S).filter
          (fun i => ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
            halfSlabBox S b sh q).Nonempty)) →
        (∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).shade
          = (trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ halfSlabBox S b sh q) →
        (∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).carrier = (P i).carrier) →
        (∀ S sh q, ∀ i ∈ T S sh q, Kakeya.ComparableScalars cTan
          (volume (((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ S sh, ∀ q ∈ Dg S sh,
          b * lamScale ≤ ShadedBody.fullness (T S sh q) (Z S sh q)) →
        ∃ Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) →
            Set (EuclideanSpace ℝ (Fin 3)),
          (∀ S sh q, MeasurableSet (Gbox S sh q)) ∧
          (∀ S ∈ 𝒮, ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh,
            Gbox S sh q ⊆ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) ∧
            volume (smallSlabUnion Cset Cang s' P Y' S ∩
                ((shiftedSlabBox S b sh q).carrier :
                  Set (EuclideanSpace ℝ (Fin 3))))
              ≤ 2 * volume ((smallSlabUnion Cset Cang s' P Y' S ∩
                ((shiftedSlabBox S b sh q).carrier :
                  Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q) ∧
            (∀ y ∈ Gbox S sh q, ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ thetaBall θ b c ∧
              ((cBall * cLamBox * cLamBox * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                  volume (thetaBall θ b c)
                ≤ volume (((smallSlabUnion Cset Cang s' P Y' S ∩
                    ((shiftedSlabBox S b sh q).carrier :
                      Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q) ∩
                  thetaBall θ b c))) := by
  classical
  obtain ⟨cBall, hcBall, hdb⟩ := denseBall_of_goodBox cTan Ceta hCeta
  refine ⟨cBall, hcBall, ?_⟩
  intro a b θ hab hb1 hθ1 ι Cset Cang Cset' Cang' cLamBox lamScale η εwork ηL s' P Y' 𝒮 Dg T Z
    ha ha1 hb hθ hηL hcLamBox hdivb h3ηL hlamScale hCsetLe hCangLe hLAC hshV hT hZsh hZcar
    htan hboxfull
  have hUloc : ∀ S : Slab θ hθ1,
      (⋃ i ∈ inSlabFamilyC Cset' Cang' s' P S,
          (trimmedSlabShading Cset Cang s' P Y' S i).shade)
        = smallSlabUnion Cset Cang s' P Y' S :=
    fun S => biUnion_trimmed_eq_smallSlabUnion Cset Cang Cset' Cang' s' P Y' S hCsetLe hCangLe
  choose θ0 Cstar Mtyp hprod hboxdata using hLAC
  have hsel : ∀ (S : Slab θ hθ1) (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ),
      ∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
        (S ∈ 𝒮 → sh ∈ gridShiftSet → q ∈ Dg S sh →
          G ⊆ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
          volume (smallSlabUnion Cset Cang s' P Y' S ∩
              ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
            ≤ 2 * volume ((smallSlabUnion Cset Cang s' P Y' S ∩
              ((shiftedSlabBox S b sh q).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) ∩ G) ∧
          (∀ y ∈ G, ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ thetaBall θ b c ∧
            ((cBall * cLamBox * cLamBox * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                volume (thetaBall θ b c)
              ≤ volume (((smallSlabUnion Cset Cang s' P Y' S ∩
                  ((shiftedSlabBox S b sh q).carrier :
                    Set (EuclideanSpace ℝ (Fin 3)))) ∩ G) ∩ thetaBall θ b c))) := by
    intro S sh q
    by_cases hmem : S ∈ 𝒮 ∧ sh ∈ gridShiftSet ∧ q ∈ Dg S sh
    · obtain ⟨hS, hsh, hq⟩ := hmem
      obtain ⟨hθ0lb, hθ01, hθθ0, hconc⟩ := hboxdata S sh hsh q hq
      obtain ⟨G, hGmeas, hGbox, hGret, hGball⟩ :=
        hdb η εwork ηL cLamBox lamScale S sh q
          (inSlabFamilyC Cset' Cang' s' P S) P
          (trimmedSlabShading Cset Cang s' P Y' S)
          (T S sh q) (Z S sh q) (θ0 S sh q) (Mtyp S) (Cstar S)
          ha ha1 hb hθ hηL hcLamBox hdivb h3ηL hlamScale hθ0lb hθ01 hθθ0 (hprod S)
          (by rw [hT S sh q]; exact Finset.filter_subset _ _)
          (fun i hi => by
            refine Set.Subset.trans ?_ (hshV i (inSlabFamilyC_subset hi))
            rw [trimmedSlabShading_shade]
            exact Set.inter_subset_left)
          (fun i hi => by
            rw [hZsh S sh q i hi]
            exact Set.inter_subset_inter_right _ (halfSlabBox_subset S b sh q))
          (fun i hi => hZcar S sh q i hi)
          (fun i hi => htan S sh q i hi)
          (hboxfull S sh q hq) hconc
      refine ⟨G, hGmeas, fun _ _ _ => ⟨hGbox, ?_, ?_⟩⟩
      · rw [← hUloc S]; exact hGret
      · rw [← hUloc S]; exact hGball
    · exact ⟨∅, MeasurableSet.empty, fun hS hsh hq => absurd ⟨hS, hsh, hq⟩ hmem⟩
  choose Gbox hGmeas hGprop using hsel
  exact ⟨Gbox, hGmeas, fun S hS sh hsh q hq => hGprop S sh q hS hsh hq⟩

open scoped Classical in
/-- **Item 1 and the final refinement, from the preassembly-shaped data.**

Phases C, D and E composed: the good boxes are selected, the per-box dense-ball regions are chosen,
and `Plank.localDensity_of_denseBalls` assembles them.  The outputs are exactly what the final
assembly consumes:

* `Gtot = Plank.denseBallUnion 𝒮 Dg Gbox` with its measurability;
* the quantitative refinement of `Yfinal = ShadedBody.restrictShade (Y' i) Gtot` at
  `(256 · Nov · C_mult)⁻¹ · a^{ε_int}`;
* Item 1 at exponent `4η + εwork`, threshold `cBall · cLamBox² · a^{4η+εwork}`, and dilation exactly
  `Kakeya.plankReduction.ballDilation = 3`.

The single `Nov` is the common `max Nov_pt Nov_idx` of the module docstring: `hoverlapPt` is the
preassembly's pointwise bound on the small slab unions and `hoverlapIdx` the index bound on the
enlarged families, both widened to it. -/
theorem slabwiseDensity_of_preassembly (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cBall : ℝ≥0, 0 < cBall ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (Cset Cang Cset' Cang' Cmult cLamBox lamLower lamScale : ℝ≥0)
        (η εwork εint ηL : ℝ) (Nov : ℕ)
        (s' : Finset ι) (P : ι → Plank a b hab hb1)
        (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒮 : Finset (Slab θ hθ1))
        (T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
        (Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι →
          ShadedBody (EuclideanSpace ℝ (Fin 3))),
        1 ≤ cTan → 1 ≤ Cset' → 0 < Cmult → 1 ≤ Nov →
        0 < a → a ≤ 1 → 0 < b → 0 < θ → b ≤ 1 → a / b ≤ θ →
        0 < ηL → 0 < cLamBox → 3 * ηL ≤ 4 * η + εwork →
        cLamBox * a ^ ηL ≤ lamScale →
        lamScale = (2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan) →
        Cset ≤ Cset' → Cang ≤ Cang' →
        (∀ i ∈ s', ∃ S ∈ 𝒮, i ∈ inSlabFamilyC Cset Cang s' P S) →
        (∀ i ∈ s', (𝒮.filter fun S => i ∈ inSlabFamilyC Cset' Cang' s' P S).card ≤ Nov) →
        (∀ x, (𝒮.filter fun S => x ∈ smallSlabUnion Cset Cang s' P Y' S).card ≤ Nov) →
        (∀ i ∈ s', (Y' i).shade ⊆ ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ s', ((Y' i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ S sh q, T S sh q = (inSlabFamilyC Cset' Cang' s' P S).filter
          (fun i => ((trimmedSlabShading Cset Cang s' P Y' S i).shade ∩
            halfSlabBox S b sh q).Nonempty)) →
        (∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).shade
          = (trimmedSlabShading Cset Cang s' P Y' S i).shade ∩ halfSlabBox S b sh q) →
        (∀ S sh q, ∀ i ∈ T S sh q, (Z S sh q i).carrier = (P i).carrier) →
        (∀ S sh q, ∀ i ∈ T S sh q, Kakeya.ComparableScalars cTan
          (volume (((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ S sh q, ∀ i ∈ T S sh q,
          ((Z S sh q i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            = ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ S : Slab θ hθ1, ∀ Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ),
          LocalAngleConcentration P θ gridShiftSet (Dg S) (T S) (Z S) Ceta ηL) →
        lamLower ≤ ShadedBody.fullness s' Y' →
        ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)) →
        ∃ (Gtot : Set (EuclideanSpace ℝ (Fin 3))) (hGtot : MeasurableSet Gtot),
          ShadedBody.IsCRefinement s'
              (fun i => ShadedBody.restrictShade (Y' i) Gtot hGtot) s' Y'
              ((256 * (Nov : ℝ≥0) * Cmult)⁻¹ * a ^ εint) ∧
          ∀ x : EuclideanSpace ℝ (Fin 3),
            ((⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) Gtot hGtot).shade) ∩
              Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
              ((cBall * cLamBox * cLamBox * a ^ (4 * η + εwork) : ℝ≥0) : ENNReal) *
                  volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ))
                ≤ volume ((⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) Gtot hGtot).shade) ∩
                  Metric.closedBall x
                    ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))) := by
  classical
  obtain ⟨cBall, hcBall, hballsel⟩ := denseBallRegions_of_goodBoxes cTan Ceta hCeta
  refine ⟨cBall, hcBall, ?_⟩
  intro a b θ hab hb1 hθ1 ι Cset Cang Cset' Cang' Cmult cLamBox lamLower lamScale
    η εwork εint ηL Nov s' P Y' 𝒮 T Z
    hcTan hCset' hCmult hNov ha ha1 hb hθ hb1' hdivb hηL hcLamBox h3ηL hlamScale hlamDef
    hCsetLe hCangLe hcover hovIdx hovPt hshV hcarEq hT hZsh hZcarP htan hZcarSet hLAC
    hfull hC
  obtain ⟨Dg, -, hDgfull, hcap⟩ :=
    goodBoxes_of_preassemblyData cTan Cset Cang Cset' Cang' Cmult lamLower εint Nov
      hcTan hCset' hCmult hNov ha hb hθ hb1' hCsetLe hCangLe s' P Y' 𝒮 T Z
      hcover hovIdx hshV hcarEq hT hZsh hZcarSet htan hfull hC
  have hboxfull : ∀ S sh, ∀ q ∈ Dg S sh,
      b * lamScale ≤ ShadedBody.fullness (T S sh q) (Z S sh q) := by
    intro S sh q hq
    rw [hlamDef]
    exact hDgfull S sh q hq
  obtain ⟨Gbox, hGmeas, hGprop⟩ :=
    hballsel Cset Cang Cset' Cang' cLamBox lamScale η εwork ηL s' P Y' 𝒮 Dg T Z
      ha ha1 hb hθ hηL hcLamBox hdivb h3ηL hlamScale hCsetLe hCangLe (fun S => hLAC S Dg)
      hshV hT hZsh hZcarP htan hboxfull
  refine ⟨denseBallUnion 𝒮 Dg Gbox,
    measurableSet_denseBallUnion 𝒮 Dg Gbox hGmeas, ?_⟩
  exact localDensity_of_denseBalls s' Y' 𝒮 (smallSlabUnion Cset Cang s' P Y') Dg Gbox
    Cmult (cBall * cLamBox * cLamBox * a ^ (4 * η + εwork)) εint Nov hb hθ ha hCmult hNov
    (fun S _ => measurableSet_smallSlabUnion Cset Cang s' P Y' S)
    (fun S _ => smallSlabUnion_subset Cset Cang s' P Y' S)
    hovPt hGmeas
    (fun S hS sh hsh q hq => (hGprop S hS sh hsh q hq).2.1)
    (fun S hS sh hsh q hq => (hGprop S hS sh hsh q hq).2.2)
    hC hcap

end Plank

end
