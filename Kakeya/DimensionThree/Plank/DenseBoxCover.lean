/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SaturatedGoodCover
public import Kakeya.DimensionThree.Plank.SlabAggregation
public import Kakeya.DimensionThree.Plank.BoxMassCapture

/-!
# The global good-box union capture

Phase E of GWZ Lemma 6.13 needs one set `W`, built from the selected good boxes of *every* used
slab, such that the shading union is captured by `W` up to a factor `2`:

`|U| ≤ 2 |U ∩ W|`.

`Plank.union_capture_of_sum_capture_rate` reduces that to a bound on the *discarded* mass in the sum
norm, at the discard fraction `f = (2 C_mult)⁻¹ a^{ε_int}` matched to the constant multiplicity
`C_mult a^{-ε_int}` of the preassembly.  This file supplies that bound.

Two things fix the shape of the construction.

**All eight shifts are used.**  At a single shift of `Plank.gridShiftSet` the middle-half boxes
`Plank.halfSlabBox` cover only an eighth of space, so a `W` built from one shift leaves seven
eighths of the mass discarded and the estimate is false.
`Plank.shade_subset_iUnion_halfSlabBox` covers a shading by the middle halves of *all* eight
shifts, and `Plank.goodBoxUnionLocal` accordingly ranges over `Plank.gridShiftSet`.  The whole price
is the absolute constant `#gridShiftSet = 8`, bound before every geometric datum.

**The slabs cover the indices with bounded overlap, and do not partition the shadings.**  The
slab-local families cover `s'` and overlap at most `Nov`-fold in the *index*
(`Plank.slab_index_overlap_le`), so the discarded mass is summed over them at the single constant
cost `Nov`.  No disjointness of the slab *shading unions* is claimed; that is exactly the
distinction recorded in `Kakeya/DimensionThree/Plank/AssignedSlabFamily.lean`, and it is why the
multiplicity hypothesis is used only on the global family `(s', Y')` and never on a slab subfamily.

The threshold scale is
`lamScale = f · lamLower / (512 c_tan)`,
with `lamLower ≤ λ(s', Y')` the incoming fullness bound.  The `512` is forced and exact: the
bad-box charge of `Plank.goodBoxes_saturated_discarded` is `512 c_tan · lamScale · ab · #F` per
(slab, shift), the eight shifts multiply it by `8`, the covering families sum `#F` to `Nov · #s'`,
and the fullness bound `lamLower · #s' · 8ab ≤ ∑ |Y'_i|` converts the target into
`4096 c_tan · lamScale = 8 f · lamLower`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## Two combinatorial ingredients -/

/-- The eight grid shifts of `Plank.gridShiftSet`, counted. -/
theorem gridShiftSet_card : gridShiftSet.card = 8 := by
  rw [gridShiftSet, Fintype.card_piFinset_const]
  norm_num

/-- **Outside the selected boxes, one lands in an unselected box.**  If `A` is covered by the boxes
indexed by `I × J` and `D p ⊆ J` is the selection made at `p`, then the part of `A` outside the
selected boxes is covered by the *unselected* boxes.  This is the set-level step behind every
bad-box charge; it is stated for a two-level index (shift, box) because the good-box selection is
made shift by shift. -/
theorem sdiff_biUnion₂_subset {β γ : Type*} [DecidableEq γ] {E : Type*}
    (I : Finset β) (J : Finset γ) (D : β → Finset γ) (box : β → γ → Set E) (A : Set E)
    (hcover : A ⊆ ⋃ p ∈ I, ⋃ q ∈ J, box p q) :
    A \ (⋃ p ∈ I, ⋃ q ∈ D p, box p q)
      ⊆ ⋃ p ∈ I, ⋃ q ∈ J \ D p, (A ∩ box p q) := by
  classical
  intro x hx
  obtain ⟨hxA, hxn⟩ := hx
  rcases Set.mem_iUnion₂.mp (hcover hxA) with ⟨p, hpI, hx2⟩
  rcases Set.mem_iUnion₂.mp hx2 with ⟨q, hqJ, hbox⟩
  have hqD : q ∉ D p := fun hqDp =>
    hxn (Set.mem_iUnion₂.mpr ⟨p, hpI, Set.mem_iUnion₂.mpr ⟨q, hqDp, hbox⟩⟩)
  exact Set.mem_iUnion₂.mpr ⟨p, hpI,
    Set.mem_iUnion₂.mpr ⟨q, Finset.mem_sdiff.mpr ⟨hqJ, hqD⟩, ⟨hxA, hbox⟩⟩⟩

/-- The measure form of `Plank.sdiff_biUnion₂_subset`. -/
theorem volume_sdiff_biUnion₂_le {β γ : Type*} [DecidableEq γ]
    (I : Finset β) (J : Finset γ) (D : β → Finset γ)
    (box : β → γ → Set (EuclideanSpace ℝ (Fin 3))) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hcover : A ⊆ ⋃ p ∈ I, ⋃ q ∈ J, box p q) :
    volume (A \ (⋃ p ∈ I, ⋃ q ∈ D p, box p q))
      ≤ ∑ p ∈ I, ∑ q ∈ J \ D p, volume (A ∩ box p q) := by
  classical
  calc
    volume (A \ (⋃ p ∈ I, ⋃ q ∈ D p, box p q))
        ≤ volume (⋃ p ∈ I, ⋃ q ∈ J \ D p, (A ∩ box p q)) :=
          measure_mono (sdiff_biUnion₂_subset I J D box A hcover)
    _ ≤ ∑ p ∈ I, volume (⋃ q ∈ J \ D p, (A ∩ box p q)) :=
          measure_biUnion_finset_le I _
    _ ≤ ∑ p ∈ I, ∑ q ∈ J \ D p, volume (A ∩ box p q) :=
          Finset.sum_le_sum fun p _ => measure_biUnion_finset_le _ _

/-! ## The per-slab discarded-mass bound -/

open scoped Classical in
/-- **The discarded mass of one slab, over all eight shifts.**  Summing the bad-box charge of
`Plank.goodBoxes_saturated_discarded` over `Plank.gridShiftSet` bounds the mass of the assigned
family that escapes the slab's own selected good boxes.  The factor `8` is `#gridShiftSet`, and it
is the only loss. -/
theorem sum_volume_sdiff_slabPart_le {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan lamScale Cset Cang : ℝ≥0) (hCset : 1 ≤ Cset)
    (S : Slab θ hθ1) (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Dg : (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (hb : 0 < b) (hθ : 0 < θ) (hb1' : b ≤ 1)
    (hshV : ∀ i ∈ F, (Y' i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ i ∈ F, i ∈ inSlabFamilyC Cset Cang F V S)
    (hbad : ∀ sh, ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊ \ Dg sh,
        ∑ i ∈ F.filter (fun i => ((Y' i).shade ∩ halfSlabBox S b sh q).Nonempty),
          volume ((Y' i).shade ∩ halfSlabBox S b sh q)
      ≤ ((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal)) :
    ∑ i ∈ F, volume ((Y' i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh, halfSlabBox S b sh q)
      ≤ ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal) := by
  classical
  set 𝒦 : Finset (Fin 3 → ℤ) := slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊ with h𝒦
  have h1 :
      ∑ i ∈ F, volume ((Y' i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh, halfSlabBox S b sh q)
        ≤ ∑ i ∈ F, ∑ sh ∈ gridShiftSet, ∑ q ∈ 𝒦 \ Dg sh,
            volume ((Y' i).shade ∩ halfSlabBox S b sh q) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hcov : (Y' i).shade ⊆ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ 𝒦, halfSlabBox S b sh q :=
      shade_subset_iUnion_halfSlabBox S Cset Cang hCset F V Y' hθ hb hb1' hshV hfam hi
    exact volume_sdiff_biUnion₂_le gridShiftSet 𝒦 Dg (fun sh q => halfSlabBox S b sh q)
      ((Y' i).shade) hcov
  have h2 :
      ∑ i ∈ F, ∑ sh ∈ gridShiftSet, ∑ q ∈ 𝒦 \ Dg sh,
        volume ((Y' i).shade ∩ halfSlabBox S b sh q)
      = ∑ sh ∈ gridShiftSet, ∑ q ∈ 𝒦 \ Dg sh, ∑ i ∈ F,
        volume ((Y' i).shade ∩ halfSlabBox S b sh q) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun sh _ => ?_
    rw [Finset.sum_comm]
  have h3 : ∀ sh : Fin 3 → ℝ,
      ∑ q ∈ 𝒦 \ Dg sh, ∑ i ∈ F, volume ((Y' i).shade ∩ halfSlabBox S b sh q)
        ≤ ((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal) := by
    intro sh
    have hrw : ∑ q ∈ 𝒦 \ Dg sh, ∑ i ∈ F, volume ((Y' i).shade ∩ halfSlabBox S b sh q)
        = ∑ q ∈ 𝒦 \ Dg sh,
            ∑ i ∈ F.filter (fun i => ((Y' i).shade ∩ halfSlabBox S b sh q).Nonempty),
              volume ((Y' i).shade ∩ halfSlabBox S b sh q) :=
      Finset.sum_congr rfl fun q _ => sum_halfBox_eq_sum_saturated S sh q F Y'
    rw [hrw, h𝒦]
    exact hbad sh
  have h4 : ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal)
      = (gridShiftSet.card : ENNReal) *
        (((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal)) := by
    rw [gridShiftSet_card]
    push_cast
    ring
  calc
    ∑ i ∈ F, volume ((Y' i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh, halfSlabBox S b sh q)
        ≤ ∑ i ∈ F, ∑ sh ∈ gridShiftSet, ∑ q ∈ 𝒦 \ Dg sh,
            volume ((Y' i).shade ∩ halfSlabBox S b sh q) := h1
    _ = ∑ sh ∈ gridShiftSet, ∑ q ∈ 𝒦 \ Dg sh, ∑ i ∈ F,
            volume ((Y' i).shade ∩ halfSlabBox S b sh q) := h2
    _ ≤ ∑ _sh ∈ gridShiftSet,
            ((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal) :=
          Finset.sum_le_sum fun sh _ => h3 sh
    _ = (gridShiftSet.card : ENNReal) *
            (((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal) := h4.symm

/-! ## The arithmetic of the threshold scale -/

/-- The threshold scale `lamScale = f · lamLower / (512 · Nov · c_tan)` is exactly the one making
the total bad-box charge `4096 · Nov · c_tan · lamScale · ab · #s'` equal to
`f · lamLower · #s' · 8ab`, with the slab-overlap constant `Nov` absorbed into the scale. -/
private lemma four_thousand_ninetysix_mul_lamScale_overlap {cTan f lamLower Nov : ℝ≥0}
    (hcTan : cTan ≠ 0) (hNov : Nov ≠ 0) :
    4096 * Nov * cTan * (f * lamLower / (512 * Nov * cTan)) = 8 * (f * lamLower) := by
  field_simp
  ring

/-! ## The trimmed geometric route

The angular layer cannot be fed the global shading `Y'` on a slab-local family: the typical-angle
predicate does not restrict to an arbitrary subfamily.  What *is* available is
`Plank.isTypicalPlankAngle_inSlabFamilyC_trimmed`, which needs the shading of the **enlarged**
controlled slab family trimmed to the shading union of the **small** one.  So the good-box selection
has to be run on a slab-*dependent* shading `YS S`, while the discarded-mass ledger must still be
stated for the original global `Y'`.

The reconciliation is the one fact that makes the trimming free where it matters: for `i` in the
small family, `(Y' i).shade` is one of the sets whose union is trimmed to, so
`(YS S i).shade = (Y' i).shade` there.  The small families cover `s'`, so every original shading is
accounted for exactly once through the family it belongs to; the enlarged families carry the
fullness, saturation and angle data and are summed with the geometric overlap constant `Nov`, never
with `#𝒮`.

Everything below is abstract in `Small`, `Large` and `YS`: the geometric instantiation
`Small S = inSlabFamilyC Cset Cang s' V S`, `Large S = inSlabFamilyC Cset' Cang' s' V S`,
`YS S i = ShadedBody.restrictShade (Y' i) (⋃ j ∈ Small S, (Y' j).shade)` is a separate step,
so this file keeps its import set and stays upstream of `Kakeya.plankReduction`.
-/

open scoped Classical in
/-- **One slab, trimmed.**  The discarded mass of the *original* shadings of the small family,
bounded by the bad-box charge of the *enlarged* family carrying the trimmed shadings.

The two index sets are genuinely different: `Fsmall` is what the global ledger sums over, `Flarge`
is what the Markov step and the angular layer run on.  The bridge is `hshadeEq`, which is free for
the geometric instantiation. -/
theorem sum_volume_sdiff_slabPart_le_trimmed
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan lamScale Cset Cang : ℝ≥0) (hCset : 1 ≤ Cset)
    (S : Slab θ hθ1) (Fsmall Flarge : Finset ι) (V : ι → Plank a b hab hb1)
    (Y' YS : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Dg : (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (hb : 0 < b) (hθ : 0 < θ) (hb1' : b ≤ 1)
    (hsub : Fsmall ⊆ Flarge)
    (hshadeEq : ∀ i ∈ Fsmall, (Y' i).shade = (YS i).shade)
    (hshV : ∀ i ∈ Flarge, (YS i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ i ∈ Flarge, i ∈ inSlabFamilyC Cset Cang Flarge V S)
    (hbad : ∀ sh, ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊ \ Dg sh,
        ∑ i ∈ Flarge.filter (fun i => ((YS i).shade ∩ halfSlabBox S b sh q).Nonempty),
          volume ((YS i).shade ∩ halfSlabBox S b sh q)
      ≤ ((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (Flarge.card : ENNReal)) :
    ∑ i ∈ Fsmall, volume ((Y' i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh, halfSlabBox S b sh q)
      ≤ ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (Flarge.card : ENNReal) := by
  classical
  calc
    ∑ i ∈ Fsmall, volume ((Y' i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh, halfSlabBox S b sh q)
        = ∑ i ∈ Fsmall, volume ((YS i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh,
            halfSlabBox S b sh q) :=
          Finset.sum_congr rfl fun i hi => by rw [hshadeEq i hi]
    _ ≤ ∑ i ∈ Flarge, volume ((YS i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg sh,
            halfSlabBox S b sh q) := Finset.sum_le_sum_of_subset hsub
    _ ≤ ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (Flarge.card : ENNReal) :=
          sum_volume_sdiff_slabPart_le cTan lamScale Cset Cang hCset S Flarge V YS Dg hb hθ hb1'
            hshV hfam hbad

/-! ## The localized capture set

The naive capture set — the plain union of the selected half-boxes over all slabs — is too coarse
for the slab/shift/box aggregation: a point of `U` inside a box of slab `S` need not lie in the
slab-local union `U_S`, so `U ∩ W` does not decompose into slab-local pieces, and the bounded
overlap `Nov` — which controls the slab-local *shading unions*, not the slab grids — does not apply.

The repair is to localize the capture set itself,

`Wloc = ⋃ S ∈ 𝒮, Uloc S ∩ (⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)`,

which is *smaller* than that plain union yet captures exactly as much.  The reason the
discarded-mass ledger is unaffected is `Plank.sdiff_goodBoxUnionLocal_subset`: for `i` in the small
family of `S` the shade `(Y' i).shade` already lies inside `Uloc S`, so intersecting the slab's
box-union with `Uloc S` removes nothing that `i` could have been charged for.

With `Wloc` every retained piece is a subset of some `Uloc S`, and the aggregation closes with the
constants `2` (capture), `2` (per-box retention), `8` (`Plank.shiftedSlabBox_sum_inter_volume_le`,
the grid boxes at a fixed shift are closed and share faces), `8` (`Plank.gridShiftSet_card`) and
`Nov` — and no `#𝒮`.
-/

/-- **The trimmed enlarged-family union is the small-family union.**

Trimming every shade of the *enlarged* family to the shading union `USmall` of the *small* family
does not enlarge and does not shrink that union: the trimmed shades all lie inside `USmall` by
construction, and each small-family shade survives trimming untouched because it is one of the sets
whose union `USmall` is.

This is the identity that lets `Uloc S = ⋃ i ∈ Large S, (YS S i).shade` be used interchangeably with
the small-family union — in particular it is how the `Nov` overlap of
`Kakeya.plankReduction_preassembly`, which is stated for the small families, transfers to
`Uloc`.  It is stated once here rather than reproved at each use. -/
theorem biUnion_trimmed_eq_smallUnion
    (Small Large : Finset ι) (Y' YS : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (USmall : Set (EuclideanSpace ℝ (Fin 3)))
    (hSL : Small ⊆ Large)
    (hUSmall : USmall = ⋃ i ∈ Small, (Y' i).shade)
    (hYS : ∀ i, (YS i).shade = (Y' i).shade ∩ USmall) :
    (⋃ i ∈ Large, (YS i).shade) = USmall := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun i _ => ?_
    rw [hYS i]
    exact Set.inter_subset_right
  · intro x hx
    have hx' : x ∈ ⋃ i ∈ Small, (Y' i).shade := by rw [← hUSmall]; exact hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx'
    refine Set.mem_iUnion₂.mpr ⟨i, hSL hi, ?_⟩
    rw [hYS i]
    exact ⟨hxi, hx⟩

/-- **The localized good-box capture set.** -/
def goodBoxUnionLocal {θ : ℝ≥0} {hθ1 : θ ≤ 1} (𝒮 : Finset (Slab θ hθ1)) (b : ℝ≥0)
    (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ S ∈ 𝒮, Uloc S ∩ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q

theorem measurableSet_goodBoxUnionLocal {θ : ℝ≥0} {hθ1 : θ ≤ 1} (𝒮 : Finset (Slab θ hθ1))
    (b : ℝ≥0) (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (hUloc : ∀ S ∈ 𝒮, MeasurableSet (Uloc S)) :
    MeasurableSet (goodBoxUnionLocal 𝒮 b Uloc Dg) := by
  classical
  refine MeasurableSet.biUnion (Finset.countable_toSet 𝒮) fun S hS => ?_
  refine (hUloc S (Finset.mem_coe.mp hS)).inter ?_
  refine MeasurableSet.biUnion (Finset.countable_toSet gridShiftSet) fun sh _ => ?_
  refine MeasurableSet.biUnion (Finset.countable_toSet (Dg S sh)) fun q _ => ?_
  exact ((shiftedSlabBox S b sh q).toPrismNDim.dilation 2⁻¹).measurableSet_carrier

/-- The slab-local piece of `Plank.goodBoxUnionLocal`. -/
theorem slabPartLocal_subset_goodBoxUnionLocal {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    {𝒮 : Finset (Slab θ hθ1)} {b : ℝ≥0}
    {Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))}
    {Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)} {S : Slab θ hθ1} (hS : S ∈ 𝒮) :
    Uloc S ∩ (⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
      ⊆ goodBoxUnionLocal 𝒮 b Uloc Dg := by
  simp only [goodBoxUnionLocal]
  intro x hx
  exact Set.mem_biUnion (Finset.mem_coe.mpr hS) hx

/-- **Localizing the capture set costs nothing on the ledger.**  For a shade already contained in
`Uloc S`, the part missed by the localized capture set is contained in the part missed by the slab's
own box-union.  This is what lets the discarded-mass estimate be re-run verbatim for
`Plank.goodBoxUnionLocal`. -/
theorem sdiff_goodBoxUnionLocal_subset {θ : ℝ≥0} {hθ1 : θ ≤ 1}
    {𝒮 : Finset (Slab θ hθ1)} {b : ℝ≥0}
    {Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3))}
    {Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)} {S : Slab θ hθ1} (hS : S ∈ 𝒮)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : A ⊆ Uloc S) :
    A \ goodBoxUnionLocal 𝒮 b Uloc Dg
      ⊆ A \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q := by
  intro x hx
  refine ⟨hx.1, fun hxW => hx.2 ?_⟩
  exact slabPartLocal_subset_goodBoxUnionLocal hS ⟨hA hx.1, hxW⟩

open scoped Classical in
/-- **The global discarded mass against the localized capture set.**  The per-slab charge of
`Plank.sum_volume_sdiff_slabPart_le_trimmed` summed over the covering families, with the `Nov`-fold
index overlap as the only loss beyond the absolute constants.  The one input specific to the
localized capture set is that each small family's shades lie in its own slab-local union, which is
what `Plank.sdiff_goodBoxUnionLocal_subset` consumes. -/
theorem sum_volume_sdiff_goodBoxUnionLocal_le_of_trimmed
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan lamScale Cset Cang : ℝ≥0) (hCset : 1 ≤ Cset) (Nov : ℕ)
    (s' : Finset ι) (V : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (YS : Slab θ hθ1 → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒮 : Finset (Slab θ hθ1)) (Small Large : Slab θ hθ1 → Finset ι)
    (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (hb : 0 < b) (hθ : 0 < θ) (hb1' : b ≤ 1)
    (hSmallsub : ∀ S ∈ 𝒮, Small S ⊆ s')
    (hcover : ∀ i ∈ s', ∃ S ∈ 𝒮, i ∈ Small S)
    (hSmallLarge : ∀ S ∈ 𝒮, Small S ⊆ Large S)
    (hLargesub : ∀ S ∈ 𝒮, Large S ⊆ s')
    (hoverlap : ∀ i ∈ s', (𝒮.filter fun S => i ∈ Large S).card ≤ Nov)
    (hshadeUloc : ∀ S ∈ 𝒮, ∀ i ∈ Small S, (Y' i).shade ⊆ Uloc S)
    (hshadeEq : ∀ S ∈ 𝒮, ∀ i ∈ Small S, (Y' i).shade = (YS S i).shade)
    (hshV : ∀ S ∈ 𝒮, ∀ i ∈ Large S,
      (YS S i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ S ∈ 𝒮, ∀ i ∈ Large S, i ∈ inSlabFamilyC Cset Cang (Large S) V S)
    (hbad : ∀ S ∈ 𝒮, ∀ sh : Fin 3 → ℝ,
      ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊ \ Dg S sh,
        ∑ i ∈ (Large S).filter
            (fun i => ((YS S i).shade ∩ halfSlabBox S b sh q).Nonempty),
          volume ((YS S i).shade ∩ halfSlabBox S b sh q)
      ≤ ((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (((Large S).card : ℕ) : ENNReal)) :
    ∑ i ∈ s', volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
      ≤ ((4096 * (Nov : ℝ≥0) * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
          (s'.card : ENNReal) := by
  classical
  have hstep1 := sum_le_sum_families_of_cover s' 𝒮 Small
    (fun i => volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)) hSmallsub hcover
  have hstep2 : ∀ S ∈ 𝒮, ∑ i ∈ Small S,
      volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
      ≤ ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
          (((Large S).card : ℕ) : ENNReal) := by
    intro S hS
    calc
      ∑ i ∈ Small S, volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
          ≤ ∑ i ∈ Small S, volume ((Y' i).shade \ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh,
              halfSlabBox S b sh q) := by
            refine Finset.sum_le_sum fun i hi => ?_
            exact measure_mono (sdiff_goodBoxUnionLocal_subset hS (hshadeUloc S hS i hi))
      _ ≤ ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
              (((Large S).card : ℕ) : ENNReal) :=
            sum_volume_sdiff_slabPart_le_trimmed cTan lamScale Cset Cang hCset S (Small S)
              (Large S) V Y' (YS S) (Dg S) hb hθ hb1' (hSmallLarge S hS) (hshadeEq S hS)
              (hshV S hS) (hfam S hS) (hbad S hS)
  have hcard : (∑ S ∈ 𝒮, (Large S).card) ≤ Nov * s'.card :=
    sum_card_le_mul_card_of_overlap s' 𝒮 Large Nov hLargesub hoverlap
  have hfinal : ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
        ((Nov * s'.card : ℕ) : ENNReal)
      = ((4096 * (Nov : ℝ≥0) * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
        (s'.card : ENNReal) := by
    push_cast
    ring
  calc
    ∑ i ∈ s', volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
        ≤ ∑ S ∈ 𝒮, ∑ i ∈ Small S,
            volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg) := hstep1
    _ ≤ ∑ S ∈ 𝒮, ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
          (((Large S).card : ℕ) : ENNReal) := Finset.sum_le_sum hstep2
    _ = ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
          ∑ S ∈ 𝒮, (((Large S).card : ℕ) : ENNReal) := by rw [Finset.mul_sum]
    _ = ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
          (((∑ S ∈ 𝒮, (Large S).card : ℕ)) : ENNReal) := by rw [← Nat.cast_sum]
    _ ≤ ((4096 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * ((Nov * s'.card : ℕ) : ENNReal) :=
          mul_le_mul_right (Nat.cast_le.mpr hcard) _
    _ = ((4096 * (Nov : ℝ≥0) * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) *
          (s'.card : ENNReal) := hfinal

open scoped Classical in
/-- **The union capture against the localized capture set.**

The local families are drawn from the *enlarged* controlled slab family `Large S` and their shadings
are the trimmed `YS S` cut to the middle half of a box, while the discarded-mass ledger
(`Plank.sum_volume_sdiff_goodBoxUnionLocal_le_of_trimmed`) and the union capture are stated for the
original global `(s', Y')`; the capture is `Plank.union_capture_of_sum_capture_rate` applied to that
global family, so the constant multiplicity is never restricted to a slab subfamily.

The threshold scale is
`lamScale = (2 C_mult)⁻¹ a^{ε_int} · lamLower / (512 · Nov · c_tan)`,
so the trimming costs nothing in the exponent ledger: the layer spends exactly one factor
`a^{ε_int}` and the fixed constants `512`, `8` (the grid shifts, already inside the `4096`) and
`Nov`.

This is the form the slab/shift/box aggregation consumes: every point of `Wloc` lies in some
`Uloc S`, so the retained pieces inherit the `Nov` overlap of the slab-local unions. -/
theorem goodBoxes_unionLocal_capture_of_trimmedSlabFamilies
    {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan Cset Cang Cmult lamLower : ℝ≥0) (εint : ℝ) (Nov : ℕ)
    (hcTan : 1 ≤ cTan) (hCset : 1 ≤ Cset) (hCmult : 0 < Cmult) (hNov : 1 ≤ Nov)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ) (hb1' : b ≤ 1)
    (s' : Finset ι) (V : ι → Plank a b hab hb1)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (YS : Slab θ hθ1 → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒮 : Finset (Slab θ hθ1)) (Small Large : Slab θ hθ1 → Finset ι)
    (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (T : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
    (Z : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hUlocMeas : ∀ S ∈ 𝒮, MeasurableSet (Uloc S))
    (hSmallsub : ∀ S ∈ 𝒮, Small S ⊆ s')
    (hcover : ∀ i ∈ s', ∃ S ∈ 𝒮, i ∈ Small S)
    (hSmallLarge : ∀ S ∈ 𝒮, Small S ⊆ Large S)
    (hLargesub : ∀ S ∈ 𝒮, Large S ⊆ s')
    (hoverlap : ∀ i ∈ s', (𝒮.filter fun S => i ∈ Large S).card ≤ Nov)
    (hshadeUloc : ∀ S ∈ 𝒮, ∀ i ∈ Small S, (Y' i).shade ⊆ Uloc S)
    (hshadeEq : ∀ S ∈ 𝒮, ∀ i ∈ Small S, (Y' i).shade = (YS S i).shade)
    (hshV : ∀ S ∈ 𝒮, ∀ i ∈ Large S,
      (YS S i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hcarvol : ∀ i ∈ s', 8 * (a : ENNReal) * (b : ENNReal) ≤ volume (Y' i).carrier)
    (hfam : ∀ S ∈ 𝒮, ∀ i ∈ Large S, i ∈ inSlabFamilyC Cset Cang (Large S) V S)
    (hT : ∀ S sh q, T S sh q = (Large S).filter
      (fun i => ((YS S i).shade ∩ halfSlabBox S b sh q).Nonempty))
    (hZsh : ∀ S sh q, ∀ i ∈ T S sh q,
      (Z S sh q i).shade = (YS S i).shade ∩ halfSlabBox S b sh q)
    (hZcar : ∀ S sh q, ∀ i ∈ T S sh q,
      (Z S sh q i).carrier = ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ S sh q, ∀ i ∈ T S sh q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hfull : lamLower ≤ ShadedBody.fullness s' Y')
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hUtop : volume (⋃ i ∈ s', (Y' i).shade) ≠ ⊤) :
    ∃ Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ),
      (∀ S sh, Dg S sh ⊆ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊) ∧
      (∀ S sh, ∀ q ∈ Dg S sh,
        b * ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan))
          ≤ ShadedBody.fullness (T S sh q) (Z S sh q)) ∧
      (∑ i ∈ s', volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
        ≤ (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ENNReal) * ∑ i ∈ s', volume (Y' i).shade) ∧
      volume (⋃ i ∈ s', (Y' i).shade)
        ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ goodBoxUnionLocal 𝒮 b Uloc Dg) := by
  classical
  have hcTan0 : cTan ≠ 0 := (lt_of_lt_of_le zero_lt_one hcTan).ne'
  have hNov0 : ((Nov : ℝ≥0)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hNov))
  have hsel : ∀ (S : Slab θ hθ1) (sh : Fin 3 → ℝ),
      ∃ D ⊆ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊,
        (∀ q ∈ D, b * ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan))
          ≤ ShadedBody.fullness (T S sh q) (Z S sh q)) ∧
        (∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊ \ D, ∑ i ∈ T S sh q,
            volume ((YS S i).shade ∩ halfSlabBox S b sh q)
          ≤ ((512 * cTan * ((2 * Cmult)⁻¹ * a ^ εint * lamLower /
                (512 * (Nov : ℝ≥0) * cTan)) * (a * b) : ℝ≥0) : ENNReal) *
              (((Large S).card : ℕ) : ENNReal)) := by
    intro S sh
    obtain ⟨D, hDsub, hfullD, -, hdiscD⟩ :=
      goodBoxes_saturated_discarded cTan
        ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan)) S sh
        (slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊)
        (Large S) V (YS S) (T S sh) (Z S sh) (fun q => halfSlabBox S b sh q) ha hb hθ
        (fun q => by rw [hT S sh q]; exact Finset.filter_subset _ _)
        (hZsh S sh) (hZcar S sh) (htan S sh)
    exact ⟨D, hDsub, hfullD, hdiscD⟩
  choose Dg hDgsub hDgfull hDgdisc using hsel
  have hbad' : ∀ S ∈ 𝒮, ∀ sh : Fin 3 → ℝ,
      ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊ \ Dg S sh,
        ∑ i ∈ (Large S).filter (fun i => ((YS S i).shade ∩ halfSlabBox S b sh q).Nonempty),
          volume ((YS S i).shade ∩ halfSlabBox S b sh q)
      ≤ ((512 * cTan * ((2 * Cmult)⁻¹ * a ^ εint * lamLower /
            (512 * (Nov : ℝ≥0) * cTan)) * (a * b) : ℝ≥0) : ENNReal) *
          (((Large S).card : ℕ) : ENNReal) := by
    intro S _ sh
    simp only [← hT S sh]
    exact hDgdisc S sh
  have h1 := sum_volume_sdiff_goodBoxUnionLocal_le_of_trimmed cTan
    ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan)) Cset Cang hCset Nov
    s' V Y' YS 𝒮 Small Large Uloc Dg hb hθ hb1' hSmallsub hcover hSmallLarge hLargesub hoverlap
    hshadeUloc hshadeEq hshV hfam hbad'
  have hmass := ShadedBody.coe_fullness_mul_le_sum_volume_shade s' Y' hfull hcarvol
  have hnn : (4096 * (Nov : ℝ≥0) * cTan *
        ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan)) * (a * b) : ℝ≥0)
      = ((2 * Cmult)⁻¹ * a ^ εint) * (lamLower * (8 * a * b)) := by
    rw [four_thousand_ninetysix_mul_lamScale_overlap
      (f := (2 * Cmult)⁻¹ * a ^ εint) hcTan0 hNov0]
    ring
  have h2 : ((4096 * (Nov : ℝ≥0) * cTan *
        ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan)) * (a * b) : ℝ≥0)
        : ENNReal) * (s'.card : ENNReal)
      = (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ENNReal) *
        ((lamLower : ENNReal) * ((s'.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))) := by
    rw [hnn]
    push_cast
    ring
  have hdiscard : ∑ i ∈ s', volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
      ≤ (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ENNReal) * ∑ i ∈ s', volume (Y' i).shade := by
    calc
      ∑ i ∈ s', volume ((Y' i).shade \ goodBoxUnionLocal 𝒮 b Uloc Dg)
          ≤ ((4096 * (Nov : ℝ≥0) * cTan *
              ((2 * Cmult)⁻¹ * a ^ εint * lamLower / (512 * (Nov : ℝ≥0) * cTan)) * (a * b)
                : ℝ≥0) : ENNReal) * (s'.card : ENNReal) := h1
      _ = (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ENNReal) *
            ((lamLower : ENNReal) *
              ((s'.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))) := h2
      _ ≤ (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ENNReal) * ∑ i ∈ s', volume (Y' i).shade :=
            mul_le_mul_right hmass _
  exact ⟨Dg, hDgsub, hDgfull, hdiscard,
    union_capture_of_sum_capture_rate s' Y' (goodBoxUnionLocal 𝒮 b Uloc Dg)
      (measurableSet_goodBoxUnionLocal 𝒮 b Uloc Dg hUlocMeas) Cmult εint hCmult ha hC
      hdiscard hUtop⟩

open scoped Classical in
/-- **The slab/shift/box aggregation.**

From the localized capture `|U| ≤ 2 |U ∩ Wloc|` and the per-box half-retention of each slab-local
union, the globally retained set `Gtot` keeps a fixed fraction of `U`:

`|U| ≤ 256 · Nov · |U ∩ Gtot|`.

The four factors are all fixed before the configuration and none of them is `#𝒮`:

* `2` from the localized capture;
* `2` from the per-box half-retention;
* `8` from `Plank.shiftedSlabBox_sum_inter_volume_le` — at a *fixed* shift the grid boxes are closed
  and share faces, so a point can lie in up to `2³` of them;
* `8` from `Plank.gridShiftSet_card`;
* `Nov` from the pointwise overlap of the slab-local unions, applied through
  `MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le` to the sets
  `Uloc S ∩ Gtot ⊆ Uloc S`.

The reason this works — and the reason a non-localized capture set does not — is that every retained
piece is a subset of some `Uloc S`, so the `Nov` overlap of the slab-local *shading unions* is
exactly the right tool.  No slab-local constant multiplicity is used anywhere. -/
theorem volume_le_mul_volume_inter_of_localCapture
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (𝒮 : Finset (Slab θ hθ1)) (b : ℝ≥0)
    (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (U Gtot : Set (EuclideanSpace ℝ (Fin 3))) (Nov : ℕ)
    (hb : 0 < b) (hθ : 0 < θ)
    (hUlocMeas : ∀ S ∈ 𝒮, MeasurableSet (Uloc S))
    (hGtotMeas : MeasurableSet Gtot)
    (hUlocU : ∀ S ∈ 𝒮, Uloc S ⊆ U)
    (hGsub : ∀ S ∈ 𝒮, ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh, Gbox S sh q ⊆ Gtot)
    (hoverlap : ∀ x, (𝒮.filter fun S => x ∈ Uloc S).card ≤ Nov)
    (hret : ∀ S ∈ 𝒮, ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh,
      volume (Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
          Set (EuclideanSpace ℝ (Fin 3))))
        ≤ 2 * volume ((Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q))
    (hcap : volume U ≤ 2 * volume (U ∩ goodBoxUnionLocal 𝒮 b Uloc Dg)) :
    volume U ≤ (256 * (Nov : ENNReal)) * volume (U ∩ Gtot) := by
  classical
  -- one slab: its localized capture piece is captured by `Gtot` up to `128`
  have hslab : ∀ S ∈ 𝒮,
      volume (Uloc S ∩ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
        ≤ (128 : ENNReal) * volume (Uloc S ∩ Gtot) := by
    intro S hS
    have hbox : ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh,
        volume (Uloc S ∩ halfSlabBox S b sh q)
          ≤ 2 * volume ((Uloc S ∩ Gtot) ∩ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) := by
      intro sh hsh q hq
      calc
        volume (Uloc S ∩ halfSlabBox S b sh q)
            ≤ volume (Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) :=
              measure_mono (Set.inter_subset_inter_right _ (halfSlabBox_subset S b sh q))
        _ ≤ 2 * volume ((Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q) := hret S hS sh hsh q hq
        _ ≤ 2 * volume ((Uloc S ∩ Gtot) ∩ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) := by
              refine mul_le_mul_right (measure_mono ?_) _
              intro x hx
              exact ⟨⟨hx.1.1, hGsub S hS sh hsh q hq hx.2⟩, hx.1.2⟩
    have hshift : ∀ sh ∈ gridShiftSet,
        volume (Uloc S ∩ ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
          ≤ (16 : ENNReal) * volume (Uloc S ∩ Gtot) := by
      intro sh hsh
      have hsplit : Uloc S ∩ (⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
          = ⋃ q ∈ Dg S sh, (Uloc S ∩ halfSlabBox S b sh q) := by
        simp [Set.inter_iUnion]
      calc
        volume (Uloc S ∩ ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
            = volume (⋃ q ∈ Dg S sh, (Uloc S ∩ halfSlabBox S b sh q)) := by rw [hsplit]
        _ ≤ ∑ q ∈ Dg S sh, volume (Uloc S ∩ halfSlabBox S b sh q) :=
              measure_biUnion_finset_le _ _
        _ ≤ ∑ q ∈ Dg S sh, 2 * volume ((Uloc S ∩ Gtot) ∩
              ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :=
              Finset.sum_le_sum fun q hq => hbox sh hsh q hq
        _ = 2 * ∑ q ∈ Dg S sh, volume ((Uloc S ∩ Gtot) ∩
              ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
              rw [Finset.mul_sum]
        _ ≤ 2 * ((8 : ENNReal) * volume (Uloc S ∩ Gtot)) := by
              refine mul_le_mul_right ?_ _
              exact shiftedSlabBox_sum_inter_volume_le S hb hθ sh (Dg S sh)
                ((hUlocMeas S hS).inter hGtotMeas)
        _ = (16 : ENNReal) * volume (Uloc S ∩ Gtot) := by ring
    have hsplit : Uloc S ∩ (⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
        = ⋃ sh ∈ gridShiftSet, (Uloc S ∩ ⋃ q ∈ Dg S sh, halfSlabBox S b sh q) := by
      simp [Set.inter_iUnion]
    calc
      volume (Uloc S ∩ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, halfSlabBox S b sh q)
          = volume (⋃ sh ∈ gridShiftSet, (Uloc S ∩ ⋃ q ∈ Dg S sh,
              halfSlabBox S b sh q)) := by rw [hsplit]
      _ ≤ ∑ sh ∈ gridShiftSet, volume (Uloc S ∩ ⋃ q ∈ Dg S sh, halfSlabBox S b sh q) :=
            measure_biUnion_finset_le _ _
      _ ≤ ∑ _sh ∈ gridShiftSet, (16 : ENNReal) * volume (Uloc S ∩ Gtot) :=
            Finset.sum_le_sum fun sh hsh => hshift sh hsh
      _ = (gridShiftSet.card : ENNReal) * ((16 : ENNReal) * volume (Uloc S ∩ Gtot)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (128 : ENNReal) * volume (Uloc S ∩ Gtot) := by
            rw [gridShiftSet_card]; push_cast; ring
  -- the slab-local retained pieces have overlap at most `Nov`
  have hgen : ∀ A : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ S ∈ 𝒮, MeasurableSet (A S)) → (∀ S ∈ 𝒮, A S ⊆ Uloc S) →
      ∑ S ∈ 𝒮, volume (A S) ≤ (Nov : ENNReal) * volume (⋃ S ∈ 𝒮, A S) := by
    intro A hAmeas hAsub
    refine MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le (s := 𝒮)
      (A := A) (μ := volume) (hA := hAmeas) (C := Nov) (hC := ?_)
    intro x
    refine le_trans ?_ (hoverlap x)
    refine Finset.card_le_card ?_
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hS𝒮, hx⟩
    exact Finset.mem_filter.mpr ⟨hS𝒮, hAsub S hS𝒮 hx⟩
  have hsumG : ∑ S ∈ 𝒮, volume (Uloc S ∩ Gtot)
      ≤ (Nov : ENNReal) * volume (⋃ S ∈ 𝒮, (Uloc S ∩ Gtot)) :=
    hgen (fun S => Uloc S ∩ Gtot) (fun S hS => (hUlocMeas S hS).inter hGtotMeas)
      (fun S _ => Set.inter_subset_left)
  have hUG : (⋃ S ∈ 𝒮, (Uloc S ∩ Gtot)) ⊆ U ∩ Gtot := by
    refine Set.iUnion₂_subset fun S hS => ?_
    exact Set.inter_subset_inter_left _ (hUlocU S hS)
  calc
    volume U ≤ 2 * volume (U ∩ goodBoxUnionLocal 𝒮 b Uloc Dg) := hcap
    _ ≤ 2 * volume (goodBoxUnionLocal 𝒮 b Uloc Dg) :=
          mul_le_mul_right (measure_mono Set.inter_subset_right) _
    _ ≤ 2 * ∑ S ∈ 𝒮, volume (Uloc S ∩ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh,
          halfSlabBox S b sh q) :=
          mul_le_mul_right (measure_biUnion_finset_le _ _) _
    _ ≤ 2 * ∑ S ∈ 𝒮, (128 : ENNReal) * volume (Uloc S ∩ Gtot) :=
          mul_le_mul_right (Finset.sum_le_sum hslab) _
    _ = 256 * ∑ S ∈ 𝒮, volume (Uloc S ∩ Gtot) := by rw [← Finset.mul_sum]; ring
    _ ≤ 256 * ((Nov : ENNReal) * volume (⋃ S ∈ 𝒮, (Uloc S ∩ Gtot))) :=
          mul_le_mul_right hsumG _
    _ ≤ 256 * ((Nov : ENNReal) * volume (U ∩ Gtot)) :=
          mul_le_mul_right (mul_le_mul_right (measure_mono hUG) _) _
    _ = (256 * (Nov : ENNReal)) * volume (U ∩ Gtot) := by ring

end Plank

end
