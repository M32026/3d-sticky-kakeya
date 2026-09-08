/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.ThickenedGeometry
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# The typed prism view of a thickened anchor

`Plank.ThickenedRepr` returns its anchors as bare `Plank.EnsemblePrism`s, i.e. as
`PrismNDim 3`s with no record of their widths.  Every consumer that has to *cut* a shading against
an anchor — `Plank.exists_goodCover_saturated_aggregate` and, through it,
`Kakeya.exists_absorb_refined_fullness` and the internal Item 2 clause — needs the typed
`Prism3D (θ·b) b 1` view instead, together with the anchor's angle to the slab.

Both are recoverable from the `Plank.ThickenedRepr` itself, and this file does that once.  No
geometric content is added by the *view*: an active anchor **is** the undilated standard thickening
of the selected plank (`Plank.ThickenedRepr.repr_eq`), so its thickness vector is literally
`![θ·b, b, 1]` and the typed reading is the same prism at a more informative type.

The angle bound is the content, and it costs an enlarged but uniform constant.  The selected plank's
thickening is not essentially distinct from the thickening of any plank of the anchor's fibre
(`Plank.ThickenedRepr.notEssentiallyDistinct_repr`), hence within `8·θ` of it
(`Plank.thickening_angle_lt_of_not_essentiallyDistinct`); chaining that with the fibre member's own
`Cang·θ` bound through the quasi-triangle inequality `Prism3D.angle_le_two_mul_add_angle` costs the
absolute factor `2`, giving `2·Cang + 16`.

`Plank.inSlabFamilyC_mono` is here for the same reason: the enlarged angle constant has to be fed
back into the slab family, and consumers take a *single* constant in both slots.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## Monotonicity of the controlled slab family in its two constants -/

/-- The controlled slab subfamily only grows when its two constants grow.  Needed because the
angle constant of the typed anchor view (`Plank.exists_typedAnchorPrism`) is larger than the one
the slab assignment produces, and the internal Item 2 clause consumes a single constant in both
slots. -/
theorem inSlabFamilyC_mono {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {Cset Cang Cset' Cang' : ℝ≥0} (hset : Cset ≤ Cset') (hang : Cang ≤ Cang')
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ : θ ≤ 1} {S : Slab θ hθ} :
    inSlabFamilyC Cset Cang s V S ⊆ inSlabFamilyC Cset' Cang' s V S := by
  intro i hi
  obtain ⟨his, hcar, hangl⟩ := mem_inSlabFamilyC.mp hi
  exact mem_inSlabFamilyC.mpr ⟨his, hcar.trans (S.toPrismNDim.dilation_carrier_mono hset),
    hangl.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hang) θ.coe_nonneg)⟩

/-! ## The typed anchor view -/

/-- `θ · b ≤ b` for `θ ≤ 1`: the first type-level side condition of the thickened prism
`Prism3D (θ · b) b 1`. -/
theorem thickenedWidth_le {θ b : ℝ≥0} (hθ1 : θ ≤ 1) : θ * b ≤ b := by
  simpa [mul_comm, one_mul] using mul_le_mul_right hθ1 b

/-- The geometric core shared by `Plank.exists_typedAnchorPrism` and
`Plank.angle_typedAnchor_le_two_mul_add`: any typed prism sitting over the anchor `R.repr i` meets
an arbitrary slab `S` at angle at most `2·∠(V i, S) + 16·θ`.

The anchor **is** the undilated standard thickening of the selected plank
(`Plank.ThickenedRepr.repr_eq`), so `P` has the basis of `V (sel i)` and hence its angle to `S`;
the selected plank's thickening is not essentially distinct from `i`'s, hence within `8·θ`
(`Plank.thickening_angle_lt_of_not_essentiallyDistinct`); and the quasi-triangle inequality
`Prism3D.angle_le_two_mul_add_angle` chains the two at the absolute cost `2`. -/
private theorem angle_le_two_mul_add_of_toPrismNDim_eq -- (extracted by Fuse golfer)
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk) (hθ0 : 0 < θ) (hb0 : 0 < b)
    {P : Prism3D (θ * b) b 1 (thickenedWidth_le hθ1) hb1} {i : ι} (hi : i ∈ s)
    (hP : P.toPrismNDim = (R.repr i).toPrismNDim) (S : Slab θ hθ1) :
    Prism3D.angle P S ≤ 2 * Prism3D.angle (V i) S + 16 * (θ : ℝ) := by
  have hbasis : P.basis = (V (R.sel i)).basis := by
    have h : P.toPrismNDim = ((V (R.sel i)).thickened θ hθ1).toPrismNDim := by
      rw [hP, R.repr_eq i hi]
    simpa using congrArg PrismNDim.basis h
  have h8 : Prism3D.angle (V (R.sel i)) (V i) < 8 * (θ : ℝ) := by
    have hnd := R.notEssentiallyDistinct_repr i hi
    rw [R.repr_eq i hi] at hnd
    rw [Prism3D.angle_comm]
    exact thickening_angle_lt_of_not_essentiallyDistinct hθ1 hθ0 hb0 (V i) (V (R.sel i)) hnd
  have htri := Prism3D.angle_le_two_mul_add_angle (V (R.sel i)) (V i) S
  rw [Prism3D.angle_def, hbasis, ← Prism3D.angle_def]
  linarith

open scoped Classical in
/-- **The typed `Prism3D` view of a thickened anchor, with its slab angle** (extra69,
`rem:existsTypedAnchorPrism`).

Every active anchor of a `Plank.ThickenedRepr` is, by `Plank.ThickenedRepr.repr_eq`, the undilated
standard thickening of the selected plank, hence a `PrismNDim` whose thickness vector is
`![θ·b, b, 1]`.  So the typed view exists and is the identity on the underlying prism; no geometric
content is added.

The angle clause is the content.  If the whole `repr`-fibre of an anchor lies in the controlled
slab subfamily of a slab `S`, then the anchor's own plane meets `S` at angle at most
`(2·Cang + 16)·θ`: the selected plank's thickening is not essentially distinct from the thickening
of any plank of the fibre, so the two planes are within `8·θ`
(`Plank.thickening_angle_lt_of_not_essentiallyDistinct`), and chaining that with the fibre member's
own `Cang·θ` bound through the quasi-triangle inequality `Prism3D.angle_le_two_mul_add_angle` costs
the absolute factor `2`.

This is exactly the anchor-angle input of the internal Item 2 clause, at the enlarged but still
uniform angle constant `2·Cang + 16`. -/
theorem exists_typedAnchorPrism {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk) (hθ0 : 0 < θ) (hb0 : 0 < b) :
    ∃ Pr : ThickenedPlank θ b hθ1 hb1 → Prism3D (θ * b) b 1 (thickenedWidth_le hθ1) hb1,
      (∀ t ∈ R.indexSet, (Pr t).toPrismNDim = t.toPrismNDim) ∧
      ∀ (Cset Cang : ℝ≥0) (S : Slab θ hθ1) (t : ThickenedPlank θ b hθ1 hb1), t ∈ R.indexSet →
        (∀ j ∈ s, R.repr j = t → j ∈ inSlabFamilyC Cset Cang s V S) →
        Prism3D.angle (Pr t) S ≤ (2 * (Cang : ℝ) + 16) * (θ : ℝ) := by
  refine ⟨fun t => t, fun _ _ => rfl, fun Cset Cang S t ht hfam => ?_⟩
  obtain ⟨i, hi, hrepr⟩ := Finset.mem_image.mp ht
  have h := angle_le_two_mul_add_of_toPrismNDim_eq R hθ0 hb0 hi (P := t) (by rw [hrepr]) S
  have hang := (mem_inSlabFamilyC.mp (hfam i hi hrepr)).2.2
  linarith

open scoped Classical in
/-- **The typed anchor's angle to an arbitrary slab, pointwise in the plank** (extra69,
`rem:angleTypedAnchorLeTwoMulAdd`).

`Plank.exists_typedAnchorPrism` bounds `∠(Pr t, S)` only when the *whole* `repr`-fibre of `t` lies
in the controlled slab subfamily of `S`.  The assembly needs the bound at a slab that the anchor
was not assigned to, where that hypothesis is unavailable, so the bound has to be stated pointwise
in a single plank instead:

  `∠(Pr (repr i), S) ≤ 2 · ∠(V i, S) + 16 · θ`   for every `i ∈ s` and every slab `S`.

The geometry is exactly the chain of `Plank.exists_typedAnchorPrism`: the anchor **is** the
undilated standard thickening of the selected plank (`Plank.ThickenedRepr.repr_eq`), so it has the
same basis and hence the same angle to `S` as `V (sel i)`; the selected plank's thickening is not
essentially distinct from `i`'s (`Plank.ThickenedRepr.notEssentiallyDistinct_repr`), hence within
`8·θ` of it (`Plank.thickening_angle_lt_of_not_essentiallyDistinct`); and the quasi-triangle
inequality `Prism3D.angle_le_two_mul_add_angle` chains the two at the absolute cost `2`.

Only the *typed view* is needed, not the way it was constructed, so the statement takes an
arbitrary `Pr` sitting over the anchors.  That is what lets a caller apply it to the `Pr` already
returned by `Kakeya.representativeWitness_strong_uniform`. -/
theorem angle_typedAnchor_le_two_mul_add {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk) (hθ0 : 0 < θ) (hb0 : 0 < b)
    (Pr : ThickenedPlank θ b hθ1 hb1 → Prism3D (θ * b) b 1 (thickenedWidth_le hθ1) hb1)
    (hPr : ∀ t ∈ R.indexSet, (Pr t).toPrismNDim = t.toPrismNDim)
    (S : Slab θ hθ1) (i : ι) (hi : i ∈ s) :
    Prism3D.angle (Pr (R.repr i)) S ≤ 2 * Prism3D.angle (V i) S + 16 * (θ : ℝ) :=
  angle_le_two_mul_add_of_toPrismNDim_eq R hθ0 hb0 hi (hPr _ (R.repr_mem_indexSet hi)) S

/-- `1 ≤ 4 · Nov · Cres + 1`: the side condition of the enlarged reserve constant
`kappa = 4 · Nov · Cres + 1` used by `Kakeya.representativeWitness_strong_uniform`.

This explicit bound avoids relying on `positivity`, which targets strict positivity rather than a
`1 ≤ _` goal. -/
theorem one_le_four_mul_natCast_mul_add_one (Nov : ℕ) (Cres : ℝ≥0) :
    (1 : ℝ) ≤ 4 * (Nov : ℝ) * (Cres : ℝ) + 1 := by
  have h : (0 : ℝ) ≤ 4 * (Nov : ℝ) * (Cres : ℝ) := by positivity
  linarith

end Plank

end
