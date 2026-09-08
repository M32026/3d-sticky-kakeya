/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Prism
public import Kakeya.Shading

/-!
# Planks and shaded planks
-/

@[expose] public section

open MeasureTheory

noncomputable section

/-- A `Plank a b` is an `(a, b)`-plank in `EuclideanSpace ℝ (Fin 3)` (i.e. `ℝ³`):
the `(a, b, 1)`-prism whose unit-segment direction is the long axis.
Planks have dimensions `a × b × 1`. -/
abbrev Plank (a b : NNReal) (a_le_b : a ≤ b) (b_le_one : b ≤ 1) :=
  Prism3D a b (1 : NNReal) a_le_b b_le_one

/-- A **shaded plank**: an `a × b × 1` plank together with a shading, exactly as `ShadedTube`
bundles a `δ`-tube with a shading.  Both parents extend `ConvexSpaceBody`, so the carrier of the
shading and the carrier of the plank are *the same field*.

That identification is the point of the bundling.  Stated with a separate plank `P i` and a
separate `ShadedBody Y i`, the two carriers are unrelated, and every downstream statement has to
carry the coherence hypotheses `(Y i).shade ⊆ (P i).carrier` and
`(Y i).carrier = (P i).carrier` by hand — the second of which was previously supplied as an
explicit numeric hypothesis (`8ab ≤ volume (Y i).carrier`).  With `ShadedPlank` both are
structural: `shade_subset` is a field, and the carrier equality is definitional. -/
structure ShadedPlank (a b : NNReal) (a_le_b : a ≤ b) (b_le_one : b ≤ 1)
  extends Plank a b a_le_b b_le_one, ShadedBody (EuclideanSpace ℝ (Fin 3))

attribute [nolint docBlame] ShadedPlank.toShadedBody

namespace ShadedPlank

variable {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- The underlying plank of a shaded plank. -/
abbrev plank (Y : ShadedPlank a b hab hb1) : Plank a b hab hb1 := Y.toPrism3D

@[simp] theorem plank_carrier (Y : ShadedPlank a b hab hb1) :
    (Y.plank.carrier : Set (EuclideanSpace ℝ (Fin 3))) = Y.carrier := rfl

@[simp] theorem toShadedBody_carrier (Y : ShadedPlank a b hab hb1) :
    (Y.toShadedBody.carrier : Set (EuclideanSpace ℝ (Fin 3))) = Y.carrier := rfl

/-- The shading of a shaded plank lies in its plank. -/
theorem shade_subset_plank (Y : ShadedPlank a b hab hb1) :
    Y.shade ⊆ (Y.plank.carrier : Set (EuclideanSpace ℝ (Fin 3))) := Y.shade_subset

/-- The family of underlying shadings of a family of shaded planks.  This is how a bundled
Section 6 statement hands its data to the unbundled witness API. -/
abbrev bodies {ι : Type*} (Y : ι → ShadedPlank a b hab hb1) :
    ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i => (Y i).toShadedBody

/-- The family of underlying planks of a family of shaded planks. -/
abbrev planks {ι : Type*} (Y : ι → ShadedPlank a b hab hb1) : ι → Plank a b hab hb1 :=
  fun i => (Y i).plank

@[simp] theorem bodies_shade {ι : Type*} (Y : ι → ShadedPlank a b hab hb1) (i : ι) :
    (bodies Y i).shade = (Y i).shade := rfl

@[simp] theorem planks_carrier {ι : Type*} (Y : ι → ShadedPlank a b hab hb1) (i : ι) :
    ((planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = (Y i).carrier := rfl

/-- Shadings lie in their planks, for the two unbundled families. -/
theorem bodies_shade_subset_planks {ι : Type*} (Y : ι → ShadedPlank a b hab hb1) (i : ι) :
    (bodies Y i).shade ⊆ ((planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
  (Y i).shade_subset

end ShadedPlank

end

end
