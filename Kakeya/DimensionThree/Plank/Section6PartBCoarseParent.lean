/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.InnerSlabNonconcentration
public import Kakeya.DimensionThree.Plank.Section6CoarseFactorisation

/-!
# The coarse-parent system of a Part-(B) cell

`Kakeya.innerFamilySlabNonconcentration` consumes a `Kakeya.CoarseParentSystem`: a fine family, a
coarse family carrying it with comparable fibres, and a Frostman datum for the *coarse* family
inside the ambient plank.  Section 6.6(B) supplies its data as a
`Kakeya.Section6PartBData`, which packages the same information globally.

This module is the one-way adapter between them, taken cellwise: for a cell `x` of the Part-(B)
factorisation, the fine tubes over `x` and the coarse tubes over `x` form a coarse-parent system
inside the representative plank `D.factor.repr x`.

Everything is already proved elsewhere; the adapter only rearranges it:

* the assignment, its comparability and the leaf-in-parent containment come from
  `Kakeya.Section6PartBData.cellDecomposition`, the cellwise restriction of `D.decomp`;
* `parent_le_plank` is `Kakeya.Section6PartBFactorisation.le_repr` read at the cell of `k`;
* the Frostman clause is exactly `Kakeya.Section6PartBData.remark53FibreFrostman`, which is the
  *coarse* datum of the factorisation — the fine family is not Frostman, and this adapter does not
  pretend otherwise (GWZ Remark 5.3).

Nonemptiness of the coarse fibre is an argument rather than a derived fact: at a selected outer cell
it is supplied by `Kakeya.Section6PartBData.coarseFibre_nonempty_of_mem_outerSet`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}

open Classical in
/-- **The cellwise coarse-parent system of a Part-(B) datum.**

The fine tubes over the cell `x`, carried by the coarse tubes over `x`, inside the representative
plank `D.factor.repr x`.  This is the input shape of `Kakeya.innerFamilySlabNonconcentration`. -/
def Section6PartBData.coarseParentSystem
    (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (x : D.factor.Cell) (hx : x ∈ D.factor.cells)
    (hne : (D.factor.coarseFibre x).Nonempty) :
    CoarseParentSystem (D.fineFibre x) (D.factor.coarseFibre x) T R
      (D.factor.repr x) Cfib CF m := by
  refine {
    assign := D.decomp.assign
    assign_mem := (D.cellDecomposition x).assign_mem
    leaf_le_parent := (D.cellDecomposition x).leaf_le_parent
    one_le_Cfib := (D.cellDecomposition x).one_le_Cfib
    fibre_lower := by
      intro k hk
      rw [D.filter_fineFibre_eq hk]
      simpa [Section6CoarseTubeDecomposition.fibre, div_eq_mul_inv, mul_comm] using
        D.decomp.le_card_fibre k (D.factor.coarseFibre_subset x hk)
    fibre_upper := by
      intro k hk
      rw [D.filter_fineFibre_eq hk]
      simpa [Section6CoarseTubeDecomposition.fibre] using
        D.decomp.card_fibre_le k (D.factor.coarseFibre_subset x hk)
    parent_le_plank := by
      intro k hk
      rw [D.factor.mem_coarseFibre_iff] at hk
      rcases hk with ⟨hkcoarse, hkcell⟩
      rw [← hkcell]
      exact Section6PartBFactorisation.le_repr (F := D.factor) hkcoarse
    frostman := D.remark53FibreFrostman x hx
    parents_nonempty := hne
  }

end Kakeya

end

end
