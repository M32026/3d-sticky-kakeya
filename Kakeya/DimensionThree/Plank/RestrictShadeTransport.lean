/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# Transport of the angular data through a common restriction

The final family of GWZ Lemma 6.13 is `ShadedBody.restrictShade (Y' i) G` for one measurable set `G`
shared by every index.  This file records what that operation does to the angular data.

The point is that a *common* restriction is not a refinement in the lossy sense: at a point of `G`
the restricted shade fibre is the unrestricted one, because `i` belongs to the fibre iff
`x ∈ (Y' i).shade ∩ G`, and `x ∈ G` holds by assumption.  So the two-sided
`Kakeya.IsTypicalPlankAngle` transfers with the *same* constant and the *same* stability scale — no
fibre-retention factor is spent, and the two-sided predicate, which is not monotone under shrinking
a family, survives.

Contrast `Kakeya.HasMaxPlankAngleBound.mono`, which handles an arbitrary shrinking but only for the
one-sided predicate; that is not enough here, because `Kakeya.plankReduction` returns the two-sided
`Kakeya.IsTypicalPlankAngle`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

@[simp] theorem restrictShade_carrier (Z : ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G) :
    ((ShadedBody.restrictShade Z G hG).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Z.carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

theorem restrictShade_shade_subset (Z : ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G) :
    (ShadedBody.restrictShade Z G hG).shade ⊆ Z.shade := Set.inter_subset_left

/-- **A common restriction does not change the shade fibre at a point of the restricting set.** -/
theorem shadeFibre_restrictShade (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ G) :
    Kakeya.shadeFibre s (fun i => ShadedBody.restrictShade (Y i) G hG) x =
      Kakeya.shadeFibre s Y x := by
  ext i
  rw [Kakeya.mem_shadeFibre, Kakeya.mem_shadeFibre]
  exact and_congr_right fun _ => ⟨And.left, (⟨·, hx⟩)⟩

/-- Every point of the restricted shading union lies in the restricting set. -/
theorem mem_of_mem_biUnion_restrictShade {s : Finset ι}
    {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {G : Set (EuclideanSpace ℝ (Fin 3))} {hG : MeasurableSet G}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ s, (ShadedBody.restrictShade (Y i) G hG).shade) : x ∈ G :=
  Set.iUnion₂_subset (fun _ _ => Set.inter_subset_right) hx

/-- Every point of the restricted shading union lies in the original shading union. -/
theorem mem_biUnion_of_mem_biUnion_restrictShade {s : Finset ι}
    {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {G : Set (EuclideanSpace ℝ (Fin 3))} {hG : MeasurableSet G}
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ⋃ i ∈ s, (ShadedBody.restrictShade (Y i) G hG).shade) :
    x ∈ ⋃ i ∈ s, (Y i).shade :=
  Set.iUnion₂_mono (fun i _ => restrictShade_shade_subset (Y i) G hG) hx

/-- **The two-sided typical plank angle survives a common restriction, at the same constant and the
same stability scale.**

This is the transport `Kakeya.plankReduction` needs for its typical-angle clause: the final
family is `Y'` cut by one global set, and the predicate is recovered with no loss because the
shade fibres are literally unchanged on the restricting set. -/
theorem isTypicalPlankAngle_restrictShade {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) {θ Cθ A : ℝ≥0}
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G)
    (hty : Kakeya.IsTypicalPlankAngle s Y P θ Cθ A) :
    Kakeya.IsTypicalPlankAngle s (fun i => ShadedBody.restrictShade (Y i) G hG) P θ Cθ A := by
  intro x hx
  rw [shadeFibre_restrictShade s Y G hG (mem_of_mem_biUnion_restrictShade hx)]
  exact hty x (mem_biUnion_of_mem_biUnion_restrictShade hx)

end Plank

end
