/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeNoFill

/-!
# A certificate for restoration of the fill condition

The forcing certificate records a family, a node and a restriction for which
the fill condition fails before restriction and holds afterwards. Keeping both
halves at explicit data separates a change of node from a change of family.
The implication below shows what the third clause certifies when restriction
preserves the reading node.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Forcing

/-- **'s forcing record.**  At a **fixed** node, a before/after pair forces the
maximal density to fall: `Δ(·, q)` is monotone in the family, so the only room a restriction has is
on the left of `FillAt`.

Stated on the four scalars rather than on `Kakeya.ML2Core.FillAt`, so that it applies to *any* pair
of families at a common node — including a family and its `Tube.UniformTubeSet.restrictOccupied`
restriction, whose node tubes agree by `Kakeya.ML2Core.restrictOccupied_cover`. -/
theorem fillAt_restrict_forces_maxDensity_lt {κ mDF mDF' dIF dIF' : ℝ≥0∞}
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ⊤)
    (hmono : dIF' ≤ dIF) (hafter : κ * mDF' ≤ dIF') (hbefore : dIF < κ * mDF) :
    mDF' < mDF := by
  have h : κ * mDF' < κ * mDF := lt_of_le_of_lt (hafter.trans hmono) hbefore
  exact (ENNReal.mul_lt_mul_iff_right hκ0 hκtop).mp h

/-- **the fill-restoration certificate, and what it certifies.**  If the restriction **preserves** the
maximal density, then no fixed-node before/after pair can exist — so a certificate carrying clause 3
has demonstrably obtained its rescue by **moving the reading node**, i.e. by `R5`'s mechanism (i),
and not by deleting the concentration (mechanism (ii)).

This is the contrapositive of `Kakeya.ML2Core.fillAt_restrict_forces_maxDensity_lt` and it is the
reason  makes clause 3 the discriminating one. -/
theorem maxDensity_eq_forces_node_change {κ mDF mDF' dIF dIF' : ℝ≥0∞}
    (hκ0 : κ ≠ 0) (hκtop : κ ≠ ⊤) (hpreserve : mDF' = mDF) (hmono : dIF' ≤ dIF) :
    ¬ (κ * mDF' ≤ dIF' ∧ dIF < κ * mDF) := by
  rintro ⟨hafter, hbefore⟩
  exact absurd hpreserve
    (ne_of_lt (fillAt_restrict_forces_maxDensity_lt hκ0 hκtop hmono hafter hbefore))

end Forcing

/-! ### The certificate's shape, for the host to target -/

section Shape

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

open scoped Classical in
/-- ** Fill-restoration certificate: the `T-S2` certificate, as a named target.**

Three clauses on **one** hierarchy and **one** configuration.  `F` is the level-`c` cell family of
the full hierarchy under the coarse node `j` at level `k`; `F'` is the retained family, carried by
the node `jq` at the finer level `q > k`, i.e. at `F'`'s own hull scale.

Naming the target rather than leaving it in prose is deliberate: the host build must hit *this*, and
`Kakeya.ML2Core.maxDensity_eq_forces_node_change` shows that a host hitting clauses 1 and 2
without clause 3 would certify the wrong mechanism. -/
def IsFillSeparationCertificate (𝒰 : Tube.UniformTubeSet s T N C) (κ : ℝ) (c k q : ℕ) (j jq : ι) :
    Prop :=
  k < q ∧
    ¬ FillAt 𝒰 κ k c j ∧
    FillAt 𝒰 κ q c jq ∧
    Kakeya.maxDensity (𝒰.nodesUnder c q jq)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      = Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)

omit [Nontrivial E] in
open scoped Classical in
/-- **A certificate's clauses 1 and 3 already force `q ≠ k`** — the reading node *must* move.  So
the
`k < q` clause of `Kakeya.ML2Core.IsFillSeparationCertificate` is not an extra demand but a
consequence, and recording it is the form 's *"any fixed-node pair witnesses
mechanism (ii)"*. -/
theorem node_ne_of_fillSeparationCertificate (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ}
    {c k q : ℕ} {j jq : ι} (hκ0 : ENNReal.ofReal κ ≠ 0)
    (hmono : Kakeya.densityIn (𝒰.nodesUnder c q jq)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) (𝒰.cover.tube q jq).toConvexSpaceBody
      ≤ Kakeya.densityIn (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) (𝒰.cover.tube q jq).toConvexSpaceBody)
    (hbefore : ¬ FillAt 𝒰 κ k c j) (hafter : FillAt 𝒰 κ q c jq)
    (hpreserve : Kakeya.maxDensity (𝒰.nodesUnder c q jq)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      = Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (hsame : (𝒰.cover.tube q jq).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody) :
    False := by
  classical
  unfold FillAt at hbefore hafter
  rw [hsame] at hafter
  exact maxDensity_eq_forces_node_change hκ0 ENNReal.ofReal_ne_top hpreserve
    (by rw [← hsame]; exact hmono) ⟨hafter, not_le.mp hbefore⟩

end Shape

end Kakeya.ML2Core
