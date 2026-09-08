/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeSelfHierarchy
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorGateRed

/-!
# Two measurements, with their obstructions (a) and  both say *measure before writing*.  Both answers are negative and
both are here rather than argued.

## Measurement 1  — `boundedOverlap` does **not** reach `LineEDLevelsAt`

`Tube.UniformTubeSet.boundedOverlap` counts, for a **`ρ_k`-tube** `V`, the level-`k` nodes that
share a member of `s` with `V`.  `Kakeya.VeryNotSticky.LineEDLevelsAt K A₁ 𝒰` counts, for a **line**
`L`, the level-`k` nodes **contained in** `Kakeya.VeryNotSticky.lineNbhd p d (K ρ_k)`.  The brief
named two gaps; there are **three**, and the third is fatal.

* **the filter gap — DISCHARGED**, as hoped.  A node contained in the neighbourhood has a member
  (`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent`, needing `s.Nonempty`), and that member
  lies in the node, so "contained in" feeds "shares a member with".
* **the radius gap — PAID** by the floor's existing `Kakeya.Tube.tubeOverlapCoreClose.C 3` row
  (`K ρ_k` against `ρ_k`).
* **the SHAPE gap — FATAL, and the brief did not name it.**  `boundedOverlap`'s test object is a
  `Tube`: **compact, of axis length exactly one**.  `lineNbhd p d r` is the neighbourhood of a
  *whole line* and is **unbounded** — `Kakeya.ML2Core.lineNbhd_not_subset_tube` below.  So no
  single `V` tests it.  Covering it costs: inside the unit ball the neighbourhood still has axis
  extent `≍ 1`, while each `V` admits only nodes whose axis matches to within `ρ_k` (all tubes
  here have length one, so containment pins both endpoints).  The covering number is therefore
  `≍ ρ_k^{-1}` — **a polynomial in `δ`**, and a `Cu · ρ_k^{-1}` bound is not `LineEDLevelsAt`.

> **Verdict: `boundedOverlap` does not give `LineEDLevelsAt` for free.**  Per the brief I have not
> written a producer.  The shortfall is not a constant but a `δ`-power, so it is not absorbable and
> the producer needs a genuinely different input (a line-parameter count, not a tube-overlap count).

## Measurement 2  — `X2′` gives the **scale**, not the **node**

`R5`'s `hretain` asks that a grid node's `nodesUnder` be *exactly* the cells inside the maximizer's
hull.  `X2′` is `Kakeya.ML2Core.le_ethickness_of_tube_le`:

```
    V.toConvexSpaceBody ≤ W  →  (ρ : ENNReal) ≤ ethickness ℝ W.carrier n
```

— a **thickness lower bound on the hull**.  It locates the grid *scale* at which a node could match
the hull and says nothing whatever about *where* such a node sits or which cells it contains.

> **Verdict: `X2′` yields neither the `Finset` equality nor `⊇`.**  the escape
> (`Kakeya.ML2Core.fillAt_of_biasedMaximizer_supseteq`, existing the estimate) weakens `hretain` to `⊇`, but
> **even `⊇` is not free from `X2′`** — it needs a node at that scale *containing the hull*, which
is
> a positioning statement.  `Kakeya.ML2Core.thickness_does_not_give_containment` is the > control: two bodies can be equally thick with neither inside the other.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section LineGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Measurement 1's obstruction: a line neighbourhood is unbounded, a tube is not.**

`Tube.UniformTubeSet.boundedOverlap`'s test object is a `Tube`, whose carrier is compact; the object
`Kakeya.VeryNotSticky.LineEDLevelsAt` tests against is the neighbourhood of a whole line.  **No
single `V` can play the part**, so the two counts are not comparable term by term and the passage
costs a covering number — which, all tubes having axis length one, is `≍ ρ_k^{-1}`. -/
theorem lineNbhd_not_subset_tube {ρ : NNReal} (V : Tube ρ E) (p d : E) (hd : ‖d‖ = 1) (r : ℝ) :
    ¬ (Kakeya.VeryNotSticky.lineNbhd p d r ⊆ V.carrier) := by
  intro hsub
  have hline : Kakeya.VeryNotSticky.lineSet p d ⊆ V.carrier := by
    refine subset_trans ?_ hsub
    exact Metric.self_subset_cthickening _
  have hbdd : Bornology.IsBounded (Kakeya.VeryNotSticky.lineSet p d) :=
    V.isCompact'.isBounded.subset hline
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall p
  have hmem : p + (R + 1) • d ∈ Kakeya.VeryNotSticky.lineSet p d :=
    Kakeya.VeryNotSticky.mem_lineSet p d (R + 1)
  have hdist : dist (p + (R + 1) • d) p ≤ R := by
    simpa using hR hmem
  have hR0 : (0 : ℝ) ≤ R := le_trans dist_nonneg hdist
  rw [dist_eq_norm, show p + (R + 1) • d - p = (R + 1) • d from by abel, norm_smul,
    Real.norm_eq_abs, hd, mul_one, abs_of_nonneg (by linarith)] at hdist
  linarith

end LineGap

section ThicknessGap

/-- **Measurement 2's control: thickness does not give containment.**  `X2′` concludes a thickness
lower bound; two bodies can meet the same lower bound with neither contained in the other, so no
`hretain`-shaped conclusion — equality *or* `⊇` — follows from it.

Witness: two distinct translates of the red leaf, which are **disjoint**
(`Kakeya.ML2Core.disjoint_redLeaf`) and nonempty, so neither contains the
other. -/
theorem thickness_does_not_give_containment {δ : NNReal} (hδ : 0 < δ) :
    ¬ ((redLeaf δ 0).carrier ⊆ (redLeaf δ 1).carrier) := by
  intro hsub
  have hdisj := disjoint_redLeaf hδ (n := 0) (m := 1) (by norm_num)
  have hne := (redLeaf δ 0).toConvexSpaceBody.nonempty
  obtain ⟨x, hx⟩ := hne
  exact (Set.disjoint_left.mp hdisj hx) (hsub hx)

end ThicknessGap

end Kakeya.ML2Core
