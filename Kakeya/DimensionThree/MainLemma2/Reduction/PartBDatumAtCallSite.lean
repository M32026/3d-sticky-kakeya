/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.Plank.Section6PartBDataBridge

/-!
# The Part-(B) datum at the one application site of GWZ Proposition 6.6(B)

`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank`
(`Kakeya/DimensionThree/Plank/Section6PartBDataBridge.lean`) converts the pair `(PS, Fz)` that
GWZ Proposition 6.6(B) quantifies over into the `Kakeya.Section6PartBData` that the proved
Part-(B) chain consumes.  Two of its hypotheses are *not* carried by Proposition 6.6(B) as
currently stated: the parent window `hballs` and the branching floor `Cpar ^ 2 ≤ PS.branchingN`.

This file measures which of the two the actual call site can pay for, and the answer is settled by
the compiler rather than by reading: **the parent window is already there.**
`Kakeya.ML2Reduction.exists_threshold_eccentric` quantifies over a
`Kakeya.ML2Reduction.PlankFactoringData ρ pa pb C₀ PS.parent PS.parentTube`, whose field
`Kakeya.ML2Reduction.PlankFactoringData.ball` reads

`∀ k ∈ r, (R k).carrier ⊆ Metric.closedBall 0 1`

and is therefore, at `r := PS.parent` and `R := PS.parentTube`, exactly `hballs`.  So adding the
parent window to Proposition 6.6(B) is a **fidelity repair with a supplier already in place**, not
a new obligation pushed onto a caller.  `Kakeya.parentWindow_of_plankFactoringData` pins that.

`Kakeya.Section6PartBData.ofPlankFactoringData` then assembles the whole datum from the datum
`Kakeya.ML2Reduction.PlankFactoringData` that the call site really has, with **the branching floor
as its only residual input**.  The plank parameters are the call site's own, `a = 2 pa` and
`b = min (2 pb) 1`, exactly as `Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization`
declares them, and the transverse constant is the absolute `Cw = 128` of that conversion.

Nothing here proves Proposition 6.6(B); the point is to record, mechanically, which of the two
missing inputs is owed and which is not.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

open Classical in
/-- **The parent window is supplied at the call site**, by the field
`Kakeya.ML2Reduction.PlankFactoringData.ball`. -/
theorem parentWindow_of_plankFactoringData {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar pa pb C₀ : ℝ≥0}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (D : ML2Reduction.PlankFactoringData ρ pa pb C₀ PS.parent PS.parentTube) :
    ∀ k ∈ PS.parent,
      (PS.parentTube k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  D.ball

open Classical in
/-- **The Part-(B) datum, from the data the one application site of GWZ Proposition 6.6(B) actually
has.**

The only hypothesis here that Proposition 6.6(B) does not already carry, or that
`Kakeya.ML2Reduction.PlankFactoringData` does not already supply, is the branching floor `hNC`. -/
def Section6PartBData.ofPlankFactoringData
    {ι : Type} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar pa pb C₀ : ℝ≥0}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (D : ML2Reduction.PlankFactoringData ρ pa pb C₀ PS.parent PS.parentTube)
    (hCpar : 1 ≤ Cpar) (hδρ : δ ≤ ρ) (hNC : Cpar ^ 2 ≤ PS.branchingN)
    (hρ : 0 < ρ) (hq : q.Nonempty)
    (hpa1 : 2 * pa ≤ 1) (hab : 2 * pa ≤ min (2 * pb) 1) :
    Section6PartBData
      (D.toGlobalPlankFactorization hρ hpa1 hab).uniformThin
      (D.toGlobalPlankFactorization hρ hpa1 hab).uniformMid
      (D.toGlobalPlankFactorization hρ hpa1 hab).uniformThin_le_uniformMid
      ((D.toGlobalPlankFactorization hρ hpa1 hab).uniformMid_le_one D.ball)
      q T PS.parent PS.parentTube PS.branchingN (2 * Cpar ^ 2)
      (GlobalPlankFactorization.partBFrostmanConst 128 C₀) C₀ :=
  Section6PartBData.ofUniformAtScaleOfGlobalPlank PS
    (D.toGlobalPlankFactorization hρ hpa1 hab) hCpar hδρ hNC
    (by
      have hpb : 0 < pb := lt_of_lt_of_le (lt_of_lt_of_le hρ D.scale_le) D.thin_le_wide
      exact lt_min (by positivity) one_pos)
    hρ hq D.ball

/-! ### The parent window is not even a hypothesis: a leaf window with `4ρ` of room gives it -/

open Classical in
/-- **The parent window, from a leaf window with room.**

Stronger than `Kakeya.parentWindow_of_plankFactoringData`, and it needs no factorisation datum at
all: the tree already proves that the parents of a single-scale uniformity structure whose leaves
lie in `B̄(0, r)` lie in `B̄(0, r + 4ρ)`
(`Kakeya.ML2Reduction.parentTube_carrier_subset_closedBall`), and every parent carries a leaf as
soon as the leaf family is nonempty (`Kakeya.ML2Reduction.exists_leaf_of_mem_parent` with
`Kakeya.branchingN_pos_of_nonempty`).

**This is the precise sense in which GWZ Proposition 6.6(B)'s leaf window is the wrong radius**, not
the wrong hypothesis: its `∀ i ∈ q, (T i).carrier ⊆ closedBall 0 1` is at `r = 1`, which yields
parents only in `B̄(0, 1 + 4ρ)`; the `4ρ` of slack is exactly what the eccentric chain already
budgets for, in the hypothesis `r + 4 * ρ ≤ 1` of
`Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_of_leafBall`. -/
theorem parentWindow_of_leafWindow {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar : ℝ≥0}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (hq : q.Nonempty) (hρ1 : 2 * (ρ : ℝ) < 1) {r : ℝ} (hr : r + 4 * (ρ : ℝ) ≤ 1)
    (hleaf : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r) :
    ∀ k ∈ PS.parent,
      (PS.parentTube k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  intro k hk
  refine subset_trans ?_ (Metric.closedBall_subset_closedBall hr)
  refine ML2Reduction.parentTube_carrier_subset_closedBall PS hρ1 ?_ ?_ k hk
  · intro j hj
    exact ML2Reduction.exists_leaf_of_mem_parent PS (branchingN_pos_of_nonempty PS hq) hj
  · intro i hi
    simpa using hleaf i hi

open Classical in
/-- **The Part-(B) datum with the parent window replaced by a leaf window.**

`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank'` with `hballs` discharged by
`Kakeya.parentWindow_of_leafWindow`.  The remaining hypotheses are all either derivable inside the
statement of GWZ Proposition 6.6(B) or already carried by the eccentric chain — **except the
branching floor `hNC`**, which is the single residual obligation of the datum conversion. -/
def Section6PartBData.ofUniformAtScaleOfGlobalPlankOfLeafBall
    {ι : Type} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar : ℝ≥0}
    {Cw a b C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
      (fun k => (PS.parentTube k).toConvexSpaceBody) C₀)
    (hδρ : δ ≤ ρ) (hNC : max 1 Cpar ^ 2 ≤ PS.branchingN)
    (hb0 : 0 < b) (hρ : 0 < ρ) (hq : q.Nonempty)
    (hρ1 : 2 * (ρ : ℝ) < 1) {r : ℝ} (hr : r + 4 * (ρ : ℝ) ≤ 1)
    (hleaf : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r) :
    Section6PartBData Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one (parentWindow_of_leafWindow PS hq hρ1 hr hleaf))
      q T PS.parent PS.parentTube PS.branchingN (2 * max 1 Cpar ^ 2)
      (GlobalPlankFactorization.partBFrostmanConst Cw C₀) C₀ :=
  Section6PartBData.ofUniformAtScaleOfGlobalPlank' PS Fz hδρ hNC hb0 hρ hq
    (parentWindow_of_leafWindow PS hq hρ1 hr hleaf)


end Kakeya

end

end
