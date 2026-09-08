/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankPartBBridge
public import Kakeya.Factoring.RhoFreeParentCount
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# GWZ Proposition 6.6(B) is not vacuous

`Kakeya.tubeMultiplicityOfLocalPlankFactorisation` (GWZ 6.6(A)) is **vacuously** true: its
hypotheses are contradictory over a nonempty family
(`Kakeya.localPlankFactorisation_proves_anything`).  The repaired 6.6(B) datum
`Kakeya.GlobalPlankFactorization` was introduced precisely to avoid that, and its docstring argues
informally that it is satisfiable — but nothing in this development ever *constructed* one, nor a
`Kakeya.ComparableBodyFactorization`, nor a `Kakeya.GlobalComparableBodyFactorization`.  All three
carry a `wide` field asking for a `Kakeya.ContainsFlatDisc` of a **convex hull of tubes**, and the
only producer of `Kakeya.ContainsFlatDisc` in the development is
`Kakeya.Prism3D.containsFlatDisc`, which produces one for an **exact prism**.  So the `wide` clause
had never been supplied for the bodies it is actually asked of.

This file supplies it, and the datum.

* `Kakeya.containsFlatDisc_of_closedBall_subset` — a producer for round bodies: a set containing a
  ball of radius `r` contains a flat disc of radius `r`.  The two-plane is the orthogonal
  complement of a line, whose rank is `3 - 1 = 2`.  This is the shape `wide` needs, because the
  bodies of a `Kakeya.GlobalPlankFactorization` are hulls of tubes, which are round, not boxes.
* `Kakeya.Tube.containsFlatDisc` — a `ρ`-tube contains a flat `ρ`-disc, because it contains the
  `ρ`-ball around its own endpoint.
* `Kakeya.exists_globalPlankFactorization_singleton` — **the inhabitation certificate**: for every
  `ρ`-tube `R` inside the unit ball with `0 < ρ ≤ 1`, the one-member coarse family `{k}` carries a
  `Kakeya.GlobalPlankFactorization 1 ρ ρ … 2`.  All of `isKatzTao`, `maxDensity_le_mul`, `simDims`,
  `le_plank` and `wide` hold simultaneously, at the absolute constants `Cw = 1` and `C₀ = 2`.

So GWZ 6.6(B) is **not** vacuous in the way 6.6(A) is, and
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation` is not a map out of an empty type.

The certificate uses the framed plank of `Kakeya/DimensionThree/Plank/GlobalPlankPartBBridge.lean`
for `le_plank`, which is why the two files travel together.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Metric

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-! ### The first producer of `Kakeya.ContainsFlatDisc` -/

/-- **A set containing a ball of radius `r` contains a flat disc of radius `r`.**

The two-plane is `(ℝ ∙ e₀)ᗮ`, whose rank is `3 - 1 = 2`.  Nothing else in this development
constructs a `Kakeya.ContainsFlatDisc`; every prior occurrence consumes one. -/
theorem containsFlatDisc_of_closedBall_subset {r : ℝ≥0} {c : EuclideanSpace ℝ (Fin 3)}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : Metric.closedBall c (r : ℝ) ⊆ S) :
    ContainsFlatDisc r S := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  set v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ) with hv_def
  have hv : v ≠ 0 := by
    intro hzero
    have := congrFun (congrArg WithLp.ofLp hzero) 0
    simp [hv_def] at this
  refine ⟨c, (ℝ ∙ v)ᗮ, Submodule.finrank_orthogonal_span_singleton hv, ?_⟩
  intro w _ hw
  refine h ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa using hw

/-- **A `ρ`-tube contains a flat `ρ`-disc.**  Its carrier is the union of the `ρ`-balls around the
points of its core segment, and its own endpoint is such a point. -/
theorem Tube.containsFlatDisc {ρ : ℝ≥0} (T : Tube ρ (EuclideanSpace ℝ (Fin 3))) :
    ContainsFlatDisc ρ (T.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  refine containsFlatDisc_of_closedBall_subset (c := T.x) ?_
  intro p hp
  rw [T.carrier_eq]
  exact Set.mem_biUnion (left_mem_segment ℝ T.x T.y) hp

/-! ### The non-vacuity certificate -/

/-- **The factorisation datum of GWZ Proposition 6.6(B) is inhabited.**

For every `ρ`-tube `R k` inside the unit ball with `0 < ρ ≤ 1`, the singleton coarse family `{k}`
carries a `Kakeya.GlobalPlankFactorization` with `Cw = 1` and `C₀ = 2`, at the declared half-widths
`a = b = ρ`.

The comparison with 6.6(A) is exact, and it is at the level of the *datum*:
`Kakeya.localPlankFactorisation_hypotheses_uninhabited` derives `False` from 6.6(A)'s
factorisation block alone (`0 < δ`, `q` nonempty, the assignment clause, the local
`Kakeya.PlankFactorization`s), so 6.6(A)'s datum is *empty*.  6.6(B)'s datum is not, and this
theorem is the compiler-checked witness.

This certifies the factorisation datum, which is the clause that was in doubt; it says nothing
about the remaining hypotheses of the 6.6(B) statement (the shaded fine family, its uniformity and
fullness, and the coarse parent structure), which are standard and are not in question.

The three `ConvexSpaceBody.Factorization` clauses come from
`Kakeya.exists_factorization_singleton` (the indiscrete partition of a one-member family
factorises at the constant `2`); `le_plank` is the framed plank of the tube, which exists because
a tube of radius `ρ ≤ 1` has both transverse thicknesses at most `ρ` and lies in the unit ball; and
`wide` is `Kakeya.Tube.containsFlatDisc` together with `min ρ (1 / 2) / 1 ≤ ρ`. -/
theorem exists_globalPlankFactorization_singleton {κ : Type*} [DecidableEq κ] {ρ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (Rt : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (k : κ)
    (hball : ((Rt k).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1) :
    Nonempty (GlobalPlankFactorization 1 ρ ρ le_rfl hρ1 ({k} : Finset κ)
      (fun j => (Rt j).toConvexSpaceBody) 2) := by
  classical
  -- the coarse tube has positive, finite volume
  have hvolpos : 0 < volume ((Rt k).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    refine lt_of_lt_of_le ?_ (Tube.le_volume (Rt k))
    have hc : (0 : ℝ≥0) < Tube.le_volume.c (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
      Tube.le_volume.c_pos _
    refine zero_lt_iff.mpr (mul_ne_zero (ENNReal.coe_ne_zero.mpr hc.ne') ?_)
    exact pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hρ0.ne')
  have hvoltop : volume ((Rt k).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
    (Rt k).isCompact'.measure_lt_top.ne
  obtain ⟨F, hFparts⟩ :=
    exists_factorization_singleton (fun j => (Rt j).toConvexSpaceBody) k hvolpos hvoltop
  -- transverse thicknesses of a tube
  have h1 : thicknessNN ((Rt k).toConvexSpaceBody) 1 ≤ ρ :=
    thicknessNN_le_of_ethickness_le (Tube.ethickness_one_le (Rt k))
  have h2 : thicknessNN ((Rt k).toConvexSpaceBody) 2 ≤ ρ :=
    le_trans (thicknessNN_antitone _ (by norm_num)) h1
  have hhull : ({k} : Finset κ).convexHull_biUnion (fun j => (Rt j).toConvexSpaceBody)
      = (Rt k).toConvexSpaceBody :=
    Finset.convexHull_biUnion_singleton (fun j => (Rt j).toConvexSpaceBody) k
  refine ⟨{ toFactorization := F
            one_le_Cw := le_rfl
            le_plank := ?_
            wide := ?_ }⟩
  · intro part hpart
    rw [hFparts, Finset.mem_singleton] at hpart
    subst hpart
    refine ⟨framedPlank ((Rt k).toConvexSpaceBody) ρ ρ le_rfl hρ1, ?_⟩
    rw [hhull]
    exact le_framedPlank le_rfl hρ1 h2 h1 hball
  · intro part hpart
    rw [hFparts, Finset.mem_singleton] at hpart
    subst hpart
    have hdisc : ContainsFlatDisc ρ
        ((({k} : Finset κ).convexHull_biUnion
          (fun j => (Rt j).toConvexSpaceBody)).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [hhull]
      exact Tube.containsFlatDisc (Rt k)
    refine hdisc.mono ?_
    rw [div_one]
    exact min_le_left _ _

end Kakeya

end

end
