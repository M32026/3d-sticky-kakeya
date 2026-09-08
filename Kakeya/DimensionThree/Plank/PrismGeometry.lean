/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization

/-!
# Geometry of flat `a × b × c` prisms

Harvested from the `merge_try` development.  This file collects the elementary Euclidean geometry
of a `Kakeya.Prism3D`, together with the two comparisons between a prism and a `Kakeya.Tube` that
the Section 6 factorisation arguments consume.  Nothing here depends on any factorisation datum;
every declaration is a statement about one prism, one tube, or one flat disc.

## Contents

* **Coordinates.**  `Kakeya.Prism3D.abs_repr_le` / `Kakeya.Prism3D.mem_of_abs_repr_le` are the
  `-ᵥ`-free membership criterion, and `Kakeya.Prism3D.corner` is the vertex at which all three
  defining inequalities are tight.
* **The transverse (rank-`2`) width.**  `Kakeya.Prism3D.ethickness_two_le` bounds it by the
  smallest half-width `a`; with `Kakeya.Tube.rho_le_of_le_prism3D` this gives the scale relation
  `ρ ≤ a` for a `ρ`-tube inside an `a × b × c` prism.
* **The corner obstruction.**  `Kakeya.Prism3D.ne_convexHull_biUnion_tubes`: for `0 < ρ`, the
  convex hull of a nonempty finite union of `ρ`-tubes is never an exact prism.  (This is the
  public, `Finset.convexHull_biUnion`-shaped companion of the private
  `convexHull_tubes_ne_prism` in `Kakeya/DimensionThree/Plank/Factorization.lean`.)
* **The long plane and flat discs.**  `Kakeya.Prism3D.mem_add_smul_mem_longPlane`,
  `Kakeya.Prism3D.containsFlatDisc` (every prism contains a flat disc of radius its *middle*
  half-width `b`), and the longitudinal (rank-`1`) lower bounds
  `Kakeya.Prism3D.b_le_ethickness_one`, `Kakeya.ContainsFlatDisc.le_ethickness_one`.  These give
  `b ≤ ρ` for a prism (or any set with a flat `b`-disc) inside a `ρ`-tube:
  `Kakeya.Plank.b_le_of_le_tube`, `Kakeya.ContainsFlatDisc.le_of_subset_tube`.
* **Tube-shapedness.**  `Kakeya.IsTubeShaped r K` says `K` lies inside *some* tube of radius `r`.
  `Kakeya.Prism3D.isTubeShaped` proves it, with `r = a + b`, for any prism whose long half-width is
  at most `1/2` — i.e. for the paper's normalisation of an `a × b × 1` plank as an object of
  longitudinal *extent* `1`.  `Kakeya.Plank.half_le_of_le_tube` is the matching negative result for
  the Lean `Plank a b = Prism3D a b 1`, whose longitudinal extent is `2`.
* **Two counting lemmas** used by the Section 6 slab non-concentration step:
  `Kakeya.card_le_of_comparable_fibres` and `Kakeya.card_le_of_frostmanIn`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-- A `δ`-tube contains the closed `δ`-ball about its centre, since the centre lies on its axis and
the carrier is the union of the `δ`-balls about the points of that axis.  Hence any set containing
the tube contains that ball. -/
theorem Plank.closedBall_center_subset_of_tube {δ : ℝ≥0}
    (T : Tube δ (EuclideanSpace ℝ (Fin 3)))
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hT : T.carrier ⊆ K) :
    Metric.closedBall T.center (δ : ℝ) ⊆ K := by
  refine subset_trans ?_ hT
  rw [T.carrier_eq]
  have hmem : T.center ∈ segment ℝ T.x T.y := midpoint_mem_segment T.x T.y
  exact Set.subset_biUnion_of_mem
    (u := fun z : EuclideanSpace ℝ (Fin 3) => Metric.closedBall z (δ : ℝ)) hmem

/-! ### Coordinates of a `Prism3D` -/

/-- The defining inequalities of a `Prism3D`, in the `-ᵥ`-free form used below: a point of the
carrier has all its basis coordinates bounded by the corresponding half-width. -/
theorem Prism3D.abs_repr_le {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ P.carrier) (j : Fin 3) :
    |P.basis.repr (x -ᵥ P.center) j| ≤ (P.thicknesses j : ℝ) :=
  (P.mem_carrier_iff x).1 hx j

/-- A point whose basis coordinates are all bounded by the half-widths lies in the carrier. -/
theorem Prism3D.mem_of_abs_repr_le {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ∀ j, |P.basis.repr (x -ᵥ P.center) j| ≤ (P.thicknesses j : ℝ)) : x ∈ P.carrier :=
  (P.mem_carrier_iff x).2 hx

/-- **The corner of a `Prism3D`.**  The point whose basis coordinates are exactly the half-widths.
It is the vertex of the box at which all three defining inequalities are tight. -/
def Prism3D.corner {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c} (P : Prism3D a b c hab hbc) :
    EuclideanSpace ℝ (Fin 3) :=
  P.center + P.basis.repr.symm (WithLp.toLp 2 fun j => (P.thicknesses j : ℝ))

/-- The corner has basis coordinates equal to the half-widths. -/
theorem Prism3D.repr_corner {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) (j : Fin 3) :
    P.basis.repr (Prism3D.corner P -ᵥ P.center) j = (P.thicknesses j : ℝ) := by
  rw [Prism3D.corner]
  simp only [vsub_eq_sub, add_sub_cancel_left]
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- The corner belongs to the carrier. -/
theorem Prism3D.corner_mem {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) : Prism3D.corner P ∈ P.carrier := by
  refine Prism3D.mem_of_abs_repr_le P (fun j => ?_)
  rw [Prism3D.repr_corner P j, abs_of_nonneg (NNReal.coe_nonneg (P.thicknesses j))]

/-- **A ball inside a `Prism3D` is `ρ`-far from every face.**  If the closed ball of radius `ρ`
about `y` lies in the carrier then each basis coordinate of `y` is at most `half-width − ρ`. -/
theorem Prism3D.repr_add_le_of_closedBall_subset {a b c ρ : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) {y : EuclideanSpace ℝ (Fin 3)}
    (hy : Metric.closedBall y (ρ : ℝ) ⊆ P.carrier) (j : Fin 3) :
    P.basis.repr (y -ᵥ P.center) j + (ρ : ℝ) ≤ (P.thicknesses j : ℝ) := by
  set x : EuclideanSpace ℝ (Fin 3) := y + (ρ : ℝ) • P.basis j
  have hxmem_closed : x ∈ Metric.closedBall y (ρ : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hxx : x - y = (ρ : ℝ) • P.basis j := by
      simp [x, sub_eq_add_neg, add_left_comm, add_comm]
    have habs : |(ρ : ℝ)| = (ρ : ℝ) := abs_of_nonneg ρ.2
    rw [hxx, norm_smul, Real.norm_eq_abs, habs, P.basis.norm_eq_one j, mul_one]
  have hxcarrier : x ∈ P.carrier := hy hxmem_closed
  have hbnd : |P.basis.repr (x -ᵥ P.center) j| ≤ (P.thicknesses j : ℝ) :=
    Prism3D.abs_repr_le P hxcarrier j
  have hlhs : P.basis.repr (x -ᵥ P.center) j = P.basis.repr (y -ᵥ P.center) j + (ρ : ℝ) := by
    rw [vsub_eq_sub]
    have hxc : x - P.center = (y - P.center) + (ρ : ℝ) • P.basis j := by
      simp [x, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hxc]
    simp [map_add, map_smul, P.basis.repr_self]
  rw [hlhs] at hbnd
  exact (abs_le.mp hbnd).2

/-! ### The least width of a plank, and the scale relation `ρ ≤ a` -/

/-- The rank-`2` `ethickness` of a `Prism3D` is at most its smallest half-width `a`: the carrier
lies within `a` of its own tangent plane, which is a two-dimensional affine subspace. -/
theorem Prism3D.ethickness_two_le {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) : Metric.ethickness ℝ P.carrier 2 ≤ (a : ENNReal) := by
  apply Metric.ethickness_le_of_cthickening (r := a) (A := P.tangentPlane)
  · rw [AffineSubspace.direction_mk']
    rw [← Module.finrank_eq_rank, P.finrank_longPlane]
  · exact P.carrier_subset_cthickening_tangentPlane

/-- **Part (B)'s scale relation, geometric core.**  A `ρ`-tube contained in an `a × b × c` prism
forces `ρ ≤ a`.

The tube contains the ball of radius `ρ` about its centre, whose rank-`2` `ethickness` is `ρ`
(`Metric.le_ethickness_closedBall`, `2 < 3`), while the prism has rank-`2` `ethickness` at most `a`
(`Kakeya.Prism3D.ethickness_two_le`).

This is the *mirror image* of `Kakeya.Plank.b_le_of_le_tube`, which bounds `b ≤ ρ` for a plank
inside a `ρ`-tube.  In Proposition 6.6(A) the plank is the inner body and the tube the outer one, so
`ρ ≤ a` is false there; in Proposition 6.6(B) the tube is the inner body, so `ρ ≤ a` is forced. -/
theorem Tube.rho_le_of_le_prism3D {a b c ρ : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3))) (P : Prism3D a b c hab hbc)
    (h : R.toConvexSpaceBody ≤ P.toConvexSpaceBody) : ρ ≤ a := by
  have hcarrier : (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    (SetLike.coe_subset_coe (S := R.toConvexSpaceBody)
      (T := P.toConvexSpaceBody)).mp h
  have hsub : Metric.closedBall R.center (ρ : ℝ) ⊆ P.carrier :=
    Plank.closedBall_center_subset_of_tube R hcarrier
  have hρ_eth : (ρ : ENNReal) ≤ Metric.ethickness ℝ (Metric.closedBall R.center ρ) 2 := by
    exact le_ethickness_closedBall ρ (by
      rw [finrank_euclideanSpace_fin]; norm_num)
  have hmono : Metric.ethickness ℝ (Metric.closedBall R.center ρ) 2 ≤
      Metric.ethickness ℝ P.carrier 2 := by
    exact Metric.ethickness_monotone hsub 2
  have hle : (ρ : ENNReal) ≤ (a : ENNReal) := by
    calc
      (ρ : ENNReal) ≤ Metric.ethickness ℝ (Metric.closedBall R.center ρ) 2 := hρ_eth
      _ ≤ Metric.ethickness ℝ P.carrier 2 := hmono
      _ ≤ (a : ENNReal) := Prism3D.ethickness_two_le P
  exact ENNReal.coe_le_coe.mp hle

/-! ### The corner obstruction: no hull of `ρ`-tubes is an exact prism -/

/-- A point of a `ρ`-tube is within `ρ` of a point of the axis segment whose `ρ`-ball is contained
in the tube. -/
theorem Tube.exists_axis_point_closedBall_subset {ρ : ℝ≥0}
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3))) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ R.carrier) :
    ∃ y : EuclideanSpace ℝ (Fin 3), ‖x - y‖ ≤ (ρ : ℝ) ∧
      Metric.closedBall y (ρ : ℝ) ⊆ R.carrier := by
  rw [R.carrier_eq] at hx
  obtain ⟨y, hy_seg, hxy⟩ := Set.mem_iUnion₂.mp hx
  refine ⟨y, ?_, ?_⟩
  · simpa [Metric.mem_closedBall, dist_eq_norm] using hxy
  · rw [R.carrier_eq]
    exact Set.subset_biUnion_of_mem (u := fun z : EuclideanSpace ℝ (Fin 3) =>
      Metric.closedBall z (ρ : ℝ)) hy_seg

/-- **The corner obstruction, one tube.**  A `ρ`-tube inside an `a × b × c` prism contains no point
at which two of the defining inequalities are tight, unless `ρ = 0`.

Such a point `x` is within `ρ` of an axis point `y` whose `ρ`-ball lies in the prism, so `x - y` has
two basis coordinates at least `ρ`; Parseval then gives `2ρ² ≤ ‖x - y‖² ≤ ρ²`. -/
theorem Tube.not_two_tight_of_le_prism3D {a b c ρ : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (hρ : 0 < ρ) (R : Tube ρ (EuclideanSpace ℝ (Fin 3))) (P : Prism3D a b c hab hbc)
    (hRP : R.toConvexSpaceBody ≤ P.toConvexSpaceBody)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ R.carrier)
    (h0 : (P.thicknesses 0 : ℝ) ≤ P.basis.repr (x -ᵥ P.center) 0)
    (h1 : (P.thicknesses 1 : ℝ) ≤ P.basis.repr (x -ᵥ P.center) 1) : False := by
  obtain ⟨y, hxy, hyball⟩ := Tube.exists_axis_point_closedBall_subset R hx
  have hcarrier : (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    (SetLike.coe_subset_coe (S := R.toConvexSpaceBody) (T := P.toConvexSpaceBody)).mp hRP
  have hyP : Metric.closedBall y (ρ : ℝ) ⊆ P.carrier := subset_trans hyball hcarrier
  let u : EuclideanSpace ℝ (Fin 3) := x - y
  let v : EuclideanSpace ℝ (Fin 3) := P.basis.repr u
  have hpart (j : Fin 3) (ht : (P.thicknesses j : ℝ) ≤ P.basis.repr (x -ᵥ P.center) j) :
      (ρ : ℝ) ≤ P.basis.repr (x - y) j := by
    have hbar : P.basis.repr (y -ᵥ P.center) j + (ρ : ℝ) ≤ (P.thicknesses j : ℝ) :=
      Prism3D.repr_add_le_of_closedBall_subset P hyP j
    have hcompat : P.basis.repr (x - y) j = P.basis.repr (x -ᵥ P.center) j -
        P.basis.repr (y -ᵥ P.center) j := by
      have hΔ : (x -ᵥ P.center) - (y -ᵥ P.center) = x - y := by
        simpa [vsub_eq_sub, sub_eq_add_neg, neg_sub, add_assoc, add_comm, add_left_comm,
          add_neg_cancel, sub_add_cancel]
      rw [← hΔ]
      simpa using map_sub P.basis.repr (x -ᵥ P.center) (y -ᵥ P.center)
    rw [hcompat]
    nlinarith [hbar, ht]
  have hbig0 : (ρ : ℝ) ≤ v 0 := by
    simpa [v, u] using hpart 0 h0
  have hbig1 : (ρ : ℝ) ≤ v 1 := by
    simpa [v, u] using hpart 1 h1
  have hiso : ‖u‖ = ‖v‖ := by
    simpa [v] using (LinearIsometryEquiv.norm_map P.basis.repr u).symm
  have hnorm : ‖u‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
    calc
      ‖u‖ ^ 2 = ‖v‖ ^ 2 := by rw [hiso]
      _ = ∑ i : Fin 3, (v i) ^ 2 := EuclideanSpace.real_norm_sq_eq v
      _ = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by rw [Fin.sum_univ_three]
  have hρ0 : 0 ≤ (ρ : ℝ) := by positivity
  have hv00 : 0 ≤ v 0 := le_trans hρ0 hbig0
  have hv10 : 0 ≤ v 1 := le_trans hρ0 hbig1
  have hsq0 : (ρ : ℝ) ^ 2 ≤ (v 0) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg hρ0, abs_of_nonneg hv00]; exact hbig0)
  have hsq1 : (ρ : ℝ) ^ 2 ≤ (v 1) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg hρ0, abs_of_nonneg hv10]; exact hbig1)
  have h2 : 2 * (ρ : ℝ) ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [hnorm]
    nlinarith [hsq0, hsq1, sq_nonneg (v 2)]
  have hleu : ‖u‖ ≤ (ρ : ℝ) := by
    simpa [u] using hxy
  have h1sq : ‖u‖ ^ 2 ≤ (ρ : ℝ) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg (norm_nonneg u), abs_of_nonneg hρ0]; exact hleu)
  have hc : 2 * (ρ : ℝ) ^ 2 ≤ (ρ : ℝ) ^ 2 := le_trans h2 h1sq
  have hpos : 0 < (ρ : ℝ) ^ 2 := sq_pos_of_pos (show (0 : ℝ) < (ρ : ℝ) by exact_mod_cast hρ)
  nlinarith

/-- **The corner obstruction.**  For `0 < ρ`, the convex hull of a nonempty finite union of
`ρ`-tubes is never an exact `a × b × c` prism.

The prism's corner lies in the hull, so it is a positive convex combination of points of the union;
since every one of the corner's basis coordinates is maximal over the prism, every point occurring
in the combination has two tight coordinates, and lies in some tube.
`Kakeya.Tube.not_two_tight_of_le_prism3D` rules that out.

This is what makes the `Kakeya.PlankFactorization` hypothesis of Proposition 6.6(B) unsatisfiable,
and it is *not* the part-(A) obstruction: no longitudinal comparison is used, and the conclusion is
`ρ = 0` rather than `1/2 ≤ ρ`. -/
theorem Prism3D.ne_convexHull_biUnion_tubes {ι : Type*} {a b c ρ : ℝ≥0}
    {hab : a ≤ b} {hbc : b ≤ c} (hρ : 0 < ρ) {s : Finset ι} (hs : s.Nonempty)
    (R : ι → Tube ρ (EuclideanSpace ℝ (Fin 3))) (P : Prism3D a b c hab hbc) :
    Finset.convexHull_biUnion s (fun i => (R i).toConvexSpaceBody) ≠ P.toConvexSpaceBody := by
  intro hEq
  let K : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (R i).toConvexSpaceBody.carrier
  have hH : (Finset.convexHull_biUnion s (fun i => (R i).toConvexSpaceBody)).carrier =
      Convexity.convexHull ℝ K := by
    change (Finset.convexHull_biUnion s (fun i => (R i).toConvexSpaceBody)).carrier =
      Convexity.convexHull ℝ (⋃ i ∈ s, (R i).toConvexSpaceBody.carrier)
    exact hs.convexHull_biUnion_carrier (fun i => (R i).toConvexSpaceBody)
  have hEqc : (Finset.convexHull_biUnion s (fun i => (R i).toConvexSpaceBody)).carrier
      = P.carrier := by
    exact congrArg (fun B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) => B.carrier) hEq
  have hcorner : Prism3D.corner P ∈ Convexity.convexHull ℝ K := by
    rw [← hH, hEqc]
    exact Prism3D.corner_mem P
  have hcorner' : Prism3D.corner P ∈ _root_.convexHull ℝ K := by
    rw [← Convexity.convexHull_eq_convexHull]
    exact hcorner
  obtain ⟨κ, hFI, z, w, hrange, _haff, hwpos, hwsum, hwzsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull hcorner'
  letI : Fintype κ := hFI
  have hzK : ∀ a, z a ∈ K := fun a => hrange ⟨a, rfl⟩
  have hRP : ∀ i ∈ s, (R i).toConvexSpaceBody ≤ P.toConvexSpaceBody := by
    intro i hi
    calc
      (R i).toConvexSpaceBody ≤ Finset.convexHull_biUnion s (fun i => (R i).toConvexSpaceBody) :=
        Finset.le_convexHull_biUnion (fun i => (R i).toConvexSpaceBody) hi
      _ = P.toConvexSpaceBody := hEq
  have hKP : K ⊆ P.carrier := by
    intro x hx
    change x ∈ ⋃ i ∈ s, (R i).toConvexSpaceBody.carrier at hx
    rcases (Set.mem_iUnion₂.mp hx) with ⟨i, hi, hxRi⟩
    exact (hRP i hi) hxRi
  have hzP : ∀ a, z a ∈ P.carrier := fun a => hKP (hzK a)
  have habs : ∀ a (j : Fin 3), |P.basis.repr (z a - P.center) j| ≤ (P.thicknesses j : ℝ) := by
    intro a j
    exact Prism3D.abs_repr_le P (hzP a) j
  have hle : ∀ a (j : Fin 3), P.basis.repr (z a - P.center) j ≤ (P.thicknesses j : ℝ) := by
    intro a j
    exact (le_abs_self _).trans (habs a j)
  have htight : ∀ (j : Fin 3) (a : κ),
      P.basis.repr (z a - P.center) j = (P.thicknesses j : ℝ) := by
    intro j a
    have hsum_eq : (∑ a : κ, w a • (z a - P.center)) = Prism3D.corner P - P.center := by
      have hc : (∑ a : κ, w a • P.center) = P.center := by
        rw [← Finset.sum_smul, hwsum, one_smul]
      calc
        (∑ a : κ, w a • (z a - P.center))
            = ∑ a : κ, (w a • z a - w a • P.center) := by
              apply Finset.sum_congr rfl; intro a _; rw [smul_sub]
        _ = (∑ a : κ, w a • z a) - (∑ a : κ, w a • P.center) := by rw [Finset.sum_sub_distrib]
        _ = Prism3D.corner P - P.center := by rw [hwzsum, hc]
    have hpow : (∑ a : κ, w a * P.basis.repr (z a - P.center) j) = (P.thicknesses j : ℝ) := by
      calc
        (∑ a : κ, w a * P.basis.repr (z a - P.center) j)
            = P.basis.repr (∑ a : κ, w a • (z a - P.center)) j := by
              rw [map_sum]
              simp only [map_smul]
              simp [Finset.sum_apply]
        _ = P.basis.repr (Prism3D.corner P - P.center) j := by rw [hsum_eq]
        _ = (P.thicknesses j : ℝ) := by simpa using (Prism3D.repr_corner P j)
    by_contra hne
    have hlt : P.basis.repr (z a - P.center) j < (P.thicknesses j : ℝ) :=
      lt_of_le_of_ne (hle a j) hne
    have hSnn : ∀ b : κ,
        0 ≤ w b * ((P.thicknesses j : ℝ) - P.basis.repr (z b - P.center) j) := by
      intro b
      exact mul_nonneg (le_of_lt (hwpos b)) (sub_nonneg.mpr (hle b j))
    have hSsum : (∑ b : κ, w b * ((P.thicknesses j : ℝ)
          - P.basis.repr (z b - P.center) j)) = 0 := by
      calc
        (∑ b : κ, w b * ((P.thicknesses j : ℝ) - P.basis.repr (z b - P.center) j))
            = ∑ b : κ, (w b * (P.thicknesses j : ℝ) - w b * P.basis.repr (z b - P.center) j) := by
              apply Finset.sum_congr rfl; intro b _; rw [mul_sub]
        _ = (∑ b : κ, w b * (P.thicknesses j : ℝ))
                - (∑ b : κ, w b * P.basis.repr (z b - P.center) j) := by
              rw [Finset.sum_sub_distrib]
        _ = (P.thicknesses j : ℝ) - (P.thicknesses j : ℝ) := by
              rw [← Finset.sum_mul, hwsum, hpow]; ring
        _ = 0 := by ring
    have hposA : 0 < w a * ((P.thicknesses j : ℝ) - P.basis.repr (z a - P.center) j) := by
      exact mul_pos (hwpos a) (sub_pos.mpr hlt)
    have hge : w a * ((P.thicknesses j : ℝ) - P.basis.repr (z a - P.center) j)
        ≤ ∑ b : κ, w b * ((P.thicknesses j : ℝ) - P.basis.repr (z b - P.center) j) := by
      exact Finset.single_le_sum (by intro b _; exact hSnn b) (Finset.mem_univ a)
    linarith
  have hκ : Nonempty κ := by
    by_contra hbot
    haveI : IsEmpty κ := not_nonempty_iff.mp hbot
    have hε : (Finset.univ : Finset κ) = (∅ : Finset κ) := by
      ext x
      exact (IsEmpty.false x).elim
    have h₀ : (∑ a : κ, w a) = 0 := by
      rw [hε, Finset.sum_empty]
    rw [hwsum] at h₀
    norm_num at h₀
  let a₀ : κ := Classical.choice hκ
  have hz₀ : z a₀ ∈ K := hzK a₀
  obtain ⟨i₀, hi₀, hzRi₀⟩ : ∃ i ∈ s, z a₀ ∈ (R i).toConvexSpaceBody.carrier := by
    change z a₀ ∈ ⋃ i ∈ s, (R i).toConvexSpaceBody.carrier at hz₀
    simpa using (Set.mem_iUnion₂.mp hz₀)
  have htight0 : (P.thicknesses 0 : ℝ) ≤ P.basis.repr (z a₀ - P.center) 0 := by
    exact (htight 0 a₀).ge
  have htight1 : (P.thicknesses 1 : ℝ) ≤ P.basis.repr (z a₀ - P.center) 1 := by
    exact (htight 1 a₀).ge
  exact Tube.not_two_tight_of_le_prism3D hρ (R i₀) P (hRP i₀ hi₀) hzRi₀ htight0 htight1
/-! ### The Scale comparison: a plank inside a coarse tube is thin -/

/-- A `Prism3D` contains the flat disc of radius `b` in the affine plane through its centre spanned
by `basis 1` and `basis 2`.  This is the `longPlane` companion of
`Kakeya.Prism3D.mem_add_smul_mem_longAxis`, whose proof it copies: the `basis 0` coordinate
vanishes because the long plane is the orthogonal complement of `basis 0`, and the `basis 1`,
`basis 2` coordinates are bounded by `|ε| ≤ b ≤ c`. -/
theorem Prism3D.mem_add_smul_mem_longPlane {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) (e : EuclideanSpace ℝ (Fin 3))
    (he1 : ‖e‖ = 1) (he2 : e ∈ P.longPlane) (ε : ℝ) (hε : |ε| ≤ (b : ℝ)) :
    P.center + ε • e ∈ P.carrier := by
  rw [P.mem_carrier_iff]
  intro i
  rw [P.basis.repr_apply_apply, real_inner_comm]
  fin_cases i
  · have he0 : inner ℝ e (P.basis 0) = (0 : ℝ) := by
      rcases (Submodule.mem_span_pair.mp he2) with ⟨s, t, rfl⟩
      simp [inner_add_left, inner_smul_left,
        P.basis.inner_eq_zero (show (1 : Fin 3) ≠ 0 by decide),
        P.basis.inner_eq_zero (show (2 : Fin 3) ≠ 0 by decide)]
    simp [vsub_eq_sub, add_sub_cancel_left, inner_smul_left, he0]
  · rw [vsub_eq_sub, add_sub_cancel_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp [norm_smul, Real.norm_eq_abs, he1, P.basis.norm_eq_one, P.thicknesses_eq, hε]
  · rw [vsub_eq_sub, add_sub_cancel_left]
    calc
      |inner ℝ (ε • e) (P.basis 2)| ≤ ‖ε • e‖ * ‖P.basis 2‖ :=
        abs_real_inner_le_norm _ _
      _ = |ε| := by
        simp [norm_smul, Real.norm_eq_abs, he1, P.basis.norm_eq_one]
      _ ≤ (b : ℝ) := hε
      _ ≤ (c : ℝ) := by exact_mod_cast hbc
      _ = P.thicknesses 2 := by simp [P.thicknesses_eq]

/-- In `ℝ³` a two-dimensional subspace meets the orthogonal complement of any at most
one-dimensional subspace in a nonzero vector.  Applied with `D = A.direction` for the affine line
`A` witnessing the rank-`1` thickness. -/
theorem Prism3D.exists_unit_longPlane_orthogonal {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) (D : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hD : Module.finrank ℝ D ≤ 1) :
    ∃ e : EuclideanSpace ℝ (Fin 3), e ∈ P.longPlane ∧ ‖e‖ = 1 ∧
      ∀ z ∈ D, inner ℝ e z = (0 : ℝ) := by
  have hDperp_ge : 2 ≤ Module.finrank ℝ Dᗮ := by
    have h_eq : Module.finrank ℝ D + Module.finrank ℝ Dᗮ =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
      Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) D
    rw [finrank_euclideanSpace_fin] at h_eq
    omega
  have hinf_pos : 1 ≤ Module.finrank ℝ
      ((P.longPlane ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) := by
    have h_sup_le : Module.finrank ℝ
        ((P.longPlane ⊔ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
      (P.longPlane ⊔ Dᗮ).finrank_le
    have h_eq : Module.finrank ℝ ((P.longPlane ⊔ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) +
          Module.finrank ℝ ((P.longPlane ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) =
        Module.finrank ℝ P.longPlane + Module.finrank ℝ Dᗮ :=
      Submodule.finrank_sup_add_finrank_inf_eq P.longPlane Dᗮ
    rw [P.finrank_longPlane] at h_eq
    rw [finrank_euclideanSpace_fin] at h_sup_le
    omega
  have h_nonbot : (P.longPlane ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ≠ ⊥ := by
    intro h_bot
    rw [h_bot] at hinf_pos
    simp at hinf_pos
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_nonbot
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_, ?_⟩
  · exact P.longPlane.smul_mem (‖w‖⁻¹ : ℝ) (Submodule.mem_inf.mp hw_mem).1
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (ne_of_gt hw_pos)]
  · have hw_orth : w ∈ Dᗮ := (Submodule.mem_inf.mp hw_mem).2
    have he_orth : (‖w‖⁻¹ : ℝ) • w ∈ Dᗮ :=
      Submodule.smul_mem (Dᗮ) (‖w‖⁻¹ : ℝ) hw_orth
    intro z hz
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal D ((‖w‖⁻¹ : ℝ) • w)).mp he_orth z hz

/-- **The separation estimate.**  A linear functional `⟪e, ·⟫` whose direction is orthogonal to an
affine subspace `A` is constant on `A`, so on the `r`-neighbourhood of `A` it varies by at most
`2r`.  This is what forbids a wide flat disc from fitting around a line. -/
theorem abs_inner_sub_le_two_mul_of_subset_cthickening
    {s : Set (EuclideanSpace ℝ (Fin 3))} {r : ℝ≥0}
    {A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3))}
    (hs : s ⊆ Metric.cthickening (r : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))))
    {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1)
    (heA : ∀ z ∈ A.direction, inner ℝ e z = (0 : ℝ))
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ s) (hy : y ∈ s) :
    |inner ℝ e (x - y)| ≤ 2 * (r : ℝ) := by
  classical
  have hAne : (A : Set (EuclideanSpace ℝ (Fin 3))).Nonempty := by
    by_contra hA
    have hAeq : (A : Set (EuclideanSpace ℝ (Fin 3))) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (by intro z hz; exact hA ⟨z, hz⟩)
    simpa [hAeq, Metric.cthickening_empty] using (hs hx)
  have exists_close : ∀ {w : EuclideanSpace ℝ (Fin 3)}, w ∈ s → ∀ η : ℝ, 0 < η →
      ∃ z ∈ (A : Set (EuclideanSpace ℝ (Fin 3))), dist w z ≤ (r : ℝ) + η := by
    intro w hw η hη
    have hmem : w ∈ Metric.cthickening (r : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) :=
      hs hw
    have hinfE : Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3))) ≤
        ENNReal.ofReal (r : ℝ) := by
      simpa using hmem
    have hinfD : Metric.infDist w (A : Set (EuclideanSpace ℝ (Fin 3))) ≤ (r : ℝ) := by
      change ENNReal.toReal (Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3)))) ≤ (r : ℝ)
      have hne1 : Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt hinfE ENNReal.ofReal_lt_top)
      calc
        ENNReal.toReal (Metric.infEDist w (A : Set (EuclideanSpace ℝ (Fin 3)))) ≤
            ENNReal.toReal (ENNReal.ofReal (r : ℝ)) :=
          (ENNReal.toReal_le_toReal hne1 ENNReal.ofReal_ne_top).mpr hinfE
        _ = (r : ℝ) := ENNReal.toReal_ofReal (NNReal.coe_nonneg r)
    have hlt : Metric.infDist w (A : Set (EuclideanSpace ℝ (Fin 3))) < (r : ℝ) + η :=
      lt_of_le_of_lt hinfD (lt_add_of_pos_right (r : ℝ) hη)
    rcases (Metric.infDist_lt_iff hAne).mp hlt with ⟨z, hz, hzlt⟩
    exact ⟨z, hz, le_of_lt hzlt⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  rcases exists_close hx (ε / 2) hε2 with ⟨z₁, hz₁, hxz₁⟩
  rcases exists_close hy (ε / 2) hε2 with ⟨z₂, hz₂, hyz₂⟩
  have hdirmem : z₁ -ᵥ z₂ ∈ A.direction := by
    simpa using AffineSubspace.vsub_mem_direction (s := A) (p₁ := z₁) (p₂ := z₂) hz₁ hz₂
  have hzero : inner ℝ e (z₁ - z₂) = (0 : ℝ) := by
    simpa [vsub_eq_sub] using heA (z₁ -ᵥ z₂) hdirmem
  calc
    |inner ℝ e (x - y)| ≤ |inner ℝ e (x - z₁)| + |inner ℝ e (z₂ - y)| := by
      have hxy : x - y = (x - z₁) + (z₁ - z₂) + (z₂ - y) := by abel
      rw [hxy]
      rw [inner_add_right, inner_add_right, hzero]
      simpa [add_zero] using abs_add_le (inner ℝ e (x - z₁)) (inner ℝ e (z₂ - y))
    _ ≤ ‖x - z₁‖ + ‖z₂ - y‖ := by
      have hb1 : |inner ℝ e (x - z₁)| ≤ ‖x - z₁‖ := by
        simpa [he] using (abs_real_inner_le_norm e (x - z₁))
      have hb2 : |inner ℝ e (z₂ - y)| ≤ ‖z₂ - y‖ := by
        simpa [he] using (abs_real_inner_le_norm e (z₂ - y))
      exact add_le_add hb1 hb2
    _ ≤ (r : ℝ) + ε / 2 + ((r : ℝ) + ε / 2) := by
      have hn1 : ‖x - z₁‖ ≤ (r : ℝ) + ε / 2 := by
        calc
          ‖x - z₁‖ = dist x z₁ := by rw [dist_eq_norm]
          _ ≤ (r : ℝ) + ε / 2 := hxz₁
      have hn2 : ‖z₂ - y‖ ≤ (r : ℝ) + ε / 2 := by
        calc
          ‖z₂ - y‖ = dist z₂ y := by rw [dist_eq_norm]
          _ = dist y z₂ := by rw [dist_comm]
          _ ≤ (r : ℝ) + ε / 2 := hyz₂
      exact add_le_add hn1 hn2
    _ = 2 * (r : ℝ) + ε := by ring

/-- The middle half-width of a `Prism3D` is a lower bound for its rank-`1` thickness.

The rank-`1` thickness is the least `r` for which the prism fits in the `r`-neighbourhood of an
affine *line*.  The prism contains the flat disc of radius `b` in the affine plane through its
centre spanned by `basis 1` and `basis 2` (the coordinate bounds there are `0 ≤ a`, `‖v‖ ≤ b` and
`‖v‖ ≤ b ≤ c`), and a two-dimensional disc of radius `b` cannot be squeezed into the
`r`-neighbourhood of a line unless `b ≤ r`: pick a unit `u` in the disc's plane orthogonal to the
line's direction and test the two endpoints `centre ± b • u`, on which the linear functional
`⟪·, u⟫` — constant along the line — differs by `2b`.

This is the `i = 1` companion of `Kakeya.Prism3D.c_le_ethickness_zero`.  Note that the general
`Kakeya.PrismNDim.thicknesses_le_ethickness` does *not* apply: it wants the half-widths antitone,
while `Prism3D` stores them increasing as `![a, b, c]`. -/
theorem Prism3D.b_le_ethickness_one {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) :
    (b : ENNReal) ≤ Metric.ethickness ℝ P.carrier 1 := by
  rw [Metric.le_ethickness_iff]
  intro r A hA hsub
  have hAfin : Module.finrank ℝ A.direction ≤ 1 := Module.finrank_le_of_rank_le hA
  obtain ⟨e, heP, he1, heOrth⟩ := Prism3D.exists_unit_longPlane_orthogonal P A.direction hAfin
  have hx : P.center + (b : ℝ) • e ∈ P.carrier := by
    exact Prism3D.mem_add_smul_mem_longPlane P e he1 heP (b : ℝ)
      (by rw [abs_of_nonneg b.coe_nonneg])
  have hy : P.center + (-(b : ℝ)) • e ∈ P.carrier := by
    exact Prism3D.mem_add_smul_mem_longPlane P e he1 heP (-(b : ℝ))
      (by rw [abs_neg, abs_of_nonneg b.coe_nonneg])
  have hkey : |inner ℝ e ((P.center + (b : ℝ) • e) - (P.center + (-(b : ℝ)) • e))| ≤
      2 * (r : ℝ) :=
    abs_inner_sub_le_two_mul_of_subset_cthickening hsub he1 heOrth hx hy
  have htwo : 2 * (b : ℝ) ≤ 2 * (r : ℝ) := by
    have hinner : inner ℝ e ((P.center + (b : ℝ) • e) - (P.center + (-(b : ℝ)) • e)) =
        2 * (b : ℝ) := by
      have hdiff : (P.center + (b : ℝ) • e) - (P.center + (-(b : ℝ)) • e) =
          (2 : ℝ) • ((b : ℝ) • e) := by
        rw [neg_smul, two_smul]
        abel
      rw [hdiff, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, he1]
      ring
    calc
      2 * (b : ℝ) = |inner ℝ e ((P.center + (b : ℝ) • e) - (P.center + (-(b : ℝ)) • e))| := by
        rw [hinner, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) b.coe_nonneg)]
      _ ≤ 2 * (r : ℝ) := hkey
  have hbr : (b : ℝ) ≤ (r : ℝ) := by
    nlinarith [htwo]
  have hbl : b ≤ r := by
    exact_mod_cast hbr
  exact ENNReal.coe_le_coe.mpr hbl

/-- **Scale comparison, geometric core.**  An `a × b × 1` plank contained in a `ρ`-tube has `b ≤ ρ`.

`Tube.ethickness_one_le` says a `ρ`-tube has rank-`1` thickness at most `ρ`, and rank-`1`
thickness is monotone under inclusion, so `b ≤ ethickness (plank) 1 ≤ ethickness (tube) 1 ≤ ρ`. -/
theorem Plank.b_le_of_le_tube {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (h : P.toConvexSpaceBody ≤ R.toConvexSpaceBody) : b ≤ ρ := by
  have hb_eth : (b : ENNReal) ≤ Metric.ethickness ℝ P.carrier 1 :=
    Prism3D.b_le_ethickness_one P
  have hsub : (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    exact (SetLike.coe_subset_coe (S := P.toConvexSpaceBody)
      (T := R.toConvexSpaceBody)).mp h
  have hmono : Metric.ethickness ℝ P.carrier 1 ≤ Metric.ethickness ℝ R.carrier 1 := by
    exact Metric.ethickness_monotone hsub 1
  have hle : (b : ENNReal) ≤ (ρ : ENNReal) := by
    calc
      (b : ENNReal) ≤ Metric.ethickness ℝ P.carrier 1 := hb_eth
      _ ≤ Metric.ethickness ℝ R.carrier 1 := hmono
      _ ≤ (ρ : ENNReal) := R.ethickness_one_le
  exact ENNReal.coe_le_coe.mp hle

/-! ### The *longitudinal* scale relation, and why it is decisive

`Kakeya.Plank.b_le_of_le_tube` compares the transverse extents of a plank and a coarse tube.  The
longitudinal extents must also be compared, and doing so is much more restrictive.

In this development a `Plank a b` is `Prism3D a b 1`, whose `thicknesses` are *half*-widths
(`Kakeya.Prism3D.volume_carrier` is `8 * a * b * c`).  So a plank has longitudinal **extent 2**: it
contains the two points `centre ± e` for a unit `e` on its long axis, at distance `2`
(`Kakeya.Prism3D.mem_add_mem_longAxis`, `mem_sub_mem_longAxis`).

A `Tube ρ`, by contrast, is the `ρ`-neighbourhood of a *unit* segment, so it sits in a ball of
radius `1/2 + ρ` about its midpoint (`Kakeya.Tube.carrier_subset_closedBall_midpoint`) and therefore
has diameter at most `1 + 2ρ`.

Consequently a plank inside a `ρ`-tube forces `2 ≤ 1 + 2ρ`, i.e. `1/2 ≤ ρ`.  The two normalisations
disagree by a factor of two in the long direction, and the consequence is not cosmetic: the
`PlankFactorization` hypothesis of Proposition 6.6(A) is only satisfiable for `ρ ∈ [1/2, 1]`. -/

/-- **Sharp longitudinal scale relation.**  An `a × b × 1` plank inside a `ρ`-tube forces
`1/2 ≤ ρ`, because the plank has longitudinal extent `2` while a `ρ`-tube has diameter at most
`1 + 2ρ`. -/
theorem Plank.half_le_of_le_tube {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (P : Plank a b hab hb1) (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (h : P.toConvexSpaceBody ≤ R.toConvexSpaceBody) : 1 / 2 ≤ ρ := by
  have hb_eth : (1 : ENNReal) ≤ Metric.ethickness ℝ P.carrier 0 := by
    simpa using (Prism3D.c_le_ethickness_zero P)
  have hsub : (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    exact (SetLike.coe_subset_coe (S := P.toConvexSpaceBody)
      (T := R.toConvexSpaceBody)).mp h
  have hmono : Metric.ethickness ℝ P.carrier 0 ≤ Metric.ethickness ℝ R.carrier 0 := by
    exact Metric.ethickness_monotone hsub 0
  have hmono2 : Metric.ethickness ℝ R.carrier 0 ≤
      Metric.ethickness ℝ (Metric.closedBall (midpoint ℝ R.x R.y) (1 / 2 + (ρ : ℝ))) 0 := by
    exact Metric.ethickness_monotone
      (Tube.carrier_subset_closedBall_midpoint (E := EuclideanSpace ℝ (Fin 3)) R) 0
  have hbnd : Metric.ethickness ℝ
      (Metric.closedBall (midpoint ℝ R.x R.y) (1 / 2 + (ρ : ℝ))) 0 ≤ (1 / 2 + ρ : ℝ≥0) := by
    simpa using (Metric.ethickness_closedBall_le (x := midpoint ℝ R.x R.y) (1 / 2 + ρ) 0)
  have hle : (1 : ENNReal) ≤ ((1 / 2 + ρ : ℝ≥0) : ENNReal) := by
    calc
      (1 : ENNReal) ≤ Metric.ethickness ℝ P.carrier 0 := hb_eth
      _ ≤ Metric.ethickness ℝ R.carrier 0 := hmono
      _ ≤ Metric.ethickness ℝ (Metric.closedBall (midpoint ℝ R.x R.y) (1 / 2 + (ρ : ℝ))) 0 :=
        hmono2
      _ ≤ (1 / 2 + ρ : ℝ≥0) := hbnd
  have hnn : (1 : ℝ≥0) ≤ (1 / 2 : ℝ≥0) + ρ := ENNReal.coe_le_coe.mp hle
  have hrr : (1 : ℝ) ≤ (1 / 2 : ℝ) + (ρ : ℝ) := by exact_mod_cast hnn
  have hρ : (1 / 2 : ℝ) ≤ (ρ : ℝ) := by linarith
  exact_mod_cast hρ
/-! ### The comparable-plank normalisation, and the local cover it unlocks

The covering datum above is still an *assumed* counting statement.  This section reduces it to a
single *containment*, which is both weaker and manifestly true in the paper's normalisation, and
proves the counting.

**The normalisation defect.**  `Plank a b` is `Prism3D a b 1`, and `Prism3D` records half-widths, so
a Lean plank has longitudinal *extent* `2`.  A `Tube r` is the `r`-neighbourhood of a segment of
length exactly `1` (`Tube.dist_eq_one`), hence has diameter at most `1 + 2r`.  A plank inside
a tube therefore forces `2 ≤ 1 + 2r`, i.e. `1/2 ≤ r` (`Kakeya.Plank.half_le_of_le_tube`).  This is a
fixed-constant mismatch between two normalisations, not a statement about the mathematics: the paper
asks only for dimensions *comparable* to `a × b × 1`, and its `θb × b × 1` plank does sit inside a
tube of radius comparable to `b`.  Because the deficiency is longitudinal and `Tube`'s core length
is pinned to `1`, no dilation of the covering radius repairs it, and neither does a position or a
direction net: a leaf has core length `1` and so does a covering tube, so covering a container of
extent `2` leafwise needs `⌈1/ρ⌉` tubes, not `O(1)`.

**The minimal comparable-plank interface.**  What the argument consumes is exactly
`IsTubeShaped r K` — the container lies in *some* tube of radius `r` — with `r` comparable to `b`.
`Kakeya.Prism3D.isTubeShaped` proves that this holds, with `r = a + b ≤ 2 * b`, for any prism whose
long half-width is at most `1/2`, i.e. for the paper's normalisation.  Nothing about
`PlankFactorization`, `Prism3D` or `Tube` is changed; the datum is simply requested where the paper
supplies it.

**What it buys.**  With a tube-shaped container the cover is a *singleton* and no `δ` enters at all:
a body inside `K` is inside `V₀`, hence inside `V₀.rescale ρ` as soon as `r ≤ ρ`.  So
`Ccover = 1`, the covering radius is exactly `ρ`, and the statement is available for arbitrarily
small `ρ` — the local theorem that `Kakeya.exists_leafwise_tube_cover` (which discretises all of
`B₁` and therefore needs `1/2 ≤ ρ`) is not. -/

/-- **A convex body is `r`-tube-shaped** when it lies inside some tube of radius `r`.

This is the whole comparable-plank datum needed by the cross-parent count: not equality with a
plank representative, not comparability of every dimension, just the one containment.  It is
implied by the paper's normalisation via `Kakeya.Prism3D.isTubeShaped`. -/
def IsTubeShaped {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (r : NNReal) (K : ConvexSpaceBody E) : Prop :=
  ∃ V : Tube r E, K ≤ V.toConvexSpaceBody

/-- Tube-shapedness is monotone in the radius. -/
theorem IsTubeShaped.mono_radius {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {r r' : NNReal} {K : ConvexSpaceBody E} (h : IsTubeShaped r K) (hr : r ≤ r') :
    IsTubeShaped r' K := by
  obtain ⟨V, hV⟩ := h
  exact ⟨V.rescale r', le_trans hV (V.le_rescale hr)⟩

/-- Tube-shapedness passes to subbodies. -/
theorem IsTubeShaped.mono_body {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {r : NNReal} {K K' : ConvexSpaceBody E} (h : IsTubeShaped r K)
    (hK : K' ≤ K) : IsTubeShaped r K' := by
  obtain ⟨V, hV⟩ := h
  exact ⟨V, le_trans hK hV⟩

/-- **The comparable-plank normalisation, proved.**

A `Prism3D a b c` whose long half-width satisfies `c ≤ 1/2` — equivalently, whose long *extent* is
at most `1`, matching the unit core length of a `Tube` — is `(a + b)`-tube-shaped.  The witness is
the tube on the prism's own long axis: a prism point `centre + α e₀ + β e₁ + γ e₂` with `|γ| ≤ c`
projects to the core point `centre + γ e₂`, which lies on the unit segment because `|γ| ≤ 1/2`, at
distance `‖α e₀ + β e₁‖ ≤ |α| + |β| ≤ a + b`.

This is the statement whose failure for `c = 1` is `Kakeya.Plank.half_le_of_le_tube`. -/
theorem Prism3D.isTubeShaped {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) (hc : (c : ℝ) ≤ 1 / 2) :
    IsTubeShaped (a + b) P.toConvexSpaceBody := by
  classical
  let e : EuclideanSpace ℝ (Fin 3) := P.basis 2
  have he : ‖e‖ = 1 := by
    change ‖P.basis 2‖ = 1
    exact P.basis.norm_eq_one 2
  let x₀ : EuclideanSpace ℝ (Fin 3) := P.center - (1 / 2 : ℝ) • e
  let y₀ : EuclideanSpace ℝ (Fin 3) := P.center + (1 / 2 : ℝ) • e
  have hdist : dist x₀ y₀ = 1 := by
    rw [dist_eq_norm]
    have hdiff : x₀ - y₀ = -e := by
      dsimp [y₀, x₀]
      module
    rw [hdiff, norm_neg, he]
  let V : Tube (a + b) (EuclideanSpace ℝ (Fin 3)) := Tube.mk' (a + b) hdist
  have he₁ : ‖P.basis 1‖ = 1 := P.basis.norm_eq_one 1
  have he₀ : ‖P.basis 0‖ = 1 := P.basis.norm_eq_one 0
  refine ⟨V, ?_⟩
  -- K ≤ V.toConvexSpaceBody, i.e. carrier inclusion
  refine (SetLike.coe_subset_coe (S := P.toConvexSpaceBody)
      (T := V.toConvexSpaceBody)).mpr ?_
  intro p hp
  have ht : ∀ i : Fin 3, |P.basis.repr (p - P.center) i| ≤ (P.thicknesses i : ℝ) := by
    have hpcarrier : p ∈ P.carrier := hp
    have hvs : p -ᵥ P.center = p - P.center := by
      rw [vsub_eq_sub p P.center]
    intro i
    have hloc := (P.mem_carrier_iff p).1 hpcarrier i
    simpa [hvs] using hloc
  let t : Fin 3 → ℝ := fun i => P.basis.repr (p - P.center) i
  have ht0 : |t 0| ≤ (a : ℝ) := by simpa [t, P.thicknesses_eq] using ht 0
  have ht1 : |t 1| ≤ (b : ℝ) := by simpa [t, P.thicknesses_eq] using ht 1
  have ht2 : |t 2| ≤ (c : ℝ) := by simpa [t, P.thicknesses_eq] using ht 2
  have hc2 : |t 2| ≤ (1 / 2 : ℝ) := le_trans ht2 hc
  have hneg : -(1 / 2 : ℝ) ≤ t 2 := (abs_le.mp hc2).1
  have hpos : t 2 ≤ (1 / 2 : ℝ) := (abs_le.mp hc2).2
  have hge0b : 0 ≤ 1 / 2 + t 2 := by linarith
  have hge0a : 0 ≤ 1 / 2 - t 2 := by linarith
  have hsum_ab : (1 / 2 - t 2) + (1 / 2 + t 2) = 1 := by ring
  let z : EuclideanSpace ℝ (Fin 3) := P.center + (t 2) • e
  -- z lies on the segment x₀ y₀
  have hzseg : z ∈ segment ℝ V.x V.y := by
    dsimp [V]
    change z ∈ segment ℝ x₀ y₀
    refine ⟨1 / 2 - t 2, 1 / 2 + t 2, hge0a, hge0b, hsum_ab, ?_⟩
    dsimp [z, x₀, y₀, e]
    module
  -- dist p z ≤ a + b
  have hsum3 : (∑ i : Fin 3, t i • P.basis i) = p - P.center := by
    simpa [t] using (P.basis.sum_repr (p - P.center))
  have hptc : p - P.center = (t 0) • P.basis 0 + (t 1) • P.basis 1 +
      (t 2) • P.basis 2 := by
    rw [← hsum3]
    rw [Fin.sum_univ_three]
  have hzcomp : p - z = (p - P.center) - (t 2) • P.basis 2 := by
    dsimp [z, e]
    module
  have hdiff : p - z = (t 0) • P.basis 0 + (t 1) • P.basis 1 := by
    rw [hzcomp, hptc]
    module
  have hnorm : ‖p - z‖ ≤ (a : ℝ) + (b : ℝ) := by
    rw [hdiff]
    calc
      ‖(t 0) • P.basis 0 + (t 1) • P.basis 1‖ ≤ ‖(t 0) • P.basis 0‖ + ‖(t 1) • P.basis 1‖ :=
        norm_add_le _ _
      _ ≤ |t 0| + |t 1| := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, he₀, mul_one]
        · rw [norm_smul, Real.norm_eq_abs, he₁, mul_one]
      _ ≤ (a : ℝ) + (b : ℝ) := add_le_add ht0 ht1
  have hdistpz : dist p z ≤ ((a + b : NNReal) : ℝ) := by
    rw [dist_eq_norm]
    rw [NNReal.coe_add]
    exact hnorm
  have hzball : p ∈ Metric.closedBall z (a + b) := Metric.mem_closedBall.mpr hdistpz
  change p ∈ (V.carrier : Set (EuclideanSpace ℝ (Fin 3)))
  rw [V.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨z, hzseg, hzball⟩

/-- **The local leafwise cover.**

Exactly the covering datum consumed by `Kakeya.card_extParents_le_of_cover`, with covering constant
`1`, covering radius exactly `ρ`, and no constraint beyond `r ≤ ρ`.  In particular no lower bound on
`ρ` and no appearance of the leaf radius `δ`: the leaves are already inside the container, so
convexity is not even needed a second time. -/
theorem exists_leafwise_cover_of_isTubeShaped
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι : Type*} {r ρ : NNReal} (hrρ : r ≤ ρ)
    (q : Finset ι) (Tb : ι → ConvexSpaceBody E) {K : ConvexSpaceBody E}
    (hK : IsTubeShaped r K) :
    ∃ F : Finset (Tube ρ E), (F.card : ℝ≥0) ≤ 1 ∧
      ∀ i ∈ q, Tb i ≤ K → ∃ V ∈ F, Tb i ≤ V.toConvexSpaceBody := by
  rcases hK with ⟨V₀, hV₀⟩
  refine ⟨{V₀.rescale ρ}, ?_, ?_⟩
  · simp
  · intro i hi hiK
    refine ⟨V₀.rescale ρ, Finset.mem_singleton_self (V₀.rescale ρ), ?_⟩
    exact le_trans hiK (le_trans hV₀ (V₀.le_rescale hrρ))

/-- **The contributing-parent count from tube-shapedness alone.**

`#Parents(K) ≤ Cu`, with covering constant `1`: a tube-shaped container is caught by a single test
tube, so leaf-mediated bounded overlap of the external system applies once. -/
theorem card_extParents_le_of_isTubeShaped
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι κ : Type*} {ρ r : NNReal} {q : Finset ι} {Tb : ι → ConvexSpaceBody E}
    {rs : Finset κ} {assign : ι → κ} {Cu : ℝ≥0}
    (hover : ∀ V : Tube ρ E,
      ((({k ∈ rs | ∃ i ∈ q, assign i = k ∧ Tb i ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    {K : ConvexSpaceBody E} (hrρ : r ≤ ρ) (hK : IsTubeShaped r K) :
    ((({k ∈ rs | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}).card : ℝ≥0)) ≤ Cu := by
  classical
  obtain ⟨V, hV⟩ := hK
  let Vp : Tube ρ E := V.rescale ρ
  have hKV : K ≤ Vp.toConvexSpaceBody := by
    dsimp [Vp]
    exact le_trans hV (V.le_rescale hrρ)
  have hsub : ({k ∈ rs | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K} : Finset κ) ⊆
      {k ∈ rs | ∃ i ∈ q, assign i = k ∧ Tb i ≤ Vp.toConvexSpaceBody} := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, i, hiq, hassign, hTiK⟩
    exact Finset.mem_filter.mpr ⟨hkr, i, hiq, hassign, hTiK.trans hKV⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hover Vp)
/-- In `ℝ³` a two-dimensional subspace meets the orthogonal complement of any at most
one-dimensional subspace in a unit vector.  The submodule-level generalisation of
`Kakeya.Prism3D.exists_unit_longPlane_orthogonal`, whose proof used the prism only through
`finrank longPlane = 2`. -/
theorem exists_unit_mem_orthogonal_of_finrank_two
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hP : Module.finrank ℝ P = 2)
    (D : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hD : Module.finrank ℝ D ≤ 1) :
    ∃ e : EuclideanSpace ℝ (Fin 3), e ∈ P ∧ ‖e‖ = 1 ∧
      ∀ z ∈ D, inner ℝ e z = (0 : ℝ) := by
  have hDperp_ge : 2 ≤ Module.finrank ℝ Dᗮ := by
    have h_eq : Module.finrank ℝ D + Module.finrank ℝ Dᗮ =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
      Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) D
    rw [finrank_euclideanSpace_fin] at h_eq
    omega
  have hinf_pos : 1 ≤ Module.finrank ℝ ((P ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) := by
    have h_sup_le : Module.finrank ℝ
        ((P ⊔ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
      (P ⊔ Dᗮ).finrank_le
    have h_eq : Module.finrank ℝ ((P ⊔ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) +
          Module.finrank ℝ ((P ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))) =
        Module.finrank ℝ P + Module.finrank ℝ Dᗮ :=
      Submodule.finrank_sup_add_finrank_inf_eq P Dᗮ
    rw [hP] at h_eq
    rw [finrank_euclideanSpace_fin] at h_sup_le
    omega
  have h_nonbot : (P ⊓ Dᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) ≠ ⊥ := by
    intro h_bot
    rw [h_bot] at hinf_pos
    simp at hinf_pos
  obtain ⟨w, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_nonbot
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_, ?_, ?_⟩
  · exact P.smul_mem (‖w‖⁻¹ : ℝ) (Submodule.mem_inf.mp hw_mem).1
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (ne_of_gt hw_pos)]
  · have hw_orth : w ∈ Dᗮ := (Submodule.mem_inf.mp hw_mem).2
    have he_orth : (‖w‖⁻¹ : ℝ) • w ∈ Dᗮ :=
      Submodule.smul_mem (Dᗮ) (‖w‖⁻¹ : ℝ) hw_orth
    intro z hz
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal D ((‖w‖⁻¹ : ℝ) • w)).mp he_orth z hz

/-- Every `Prism3D` contains a flat disc of radius its middle half-width, in the plane through its
centre spanned by `basis 1` and `basis 2`.  This is why `ContainsFlatDisc` is a *faithful* weakening
of `parts_are_planks`: any genuine plank representative supplies it. -/
theorem Prism3D.containsFlatDisc {a b c : ℝ≥0} {hab : a ≤ b} {hbc : b ≤ c}
    (P : Prism3D a b c hab hbc) : ContainsFlatDisc b P.carrier := by
  refine ⟨P.center, P.longPlane, P.finrank_longPlane, ?_⟩
  intro v hv hb
  by_cases hv0 : v = 0
  · subst hv0
    rw [P.mem_carrier_iff]
    intro i
    simp
  · set e : EuclideanSpace ℝ (Fin 3) := ‖v‖⁻¹ • v
    let t : ℝ := ‖v‖
    have he1 : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    have he2 : e ∈ P.longPlane := by
      dsimp [e]
      exact P.longPlane.smul_mem (‖v‖⁻¹ : ℝ) hv
    have ht : |t| ≤ (b : ℝ) := by
      dsimp [t]
      rw [abs_of_nonneg (norm_nonneg v)]
      exact hb
    have hstep : t • e = v := by
      dsimp [t, e]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
    have hmem : P.center + t • e ∈ P.carrier :=
      Prism3D.mem_add_smul_mem_longPlane P e he1 he2 t ht
    rw [← hstep]
    exact hmem

/-- A flat disc of radius `b` cannot be squeezed into the `r`-neighbourhood of a line unless
`b ≤ r`: pick a unit `e` in the disc's plane orthogonal to the line's direction and test the two
points `c ± b • e`, on which `⟪e, ·⟫` — constant along the line — differs by `2b`.  The
normalisation-free form of `Kakeya.Prism3D.b_le_ethickness_one`. -/
theorem ContainsFlatDisc.le_ethickness_one {b : ℝ≥0}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : ContainsFlatDisc b S) :
    (b : ENNReal) ≤ Metric.ethickness ℝ S 1 := by
  rw [Metric.le_ethickness_iff]
  intro r A hA hsub
  have hAfin : Module.finrank ℝ A.direction ≤ 1 := Module.finrank_le_of_rank_le hA
  rcases h with ⟨c, P, hP2, hmem⟩
  obtain ⟨e, heP, he1, heOrth⟩ :=
    exists_unit_mem_orthogonal_of_finrank_two P hP2 A.direction hAfin
  have hnx : ‖(b : ℝ) • e‖ = (b : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg b.coe_nonneg, he1]
    simp
  have hx : c + (b : ℝ) • e ∈ S := by
    exact hmem ((b : ℝ) • e) (Submodule.smul_mem P (b : ℝ) heP)
      (le_of_eq hnx)
  have hny : ‖(-(b : ℝ)) • e‖ = (b : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg b.coe_nonneg, he1]
    simp
  have hy : c + (-(b : ℝ)) • e ∈ S := by
    exact hmem (-(b : ℝ) • e) (Submodule.smul_mem P (-(b : ℝ)) heP)
      (le_of_eq hny)
  have hkey : |inner ℝ e ((c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e))| ≤
      2 * (r : ℝ) :=
    abs_inner_sub_le_two_mul_of_subset_cthickening hsub he1 heOrth hx hy
  have htwo : 2 * (b : ℝ) ≤ 2 * (r : ℝ) := by
    have hinner : inner ℝ e ((c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e)) =
        2 * (b : ℝ) := by
      have hdiff : (c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e) =
          (2 : ℝ) • ((b : ℝ) • e) := by
        rw [neg_smul, two_smul]
        abel
      rw [hdiff, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he1]
      ring
    calc
      2 * (b : ℝ) = |inner ℝ e ((c + (b : ℝ) • e) - (c + (-(b : ℝ)) • e))| := by
        rw [hinner, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) b.coe_nonneg)]
      _ ≤ 2 * (r : ℝ) := hkey
  have hbr : (b : ℝ) ≤ (r : ℝ) := by
    nlinarith [htwo]
  have hbl : b ≤ r := by
    exact_mod_cast hbr
  exact ENNReal.coe_le_coe.mpr hbl

/-- **Scale comparison, normalisation-free core.**  A set containing a flat disc of radius `b` and
contained in a `ρ`-tube has `b ≤ ρ`.  Unlike `Kakeya.Plank.b_le_of_le_tube` this makes no demand on
the longitudinal extent, so it does not force `1/2 ≤ ρ`. -/
theorem ContainsFlatDisc.le_of_subset_tube {b ρ : ℝ≥0}
    {S : Set (EuclideanSpace ℝ (Fin 3))} (h : ContainsFlatDisc b S)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3))) (hsub : S ⊆ R.carrier) : b ≤ ρ := by
  have hb_eth : (b : ENNReal) ≤ Metric.ethickness ℝ S 1 :=
    ContainsFlatDisc.le_ethickness_one h
  have hmono : Metric.ethickness ℝ S 1 ≤ Metric.ethickness ℝ R.carrier 1 := by
    exact Metric.ethickness_monotone hsub 1
  have hle : (b : ENNReal) ≤ (ρ : ENNReal) := by
    calc
      (b : ENNReal) ≤ Metric.ethickness ℝ S 1 := hb_eth
      _ ≤ Metric.ethickness ℝ R.carrier 1 := hmono
      _ ≤ (ρ : ENNReal) := R.ethickness_one_le
  exact ENNReal.coe_le_coe.mp hle

/-- Pure `ℝ≥0` arithmetic behind the corrected scale relation: `min b (1/2) ≤ ρ` and `b ≤ 1` give
`b ≤ 2 * ρ`.  Either the minimum is `b`, and `b ≤ ρ ≤ 2ρ`; or it is `1/2`, and then
`b ≤ 1 = 2 * (1/2) ≤ 2ρ`. -/
theorem le_two_mul_of_min_le {b ρ : ℝ≥0} (hb1 : b ≤ 1) (hmin : min b (1 / 2 : ℝ≥0) ≤ ρ) :
    b ≤ 2 * ρ := by
  have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hmin' : min (b : ℝ) (1 / 2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hmin
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have : (b : ℝ) ≤ 2 * (ρ : ℝ) := by
    rcases le_total (b : ℝ) (1 / 2 : ℝ) with h | h
    · rw [min_eq_left h] at hmin'
      linarith
    · rw [min_eq_right h] at hmin'
      linarith
  exact_mod_cast this
/-! ### Inner slab non-concentration: the Part-(B) concentration step

The concentration parameter of Proposition 6.6(B) is *not* the part-(A) one.  The outer plank family
is Katz--Tao, so GWZ Lemma 6.1 is applied to it with `γ = 0`, where the slab hypothesis is vacuous
(`Kakeya.gammaZeroSlabBound`): no concentration bound, and in particular no cross-parent overlap
loss, is needed for the outer family.  The concentration that *is* needed is for the inner,
rescaled family, with `γ = 1` and a sub-polynomial constant.  The counting core of that bound is the
following (blueprint `lem:factorInnerSlabNonconcentration`).
-/

/-- **Inner slab non-concentration, counting core** (blueprint
`lem:factorInnerSlabNonconcentration`).

Let `proj : q → r` assign to each fine index a coarse index, with all fibres of comparable size
`m` up to a factor `Cfib`, and let `qS ⊆ q` be a set of fine indices whose coarse indices all lie in
a selected set `sel` of coarse indices.  Then

`|qS| ≤ Cfib ^ 2 * (|sel| / |r|) * |q|`,

in the multiplicative form below.  Each selected coarse index carries at most `Cfib * m` fine
indices, while `|q| ≥ Cfib⁻¹ * m * |r|`; the common fibre size `m` then cancels, so no positivity
hypothesis on it is needed.

In the application `sel = {k | R k ≤ K_S}` is bounded by `C_F * θ * |r|` by the Frostman property of
the coarse fibre, which turns the conclusion into `|qS| ≤ C_F * Cfib ^ 2 * θ * |q|`: slab
non-concentration with exponent `γ = 1` and the sub-polynomial constant `C_F * Cfib ^ 2`. -/
theorem card_le_of_comparable_fibres {ιq ιr : Type*} [DecidableEq ιq] [DecidableEq ιr]
    {q : Finset ιq} {r : Finset ιr} {proj : ιq → ιr} {m Cfib : ℝ≥0}
    (hCfib : 1 ≤ Cfib)
    (hproj : ∀ i ∈ q, proj i ∈ r)
    (hlb : ∀ k ∈ r, Cfib⁻¹ * m ≤ (({i ∈ q | proj i = k}).card : ℝ≥0))
    (hub : ∀ k ∈ r, (({i ∈ q | proj i = k}).card : ℝ≥0) ≤ Cfib * m)
    {sel : Finset ιr} (hsel : sel ⊆ r)
    {qS : Finset ιq} (hqS : qS ⊆ q) (hmem : ∀ i ∈ qS, proj i ∈ sel) :
    ((qS.card : ℝ≥0)) * (r.card : ℝ≥0) ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := by
  let fib : ιr → ℝ≥0 := fun k => ((q.filter fun i => proj i = k).card : ℝ≥0)
  -- upper bound on qS over sel
  have hUB : (qS.card : ℝ≥0) ≤ (sel.card : ℝ≥0) * Cfib * m := by
    have hsub : qS ⊆ q.filter (fun i => proj i ∈ sel) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hqS hi, hmem i hi⟩
    have hcard_sub : (qS.card : ℝ≥0) ≤ ((q.filter (fun i => proj i ∈ sel)).card : ℝ≥0) := by
      exact Nat.cast_le.2 (Finset.card_le_card hsub)
    have hfib_sum : ((q.filter (fun i => proj i ∈ sel)).card : ℝ≥0) = Finset.sum sel fib := by
      have hnat : (q.filter (fun i => proj i ∈ sel)).card =
          (∑ k ∈ sel, (q.filter (fun i => proj i = k)).card) :=
        (Finset.sum_card_fiberwise_eq_card_filter (s := q) (t := sel) (g := proj)).symm
      rw [hnat]
      push_cast
      rfl
    have hqS_le_sum : (qS.card : ℝ≥0) ≤ Finset.sum sel fib := hcard_sub.trans hfib_sum.le
    have hterm : ∀ k ∈ sel, fib k ≤ Cfib * m := by
      intro k hk
      exact hub k (hsel hk)
    calc
      (qS.card : ℝ≥0) ≤ Finset.sum sel fib := hqS_le_sum
      _ ≤ Finset.sum sel (fun _k => Cfib * m) := Finset.sum_le_sum (fun k hk => hterm k hk)
      _ = (sel.card : ℝ≥0) * Cfib * m := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  -- lower bound for q
  have hLB : Cfib⁻¹ * m * (r.card : ℝ≥0) ≤ (q.card : ℝ≥0) := by
    have hQeq : q.filter (fun i => proj i ∈ r) = q := by
      ext i
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hi, _⟩
        exact hi
      · intro hi
        exact ⟨hi, hproj i hi⟩
    have hfib_sum_r : Finset.sum r fib = ((q.filter (fun i => proj i ∈ r)).card : ℝ≥0) := by
      have hnat : (q.filter (fun i => proj i ∈ r)).card =
          (∑ k ∈ r, (q.filter (fun i => proj i = k)).card) :=
        (Finset.sum_card_fiberwise_eq_card_filter (s := q) (t := r) (g := proj)).symm
      rw [hnat]
      push_cast
      rfl
    calc
      Cfib⁻¹ * m * (r.card : ℝ≥0) = (r.card : ℝ≥0) * (Cfib⁻¹ * m) := by ring
      _ ≤ Finset.sum r fib := by
        calc
          (r.card : ℝ≥0) * (Cfib⁻¹ * m) = Finset.sum r (fun _ : ιr => Cfib⁻¹ * m) := by
            rw [← nsmul_eq_mul, ← Finset.sum_const]
          _ ≤ Finset.sum r fib := Finset.sum_le_sum (fun k hk => hlb k hk)
      _ = (q.card : ℝ≥0) := by
        rw [hfib_sum_r, hQeq]
  -- combine
  have hCf0 : Cfib ≠ 0 := by
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCfib).ne'
  calc
    (qS.card : ℝ≥0) * (r.card : ℝ≥0)
        ≤ ((sel.card : ℝ≥0) * Cfib * m) * (r.card : ℝ≥0) := by
            exact mul_le_mul_of_nonneg_right hUB zero_le
    _ = Cfib ^ 2 * (sel.card : ℝ≥0) * (Cfib⁻¹ * m * (r.card : ℝ≥0)) := by
      field_simp [hCf0]
    _ ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := by
      gcongr

/-- **Inner slab non-concentration, `γ = 1` form.**  Once the selected coarse set is known to be a
`Cθ`-fraction of the coarse family — in the application `Cθ = C_F * θ`, by the Frostman property of
the coarse fibre (`Kakeya.card_le_of_frostmanIn`) — the counting core
`Kakeya.card_le_of_comparable_fibres` gives exactly the slab non-concentration hypothesis of GWZ
Lemma 6.1 with exponent `γ = 1` and constant `Cfib ^ 2 * Cθ`. -/
theorem card_le_of_comparable_fibres_of_selected_le {ιq ιr : Type*} [DecidableEq ιq]
    [DecidableEq ιr] {q : Finset ιq} {r : Finset ιr} {proj : ιq → ιr} {m Cfib Cθ : ℝ≥0}
    (hCfib : 1 ≤ Cfib) (hr : r.Nonempty)
    (hproj : ∀ i ∈ q, proj i ∈ r)
    (hlb : ∀ k ∈ r, Cfib⁻¹ * m ≤ (({i ∈ q | proj i = k}).card : ℝ≥0))
    (hub : ∀ k ∈ r, (({i ∈ q | proj i = k}).card : ℝ≥0) ≤ Cfib * m)
    {sel : Finset ιr} (hsel : sel ⊆ r) (hselcard : (sel.card : ℝ≥0) ≤ Cθ * (r.card : ℝ≥0))
    {qS : Finset ιq} (hqS : qS ⊆ q) (hmem : ∀ i ∈ qS, proj i ∈ sel) :
    (qS.card : ℝ≥0) ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) := by
  have hmain : (qS.card : ℝ≥0) * (r.card : ℝ≥0)
      ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := by
    exact card_le_of_comparable_fibres hCfib hproj hlb hub hsel hqS hmem
  have hrpos : 0 < (r.card : ℝ≥0) := by
    exact_mod_cast (Finset.card_pos.mpr hr)
  have hle : (qS.card : ℝ≥0) * (r.card : ℝ≥0)
      ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) * (r.card : ℝ≥0) := by
    calc
      (qS.card : ℝ≥0) * (r.card : ℝ≥0)
          ≤ Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0) := hmain
      _ ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) * (r.card : ℝ≥0) := by
        have hnn : 0 ≤ Cfib ^ 2 * (q.card : ℝ≥0) := by positivity
        calc
          Cfib ^ 2 * (sel.card : ℝ≥0) * (q.card : ℝ≥0)
              = (Cfib ^ 2 * (q.card : ℝ≥0)) * (sel.card : ℝ≥0) := by ring
          _ ≤ (Cfib ^ 2 * (q.card : ℝ≥0)) * (Cθ * (r.card : ℝ≥0)) := by
            exact mul_le_mul_of_nonneg_left hselcard hnn
          _ = Cfib ^ 2 * Cθ * (q.card : ℝ≥0) * (r.card : ℝ≥0) := by ring
  exact le_of_mul_le_mul_right hle hrpos

/-- **The Frostman coarse count** (the first step of blueprint
`lem:factorInnerSlabNonconcentration`).

If the coarse family `(Rb k)_{k ∈ r}` is `C_F`-Frostman in `W`, all its members lie in `W`, their
volumes lie in `[vmin, vmax]` with `vmin ≠ 0`, and `K ≤ W`, then the number of coarse bodies
contained in `K` is controlled by the volume ratio `|K| / |W|`:

`|{k ∈ r | Rb k ≤ K}| * vmin ≤ C_F * (|r| * vmax) * (|K| / |W|)`.

Counting: the selected bodies each have volume at least `vmin`, their total volume is
`densityIn r Rb K * |K|`, the Frostman property bounds that density by `C_F * densityIn r Rb W`, and
the latter is `(∑_{k ∈ r} |Rb k|) / |W| ≤ |r| * vmax / |W|`.

Together with `Kakeya.card_le_of_comparable_fibres_of_selected_le` and the coarse-container volume
bound `|K_S| ≲ θ |W|` this is the `γ = 1` slab non-concentration input of GWZ Lemma 6.1 used by
Proposition 6.6(B); what is still missing is the *geometric* construction of the coarse container
`K_S` (blueprint Equation `eq:factor-coarse-container-compatibility`), which fine-tube containment
alone does not give. -/
theorem card_le_of_frostmanIn {ιr : Type*} [DecidableEq ιr] {r : Finset ιr}
    {Rb : ιr → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {W K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {CF : ENNReal}
    (hFrost : IsFrostmanIn r Rb W CF) (hRW : ∀ k ∈ r, Rb k ≤ W) (hKW : K ≤ W)
    {vmin vmax : ENNReal} (hvmin : vmin ≠ 0)
    (hmin : ∀ k ∈ r, vmin ≤ volume (Rb k).carrier)
    (hmax : ∀ k ∈ r, volume (Rb k).carrier ≤ vmax)
    (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤) :
    (({k ∈ r | Rb k ≤ K}).card : ENNReal) * vmin
      ≤ CF * ((r.card : ENNReal) * vmax) * (volume K.carrier / volume W.carrier) := by
  let sel : Finset ιr := {k ∈ r | Rb k ≤ K}
  -- `densityIn r Rb W = (∑_{k ∈ r} |Rb k|) / |W| ≤ |r| * vmax / |W|`.
  have hdenW :
      densityIn r Rb W ≤ ((r.card : ENNReal) * vmax) / volume W.carrier := by
    rw [densityIn_of_all_le hRW]
    exact ENNReal.div_le_div_right
      (by simpa [nsmul_eq_mul] using
        Finset.sum_le_card_nsmul r (fun k => volume (Rb k).carrier) vmax hmax) _
  -- counting: each selected body has volume at least `vmin`.
  have hcount : (sel.card : ENNReal) * vmin ≤ ∑ k ∈ sel, volume (Rb k).carrier := by
    simpa [nsmul_eq_mul] using
      Finset.card_nsmul_le_sum sel (fun k => volume (Rb k).carrier) vmin
        (fun k hk => hmin k (Finset.mem_filter.mp hk).1)
  calc
    (sel.card : ENNReal) * vmin ≤ ∑ k ∈ sel, volume (Rb k).carrier := hcount
    _ = densityIn r Rb K * volume K.carrier := sum_volume_eq_densityIn_mul_volume r Rb K
    _ ≤ (CF * densityIn r Rb W) * volume K.carrier := by
      gcongr
      exact hFrost K hKW
    _ ≤ (CF * (((r.card : ENNReal) * vmax) / volume W.carrier)) * volume K.carrier := by
      gcongr
    _ = CF * ((r.card : ENNReal) * vmax) * (volume K.carrier / volume W.carrier) := by
      rw [mul_assoc, ENNReal.mul_comm_div, ← mul_assoc]

end Kakeya

end

end
