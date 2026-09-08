/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorGateRed
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeVolume

/-!
# The **two-dimensional** transverse lattice, and its inscribed ball

 proved that a **one-dimensional** clump of cells — the
`Kakeya.ML2Core.redLeaf` alignment, all offsets along `e₀` — cannot carry the `T-S2` certificate:
containment under the level-`q` node caps the cell count at `M ≲ ρ_q/ρ_c`, while the hull-volume
comparison needs `M ≳ (ρ_q/ρ_c)²`.  The host must spread in **two** transverse directions.

This file supplies the geometric core of that host, and only it: the four corner cells of the
transverse square, and the fact that their convex hull contains a **ball** of radius equal to the
half-spread.  That ball is what `Kakeya.ML2Core.le_volume_of_dist_of_closedBall_subset` consumes at
ranks `1` and `2`; the long-axis input at rank `0` is the cell's own unit axis.

The corner offsets are `(± a) e₀ + (± a) e₁`, so the transverse square has half-side `a`, and the
inscribed ball has radius `min a (1/2)` — the `1/2` being the half-length of the unit axis, which is
the same length constraint that refuted the tube-containment route : a unit-length tube is
`1/2` long each way from its midpoint and no fatter object fits past its ends.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Kakeya.ML2Core

/-- The corner cell at transverse offset `u • e₀ + v • e₁`. -/
noncomputable def redOffset (δ : NNReal) (u v : ℝ) : Tube δ E3 :=
  (redTube δ).translate (u • redE 0 + v • redE 1)

/-- A point of the translated axis lies in the corresponding corner cell. -/
theorem mem_redOffset_of_axis {δ : NNReal} (u v : ℝ) {c : ℝ} (hc : |c| ≤ 1 / 2) :
    (u • redE 0 + v • redE 1) + c • redE 2 ∈ (redOffset δ u v).carrier := by
  rw [redOffset, translate_carrier_eq_image]
  refine ⟨c • redE 2, ?_, rfl⟩
  rw [(redTube δ).carrier_eq]
  refine Set.mem_iUnion₂.mpr ⟨c • redE 2, ?_, Metric.mem_closedBall_self δ.coe_nonneg⟩
  rw [segment_eq_image]
  refine ⟨c + 1 / 2, ⟨by cases abs_le.mp hc; linarith, by cases abs_le.mp hc; linarith⟩, ?_⟩
  simp only [redTube, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
  module

/-- Every coordinate of a vector of `E3` is bounded by its norm. -/
theorem abs_apply_le_norm (p : E3) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  have h := EuclideanSpace.norm_eq p
  rw [h]
  rw [show |p i| = Real.sqrt (|p i| ^ 2) from (Real.sqrt_sq (abs_nonneg _)).symm]
  refine Real.sqrt_le_sqrt ?_
  refine Finset.single_le_sum (f := fun j => ‖p j‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i) |>.trans_eq' ?_
  simp [Real.norm_eq_abs]

/-- The coordinate decomposition of a vector of `E3` in the `redE` basis. -/
theorem redE_decomp (p : E3) : p = (p 0) • redE 0 + (p 1) • redE 1 + (p 2) • redE 2 := by
  ext i
  fin_cases i <;> simp [redE]

/-- **The inscribed ball.**  The convex hull of the four corner cells at transverse offsets
`(± a) e₀ + (± a) e₁` contains the closed ball of radius `min a (1/2)` about the origin.

This is the rank-`1`/rank-`2` input obligation of `T-S2`'s `hvol`, discharged for the
two-dimensional lattice host: `Kakeya.ML2Core.le_volume_of_dist_of_closedBall_subset` needs exactly
this ball, and  shows no one-dimensional family can supply it. -/
theorem closedBall_subset_convexHull_redOffset {δ : NNReal} {a r : ℝ} (ha : 0 < a)
    (hr : r ≤ a) (hr2 : r ≤ 1 / 2) :
    Metric.closedBall (0 : E3) r ⊆ convexHull ℝ
      ((redOffset δ a a).carrier ∪ (redOffset δ (-a) a).carrier ∪
        (redOffset δ a (-a)).carrier ∪ (redOffset δ (-a) (-a)).carrier) := by
  intro p hp
  rw [Metric.mem_closedBall, dist_zero_right] at hp
  set c : ℝ := p 2 with hc
  have hc2 : |c| ≤ 1 / 2 := ((abs_apply_le_norm p 2).trans hp).trans hr2
  have h0 : |p 0| ≤ a := ((abs_apply_le_norm p 0).trans hp).trans hr
  have h1 : |p 1| ≤ a := ((abs_apply_le_norm p 1).trans hp).trans hr
  set S : Set E3 := (redOffset δ a a).carrier ∪ (redOffset δ (-a) a).carrier ∪
    (redOffset δ a (-a)).carrier ∪ (redOffset δ (-a) (-a)).carrier with hS
  have hconv : Convex ℝ (convexHull ℝ S) := convex_convexHull ℝ S
  -- the four corner axis points
  have hPP : (a • redE 0 + a • redE 1) + c • redE 2 ∈ convexHull ℝ S :=
    subset_convexHull ℝ S (by
      exact Or.inl (Or.inl (Or.inl (mem_redOffset_of_axis a a hc2))))
  have hMP : ((-a) • redE 0 + a • redE 1) + c • redE 2 ∈ convexHull ℝ S :=
    subset_convexHull ℝ S (by
      exact Or.inl (Or.inl (Or.inr (mem_redOffset_of_axis (-a) a hc2))))
  have hPM : (a • redE 0 + (-a) • redE 1) + c • redE 2 ∈ convexHull ℝ S :=
    subset_convexHull ℝ S (by
      exact Or.inl (Or.inr (mem_redOffset_of_axis a (-a) hc2)))
  have hMM : ((-a) • redE 0 + (-a) • redE 1) + c • redE 2 ∈ convexHull ℝ S :=
    subset_convexHull ℝ S (by
      exact Or.inr (mem_redOffset_of_axis (-a) (-a) hc2))
  -- interpolate along `e₀` at each of the two `e₁`-levels
  set α : ℝ := (a + p 0) / (2 * a) with hα
  set β : ℝ := (a + p 1) / (2 * a) with hβ
  have hα0 : 0 ≤ α := by
    rw [hα]; apply div_nonneg _ (by linarith); cases abs_le.mp h0; linarith
  have hα1 : 0 ≤ 1 - α := by
    rw [hα, sub_nonneg, div_le_one (by linarith)]; cases abs_le.mp h0; linarith
  have hβ0 : 0 ≤ β := by
    rw [hβ]; apply div_nonneg _ (by linarith); cases abs_le.mp h1; linarith
  have hβ1 : 0 ≤ 1 - β := by
    rw [hβ, sub_nonneg, div_le_one (by linarith)]; cases abs_le.mp h1; linarith
  have hane : a ≠ 0 := ne_of_gt ha
  have hQP : (p 0) • redE 0 + a • redE 1 + c • redE 2 ∈ convexHull ℝ S := by
    have hmem := hconv hPP hMP hα0 hα1 (by ring)
    have heq : α • ((a • redE 0 + a • redE 1) + c • redE 2)
        + (1 - α) • (((-a) • redE 0 + a • redE 1) + c • redE 2)
        = (p 0) • redE 0 + a • redE 1 + c • redE 2 := by
      rw [hα]; match_scalars <;> field_simp <;> ring
    rwa [heq] at hmem
  have hQM : (p 0) • redE 0 + (-a) • redE 1 + c • redE 2 ∈ convexHull ℝ S := by
    have hmem := hconv hPM hMM hα0 hα1 (by ring)
    have heq : α • ((a • redE 0 + (-a) • redE 1) + c • redE 2)
        + (1 - α) • (((-a) • redE 0 + (-a) • redE 1) + c • redE 2)
        = (p 0) • redE 0 + (-a) • redE 1 + c • redE 2 := by
      rw [hα]; match_scalars <;> field_simp <;> ring
    rwa [heq] at hmem
  have hmem := hconv hQP hQM hβ0 hβ1 (by ring)
  have heq : β • ((p 0) • redE 0 + a • redE 1 + c • redE 2)
      + (1 - β) • ((p 0) • redE 0 + (-a) • redE 1 + c • redE 2) = p := by
    rw [hβ, hc]
    conv_rhs => rw [redE_decomp p]
    match_scalars <;> field_simp <;> ring
  rwa [heq] at hmem

/-- **The lattice host's `hvol` lower bound.**  The convex hull of the four corner cells has volume
at least `c(3) · (1/2) · r · r`, where `r = min a (1/2)` is the inscribed-ball radius of
`Kakeya.ML2Core.closedBall_subset_convexHull_redOffset`.

Both input obligations are discharged here: rank `0` by the unit axis of a corner cell (its two
endpoints are at distance `1`), ranks `1` and `2` by the inscribed ball.  This is the form
of the statement that a **two-dimensional** transverse spread converts into volume, which 
shows a one-dimensional clump cannot do. -/
theorem le_volume_convexHull_redOffset {δ : NNReal} {a r : ℝ} (ha : 0 < a)
    (hr0 : 0 ≤ r) (hr : r ≤ a) (hr2 : r ≤ 1 / 2) :
    (Metric.lt_volume_convexHull.c 3 : ENNReal) * ENNReal.ofReal (1 / 2 * r * r)
      ≤ volume (convexHull ℝ
        ((redOffset δ a a).carrier ∪ (redOffset δ (-a) a).carrier ∪
          (redOffset δ a (-a)).carrier ∪ (redOffset δ (-a) (-a)).carrier)) := by
  set S : Set E3 := (redOffset δ a a).carrier ∪ (redOffset δ (-a) a).carrier ∪
    (redOffset δ a (-a)).carrier ∪ (redOffset δ (-a) (-a)).carrier with hS
  set x : E3 := (a • redE 0 + a • redE 1) + (1 / 2 : ℝ) • redE 2 with hx
  set y : E3 := (a • redE 0 + a • redE 1) + (-(1 / 2) : ℝ) • redE 2 with hy
  have hdist : dist x y = 1 := by
    rw [dist_eq_norm, show x - y = redE 2 from by rw [hx, hy]; module, norm_redE]
  have hxS : x ∈ convexHull ℝ S :=
    subset_convexHull ℝ S (Or.inl (Or.inl (Or.inl
      (mem_redOffset_of_axis a a (by norm_num)))))
  have hyS : y ∈ convexHull ℝ S :=
    subset_convexHull ℝ S (Or.inl (Or.inl (Or.inl
      (mem_redOffset_of_axis a a (by norm_num)))))
  have hE : Module.finrank ℝ E3 = 3 := by simp
  have hball : Metric.closedBall (0 : E3) r ⊆ convexHull ℝ S :=
    closedBall_subset_convexHull_redOffset (δ := δ) ha hr hr2
  have := le_volume_of_dist_of_closedBall_subset (E := E3) hE (convex_convexHull ℝ S)
    hxS hyS hr0 hball
  rwa [hdist] at this
