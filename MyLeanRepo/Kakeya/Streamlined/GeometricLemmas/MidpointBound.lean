import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Midpoint bound for tubes intersecting the unit ball

If a tube of radius `δ ≤ 1` contains any point in the unit ball,
then its midpoint has norm at most `3`.

## Main result

- `tubeMidpoint_bound_of_unitBall_point`: midpoint norm ≤ 3.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Streamlined.GeometricLemmas

/-- If a radius-`δ` tube (`δ ≤ 1`) contains a point `x` with `‖x‖ ≤ 1`,
then its midpoint has norm at most `3`. -/
lemma tubeMidpoint_bound_of_unitBall_point {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (T : Kakeya.DeltaTube δ) (x : Point3)
    (hx : x ∈ T.carrier) (hxball : ‖x‖ ≤ 1) :
    ‖tubeMidpoint T‖ ≤ 3 := by
  let S := Kakeya.unitSegment T.base T.direction
  have hS_compact : IsCompact S := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hS_nonempty : S.Nonempty :=
    ⟨T.base, 0, by norm_num, by simp⟩
  have h_inf : Metric.infEDist x S ≤ ENNReal.ofReal δ := by
    have h : x ∈ Metric.cthickening δ S := hx
    rw [Metric.mem_cthickening_iff] at h
    exact h
  rcases hS_compact.exists_infEDist_eq_edist hS_nonempty x with ⟨y, hy, h_inf_eq⟩
  have hxy : dist x y ≤ δ := by
    have h_edist : edist x y ≤ ENNReal.ofReal δ := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp h_edist
  rcases hy with ⟨t, ht, rfl⟩
  let m := tubeMidpoint T
  have h_seg : T.base + t • T.direction = m + (t - 1 / 2) • T.direction := by
    simp [m, tubeMidpoint] <;> ext i <;> simp <;> ring
  have h_ym : dist (T.base + t • T.direction) m ≤ 1 / 2 := by
    have h_eq : dist (T.base + t • T.direction) m = ‖(t - 1 / 2 : ℝ) • T.direction‖ := by
      rw [dist_eq_norm]
      have h : T.base + t • T.direction - m = (t - 1 / 2 : ℝ) • T.direction := by
        rw [h_seg] <;> abel
      rw [h]
    rw [h_eq]
    have h_norm_smul : ‖(t - 1 / 2 : ℝ) • T.direction‖ = |t - 1 / 2| * ‖T.direction‖ := by
      rw [norm_smul]
      have h_abs : ‖(t - 1 / 2 : ℝ)‖ = |t - 1 / 2| := by
        simp [Real.norm_eq_abs]
      rw [h_abs]
    rw [h_norm_smul, T.direction_unit]
    have h2 : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
    linarith
  have h_xm : dist x m ≤ δ + 1 / 2 := by
    calc dist x m
      ≤ dist x (T.base + t • T.direction) + dist (T.base + t • T.direction) m := dist_triangle _ _ _
    _ ≤ δ + 1 / 2 := by linarith
  have h_norm : ‖m‖ ≤ ‖x‖ + dist x m := by
    have h1 : ‖m‖ ≤ ‖x‖ + ‖m - x‖ := by
      calc ‖m‖
        = ‖x + (m - x)‖ := by abel
      _ ≤ ‖x‖ + ‖m - x‖ := norm_add_le x (m - x)
    have h2 : ‖m - x‖ = dist x m := by
      rw [← dist_eq_norm, dist_comm]
    rw [h2] at h1
    exact h1
  calc ‖m‖
    ≤ ‖x‖ + dist x m := h_norm
  _ ≤ 1 + (δ + 1 / 2) := by linarith [hxball]
  _ ≤ 3 := by linarith [hδ1]

/-- **Tight midpoint bound.**

If a radius-`δ` tube (`δ ≤ 1`) contains a point `x` with `‖x‖ ≤ 1`,
then its midpoint has norm at most `3/2 + δ`.

This is tighter than `tubeMidpoint_bound_of_unitBall_point` (which gives `≤ 3`).
The proof is identical; the original lemma weakens the bound to `3` for
convenience, while this one preserves the tight `3/2 + δ` conclusion. -/
lemma tubeMidpoint_bound_tight {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (T : Kakeya.DeltaTube δ) (x : Point3)
    (hx : x ∈ T.carrier) (hxball : ‖x‖ ≤ 1) :
    ‖tubeMidpoint T‖ ≤ 3 / 2 + δ := by
  let S := Kakeya.unitSegment T.base T.direction
  have hS_compact : IsCompact S := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hS_nonempty : S.Nonempty :=
    ⟨T.base, 0, by norm_num, by simp⟩
  have h_inf : Metric.infEDist x S ≤ ENNReal.ofReal δ := by
    have h : x ∈ Metric.cthickening δ S := hx
    rw [Metric.mem_cthickening_iff] at h
    exact h
  rcases hS_compact.exists_infEDist_eq_edist hS_nonempty x with ⟨y, hy, h_inf_eq⟩
  have hxy : dist x y ≤ δ := by
    have h_edist : edist x y ≤ ENNReal.ofReal δ := by
      rw [← h_inf_eq]; exact h_inf
    rw [edist_dist] at h_edist
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp h_edist
  rcases hy with ⟨t, ht, rfl⟩
  let m := tubeMidpoint T
  have h_seg : T.base + t • T.direction = m + (t - 1 / 2) • T.direction := by
    simp [m, tubeMidpoint] <;> ext i <;> simp <;> ring
  have h_ym : dist (T.base + t • T.direction) m ≤ 1 / 2 := by
    have h_eq : dist (T.base + t • T.direction) m = ‖(t - 1 / 2 : ℝ) • T.direction‖ := by
      rw [dist_eq_norm]
      have h : T.base + t • T.direction - m = (t - 1 / 2 : ℝ) • T.direction := by
        rw [h_seg] <;> abel
      rw [h]
    rw [h_eq]
    have h_norm_smul : ‖(t - 1 / 2 : ℝ) • T.direction‖ = |t - 1 / 2| * ‖T.direction‖ := by
      rw [norm_smul]
      have h_abs : ‖(t - 1 / 2 : ℝ)‖ = |t - 1 / 2| := by
        simp [Real.norm_eq_abs]
      rw [h_abs]
    rw [h_norm_smul, T.direction_unit]
    have h2 : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
    linarith
  have h_xm : dist x m ≤ δ + 1 / 2 := by
    calc dist x m
      ≤ dist x (T.base + t • T.direction) + dist (T.base + t • T.direction) m := dist_triangle _ _ _
    _ ≤ δ + 1 / 2 := by linarith
  have h_norm : ‖m‖ ≤ ‖x‖ + dist x m := by
    have h1 : ‖m‖ ≤ ‖x‖ + ‖m - x‖ := by
      calc ‖m‖
        = ‖x + (m - x)‖ := by abel
      _ ≤ ‖x‖ + ‖m - x‖ := norm_add_le x (m - x)
    have h2 : ‖m - x‖ = dist x m := by
      rw [← dist_eq_norm, dist_comm]
    rw [h2] at h1
    exact h1
  calc ‖m‖
    ≤ ‖x‖ + dist x m := h_norm
  _ ≤ 1 + (δ + 1 / 2) := by linarith [hxball]
  _ = 3 / 2 + δ := by ring

/--
If a tube intersects the closed unit ball, its midpoint has norm at most `3`.
Convenience wrapper around `tubeMidpoint_bound_of_unitBall_point`.
-/
lemma tubeMidpoint_norm_le_of_intersects_unitBall
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (T : Kakeya.DeltaTube ρ)
    (h_inter : (T.carrier ∩ Metric.closedBall (0 : Point3) 1).Nonempty) :
    ‖tubeMidpoint T‖ ≤ 3 := by
  rcases h_inter with ⟨x, hx, hball⟩
  have hxball : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  exact tubeMidpoint_bound_of_unitBall_point hρ hρ1 T x hx hxball

/--
For a coarse tube family obtained from an exact cover of a fine family
that lies in the unit ball, every coarse tube midpoint has norm at most `3`.
-/
lemma coarse_tube_midpoint_bound
    {δ ρ : ℝ} {F : TubeFamily δ} {coarse : TubeFamily ρ}
    (cover : TubeCover F coarse)
    (hF_ball : F.IsInUnitBall)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (j : Fin coarse.card) :
    ‖tubeMidpoint (coarse.tube j)‖ ≤ 3 := by
  have h_surj : ∃ (i : Fin F.card), cover.parent i = j :=
    cover.parent_surjective j
  rcases h_surj with ⟨i, hi⟩
  let x := tubeMidpoint (F.tube i)
  have hx_fine : x ∈ (F.tube i).carrier := tubeMidpoint_mem_carrier (F.tube i)
  have h1 : (F.tube i).carrier ⊆ (coarse.tube (cover.parent i)).carrier := cover.nested i
  have hx_coarse : x ∈ (coarse.tube j).carrier := by
    rw [hi] at h1
    exact h1 hx_fine
  have hxball : ‖x‖ ≤ 1 := by
    have h : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball i
    have h2 : x ∈ Kakeya.DeltaTube.unitBall := h hx_fine
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using h2
  exact tubeMidpoint_bound_of_unitBall_point hρ hρ1 (coarse.tube j) x hx_coarse hxball

end Kakeya.Streamlined.GeometricLemmas
