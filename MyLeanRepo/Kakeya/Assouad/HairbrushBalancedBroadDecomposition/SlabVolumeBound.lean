import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.OrientedUnitSlabVolume
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
# Slab volume bound

A `Kakeya.Slab` of radius `r` has volume at most `8 * r`.

This follows from `oriented_unit_slab_volume`, since `S.carrier` equals
`orientedUnitSlab (S.offset • S.normal) S.normal S.radius`.
-/

noncomputable section

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Volume of a slab is at most 8 times its radius. -/
lemma slab_volume_le (S : Kakeya.Slab) :
    volume S.carrier ≤ ENNReal.ofReal (8 * S.radius) := by
  let n : Point3 := S.normal
  let c : ℝ := S.offset
  let center : Point3 := c • n
  have hn : ‖n‖ = 1 := S.normal_unit
  have h_inner_n : inner ℝ n n = 1 := by
    have h : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
    rw [h, hn] <;> norm_num
  have h_center_inner : inner ℝ center n = c := by
    dsimp only [center]
    have h : inner ℝ (c • n) n = c * inner ℝ n n := real_inner_smul_left n n c
    rw [h, h_inner_n] <;> ring
  have h_center_in_H : center ∈ S.hyperplane := by
    simp only [Kakeya.Slab.hyperplane, Set.mem_setOf_eq]
    exact h_center_inner
  have h_nonempty : S.hyperplane.Nonempty := ⟨center, h_center_in_H⟩
  have h_infDist : ∀ (x : Point3), Metric.infDist x S.hyperplane = |inner ℝ x n - c| := by
    intro x
    have h1 : ∀ y ∈ S.hyperplane, |inner ℝ x n - c| ≤ dist x y := by
      intro y hy
      have h_y_in : inner ℝ y n = c := by simpa [Kakeya.Slab.hyperplane] using hy
      have h2 : inner ℝ (x - y) n = inner ℝ x n - c := by
        rw [inner_sub_left, h_y_in] <;> ring
      have h3 : |inner ℝ (x - y) n| ≤ ‖x - y‖ * ‖n‖ := abs_real_inner_le_norm (x - y) n
      rw [h2, hn] at h3
      simpa [dist_eq_norm] using h3
    have h1' : (|inner ℝ x n - c|) ∈ lowerBounds (dist x '' S.hyperplane) := by
      intro d hd
      rcases hd with ⟨y, hy, rfl⟩
      exact h1 y hy
    have h_glb : IsGLB (dist x '' S.hyperplane) (Metric.infDist x S.hyperplane) :=
      Metric.isGLB_infDist h_nonempty
    have h_lower : |inner ℝ x n - c| ≤ Metric.infDist x S.hyperplane :=
      h_glb.2 h1'
    let z : Point3 := x - (inner ℝ x n - c) • n
    have hz_in_H : z ∈ S.hyperplane := by
      simp only [Kakeya.Slab.hyperplane, Set.mem_setOf_eq]
      have h : inner ℝ z n = c := by
        dsimp only [z]
        rw [inner_sub_left]
        have h2 : inner ℝ ((inner ℝ x n - c) • n) n = (inner ℝ x n - c) * inner ℝ n n :=
          real_inner_smul_left n n (inner ℝ x n - c)
        rw [h2, h_inner_n] <;> ring
      exact h
    have h_upper : Metric.infDist x S.hyperplane ≤ dist x z :=
      Metric.infDist_le_dist_of_mem hz_in_H
    have h_dist : dist x z = |inner ℝ x n - c| := by
      dsimp only [z]
      have h : x - z = (inner ℝ x n - c) • n := by simp [z] <;> abel
      rw [dist_eq_norm, h, norm_smul, hn]
      <;> rw [Real.norm_eq_abs] <;> ring
    rw [h_dist] at h_upper
    exact le_antisymm h_upper h_lower
  have h1 : S.carrier = orientedUnitSlab center n S.radius := by
    ext x
    simp only [Kakeya.Slab.carrier, orientedUnitSlab, Set.mem_inter_iff, Set.mem_setOf_eq]
    have h2 : x ∈ Metric.cthickening S.radius S.hyperplane ↔
        |inner ℝ x n - c| ≤ S.radius := by
      have h_ne_top : Metric.infEDist x S.hyperplane ≠ ⊤ :=
        Metric.infEDist_ne_top h_nonempty
      have h_edist : Metric.infEDist x S.hyperplane = ENNReal.ofReal (Metric.infDist x S.hyperplane) := by
        have h_def : Metric.infDist x S.hyperplane = ENNReal.toReal (Metric.infEDist x S.hyperplane) := by
          rfl
        rw [h_def]
        exact (ENNReal.ofReal_toReal h_ne_top).symm
      have h_radius_nonneg : 0 ≤ S.radius := S.radius_nonneg
      have h_cthick : x ∈ Metric.cthickening S.radius S.hyperplane ↔
          Metric.infDist x S.hyperplane ≤ S.radius := by
        rw [Metric.mem_cthickening_iff, h_edist]
        exact ENNReal.ofReal_le_ofReal_iff h_radius_nonneg
      rw [h_cthick, h_infDist x]
    have h5 : inner ℝ (x - center) n = inner ℝ x n - c := by
      rw [inner_sub_left, h_center_inner] <;> ring
    rw [h2, h5]
  rw [h1]
  exact oriented_unit_slab_volume center n S.radius hn S.radius_nonneg

end Kakeya.Assouad
