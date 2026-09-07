import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalRescaling
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.LocalThickening
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Diagonal re-tubing lemma

The diagonal map φ(x,y,z) = (x, m²/100·y, 100/m·z) is (100/m)-Lipschitz
for 0 < m ≤ 1. Therefore the image of a δ-thickening of any set S under
φ is contained in the (100/m · δ)-thickening of φ '' S.

This is the foundation for Lemma 8 cover transfer: coarse tubes at scale
ρ map to sets covered by tubes at scale (100/m)·ρ.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The diagonal rescaling map is (100/m)-Lipschitz. -/
lemma diagonalRescalingMap_lipschitz
    (m : ℝ) (hm : 0 < m) (hm_le_one : m ≤ 1) :
    LipschitzWith (⟨100 / m, by positivity⟩ : NNReal)
      (diagonalRescalingMap m) := by
  have hK_pos : 0 < 100 / m := by positivity
  have h_m2_le : m ^ 2 ≤ 1 := by nlinarith
  have h_a_le_b : m ^ 2 / 100 ≤ 100 / m := by
    have h3 : m ^ 2 / 100 ≤ 1 / 100 := by
      have h4 : m ^ 2 ≤ 1 := h_m2_le
      have h5 : m ^ 2 / 100 ≤ 1 / 100 := by
        calc m ^ 2 / 100
          = (1 / 100 : ℝ) * m ^ 2 := by ring
        _ ≤ (1 / 100 : ℝ) * 1 := by gcongr
        _ = 1 / 100 := by ring
      exact h5
    have h6 : 1 / 100 ≤ 100 / m := by
      have h7 : 0 < m := hm
      have h8 : 1 / m ≥ 1 := one_le_one_div hm hm_le_one
      have h9 : 100 / m ≥ 100 := by
        calc 100 / m
          = 100 * (1 / m) := by ring
        _ ≥ 100 * 1 := by gcongr
        _ = 100 := by ring
      linarith
    linarith
  have h_scale1 : (m ^ 2 / 100) ^ 2 ≤ (100 / m) ^ 2 := by
    have h1 : 0 ≤ m ^ 2 / 100 := by positivity
    nlinarith
  have h_scale2 : (1 : ℝ) ≤ 100 / m := by
    have h3 : 1 ≤ 1 / m := one_le_one_div hm hm_le_one
    have h4 : 1 / m ≤ 100 / m := by
      have h5 : (1 : ℝ) ≤ 100 := by norm_num
      have h6 : 0 < m := hm
      calc 1 / m
        = 1 * (1 / m) := by ring
      _ ≤ 100 * (1 / m) := by gcongr
      _ = 100 / m := by ring
    linarith
  have h1 : ∀ (x y : Point3),
      dist (diagonalRescalingMap m x) (diagonalRescalingMap m y) ≤
        (100 / m) * dist x y := by
    intro x y
    let d := x - y
    have h2 : diagonalRescalingMap m x - diagonalRescalingMap m y =
        diagonalRescalingMap m d := by
      ext i
      fin_cases i <;> simp [diagonalRescalingMap_apply, point3, d] <;> ring
    have h3 : ‖diagonalRescalingMap m d‖ ^ 2 =
        (d 0) ^ 2 + (m ^ 2 / 100 * d 1) ^ 2 + (100 / m * d 2) ^ 2 := by
      rw [diagonalRescalingMap_apply]
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [point3, Fin.sum_univ_succ] <;> ring
    have h5 : ‖d‖ ^ 2 = (d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq] <;> simp [Fin.sum_univ_succ] <;> ring
    have h4 : ‖diagonalRescalingMap m d‖ ^ 2 ≤ (100 / m) ^ 2 * ‖d‖ ^ 2 := by
      rw [h3, h5]
      have h6 : (d 0) ^ 2 ≤ (100 / m) ^ 2 * (d 0) ^ 2 := by
        have h7 : (1 : ℝ) ^ 2 ≤ (100 / m) ^ 2 := by nlinarith
        nlinarith
      have h8 : (m ^ 2 / 100 * d 1) ^ 2 ≤ (100 / m) ^ 2 * (d 1) ^ 2 := by
        have h9 : (m ^ 2 / 100) ^ 2 ≤ (100 / m) ^ 2 := h_scale1
        nlinarith
      have h10 : (100 / m * d 2) ^ 2 ≤ (100 / m) ^ 2 * (d 2) ^ 2 := by
        ring_nf <;> nlinarith
      nlinarith
    have h11 : 0 ≤ ‖diagonalRescalingMap m d‖ := by positivity
    have h12 : 0 ≤ (100 / m) * ‖d‖ := by positivity
    have h13 : ‖diagonalRescalingMap m d‖ ≤ (100 / m) * ‖d‖ := by nlinarith
    calc
      dist (diagonalRescalingMap m x) (diagonalRescalingMap m y)
        = ‖diagonalRescalingMap m x - diagonalRescalingMap m y‖ := by
          rw [dist_eq_norm]
      _ = ‖diagonalRescalingMap m d‖ := by rw [h2]
      _ ≤ (100 / m) * ‖d‖ := h13
      _ = (100 / m) * dist x y := by
        have h14 : ‖d‖ = dist x y := by
          simp [d, dist_eq_norm] <;> ring
        rw [h14]
  exact lipschitzWith_iff_dist_le_mul.mpr h1

/-- The diagonal map scales thickenings by at most K = 100/m. -/
lemma diagonalRescalingMap_image_cthickening
    (m : ℝ) (hm : 0 < m) (hm_le_one : m ≤ 1)
    {S : Set Point3} {δ : ℝ} (hδ : 0 ≤ δ) :
    diagonalRescalingMap m '' (cthickening δ S) ⊆
    cthickening ((100 / m) * δ) (diagonalRescalingMap m '' S) := by
  have hL : LipschitzWith (⟨100 / m, by positivity⟩ : NNReal) (diagonalRescalingMap m) :=
    diagonalRescalingMap_lipschitz m hm hm_le_one
  have hL_on : LipschitzOnWith (⟨100 / m, by positivity⟩ : NNReal)
      (diagonalRescalingMap m) Set.univ :=
    hL.lipschitzOnWith
  have hthick : cthickening δ S ⊆ (Set.univ : Set Point3) := by simp
  exact lipschitzOn_image_cthickening hL_on hthick hδ

/--
Re-tubing: image of a δ-tube carrier is contained in the (K·δ)-thickening
of the image segment, where K = 100/m.
-/
lemma diagonalRescalingMap_tube_image
    (m : ℝ) (hm : 0 < m) (hm_le_one : m ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (T : Kakeya.DeltaTube δ) :
    diagonalRescalingMap m '' T.carrier ⊆
    cthickening ((100 / m) * δ)
      (diagonalRescalingMap m '' (unitSegment T.base T.direction)) := by
  have h1 : T.carrier = cthickening δ (unitSegment T.base T.direction) := by rfl
  rw [h1]
  exact diagonalRescalingMap_image_cthickening m hm hm_le_one (hδ := hδ)

end Kakeya.Assouad

end
