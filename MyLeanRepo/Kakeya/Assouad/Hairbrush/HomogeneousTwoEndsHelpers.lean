import MyLeanRepo.Kakeya.Assouad.Hairbrush.CrossSectionBound
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

/-!
# Supporting geometric lemmas for homogeneous two-ends refinement

Three lemmas:
1. Tube contained in midpoint ball (closed and corrected open versions)
2. Ball-tube intersection volume bound
3. ENNReal score maximization two-ends
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- A δ-tube is contained in the closed ball centered at its midpoint
with radius `1/2 + δ`.

Note: the open-ball version with radius `1/2 + δ` is **false** for the
closed thickening: a point at distance exactly δ from an endpoint lies
on the boundary. Use `tube_subset_midpoint_ball` with radius `1/2 + 2*δ`
for an open-ball containment. -/
lemma tube_subset_midpoint_closedBall {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ) :
    T.carrier ⊆ Metric.closedBall (T.base + (1 / 2 : ℝ) • T.direction) (1 / 2 + δ) := by
  let midpoint := T.base + (1 / 2 : ℝ) • T.direction
  have hsegment_compact : IsCompact (Kakeya.unitSegment T.base T.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  have hcarrier_eq : T.carrier = ⋃ (z : Point3) (_ : z ∈ Kakeya.unitSegment T.base T.direction),
      Metric.closedBall z δ :=
    hsegment_compact.cthickening_eq_biUnion_closedBall hδ.le
  intro x hx
  rw [hcarrier_eq] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨z, hz, hxball⟩
  rcases hz with ⟨t, ht, rfl⟩
  have hdist1 : dist x (T.base + t • T.direction) ≤ δ := by
    simpa [Metric.mem_closedBall] using hxball
  have hdist2 : dist (T.base + t • T.direction) midpoint ≤ 1 / 2 := by
    have h1 : (T.base + t • T.direction) - midpoint = (t - 1 / 2 : ℝ) • T.direction := by
      simp [midpoint, sub_smul] <;> abel
    have h2 : dist (T.base + t • T.direction) midpoint =
        ‖(T.base + t • T.direction) - midpoint‖ := by
      rw [dist_eq_norm]
    rw [h2, h1, norm_smul]
    have h3 : ‖(t - 1 / 2 : ℝ)‖ = |t - 1 / 2| := by
      simp [Real.norm_eq_abs]
    rw [h3, T.direction_unit]
    have h4 : 0 ≤ t := ht.1
    have h5 : t ≤ 1 := ht.2
    have h6 : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith
    linarith
  have h7 : dist x midpoint ≤ dist x (T.base + t • T.direction) + dist (T.base + t • T.direction) midpoint :=
    dist_triangle _ _ _
  have h8 : dist x midpoint ≤ 1 / 2 + δ := by linarith
  exact h8

/-- A δ-tube is contained in the open ball centered at its midpoint
with radius `1/2 + 2*δ`.

This is the corrected open-ball version; radius `1/2 + δ` does not work
because the tube uses closed thickening. -/
lemma tube_subset_midpoint_ball {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ) :
    T.carrier ⊆ Metric.ball (T.base + (1 / 2 : ℝ) • T.direction) (1 / 2 + 2 * δ) := by
  let midpoint := T.base + (1 / 2 : ℝ) • T.direction
  have h1 : T.carrier ⊆ Metric.closedBall midpoint (1 / 2 + δ) :=
    tube_subset_midpoint_closedBall hδ T
  intro x hx
  have h2 : dist x midpoint ≤ 1 / 2 + δ := h1 hx
  have h3 : dist x midpoint < 1 / 2 + 2 * δ := by linarith
  exact h3

/-- Volume bound for intersection of a δ-tube with an open ball of radius r.

The axial projection of the ball onto the tube axis spans at most `2*r`,
so the intersection is contained in an axial slab of width `2*r`. -/
lemma ball_tube_intersection_volume {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ)
    (x : Point3) (r : ℝ) (hr : 0 < r) :
    volume (T.carrier ∩ Metric.ball x r) ≤ ENNReal.ofReal (4 * δ^2 * (2 * r)) := by
  let π : Point3 → ℝ := fun y => inner ℝ (y - T.base) T.direction
  let a : ℝ := π x - r
  let b : ℝ := π x + r
  have hab : a ≤ b := by linarith
  have h1 : T.carrier ∩ Metric.ball x r ⊆ T.carrier ∩ {y | a ≤ π y ∧ π y ≤ b} := by
    intro y hy
    have hyT : y ∈ T.carrier := hy.1
    have hyball : y ∈ Metric.ball x r := hy.2
    have hdist : dist y x < r := hyball
    have h2 : |inner ℝ (y - x) T.direction| ≤ ‖y - x‖ * ‖T.direction‖ :=
      abs_real_inner_le_norm (y - x) T.direction
    have h3 : ‖T.direction‖ = 1 := T.direction_unit
    have h4 : |inner ℝ (y - x) T.direction| < r := by
      rw [h3] at h2
      have h5 : ‖y - x‖ < r := by simpa [dist_eq_norm] using hdist
      calc |inner ℝ (y - x) T.direction| ≤ ‖y - x‖ * 1 := h2
        _ = ‖y - x‖ := by ring
        _ < r := h5
    have h6 : π y = π x + inner ℝ (y - x) T.direction := by
      simp [π]
      rw [show y - T.base = (y - x) + (x - T.base) by abel]
      rw [inner_add_left] <;> ring
    have h7 : -r < inner ℝ (y - x) T.direction := (abs_lt.mp h4).1
    have h8 : inner ℝ (y - x) T.direction < r := (abs_lt.mp h4).2
    have h9 : a ≤ π y ∧ π y ≤ b := by
      rw [h6]
      constructor <;> linarith
    exact ⟨hyT, h9⟩
  have h10 : volume (T.carrier ∩ Metric.ball x r) ≤
      volume (T.carrier ∩ {y | a ≤ π y ∧ π y ≤ b}) := measure_mono h1
  have h11 : volume (T.carrier ∩ {y | a ≤ π y ∧ π y ≤ b}) ≤
      ENNReal.ofReal (4 * δ^2 * (b - a)) := tube_slab_volume_bound hδ T a b hab
  have h12 : b - a = 2 * r := by
    simp [a, b] <;> ring
  rw [h12] at h11
  exact h10.trans h11

/-- Volume bound for intersection of a δ-tube with a closed ball of radius r.

The axial projection of the closed ball onto the tube axis spans at most `2*r`,
so the intersection is contained in an axial slab of width `2*r`. -/
lemma closedBall_tube_intersection_volume {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ)
    (x : Point3) (r : ℝ) (hr : 0 ≤ r) :
    volume (T.carrier ∩ Metric.closedBall x r) ≤ ENNReal.ofReal (4 * δ^2 * (2 * r)) := by
  let π : Point3 → ℝ := fun y => inner ℝ (y - T.base) T.direction
  let a : ℝ := π x - r
  let b : ℝ := π x + r
  have hab : a ≤ b := by linarith
  have h1 : T.carrier ∩ Metric.closedBall x r ⊆ T.carrier ∩ {y | a ≤ π y ∧ π y ≤ b} := by
    intro y hy
    have hyT : y ∈ T.carrier := hy.1
    have hyball : dist y x ≤ r := hy.2
    have h2 : |inner ℝ (y - x) T.direction| ≤ ‖y - x‖ * ‖T.direction‖ :=
      abs_real_inner_le_norm (y - x) T.direction
    have h3 : ‖T.direction‖ = 1 := T.direction_unit
    have h4 : |inner ℝ (y - x) T.direction| ≤ r := by
      rw [h3] at h2
      have h5 : ‖y - x‖ ≤ r := by simpa [dist_eq_norm] using hyball
      calc |inner ℝ (y - x) T.direction| ≤ ‖y - x‖ * 1 := h2
        _ = ‖y - x‖ := by ring
        _ ≤ r := h5
    have h6 : π y = π x + inner ℝ (y - x) T.direction := by
      simp [π]
      rw [show y - T.base = (y - x) + (x - T.base) by abel]
      rw [inner_add_left] <;> ring
    have h7 : -r ≤ inner ℝ (y - x) T.direction := (abs_le.mp h4).1
    have h8 : inner ℝ (y - x) T.direction ≤ r := (abs_le.mp h4).2
    have h9 : a ≤ π y ∧ π y ≤ b := by
      rw [h6] <;> constructor <;> linarith
    exact ⟨hyT, h9⟩
  have h10 : volume (T.carrier ∩ Metric.closedBall x r) ≤
      volume (T.carrier ∩ {y | a ≤ π y ∧ π y ≤ b}) := measure_mono h1
  have h11 : volume (T.carrier ∩ {y | a ≤ π y ∧ π y ≤ b}) ≤
      ENNReal.ofReal (4 * δ^2 * (b - a)) := tube_slab_volume_bound hδ T a b hab
  have h12 : b - a = 2 * r := by
    simp [a, b] <;> ring
  rw [h12] at h11
  exact h10.trans h11

/-- Two-ends deduction from maximality of volume/r^zeta ratio.

If `(x0, r0)` maximizes `volume(S ∩ ball x t) / t^zeta` over all `x` and
`0 < t ≤ 2`, then for any ball `B(x, r)` with `0 < r ≤ 2`, the volume of
the restricted set `S ∩ B(x0, r0)` intersected with `B(x, r)` is at most
`(r/r0)^zeta * volume(S ∩ B(x0, r0))`. -/
lemma two_ends_from_maximizer {S : Set Point3} (hS : volume S ≠ ⊤)
    {zeta : ℝ} (hzeta_pos : 0 < zeta)
    {x0 x : Point3} {r0 r : ℝ} (hr0_pos : 0 < r0) (hr_pos : 0 < r) (hr_le_two : r ≤ 2)
    (hmax : ∀ (x : Point3) (t : ℝ), 0 < t → t ≤ 2 →
        volume (S ∩ Metric.ball x t) * ENNReal.ofReal (Real.rpow r0 zeta) ≤
        volume (S ∩ Metric.ball x0 r0) * ENNReal.ofReal (Real.rpow t zeta)) :
    volume ((S ∩ Metric.ball x0 r0) ∩ Metric.ball x r) ≤
    ENNReal.ofReal (Real.rpow (r / r0) zeta) * volume (S ∩ Metric.ball x0 r0) := by
  set V0 := volume (S ∩ Metric.ball x0 r0) with hV0_def
  set V := volume ((S ∩ Metric.ball x0 r0) ∩ Metric.ball x r) with hV_def
  have hV0_sub : (S ∩ Metric.ball x0 r0) ⊆ S := by
    intro y hy; exact hy.1
  have hV0_ne_top : V0 ≠ ⊤ := ne_top_of_le_ne_top hS (measure_mono hV0_sub)
  have hV_sub : ((S ∩ Metric.ball x0 r0) ∩ Metric.ball x r) ⊆ S := by
    intro y hy; exact hy.1.1
  have hV_ne_top : V ≠ ⊤ := ne_top_of_le_ne_top hS (measure_mono hV_sub)
  have h1 : V ≤ volume (S ∩ Metric.ball x r) := by
    rw [hV_def]
    apply measure_mono
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  set c := ENNReal.ofReal (Real.rpow r0 zeta) with hc_def
  set d := ENNReal.ofReal (Real.rpow r zeta) with hd_def
  have h2 := hmax x r hr_pos hr_le_two
  have h3 : V * c ≤ V0 * d := by
    calc V * c
        ≤ volume (S ∩ Metric.ball x r) * c := by gcongr
      _ ≤ V0 * d := h2
  have hc_pos_real : 0 < Real.rpow r0 zeta := Real.rpow_pos_of_pos hr0_pos zeta
  have hd_pos_real : 0 < Real.rpow r zeta := Real.rpow_pos_of_pos hr_pos zeta
  have hc_ne_zero : c ≠ 0 := by
    rw [hc_def]; positivity
  have hc_ne_top : c ≠ ⊤ := by
    rw [hc_def]; exact ENNReal.ofReal_ne_top
  have hd_ne_top : d ≠ ⊤ := by
    rw [hd_def]; exact ENNReal.ofReal_ne_top
  have hV_c_ne_top : V * c ≠ ⊤ := ENNReal.mul_ne_top hV_ne_top hc_ne_top
  have hV0_d_ne_top : V0 * d ≠ ⊤ := ENNReal.mul_ne_top hV0_ne_top hd_ne_top
  -- Convert inequality to Real via ofReal injection
  have h4 : ENNReal.ofReal (V * c).toReal = V * c := ENNReal.ofReal_toReal hV_c_ne_top
  have h5 : ENNReal.ofReal (V0 * d).toReal = V0 * d := ENNReal.ofReal_toReal hV0_d_ne_top
  have h7 : ENNReal.ofReal (V * c).toReal ≤ ENNReal.ofReal (V0 * d).toReal := by
    rw [h4, h5]; exact h3
  have h_nonneg2 : 0 ≤ (V0 * d).toReal := by positivity
  have h6 : (V * c).toReal ≤ (V0 * d).toReal := by
    exact (ENNReal.ofReal_le_ofReal_iff h_nonneg2).mp h7
  have h8 : (V * c).toReal = V.toReal * Real.rpow r0 zeta := by
    have h81 : (V * c).toReal = V.toReal * c.toReal := by
      rw [ENNReal.toReal_mul]
    rw [h81]
    have h82 : c.toReal = Real.rpow r0 zeta := by
      rw [hc_def, ENNReal.toReal_ofReal (by positivity)]
    rw [h82]
  have h9 : (V0 * d).toReal = V0.toReal * Real.rpow r zeta := by
    have h91 : (V0 * d).toReal = V0.toReal * d.toReal := by
      rw [ENNReal.toReal_mul]
    rw [h91]
    have h92 : d.toReal = Real.rpow r zeta := by
      rw [hd_def, ENNReal.toReal_ofReal (by positivity)]
    rw [h92]
  rw [h8, h9] at h6
  have h_r0_nonneg : 0 ≤ Real.rpow r0 zeta := by positivity
  have h10 : V.toReal ≤ V0.toReal * Real.rpow (r / r0) zeta := by
    have h101 : (V.toReal * Real.rpow r0 zeta) / Real.rpow r0 zeta = V.toReal := by
      field_simp [hc_pos_real.ne'] <;> ring
    have h102 : (V.toReal * Real.rpow r0 zeta) / Real.rpow r0 zeta ≤
        (V0.toReal * Real.rpow r zeta) / Real.rpow r0 zeta :=
      div_le_div_of_nonneg_right h6 h_r0_nonneg
    have h103 : (V0.toReal * Real.rpow r zeta) / Real.rpow r0 zeta =
        V0.toReal * (Real.rpow r zeta / Real.rpow r0 zeta) := by
      rw [mul_div_assoc]
    have h104 : Real.rpow r zeta / Real.rpow r0 zeta = Real.rpow (r / r0) zeta := by
      exact Eq.symm (Real.div_rpow (show 0 ≤ r by linarith) (show 0 ≤ r0 by linarith) zeta)
    rw [h103, h104] at h102
    rw [h101] at h102
    exact h102
  have h13 : 0 ≤ V0.toReal := by positivity
  have h14_pos : 0 < Real.rpow (r / r0) zeta :=
    Real.rpow_pos_of_pos (div_pos hr_pos hr0_pos) zeta
  have h14 : 0 ≤ Real.rpow (r / r0) zeta := by linarith
  have h15 : 0 ≤ V0.toReal * Real.rpow (r / r0) zeta := mul_nonneg h13 h14
  have h16 : ENNReal.ofReal V.toReal ≤ ENNReal.ofReal (V0.toReal * Real.rpow (r / r0) zeta) :=
    ENNReal.ofReal_le_ofReal h10
  have h17 : ENNReal.ofReal (V0.toReal * Real.rpow (r / r0) zeta) =
      ENNReal.ofReal (Real.rpow (r / r0) zeta) * ENNReal.ofReal V0.toReal := by
    have h171 : ENNReal.ofReal (V0.toReal * Real.rpow (r / r0) zeta) =
        ENNReal.ofReal V0.toReal * ENNReal.ofReal (Real.rpow (r / r0) zeta) := by
      simp [ENNReal.ofReal_mul]
    rw [h171]
    exact mul_comm _ _
  have h18 : ENNReal.ofReal V0.toReal = V0 := ENNReal.ofReal_toReal hV0_ne_top
  have h19 : ENNReal.ofReal V.toReal = V := ENNReal.ofReal_toReal hV_ne_top
  calc V
      = ENNReal.ofReal V.toReal := h19.symm
    _ ≤ ENNReal.ofReal (V0.toReal * Real.rpow (r / r0) zeta) := h16
    _ = ENNReal.ofReal (Real.rpow (r / r0) zeta) * ENNReal.ofReal V0.toReal := h17
    _ = ENNReal.ofReal (Real.rpow (r / r0) zeta) * V0 := by rw [h18]

end Kakeya.Assouad
