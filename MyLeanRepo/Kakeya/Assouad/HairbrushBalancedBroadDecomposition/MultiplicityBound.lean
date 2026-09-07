import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.AdditiveVolumeFromMultiplicity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Multiplicity bound for angle-separated tube families

Pointwise multiplicity bound: at any point x, the number of tubes whose shading
contains x is at most `Nat.ceil (65 / δ^2)`.

## Proof outline

1. Tubes through x have directions whose pairwise acute angle is ≥ δ.
2. Acute angle α gives Euclidean distance ≥ (2/π) * α for unit vectors.
3. So directions are (2δ/π)-separated on the unit sphere.
4. Sphere packing bound: N ≤ 26 / ε² with ε = 2δ/π.
5. N ≤ 26π²/(4δ²) < 65/δ² (using π² < 10).

## Main results

- `acute_angle_dist_lower`: `dist v w ≥ (2/π) * acute_angle`
- `sphere_separated_card_bound_annulus`: ε-separated unit vectors ≤ 26/ε²
- `multiplicity_bound_concrete`: multiplicity ≤ Nat.ceil(65/δ²)
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Finset Real MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-! ### Acute angle to Euclidean distance -/

/-- For unit vectors, Euclidean distance is at least `(2/π)` times the acute angle. -/
lemma acute_angle_dist_lower {v w : Point3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (2 / Real.pi) * hairbrushAcuteDirectionAngle v w ≤ dist v w := by
  set θ : ℝ := Real.arccos (inner ℝ v w) with hθ_def
  have hθ_nonneg : 0 ≤ θ := Real.arccos_nonneg _
  have hθ_le_pi : θ ≤ Real.pi := Real.arccos_le_pi _
  have hθ2_nonneg : 0 ≤ θ / 2 := by linarith
  have hθ2_le : θ / 2 ≤ Real.pi / 2 := by linarith

  have h_inner_bound1 : -1 ≤ inner ℝ v w := by
    have h : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
    rw [hv, hw] at h; linarith [abs_le.mp h]
  have h_inner_bound2 : inner ℝ v w ≤ 1 := by
    have h : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
    rw [hv, hw] at h; linarith [abs_le.mp h]
  have h_cos : inner ℝ v w = Real.cos θ := by
    rw [hθ_def, Real.cos_arccos h_inner_bound1 h_inner_bound2]

  have h_dist_sq : dist v w ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    have h1 : dist v w = ‖v - w‖ := by rfl
    rw [h1]
    have h2 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 := norm_sub_sq_real v w
    rw [h2, hv, hw, h_cos]
    have h6 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h_tmp : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := Real.cos_two_mul (θ / 2)
      have h : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
        rw [show 2 * (θ / 2) = θ by ring] at h_tmp
        linarith [Real.sin_sq_add_cos_sq (θ / 2)]
      exact h
    rw [h6] <;> ring
  have h_sin_nonneg : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h_dist : dist v w = 2 * Real.sin (θ / 2) := by
    have h1 : (dist v w) ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
      rw [h_dist_sq] <;> ring
    have h2 : 0 ≤ dist v w := dist_nonneg
    have h3 : 0 ≤ 2 * Real.sin (θ / 2) := by positivity
    nlinarith

  have h_sin_bound : (2 / Real.pi) * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin hθ2_nonneg hθ2_le

  have h_acute_le_theta : hairbrushAcuteDirectionAngle v w ≤ θ := by
    simp [hairbrushAcuteDirectionAngle, hθ_def] <;> linarith

  calc (2 / Real.pi) * hairbrushAcuteDirectionAngle v w
    ≤ (2 / Real.pi) * θ := by gcongr
  _ = 2 * ((2 / Real.pi) * (θ / 2)) := by ring
  _ ≤ 2 * Real.sin (θ / 2) := by gcongr
  _ = dist v w := h_dist.symm

/-! ### Sphere packing via annulus volume -/

/-- Sphere packing bound: ε-separated unit vectors have ≤ 26/ε² elements. -/
lemma sphere_separated_card_bound_annulus
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {s : Finset Point3}
    (hs1 : ∀ v ∈ s, ‖v‖ = 1)
    (hs2 : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ε ≤ dist v w) :
    (s.card : ℝ) ≤ 26 / ε ^ 2 := by
  set r : ℝ := ε / 2 with hr_def
  have hr_pos : 0 < r := by positivity
  have h1mr_pos : 0 < 1 - r := by linarith
  let B : Point3 → Set Point3 := fun x => ball x r
  let outer : Set Point3 := ball (0 : Point3) (1 + r)
  let inner : Set Point3 := ball (0 : Point3) (1 - r)
  let annulus : Set Point3 := outer \ inner
  let V : ENNReal := volume (ball (0 : Point3) 1)
  have hV_pos : 0 < V := IsOpen.measure_pos volume isOpen_ball ⟨0, by simp⟩
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_ne_top : V ≠ ⊤ := by
    have h : V = ENNReal.ofReal (Real.pi * 4 / 3) := by
      simpa [V] using EuclideanSpace.volume_ball_fin_three (0 : Point3) 1
    rw [h]
    exact ENNReal.ofReal_ne_top

  have h_vol_scale : ∀ (a : Point3) (t : ℝ), 0 ≤ t →
      volume (ball a t) = ENNReal.ofReal (t ^ 3) * V := by
    intro a t ht
    have h_main : volume (ball a t) =
        ENNReal.ofReal (t ^ Module.finrank ℝ Point3) * V :=
      MeasureTheory.Measure.addHaar_ball (μ := volume) (x := a) (hr := ht)
    have h_finrank : Module.finrank ℝ Point3 = 3 := by simp [Point3]
    rw [h_main, h_finrank]

  have h_vol_B : ∀ x ∈ s, volume (B x) = ENNReal.ofReal (r ^ 3) * V := by
    intro x _
    exact h_vol_scale x r (by linarith)

  have h_vol_outer : volume outer = ENNReal.ofReal ((1 + r) ^ 3) * V :=
    h_vol_scale (0 : Point3) (1 + r) (by linarith)

  have h_vol_inner : volume inner = ENNReal.ofReal ((1 - r) ^ 3) * V :=
    h_vol_scale (0 : Point3) (1 - r) (by linarith)

  have h_disj : Set.PairwiseDisjoint (s : Set Point3) B := by
    intro x hx y hy hxy
    have h_goal : Disjoint (B x) (B y) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have h1 : dist z x < r := mem_ball.mp hz1
      have h2 : dist z y < r := mem_ball.mp hz2
      have h3 : dist x y < ε := by
        calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
             _ = dist z x + dist z y := by rw [dist_comm x z]
             _ < r + r := by linarith
             _ = ε := by ring
      have h4 : ε ≤ dist x y := hs2 x hx y hy hxy
      linarith
    exact h_goal

  have h_sub : (⋃ x ∈ s, B x) ⊆ annulus := by
    intro z hz
    have h_exists : ∃ (x : Point3), x ∈ s ∧ z ∈ B x := by
      simpa [Set.mem_iUnion] using hz
    rcases h_exists with ⟨x, hx, hzx⟩
    have h5 : dist z x < r := mem_ball.mp hzx
    have h6 : ‖x‖ = 1 := hs1 x hx
    have h7 : ‖z‖ < 1 + r := by
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ = dist z x + ‖x‖ := by rfl
        _ < r + 1 := by linarith
        _ = 1 + r := by ring
    have h81 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      have h : ‖(x - z) + z‖ ≤ ‖x - z‖ + ‖z‖ := norm_add_le (x - z) z
      have h2 : (x - z) + z = x := by abel
      rw [h2] at h
      exact h
    have h82 : ‖x - z‖ = dist z x := by
      rw [← dist_eq_norm, dist_comm]
    have h83 : dist z x < r := h5
    have h84 : ‖x‖ < r + ‖z‖ := by
      rw [h82] at h81
      linarith
    have h9 : ‖x‖ = 1 := h6
    have h8 : ‖z‖ > 1 - r := by linarith
    have h9 : z ∈ outer := by simpa [outer, dist_eq_norm] using h7
    have h10 : z ∉ inner := by
      intro h11
      have h12 : ‖z‖ < 1 - r := by simpa [inner, dist_eq_norm] using h11
      linarith
    exact ⟨h9, h10⟩

  have h_meas : ∀ x ∈ s, MeasurableSet (B x) := by
    intro x _
    exact isOpen_ball.measurableSet

  have h_sum_vol : volume (⋃ x ∈ s, B x) =
      (s.card : ENNReal) * ENNReal.ofReal (r ^ 3) * V := by
    have h1 : volume (⋃ x ∈ s, B x) = ∑ x ∈ s, volume (B x) :=
      measure_biUnion_finset h_disj h_meas
    rw [h1]
    have h2 : ∑ x ∈ s, volume (B x) = ∑ x ∈ s, (ENNReal.ofReal (r ^ 3) * V) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact h_vol_B x hx
    rw [h2]
    have h3 : ∑ x ∈ s, (ENNReal.ofReal (r ^ 3) * V) =
        (s.card : ENNReal) * ENNReal.ofReal (r ^ 3) * V := by
      simp [Finset.sum_const, mul_assoc]
      <;> ring
    exact h3

  have hms_outer : MeasurableSet outer := isOpen_ball.measurableSet
  have hms_inner : MeasurableSet inner := isOpen_ball.measurableSet
  have hms_annulus : MeasurableSet annulus := hms_outer.diff hms_inner

  have h_inner_sub_outer : inner ⊆ outer := by
    intro z hz
    have h : dist z 0 < 1 - r := by simpa [inner] using hz
    have h' : dist z 0 < 1 + r := by linarith
    simpa [outer] using h'

  have h_disj2 : Disjoint inner annulus := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    exact hy2.2 hy1

  have h_union : outer = inner ∪ annulus := by
    ext y
    simp only [annulus, inner, outer, Set.mem_union, Set.mem_sdiff]
    constructor
    · intro h
      by_cases h2 : y ∈ inner
      · exact Or.inl h2
      · exact Or.inr ⟨h, h2⟩
    · rintro (h | h)
      · exact h_inner_sub_outer h
      · exact h.1

  have h_vol_add : volume outer = volume inner + volume annulus := by
    rw [h_union]
    exact measure_union h_disj2 hms_annulus

  have h_nonneg_inner : 0 ≤ (1 - r) ^ 3 := by positivity
  have h_sub' : volume inner ≤ volume outer := by
    rw [h_vol_inner, h_vol_outer]
    have h : (1 - r) ^ 3 ≤ (1 + r) ^ 3 := by gcongr <;> linarith
    have h' : ENNReal.ofReal ((1 - r) ^ 3) ≤ ENNReal.ofReal ((1 + r) ^ 3) :=
      ENNReal.ofReal_le_ofReal h
    exact mul_le_mul_of_nonneg_right h' (by positivity)

  have h_inner_ne_top : volume inner ≠ ⊤ := by
    rw [h_vol_inner]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV_ne_top

  have h_annulus_vol : volume annulus =
      ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) * V := by
    have h' : volume annulus = volume outer - volume inner := by
      rw [h_vol_add]
      rw [ENNReal.add_sub_cancel_left h_inner_ne_top]
    rw [h', h_vol_outer, h_vol_inner]
    have h_sub2 : ENNReal.ofReal ((1 - r) ^ 3) ≤ ENNReal.ofReal ((1 + r) ^ 3) := by
      gcongr <;> linarith
    have h_mul_sub : (ENNReal.ofReal ((1 + r) ^ 3) - ENNReal.ofReal ((1 - r) ^ 3)) * V =
        ENNReal.ofReal ((1 + r) ^ 3) * V - ENNReal.ofReal ((1 - r) ^ 3) * V :=
      ENNReal.sub_mul (fun _ _ => hV_ne_top)
    have h_ofReal_sub : ENNReal.ofReal ((1 + r) ^ 3) - ENNReal.ofReal ((1 - r) ^ 3) =
        ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) := by
      rw [ENNReal.ofReal_sub] <;> linarith
    calc ENNReal.ofReal ((1 + r) ^ 3) * V - ENNReal.ofReal ((1 - r) ^ 3) * V
      = (ENNReal.ofReal ((1 + r) ^ 3) - ENNReal.ofReal ((1 - r) ^ 3)) * V := h_mul_sub.symm
    _ = ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) * V := by rw [h_ofReal_sub]

  have h_main : (s.card : ENNReal) * ENNReal.ofReal (r ^ 3) * V ≤
      ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) * V := by
    calc (s.card : ENNReal) * ENNReal.ofReal (r ^ 3) * V
      = volume (⋃ x ∈ s, B x) := h_sum_vol.symm
    _ ≤ volume annulus := measure_mono h_sub
    _ = ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) * V := h_annulus_vol

  have h_iff : ∀ (a b : ENNReal), (a * V ≤ b * V) ↔ (a ≤ b) := by
    intro a b
    have h_comm1 : a * V = V * a := mul_comm a V
    have h_comm2 : b * V = V * b := mul_comm b V
    rw [h_comm1, h_comm2]
    exact ENNReal.mul_le_mul_iff_right hV_ne_zero hV_ne_top
  have h_cancel : (s.card : ENNReal) * ENNReal.ofReal (r ^ 3) ≤
      ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) :=
    (h_iff _ _).mp h_main

  have h_pos1 : 0 ≤ r ^ 3 := by positivity
  have h_pos_card : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg s.card
  have h_left : (s.card : ENNReal) * ENNReal.ofReal (r ^ 3) =
      ENNReal.ofReal ((s.card : ℝ) * r ^ 3) := by
    have h_cast : (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) := by norm_cast
    rw [h_cast]
    have h : ENNReal.ofReal ((s.card : ℝ) * r ^ 3) =
        ENNReal.ofReal (s.card : ℝ) * ENNReal.ofReal (r ^ 3) :=
      ENNReal.ofReal_mul h_pos_card
    exact h.symm
  rw [h_left] at h_cancel

  have h_pos_a : 0 ≤ (s.card : ℝ) * r ^ 3 := mul_nonneg (Nat.cast_nonneg s.card) h_pos1
  have h_pos_b : 0 ≤ (1 + r) ^ 3 - (1 - r) ^ 3 := by
    have h3 : (1 + r) ^ 3 ≥ (1 - r) ^ 3 := by gcongr <;> linarith
    linarith
  have h_ne_top1 : ENNReal.ofReal ((s.card : ℝ) * r ^ 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_ne_top2 : ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_to_real : ENNReal.toReal (ENNReal.ofReal ((s.card : ℝ) * r ^ 3)) ≤
      ENNReal.toReal (ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3))) :=
    (ENNReal.toReal_le_toReal h_ne_top1 h_ne_top2).mpr h_cancel
  have h_tr1 : ENNReal.toReal (ENNReal.ofReal ((s.card : ℝ) * r ^ 3)) = (s.card : ℝ) * r ^ 3 := by
    rw [ENNReal.toReal_ofReal h_pos_a]
  have h_tr2 : ENNReal.toReal (ENNReal.ofReal (((1 + r) ^ 3 - (1 - r) ^ 3))) = (1 + r) ^ 3 - (1 - r) ^ 3 := by
    rw [ENNReal.toReal_ofReal h_pos_b]
  have h_real : (s.card : ℝ) * r ^ 3 ≤ (1 + r) ^ 3 - (1 - r) ^ 3 := by
    rw [h_tr1, h_tr2] at h_to_real
    exact h_to_real

  have h5 : 0 < r ^ 3 := by positivity
  have h_bound : (s.card : ℝ) ≤ ((1 + r) ^ 3 - (1 - r) ^ 3) / r ^ 3 := by
    have h7 : (s.card : ℝ) * (r ^ 3) ≤ (1 + r) ^ 3 - (1 - r) ^ 3 := h_real
    have h9 : r ^ 3 ≠ 0 := h5.ne'
    have h10 : ((s.card : ℝ) * (r ^ 3)) / (r ^ 3) ≤ ((1 + r) ^ 3 - (1 - r) ^ 3) / (r ^ 3) := by gcongr
    have h11 : ((s.card : ℝ) * (r ^ 3)) / (r ^ 3) = (s.card : ℝ) := by
      have h9' : r ^ 3 ≠ 0 := h5.ne'
      apply (div_eq_iff h9').mpr
      <;> ring
    rw [h11] at h10
    exact h10
  have h10 : ((1 + r) ^ 3 - (1 - r) ^ 3) / r ^ 3 = 6 / r ^ 2 + 2 := by
    have h11 : (1 + r) ^ 3 - (1 - r) ^ 3 = 6 * r + 2 * r ^ 3 := by ring
    rw [h11]
    field_simp [hr_pos.ne'] <;> ring
  rw [h10] at h_bound
  have h12 : (s.card : ℝ) ≤ 6 / r ^ 2 + 2 := h_bound
  have h13 : 6 / r ^ 2 + 2 ≤ 26 / ε ^ 2 := by
    rw [hr_def]
    field_simp [hε.ne'] <;> nlinarith
  exact h12.trans h13

/-! ### Multiplicity bound -/

/-- Concrete multiplicity bound: for an angle-separated family, the number of
tubes whose shading contains any point x is at most `Nat.ceil (65 / δ ^ 2)`. -/
lemma multiplicity_bound_concrete {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (h_angle : HairbrushAngleSeparated F) :
    ∀ x, shadedMultiplicity' Y x ≤ Nat.ceil (65 / δ ^ 2) := by
  intro x
  let through : Finset (Kakeya.DeltaTube δ) :=
    F.filter fun T => x ∈ Y.carrier T
  have h_through_sub : through ⊆ F := Finset.filter_subset _ _

  let dirs : Finset Point3 := through.image fun T => T.direction
  have h_dirs_unit : ∀ v ∈ dirs, ‖v‖ = 1 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, _, rfl⟩
    exact T.direction_unit

  have h_dirs_sep : ∀ (v : Point3), v ∈ dirs → ∀ (w : Point3), w ∈ dirs →
      v ≠ w → (2 * δ / Real.pi) ≤ dist v w := by
    intro v hv w hw hne
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨U, hU, rfl⟩
    have hT_ne_U : T ≠ U := by
      intro h
      rw [h] at hne
      exact hne rfl
    have hT_F : T ∈ F := h_through_sub hT
    have hU_F : U ∈ F := h_through_sub hU
    have h_x_in_T : x ∈ Y.carrier T := (Finset.mem_filter.mp hT).2
    have h_x_in_U : x ∈ Y.carrier U := (Finset.mem_filter.mp hU).2
    have h_sub_T : Y.carrier T ⊆ T.carrier := Y.subset_tube hT_F
    have h_sub_U : Y.carrier U ⊆ U.carrier := Y.subset_tube hU_F
    have h_intersect : T.carrier ∩ U.carrier ≠ ∅ := by
      exact Set.nonempty_iff_ne_empty.mp ⟨x, h_sub_T h_x_in_T, h_sub_U h_x_in_U⟩
    have h_ang : δ ≤ hairbrushAcuteAngle T U :=
      h_angle T hT_F U hU_F hT_ne_U h_intersect
    have h_dist_lower : (2 / Real.pi) * hairbrushAcuteAngle T U ≤ dist T.direction U.direction :=
      acute_angle_dist_lower T.direction_unit U.direction_unit
    calc dist T.direction U.direction
      ≥ (2 / Real.pi) * hairbrushAcuteAngle T U := h_dist_lower
    _ ≥ (2 / Real.pi) * δ := by gcongr
    _ = 2 * δ / Real.pi := by ring

  set ε : ℝ := 2 * δ / Real.pi with hε_def
  have hε_pos : 0 < ε := by positivity
  have hε_le1 : ε ≤ 1 := by
    rw [hε_def]
    have hpi2 : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h : 2 * δ ≤ Real.pi := by linarith
    have hpos : 0 < Real.pi := Real.pi_pos
    calc (2 * δ) / Real.pi
        ≤ Real.pi / Real.pi := by gcongr
      _ = 1 := by field_simp [hpos.ne']
  have h_bound : (dirs.card : ℝ) ≤ 26 / ε ^ 2 :=
    sphere_separated_card_bound_annulus hε_pos hε_le1 h_dirs_unit h_dirs_sep

  have h_inj : Set.InjOn (fun (T : Kakeya.DeltaTube δ) => T.direction) (through : Set (Kakeya.DeltaTube δ)) := by
    intro T hT U hU h_eq
    by_contra hne
    have hT_F : T ∈ F := h_through_sub hT
    have hU_F : U ∈ F := h_through_sub hU
    have h_xT : x ∈ Y.carrier T := (Finset.mem_filter.mp hT).2
    have h_xU : x ∈ Y.carrier U := (Finset.mem_filter.mp hU).2
    have h_subT : Y.carrier T ⊆ T.carrier := Y.subset_tube hT_F
    have h_subU : Y.carrier U ⊆ U.carrier := Y.subset_tube hU_F
    have h_inter : T.carrier ∩ U.carrier ≠ ∅ := by
      exact Set.nonempty_iff_ne_empty.mp ⟨x, h_subT h_xT, h_subU h_xU⟩
    have h_ang : δ ≤ hairbrushAcuteAngle T U := h_angle T hT_F U hU_F hne h_inter
    have h_dist : (2 / Real.pi) * hairbrushAcuteAngle T U ≤ dist T.direction U.direction :=
      acute_angle_dist_lower T.direction_unit U.direction_unit
    have h_pos : 0 < (2 / Real.pi) * δ := by positivity
    have h_lower : (2 / Real.pi) * δ ≤ dist T.direction U.direction := by
      calc (2 / Real.pi) * δ
        ≤ (2 / Real.pi) * hairbrushAcuteAngle T U := by gcongr
      _ ≤ dist T.direction U.direction := h_dist
    have h_cont : 0 < dist T.direction U.direction := h_pos.trans_le h_lower
    have h_cont2 : 0 < dist U.direction U.direction := by
      have h : dist T.direction U.direction = dist U.direction U.direction := by
        congr
        <;> exact h_eq
      rw [h] at h_cont
      exact h_cont
    simpa using h_cont2
  have h_card_eq : through.card = dirs.card := by
    rw [← Finset.card_image_of_injOn h_inj] <;> rfl

  have h_pi_bound : Real.pi ^ 2 < 10 := by
    have h1 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
    have h2 : 0 < Real.pi := Real.pi_pos
    have h3 : Real.pi ^ 2 < (3.15 : ℝ) ^ 2 := by nlinarith
    have h4 : (3.15 : ℝ) ^ 2 < 10 := by norm_num
    exact h3.trans h4
  have h_26_div_eps2 : 26 / ε ^ 2 ≤ 65 / δ ^ 2 := by
    rw [hε_def]
    have h_pos : 0 < δ ^ 2 := by positivity
    have h_pos2 : 0 < Real.pi ^ 2 := by positivity
    field_simp [h_pos.ne', h_pos2.ne']
    <;> nlinarith [Real.pi_pos, h_pi_bound]
  have h_final : (through.card : ℝ) ≤ 65 / δ ^ 2 := by
    rw [h_card_eq]
    exact h_bound.trans h_26_div_eps2
  have h_le_ceil : (65 / δ ^ 2) ≤ (Nat.ceil (65 / δ ^ 2) : ℝ) := Nat.le_ceil (65 / δ ^ 2)
  have h_final2 : (through.card : ℝ) ≤ (Nat.ceil (65 / δ ^ 2) : ℝ) := h_final.trans h_le_ceil
  have h_nat_ceil : through.card ≤ Nat.ceil (65 / δ ^ 2) := by exact_mod_cast h_final2
  simpa [shadedMultiplicity'] using h_nat_ceil

end Kakeya.Assouad
