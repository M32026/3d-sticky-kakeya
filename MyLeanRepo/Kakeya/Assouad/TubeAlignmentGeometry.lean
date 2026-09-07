import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Geometric helper lemmas for tube axis alignment

1. Transverse bound: a point in a δ-tube has bounded inner product with any
   unit vector perpendicular to the tube axis.
2. Two-point diameter bound in a tube.
3. Trigonometric inequalities on `[0, π/2]`.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Assouad

/-- The unit segment of a tube is compact. -/
private lemma unit_segment_compact (base direction : Point3) :
    IsCompact (Kakeya.unitSegment base direction) := by
  apply IsCompact.image isCompact_Icc
  fun_prop

/-- The unit segment of a tube is nonempty. -/
private lemma unit_segment_nonempty (base direction : Point3) :
    (Kakeya.unitSegment base direction).Nonempty := by
  refine ⟨base, 0, by norm_num, by simp⟩

/--
If `x ∈ T.carrier`, there exists a point `p` on the tube axis segment with
`dist x p ≤ δ`.
-/
lemma exists_closest_on_axis {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (x : Point3) (hx : x ∈ T.carrier) :
    ∃ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧
      dist x (T.base + t • T.direction) ≤ δ := by
  let s := Kakeya.unitSegment T.base T.direction
  have hcompact : IsCompact s := unit_segment_compact T.base T.direction
  have hnonempty : s.Nonempty := unit_segment_nonempty T.base T.direction
  have hinf : Metric.infEDist x s ≤ ENNReal.ofReal δ := by
    exact (Metric.mem_cthickening_iff (x := x) (s := s)).mp hx
  rcases hcompact.exists_infEDist_eq_edist hnonempty x with ⟨p, hp, hedist⟩
  have hle : edist x p ≤ ENNReal.ofReal δ := by
    rw [← hedist]
    exact hinf
  have hdist : dist x p ≤ δ := by
    have h1 : edist x p = ENNReal.ofReal (dist x p) := edist_dist x p
    rw [h1] at hle
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp hle
  rcases hp with ⟨t, ht, rfl⟩
  exact ⟨t, ht, hdist⟩

/--
For any `x ∈ T.carrier` and any unit vector `w` perpendicular to `T.direction`,
we have `|inner ℝ (x - T.base) w| ≤ δ`.
-/
lemma tube_point_transverse_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (x : Point3) (hx : x ∈ T.carrier)
    (w : Point3) (hw : ‖w‖ = 1) (hperp : inner ℝ T.direction w = 0) :
    |inner ℝ (x - T.base) w| ≤ δ := by
  rcases exists_closest_on_axis hδ T x hx with ⟨t, _ht, hdist⟩
  let p := T.base + t • T.direction
  have h : inner ℝ (x - T.base) w = inner ℝ (x - p) w := by
    have h5 : x - T.base = (x - p) + (p - T.base) := by abel
    rw [h5]
    have h6 : inner ℝ (p - T.base) w = 0 := by
      have h7 : p - T.base = t • T.direction := by
        simp [p]
      rw [h7]
      rw [inner_smul_left, hperp]
      ; ring
    rw [inner_add_left, h6, add_zero]
  rw [h]
  have hcauchy : |inner ℝ (x - p) w| ≤ ‖x - p‖ * ‖w‖ :=
    abs_real_inner_le_norm (x - p) w
  rw [hw] at hcauchy
  have h9 : ‖x - p‖ = dist x p := by rw [dist_eq_norm]
  rw [h9] at hcauchy
  linarith

/--
For any two points `x, y ∈ T.carrier` and any unit vector `w`,
`|inner ℝ (x - y) w| ≤ |inner ℝ T.direction w| + 2 * δ`.

When `w` is perpendicular to `T.direction`, this gives `|inner ℝ (x - y) w| ≤ 2 * δ`.
-/
lemma tube_two_point_diameter_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (x y : Point3)
    (hx : x ∈ T.carrier) (hy : y ∈ T.carrier)
    (w : Point3) (hw : ‖w‖ = 1) :
    |inner ℝ (x - y) w| ≤ |inner ℝ T.direction w| + 2 * δ := by
  rcases exists_closest_on_axis hδ T x hx with ⟨t, ht, hdist_x⟩
  rcases exists_closest_on_axis hδ T y hy with ⟨s, hs, hdist_y⟩
  set p : Point3 := T.base + t • T.direction with hp_def
  set q : Point3 := T.base + s • T.direction with hq_def
  have hdecomp : x - y = (x - p) + ((t - s) • T.direction) + (q - y) := by
    have h1 : x - y = (x - p) + (p - q) + (q - y) := by abel
    have h2 : p - q = (t - s) • T.direction := by
      simp [hp_def, hq_def, sub_smul]
    rw [h1, h2]
  have h2 : inner ℝ (x - y) w =
      inner ℝ (x - p) w + (t - s) * inner ℝ T.direction w + inner ℝ (q - y) w := by
    rw [hdecomp]
    simp [inner_add_left, inner_smul_left]
  rw [h2]
  have h3 : |inner ℝ (x - p) w| ≤ δ := by
    have hcauchy : |inner ℝ (x - p) w| ≤ ‖x - p‖ * ‖w‖ :=
      abs_real_inner_le_norm (x - p) w
    rw [hw] at hcauchy
    have h4 : ‖x - p‖ = dist x p := by rw [dist_eq_norm]
    rw [h4] at hcauchy
    linarith
  have h4 : |inner ℝ (q - y) w| ≤ δ := by
    have hcauchy : |inner ℝ (q - y) w| ≤ ‖q - y‖ * ‖w‖ :=
      abs_real_inner_le_norm (q - y) w
    rw [hw] at hcauchy
    have h5 : ‖q - y‖ = dist y q := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [h5] at hcauchy
    linarith
  have hts : |t - s| ≤ 1 := by
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h : -1 ≤ t - s := by linarith
    have h' : t - s ≤ 1 := by linarith
    exact abs_le.mpr ⟨h, h'⟩
  have h5 : |(t - s) * inner ℝ T.direction w| ≤ |inner ℝ T.direction w| := by
    calc
      |(t - s) * inner ℝ T.direction w|
        = |t - s| * |inner ℝ T.direction w| := by rw [abs_mul]
      _ ≤ 1 * |inner ℝ T.direction w| := by gcongr
      _ = |inner ℝ T.direction w| := by ring
  calc
    |inner ℝ (x - p) w + (t - s) * inner ℝ T.direction w + inner ℝ (q - y) w|
      ≤ |inner ℝ (x - p) w| + |(t - s) * inner ℝ T.direction w| + |inner ℝ (q - y) w| :=
        by apply abs_add_three
    _ ≤ δ + |inner ℝ T.direction w| + δ := by gcongr
    _ = |inner ℝ T.direction w| + 2 * δ := by ring

/--
Specialization: for `w` perpendicular to `T.direction`,
`|inner ℝ (x - y) w| ≤ 2 * δ`.
-/
lemma tube_two_point_transverse_bound {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (x y : Point3)
    (hx : x ∈ T.carrier) (hy : y ∈ T.carrier)
    (w : Point3) (hw : ‖w‖ = 1) (hperp : inner ℝ T.direction w = 0) :
    |inner ℝ (x - y) w| ≤ 2 * δ := by
  have h := tube_two_point_diameter_bound hδ T x y hx hy w hw
  rw [hperp] at h
  simpa using h

/--
Slab two-point bound: if both `x` and `y` satisfy
`|inner ℝ (z - center) normal| ≤ width`, then
`|inner ℝ (x - y) normal| ≤ 2 * width`.
-/
lemma slab_two_point_bound (center normal : Point3) (width : ℝ) (x y : Point3)
    (hx : |inner ℝ (x - center) normal| ≤ width)
    (hy : |inner ℝ (y - center) normal| ≤ width) :
    |inner ℝ (x - y) normal| ≤ 2 * width := by
  have h : inner ℝ (x - y) normal =
      inner ℝ (x - center) normal - inner ℝ (y - center) normal := by
    simp [inner_sub_left]
  rw [h]
  calc
    |inner ℝ (x - center) normal - inner ℝ (y - center) normal|
      ≤ |inner ℝ (x - center) normal| + |inner ℝ (y - center) normal| :=
        abs_sub _ _
    _ ≤ width + width := by gcongr
    _ = 2 * width := by ring

/-- Trigonometric: `2 * sin(θ / 2) ≤ θ` for `0 ≤ θ`. -/
lemma two_sin_half_le (θ : ℝ) (hθ1 : 0 ≤ θ) :
    2 * Real.sin (θ / 2) ≤ θ := by
  have hpos : 0 ≤ θ / 2 := by linarith
  have h : Real.sin (θ / 2) ≤ θ / 2 := Real.sin_le hpos
  linarith

/-- Trigonometric: `θ ≤ (π / 2) * sin θ` for `0 ≤ θ ≤ π/2`. -/
lemma le_pi2_mul_sin (θ : ℝ) (hθ1 : 0 ≤ θ) (hθ2 : θ ≤ Real.pi / 2) :
    θ ≤ (Real.pi / 2) * Real.sin θ := by
  have h : (2 / Real.pi) * θ ≤ Real.sin θ := Real.mul_le_sin hθ1 hθ2
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  calc
    θ = (Real.pi / 2) * ((2 / Real.pi) * θ) := by
      field_simp [hpi_pos.ne']
    _ ≤ (Real.pi / 2) * Real.sin θ := by
      gcongr

end Kakeya.Assouad
