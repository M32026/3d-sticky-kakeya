import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.GeometryHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabContainment
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabVolumeBound
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

/-!
# Slab geometry helpers for incidence grouping

Provides geometric and measure-theoretic helpers used in the finite-label
slab incidence grouping proof:

1. `tube_point_near_segment`: every tube point is within δ of its axis segment.
2. `tube_projection_variation`: projection onto a perpendicular normal varies
   by at most `θ + 2δ` on a tube.
3. `abs_floor_sub_le`: floor preserves integer diameter bounds.
4. `floor_image_bound_by_ref`: floor image of a bounded-diameter set is
   contained in a finite integer interval.
5. `measurable_strip_set`: strip sets defined by floor of projection are
   measurable.
6. `tube_in_strip_slab`: a tube with a point in a given strip is contained
   in an `O(w)` slab.
7. `tube_in_strip_slab_volume`: same with the explicit `100*w` volume bound.
-/

noncomputable section

open MeasureTheory Metric Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Every point of a δ-tube is within δ of some point on its unit segment. -/
lemma tube_point_near_segment {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ)
    (x : Point3) (hx : x ∈ T.carrier) :
    ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ dist x (T.base + t • T.direction) ≤ δ := by
  have h_seg_nonempty : (Kakeya.unitSegment T.base T.direction).Nonempty := by
    refine ⟨T.base, 0, by norm_num, by simp⟩
  have h_compact : IsCompact (Kakeya.unitSegment T.base T.direction) := by
    let f : ℝ → Point3 := fun t => T.base + t • T.direction
    have h_cont : Continuous f := by fun_prop
    have h : IsCompact (f '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image h_cont
    have h_eq : f '' Set.Icc (0 : ℝ) 1 = Kakeya.unitSegment T.base T.direction := by rfl
    rw [h_eq] at h; exact h
  rcases h_compact.exists_infEDist_eq_edist h_seg_nonempty x with ⟨y, hy, h_eq⟩
  have h_inf : infEDist x (Kakeya.unitSegment T.base T.direction) ≤ ENNReal.ofReal δ := hx
  rw [h_eq] at h_inf
  have h2 : edist x y = ENNReal.ofReal (dist x y) := by simp [edist_dist]
  rw [h2] at h_inf
  have hdist : dist x y ≤ δ := (ENNReal.ofReal_le_ofReal_iff hδ.le).mp h_inf
  rcases hy with ⟨t, ht, rfl⟩
  exact ⟨t, ht.1, ht.2, hdist⟩

/-- Variation of the projection of tube points onto a normal.

Given a tube T whose direction is within θ of v, and n ⊥ v, the projection
of any two points of T onto n differs by at most `θ + 2*δ`.

Since `δ ≤ θ`, this is at most `3*θ`. -/
lemma tube_projection_variation {δ θ : ℝ} (hδ : 0 < δ) (hθ : δ ≤ θ) (hθ1 : θ ≤ 1)
    (T : Kakeya.DeltaTube δ) (v n : Point3)
    (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hn_orth : inner ℝ v n = 0)
    (h_angle : hairbrushAcuteDirectionAngle T.direction v ≤ θ) :
    ∀ (x y : Point3), x ∈ T.carrier → y ∈ T.carrier →
      |inner ℝ x n - inner ℝ y n| ≤ θ + 2 * δ := by
  have h_dir_bound : |inner ℝ T.direction n| ≤ θ :=
    acute_angle_implies_perp_inner_bound T.direction_unit hv hn hn_orth hθ1 h_angle
  intro x y hx hy
  rcases tube_point_near_segment hδ T x hx with ⟨t_x, ht_x1, ht_x2, hdist_x⟩
  rcases tube_point_near_segment hδ T y hy with ⟨t_y, ht_y1, ht_y2, hdist_y⟩
  set y_x : Point3 := T.base + t_x • T.direction with hy_x_def
  set y_y : Point3 := T.base + t_y • T.direction with hy_y_def
  have h_tdiff_bound : |t_x - t_y| ≤ 1 := by
    have h1 : -1 ≤ t_x - t_y := by linarith
    have h2 : t_x - t_y ≤ 1 := by linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have h_eq : inner ℝ x n - inner ℝ y n =
      (t_x - t_y) * inner ℝ T.direction n +
      inner ℝ (x - y_x - (y - y_y)) n := by
    simp [hy_x_def, hy_y_def, inner_sub_left, inner_add_left, inner_smul_left] <;> ring
  rw [h_eq]
  have h1 : |(t_x - t_y) * inner ℝ T.direction n| ≤ θ := by
    calc
      |(t_x - t_y) * inner ℝ T.direction n|
        = |t_x - t_y| * |inner ℝ T.direction n| := by rw [abs_mul]
      _ ≤ 1 * θ := by gcongr <;> linarith
      _ = θ := by ring
  have h2 : |inner ℝ (x - y_x - (y - y_y)) n| ≤ 2 * δ := by
    have h_eq2 : x - y_x - (y - y_y) = (x - y_x) - (y - y_y) := by abel
    rw [h_eq2]
    have h3 : |inner ℝ ((x - y_x) - (y - y_y)) n| ≤
        |inner ℝ (x - y_x) n| + |inner ℝ (y - y_y) n| := by
      have h4 : inner ℝ ((x - y_x) - (y - y_y)) n =
          inner ℝ (x - y_x) n - inner ℝ (y - y_y) n := by
        rw [inner_sub_left]
      rw [h4]
      have h5 : |inner ℝ (x - y_x) n - inner ℝ (y - y_y) n| ≤
          |inner ℝ (x - y_x) n| + |inner ℝ (y - y_y) n| := by
        calc
          |inner ℝ (x - y_x) n - inner ℝ (y - y_y) n|
            ≤ |inner ℝ (x - y_x) n| + |-(inner ℝ (y - y_y) n)| := abs_add_le _ _
          _ = |inner ℝ (x - y_x) n| + |inner ℝ (y - y_y) n| := by rw [abs_neg]
      exact h5
    have h6 : |inner ℝ (x - y_x) n| ≤ dist x y_x := by
      have h7 : |inner ℝ (x - y_x) n| ≤ ‖x - y_x‖ * ‖n‖ := abs_real_inner_le_norm (x - y_x) n
      have h8 : ‖x - y_x‖ = dist x y_x := by simp [dist_eq_norm]
      rw [h8, hn] at h7; simpa using h7
    have h9 : |inner ℝ (y - y_y) n| ≤ dist y y_y := by
      have h10 : |inner ℝ (y - y_y) n| ≤ ‖y - y_y‖ * ‖n‖ := abs_real_inner_le_norm (y - y_y) n
      have h11 : ‖y - y_y‖ = dist y y_y := by simp [dist_eq_norm]
      rw [h11, hn] at h10; simpa using h10
    linarith
  calc
    |(t_x - t_y) * inner ℝ T.direction n + inner ℝ (x - y_x - (y - y_y)) n|
      ≤ |(t_x - t_y) * inner ℝ T.direction n| + |inner ℝ (x - y_x - (y - y_y)) n| :=
        abs_add_le _ _
    _ ≤ θ + 2 * δ := by linarith

/-- If `|x - y| ≤ n` for a natural number `n`, then `|Int.floor x - Int.floor y| ≤ n`. -/
lemma abs_floor_sub_le {x y : ℝ} {n : ℕ} (h : |x - y| ≤ (n : ℝ)) :
    |(Int.floor x : ℤ) - (Int.floor y : ℤ)| ≤ (n : ℤ) := by
  have h1 : x - y ≤ (n : ℝ) := (abs_le.mp h).2
  have h2 : y - x ≤ (n : ℝ) := by
    have h3 : |y - x| = |x - y| := by
      rw [show y - x = -(x - y) by ring, abs_neg]
    have h4 : |y - x| ≤ (n : ℝ) := by rw [h3]; exact h
    exact (abs_le.mp h4).2
  have h4 : (Int.floor x : ℝ) - (Int.floor y : ℝ) < (n : ℝ) + 1 := by
    have hfx : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have hfy : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
    linarith
  have h5 : (Int.floor x : ℤ) - (Int.floor y : ℤ) ≤ (n : ℤ) := by
    by_contra h6
    have h7 : (Int.floor x : ℤ) - (Int.floor y : ℤ) ≥ (n : ℤ) + 1 := by omega
    have h8 : (Int.floor x : ℝ) - (Int.floor y : ℝ) ≥ ((n : ℝ) + 1) := by exact_mod_cast h7
    linarith
  have h9 : (Int.floor y : ℝ) - (Int.floor x : ℝ) < (n : ℝ) + 1 := by
    have hfy : (Int.floor y : ℝ) ≤ y := Int.floor_le y
    have hfx : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    linarith
  have h10 : (Int.floor y : ℤ) - (Int.floor x : ℤ) ≤ (n : ℤ) := by
    by_contra h11
    have h12 : (Int.floor y : ℤ) - (Int.floor x : ℤ) ≥ (n : ℤ) + 1 := by omega
    have h13 : (Int.floor y : ℝ) - (Int.floor x : ℝ) ≥ ((n : ℝ) + 1) := by exact_mod_cast h12
    linarith
  have h14 : (Int.floor x : ℤ) - (Int.floor y : ℤ) ≥ -(n : ℤ) := by linarith
  exact abs_le.mpr ⟨h14, h5⟩

/-- The floor image of a set whose diameter from a reference point is at most
`n * w` is contained in an integer interval of radius `n` around the reference
floor value. Hence it has at most `2*n + 1` elements. -/
lemma floor_image_bound_by_ref {w : ℝ} (hw : 0 < w) {s : Set ℝ} {n : ℕ}
    (t0 : ℝ)
    (h_diam : ∀ x, x ∈ s → |x - t0| ≤ (n : ℝ) * w) :
    ∀ t ∈ s, Int.floor (t / w) ∈ Finset.Icc (Int.floor (t0 / w) - (n : ℤ)) (Int.floor (t0 / w) + (n : ℤ)) := by
  intro t ht
  have h1 : |t - t0| ≤ (n : ℝ) * w := h_diam t ht
  have h2 : |t / w - t0 / w| ≤ (n : ℝ) := by
    have h3 : t / w - t0 / w = (t - t0) / w := by ring
    rw [h3]
    have h4 : |(t - t0) / w| = |t - t0| / w := by
      rw [abs_div, abs_of_pos hw]
    rw [h4]
    have h5 : |t - t0| / w ≤ (n : ℝ) := by
      calc
        |t - t0| / w ≤ ((n : ℝ) * w) / w := by gcongr
        _ = (n : ℝ) := by field_simp [hw.ne'] <;> ring
    exact h5
  have h4 : |(Int.floor (t / w) : ℤ) - (Int.floor (t0 / w) : ℤ)| ≤ (n : ℤ) :=
    abs_floor_sub_le h2
  have h5 : -(n : ℤ) ≤ (Int.floor (t / w) : ℤ) - (Int.floor (t0 / w) : ℤ) := (abs_le.mp h4).1
  have h6 : (Int.floor (t / w) : ℤ) - (Int.floor (t0 / w) : ℤ) ≤ (n : ℤ) := (abs_le.mp h4).2
  simp only [Finset.mem_Icc]
  exact ⟨by linarith, by linarith⟩

/-- Measurability of a strip set defined by floor of a real-valued function. -/
lemma measurable_strip_set {n : Point3} {w : ℝ} (k : ℤ) :
    MeasurableSet {x : Point3 | Int.floor (inner ℝ x n / w) = k} := by
  have h1 : Continuous (fun x : Point3 => inner ℝ x n / w) := by fun_prop
  have h2 : MeasurableSet {t : ℝ | Int.floor t = k} := by
    have h3 : {t : ℝ | Int.floor t = k} = Set.Ico (k : ℝ) ((k : ℝ) + 1) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Ico]
      exact Int.floor_eq_iff
    rw [h3]
    exact measurableSet_Ico
  exact h1.measurable h2

/-- A tube with a point in a given strip is contained in an `O(w)` slab.

If T has a point x whose projection onto n lies in strip k of width w,
and the projection variation on T is at most `3*w`, then T is contained
in a slab of radius `4*w` centered at `(k + 1/2)*w`.

The slab volume is at most `32*w` by `slab_volume_le`, well within the
`100*w` bound required by the grouping statement. -/
lemma tube_in_strip_slab {δ θ w : ℝ} (hδ : 0 < δ) (hθ : δ ≤ θ) (hθ1 : θ ≤ 1)
    (hw : 0 < w) (hθw : θ + 2 * δ ≤ 3 * w)
    (T : Kakeya.DeltaTube δ) (hT_unit : T.IsInUnitBall)
    (v n : Point3) (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hn_orth : inner ℝ v n = 0)
    (h_angle : hairbrushAcuteDirectionAngle T.direction v ≤ θ)
    (x : Point3) (hx : x ∈ T.carrier) (k : ℤ)
    (hk : Int.floor (inner ℝ x n / w) = k) :
    ∃ (S : Kakeya.Slab), T.carrier ⊆ S.carrier ∧ S.radius ≤ 4 * w := by
  let offset : ℝ := (k : ℝ) * w + w / 2
  let radius : ℝ := 4 * w
  have hradius_nonneg : 0 ≤ radius := by positivity
  let S : Kakeya.Slab :=
    { normal := n
      offset := offset
      radius := radius
      normal_unit := hn
      radius_nonneg := hradius_nonneg }
  have h_proj_var : ∀ (z : Point3), z ∈ T.carrier →
      |inner ℝ z n - inner ℝ x n| ≤ θ + 2 * δ :=
    fun z hz => tube_projection_variation hδ hθ hθ1 T v n hv hn hn_orth h_angle z x hz hx
  have h_strip : (k : ℝ) * w ≤ inner ℝ x n ∧ inner ℝ x n < (k : ℝ) * w + w := by
    have h4 : (k : ℝ) ≤ inner ℝ x n / w ∧ inner ℝ x n / w < (k : ℝ) + 1 := by
      rw [← hk]
      exact ⟨Int.floor_le (inner ℝ x n / w), Int.lt_floor_add_one (inner ℝ x n / w)⟩
    have h5 : (k : ℝ) * w ≤ inner ℝ x n := by
      have h51 : (k : ℝ) ≤ inner ℝ x n / w := h4.1
      calc
        (k : ℝ) * w ≤ (inner ℝ x n / w) * w := by gcongr
        _ = inner ℝ x n := by field_simp [hw.ne'] <;> ring
    have h6 : inner ℝ x n < (k : ℝ) * w + w := by
      have h61 : inner ℝ x n / w < (k : ℝ) + 1 := h4.2
      calc
        inner ℝ x n = (inner ℝ x n / w) * w := by field_simp [hw.ne'] <;> ring
        _ < ((k : ℝ) + 1) * w := by gcongr
        _ = (k : ℝ) * w + w := by ring
    exact ⟨h5, h6⟩
  have h_main : ∀ (y : Point3), y ∈ T.carrier → |inner ℝ y n - offset| ≤ radius := by
    intro y hy
    have h6 : |inner ℝ y n - inner ℝ x n| ≤ θ + 2 * δ := h_proj_var y hy
    have h7 : |inner ℝ x n - offset| ≤ w / 2 := by
      have h71 : -(w / 2) ≤ inner ℝ x n - offset := by
        dsimp only [offset]
        linarith [h_strip.1]
      have h72 : inner ℝ x n - offset ≤ w / 2 := by
        dsimp only [offset]
        linarith [h_strip.2]
      exact abs_le.mpr ⟨h71, h72⟩
    calc
      |inner ℝ y n - offset|
        = |(inner ℝ y n - inner ℝ x n) + (inner ℝ x n - offset)| := by ring_nf
      _ ≤ |inner ℝ y n - inner ℝ x n| + |inner ℝ x n - offset| := abs_add_le _ _
      _ ≤ (θ + 2 * δ) + w / 2 := by gcongr
      _ ≤ 3 * w + w / 2 := by linarith [hθw]
      _ ≤ 4 * w := by linarith [hw]
  have h_H_nonempty : S.hyperplane.Nonempty := by
    have hinner_n : inner ℝ n n = (1 : ℝ) := by
      have h : inner ℝ n n = ‖n‖ ^ 2 := real_inner_self_eq_norm_sq n
      rw [h, hn] <;> norm_num
    have h2 : inner ℝ (offset • n) n = offset := by
      have h21 : inner ℝ (offset • n) n = offset * inner ℝ n n :=
        real_inner_smul_left n n offset
      rw [h21, hinner_n] <;> ring
    exact ⟨offset • n, by simpa [S, Kakeya.Slab.hyperplane] using h2⟩
  have h_containment : T.carrier ⊆ S.carrier := by
    intro y hy
    have h_ball : y ∈ Kakeya.DeltaTube.unitBall := hT_unit hy
    have h_final : |inner ℝ y n - offset| ≤ radius := h_main y hy
    have h_hyperplane : S.hyperplane = {z : Point3 | inner ℝ z n = offset} := by
      ext z; simp [S, Kakeya.Slab.hyperplane] <;> rfl
    have h_dist_eq : Metric.infDist y S.hyperplane = |inner ℝ y n - offset| := by
      rw [h_hyperplane]; exact dist_to_hyperplane hn
    have h_cthick : y ∈ Metric.cthickening S.radius S.hyperplane := by
      have h7 : Metric.infDist y S.hyperplane ≤ S.radius := by
        rw [h_dist_eq]; exact h_final
      have h9 : ENNReal.ofReal (Metric.infDist y S.hyperplane) = Metric.infEDist y S.hyperplane := by
        rw [← ENNReal.ofReal_toReal (Metric.infEDist_ne_top h_H_nonempty)] <;> rfl
      have h8 : Metric.infEDist y S.hyperplane ≤ ENNReal.ofReal S.radius := by
        rw [← h9]; exact ENNReal.ofReal_le_ofReal h7
      exact h8
    exact ⟨h_ball, h_cthick⟩
  exact ⟨S, h_containment, by rfl⟩

/-- Version of `tube_in_strip_slab` that directly gives the `100*w` volume
bound required by the slab incidence grouping statement. -/
lemma tube_in_strip_slab_volume {δ θ w : ℝ} (hδ : 0 < δ) (hθ : δ ≤ θ) (hθ1 : θ ≤ 1)
    (hw : 0 < w) (hθw : θ + 2 * δ ≤ 3 * w)
    (T : Kakeya.DeltaTube δ) (hT_unit : T.IsInUnitBall)
    (v n : Point3) (hv : ‖v‖ = 1) (hn : ‖n‖ = 1) (hn_orth : inner ℝ v n = 0)
    (h_angle : hairbrushAcuteDirectionAngle T.direction v ≤ θ)
    (x : Point3) (hx : x ∈ T.carrier) (k : ℤ)
    (hk : Int.floor (inner ℝ x n / w) = k) :
    ∃ (S : Kakeya.Slab), T.carrier ⊆ S.carrier ∧
      volume S.carrier ≤ ENNReal.ofReal (100 * w) := by
  rcases tube_in_strip_slab hδ hθ hθ1 hw hθw T hT_unit v n hv hn hn_orth h_angle x hx k hk
    with ⟨S, h_cont, h_rad⟩
  have h_vol : volume S.carrier ≤ ENNReal.ofReal (8 * S.radius) := slab_volume_le S
  have h_bound : 8 * S.radius ≤ 100 * w := by
    calc
      8 * S.radius ≤ 8 * (4 * w) := by gcongr
      _ = 32 * w := by ring
      _ ≤ 100 * w := by linarith [hw]
  exact ⟨S, h_cont, h_vol.trans (ENNReal.ofReal_le_ofReal h_bound)⟩

/-- Label consistency for a slab incidence group.

If a group's shading is defined by intersecting with the set of points whose
`pointLabel` equals `p`, then every point in the group's shading has direction
label equal to `p.1`. -/
lemma group_label_consistency
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {labelCount : ℕ} {label : Point3 → Fin labelCount}
    (n : Fin labelCount → Point3) (capRadius : ℝ)
    (pointLabel : Point3 → Fin labelCount × ℤ)
    (hpointLabel_def : ∀ x, pointLabel x = (label x, Int.floor (inner ℝ x (n (label x)) / capRadius)))
    (p : Fin labelCount × ℤ)
    (family_p : Kakeya.TubeFamily δ)
    (shading_p : Kakeya.Shading family_p)
    (h_shading_def : ∀ T ∈ family_p,
        shading_p.carrier T = Y.carrier T ∩ {x | pointLabel x = p}) :
    ∀ T, ∀ hT : T ∈ family_p, ∀ x ∈ shading_p.carrier T,
      label x = p.1 := by
  intro T hT x hx
  have h1 : x ∈ {x : Point3 | pointLabel x = p} := by
    have h2 : x ∈ shading_p.carrier T := hx
    rw [h_shading_def T hT] at h2
    exact h2.2
  have h3 : pointLabel x = p := h1
  have h4 : pointLabel x = (label x, Int.floor (inner ℝ x (n (label x)) / capRadius)) :=
    hpointLabel_def x
  rw [h4] at h3
  simpa using congr_arg Prod.fst h3

/-- Transfer of `IsTwoBroadAtScale` under pointwise restriction.

If `Y'` is obtained from `Y` by intersecting every carrier with a fixed set `S`,
then at every point `x ∈ Y'.union`, the through-family and near-family are
identical for `Y` and `Y'` (because `x ∈ S`). Hence the two-broadness
inequality transfers unchanged. -/
lemma two_broad_transfer_pointwise
    {δ theta eta : ℝ}
    {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    (h_broad : IsTwoBroadAtScale Y theta eta)
    (S : Set Point3)
    (Y' : Kakeya.Shading F)
    (hY'_def : ∀ T ∈ F, Y'.carrier T = Y.carrier T ∩ S) :
    IsTwoBroadAtScale Y' theta eta := by
  intro x hx
  have hxS : x ∈ S := by
    rcases hx with ⟨T, hT, hxT⟩
    have h : x ∈ Y.carrier T ∩ S := by
      rw [hY'_def T hT] at hxT <;> exact hxT
    exact h.2
  have hxY : x ∈ Y.union := by
    rcases hx with ⟨T, hT, hxT⟩
    refine ⟨T, hT, ?_⟩
    have h : x ∈ Y.carrier T ∩ S := by
      rw [hY'_def T hT] at hxT <;> exact hxT
    exact h.1
  rcases h_broad x hxY with ⟨thetaLocal, hδ, h1, h2, h_main⟩
  refine ⟨thetaLocal, hδ, h1, h2, ?_⟩
  have h_through : F.filter (fun T => x ∈ Y'.carrier T) =
      F.filter (fun T => x ∈ Y.carrier T) := by
    apply Finset.ext
    intro T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, h4⟩
      have h6 : x ∈ Y.carrier T ∩ S := by
        rw [hY'_def T hT] at h4 <;> exact h4
      exact ⟨hT, h6.1⟩
    · rintro ⟨hT, h4⟩
      have h6 : x ∈ Y'.carrier T := by
        rw [hY'_def T hT]
        exact ⟨h4, hxS⟩
      exact ⟨hT, h6⟩
  intro w hw r hr1 hr2
  have h_goal := h_main w hw r hr1 hr2
  dsimp only at h_goal ⊢
  rw [h_through]
  exact h_goal

/-- Transfer two-broadness from a shading on `F` to a shading on a subfamily `F'`.

Requires that every tube in `F` meeting the point is also in `F'`. -/
lemma two_broad_transfer_subfamily
    {δ theta eta : ℝ}
    {F : Kakeya.TubeFamily δ} {F' : Kakeya.TubeFamily δ} (hF'_sub : F' ⊆ F)
    (Y : Kakeya.Shading F) (Y' : Kakeya.Shading F')
    (h_carrier : ∀ T ∈ F', Y'.carrier T = Y.carrier T)
    (h_cover : ∀ (x : Point3), x ∈ Y'.union → ∀ T ∈ F, x ∈ Y.carrier T → T ∈ F')
    (h_broad : IsTwoBroadAtScale Y theta eta) :
    IsTwoBroadAtScale Y' theta eta := by
  intro x hx
  have hxY : x ∈ Y.union := by
    rcases hx with ⟨T, hT, hxT⟩
    exact ⟨T, hF'_sub hT, (h_carrier T hT) ▸ hxT⟩
  rcases h_broad x hxY with ⟨thetaLocal, hδ, h1, h2, h_main⟩
  refine ⟨thetaLocal, hδ, h1, h2, ?_⟩
  have h_through : F'.filter (fun T => x ∈ Y'.carrier T) = F.filter (fun T => x ∈ Y.carrier T) := by
    apply Finset.ext
    intro T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT', hmem⟩
      exact ⟨hF'_sub hT', (h_carrier T hT') ▸ hmem⟩
    · rintro ⟨hT, hmem⟩
      have hT' : T ∈ F' := h_cover x hx T hT hmem
      have hmem' : x ∈ Y'.carrier T := (h_carrier T hT').symm ▸ hmem
      exact ⟨hT', hmem'⟩
  intro w hw r hr1 hr2
  have h_goal := h_main w hw r hr1 hr2
  dsimp only at h_goal ⊢
  rw [h_through]
  exact h_goal

/-- Each tube occurs in at most 7000 slab incidence groups.

For each tube T:
- At most 1000 direction labels can appear on T (from label overlap).
- For each direction label j, the projection of T.carrier onto n j has
  diameter ≤ capRadius + 2*δ ≤ 3*capRadius, so at most 7 strip indices
  are met (using abs_floor_sub_le with n=3).
- Total: ≤ 1000 * 7 = 7000 groups per tube, well under 1000000.
-/
lemma tube_occurrence_bound
    {δ : ℝ} {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    {labelCount : ℕ}
    {label : Point3 → Fin labelCount}
    {center : Fin labelCount → Point3}
    {capRadius : ℝ}
    (hδ : 0 < δ) (hcap : δ ≤ capRadius) (hcap1 : capRadius ≤ 1)
    (hcenter_unit : ∀ j, ‖center j‖ = 1)
    (n : Fin labelCount → Point3)
    (hn_unit : ∀ j, ‖n j‖ = 1)
    (hn_orth : ∀ j, inner ℝ (center j) (n j) = 0)
    (h_pointwise : ∀ x ∈ Y.union, ∀ T ∈ F, x ∈ Y.carrier T →
        hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius)
    (h_label_overlap : ∀ T ∈ F,
        ((Finset.univ.filter fun j : Fin labelCount =>
            ∃ x ∈ Y.carrier T, label x = j).card : ENNReal) ≤ 1000)
    (groups : Finset (Fin labelCount × ℤ))
    (family : (Fin labelCount × ℤ) → Kakeya.TubeFamily δ)
    (h_family_def : ∀ p, family p = F.filter (fun T =>
        ∃ x ∈ Y.carrier T, label x = p.1 ∧
          Int.floor (inner ℝ x (n p.1) / capRadius) = p.2)) :
    ∑ p ∈ groups, (family p).enncard ≤ 1000000 * F.enncard := by
  have hcap_pos : 0 < capRadius := by linarith
  have h_main : ∀ T ∈ F, (groups.filter (fun p => T ∈ family p)).card ≤ 7000 := by
    intro T hT
    let J_T : Finset (Fin labelCount) :=
      Finset.univ.filter (fun j => ∃ x ∈ Y.carrier T, label x = j)
    have hJ_card : (J_T.card : ENNReal) ≤ 1000 := h_label_overlap T hT
    have hJ_card' : J_T.card ≤ 1000 := by exact_mod_cast hJ_card
    have h_witness : ∀ j ∈ J_T, ∃ (x : Point3), x ∈ Y.carrier T ∧ label x = j := by
      intro j hj
      simp only [J_T, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    let xfunc : Fin labelCount → Point3 := fun j =>
      if hj : j ∈ J_T then Classical.choose (h_witness j hj) else 0
    have hx1 : ∀ j ∈ J_T, xfunc j ∈ Y.carrier T := by
      intro j hj
      dsimp only [xfunc]
      rw [dif_pos hj]
      exact (Classical.choose_spec (h_witness j hj)).1
    have hx2 : ∀ j ∈ J_T, label (xfunc j) = j := by
      intro j hj
      dsimp only [xfunc]
      rw [dif_pos hj]
      exact (Classical.choose_spec (h_witness j hj)).2
    let K (j : Fin labelCount) : Finset ℤ :=
      Finset.Icc (Int.floor (inner ℝ (xfunc j) (n j) / capRadius) - 3)
                (Int.floor (inner ℝ (xfunc j) (n j) / capRadius) + 3)
    have hK_card : ∀ j ∈ J_T, (K j).card ≤ 7 := by
      intro j _
      simp [K] <;> omega
    have h_include : ∀ (p : Fin labelCount × ℤ), T ∈ family p →
        p.1 ∈ J_T ∧ p.2 ∈ K p.1 := by
      rintro ⟨j, k⟩ hTp
      have h_exists : ∃ (x : Point3), x ∈ Y.carrier T ∧ label x = j ∧
          Int.floor (inner ℝ x (n j) / capRadius) = k := by
        rw [h_family_def (j, k)] at hTp
        simp only [Finset.mem_filter] at hTp
        exact hTp.2
      rcases h_exists with ⟨x, hxY, hlabel, hstrip⟩
      have hj_J : j ∈ J_T := by
        simp only [J_T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, hxY, hlabel⟩
      have h_x_in_T : x ∈ T.carrier := Y.subset_tube hT hxY
      have h_xj_in_T : xfunc j ∈ T.carrier := Y.subset_tube hT (hx1 j hj_J)
      have h_xj_union : xfunc j ∈ Y.union := by
        exact ⟨T, hT, hx1 j hj_J⟩
      have h_angle : hairbrushAcuteDirectionAngle T.direction (center j) ≤ capRadius := by
        have h := h_pointwise (xfunc j) h_xj_union T hT (hx1 j hj_J)
        have hlabel_j : label (xfunc j) = j := hx2 j hj_J
        rw [hlabel_j] at h
        exact h
      have h_proj_var : |inner ℝ x (n j) - inner ℝ (xfunc j) (n j)| ≤ capRadius + 2 * δ :=
        tube_projection_variation hδ hcap hcap1 T (center j) (n j)
          (hcenter_unit j) (hn_unit j) (hn_orth j) h_angle x (xfunc j) h_x_in_T h_xj_in_T
      have h_abs : |inner ℝ x (n j) / capRadius - inner ℝ (xfunc j) (n j) / capRadius| ≤ 3 := by
        have h41 : |inner ℝ x (n j) - inner ℝ (xfunc j) (n j)| ≤ capRadius + 2 * δ := h_proj_var
        have h42 : |inner ℝ x (n j) - inner ℝ (xfunc j) (n j)| / capRadius ≤ (capRadius + 2 * δ) / capRadius :=
          div_le_div_of_nonneg_right h41 (by linarith)
        have h43 : (capRadius + 2 * δ) / capRadius ≤ 3 := by
          have h44 : capRadius + 2 * δ ≤ 3 * capRadius := by linarith [hcap]
          have h45 : (capRadius + 2 * δ) / capRadius ≤ (3 * capRadius) / capRadius :=
            div_le_div_of_nonneg_right h44 (by linarith)
          have h46 : (3 * capRadius) / capRadius = 3 := by
            field_simp [hcap_pos.ne'] <;> ring
          rw [h46] at h45
          exact h45
        have h47 : |(inner ℝ x (n j) - inner ℝ (xfunc j) (n j)) / capRadius| ≤ 3 := by
          rw [abs_div, abs_of_pos hcap_pos]
          exact le_trans h42 h43
        have h5 : (inner ℝ x (n j) - inner ℝ (xfunc j) (n j)) / capRadius =
            inner ℝ x (n j) / capRadius - inner ℝ (xfunc j) (n j) / capRadius := by ring
        rw [h5] at h47
        exact h47
      have h_floor : |(Int.floor (inner ℝ x (n j) / capRadius) : ℤ) -
          (Int.floor (inner ℝ (xfunc j) (n j) / capRadius) : ℤ)| ≤ 3 :=
        abs_floor_sub_le h_abs
      rw [hstrip] at h_floor
      have h_bounds : -3 ≤ k - Int.floor (inner ℝ (xfunc j) (n j) / capRadius) ∧
          k - Int.floor (inner ℝ (xfunc j) (n j) / capRadius) ≤ 3 := abs_le.mp h_floor
      simp only [K, Finset.mem_Icc]
      exact ⟨hj_J, by linarith, by linarith⟩
    let S_T : Finset (Fin labelCount × ℤ) :=
      Finset.biUnion J_T (fun j => Finset.image (fun k : ℤ => (j, k)) (K j))
    have h_subset : groups.filter (fun p => T ∈ family p) ⊆ S_T := by
      intro p hp
      have hTp : T ∈ family p := (Finset.mem_filter.mp hp).2
      have h1 : p.1 ∈ J_T ∧ p.2 ∈ K p.1 := h_include p hTp
      have h2 : p ∈ S_T := by
        rw [Finset.mem_biUnion]
        refine ⟨p.1, h1.1, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p.2, h1.2, ?_⟩
        simp
      exact h2
    calc
      (groups.filter (fun p => T ∈ family p)).card
        ≤ S_T.card := Finset.card_le_card h_subset
      _ ≤ ∑ j ∈ J_T, (Finset.image (fun k : ℤ => (j, k)) (K j)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ j ∈ J_T, (K j).card := by
          apply Finset.sum_le_sum
          intro j _
          exact Finset.card_image_le
      _ ≤ ∑ j ∈ J_T, 7 := by
          apply Finset.sum_le_sum
          intro j hj
          exact hK_card j hj
      _ = 7 * J_T.card := by
          simp [Finset.sum_const] <;> ring
      _ ≤ 7 * 1000 := by gcongr
      _ = 7000 := by norm_num
  have h1 : ∀ p ∈ groups, family p ⊆ F := by
    intro p _
    rw [h_family_def p]
    exact Finset.filter_subset _ _
  have h_double_count : ∑ p ∈ groups, (family p).enncard =
      ∑ T ∈ F, ↑((groups.filter (fun p => T ∈ family p)).card) := by
    calc
      ∑ p ∈ groups, (family p).enncard
        = ∑ p ∈ groups, ∑ T ∈ family p, (1 : ENNReal) := by
          apply Finset.sum_congr rfl
          intro p _
          simp [Kakeya.TubeFamily.enncard]
      _ = ∑ p ∈ groups, ∑ T ∈ F, if T ∈ family p then (1 : ENNReal) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          have h2 : family p ⊆ F := h1 p hp
          rw [Finset.sum_ite]
          <;> simp [h2]
      _ = ∑ T ∈ F, ∑ p ∈ groups, if T ∈ family p then (1 : ENNReal) else 0 := by
          rw [Finset.sum_comm]
      _ = ∑ T ∈ F, ↑((groups.filter (fun p => T ∈ family p)).card) := by
          apply Finset.sum_congr rfl
          intro T _
          simp [Finset.filter]
  rw [h_double_count]
  calc
    ∑ T ∈ F, ↑((groups.filter (fun p => T ∈ family p)).card)
      ≤ ∑ T ∈ F, (7000 : ENNReal) := by
        apply Finset.sum_le_sum
        intro T hT
        exact_mod_cast h_main T hT
    _ = 7000 * F.enncard := by
        simp [Kakeya.TubeFamily.enncard, Finset.sum_const]
        <;> ring
    _ ≤ 1000000 * F.enncard := by
        gcongr
        <;> norm_num

end Kakeya.Assouad
