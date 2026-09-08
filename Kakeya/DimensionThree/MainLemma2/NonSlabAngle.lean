/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.Thickness.Diam
public import Kakeya.Thickness.HasThicknesses
public import Kakeya.Thickness.OuterPrism
public import Kakeya.DimensionThree.MainLemma2.VeryNotSticky
public import Kakeya.DimensionThree.MainLemma2.AngularCover
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The angular machinery of the non-slab case of Main Lemma 2

This file collects the pieces of the non-slab case (blueprint subsection *The non-slab case*)
that are purely about *directions*: the admissible range of the angular scale
`ρ₂ = b / r₁` (blueprint `lem:ml2rho2range`), the axis `v(W)` attached to a factoring body
and the angle it controls (blueprint `def:ml2bodyAxis`, `def:ml2bodyAngleConstant`,
`lem:ml2bodyAngle`), the dilated scale `ρ₂*` (blueprint `def:ml2rho2star`) and the count of
the tubes through a point whose direction is close to a fixed line (blueprint
`lem:ml2angularInnerCount`).

Angles between tubes and bodies are unoriented: what matters is the *line* spanned by a
direction, not its orientation. We therefore work with `Kakeya.NonSlab.lineAngle`, the angle
on the projective space of unoriented directions, which is a genuine metric and hence obeys
the triangle inequality exactly — the property the counting argument of
`Kakeya.VeryNotSticky.angularInnerCount` rests on.
-/

@[expose] public section

namespace Kakeya.NonSlab

open Metric Set

section Angle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unoriented angle between the lines `ℝ u` and `ℝ v`: the smaller of the two angles
`∠(u, v)` and `∠(u, -v)`.

This is the angular quantity `angle(T, T₀)` of the blueprint, read on the projective space of
unoriented directions of `ℝ³`. On that space it is a metric, so it is symmetric and satisfies
the triangle inequality exactly (`Kakeya.NonSlab.lineAngle_le_add`); for unit vectors it
equals `arccos |⟪u, v⟫|`, and on the range of values used in the non-slab case — all of them
at most `1` — it is comparable to the transversality measure `|sin α|` of the blueprint's
`def:planarAngle`. -/
noncomputable def lineAngle (u v : E) : ℝ :=
  min (InnerProductGeometry.angle u v) (InnerProductGeometry.angle u (-v))

lemma lineAngle_nonneg (u v : E) : 0 ≤ lineAngle u v :=
  le_min (InnerProductGeometry.angle_nonneg u v) (InnerProductGeometry.angle_nonneg u (-v))

lemma lineAngle_comm (u v : E) : lineAngle u v = lineAngle v u := by
  simp [lineAngle, InnerProductGeometry.angle_neg_right, InnerProductGeometry.angle_comm u v]

lemma lineAngle_self {u : E} (hu : u ≠ 0) : lineAngle u u = 0 := by
  rw [lineAngle, InnerProductGeometry.angle_self hu,
    InnerProductGeometry.angle_self_neg_of_nonzero hu]
  exact min_eq_left Real.pi_nonneg

/-- The unoriented angle is a metric on directions, hence satisfies the triangle inequality
exactly. This is the only property of `lineAngle` used by
`Kakeya.VeryNotSticky.angularInnerCount`. -/
lemma lineAngle_le_add (u v w : E) : lineAngle u w ≤ lineAngle u v + lineAngle v w := by
  have h1 := InnerProductGeometry.angle_le_angle_add_angle u v w
  have h2 := InnerProductGeometry.angle_le_angle_add_angle u v (-w)
  have h3 := InnerProductGeometry.angle_le_angle_add_angle u (-v) (-w)
  have h4 := InnerProductGeometry.angle_le_angle_add_angle u (-v) w
  rw [InnerProductGeometry.angle_neg_neg] at h3
  rw [show InnerProductGeometry.angle (-v) w = InnerProductGeometry.angle v (-w) by
    rw [InnerProductGeometry.angle_neg_left, InnerProductGeometry.angle_neg_right]] at h4
  simp only [lineAngle, min_def]
  split_ifs <;> linarith

/-- `lineAngle` never exceeds a right angle: it is `min θ (π - θ)`. -/
private lemma lineAngle_le_pi_div_two (u v : E) : lineAngle u v ≤ Real.pi / 2 := by
  rw [lineAngle, InnerProductGeometry.angle_neg_right, min_le_iff]
  rcases le_total (InnerProductGeometry.angle u v) (Real.pi / 2) with h | h
  exacts [Or.inl h, Or.inr (by linarith)]

/-- **Pythagoras for the component orthogonal to a unit vector.** -/
private lemma norm_sub_inner_smul_sq_of_norm_one {e : E} (he : ‖e‖ = 1) (w : E) :
    ‖w - (inner ℝ w e : ℝ) • e‖ ^ 2 = ‖w‖ ^ 2 - (inner ℝ w e : ℝ) ^ 2 := by
  -- (extracted by Fuse golfer)
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, he, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- **Small orthogonal component forces a small line angle.**

For a unit vector `e` and a nonzero `w`, the angle between the lines `ℝ w` and `ℝ e` is
controlled by the size of the component of `w` orthogonal to `e`, relative to `‖w‖`. This is
the quantitative form of "`w` nearly parallel to `e`" used by
`Kakeya.NonSlab.lineAngle_bodyAxis_le`. -/
private lemma lineAngle_le_of_orthogonal_component {w e : E} (he : ‖e‖ = 1) (hw : w ≠ 0) :
    lineAngle w e ≤ Real.pi / 2 * (‖w - (inner ℝ w e : ℝ) • e‖ / ‖w‖) := by
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hsq : √(‖w‖ ^ 2 - inner ℝ w e * inner ℝ w e) = ‖w - (inner ℝ w e : ℝ) • e‖ := by
    rw [← pow_two, ← norm_sub_inner_smul_sq_of_norm_one he w]
    exact Real.sqrt_sq (norm_nonneg _)
  have h1 := InnerProductGeometry.sin_angle_mul_norm_mul_norm w e
  simp only [he, mul_one, real_inner_self_eq_norm_sq, one_pow] at h1
  rw [hsq] at h1
  have hlin : Real.sin (lineAngle w e) = Real.sin (InnerProductGeometry.angle w e) := by
    rw [lineAngle, InnerProductGeometry.angle_neg_right]
    rcases le_total (InnerProductGeometry.angle w e) (Real.pi - InnerProductGeometry.angle w e)
      with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.sin_pi_sub]
  rw [show ‖w - (inner ℝ w e : ℝ) • e‖ / ‖w‖ = Real.sin (lineAngle w e) by
    rw [hlin, div_eq_iff hwpos.ne']; exact h1.symm]
  calc lineAngle w e = Real.pi / 2 * (2 / Real.pi * lineAngle w e) := by
        field_simp
    _ ≤ Real.pi / 2 * Real.sin (lineAngle w e) :=
        mul_le_mul_of_nonneg_left
          (Real.mul_le_sin (lineAngle_nonneg w e) (lineAngle_le_pi_div_two w e)) (by positivity)

/-- **A long chord with a small orthogonal component is nearly parallel.**

The ratio form of `Kakeya.NonSlab.lineAngle_le_of_orthogonal_component`: if the chord `w` is
longer than `m` and its component orthogonal to the unit vector `e` is at most `K`, then the
angle between the lines `ℝ w` and `ℝ e` is at most `(π/2) · K/m`. Both steps of
`Kakeya.NonSlab.lineAngle_bodyAxis_le` are instances of this. -/
private lemma lineAngle_le_of_norm_orthogonal_le {w e : E} (he : ‖e‖ = 1) {K m : ℝ}
    (hm : 0 < m) (hmw : m < ‖w‖) (hK : ‖w - (inner ℝ w e : ℝ) • e‖ ≤ K) :
    lineAngle w e ≤ Real.pi / 2 * (K / m) := by
  -- (extracted by Fuse golfer)
  have hw : (0 : ℝ) < ‖w‖ := hm.trans hmw
  exact (lineAngle_le_of_orthogonal_component he (norm_pos_iff.mp hw)).trans
    (mul_le_mul_of_nonneg_left (div_le_div₀ ((norm_nonneg _).trans hK) hK hm hmw.le)
      Real.pi_div_two_pos.le)

/-- **Close unit directions make a small line angle.**

For unit vectors the line angle is at most `(π/2)` times the chordal distance.  Together with
`Kakeya.NonSlab.norm_sub_or_norm_add_le_of_lineAngle_le` this is the pair of bridges between
the metric of `S²`, in which the angular hierarchy of `Kakeya.AngularCover` is built, and the
projective angle of `Kakeya.VeryNotSticky.angularFibreWith`. -/
lemma lineAngle_le_pi_div_two_mul_norm_sub {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    lineAngle u w ≤ Real.pi / 2 * ‖u - w‖ := by
  have hune : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have h := lineAngle_le_of_orthogonal_component hw hune
  rw [hu, div_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  set c : ℝ := inner ℝ u w with hc
  have h1 : ‖u - c • w‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_inner_smul_sq_of_norm_one hw u, hu]; ring
  have h2 : ‖u - w‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hu, hw, ← hc]; ring
  nlinarith [norm_nonneg (u - c • w), norm_nonneg (u - w), sq_nonneg (1 - c)]

/-- **A small unoriented angle makes close unit directions.**  The chord is at most the arc. -/
lemma norm_sub_le_angle {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ‖u - w‖ ≤ InnerProductGeometry.angle u w := by
  set θ : ℝ := InnerProductGeometry.angle u w with hθ
  have hcos : Real.cos θ = inner ℝ u w := by
    rw [hθ, InnerProductGeometry.cos_angle, hu, hw]; ring
  have h2 : ‖u - w‖ ^ 2 = 2 - 2 * (inner ℝ u w : ℝ) := by
    rw [norm_sub_sq_real, hu, hw]; ring
  have hb := Real.one_sub_sq_div_two_le_cos (x := θ)
  have hθ0 : 0 ≤ θ := InnerProductGeometry.angle_nonneg u w
  nlinarith [norm_nonneg (u - w)]

/-- **A bound on the line angle puts the direction, or its antipode, in a metric ball of the
same radius.**  This is the hypothesis shape of
`Kakeya.AngularCover.card_le_of_ball_of_class_bound`: the projective ball of radius `ρ` around
a unit vector `w` is contained in the union of the two metric balls of radius `ρ` around `w`
and `-w`. -/
lemma norm_sub_or_norm_add_le_of_lineAngle_le {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {ρ : ℝ}
    (h : lineAngle u w ≤ ρ) : ‖u - w‖ ≤ ρ ∨ ‖u + w‖ ≤ ρ := by
  have hnw : ‖(-w : E)‖ = 1 := by rw [norm_neg]; exact hw
  rw [lineAngle, min_le_iff] at h
  rcases h with h | h
  · exact Or.inl ((norm_sub_le_angle hu hw).trans h)
  · refine Or.inr ?_
    have hstep := (norm_sub_le_angle hu hnw).trans h
    simpa [sub_neg_eq_add] using hstep

/-- **The cosine of the unoriented angle is the absolute inner product.**

For unit vectors, `cos (angle u v) = ⟪u, v⟫` and `angle u (-v) = π - angle u v`, so the
smaller of the two angles has cosine `|⟪u, v⟫|`. This is the bridge between
`Kakeya.NonSlab.lineAngle` and the algebra of inner products used by the packing argument of
`Kakeya.NonSlab.card_le_coneDirectionCount`. -/
private lemma cos_lineAngle_of_norm_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.cos (lineAngle u v) = |inner ℝ u v| := by
  have hcos : Real.cos (InnerProductGeometry.angle u v) = inner ℝ u v := by
    simpa [hu, hv] using (InnerProductGeometry.cos_angle u v)
  rw [lineAngle, InnerProductGeometry.angle_neg_right]
  rcases le_total (InnerProductGeometry.angle u v)
      (Real.pi - InnerProductGeometry.angle u v) with hle | hge
  · rw [min_eq_left hle]
    have hnonneg : 0 ≤ inner ℝ u v := by
      rw [← hcos]
      exact Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [InnerProductGeometry.angle_nonneg u v, Real.pi_nonneg], by linarith⟩
    rw [abs_of_nonneg hnonneg]
    exact hcos
  · rw [min_eq_right hge]
    have hnonpos : inner ℝ u v ≤ 0 := by
      rw [← hcos]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith)
        (by linarith [InnerProductGeometry.angle_le_pi u v, Real.pi_nonneg])
    rw [abs_of_nonpos hnonpos, Real.cos_pi_sub, hcos]

/-- **Angular separation forces chordal separation.**

For unit vectors `min ‖u - v‖ ‖u + v‖ = 2 sin (lineAngle u v / 2)`, and Jordan's inequality
turns a lower bound `σ` on the angle into the chordal lower bound `(2/π) σ ≥ (3/5) σ`. No
upper bound on `σ` is needed: `lineAngle` never exceeds `π/2`, so the hypothesis already
forces `σ ≤ π/2`. -/
private lemma le_min_norm_sub_norm_add {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσuv : σ ≤ lineAngle u v) :
    3 / 5 * σ ≤ min ‖u - v‖ ‖u + v‖ := by
  let i : ℝ := inner ℝ u v
  have hline_le : lineAngle u v ≤ Real.pi / 2 := lineAngle_le_pi_div_two u v
  have hσle : σ ≤ Real.pi / 2 := hσuv.trans hline_le
  -- ‖u - v‖² = 2 - 2 i and ‖u + v‖² = 2 + 2 i
  have hsub : ‖u - v‖ ^ 2 = 2 - 2 * i := by
    rw [norm_sub_sq_real, hu, hv]
    dsimp [i]
    ring
  have hadd : ‖u + v‖ ^ 2 = 2 + 2 * i := by
    rw [norm_add_sq_real, hu, hv]
    dsimp [i]
    ring
  -- (min ‖u - v‖ ‖u + v‖)² = min (‖u - v‖²) (‖u + v‖²)
  have hmin : (min ‖u - v‖ ‖u + v‖) ^ 2 = min (‖u - v‖ ^ 2) (‖u + v‖ ^ 2) := by
    rcases lt_or_ge (‖u - v‖) (‖u + v‖) with hab | hab
    · have hab' : ‖u - v‖ ^ 2 ≤ ‖u + v‖ ^ 2 := by
        simpa [pow_two] using mul_le_mul hab.le hab.le (norm_nonneg _) (norm_nonneg _)
      rw [min_eq_left hab.le, min_eq_left hab']
    · have hab' : ‖u + v‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
        simpa [pow_two] using mul_le_mul hab hab (norm_nonneg _) (norm_nonneg _)
      rw [min_eq_right hab, min_eq_right hab']
  -- min (2 - 2 i) (2 + 2 i) = 2 - 2 |i|
  have hmin2 : min (2 - 2 * i) (2 + 2 * i) = 2 - 2 * |i| := by
    dsimp [i]
    by_cases hi : 0 ≤ inner ℝ u v
    · rw [abs_of_nonneg hi, min_eq_left (by linarith)]
    · have hi' : inner ℝ u v ≤ 0 := le_of_not_ge hi
      rw [abs_of_nonpos hi', min_eq_right (by linarith)]
      ring
  -- |⟪u, v⟫| = cos (lineAngle u v) ≤ cos σ
  have hcos_main : |i| ≤ Real.cos σ := by
    dsimp [i]
    rw [← cos_lineAngle_of_norm_one hu hv]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hσ (by linarith [hline_le, Real.pi_pos.le]) hσuv
  -- (min ‖u - v‖ ‖u + v‖)² = 2 - 2|i| ≥ 2 - 2 cos σ = 4 sin²(σ/2)
  have hm_eq : (min ‖u - v‖ ‖u + v‖) ^ 2 = 2 - 2 * |i| := by
    rw [hmin, hsub, hadd, hmin2]
  have hcos_id : 2 - 2 * Real.cos σ = 4 * Real.sin (σ / 2) ^ 2 := by
    conv_lhs =>
      rw [show σ = 2 * (σ / 2) by ring]
    rw [Real.cos_two_mul_eq_one_sub]
    ring
  have hm_sin : 4 * Real.sin (σ / 2) ^ 2 ≤ (min ‖u - v‖ ‖u + v‖) ^ 2 := by
    rw [← hcos_id, hm_eq]
    linarith [hcos_main]
  -- Jordan: sin (σ/2) ≥ σ/π, hence 4 sin²(σ/2) ≥ (3/5 σ)²
  have hsin : σ / Real.pi ≤ Real.sin (σ / 2) := by
    have h01 : (0 : ℝ) ≤ σ / 2 := div_nonneg hσ (by norm_num)
    have hσπ : σ ≤ Real.pi := hσle.trans (half_le_self Real.pi_pos.le)
    have h02 : σ / 2 ≤ Real.pi / 2 := div_le_div_of_nonneg_right hσπ (by norm_num)
    have : (2 / Real.pi) * (σ / 2) ≤ Real.sin (σ / 2) := Real.mul_le_sin h01 h02
    rwa [show (2 / Real.pi) * (σ / 2) = σ / Real.pi by ring] at this
  have hquad : (3 / 5 * σ) ^ 2 ≤ 4 * Real.sin (σ / 2) ^ 2 := by
    have hs : 0 ≤ Real.sin (σ / 2) := by linarith [hsin, div_nonneg hσ Real.pi_pos.le]
    have hsinsq : (σ / Real.pi) ^ 2 ≤ Real.sin (σ / 2) ^ 2 := by
      simpa [pow_two] using
        mul_le_mul hsin hsin (div_nonneg hσ Real.pi_pos.le) hs
    -- (3/5)² ≤ 4/π² since π < 3.15, i.e. 3π ≤ 10
    have hcoef : (3 / 5) ^ 2 ≤ 4 / Real.pi ^ 2 := by
      have hp0 : (0 : ℝ) < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      rw [le_div_iff₀ hp0]
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hA : (3 / 5 * σ) ^ 2 ≤ 4 * (σ / Real.pi) ^ 2 := by
      rw [show (3 / 5 * σ) ^ 2 = (3 / 5) ^ 2 * σ ^ 2 by ring,
        show 4 * (σ / Real.pi) ^ 2 = 4 / Real.pi ^ 2 * σ ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg σ)
    exact hA.trans (mul_le_mul_of_nonneg_left hsinsq (by norm_num))
  have hSq : (3 / 5 * σ) ^ 2 ≤ (min ‖u - v‖ ‖u + v‖) ^ 2 := hquad.trans hm_sin
  exact le_of_sq_le_sq hSq (le_min (norm_nonneg _) (norm_nonneg _))

/-- **The tangent-plane projection is bi-Lipschitz on a cap.**

If two unit vectors both have inner product at least `k > 0` with the unit vector `v`, and
both have orthogonal component of norm at most `ρ`, then the projection
`x ↦ x - ⟪x, v⟫ v` shrinks their distance by a factor of at most `(k + ρ)/k`. This is the
only estimate behind the exponent-`2` packing of
`Kakeya.NonSlab.card_le_of_inner_lower_bound_of_separated`, and it is pure algebra: no
trigonometry, no dimension. -/
private lemma mul_norm_sub_le_norm_proj_sub {v : E} (hv : ‖v‖ = 1) {k ρ : ℝ}
    (hk : 0 < k) (hρ : 0 ≤ ρ) {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxk : k ≤ (inner ℝ x v : ℝ)) (hyk : k ≤ (inner ℝ y v : ℝ))
    (hxρ : ‖x - (inner ℝ x v : ℝ) • v‖ ≤ ρ) (hyρ : ‖y - (inner ℝ y v : ℝ) • v‖ ≤ ρ) :
    k * ‖x - y‖ ≤
      (k + ρ) * ‖(x - (inner ℝ x v : ℝ) • v) - (y - (inner ℝ y v : ℝ) • v)‖ := by
  let c : ℝ := inner ℝ x v
  let c' : ℝ := inner ℝ y v
  let P : E := x - c • v
  let P' : E := y - c' • v
  let X : ℝ := ‖P - P'‖
  let Y : ℝ := ‖x - y‖
  -- Step 1: P - P' = (x - y) - ⟪x - y, v⟫ v
  have hPP' : P - P' = (x - y) - (inner ℝ (x - y) v : ℝ) • v := by
    dsimp [P, P', c, c']
    rw [inner_sub_left, sub_smul]
    abel
  -- Step 2: Pythagoras for each of P, P', and their difference
  have hP2 : ‖P‖ ^ 2 = 1 - c ^ 2 := by
    dsimp [P, c]
    rw [norm_sub_inner_smul_sq_of_norm_one hv x, hx]
    ring
  have hP'2 : ‖P'‖ ^ 2 = 1 - c' ^ 2 := by
    dsimp [P', c']
    rw [norm_sub_inner_smul_sq_of_norm_one hv y, hy]
    ring
  have hX2 : X ^ 2 = Y ^ 2 - (c - c') ^ 2 := by
    dsimp [X, Y]
    rw [hPP']
    rw [norm_sub_inner_smul_sq_of_norm_one hv (x - y)]
    dsimp [c, c']
    rw [inner_sub_left]
  -- Step 3: the projected norms are X-close
  have h3 : |‖P'‖ - ‖P‖| ≤ X := by
    dsimp [X]
    simpa [abs_sub_comm] using abs_norm_sub_norm_le P P'
  have hPρ : ‖P‖ ≤ ρ := by
    dsimp [P, c]
    exact hxρ
  have hP'ρ : ‖P'‖ ≤ ρ := by
    dsimp [P', c']
    exact hyρ
  have hcc'ge : 2 * k ≤ c + c' := by
    dsimp [c, c']
    linarith
  -- Step 4: k * |c - c'| ≤ ρ * X, via the squared identity
  have h4sq : (k * (c - c')) ^ 2 ≤ (ρ * X) ^ 2 := by
    have hcc_eq : (c - c') * (c + c') = (‖P'‖ + ‖P‖) * (‖P'‖ - ‖P‖) := by
      nlinarith [hP2, hP'2]
    have hdiffsq : (‖P'‖ - ‖P‖) ^ 2 ≤ X ^ 2 :=
      sq_le_sq' (neg_le_of_abs_le h3) (le_of_abs_le h3)
    have hsumle : ‖P'‖ + ‖P‖ ≤ 2 * ρ := by linarith
    have hsumsq : (‖P'‖ + ‖P‖) ^ 2 ≤ (2 * ρ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hsumle 2
    have hcc'ge' : (2 * k) ^ 2 ≤ (c + c') ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hcc'ge 2
    nlinarith [hcc_eq, hdiffsq, hsumsq, hcc'ge']
  -- Step 5: square (k * Y)² ≤ ((k + ρ) * X)² and take square roots
  have hY2 : Y ^ 2 = X ^ 2 + (c - c') ^ 2 := by
    dsimp [X, Y]
    linarith [hX2]
  have hXnonneg : 0 ≤ X := norm_nonneg _
  have hkX : 0 ≤ k * X := mul_nonneg hk.le hXnonneg
  have hρX : 0 ≤ ρ * X := mul_nonneg hρ hXnonneg
  have hgoal_sq : (k * Y) ^ 2 ≤ ((k + ρ) * X) ^ 2 := by
    calc
      (k * Y) ^ 2 = (k * X) ^ 2 + (k * (c - c')) ^ 2 := by
        rw [show (k * Y) ^ 2 = (k ^ 2) * (Y ^ 2) by ring]
        rw [hY2]
        ring
      _ ≤ (k * X) ^ 2 + (ρ * X) ^ 2 := by
        nlinarith [h4sq]
      _ ≤ ((k + ρ) * X) ^ 2 := by
        nlinarith [mul_nonneg hkX hρX]
  exact le_of_sq_le_sq hgoal_sq (mul_nonneg (by linarith) hXnonneg)

/-- **Two-dimensional packing in the orthogonal complement of a direction.**

A `t`-separated set of vectors of `ℝ³` orthogonal to the unit vector `v` and of norm less
than `R` has at most `(1 + 2R/t)²` elements. The exponent is `2` rather than `3` because the
points lie in the plane `(ℝ ∙ v)ᗮ`; this is where the sharp exponent of
`Kakeya.NonSlab.card_le_coneDirectionCount` comes from. -/
private lemma card_le_of_separated_orthogonal
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) {t R : ℝ} (ht : 0 < t) (hR : 0 ≤ R)
    (N : Finset (EuclideanSpace ℝ (Fin 3)))
    (hmem : ∀ x ∈ N, (inner ℝ x v : ℝ) = 0)
    (hball : ∀ x ∈ N, ‖x‖ < R)
    (hsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → t ≤ ‖x - y‖) :
    (N.card : ℝ) ≤ (1 + 2 * R / t) ^ 2 := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let K : Submodule ℝ E := (Submodule.span ℝ {v})ᗮ
  have hKmem (x : E) : x ∈ K ↔ inner ℝ x v = 0 := by
    simpa [K] using (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℝ) (u := v) (v := x))
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hv
    norm_num at hv
  have hNsub : (N : Set E) ⊆ (K : Set E) := fun x hx => (hKmem x).mpr (hmem x hx)
  let S : Set K := {z | (z : E) ∈ (N : Set E)}
  have hsepS : ∀ y : K, y ∈ S → ∀ z : K, z ∈ S → y ≠ z → t ≤ dist y z := by
    intro y hy z hz hyz
    rw [dist_eq_norm, Submodule.coe_norm, Submodule.coe_sub]
    exact hsep (y : E) (by simpa [S] using hy) (z : E) (by simpa [S] using hz) (by
      intro h
      exact hyz (Subtype.ext h))
  have hballS : ∀ z ∈ S, z ∈ ball (0 : K) R := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, Submodule.coe_norm]
    exact hball (z : E) (by simpa [S] using hz)
  haveI : Fact (Module.finrank ℝ E = 2 + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]⟩
  have hK2 : Module.finrank ℝ K = 2 :=
    Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) hv0
  have hp := finite_and_card_le_of_separated (E := K) (r := t) (R := R)
    (hr := ht) (hR := hR) (x₀ := (0 : K)) (hsep := hsepS) (hN := hballS)
  have hcard_b : (S.ncard : ℝ) ≤ (1 + 2 * R / t) ^ 2 := by
    simpa [hK2] using hp.2
  have himg : ((Subtype.val : K → E) '' S) = (N : Set E) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [S] using hz
    · intro hx
      refine ⟨⟨x, hNsub hx⟩, ?_, rfl⟩
      simpa [S] using hx
  have hScard : S.ncard = N.card := by
    rw [← Set.ncard_coe_finset N, ← himg, ← Set.ncard_image_of_injective]
    exact Subtype.coe_injective
  calc
    (N.card : ℝ) = (S.ncard : ℝ) := by exact_mod_cast hScard.symm
    _ ≤ (1 + 2 * R / t) ^ 2 := hcard_b

/-- **Packing bound in a genuine cap.**

The one-sided form of `Kakeya.NonSlab.card_le_of_inner_lower_bound_of_separated`: here the
inner product with `v` is bounded below without an absolute value, so no sign normalisation is
needed and the projection `w ↦ w - ⟪w, v⟫ v` is injective on `D` by
`Kakeya.NonSlab.mul_norm_sub_le_norm_proj_sub`. -/
private lemma card_le_of_inner_ge_of_separated
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) {k ρ s : ℝ}
    (hk : 0 < k) (hρ : 0 ≤ ρ) (hs : 0 < s)
    (D : Finset (EuclideanSpace ℝ (Fin 3))) (hunit : ∀ w ∈ D, ‖w‖ = 1)
    (hinner : ∀ w ∈ D, k ≤ (inner ℝ w v : ℝ))
    (hperp : ∀ w ∈ D, 1 - (inner ℝ w v : ℝ) ^ 2 ≤ ρ ^ 2)
    (hsep : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → s ≤ ‖w - w'‖) :
    (D.card : ℝ) ≤ (2 + 2 * ρ * (k + ρ) / (k * s)) ^ 2 := by
  classical
  let P : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun w => w - (inner ℝ w v : ℝ) • v
  let t : ℝ := k * s / (k + ρ)
  have hkρ : 0 < k + ρ := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (mul_pos hk hs) hkρ
  have hPnorm : ∀ w ∈ D, ‖P w‖ ≤ ρ := by
    intro w hw
    have hsq : ‖P w‖ ^ 2 ≤ ρ ^ 2 := by
      dsimp [P]
      rw [norm_sub_inner_smul_sq_of_norm_one hv w]
      rw [show ‖w‖ ^ 2 = 1 by rw [hunit w hw]; norm_num]
      exact hperp w hw
    exact le_of_sq_le_sq hsq hρ
  have hPmem : ∀ w : EuclideanSpace ℝ (Fin 3), (inner ℝ (P w) v : ℝ) = 0 := by
    intro w
    dsimp [P]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hv]
    ring
  have hPsep : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → t ≤ ‖P w - P w'‖ := by
    intro w hw w' hw' hne
    have hlem := mul_norm_sub_le_norm_proj_sub (v := v) hv (k := k) hk (ρ := ρ) hρ
      (x := w) (y := w') (hunit w hw) (hunit w' hw') (hinner w hw) (hinner w' hw')
      (hPnorm w hw) (hPnorm w' hw')
    have hk' : k * s ≤ (k + ρ) * ‖P w - P w'‖ := by
      calc
        k * s ≤ k * ‖w - w'‖ := mul_le_mul_of_nonneg_left (hsep w hw w' hw' hne) hk.le
        _ ≤ (k + ρ) * ‖P w - P w'‖ := by
          simpa [P] using hlem
    dsimp [t]
    rw [div_le_iff₀ hkρ]
    nlinarith [hk']
  have hP_inj : Set.InjOn P (D : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro w hw w' hw' hPP
    by_contra hne
    have : t ≤ (0 : ℝ) := by
      have hsep0 := hPsep w hw w' hw' hne
      rw [hPP] at hsep0
      simpa using hsep0
    linarith
  have hcard : (D.image P).card = D.card := Finset.card_image_of_injOn hP_inj
  have hmem_image : ∀ x ∈ D.image P, (inner ℝ x v : ℝ) = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hwD, rfl⟩
    exact hPmem w
  have hball_image : ∀ x ∈ D.image P, ‖x‖ < ρ + t / 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hwD, rfl⟩
    exact lt_of_le_of_lt (hPnorm w hwD) (by linarith [ht])
  have hsep_image : ∀ x ∈ D.image P, ∀ y ∈ D.image P, x ≠ y → t ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨w, hwD, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨w', hw'D, rfl⟩
    have hne : w ≠ w' := by
      intro h
      apply hxy
      rw [h]
    exact hPsep w hwD w' hw'D hne
  have hpack : ((D.image P).card : ℝ) ≤ (1 + 2 * (ρ + t / 2) / t) ^ 2 :=
    card_le_of_separated_orthogonal (v := v) hv (t := t) ht
      (R := ρ + t / 2) (by linarith [hρ, ht]) (D.image P) hmem_image hball_image hsep_image
  have hRHS : (1 + 2 * (ρ + t / 2) / t) ^ 2 = (2 + 2 * ρ * (k + ρ) / (k * s)) ^ 2 := by
    have hlin : 1 + 2 * (ρ + t / 2) / t = 2 + 2 * ρ * (k + ρ) / (k * s) := by
      dsimp [t]
      field_simp [hk.ne', hs.ne', hkρ.ne']
      ring
    rw [hlin]
  calc
    (D.card : ℝ) = ((D.image P).card : ℝ) := by exact_mod_cast hcard.symm
    _ ≤ (1 + 2 * (ρ + t / 2) / t) ^ 2 := hpack
    _ = (2 + 2 * ρ * (k + ρ) / (k * s)) ^ 2 := hRHS

/-- **Packing bound for unit vectors with a bounded orthogonal component.**

The two-dimensional packing step behind `Kakeya.NonSlab.card_le_coneDirectionCount`, stated
with no trigonometry: `k` is a lower bound for `|⟪w, v⟫|`, so all points of `D` lie, up to
sign, in the cap around `v` on which the orthogonal projection `w ↦ w - ⟪w, v⟫ v` is
bi-Lipschitz; `ρ` bounds the projected radius, and `s` the chordal separation. Since the
projection lands in the two-dimensional space `(ℝ ∙ v)ᗮ`, the exponent is `2` — the sharp
exponent, which no ambient three-dimensional packing bound can give. -/
private lemma card_le_of_inner_lower_bound_of_separated
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) {k ρ s : ℝ}
    (hk : 0 < k) (hρ : 0 ≤ ρ) (hs : 0 < s)
    (D : Finset (EuclideanSpace ℝ (Fin 3))) (hunit : ∀ w ∈ D, ‖w‖ = 1)
    (hinner : ∀ w ∈ D, k ≤ |inner ℝ w v|)
    (hperp : ∀ w ∈ D, 1 - (inner ℝ w v : ℝ) ^ 2 ≤ ρ ^ 2)
    (hsep : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → s ≤ min ‖w - w'‖ ‖w + w'‖) :
    (D.card : ℝ) ≤ (2 + 2 * ρ * (k + ρ) / (k * s)) ^ 2 := by
  classical
  -- Normalise signs: rotate each `w` into the positive hemisphere so that `⟪e w, v⟫ ≥ 0`.
  let e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun w => if 0 ≤ (inner ℝ w v : ℝ) then w else -w
  let D' : Finset (EuclideanSpace ℝ (Fin 3)) := D.image e
  have he_norm : ∀ w : EuclideanSpace ℝ (Fin 3), ‖e w‖ = ‖w‖ := by
    intro w
    dsimp [e]
    split_ifs with h
    · rfl
    · exact norm_neg w
  have he_inner : ∀ w : EuclideanSpace ℝ (Fin 3),
      (inner ℝ (e w) v : ℝ) = |inner ℝ w v| := by
    intro w
    dsimp [e]
    split_ifs with h
    · exact (abs_of_nonneg h).symm
    · rw [inner_neg_left]
      exact (abs_of_nonpos (le_of_not_ge h)).symm
  have he_sq : ∀ w : EuclideanSpace ℝ (Fin 3),
      (inner ℝ (e w) v : ℝ) ^ 2 = (inner ℝ w v : ℝ) ^ 2 := by
    intro w
    rw [he_inner w, sq_abs]
  -- The antipodal difference `e w - e w'` is up to sign one of `w - w'`, `w + w'`.
  have hsep_pre : ∀ w w' : EuclideanSpace ℝ (Fin 3),
      s ≤ min ‖w - w'‖ ‖w + w'‖ → s ≤ ‖e w - e w'‖ := by
    intro w w' hh
    dsimp [e]
    by_cases hw0 : 0 ≤ (inner ℝ w v : ℝ)
    · by_cases hw'0 : 0 ≤ (inner ℝ w' v : ℝ)
      · rw [if_pos hw0, if_pos hw'0]
        exact hh.trans (min_le_left ‖w - w'‖ ‖w + w'‖)
      · rw [if_pos hw0, if_neg hw'0]
        rw [sub_neg_eq_add]
        exact hh.trans (min_le_right ‖w - w'‖ ‖w + w'‖)
    · by_cases hw'0 : 0 ≤ (inner ℝ w' v : ℝ)
      · rw [if_neg hw0, if_pos hw'0]
        rw [show -w - w' = -(w + w') by abel, norm_neg]
        exact hh.trans (min_le_right ‖w - w'‖ ‖w + w'‖)
      · rw [if_neg hw0, if_neg hw'0]
        rw [show -w - -w' = -(w - w') by abel, norm_neg]
        exact hh.trans (min_le_left ‖w - w'‖ ‖w + w'‖)
  have hinj : ∀ w ∈ D, ∀ w' ∈ D, e w = e w' → w = w' := by
    intro w hw w' hw' hh
    by_contra hne
    have hse : s ≤ ‖e w - e w'‖ := hsep_pre w w' (hsep w hw w' hw' hne)
    rw [hh, sub_self, norm_zero] at hse
    linarith
  have hcard : D'.card = D.card := by
    dsimp [D']
    exact Finset.card_image_of_injOn (fun w hw w' hw' hh => hinj w hw w' hw' hh)
  have hunit' : ∀ x ∈ D', ‖x‖ = 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    rw [he_norm w]
    exact hunit w hw
  have hinner' : ∀ x ∈ D', k ≤ (inner ℝ x v : ℝ) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    rw [he_inner w]
    exact hinner w hw
  have hperp' : ∀ x ∈ D', 1 - (inner ℝ x v : ℝ) ^ 2 ≤ ρ ^ 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    rw [he_sq w]
    exact hperp w hw
  have hsep' : ∀ x ∈ D', ∀ x' ∈ D', x ≠ x' → s ≤ ‖x - x'‖ := by
    intro x hx x' hx' hne
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.mp hx' with ⟨w', hw', rfl⟩
    have hwne : w ≠ w' := by
      intro hw
      exact hne (by rw [hw])
    exact hsep_pre w w' (hsep w hw w' hw' hwne)
  have hpack := card_le_of_inner_ge_of_separated (v := v) hv (k := k) hk (ρ := ρ) hρ
    (s := s) hs D' hunit' hinner' hperp' hsep'
  calc
    (D.card : ℝ) = (D'.card : ℝ) := by rw [hcard]
    _ ≤ (2 + 2 * ρ * (k + ρ) / (k * s)) ^ 2 := hpack

/-- **Constant in Lemma `Kakeya.NonSlab.card_le_coneDirectionCount`** (blueprint
`def:coneDirectionCountConstant`, `C_{lem:coneDirectionCount}`).

An absolute constant `C ≥ 1` such that a set of directions of `ℝ³` contained in a cone of
aperture `α` about a fixed direction and pairwise separated by `σ ≤ α` has at most
`C (α/σ)²` elements. It is absolute: it depends on nothing — not on `α`, not on `σ`, not on
`δ`. The ambient dimension is `3` throughout, so it is not a parameter either, and the
exponent `2` in `card_le_coneDirectionCount` is `dim S² = 2`.

The displayed value is provisional and generous. The packing argument compares spherical
areas: the caps of angular radius `σ/2` about the points of the set are pairwise disjoint and
sit inside the cap of angular radius `3α/2`, and `1 - cos r ≥ 2r²/π²` on `[0, π]` turns the
area comparison into `# ≤ (9π²/4)(α/σ)²`, so any constant at least `9π²/4 ≈ 22.2` works. -/
def coneDirectionCountConstant : NNReal := 2 ^ 10

lemma one_le_coneDirectionCountConstant : 1 ≤ coneDirectionCountConstant := by
  unfold coneDirectionCountConstant; norm_num

/-- **The narrow-cone half of `Kakeya.NonSlab.card_le_coneDirectionCount`.**

For an aperture `α ≤ 7/10` the projection to the tangent plane at `v₀` is bi-Lipschitz with
constant `4/3`, and the packing bound in that plane gives the count with room to spare: the
constant coming out of `Kakeya.NonSlab.card_le_of_inner_lower_bound_of_separated` is
`(76/9)² ≈ 71`, well inside `2^10`. -/
private lemma card_le_cone_of_le {σ α : ℝ} (hσ : 0 < σ) (hσα : σ ≤ α) (hα : α ≤ 7 / 10)
    {v₀ : EuclideanSpace ℝ (Fin 3)} (hv₀ : ‖v₀‖ = 1)
    (D : Finset (EuclideanSpace ℝ (Fin 3))) (hunit : ∀ w ∈ D, ‖w‖ = 1)
    (hcap : ∀ w ∈ D, lineAngle w v₀ ≤ α)
    (hsep : (D : Set (EuclideanSpace ℝ (Fin 3))).Pairwise fun w w' ↦ σ ≤ lineAngle w w') :
    (D.card : ℝ) ≤ 1024 * (α / σ) ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := le_trans hσ.le hσα
  have hαpi : α ≤ Real.pi := by linarith [Real.pi_gt_three]
  -- `|⟪w, v₀⟫| = cos (lineAngle w v₀) ≥ cos α`: the bridge of the packing lemma.
  have hcos : ∀ w ∈ D, Real.cos α ≤ |inner ℝ w v₀| := by
    intro w hw
    calc
      Real.cos α ≤ Real.cos (lineAngle w v₀) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (lineAngle_nonneg w v₀) hαpi (hcap w hw)
      _ = |inner ℝ w v₀| := cos_lineAngle_of_norm_one (hunit w hw) hv₀
  -- lower bound on `cos α` from `1 - x²/2 ≤ cos x` at `x = α ≤ 7/10`.
  have hcos34 : (3 : ℝ) / 4 ≤ Real.cos α := by
    have hlb := Real.one_sub_sq_div_two_le_cos (x := α)
    have hα2 : α ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by nlinarith [hα0, hα]
    nlinarith [hlb, hα2]
  have hinner : ∀ w ∈ D, (3 / 4 : ℝ) ≤ |inner ℝ w v₀| := fun w hw => hcos34.trans (hcos w hw)
  -- `1 - ⟪w,v₀⟫² ≤ α²`: `⟪w,v₀⟫² = cos²(lineAngle) ≥ cos² α` and `1 - cos²α = sin² ≤ α²`.
  have hperp : ∀ w ∈ D, 1 - (inner ℝ w v₀ : ℝ) ^ 2 ≤ α ^ 2 := by
    intro w hw
    have hcosα0 : (0 : ℝ) ≤ Real.cos α := le_trans (by norm_num : (0 : ℝ) ≤ 3 / 4) hcos34
    have hcosα2le : (Real.cos α) ^ 2 ≤ (inner ℝ w v₀ : ℝ) ^ 2 := by
      calc
        (Real.cos α) ^ 2 ≤ |inner ℝ w v₀| ^ 2 :=
          pow_le_pow_left₀ hcosα0 (hcos w hw) 2
        _ = (inner ℝ w v₀ : ℝ) ^ 2 := by rw [sq_abs]
    have h1 : 1 - (Real.cos α) ^ 2 = (Real.sin α) ^ 2 := by
      rw [← Real.sin_sq_add_cos_sq (x := α)]
      ring
    have hsin2 : (Real.sin α) ^ 2 ≤ α ^ 2 :=
      pow_le_pow_left₀ (Real.sin_nonneg_of_nonneg_of_le_pi hα0 hαpi) (Real.sin_le hα0) 2
    calc
      1 - (inner ℝ w v₀ : ℝ) ^ 2 ≤ 1 - (Real.cos α) ^ 2 := by linarith [hcosα2le]
      _ = (Real.sin α) ^ 2 := h1
      _ ≤ α ^ 2 := hsin2
  -- turn the angular separation into chordal separation.
  have hchord : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → 3 / 5 * σ ≤ min ‖w - w'‖ ‖w + w'‖ := by
    intro w hw w' hw' hne
    exact le_min_norm_sub_norm_add (hunit w hw) (hunit w' hw') hσ.le (hsep hw hw' hne)
  -- apply the two-dimensional packing bound of the tangent plane.
  have hpack := card_le_of_inner_lower_bound_of_separated (v := v₀) hv₀ (k := 3 / 4) (by norm_num)
    (ρ := α) hα0 (s := 3 / 5 * σ) (by positivity) D hunit hinner hperp hchord
  -- numeric finish with `q := α / σ ≥ 1`.
  let q : ℝ := α / σ
  have hq1 : (1 : ℝ) ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ hσ]
    simpa using hσα
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hα_eq : α = q * σ := by
    dsimp [q]
    exact (div_mul_cancel₀ α hσ.ne').symm
  have hfrac : 2 * α * (3 / 4 + α) / ((3 / 4) * (3 / 5 * σ)) = (40 / 9) * q * (3 / 4 + α) := by
    rw [hα_eq]
    field_simp [hσ.ne']
    ring
  have h34a : (3 / 4 + α : ℝ) ≤ 29 / 20 := by linarith [hα]
  have hfrac2 : (40 / 9) * q * (3 / 4 + α) ≤ (58 / 9) * q := by
    nlinarith [h34a, hq0]
  have h2 : (2 : ℝ) ≤ 2 * q := by nlinarith [hq1]
  have hbbound : (2 + 2 * α * (3 / 4 + α) / ((3 / 4) * (3 / 5 * σ))) ≤ (76 / 9) * q := by
    rw [hfrac]
    nlinarith [h2, hfrac2]
  have hbnn : (0 : ℝ) ≤ 2 + 2 * α * (3 / 4 + α) / ((3 / 4) * (3 / 5 * σ)) := by positivity
  have hbbound_sq : (2 + 2 * α * (3 / 4 + α) / ((3 / 4) * (3 / 5 * σ))) ^ 2 ≤
      (5776 / 81) * q ^ 2 := by
    calc
      (2 + 2 * α * (3 / 4 + α) / ((3 / 4) * (3 / 5 * σ))) ^ 2 ≤ ((76 / 9) * q) ^ 2 :=
        pow_le_pow_left₀ hbnn hbbound 2
      _ = (5776 / 81) * q ^ 2 := by ring
  have hcoef : (5776 / 81 : ℝ) ≤ 1024 := by norm_num
  have hfinal : (5776 / 81) * q ^ 2 ≤ 1024 * (α / σ) ^ 2 := by
    dsimp [q]
    have hq2 : (0 : ℝ) ≤ (α / σ) ^ 2 := sq_nonneg (α / σ)
    nlinarith [hcoef, hq2]
  calc
    (D.card : ℝ) ≤ (2 + 2 * α * (3 / 4 + α) / ((3 / 4) * (3 / 5 * σ))) ^ 2 := hpack
    _ ≤ (5776 / 81) * q ^ 2 := hbbound_sq
    _ ≤ 1024 * (α / σ) ^ 2 := hfinal

/-- **Some coordinate of a unit vector of `ℝ³` carries a third of the mass.** -/
private lemma exists_coord_sq_ge {w : EuclideanSpace ℝ (Fin 3)} (hw : ‖w‖ = 1) :
    ∃ i : Fin 3, 1 / 3 ≤ (inner ℝ w (EuclideanSpace.single i (1 : ℝ)) : ℝ) ^ 2 := by
  have hinner : ∀ i : Fin 3, (inner ℝ w (EuclideanSpace.single i (1 : ℝ)) : ℝ) = w i := by
    intro i
    rw [EuclideanSpace.inner_single_right]
    simp
  have hsum : (∑ i : Fin 3, (w i) ^ 2) = 1 := by
    have hnorm : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
    calc
      (∑ i : Fin 3, (w i) ^ 2) = ∑ i : Fin 3, ‖w i‖ ^ 2 := by
        simp [Real.norm_eq_abs]
      _ = ‖w‖ ^ 2 := by rw [← EuclideanSpace.norm_sq_eq w]
      _ = 1 := hnorm
  by_contra hnot
  push Not at hnot
  have hlt' : ∀ i : Fin 3, (w i) ^ 2 < 1 / 3 := by
    intro i
    simpa [hinner i] using hnot i
  have hsumlt : (∑ i : Fin 3, (w i) ^ 2) < 1 := by
    have hstep : (∑ i : Fin 3, (w i) ^ 2) < ∑ i : Fin 3, (1 / 3 : ℝ) :=
      Finset.sum_lt_sum (fun i hi => le_of_lt (hlt' i)) ⟨0, by simp, hlt' 0⟩
    have h1 : (∑ i : Fin 3, (1 / 3 : ℝ)) = 1 := by
      rw [Fin.sum_univ_three]
      norm_num
    linarith
  linarith

/-- **The count around one coordinate axis.**

The wide-cone case is covered by the three groups on which one coordinate dominates. On each
of them `Kakeya.NonSlab.card_le_of_inner_lower_bound_of_separated` applies with `k = 1/2` and
`ρ = 5/6`, and `σ ≤ π/2` turns the resulting bound into the displayed `112/σ²`. -/
private lemma card_le_of_sq_inner_ge {σ : ℝ} (hσ : 0 < σ) (hσπ : σ ≤ Real.pi / 2)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    (D : Finset (EuclideanSpace ℝ (Fin 3))) (hunit : ∀ w ∈ D, ‖w‖ = 1)
    (hcoord : ∀ w ∈ D, 1 / 3 ≤ (inner ℝ w v : ℝ) ^ 2)
    (hsep : (D : Set (EuclideanSpace ℝ (Fin 3))).Pairwise fun w w' ↦ σ ≤ lineAngle w w') :
    (D.card : ℝ) ≤ 112 / σ ^ 2 := by
  have hk : (0 : ℝ) < 1 / 2 := by norm_num
  have hρ : (0 : ℝ) ≤ 5 / 6 := by norm_num
  have hs : (0 : ℝ) < 3 / 5 * σ := by positivity
  have hinner : ∀ w ∈ D, (1 / 2 : ℝ) ≤ |inner ℝ w v| := by
    intro w hw
    have h12sq : (1 / 2 : ℝ) ^ 2 ≤ |inner ℝ w v| ^ 2 := by
      rw [sq_abs]
      nlinarith [hcoord w hw]
    exact le_of_sq_le_sq h12sq (abs_nonneg _)
  have hperp : ∀ w ∈ D, 1 - (inner ℝ w v : ℝ) ^ 2 ≤ (5 / 6) ^ 2 := by
    intro w hw
    nlinarith [hcoord w hw]
  have hsep' : ∀ w ∈ D, ∀ w' ∈ D, w ≠ w' → 3 / 5 * σ ≤ min ‖w - w'‖ ‖w + w'‖ := by
    intro w hw w' hw' hne
    exact le_min_norm_sub_norm_add (hunit w hw) (hunit w' hw') hσ.le (hsep hw hw' hne)
  have hpack := card_le_of_inner_lower_bound_of_separated (v := v) hv (k := 1 / 2) hk
    (ρ := 5 / 6) hρ (s := 3 / 5 * σ) hs D hunit hinner hperp hsep'
  have hC_simplify :
      (2 + 2 * (5 / 6) * (1 / 2 + 5 / 6) / ((1 / 2) * (3 / 5 * σ))) = 2 + 200 / (27 * σ) := by
    field_simp [hσ.ne']
    ring
  have h1 : 2 + 200 / (27 * σ) ≤ (63 / 20 + 200 / 27) / σ := by
    have h200 : (200 / 27) / σ = 200 / (27 * σ) := by field_simp [hσ.ne']
    rw [← h200]
    rw [show (63 / 20 + 200 / 27) / σ = (63 / 20) / σ + (200 / 27) / σ by ring]
    have h2le : (2 : ℝ) ≤ (63 / 20) / σ := by
      rw [le_div_iff₀ hσ]
      have hπ : Real.pi ≤ 63 / 20 := by
        rw [show (63 / 20 : ℝ) = 3.15 by norm_num]
        exact le_of_lt Real.pi_lt_d2
      linarith [hσπ, hπ]
    nlinarith [h2le]
  have h2 : ((63 / 20 + 200 / 27) / σ) ^ 2 ≤ 112 / σ ^ 2 := by
    have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
    rw [le_div_iff₀ hσ2]
    field_simp [hσ.ne']
    norm_num
  have hfinal : (2 + 200 / (27 * σ)) ^ 2 ≤ 112 / σ ^ 2 := by
    calc
      (2 + 200 / (27 * σ)) ^ 2 ≤ ((63 / 20 + 200 / 27) / σ) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) h1 2
      _ ≤ 112 / σ ^ 2 := h2
  calc
    (D.card : ℝ) ≤ (2 + 2 * (5 / 6) * (1 / 2 + 5 / 6) / ((1 / 2) * (3 / 5 * σ))) ^ 2 := hpack
    _ = (2 + 200 / (27 * σ)) ^ 2 := by rw [hC_simplify]
    _ ≤ 112 / σ ^ 2 := hfinal

/-- **The wide-cone half of `Kakeya.NonSlab.card_le_coneDirectionCount`.**

For an aperture `α ≥ 7/10` the cap hypothesis is discarded: a `σ`-separated set of unit
vectors is split into the three groups on which one coordinate dominates, and each group is
counted by `Kakeya.NonSlab.card_le_of_inner_lower_bound_of_separated` about the corresponding
coordinate axis. The resulting `≈ 334/σ²` is below `1024 (α/σ)² ≥ 501/σ²`. -/
private lemma card_le_cone_of_ge {σ α : ℝ} (hσ : 0 < σ) (hσα : σ ≤ α) (hα : 7 / 10 ≤ α)
    (D : Finset (EuclideanSpace ℝ (Fin 3))) (hunit : ∀ w ∈ D, ‖w‖ = 1)
    (hsep : (D : Set (EuclideanSpace ℝ (Fin 3))).Pairwise fun w w' ↦ σ ≤ lineAngle w w') :
    (D.card : ℝ) ≤ 1024 * (α / σ) ^ 2 := by
  classical
  have hq1 : (1 : ℝ) ≤ α / σ := (one_le_div hσ).2 hσα
  rcases le_or_gt D.card 1 with hc | hc
  · -- trivial branch
    have h1 : (D.card : ℝ) ≤ 1 := by exact_mod_cast hc
    nlinarith [hq1, sq_nonneg (α / σ)]
  · -- main branch: σ ≤ π/2 because two distinct separated directions exist
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    have hσπ : σ ≤ Real.pi / 2 :=
      le_trans (hsep (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab)
        (lineAngle_le_pi_div_two a b)
    set Di : Fin 3 → Finset (EuclideanSpace ℝ (Fin 3)) := fun i =>
      D.filter (fun w => 1 / 3 ≤ (inner ℝ w (EuclideanSpace.single i (1 : ℝ)) : ℝ) ^ 2) with hDi
    have hcover : D ⊆ Di 0 ∪ (Di 1 ∪ Di 2) := by
      intro w hw
      obtain ⟨i, hi⟩ := exists_coord_sq_ge (hunit w hw)
      have hwDi : w ∈ Di i := by
        simpa [Finset.mem_filter, hDi, hw] using hi
      fin_cases i
      · simpa [Finset.mem_union] using Or.inl hwDi
      · simpa [Finset.mem_union] using Or.inr (Or.inl hwDi)
      · simpa [Finset.mem_union] using Or.inr (Or.inr hwDi)
    have hcard : D.card ≤ (Di 0).card + ((Di 1).card + (Di 2).card) :=
      le_trans (Finset.card_le_card hcover)
        (le_trans (Finset.card_union_le _ _) (by
          exact Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hone : ∀ i : Fin 3, ((Di i).card : ℝ) ≤ 112 / σ ^ 2 := by
      intro i
      refine card_le_of_sq_inner_ge hσ hσπ (by simp) (Di i)
        (fun w hw => hunit w (Finset.mem_of_mem_filter _ hw))
        (fun w hw => (Finset.mem_filter.mp hw).2)
        (hsep.mono (by exact_mod_cast Finset.filter_subset _ D))
    -- combine
    have hsum : (D.card : ℝ) ≤ 3 * (112 / σ ^ 2) := by
      have := hone 0; have := hone 1; have := hone 2
      have hcast : (D.card : ℝ) ≤ (Di 0).card + ((Di 1).card + (Di 2).card) := by
        exact_mod_cast hcard
      linarith
    have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
    have hgoal : 3 * (112 / σ ^ 2) ≤ 1024 * (α / σ) ^ 2 := by
      rw [div_pow]
      rw [show (3 : ℝ) * (112 / σ ^ 2) = 336 / σ ^ 2 by ring,
        show (1024 : ℝ) * (α ^ 2 / σ ^ 2) = 1024 * α ^ 2 / σ ^ 2 by ring]
      gcongr
      nlinarith [hα]
    linarith

/-- **Separated directions in a cone are few** (blueprint `lem:coneDirectionCount`).

Let `D` be a set of unit vectors of `EuclideanSpace ℝ (Fin 3)`, all within angle `α` of a
fixed unit vector `v₀` and pairwise separated by at least `σ`, with `0 < σ ≤ α`. Then
`#D ≤ C_{lem:coneDirectionCount} (α/σ)²`.

The blueprint's upper bound `α ≤ π` is not a binder: `Kakeya.NonSlab.lineAngle` never exceeds
`π/2`, so for `α > π/2` the cap hypothesis is already vacuous while the right-hand side only
grows. Dropping it is not cosmetic: the one consumer applies the lemma at
`α = 2 Ctyp δ^{-τ'} a/b`, and nothing in this development bounds that quantity.

The angular quantity is `Kakeya.NonSlab.lineAngle`, the metric on *unoriented* directions,
and not the angle on the sphere: the one consumer,
`Kakeya.VeryNotSticky.tangentialSlabFibreCount`, counts the *normals*
`Kakeya.NonSlab.bodyNormal` of slabs, which are defined only up to sign. The packing bound is
the same up to the absolute constant, `lineAngle` being the quotient metric of the angle on
`S²` under the antipodal identification.

`D` is a `Finset`, so finiteness is carried by the type rather than by a hypothesis and the
conclusion can speak of `D.card`; at the call site it comes from the finiteness clause of
`Kakeya.VeryNotSticky.IsSlabFamily`. -/
theorem card_le_coneDirectionCount {σ α : ℝ}
    (hσ : 0 < σ) (hσα : σ ≤ α)
    {v₀ : EuclideanSpace ℝ (Fin 3)} (hv₀ : ‖v₀‖ = 1)
    (D : Finset (EuclideanSpace ℝ (Fin 3))) (hunit : ∀ w ∈ D, ‖w‖ = 1)
    (hcap : ∀ w ∈ D, lineAngle w v₀ ≤ α)
    (hsep : (D : Set (EuclideanSpace ℝ (Fin 3))).Pairwise fun w w' ↦ σ ≤ lineAngle w w') :
    (D.card : ℝ) ≤ (coneDirectionCountConstant : ℝ) * (α / σ) ^ 2 := by
  rcases le_total α (7 / 10) with h | h
  · calc
      (D.card : ℝ) ≤ 1024 * (α / σ) ^ 2 := card_le_cone_of_le hσ hσα h hv₀ D hunit hcap hsep
      _ = (coneDirectionCountConstant : ℝ) * (α / σ) ^ 2 := by
          norm_num [coneDirectionCountConstant, NNReal.coe_pow]
  · calc
      (D.card : ℝ) ≤ 1024 * (α / σ) ^ 2 := card_le_cone_of_ge hσ hσα h D hunit hsep
      _ = (coneDirectionCountConstant : ℝ) * (α / σ) ^ 2 := by
          norm_num [coneDirectionCountConstant, NNReal.coe_pow]

end Angle

section Axis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **A set of large rank-zero thickness has a long chord.**

Below its rank-zero affine thickness — a fortiori below its diameter, by
`Metric.thickness_zero_le_diam` — every bound is realised by an actual pair of points. This
supplies the long chord of the tube segment used by
`Kakeya.NonSlab.lineAngle_bodyAxis_le`.

This statement is about `Metric.thickness` alone and would sit more naturally next to
`Metric.thickness_zero_le_diam` in `Kakeya/Thickness/Diam.lean`; it is kept `private` here to
avoid editing another section's file. -/
private lemma exists_dist_gt_of_lt_thickness_zero {s : Set E} (hs : Bornology.IsBounded s)
    {C : ℝ} (hC : 0 ≤ C) (h : C < Metric.thickness ℝ s 0) :
    ∃ x ∈ s, ∃ y ∈ s, C < dist x y := by
  by_contra hcon
  push Not at hcon
  have := (Metric.thickness_zero_le_diam (𝕜 := ℝ) hs).trans
    (Metric.diam_le_of_forall_dist_le hC hcon)
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The orthogonal complement of one axis of an orthonormal basis, in coordinates.**

In three dimensions, the component of `w` orthogonal to `β 0` is spanned by `β 1` and `β 2`,
so its squared norm is the sum of the two remaining squared coordinates. This is what turns
the coordinatewise bounds of `Metric.outerPrism.basis_repr_le` into a bound on the
orthogonal component required by
`Kakeya.NonSlab.lineAngle_le_of_orthogonal_component`. -/
private lemma norm_sub_inner_smul_sq (β : OrthonormalBasis (Fin 3) ℝ E) (w : E) :
    ‖w - (inner ℝ w (β 0) : ℝ) • β 0‖ ^ 2
      = (inner ℝ w (β 1) : ℝ) ^ 2 + (inner ℝ w (β 2) : ℝ) ^ 2 := by
  have hpar := β.sum_sq_inner_left w
  rw [Fin.sum_univ_three] at hpar
  rw [norm_sub_inner_smul_sq_of_norm_one (β.orthonormal.1 0)]
  linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **A point close to a line has a small component orthogonal to its direction.**

For a unit direction `u`, membership in the `d`-neighbourhood of the line through `p` with
direction `u` bounds the component of `z - p` orthogonal to `u` by `d`. This is the second
input to `Kakeya.NonSlab.lineAngle_le_of_orthogonal_component`, supplying the comparison of
a tube segment with the core line of its parent tube. -/
private lemma norm_sub_inner_smul_le_of_mem_cthickening {p u z : E} (hu : ‖u‖ = 1)
    {d : ℝ} (hd : 0 ≤ d)
    (hz : z ∈ Metric.cthickening d (AffineSubspace.mk' p (Submodule.span ℝ {u}) : Set E)) :
    ‖(z - p) - (inner ℝ (z - p) u : ℝ) • u‖ ≤ d := by
  -- `‖(z - p) - s • u‖²` is a quadratic in `s`, minimal at `s = ⟪z - p, u⟫`
  have hsq : ∀ s : ℝ, ‖(z - p) - s • u‖ ^ 2
      = ‖z - p‖ ^ 2 - 2 * s * (inner ℝ (z - p) u : ℝ) + s ^ 2 := fun s => by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hu, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  have hinf : Metric.infDist z (AffineSubspace.mk' p (Submodule.span ℝ {u}) : Set E) ≤ d :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (Metric.mem_cthickening_iff.mp hz)).trans_eq
      (ENNReal.toReal_ofReal hd)
  refine le_trans ((Metric.le_infDist ⟨p, AffineSubspace.self_mem_mk' p _⟩).2 fun y hy => ?_) hinf
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (AffineSubspace.mem_mk'.mp hy)
  rw [dist_eq_norm, show z - y = (z - p) - t • u by rw [ht, vsub_eq_sub]; abel]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [hsq, hsq]
  linarith [sq_nonneg (t - (inner ℝ (z - p) u : ℝ))]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **A chord of a set close to a line is nearly parallel to that line.**

Differencing `Kakeya.NonSlab.norm_sub_inner_smul_le_of_mem_cthickening` at the two endpoints:
each is within `d` of the line, so the component of `y - x` orthogonal to the direction is at
most `2d`. This is Step B of `Kakeya.NonSlab.lineAngle_bodyAxis_le`. -/
private lemma norm_sub_inner_smul_le_of_subset_cthickening {S : Set E} {p u : E} (hu : ‖u‖ = 1)
    {d : ℝ} (hd : 0 ≤ d)
    (hST : S ⊆ Metric.cthickening d (AffineSubspace.mk' p (Submodule.span ℝ {u}) : Set E))
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖(y - x) - (inner ℝ (y - x) u : ℝ) • u‖ ≤ 2 * d := by
  rw [show (y - x) - (inner ℝ (y - x) u : ℝ) • u =
      ((y - p) - (inner ℝ (y - p) u : ℝ) • u) - ((x - p) - (inner ℝ (x - p) u : ℝ) • u) by
    rw [show y - x = (y - p) - (x - p) by abel, inner_sub_left, sub_smul]
    abel]
  refine (norm_sub_le _ _).trans ?_
  linarith [norm_sub_inner_smul_le_of_mem_cthickening (p := p) (u := u) hu hd (hST hx),
    norm_sub_inner_smul_le_of_mem_cthickening (p := p) (u := u) hu hd (hST hy)]

/-- **The axis `v(W)` of a convex body** (blueprint `def:ml2bodyAxis`).

The rank-`0` axis of the outer prism `outerPrism W` of blueprint `def:outerPrism`: the unit
vector spanning the direction of largest half-width, that half-width being `τ₀(W)` by
`outerPrism.thicknesses_eq`. Since the affine thicknesses `Metric.thickness ℝ W.carrier k`
are antitone in the rank `k`, the largest half-width is the one at index `0`.

The vector is determined up to sign, which is harmless: everything below depends only on the
line `ℝ v(W)`, through `Kakeya.NonSlab.lineAngle`. -/
noncomputable def bodyAxis (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) : E :=
  (outerPrism hn W.isCompact' W.nonempty').basis 0

omit [MeasurableSpace E] [BorelSpace E] in
/-- The axis is the rank-`0` vector of the prism basis of `outerPrism W`. -/
private lemma bodyAxis_eq (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) :
    bodyAxis hn W = outerPrism.basis hn W.isCompact' W.nonempty' 0 := by
  -- (extracted by Fuse golfer)
  rw [bodyAxis,
    show (outerPrism hn W.isCompact' W.nonempty').basis =
        outerPrism.basis hn W.isCompact' W.nonempty' from PrismNDim.basis_mk' _ _ _]

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_bodyAxis (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) :
    ‖bodyAxis hn W‖ = 1 := by
  rw [bodyAxis_eq]
  exact OrthonormalBasis.norm_eq_one _ 0

/-- **The normal `n(W)` of a convex body** (blueprint `def:ml2bodyNormal`).

The rank-`2` axis of the outer prism `outerPrism W` of blueprint `def:outerPrism`: the unit
vector spanning the direction of *smallest* half-width, that half-width being `τ₂(W)` by
`outerPrism.thicknesses_eq`. Since the affine thicknesses `Metric.thickness ℝ W.carrier k` are
antitone in the rank `k`, the smallest half-width is the one at index `2`; this is the opposite
end of the same frame from `Kakeya.NonSlab.bodyAxis`.

The two directions are genuinely different quantities in `ℝ³` and are used for different
purposes. `bodyAxis` is the *long* direction, and it is the one a tube of a block is aligned
with (`Kakeya.NonSlab.lineAngle_bodyAxis_le`). `bodyNormal` is the direction that *separates*
two flat bodies, and it is the one the tangential case of Main Lemma 2 measures, through
`Kakeya.VeryNotSticky.axisAngle`: the typicality of a plank angle is a statement about
`Kakeya.Prism3D.angle`, i.e. about `basis 0` of a `Plank a b 1`, which by the ascending
half-width convention of `Prism3D` is the plank's normal. Reading `bodyAxis` there compared
the wrong pair of directions.

The vector is determined up to sign, which is harmless: everything below depends only on the
line `ℝ n(W)`, through `Kakeya.NonSlab.lineAngle`. -/
noncomputable def bodyNormal (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) : E :=
  (outerPrism hn W.isCompact' W.nonempty').basis 2

omit [MeasurableSpace E] [BorelSpace E] in
/-- The normal is the rank-`2` vector of the prism basis of `outerPrism W`. -/
lemma bodyNormal_eq (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) :
    bodyNormal hn W = outerPrism.basis hn W.isCompact' W.nonempty' 2 := by
  rw [bodyNormal,
    show (outerPrism hn W.isCompact' W.nonempty').basis =
        outerPrism.basis hn W.isCompact' W.nonempty' from PrismNDim.basis_mk' _ _ _]

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_bodyNormal (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) :
    ‖bodyNormal hn W‖ = 1 := by
  rw [bodyNormal_eq]
  exact OrthonormalBasis.norm_eq_one _ 2

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **The unoriented angle between two unit vectors is `arccos |⟪u,v⟫|`.**

The public form of the private `Kakeya.NonSlab.cos_lineAngle_of_norm_one`, obtained by
inverting the cosine on `[0, π]` (`Real.arccos_eq_of_eq_cos`), the angle lying in `[0, π/2]`.

It is the bridge between `Kakeya.VeryNotSticky.axisAngle`, which measures the angle between two
bodies' normals through `Kakeya.NonSlab.lineAngle`, and `Kakeya.Prism3D.angle`, which is
`arccos |⟪P₁.basis 0, P₂.basis 0⟫|` by definition. With the prescribed-frame enclosure of
`Kakeya.VeryNotSticky.plankWindowEnclosure` the two frames' `basis 0` *are* the two normals, so
the two quantities are equal and the typicality of the plank angles is literally the display
`anglebound` of blueprint `lem:ml2typicalangle`. -/
lemma lineAngle_eq_arccos_abs_inner {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    lineAngle u v = Real.arccos |inner ℝ u v| :=
  (Real.arccos_eq_of_eq_cos (lineAngle_nonneg u v)
    ((lineAngle_le_pi_div_two u v).trans (by linarith [Real.pi_pos]))
    (cos_lineAngle_of_norm_one hu hv).symm).symm

/-- **The ascending frame `f(W)` of a convex body** (blueprint `def:ml2bodyFrame`).

The orthonormal frame of the outer prism `outerPrism W`, reindexed by `Fin.revPerm` so that the
half-widths it carries are *ascending*: `f(W) 0` is the direction of smallest affine thickness,
i.e. the normal `Kakeya.NonSlab.bodyNormal`, and `f(W) 2` is the long axis
`Kakeya.NonSlab.bodyAxis`.

That is the order the type `Prism3D a b c` demands, and the reason this reindexing is named
rather than written out: `Kakeya.VeryNotSticky.plankWindowEnclosure` builds the plank enclosing
the *rescaled* body `L_B(W)` on this very frame, so that `(P j).basis 0` is
`Kakeya.NonSlab.bodyNormal (W j)` on the nose and the plank angles of blueprint
`def:typicalAnglePlank` are literally the body angles of `Kakeya.VeryNotSticky.axisAngle`. `L_B`
is a homothety and does not rotate, so no loss is incurred.

Folding it into a definition is not cosmetic, for the reason recorded on
`Kakeya.VeryNotSticky.bodyNormal`: written out, `outerPrism.basis hn W.isCompact' W.nonempty'`
costs the `finrank` proof plus five instance searches at every occurrence, and two occurrences
in one statement already exhaust the heartbeat budget of a declaration. Use `bodyFrame_repr`
and `bodyFrame_zero` rather than `simp`/`unfold`. -/
noncomputable def bodyFrame (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) :
    OrthonormalBasis (Fin 3) ℝ E :=
  (outerPrism.basis hn W.isCompact' W.nonempty').reindex (Fin.revPerm : Fin 3 ≃ Fin 3)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The coordinates of `Kakeya.NonSlab.bodyFrame` are those of the outer-prism frame, read in
the reversed order. -/
lemma bodyFrame_repr (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) (v : E) (i : Fin 3) :
    (bodyFrame hn W).repr v i
      = (outerPrism.basis hn W.isCompact' W.nonempty').repr v (Fin.rev i) := by
  rw [bodyFrame, OrthonormalBasis.repr_reindex, Fin.revPerm_symm, Fin.revPerm_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The rank-`0` vector of the ascending frame is the normal. -/
@[simp] lemma bodyFrame_zero (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E) :
    bodyFrame hn W 0 = bodyNormal hn W := by
  rw [bodyFrame, bodyNormal_eq, OrthonormalBasis.coe_reindex, Function.comp_apply,
    Fin.revPerm_symm, Fin.revPerm_apply]
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A chord of a convex body has small coordinates in the body's own ascending frame.**

Both endpoints lie in the outer prism of `W`, whose half-width in the direction
`bodyFrame hn W i = outerPrism.basis W (Fin.rev i)` is the affine thickness at rank
`Fin.rev i`; differencing the two endpoints gives the factor `2`.

This is the single-body core of `Kakeya.VeryNotSticky.plankRescaledFamily_spread`, and it is
stated here rather than there because at the fixed ambient space `EuclideanSpace ℝ (Fin 3)` the
term `Metric.outerPrism.basis finrank_euclideanSpace_fin _ _` costs the `finrank` proof and
five instance searches at every occurrence, and this proof mentions it three times. With `hn` a
hypothesis and `E` a variable it costs nothing. -/
lemma abs_bodyFrame_repr_sub_le (hn : Module.finrank ℝ E = 3) (W : ConvexSpaceBody E)
    {w₁ w₂ : E} (h₁ : w₁ ∈ (W.carrier : Set E)) (h₂ : w₂ ∈ (W.carrier : Set E)) (i : Fin 3) :
    |(bodyFrame hn W).repr (w₁ - w₂) i|
      ≤ 2 * Metric.thickness ℝ (W.carrier : Set E) (Fin.rev i) := by
  rw [bodyFrame_repr]
  have hsub : w₁ - w₂ = (w₁ -ᵥ outerPrism.center hn W.isCompact' W.nonempty')
      - (w₂ -ᵥ outerPrism.center hn W.isCompact' W.nonempty') := by
    simp only [vsub_eq_sub]
    abel
  rw [hsub, map_sub, PiLp.sub_apply]
  have h1 := outerPrism.basis_repr_le hn W.isCompact' W.nonempty' h₁ (Fin.rev i)
  have h2 := outerPrism.basis_repr_le hn W.isCompact' W.nonempty' h₂ (Fin.rev i)
  calc
    |_ - _| ≤ _ + _ := abs_sub _ _
    _ ≤ 2 * Metric.thickness ℝ (W.carrier : Set E) (Fin.rev i) := by linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A chord of a convex body is nearly parallel to the body's axis.**

Both endpoints lie in the outer prism of `W`, whose half-widths in the two directions
transverse to the axis `bodyAxis hn W` are the affine thicknesses at ranks `1` and `2`. So
the component of the chord `y - x` orthogonal to the axis is bounded by those two
thicknesses. This is Step A of `Kakeya.NonSlab.lineAngle_bodyAxis_le`. -/
private lemma norm_sub_inner_bodyAxis_le (hn : Module.finrank ℝ E = 3)
    (W : ConvexSpaceBody E) {x y : E} (hx : x ∈ W.carrier) (hy : y ∈ W.carrier) {M : ℝ}
    (h1 : Metric.thickness ℝ W.carrier 1 ≤ M) (h2 : Metric.thickness ℝ W.carrier 2 ≤ M) :
    ‖(y - x) - (inner ℝ (y - x) (bodyAxis hn W) : ℝ) • bodyAxis hn W‖ ≤ 3 * M := by
  have hM : 0 ≤ M := (Metric.thickness_nonneg W.carrier 1).trans h1
  -- each coordinate of the chord in the prism basis is at most twice the matching thickness
  have hcoord : ∀ i : Fin 3, Metric.thickness ℝ W.carrier i ≤ M →
      |(inner ℝ (y - x) (outerPrism.basis hn W.isCompact' W.nonempty' i) : ℝ)| ≤ 2 * M := by
    intro i hi
    have hxi := outerPrism.basis_repr_le hn W.isCompact' W.nonempty' hx i
    have hyi := outerPrism.basis_repr_le hn W.isCompact' W.nonempty' hy i
    rw [real_inner_comm, ← OrthonormalBasis.repr_apply_apply,
      show y - x = (y -ᵥ outerPrism.center hn W.isCompact' W.nonempty')
        - (x -ᵥ outerPrism.center hn W.isCompact' W.nonempty') by simp only [vsub_eq_sub]; abel,
      map_sub, PiLp.sub_apply]
    calc |_ - _| ≤ _ + _ := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have k1 := hcoord 1 (by simpa using h1)
  have k2 := hcoord 2 (by simpa using h2)
  rw [bodyAxis_eq hn W]
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_sub_inner_smul_sq]
  linarith [sq_le_sq' (neg_le_of_abs_le k1) (le_of_abs_le k1),
    sq_le_sq' (neg_le_of_abs_le k2) (le_of_abs_le k2), sq_nonneg M]

/-- **Constant in Lemma `lem:ml2bodyAngle`** (blueprint `def:ml2bodyAngleConstant`).

An absolute constant `C ≥ 1` such that a tube whose intersection with the ball is comparable
to a segment `T_B` of a block of the body `W` makes an angle at most `C · b / r₁` with the
axis `v(W)`. It depends only on the absolute implicit constant `C₀` of the thickness
comparisons `τ₀(T_B) ∼ r₁`, `τ₁(T_B) ∼ δ` of (C3), of the comparability defining `𝕋(T_B)`,
and of `τ₀(W) ∼ r₁`, `τ₁(W) ∼ b` of (C4); in particular it does not depend on `δ`, on the
ambient parameters `β, ζ`, on the ball `B`, on `W` or on the tube. It does depend on the
ambient dimension, fixed at `3` throughout. The displayed value is provisional; the exact
value comes out of the proof of `Kakeya.NonSlab.lineAngle_bodyAxis_le`. -/
noncomputable def bodyAngleConstant (C₀ : NNReal) : NNReal := 2 ^ 6 * C₀ ^ 4

lemma one_le_bodyAngleConstant {C₀ : NNReal} (hC₀ : 1 ≤ C₀) : 1 ≤ bodyAngleConstant C₀ :=
  one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hC₀)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Tubes of a block are aligned with the axis of its body** (blueprint `lem:ml2bodyAngle`).

Here `S` is the tube segment `T_B ∈ 𝕋_{B,W}` of (C3): it lies in the body `W` of its block by
(C4), has affine thicknesses `∼ (r₁, δ, δ)`, and is contained in the `C₀ δ`-neighbourhood of
the core line `p + ℝ u` of the parent tube `T ∈ 𝕋(T_B)`, which is the content of the
comparability `T ∩ B ∼ T_B` of (C3).

Two steps, as in the blueprint. The segment against its body: `S ⊆ W ⊆ outerPrism W`, a box
with axis `v(W)` and half-widths `τ₀(W) ∼ r₁`, `τ₁(W) ∼ b`, `τ₂(W) ∼ a ≤ b`, while `S` has
extent `≳ r₁`; hence the long direction of `S` makes an angle `≲ b / r₁` with `v(W)`. The
segment against its parent tube: `S` lies within `≲ δ` of the line of `T` and has extent
`≳ r₁`, so that line makes an angle `≲ δ / r₁ ≤ b / r₁` with the long direction of `S`.
Adding the two bounds through `Kakeya.NonSlab.lineAngle_le_add` gives the claim. -/
theorem lineAngle_bodyAxis_le (hn : Module.finrank ℝ E = 3)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {δ a b r₁ : NNReal}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b) (hbr₁ : b ≤ r₁)
    (W : ConvexSpaceBody E) (hW : HasThicknesses W.carrier C₀ ![(r₁ : ℝ), b, a])
    {S : Set E} (hSW : S ⊆ W.carrier) (hS : HasThicknesses S C₀ ![(r₁ : ℝ), δ, δ])
    {p u : E} (hu : ‖u‖ = 1)
    (hST : S ⊆ cthickening (C₀ * δ) (AffineSubspace.mk' p (Submodule.span ℝ {u}) : Set E)) :
    lineAngle u (bodyAxis hn W) ≤ (bodyAngleConstant C₀ : ℝ) * ((b : ℝ) / r₁) := by
  -- Real-valued versions of the NNReal hypotheses
  have hC₀ℝ : (1 : ℝ) ≤ (C₀ : ℝ) := NNReal.coe_le_coe.2 hC₀
  have hδb : (δ : ℝ) ≤ (b : ℝ) := NNReal.coe_le_coe.2 (hδa.trans hab)
  have habℝ : (a : ℝ) ≤ (b : ℝ) := NNReal.coe_le_coe.2 hab
  have hbℝ : (0 : ℝ) < (b : ℝ) := (NNReal.coe_pos.2 hδ).trans_le hδb
  have hr₁ℝ : (0 : ℝ) < (r₁ : ℝ) := hbℝ.trans_le (NNReal.coe_le_coe.2 hbr₁)
  -- a chord of `S` longer than `m = r₁ / (2 C₀)` exists, since `τ₀(S) ≥ r₁ / C₀`
  have hCr : (0 : ℝ) < (C₀ : ℝ)⁻¹ * (r₁ : ℝ) :=
    mul_pos (inv_pos.2 (lt_of_lt_of_le one_pos hC₀ℝ)) hr₁ℝ
  have hm : (0 : ℝ) < (C₀ : ℝ)⁻¹ * (r₁ : ℝ) / 2 := half_pos hCr
  obtain ⟨x, hxS, y, hyS, hxy⟩ :=
    exists_dist_gt_of_lt_thickness_zero (C := (C₀ : ℝ)⁻¹ * (r₁ : ℝ) / 2)
      (W.isCompact'.isBounded.subset hSW) hm.le ((half_lt_self hCr).trans_le (hS 0).1)
  have hwm : (C₀ : ℝ)⁻¹ * (r₁ : ℝ) / 2 < ‖y - x‖ := dist_eq_norm' x y ▸ hxy
  -- STEP A: the chord vs. the body axis, using `τ₁(W), τ₂(W) ≤ C₀ b`
  have hW1 : Metric.thickness ℝ W.carrier 1 ≤ (C₀ : ℝ) * (b : ℝ) := (hW 1).2
  have hW2 : Metric.thickness ℝ W.carrier 2 ≤ (C₀ : ℝ) * (b : ℝ) :=
    ((hW 2).2 : Metric.thickness ℝ W.carrier 2 ≤ (C₀ : ℝ) * (a : ℝ)).trans
      (mul_le_mul_of_nonneg_left habℝ C₀.coe_nonneg)
  have hA := lineAngle_le_of_norm_orthogonal_le (norm_bodyAxis hn W) hm hwm
    (norm_sub_inner_bodyAxis_le hn W (hSW hxS) (hSW hyS) hW1 hW2)
  -- STEP B: the chord vs. the core line of the parent tube, using `C₀ δ ≤ C₀ b`
  have hB : lineAngle u (y - x) ≤ Real.pi / 2 *
      (2 * ((C₀ : ℝ) * (b : ℝ)) / ((C₀ : ℝ)⁻¹ * (r₁ : ℝ) / 2)) :=
    (lineAngle_comm u (y - x)).trans_le (lineAngle_le_of_norm_orthogonal_le hu hm hwm
      ((norm_sub_inner_smul_le_of_subset_cthickening (p := p) hu
          (mul_nonneg C₀.coe_nonneg δ.coe_nonneg) hST hxS hyS).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδb C₀.coe_nonneg) zero_le_two)))
  -- STEP C: triangle inequality and bookkeeping
  calc lineAngle u (bodyAxis hn W)
      ≤ lineAngle u (y - x) + lineAngle (y - x) (bodyAxis hn W) :=
        lineAngle_le_add u (y - x) (bodyAxis hn W)
    _ ≤ Real.pi / 2 * (2 * ((C₀ : ℝ) * (b : ℝ)) / ((C₀ : ℝ)⁻¹ * (r₁ : ℝ) / 2))
        + Real.pi / 2 * (3 * ((C₀ : ℝ) * (b : ℝ)) / ((C₀ : ℝ)⁻¹ * (r₁ : ℝ) / 2)) :=
        add_le_add hB hA
    _ = 5 * Real.pi * (C₀ : ℝ) ^ 2 * ((b : ℝ) / r₁) := by
        rw [inv_mul_eq_div, div_div, div_div_eq_mul_div, div_div_eq_mul_div]; ring
    _ ≤ 64 * (C₀ : ℝ) ^ 4 * ((b : ℝ) / r₁) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul ((mul_le_mul_of_nonneg_left Real.pi_le_four (by norm_num)).trans
              (by norm_num)) (pow_le_pow_right₀ hC₀ℝ (by norm_num))
            (sq_nonneg _) (by norm_num)) (div_nonneg b.coe_nonneg r₁.coe_nonneg)
    _ = (bodyAngleConstant C₀ : ℝ) * ((b : ℝ) / r₁) := by
      rw [bodyAngleConstant, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_pow]
      norm_num

end Axis

end Kakeya.NonSlab

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

/-- The radius `r₁ = δ^{exscal}` of the balls `B ∈ 𝔅` of the covering family of Configuration
`hyp:ml2setup`; the factoring bodies of (C4) have dimensions `a × b × r₁`. -/
noncomputable def r₁ (cfg : VeryNotSticky) : NNReal := cfg.δ ^ cfg.exscal

/-- The angular scale `ρ₂ = b / r₁` of the non-slab case. -/
noncomputable def rho2 (cfg : VeryNotSticky) : NNReal := cfg.b / cfg.r₁

/-- **The angular scale `ρ₂` is admissible** (blueprint `lem:ml2rho2range`).

In the non-slab case `b ≤ δ^{exscal} r₁` the scale `ρ₂ = b / r₁` lies in
`[δ^{1-exscal}, δ^{exscal}]`: the upper bound is the non-slab hypothesis and the lower bound
is `b ≥ δ`. Consequently `ρ₂` lies in the window `[δ^{1-exscalb}, δ^{exscalb}]` of the
`ρ`-tube counting hypothesis `rho_count` of (C1), and every essentially distinct family of
`ρ₂`-tubes covering the configuration's *parent* family has at least
`(max C₀ L)⁻¹ ρ₂^{-2-ζ}` members, `L = Tube.coverCountLoss 3`.

The parent family is what the field `Kakeya.VeryNotSticky.rho_count` supplies; the
`∀`-over-covers form read here is `Kakeya.VeryNotSticky.rhoCountParent_of_rhoParentData`, whose
constant absorbs the cover-comparison loss `L`: see `Kakeya.VeryNotSticky.RhoCountParent`, and
`Kakeya.VeryNotSticky.not_rhoCountFieldOldStatement_empty` for why the earlier form of this
conclusion — the count on `cfg.s` itself, with no constant — was *false* rather than merely
unproved. This declaration has no term-level users; the count is spent through the carried field
`Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount`, whose own constant is, the carried `Ccnt ≤ δ^{-18η}` of
`Kakeya.VeryNotSticky.SplitInputs.countConstant` and not a δ-free number — which is what makes
the transport from this parent count to that field's node count possible at all
(`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData`).

The blueprint's (P1) identifies the two coarse exponents `exscal` and `exscalb`; this is the
field `cfg.hscale` of `Kakeya.VeryNotSticky`. The hypothesis `hexscal` makes this window
nonempty. -/
theorem rho2_range.{u} (cfg : VeryNotSticky.{u}) (hδ : 0 < cfg.δ) (_hδ1 : cfg.δ ≤ 1)
    (_hexscal : cfg.exscal ≤ 1 / 2)
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁) :
    cfg.rho2 ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscal)) (cfg.δ ^ cfg.exscal) ∧
      ∃ sPar : Finset cfg.ι, cfg.s ⊆ sPar ∧
        ∀ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube cfg.rho2 (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ sPar, ∃ j ∈ tρ, (cfg.T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
          (tρ : Set κ).Pairwise
            (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤
            ((max cfg.C₀ (Tube.coverCountLoss 3) : NNReal) : ℝ) * (tρ.card : ℝ) := by
  have hr₁ : 0 < cfg.r₁ := NNReal.rpow_pos hδ
  have hmem : cfg.rho2 ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscal)) (cfg.δ ^ cfg.exscal) := by
    refine ⟨(le_div_iff₀ hr₁).2 ?_, (div_le_iff₀ hr₁).2 hnotslab⟩
    calc
      cfg.δ ^ (1 - cfg.exscal) * cfg.r₁ = cfg.δ ^ ((1 - cfg.exscal) + cfg.exscal) := by
        rw [NNReal.rpow_add hδ.ne']; rfl
      _ = cfg.δ := by rw [sub_add_cancel, NNReal.rpow_one]
      _ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
  obtain ⟨sPar, hsub, -, -, hcnt⟩ :=
    rhoCountParent_of_rhoParentData cfg.hδ cfg.hδ1 cfg.hexscalb.le (le_max_right _ _)
      cfg.rho_count
  exact ⟨hmem, sPar, hsub, fun κ tρ Tρ hcover hdisj =>
    hcnt cfg.rho2 (by rw [← cfg.hscale]; exact hmem) κ tρ Tρ hcover hdisj⟩

/-- **Absorbing a power of the angular scale into `δ^{exscal}`** (blueprint
`lem:ml2rho2PowAbsorb`).

The one step at which the angular scale is traded for the ball scale, in the shape the two
non-slab leaves consume it: `ρ₂ = b / r₁ ≤ δ^{exscal}` is the non-slab hypothesis divided by
`r₁ > 0`, and raising it to the nonnegative power `(2+ζ)β` gives the bound below. It is stated
once here so that neither `Kakeya.VeryNotSticky.goalMult_of_multBodies_le` nor
`Kakeya.VeryNotSticky.goalMult_of_theta_lt` repeats the exponent manipulation.

The exponent is written `(2+ζ)β` on the angular scale and `exscal(2+ζ)β` on `δ`, which is the
shape produced by `Kakeya.VeryNotSticky.nonslabSplitBound`, rather than the blueprint's
`(ρ₂^{2+ζ}|𝕋|)^β`; the two agree by `ENNReal.mul_rpow_of_nonneg` and `ENNReal.rpow_mul`, and
the cardinality factor is carried along untouched so that the statement is directly usable.

No hypothesis beyond `hnotslab` is needed: unlike `Kakeya.VeryNotSticky.rho2_range` this does
not go through the `ρ`-tube counting window, so `exscal ≤ 1/2` plays no role. -/
theorem rho2PowAbsorb (cfg : VeryNotSticky.{u})
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁) :
    (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) * (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β := by
  have hr1_pos : (0 : NNReal) < cfg.r₁ := by
    unfold r₁
    exact NNReal.rpow_pos cfg.hδ
  have hle : cfg.rho2 ≤ cfg.δ ^ cfg.exscal := by
    rw [rho2]
    rw [div_le_iff₀ hr1_pos]
    exact hnotslab
  have hρ2le_e : (cfg.rho2 : ENNReal) ≤ (cfg.δ : ENNReal) ^ cfg.exscal := by
    rw [← ENNReal.coe_rpow_of_nonneg cfg.δ cfg.hexscal.le]
    exact ENNReal.coe_le_coe.mpr hle
  have h2ζ : (0 : ℝ) ≤ 2 + cfg.ζ := by linarith [cfg.hζ]
  have hpow : (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) ≤
      (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β) := by
    calc
      (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β)
          ≤ ((cfg.δ : ENNReal) ^ cfg.exscal) ^ ((2 + cfg.ζ) * cfg.β) :=
            ENNReal.rpow_le_rpow hρ2le_e (mul_nonneg h2ζ cfg.hβ.le)
      _ = (cfg.δ : ENNReal) ^ (cfg.exscal * ((2 + cfg.ζ) * cfg.β)) := by
          rw [← ENNReal.rpow_mul]
      _ = (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β) := by
          congr 1; ring
  exact mul_le_mul_of_nonneg_right hpow bot_le

/-- **Turning a non-slab exponent loss into the goal** (blueprint
`lem:ml2nonslabLossToGain`).

Both non-slab multiplicity leaves end at a bound of the shape `hbound` and differ only in the
loss `L` they have accumulated and in the budget lemma discharging `hbudget`: for the
small-multiplicity leaf `Kakeya.VeryNotSticky.goalMult_of_multBodies_le` the loss is
`L = η + C_sep(ϱ+η)/4` and the gain is `ν = exscal·β`, discharged by
`Kakeya.VeryNotSticky.smallMultiplicityBudget`; on the tangential side the loss is the
accumulated one of `Kakeya.VeryNotSticky.tangentialAccumulatedBudget`. The exponent arithmetic
is therefore done once here and no leaf repeats it.

The proof is `Kakeya.VeryNotSticky.rho2PowAbsorb` followed by `ENNReal.rpow_add` — legitimate
since `0 < δ ≤ 1`, so `(δ : ℝ≥0∞) ≠ 0` and `≠ ⊤` — and then
`ENNReal.rpow_le_rpow_of_exponent_ge`, `hbudget` being exactly `ν ≤ exscal(2+ζ)β - L`. -/
theorem nonslabLossToGain (cfg : VeryNotSticky.{u}) {L ν : ℝ}
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁)
    (hbudget : ν + L ≤ cfg.exscal * (2 + cfg.ζ) * cfg.β)
    (hbound : ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (-L) * (cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
        (cfg.s.card : ENNReal) ^ cfg.β) :
    cfg.goalMult ν := by
  have hδ_pos : 0 < (cfg.δ : ENNReal) := ENNReal.coe_pos.mpr cfg.hδ
  have hδ_ne0 : (cfg.δ : ENNReal) ≠ 0 := hδ_pos.ne'
  have hδ_ne_top : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ_le_one : (cfg.δ : ENNReal) ≤ 1 := ENNReal.coe_le_one_iff.mpr cfg.hδ1
  have hAbs := rho2PowAbsorb cfg hnotslab
  have hmain : ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
      (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β - L) *
        (cfg.s.card : ENNReal) ^ cfg.β := by
    calc
      ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
        ≤ (cfg.δ : ENNReal) ^ (-L) *
            ((cfg.rho2 : ENNReal) ^ ((2 + cfg.ζ) * cfg.β) *
              (cfg.s.card : ENNReal) ^ cfg.β) := by
            simpa [mul_assoc] using hbound
      _ ≤ (cfg.δ : ENNReal) ^ (-L) *
            ((cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β) *
              (cfg.s.card : ENNReal) ^ cfg.β) := by
            gcongr
      _ = (cfg.δ : ENNReal) ^ (-L + cfg.exscal * (2 + cfg.ζ) * cfg.β) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            rw [ENNReal.rpow_add (-L) (cfg.exscal * (2 + cfg.ζ) * cfg.β) hδ_ne0 hδ_ne_top]
            rw [← mul_assoc]
      _ = (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β - L) *
            (cfg.s.card : ENNReal) ^ cfg.β := by
            congr 1; ring_nf
  have hExp : ν ≤ cfg.exscal * (2 + cfg.ζ) * cfg.β - L := by linarith
  have hpow : (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β - L) ≤
      (cfg.δ : ENNReal) ^ ν :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδ_le_one hExp
  have hmul : (cfg.δ : ENNReal) ^ (cfg.exscal * (2 + cfg.ζ) * cfg.β - L) *
        (cfg.s.card : ENNReal) ^ cfg.β ≤
      (cfg.δ : ENNReal) ^ ν * (cfg.s.card : ENNReal) ^ cfg.β :=
    mul_le_mul' hpow le_rfl
  unfold goalMult
  exact hmain.trans hmul

/-- **The dilated angular scale `ρ₂*`** (blueprint `def:ml2rho2star`).

`ρ₂* = 2 C_{lem:ml2bodyAngle}(C₀) ρ₂`, where the factor
`C_{lem:ml2bodyAngle}(C₀)` is the loss of `Kakeya.NonSlab.lineAngle_bodyAxis_le` and the
factor `2` is the loss of the triangle inequality in
`Kakeya.VeryNotSticky.angularInnerCount`. Once the comparison constant `C₀` is fixed,
`ρ₂* ∼ ρ₂` with a fixed ratio.

Since `ρ₂ ≤ δ^{exscal}` by `rho2_range`, one has `ρ₂* ≤ 1` as soon as
`δ^{exscal} ≤ (2 C_{lem:ml2bodyAngle}(C₀))⁻¹`; this is the first field of
`Kakeya.VeryNotSticky.CaseScale`. -/
noncomputable def rho2Star (cfg : VeryNotSticky) (C₀ : NNReal) : NNReal :=
  2 * NonSlab.bodyAngleConstant C₀ * cfg.rho2

lemma rho2_le_rho2Star (cfg : VeryNotSticky) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    cfg.rho2 ≤ cfg.rho2Star C₀ :=
  le_mul_of_one_le_left' (one_le_mul_of_one_le_of_one_le (by norm_num)
    (NonSlab.one_le_bodyAngleConstant hC₀))

/-- **The dilated scale `ρ₂*` is an admissible angular scale** (blueprint
`lem:ml2rho2starRange`).

In the non-slab case the four scales are ordered

`δ ≤ ρ₂ ≤ ρ₂*/2 ≤ ρ₂* ≤ 1`,

so that `ρ₂*` lies in `[δ, 1]`, the range on which the parent family `𝕋_{ρ₂*}` of blueprint
`uniformSetOfTubes` is defined, and `ρ₂*/2 = C_{lem:ml2bodyAngle}(C₀) ρ₂` lies in `[δ, 1/2]`,
the range `Kakeya.VeryNotSticky.angularInnerCount` requires. Recording the chain once here
saves re-deriving it in `Kakeya.VeryNotSticky.nonslabFibrePartition` and in the pointwise
product bound.

The three steps are independent: `δ ≤ ρ₂` uses `δ ≤ b` and `r₁ ≤ 1` from
`Kakeya.VeryNotSticky`; `2ρ₂ ≤ ρ₂*` is `1 ≤ C_{lem:ml2bodyAngle}(C₀)`; and `ρ₂* ≤ 1` needs
both `ρ₂ ≤ δ^{exscal}` from `Kakeya.VeryNotSticky.rho2_range` and the fixed-scale threshold
`hscale`, which is the field `rho2Star_le_one` of `Kakeya.VeryNotSticky.CaseScale`. -/
theorem rho2Star_range (cfg : VeryNotSticky) (hδ : 0 < cfg.δ) (hδ1 : cfg.δ ≤ 1)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hscale : cfg.δ ^ cfg.exscal ≤ (2 * NonSlab.bodyAngleConstant C₀)⁻¹)
    (hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁) :
    cfg.δ ≤ cfg.rho2 ∧ 2 * cfg.rho2 ≤ cfg.rho2Star C₀ ∧ cfg.rho2Star C₀ ≤ 1 := by
  have hr₁0 : 0 < cfg.r₁ := NNReal.rpow_pos hδ
  have hδb : cfg.δ * cfg.r₁ ≤ cfg.b := by
    calc
      cfg.δ * cfg.r₁ ≤ cfg.δ * 1 :=
        mul_le_mul_right (NNReal.rpow_le_one hδ1 cfg.hexscal.le) cfg.δ
      _ = cfg.δ := mul_one _
      _ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
  have h2le : (2 : NNReal) ≤ 2 * NonSlab.bodyAngleConstant C₀ := by
    simpa using mul_le_mul_right (NonSlab.one_le_bodyAngleConstant hC₀) 2
  refine ⟨(le_div_iff₀ hr₁0).2 hδb, mul_le_mul_left h2le cfg.rho2, ?_⟩
  calc
    cfg.rho2Star C₀ ≤ (2 * NonSlab.bodyAngleConstant C₀) * (cfg.δ ^ cfg.exscal) :=
      mul_le_mul_right ((div_le_iff₀ hr₁0).2 hnotslab) _
    _ ≤ (2 * NonSlab.bodyAngleConstant C₀) * (2 * NonSlab.bodyAngleConstant C₀)⁻¹ :=
      mul_le_mul_right hscale _
    _ = 1 := mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le (by norm_num) h2le))

open scoped Classical in
/-- The tubes of `𝕋` shading `x` whose direction makes an angle at most `ρ` with the line
`ℝ v`; the set `{T ∈ 𝕋_Y(x) : ∠(T, v) ≤ ρ}` of blueprint `lem:ml2angularInnerCount`. -/
noncomputable def angularFibre (cfg : VeryNotSticky) (x v : EuclideanSpace ℝ (Fin 3))
    (ρ : ℝ) : Finset cfg.ι :=
  {i ∈ cfg.s | x ∈ (cfg.T i).shade ∧ NonSlab.lineAngle (cfg.T i).direction v ≤ ρ}

/-- **Counting the tubes through a point near a fixed direction** (blueprint
`lem:ml2angularInnerCount`).

If the set `{T ∈ 𝕋_Y(x) : ∠(T, v) ≤ ρ}` is non-empty, pick a member `T₀` of it; then
`x ∈ Y(T₀)`, and by the triangle inequality for `Kakeya.NonSlab.lineAngle` every member `T`
of the set satisfies `∠(T, T₀) ≤ ∠(T, v) + ∠(v, T₀) ≤ 2ρ`. So the set is contained in
`{T ∈ 𝕋_Y(x) : ∠(T, T₀) ≤ 2ρ}`, whose cardinality is `≈ μ(2ρ)` by the angular multiplicity
function of (C1).

The factor `2` is genuinely needed: the blueprint's `μ` measures the angle to a *tube* of `𝕋`
shading `x`, not to an arbitrary direction `v`, and carries no monotonicity or doubling
property that would absorb the passage from `ρ` to `2ρ`. The hypothesis `ρ ≤ 1/2` of the
blueprint places `2ρ` in the range `[δ, 1]` on which `μ` is defined; it is not needed for the
containment itself, and the identification `μ(2ρ) ≈ μ(𝕋[T_{2ρ}], Y)` is the last assertion of
the (not yet formalized) blueprint `lem:ml2murho`, so the conclusion is stated in terms of
the fibre at `T₀` rather than of `μ`. -/
theorem angularInnerCount (cfg : VeryNotSticky) (x v : EuclideanSpace ℝ (Fin 3)) {ρ : ℝ}
    (_hρ : 0 ≤ ρ) :
    cfg.angularFibre x v ρ = ∅ ∨
      ∃ i₀ ∈ cfg.s, x ∈ (cfg.T i₀).shade ∧
        cfg.angularFibre x v ρ ⊆ cfg.angularFibre x (cfg.T i₀).direction (2 * ρ) := by
  classical
  rcases Finset.eq_empty_or_nonempty (cfg.angularFibre x v ρ) with h | ⟨i₀, hi₀⟩
  · exact Or.inl h
  obtain ⟨hi₀s, hi₀x, hi₀angle⟩ := Finset.mem_filter.mp hi₀
  refine Or.inr ⟨i₀, hi₀s, hi₀x, fun i hi => ?_⟩
  obtain ⟨his, hix, hiangle⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨his, hix, ?_⟩
  linarith [NonSlab.lineAngle_le_add (cfg.T i).direction v (cfg.T i₀).direction,
    (NonSlab.lineAngle_comm v (cfg.T i₀).direction).trans_le hi₀angle]

open scoped Classical in
/-- The tubes of `𝕋` shading `x` *for the shading `Y`* whose direction makes an angle at most
`ρ` with the line `ℝ v`.

This is `Kakeya.VeryNotSticky.angularFibre` with the shading left free, which is what blueprint
`lem:ml2murho` needs: that lemma produces the angular multiplicity function only after passing
to a `⪆ 1` refinement `Y'` of the configuration's own shading. -/
noncomputable def angularFibreWith (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (x v : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) : Finset cfg.ι :=
  {i ∈ cfg.s | x ∈ (Y i).shade ∧ NonSlab.lineAngle (cfg.T i).direction v ≤ ρ}

/-- At the configuration's own shading, `Kakeya.VeryNotSticky.angularFibreWith` is
`Kakeya.VeryNotSticky.angularFibre`. -/
lemma angularFibre_eq_angularFibreWith (cfg : VeryNotSticky)
    (x v : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) :
    cfg.angularFibre x v ρ =
      cfg.angularFibreWith (fun i ↦ (cfg.T i).toShadedBody) x v ρ := by
  rfl

/-- **The angular multiplicity function `μ(ρ)`** (blueprint `def:ml2murho`, equation
`defmurho`).

`cfg.IsAngularMultiplicity Y C μ` says that the function `ρ ↦ μ(ρ)`, defined on the angular
range `[δ, 1]`, records the common size of the angular fibres of the shading `Y`: for every
tube `T₀ ∈ 𝕋` and every point `x ∈ Y(T₀)`,

`#{T ∈ 𝕋_Y(x) : ∠(T, T₀) ≤ ρ} ≈ μ(ρ)`,

with the two-sided comparison written out at the explicit constant `C`, per the project
convention on `⪅`-notation. Note that the base point `x` and the tube `T₀` are quantified
*inside* the comparison: the content of the definition is that the count depends on `ρ` alone.

The two ends of the angular range `[δ, 1]` are not symmetric. At the bottom, `δ` is where the
fibre stops varying: two essentially distinct `δ`-tubes through a common point make an angle
`≳ δ`. At the top, `1` is a *normalisation* and not a scale past which the condition has become
vacuous — `Kakeya.NonSlab.lineAngle` takes values in `[0, π/2]` and `π/2 > 1`, so the fibre at
`ρ = 1` is in general a proper subset of `𝕋_Y(x)`. Truncating there costs only an absolute
factor, because the projective space of directions of `ℝ³` has diameter `π/2` and is covered by
an absolute number of angular balls of radius `1/2`; the blueprint pays for the normalisation at
exactly that point, in the second consequence `murhoConsequences` of `lem:ml2murho`. -/
def IsAngularMultiplicity (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (C : NNReal) (μ : ℝ → NNReal) : Prop :=
  ∀ ρ : ℝ, (cfg.δ : ℝ) ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ cfg.s, ∀ x ∈ (Y i₀).shade,
    (((cfg.angularFibreWith Y x (cfg.T i₀).direction ρ).card : ℕ) : NNReal) ≤ C * μ ρ ∧
      μ ρ ≤ C * (((cfg.angularFibreWith Y x (cfg.T i₀).direction ρ).card : ℕ) : NNReal)

/-- **The angular multiplicity data of (C1)** (blueprint `hyp:ml2setup` (C1), `def:ml2murho`).

The bundle of the angular multiplicity function `μ(ρ)` of `defmurho` together with its
uniformity constant, read at the configuration's *own* shading. Blueprint (C1) lists `μ(ρ)` as
part of Configuration `hyp:ml2setup`, on the understanding — recorded in the blueprint just
after `lem:ml2murho` — that the refinement `Y'` produced by that lemma has already been
absorbed into `Y`.

It is a bundle over `cfg` rather than a field of `Kakeya.VeryNotSticky` for a layering reason:
`Kakeya.NonSlab.lineAngle` and `Kakeya.VeryNotSticky.angularFibreWith` are defined downstream
of the configuration structure, so a field would require relocating the angular primitives
above it. The second assertion of `lem:ml2murho`, the identification
`μ(𝕋[T_ρ], Y) ≈ μ(ρ)`, cannot live on `cfg` at all: it mentions the family `𝕋_ρ` of parent
tubes at the angular scale `ρ`, which enters only with the hierarchy of
`Kakeya.VeryNotSticky.SplitInputs`. That structure records
neither half as such: its fields `Cang`, `angularConstant` and `angularFibre_le_fibreMult` carry
GWZ's *composed* bound (`gwz.txt` l.2321-2322) — the inner angular count at every point and
direction is at most `Cang` times the multiplicity of the fibre `𝕋[T_{ρ₂*}]` — which is the one
consequence of `μ(ρ)` the splitting consumes (`Kakeya.VeryNotSticky.nonslabPointwiseBound`).
The earlier fields `angMult` and `fibreAngularMult`, which carried the two halves separately,
are not fields of `SplitInputs`; this bundle is consumed only by
`Kakeya.VeryNotSticky.angularFibre_card_le_mul_mu` below. -/
structure AngularMultiplicity (cfg : VeryNotSticky) where
  /-- the angular multiplicity function `ρ ↦ μ(ρ)` of `defmurho` -/
  μ : ℝ → NNReal
  /-- the uniformity constant hidden in the `≈` of `defmurho` -/
  C : NNReal
  /-- the constant is at least one, so that it may be used on either side of a comparison -/
  one_le_C : 1 ≤ C
  /-- `defmurho` itself, at the configuration's own shading -/
  isAngularMultiplicity : cfg.IsAngularMultiplicity (fun i ↦ (cfg.T i).toShadedBody) C μ

set_option maxHeartbeats 1000000 in
open Kakeya.AngularCover Tube ShadedTube in
open scoped Classical in
/-- **Uniform angular multiplicity function** (blueprint `lem:ml2murho`).

For a uniform set `(𝕋, Y)` of `δ`-tubes in `B_1` there is a `⪆ 1` refinement `(𝕋, Y')` and a
function `ρ ↦ μ(ρ)` on `[δ, 1]` with `#{T ∈ 𝕋_{Y'}(x) : ∠(T, T₀) ≤ ρ} ≈ μ(ρ)` for every
`T₀ ∈ 𝕋` and every `x ∈ Y'(T₀)`. The blueprint proof identifies `𝕋_Y(x)` with a set of
directions in `S²`, extracts a uniform subset `U_x ⊆ 𝕋_Y(x)` with `|U_x| ⪆ |𝕋_Y(x)|` by
dyadic pigeonholing on the angular scales, and defines `Y'` by `x ∈ Y'(T) ↔ T ∈ U_x`.

**The two constants carry the whole content, so they are stated explicitly.** Blueprint
`murhoRefinementConstantBound` and `murhoConstantBound` are `δ^η ≤ c ≤ 1` and
`1 ≤ C ≤ δ^{-η}`, and without them the statement is *vacuous*: with `Y' := Y`, `c := 1`,
`μ ≡ 1` and `C := |𝕋|` the upper bound is the trivial `card ≤ |𝕋|` and the lower bound holds
because `T₀` always lies in its own angular fibre. Both bounds are of dyadic-pigeonhole origin
— the loss is a power of the number `⌈log(1/δ)⌉` of angular scales — so they hold only once `δ`
is below a threshold determined by `η` alone, which is why the statement is quantified over a
threshold `δ₀` in the style of `Kakeya.VeryNotSticky.exists_setup` rather than asserted at a
fixed configuration.

**The proof.** `Kakeya.AngularCover.exists_angularCover` puts the directions of `𝕋` into a
nested family of `σ_k/8`-separated nets of `S²` at the `N+1` grid scales `σ_k = δ^{2k/N}`
(`σ = δ²`), read as an honest `Tube.GridCoverSystem` of direction tubes through the
origin. `ShadedTube.exists_balanced_shadeRefinement_of_cover` pigeonholes the shading against
that hierarchy — no branching bracket on the tubes is needed, only the cover's assignment — and
returns `Y'` with the shades shrunk together with a single band vector `Pstar` such that at
every retained point, every grid index `k` and every retained tube, the angular cell of that
tube carries between `2^{Pstar k}` and `4·2^{Pstar k}` retained members. Its shade-mass loss is
`(⌊log₂|𝕋|⌋+1)^{2N+2}`, which is `≤ δ^{-η}` by
`Kakeya.AngularCover.exists_polylog_threshold_ennreal` because
`Kakeya.Tube.card_le_of_densityIn_le`, fed by `maxDensity_le`, gives `|𝕋| ≤ C₃ δ^{-2-η}`.

For `ρ ∈ [δ, 1]` put `μ(ρ) := 2^{Pstar k(ρ)}`, where `k(ρ)` is the *first* grid index with
`σ_{k(ρ)} ≤ ρ`. The lower bound is that the whole angular cell of `T₀` at that index lies in
the fibre: two members of a cell are within `σ_k/2` of each other in `S²`, and
`(π/2)(σ_k/2) ≤ σ_k ≤ ρ` by `Kakeya.NonSlab.lineAngle_le_pi_div_two_mul_norm_sub`. The upper
bound is the packing bound `Kakeya.AngularCover.card_le_of_ball_of_class_bound` at the *same*
index: by `Kakeya.NonSlab.norm_sub_or_norm_add_le_of_lineAngle_le` the fibre lies in a ball of
radius `ρ` around `v(T₀)` or `-v(T₀)`, so it meets at most `2(1 + 2(ρ + 3σ_k/8)/(σ_k/8))³`
cells, each of size `< 4·2^{Pstar k}`.

**Why this works at every real `ρ` and not only on the grid.** Minimality of `k(ρ)` gives
`ρ ≤ δ^{-2/N} σ_{k(ρ)}`, so the packing factor is `≤ 97336 · δ^{-6/N}`: the *branching* between
consecutive grid indices is paid for by a packing count in the `2`-sphere, with exponent
`3 = dim ℝ³`, rather than being unbounded. Choosing `N = ⌈12/η⌉ + 4` makes `δ^{-6/N} ≤ δ^{-η/2}`
and the absolute constant `97336 = 2·23³·4` is absorbed into the remaining `δ^{-η/2}` below a
threshold depending on `η` alone.

Neither `murhoTwoScale` nor the comparison of `μ(𝕋, Y')` with `μ(1)` is part of this existence
statement. The first mentions `𝕋_ρ`, which is supplied only by the tube hierarchy of
`Kakeya.VeryNotSticky.SplitInputs`; that structure carries not it
but GWZ's composed consequence, the field `angularFibre_le_fibreMult` at the constant `Cang`
(the earlier field `fibreAngularMult` is deleted); the second is not needed downstream. -/
theorem exists_angularMultiplicity {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ cfg : VeryNotSticky, cfg.η = η → cfg.δ ≤ δ₀ →
        ∃ (Y' : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (c C : NNReal) (μ : ℝ → NNReal),
          cfg.δ ^ cfg.η ≤ c ∧ c ≤ 1 ∧ 1 ≤ C ∧ C ≤ cfg.δ ^ (-cfg.η) ∧
            ShadedBody.IsCRefinement cfg.s Y' cfg.s (fun i ↦ (cfg.T i).toShadedBody) c ∧
            cfg.IsAngularMultiplicity Y' C μ := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈12 / η⌉₊ + 4 := ⟨_, rfl⟩
  have hNpos : 0 < N := by omega
  have hN4 : 4 ≤ N := by omega
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hNpos
  have hN12 : 12 / η ≤ (N : ℝ) := by
    refine le_trans (Nat.le_ceil (12 / η)) ?_
    rw [hNdef]; push_cast; linarith
  have h6N : (6:ℝ) / (N:ℝ) ≤ η / 2 := by
    rw [div_le_div_iff₀ hNR (by norm_num : (0:ℝ) < 2)]
    have h12 : (12:ℝ) ≤ (N:ℝ) * η := by
      rw [div_le_iff₀ hη] at hN12; linarith
    linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Kakeya.AngularCover.exists_polylog_threshold_ennreal hη (m := 2 + η) (by linarith)
      (2 * N + 2) (Tube.card_le_of_densityIn_le.C 3)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Kakeya.AngularCover.exists_const_threshold
    (show (0:ℝ) < 97336 by norm_num) (show (0:ℝ) < η / 2 by linarith)
  refine ⟨min (min δ₁ δ₂) (min ((16:NNReal) ^ (-(N:ℝ))) (1/2)), ?_, ?_⟩
  · exact lt_min (lt_min hδ₁pos hδ₂pos) (lt_min (NNReal.rpow_pos (by norm_num)) (by norm_num))
  intro cfg hcfgη hcfgδ
  haveI := cfg.decidableEq
  subst hcfgη
  have hδpos : 0 < cfg.δ := cfg.hδ
  have hδr : (0:ℝ) < (cfg.δ:ℝ) := by exact_mod_cast hδpos
  have hle₁ : cfg.δ ≤ δ₁ := hcfgδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hle₂ : cfg.δ ≤ δ₂ := hcfgδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle₄ : cfg.δ ≤ (16:NNReal) ^ (-(N:ℝ)) :=
    hcfgδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle₅ : cfg.δ ≤ 1/2 := hcfgδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδhalf : (cfg.δ:ℝ) ≤ 1/2 := by exact_mod_cast hle₅
  have hδ1 : cfg.δ ≤ 1 := le_trans hle₅ (by norm_num)
  have hδr1 : (cfg.δ:ℝ) < 1 := by linarith
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- the cardinality bound `|𝕋| ≤ C₃ δ^{-(2+η)}`
  have hne0 : ((cfg.δ : ENNReal)) ≠ 0 := by simpa using hδpos.ne'
  have hnetop : ((cfg.δ : ENNReal)) ≠ ⊤ := ENNReal.coe_ne_top
  have hdens : densityIn cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
    (le_maxDensity _ _ _).trans cfg.maxDensity_le
  have hcard0 := Tube.card_le_of_densityIn_le (s := cfg.s) (δ := cfg.δ)
      (T := fun i ↦ (cfg.T i).toTube) (by exact_mod_cast hδpos.ne')
      (fun i hi ↦ cfg.contained i hi) hdens
  rw [hfr] at hcard0
  have hz : ((cfg.δ : ENNReal)) ^ (-(((3:ℕ):ℤ) - 1)) = (cfg.δ : ENNReal) ^ (-(2:ℝ)) := by
    rw [← ENNReal.rpow_intCast]
    norm_num
  rw [hz] at hcard0
  have hcard : (cfg.s.card : ENNReal)
      ≤ ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : ENNReal)
        * (cfg.δ : ENNReal) ^ (-(2 + cfg.η)) := by
    have hsplit : (cfg.δ : ENNReal) ^ (-(2 + cfg.η))
        = (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ (-(2:ℝ)) := by
      rw [← ENNReal.rpow_add (x := (cfg.δ : ENNReal)) _ _ hne0 hnetop]
      congr 1
      ring
    rw [hsplit, ← mul_assoc]
    exact hcard0
  obtain ⟨clamp, hclampdef⟩ : ∃ c : ℕ, c = Nat.log 2 cfg.s.card := ⟨_, rfl⟩
  have hKref : ((clamp + 1 : ℕ) : NNReal) ^ (2 * N + 2) ≤ cfg.δ ^ (-cfg.η) := by
    rw [hclampdef]
    exact hδ₁ cfg.δ hδpos hle₁ cfg.s.card hcard
  -- the angular hierarchy on the directions of `𝕋`
  obtain ⟨v, hvi⟩ : ∃ v : cfg.ι → EuclideanSpace ℝ (Fin 3), ∀ i, v i = (cfg.T i).direction :=
    ⟨_, fun _ ↦ rfl⟩
  have hv : ∀ i, ‖v i‖ = 1 := fun i ↦ by rw [hvi]; exact (cfg.T i).toTube.norm_direction
  obtain ⟨σ, hσdef⟩ : ∃ σ : NNReal, σ = cfg.δ ^ (2:ℕ) := ⟨_, rfl⟩
  have hσpos : 0 < σ := by rw [hσdef]; exact pow_pos hδpos 2
  have hσ1 : σ ≤ 1 := by rw [hσdef]; exact pow_le_one₀ (by simp) hδ1
  have hσδ : σ ≤ cfg.δ := by
    rw [hσdef]
    calc cfg.δ ^ (2:ℕ) ≤ cfg.δ ^ (1:ℕ) := pow_le_pow_of_le_one (by simp) hδ1 (by norm_num)
      _ = cfg.δ := pow_one _
  have hσN : σ ≤ (16:NNReal) ^ (-(N:ℝ)) := le_trans hσδ hle₄
  obtain ⟨𝒢, hAmem, hAdist, hAsep, hAidx⟩ :=
    Kakeya.AngularCover.exists_angularCover (E := EuclideanSpace ℝ (Fin 3)) cfg.s v hv hσpos
      hσ1 hNpos hσN
  -- the balanced angular refinement of the shading
  obtain ⟨Pstar, V', hVto, hVsub, hband, hsum⟩ :=
    ShadedTube.exists_balanced_shadeRefinement_of_cover (V := cfg.T)
      (W := Kakeya.AngularCover.dirTube σ v hv) (N := N) 𝒢 hNpos clamp
      (fun t ht ↦ by rw [hclampdef]; exact Nat.log_mono_right (Finset.card_le_card ht))
  -- the angular grid, as reals
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = ((Tube.gridScale σ N k : NNReal) : ℝ) :=
    ⟨_, fun _ ↦ rfl⟩
  have hrpos : ∀ k, 0 < r k := fun k ↦ by
    rw [hrdef]; exact_mod_cast (Tube.gridScale_pos hσpos N k)
  have hrval : ∀ k : ℕ, r k = (cfg.δ:ℝ) ^ (2 * (k:ℝ) / (N:ℝ)) := by
    intro k
    rw [hrdef, Tube.gridScale, NNReal.coe_rpow, hσdef]
    push_cast
    rw [← Real.rpow_natCast (cfg.δ:ℝ) 2, ← Real.rpow_mul hδr.le]
    ring_nf
  have hr0 : r 0 = 1 := by rw [hrval]; norm_num
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (cfg.δ:ℝ) ^ (-(2:ℝ)/(N:ℝ)) := ⟨_, rfl⟩
  have hq1 : (1:ℝ) ≤ q := by
    rw [hqdef]
    refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδr hδr1.le ?_
    rw [neg_div]
    simp only [neg_nonpos]
    positivity
  have hrq : ∀ k : ℕ, r k = q * r (k+1) := by
    intro k
    rw [hrval, hrval, hqdef, ← Real.rpow_add hδr]
    congr 1
    push_cast
    field_simp
    ring
  have hrN1 : r (N - 1) ≤ (cfg.δ : ℝ) := by
    rw [hrval]
    have h1N : (1:ℕ) ≤ N := by omega
    have hNc : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
      push_cast [Nat.cast_sub h1N]
      ring
    rw [hNc]
    have hNR4 : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN4
    have hexp : (1:ℝ) ≤ 2 * ((N:ℝ) - 1) / (N:ℝ) := by
      rw [le_div_iff₀ hNR]
      linarith
    calc (cfg.δ:ℝ) ^ (2 * ((N:ℝ) - 1) / (N:ℝ)) ≤ (cfg.δ:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hδr hδr1.le hexp
      _ = (cfg.δ:ℝ) := Real.rpow_one _
  have hAdist' : ∀ k ≤ N, ∀ i ∈ cfg.s, ‖v i - v (𝒢.assign k i)‖ ≤ r k / 4 := by
    intro k hk i hi; rw [hrdef]; exact hAdist k hk i hi
  have hAsep' : ∀ k < N, ∀ a ∈ 𝒢.indexSet k, ∀ b ∈ 𝒢.indexSet k, a ≠ b →
      r k / 8 ≤ ‖v a - v b‖ := by
    intro k hk a ha b hb hab; rw [hrdef]; exact hAsep k hk a ha b hb hab
  have hexk : ∀ ρ : ℝ, ∃ k : ℕ, r k ≤ max ρ (cfg.δ : ℝ) :=
    fun ρ ↦ ⟨N - 1, le_trans hrN1 (le_max_right _ _)⟩
  -- the two constants
  obtain ⟨Cq, hCqdef⟩ : ∃ C : NNReal, C = 97336 * cfg.δ ^ (-(6:ℝ)/(N:ℝ)) := ⟨_, rfl⟩
  obtain ⟨Kref, hKrefdef⟩ : ∃ K : NNReal, K = ((clamp + 1 : ℕ) : NNReal) ^ (2 * N + 2) :=
    ⟨_, rfl⟩
  have hKref1 : (1:NNReal) ≤ Kref := by
    rw [hKrefdef]
    exact one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _))
  have hKrefpos : (0:NNReal) < Kref := lt_of_lt_of_le zero_lt_one hKref1
  have hKref' : Kref ≤ cfg.δ ^ (-cfg.η) := by rw [hKrefdef]; exact hKref
  refine ⟨fun i ↦ (V' i).toShadedBody, Kref⁻¹, max 1 Cq,
    fun ρ ↦ (2:NNReal) ^ (Pstar (Nat.find (hexk ρ))), ?_, ?_, le_max_left _ _, ?_, ?_, ?_⟩
  · -- `δ^η ≤ c`
    calc cfg.δ ^ cfg.η = (cfg.δ ^ (-cfg.η))⁻¹ := by rw [NNReal.rpow_neg, inv_inv]
      _ ≤ Kref⁻¹ := inv_anti₀ hKrefpos hKref'
  · -- `c ≤ 1`
    simpa using inv_anti₀ (zero_lt_one' NNReal) hKref1
  · -- `C ≤ δ^{-η}`
    have h1 : (1:NNReal) ≤ cfg.δ ^ (-cfg.η) :=
      NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos cfg.hδ cfg.hδ1
        (neg_nonpos.mpr (le_of_lt cfg.hη))
    refine max_le h1 ?_
    have hc1 : (97336 : NNReal) ≤ cfg.δ ^ (-(cfg.η/2)) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
      push_cast
      exact hδ₂ cfg.δ hδpos hle₂
    have hc2 : cfg.δ ^ (-(6:ℝ)/(N:ℝ)) ≤ cfg.δ ^ (-(cfg.η/2)) := by
      refine NNReal.rpow_le_rpow_of_exponent_ge hδpos hδ1 ?_
      rw [neg_div]
      linarith
    calc Cq = 97336 * cfg.δ ^ (-(6:ℝ)/(N:ℝ)) := hCqdef
      _ ≤ cfg.δ ^ (-(cfg.η/2)) * cfg.δ ^ (-(cfg.η/2)) := mul_le_mul' hc1 hc2
      _ = cfg.δ ^ (-cfg.η) := by
          rw [← NNReal.rpow_add hδpos.ne']
          congr 1
          ring
  · -- `(𝕋, Y')` is a `c`-refinement of `(𝕋, Y)`
    refine ShadedBody.isCRefinement_of_isRefinement_of_sum_le _ _ _ _
      ⟨Finset.Subset.refl _, fun i _ ↦ ⟨congrArg Tube.toConvexSpaceBody (hVto i), hVsub i⟩⟩ ?_
    refine hsum.trans (le_of_eq ?_)
    rw [hKrefdef]
    push_cast
    ring
  · -- the angular multiplicity function
    intro ρ hδρ hρ1 i₀ hi₀ x hx
    show (((cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x
            (cfg.T i₀).direction ρ).card : ℕ) : NNReal)
          ≤ max 1 Cq * (2:NNReal) ^ (Pstar (Nat.find (hexk ρ))) ∧
        (2:NNReal) ^ (Pstar (Nat.find (hexk ρ)))
          ≤ max 1 Cq * (((cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x
            (cfg.T i₀).direction ρ).card : ℕ) : NNReal)
    have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδr hδρ
    have hmaxρ : max ρ (cfg.δ:ℝ) = ρ := max_eq_left hδρ
    have hlo : r (Nat.find (hexk ρ)) ≤ ρ :=
      (Nat.find_spec (hexk ρ)).trans (le_of_eq hmaxρ)
    have hleN1 : Nat.find (hexk ρ) ≤ N - 1 :=
      Nat.find_le (hrN1.trans (le_max_right _ _))
    have hltN : Nat.find (hexk ρ) < N := by omega
    have hhi : ρ ≤ q * r (Nat.find (hexk ρ)) := by
      rcases Nat.eq_zero_or_pos (Nat.find (hexk ρ)) with h0 | hp
      · rw [h0, hr0, mul_one]; exact hρ1.trans hq1
      · have hstep : Nat.find (hexk ρ) - 1 < Nat.find (hexk ρ) := by omega
        have hmin0 : ¬ (r (Nat.find (hexk ρ) - 1) ≤ max ρ (cfg.δ : ℝ)) :=
          Nat.find_min (hexk ρ) hstep
        have hmin : ρ < r (Nat.find (hexk ρ) - 1) :=
          lt_of_le_of_lt (le_max_left ρ ((cfg.δ : ℝ))) (not_le.mp hmin0)
        have heq : (Nat.find (hexk ρ) - 1) + 1 = Nat.find (hexk ρ) := by omega
        have hstep2 := hrq (Nat.find (hexk ρ) - 1)
        rw [heq] at hstep2
        linarith
    set k₁ : ℕ := Nat.find (hexk ρ) with hk₁def
    clear_value k₁
    have hk₁le : k₁ ≤ N := le_of_lt hltN
    have hrp : (0:ℝ) < r k₁ := hrpos k₁
    have hxU : x ∈ (⋃ i ∈ cfg.s, (V' i).shade) := Set.mem_biUnion hi₀ hx
    have hbandk := hband x hxU k₁ hk₁le
    -- lower bound: the whole angular cell of `T₀` lies in the fibre
    have hclsub : ShadedTube.shadeClass cfg.s V' (𝒢.assign k₁) (𝒢.assign k₁ i₀) x
        ⊆ cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x (cfg.T i₀).direction ρ := by
      intro i hi
      simp only [ShadedTube.shadeClass, Tube.coverClass, Finset.mem_filter] at hi
      obtain ⟨⟨his, hassign⟩, hxi⟩ := hi
      refine Finset.mem_filter.mpr ⟨his, hxi, ?_⟩
      have h1 : ‖v i - v (𝒢.assign k₁ i)‖ ≤ r k₁ / 4 := hAdist' k₁ hk₁le i his
      have h2 : ‖v i₀ - v (𝒢.assign k₁ i₀)‖ ≤ r k₁ / 4 := hAdist' k₁ hk₁le i₀ hi₀
      rw [hassign] at h1
      have h2' : ‖v (𝒢.assign k₁ i₀) - v i₀‖ ≤ r k₁ / 4 := by
        rw [norm_sub_rev]; exact h2
      have h3 : ‖v i - v i₀‖ ≤ r k₁ / 2 := by
        calc ‖v i - v i₀‖
            ≤ ‖v i - v (𝒢.assign k₁ i₀)‖ + ‖v (𝒢.assign k₁ i₀) - v i₀‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ r k₁ / 4 + r k₁ / 4 := add_le_add h1 h2'
          _ = r k₁ / 2 := by ring
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      calc NonSlab.lineAngle (cfg.T i).direction (cfg.T i₀).direction
          = NonSlab.lineAngle (v i) (v i₀) := by rw [hvi, hvi]
        _ ≤ Real.pi / 2 * ‖v i - v i₀‖ :=
            NonSlab.lineAngle_le_pi_div_two_mul_norm_sub (hv i) (hv i₀)
        _ ≤ Real.pi / 2 * (r k₁ / 2) := mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = (Real.pi / 4) * r k₁ := by ring
        _ ≤ r k₁ := mul_le_of_le_one_left hrp.le (by linarith)
        _ ≤ ρ := hlo
    have hlower : 2 ^ Pstar k₁
        ≤ (cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x (cfg.T i₀).direction ρ).card :=
      le_trans (hbandk i₀ hi₀ hx).1 (Finset.card_le_card hclsub)
    -- upper bound: packing at the same grid index
    have hupper : ((cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x
          (cfg.T i₀).direction ρ).card : ℝ) ≤ 97336 * q ^ 3 * ((2:ℝ) ^ Pstar k₁) := by
      have hFmem : ∀ i ∈ cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x
          (cfg.T i₀).direction ρ, i ∈ cfg.s ∧ x ∈ (V' i).shade ∧
          NonSlab.lineAngle (cfg.T i).direction (cfg.T i₀).direction ≤ ρ :=
        fun i hi ↦ Finset.mem_filter.mp hi
      have hB2 : (0:ℝ) < (2:ℝ) ^ Pstar k₁ := pow_pos (by norm_num) _
      have hmain := Kakeya.AngularCover.card_le_of_ball_of_class_bound
        (E := EuclideanSpace ℝ (Fin 3)) v
        (cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x (cfg.T i₀).direction ρ)
        (𝒢.assign k₁)
        (ε := r k₁ / 8) (d := r k₁ / 4) (R := ρ)
        (B := 4 * ((2:ℝ) ^ Pstar k₁)) (by linarith) (by linarith) hρ0.le (by linarith)
        (by
          intro a ha b hb hab
          have hai : a ∈ 𝒢.indexSet k₁ := by
            rw [hAidx]
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
            exact Finset.mem_image_of_mem _ (hFmem i hi).1
          have hbi : b ∈ 𝒢.indexSet k₁ := by
            rw [hAidx]
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
            exact Finset.mem_image_of_mem _ (hFmem i hi).1
          exact hAsep' k₁ hltN a hai b hbi hab)
        (fun i hi ↦ hAdist' k₁ hk₁le i (hFmem i hi).1)
        (w := v i₀)
        (by
          intro i hi
          refine NonSlab.norm_sub_or_norm_add_le_of_lineAngle_le (hv i) (hv i₀) ?_
          have h := (hFmem i hi).2.2
          rwa [hvi, hvi])
        (fun P ↦ ShadedTube.shadeClass cfg.s V' (𝒢.assign k₁) P x)
        (by
          intro i hi
          obtain ⟨his, hxi, -⟩ := hFmem i hi
          simp only [ShadedTube.shadeClass, Tube.coverClass, Finset.mem_filter]
          exact ⟨⟨his, by trivial⟩, hxi⟩)
        (by
          intro i hi
          obtain ⟨his, hxi, -⟩ := hFmem i hi
          have hb := (hbandk i his hxi).2
          have hb' : ((ShadedTube.shadeClass cfg.s V' (𝒢.assign k₁) (𝒢.assign k₁ i) x).card : ℝ)
              ≤ ((4 * 2 ^ Pstar k₁ : ℕ) : ℝ) := by exact_mod_cast hb.le
          refine hb'.trans (le_of_eq ?_)
          push_cast
          ring)
      rw [hfr] at hmain
      exact hmain.trans (Kakeya.AngularCover.murho_packing_arith hρ0 hrp hq1 hhi hB2.le)
    have hCqcoe : ((Cq : NNReal) : ℝ) = 97336 * q ^ 3 := by
      have h3 : q ^ 3 = (cfg.δ:ℝ) ^ (-(6:ℝ)/(N:ℝ)) := by
        rw [hqdef, ← Real.rpow_natCast ((cfg.δ:ℝ) ^ (-(2:ℝ)/(N:ℝ))) 3, ← Real.rpow_mul hδr.le]
        congr 1
        push_cast
        ring
      rw [h3, hCqdef]
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · rw [← NNReal.coe_le_coe]
      push_cast
      refine hupper.trans ?_
      rw [← hCqcoe]
      have hcm : ((Cq:NNReal):ℝ) ≤ max 1 ((Cq:NNReal):ℝ) := le_max_right _ _
      have hB2 : (0:ℝ) ≤ (2:ℝ) ^ Pstar k₁ := (pow_pos (by norm_num : (0:ℝ) < 2) _).le
      exact mul_le_mul_of_nonneg_right hcm hB2
    · have h1 : (2:NNReal) ^ Pstar k₁
          ≤ ((cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x
              (cfg.T i₀).direction ρ).card : NNReal) := by
        exact_mod_cast hlower
      calc (2:NNReal) ^ Pstar k₁
          ≤ ((cfg.angularFibreWith (fun i ↦ (V' i).toShadedBody) x
              (cfg.T i₀).direction ρ).card : NNReal) := h1
        _ = 1 * _ := (one_mul _).symm
        _ ≤ max 1 Cq * _ := by gcongr; exact le_max_left _ _

/-- **Counting the tubes through a point near an arbitrary direction, against `μ`**
(blueprint `lem:ml2angularInnerCount` combined with `defmurho`).

`Kakeya.VeryNotSticky.angularInnerCount` places the fibre at an arbitrary direction `v` inside
the fibre at a *tube* `T₀ ∈ 𝕋` shading `x`, at the doubled angle `2ρ`; the angular
multiplicity function then bounds the latter by `C μ(2ρ)`. The empty case is where the
hypothesis `x ∈ Y(T₀)` of `defmurho` would otherwise be unavailable.

This is the form the compatible refinement of blueprint `lem:ml2nonslabCompat` consumes: the
angle it controls is the angle to the *axis of a factoring body*, not to a tube. -/
theorem angularFibre_card_le_mul_mu (cfg : VeryNotSticky) {C : NNReal} {μ : ℝ → NNReal}
    (ham : cfg.IsAngularMultiplicity (fun i ↦ (cfg.T i).toShadedBody) C μ)
    (x v : EuclideanSpace ℝ (Fin 3)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hδ : (cfg.δ : ℝ) ≤ 2 * ρ) (h1 : 2 * ρ ≤ 1) :
    (((cfg.angularFibre x v ρ).card : ℕ) : NNReal) ≤ C * μ (2 * ρ) := by
  rcases cfg.angularInnerCount x v hρ with h | ⟨i₀, hi₀s, hx, hsub⟩
  · rw [h]
    simp
  · calc
      (((cfg.angularFibre x v ρ).card : ℕ) : NNReal)
          ≤ (((cfg.angularFibre x (cfg.T i₀).direction (2 * ρ)).card : ℕ) : NNReal) := by
            exact_mod_cast (Finset.card_le_card hsub)
      _ ≤ C * μ (2 * ρ) := by
            simpa [cfg.angularFibre_eq_angularFibreWith x (cfg.T i₀).direction (2 * ρ)] using
              (ham (2 * ρ) hδ h1 i₀ hi₀s x hx).1


/-! ### Elementary properties of the angular fibres

The lemmas of this section are the mechanical inputs of blueprint `lem:ml2murho`
(`Kakeya.VeryNotSticky.exists_angularMultiplicity`): monotonicity of the angular fibre in the
angle and in the shading, the trivial bounds `1 ≤ #fibre ≤ |𝕋|` at a base tube, and the dyadic
angular grid over which the pigeonholing of that lemma runs. None of them is the pigeonholing
itself. -/

open scoped Classical in
/-- The angular fibre is a subfamily of `𝕋`. -/
lemma angularFibreWith_subset (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (x v : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) :
    cfg.angularFibreWith Y x v ρ ⊆ cfg.s :=
  Finset.filter_subset _ _

open scoped Classical in
/-- The angular fibre never has more members than `𝕋`. -/
lemma card_angularFibreWith_le (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (x v : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) :
    (cfg.angularFibreWith Y x v ρ).card ≤ cfg.s.card :=
  Finset.card_le_card (cfg.angularFibreWith_subset Y x v ρ)

open scoped Classical in
/-- **Monotonicity in the angle.** The angular fibres of a fixed shading and base point form an
increasing family in `ρ`; this is what makes the class vector of the pigeonholing of
`lem:ml2murho` monotone along the angular grid, and hence what keeps the number of classes
polylogarithmic rather than exponential in the number of scales. -/
lemma angularFibreWith_mono_angle (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (x v : EuclideanSpace ℝ (Fin 3)) {ρ ρ' : ℝ} (h : ρ ≤ ρ') :
    cfg.angularFibreWith Y x v ρ ⊆ cfg.angularFibreWith Y x v ρ' := by
  intro i hi
  obtain ⟨his, hix, hiangle⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨his, hix, hiangle.trans h⟩

open scoped Classical in
/-- **Monotonicity in the shading.** Passing to a refinement of the shading can only shrink the
angular fibres. -/
lemma angularFibreWith_mono_shade (cfg : VeryNotSticky)
    {Y Y' : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (h : ∀ i ∈ cfg.s, (Y i).shade ⊆ (Y' i).shade)
    (x v : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) :
    cfg.angularFibreWith Y x v ρ ⊆ cfg.angularFibreWith Y' x v ρ := by
  intro i hi
  obtain ⟨his, hix, hiangle⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨his, h i his hix, hiangle⟩

open scoped Classical in
/-- **A tube lies in its own angular fibre.** This is what closes the empty-shading escape in
`Kakeya.VeryNotSticky.IsAngularMultiplicity`: at every base tube `T₀ ∈ 𝕋` and every point `x` of
its shade, the fibre is non-empty, so the two-sided comparison there forces `μ ρ ≠ 0`. -/
lemma mem_angularFibreWith_self (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (Y i₀).shade) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    i₀ ∈ cfg.angularFibreWith Y x (cfg.T i₀).direction ρ := by
  refine Finset.mem_filter.mpr ⟨hi₀, hx, ?_⟩
  have hne : ((cfg.T i₀).direction : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    have h1 : ‖((cfg.T i₀).direction : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
      (cfg.T i₀).toTube.norm_direction
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  rw [NonSlab.lineAngle_self hne]
  exact hρ

open scoped Classical in
/-- The angular fibre at a base tube through a shaded point is non-empty. -/
lemma one_le_card_angularFibreWith_self (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (Y i₀).shade) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    1 ≤ (cfg.angularFibreWith Y x (cfg.T i₀).direction ρ).card :=
  Finset.card_pos.mpr ⟨i₀, cfg.mem_angularFibreWith_self Y hi₀ hx hρ⟩

/- The low-cardinality branch of angular multiplicity is elementary: the constant function
`μ(ρ) = #T` works, because every based angular fibre is nonempty and is contained in `T`. -/
theorem exists_isAngularMultiplicity_of_card_le (cfg : VeryNotSticky.{u})
    (hcard : (cfg.s.card : NNReal) ≤ cfg.δ ^ (-cfg.η)) :
    ∃ (C : NNReal) (μ : ℝ → NNReal),
      1 ≤ C ∧ C ≤ cfg.δ ^ (-cfg.η) ∧
        cfg.IsAngularMultiplicity (fun i ↦ (cfg.T i).toShadedBody) C μ := by
  let C : NNReal := max 1 cfg.s.card
  let μ : ℝ → NNReal := fun _ ↦ cfg.s.card
  have hone_pow : (1 : NNReal) ≤ cfg.δ ^ (-cfg.η) := by
    exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos cfg.hδ cfg.hδ1
      (neg_nonpos.mpr (le_of_lt cfg.hη))
  refine ⟨C, μ, le_max_left _ _, max_le hone_pow hcard, ?_⟩
  intro ρ hδρ hρ1 i₀ hi₀ x hx
  have hρ : 0 ≤ ρ := le_trans (by positivity) hδρ
  have hnonempty : 1 ≤ (cfg.angularFibreWith
      (fun i ↦ (cfg.T i).toShadedBody) x (cfg.T i₀).direction ρ).card :=
    cfg.one_le_card_angularFibreWith_self _ hi₀ hx hρ
  have hupper := cfg.card_angularFibreWith_le
    (fun i ↦ (cfg.T i).toShadedBody) x (cfg.T i₀).direction ρ
  constructor
  · change ((cfg.angularFibreWith (fun i ↦ (cfg.T i).toShadedBody) x
        (cfg.T i₀).direction ρ).card : NNReal) ≤ C * cfg.s.card
    calc
      ((cfg.angularFibreWith (fun i ↦ (cfg.T i).toShadedBody) x
          (cfg.T i₀).direction ρ).card : NNReal) ≤ cfg.s.card := by exact_mod_cast hupper
      _ ≤ C * cfg.s.card := by
        simpa [mul_comm] using mul_le_mul_left (show (1 : NNReal) ≤ C from le_max_left _ _) cfg.s.card
  · change (cfg.s.card : NNReal) ≤ C *
      ((cfg.angularFibreWith (fun i ↦ (cfg.T i).toShadedBody) x
        (cfg.T i₀).direction ρ).card : NNReal)
    calc
      (cfg.s.card : NNReal) ≤ C := le_max_right _ _
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * ((cfg.angularFibreWith (fun i ↦ (cfg.T i).toShadedBody) x
          (cfg.T i₀).direction ρ).card : NNReal) := by
        exact mul_le_mul_left' (by exact_mod_cast hnonempty) C


open scoped Classical in
/-- **The angular multiplicity function is non-degenerate.** As soon as one tube of `𝕋` has a
non-empty shade, `1 ≤ C μ(ρ)` at every admissible angle; in particular `μ ρ ≠ 0`. This is the
mechanical form of the remark that `Kakeya.VeryNotSticky.IsAngularMultiplicity` cannot be
satisfied by `μ ≡ 0`. -/
lemma IsAngularMultiplicity.one_le_mul_mu {cfg : VeryNotSticky}
    {Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {C : NNReal} {μ : ℝ → NNReal}
    (h : cfg.IsAngularMultiplicity Y C μ) {ρ : ℝ} (hδ : (cfg.δ : ℝ) ≤ ρ) (h1 : ρ ≤ 1)
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (Y i₀).shade) :
    1 ≤ C * μ ρ := by
  have hρ : (0 : ℝ) ≤ ρ := le_trans (by positivity) hδ
  have hcard : 1 ≤ (cfg.angularFibreWith Y x (cfg.T i₀).direction ρ).card :=
    cfg.one_le_card_angularFibreWith_self Y hi₀ hx hρ
  calc (1 : NNReal) ≤ (((cfg.angularFibreWith Y x (cfg.T i₀).direction ρ).card : ℕ) : NNReal) := by
        exact_mod_cast hcard
    _ ≤ C * μ ρ := (h ρ hδ h1 i₀ hi₀ x hx).1


open scoped Classical in
/-- **The angular multiplicity function is bounded by the size of `𝕋`.** -/
lemma IsAngularMultiplicity.mu_le_mul_card {cfg : VeryNotSticky}
    {Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {C : NNReal} {μ : ℝ → NNReal}
    (h : cfg.IsAngularMultiplicity Y C μ) {ρ : ℝ} (hδ : (cfg.δ : ℝ) ≤ ρ) (h1 : ρ ≤ 1)
    {i₀ : cfg.ι} (hi₀ : i₀ ∈ cfg.s) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (Y i₀).shade) :
    μ ρ ≤ C * (cfg.s.card : NNReal) := by
  refine le_trans (h ρ hδ h1 i₀ hi₀ x hx).2 (mul_le_mul_right ?_ C)
  exact_mod_cast cfg.card_angularFibreWith_le Y x (cfg.T i₀).direction ρ


/-! ### The dyadic angular grid

Blueprint `lem:ml2murho` pigeonholes over the angular scales of `[δ, 1]`. The grid is the
dyadic one, `ρ_m = 2^{-m}` for `m ≤ ⌈log₂(1/δ)⌉`; the two lemmas below say that it has that
many members and that it is `2`-dense in `[δ, 1]`, which is all the pigeonholing uses. -/

/-- The `m`-th dyadic angular scale `ρ_m = 2^{-m}`. -/
noncomputable def angularScale (m : ℕ) : ℝ := ((2 : ℝ) ^ m)⁻¹

lemma angularScale_pos (m : ℕ) : 0 < angularScale m := by
  unfold angularScale; positivity

lemma angularScale_le_one (m : ℕ) : angularScale m ≤ 1 := by
  unfold angularScale
  rw [inv_le_one₀ (by positivity)]
  exact one_le_pow₀ (by norm_num)

lemma angularScale_antitone : Antitone angularScale := by
  intro m n hmn
  unfold angularScale
  have : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hmn
  exact inv_anti₀ (by positivity) this

/-- **The number of dyadic angular scales** covering `[δ, 1]`: `⌈log₂(1/δ)⌉`. Together with the
scale `m = 0` this is the `⌈log₂(1/δ)⌉ + 1` of the blueprint. -/
noncomputable def angularGridLength (cfg : VeryNotSticky) : ℕ :=
  ⌈Real.logb 2 ((cfg.δ : ℝ))⁻¹⌉₊

/-- **The dyadic angular grid is `2`-dense in `[δ, 1]`** (blueprint `lem:ml2murho`, Step 1).

Every admissible angle `ρ ∈ [δ, 1]` lies in exactly one dyadic window
`(2^{-(m+1)}, 2^{-m}]` with `m ≤ ⌈log₂(1/δ)⌉`. Combined with
`Kakeya.VeryNotSticky.angularFibreWith_mono_angle` this replaces the continuum of angles by
`angularGridLength cfg + 1` scales at the cost of a factor `2` in the fibre count. -/
lemma exists_angularScale (cfg : VeryNotSticky) {ρ : ℝ}
    (hδρ : (cfg.δ : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ m ≤ cfg.angularGridLength, angularScale (m + 1) < ρ ∧ ρ ≤ angularScale m := by
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hρpos : 0 < ρ := lt_of_lt_of_le hδpos hδρ
  have hinv1 : (1 : ℝ) ≤ ρ⁻¹ := (one_le_inv₀ hρpos).mpr hρ1
  set L : ℝ := Real.logb 2 ρ⁻¹ with hLdef
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hinv1
  set m : ℕ := ⌊L⌋₊ with hmdef
  have hm_le : (m : ℝ) ≤ L := Nat.floor_le hL0
  have hlt : L < (m : ℝ) + 1 := Nat.lt_floor_add_one L
  have h2L : (2 : ℝ) ^ L = ρ⁻¹ :=
    Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr hρpos)
  have hA : ((2 : ℝ) ^ m) ≤ ρ⁻¹ := by
    rw [← h2L, ← Real.rpow_natCast 2 m]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hm_le
  have hB : ρ⁻¹ < ((2 : ℝ) ^ (m + 1)) := by
    rw [← h2L, ← Real.rpow_natCast 2 (m + 1)]
    refine Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ?_
    push_cast
    exact hlt
  have hmgrid : m ≤ cfg.angularGridLength := by
    have hinvle : ρ⁻¹ ≤ ((cfg.δ : ℝ))⁻¹ := by
      exact inv_anti₀ hδpos hδρ
    have hlogle : L ≤ Real.logb 2 ((cfg.δ : ℝ))⁻¹ :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hinvle
    exact le_trans (Nat.floor_mono hlogle) (Nat.floor_le_ceil _)
  refine ⟨m, hmgrid, ?_, ?_⟩
  · have h := inv_strictAnti₀ (inv_pos.mpr hρpos) hB
    rw [inv_inv] at h
    exact h
  · have h := inv_anti₀ (by positivity : (0:ℝ) < (2:ℝ) ^ m) hA
    rw [inv_inv] at h
    exact h


open scoped Classical in
/-- **The grid sandwich** (blueprint `lem:ml2murho`, Step 1).

Every angular fibre at an admissible angle `ρ ∈ [δ, 1]` is sandwiched between the fibres at the
two neighbouring dyadic grid scales. This is the exact form in which
`Kakeya.VeryNotSticky.exists_angularScale` and
`Kakeya.VeryNotSticky.angularFibreWith_mono_angle` enter the pigeonholing: uniformity of the
counts has to be arranged only at the `angularGridLength cfg + 1` grid scales, and the sandwich
transports it to the continuum of angles — *up to the jump* `#fibre(ρ_m) / #fibre(ρ_{m+1})`
between the two ends, which the comparison constant `C` of
`Kakeya.VeryNotSticky.IsAngularMultiplicity` must absorb. -/
lemma card_angularFibreWith_grid_sandwich (cfg : VeryNotSticky)
    (Y : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (x v : EuclideanSpace ℝ (Fin 3)) {ρ : ℝ} (hδρ : (cfg.δ : ℝ) ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∃ m ≤ cfg.angularGridLength,
      (cfg.angularFibreWith Y x v (angularScale (m + 1))).card
          ≤ (cfg.angularFibreWith Y x v ρ).card ∧
        (cfg.angularFibreWith Y x v ρ).card
          ≤ (cfg.angularFibreWith Y x v (angularScale m)).card := by
  obtain ⟨m, hm, hlt, hle⟩ := cfg.exists_angularScale hδρ hρ1
  exact ⟨m, hm,
    Finset.card_le_card (cfg.angularFibreWith_mono_angle Y x v hlt.le),
    Finset.card_le_card (cfg.angularFibreWith_mono_angle Y x v hle)⟩

end Kakeya.VeryNotSticky
