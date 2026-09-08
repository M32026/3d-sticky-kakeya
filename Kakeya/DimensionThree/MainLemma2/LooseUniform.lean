/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsProduce
public import Kakeya.DimensionThree.MainLemma2.PartitionBrackets

/-!
# The loose hierarchy of Section 9

GWZ Definition 2.1 uses containment up to an absolute dilation
(`gwz.txt` l.163-166, l.181-185). A `Tube.UniformTubeSet` instead
uses exact containment in unit-length node tubes. This module defines
`LooseGridCoverSystem`, `LooseUniformTubeSet`, and
`LooseShadedUniformTubeSet` with the dilated containment needed for
angular counts.

A member lies in the `K`-dilate of its assigned node and its direction
is within `ρ_k/4` of the node's axis. Bounded overlap is tested against
the `(K + 4)`-dilate of an arbitrary `ρ_k`-tube. Assignment classes
remain `Tube.coverClass`, so they partition the family.

## Angular geometry and counting

* `cone_tube_le_dilate` shows that a tube through a point of a loose
  member, at angle at most `2ρ` from it, lies in the `(K + 4)`-dilate
  of that member's node.
* `bush_obstruction` constructs `n` unit `δ`-tubes through one point
  with a common direction. All lie in the `4`-dilate of one `ρ`-tube,
  but no two lie in a common exact `ρ`-tube. Thus the number of exact
  assignment classes met by such a cone is unbounded. This is a
  geometric counterexample; it does not itself construct a
  `VeryNotSticky` configuration satisfying every additional hypothesis.
* `angularCone_card_le_of_loose` proves the composed angular bound
  from a loose shaded hierarchy, with `Cang = C^5`. The shading
  brackets must control the dilated classes: exact-class brackets
  alone introduce the potentially unbounded number of classes met.

`Tube.PartitionBrackets` packages the index sets, assignment, branching
number, and class brackets used by the fibre-counting lemmas. Both
exact and loose hierarchies map to it. The `pbTubeFibre` and
`pbActiveTubeNodes` lemmas state the common counting arguments, and
`SplitInputs` applications retain their respective geometric inputs.

## Relation to the source hypotheses

`boundedOverlapDil` states the bounded-overlap consequence of the
essential distinctness in Definition 2.1(ii), rather than essential
distinctness itself. Likewise, the shaded structure records bracket
consequences of Definition 2.2: it does not supply an entire separate
uniform hierarchy for the family through each point. These weaker
hypotheses suffice for `angularCone_card_le_of_loose`.

The applications `angularFibre_card_le_of_looseUniform` and
`eventually_conjunct6_of_looseUniform` are conditional on a loose
datum. They do not derive that datum from an exact hierarchy.
The example `NonVacuity.wShaded` satisfies the loose hypotheses with
two distinct tubes and nonempty shadings, positive shade volume for
`δ > 0`, nonconstant branching numbers, and nonempty index sets.
This example verifies consistency of the hypotheses for that family;
it is not a construction for arbitrary families.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

namespace LooseUniform

/-- The ambient space of Section 9. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### PA — the through-point containment in a dilate -/

/-- Unpacking `x ∈ dilate V K`: `x` is within `K ρ` of a point `center + s₀ • direction` of the
dilated axis, `|s₀| ≤ K/2`. -/
lemma exists_axis_point_of_mem_dilate {ρ : NNReal} (V : Tube ρ E3) {K : ℝ} (hK : 0 < K)
    {x : E3} (hx : x ∈ (Kakeya.Tube.dilate V K).carrier) :
    ∃ s₀ : ℝ, |s₀| ≤ K / 2 ∧ dist x (V.center + s₀ • V.direction) ≤ K * ρ := by
  rw [Kakeya.Tube.dilate_carrier_eq_cthickening V hK,
    IsClosed.cthickening_eq_biUnion_closedBall isClosed_segment (by positivity)] at hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
  rw [segment_eq_image'] at hp
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := hp
  refine ⟨K * (a - 1 / 2), ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hK]
    have : |a - 1 / 2| ≤ 1 / 2 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    calc K * |a - 1 / 2| ≤ K * (1 / 2) := mul_le_mul_of_nonneg_left this hK.le
      _ = K / 2 := by ring
  · have hcenter : V.center = (1 / 2 : ℝ) • (V.x + V.y) := by
      change midpoint ℝ V.x V.y = _
      rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
    have heq : (AffineMap.homothety V.center K) V.x +
        a • ((AffineMap.homothety V.center K) V.y - (AffineMap.homothety V.center K) V.x) =
        V.center + (K * (a - 1 / 2)) • V.direction := by
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, Tube.direction, hcenter]
      module
    rw [Metric.mem_closedBall] at hxp
    simp only at hxp
    rw [heq] at hxp
    exact hxp

/-- **The through-point containment.** If `x` is within `r` of the axis point
`center + s₀ • dir` of `V` with `|s₀| ≤ K'/2 - 1`, `T` is a `δ`-tube through `x` whose direction
is within `θ` (as a vector, up to sign `σ`) of `V`'s, and `2δ + r + θ ≤ K' ρ`, then
`T ⊆ dilate V K'`. -/
theorem le_dilate_of_through_point {δ ρ : NNReal} (V : Tube ρ E3) {K' r θ : ℝ} (hK' : 0 < K')
    {x : E3} {s₀ : ℝ} (hs₀ : |s₀| ≤ K' / 2 - 1) (hxV : dist x (V.center + s₀ • V.direction) ≤ r)
    (T : Tube δ E3) (hx : x ∈ T.carrier) {σ : ℝ} (hσ : |σ| = 1)
    (hdir : ‖T.direction - σ • V.direction‖ ≤ θ)
    (hrad : 2 * (δ : ℝ) + r + θ ≤ K' * ρ) :
    T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V K' := by
  intro z hz
  change z ∈ T.carrier at hz
  rw [T.carrier_eq] at hz hx
  obtain ⟨m, hm, hzm⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨m₀, hm₀, hxm₀⟩ := Set.mem_iUnion₂.mp hx
  rw [segment_eq_image'] at hm hm₀
  obtain ⟨a, ⟨ha0, ha1⟩, rfl⟩ := hm
  obtain ⟨b, ⟨hb0, hb1⟩, rfl⟩ := hm₀
  rw [Metric.mem_closedBall] at hzm hxm₀
  have hab : |a - b| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hθ0 : 0 ≤ θ := le_trans (norm_nonneg _) hdir
  set s : ℝ := s₀ + (a - b) * σ with hs
  have hsbound : |s| ≤ K' / 2 := by
    calc |s| ≤ |s₀| + |(a - b) * σ| := abs_add_le _ _
      _ = |s₀| + |a - b| := by rw [abs_mul, hσ, mul_one]
      _ ≤ (K' / 2 - 1) + 1 := add_le_add hs₀ hab
      _ = K' / 2 := by ring
  refine Kakeya.Tube.mem_dilate_of_dist_axis_le V hK' hsbound ?_
  have hstep : dist (T.x + a • (T.y - T.x)) ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction)
      ≤ θ := by
    rw [dist_eq_norm]
    have : T.x + a • (T.y - T.x) - (T.x + b • (T.y - T.x) + ((a - b) * σ) • V.direction)
        = (a - b) • (T.direction - σ • V.direction) := by
      simp only [Tube.direction]; module
    rw [this, norm_smul, Real.norm_eq_abs]
    calc |a - b| * ‖T.direction - σ • V.direction‖ ≤ 1 * θ :=
          mul_le_mul hab hdir (norm_nonneg _) zero_le_one
      _ = θ := one_mul θ
  have hshift : dist ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction)
      (V.center + s • V.direction) =
        dist (T.x + b • (T.y - T.x)) (V.center + s₀ • V.direction) := by
    have : V.center + s • V.direction =
        (V.center + s₀ • V.direction) + ((a - b) * σ) • V.direction := by
      rw [hs, add_smul, add_assoc]
    rw [this, dist_add_right]
  calc dist z (V.center + s • V.direction)
      ≤ dist z (T.x + a • (T.y - T.x)) +
          dist (T.x + a • (T.y - T.x)) ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction) +
          dist ((T.x + b • (T.y - T.x)) + ((a - b) * σ) • V.direction)
            (V.center + s • V.direction) :=
        dist_triangle4 _ _ _ _
    _ ≤ δ + θ + (dist (T.x + b • (T.y - T.x)) x + dist x (V.center + s₀ • V.direction)) := by
        rw [hshift]
        gcongr
        exact dist_triangle _ _ _
    _ ≤ δ + θ + (δ + r) := by
        gcongr
        rw [dist_comm]; exact hxm₀
    _ = 2 * (δ : ℝ) + r + θ := by ring
    _ ≤ K' * ρ := hrad

/-- **The cone step for a loose node (container factor `K`, overlap factor `K + 4`).** If
`T₀ ⊆ dilate V K` with direction within `ρ/4` (as vectors, up to sign) of `V`'s axis, `x ∈ T₀`,
and `T` passes through `x` with direction within `2ρ` (as vectors, up to sign) of `T₀`'s, then
`T ⊆ dilate V (K + 4)`, provided `4δ ≤ ρ`.

This is the geometric heart of the loose model: **one** dilated node covers the whole angular
cone at any point of any of its members, with no dependence on how many nodes the cone meets. -/
theorem cone_tube_le_dilate {δ ρ : NNReal} (hδρ : 4 * (δ : ℝ) ≤ ρ) (V : Tube ρ E3)
    {K : ℝ} (hK : 0 < K)
    (T₀ T : Tube δ E3) (h₀ : T₀.toConvexSpaceBody ≤ Kakeya.Tube.dilate V K)
    {σ₀ : ℝ} (hσ₀ : |σ₀| = 1) (hdir₀ : ‖T₀.direction - σ₀ • V.direction‖ ≤ (ρ : ℝ) / 4)
    {x : E3} (hx₀ : x ∈ T₀.carrier) (hx : x ∈ T.carrier)
    {σ : ℝ} (hσ : |σ| = 1) (hdir : ‖T.direction - σ • T₀.direction‖ ≤ 2 * (ρ : ℝ)) :
    T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4) := by
  have hxd : x ∈ (Kakeya.Tube.dilate V K).carrier := h₀ hx₀
  obtain ⟨s₀, hs₀, hxV⟩ := exists_axis_point_of_mem_dilate V hK hxd
  have hρ0 : (0 : ℝ) ≤ ρ := ρ.coe_nonneg
  refine le_dilate_of_through_point V (K' := K + 4) (r := K * ρ) (θ := 2 * ρ + ρ / 4)
    (by linarith) (by linarith [hs₀]) hxV T hx (σ := σ * σ₀)
    (by rw [abs_mul, hσ, hσ₀, mul_one]) ?_ ?_
  · have hsplit : T.direction - (σ * σ₀) • V.direction =
        (T.direction - σ • T₀.direction) + σ • (T₀.direction - σ₀ • V.direction) := by
      module
    rw [hsplit]
    calc ‖(T.direction - σ • T₀.direction) + σ • (T₀.direction - σ₀ • V.direction)‖
        ≤ ‖T.direction - σ • T₀.direction‖ + ‖σ • (T₀.direction - σ₀ • V.direction)‖ :=
          norm_add_le _ _
      _ ≤ 2 * ρ + ρ / 4 := by
          rw [norm_smul, Real.norm_eq_abs, hσ, one_mul]
          exact add_le_add hdir hdir₀
  · nlinarith [hρ0, hK]

/-- The instance `K = 4`, `K' = 8` used by the Section-9 design. -/
theorem cone_tube_le_dilate_eight {δ ρ : NNReal} (hδρ : 4 * (δ : ℝ) ≤ ρ) (V : Tube ρ E3)
    (T₀ T : Tube δ E3) (h₀ : T₀.toConvexSpaceBody ≤ Kakeya.Tube.dilate V 4)
    {σ₀ : ℝ} (hσ₀ : |σ₀| = 1) (hdir₀ : ‖T₀.direction - σ₀ • V.direction‖ ≤ (ρ : ℝ) / 4)
    {x : E3} (hx₀ : x ∈ T₀.carrier) (hx : x ∈ T.carrier)
    {σ : ℝ} (hσ : |σ| = 1) (hdir : ‖T.direction - σ • T₀.direction‖ ≤ 2 * (ρ : ℝ)) :
    T.toConvexSpaceBody ≤ Kakeya.Tube.dilate V 8 := by
  have := cone_tube_le_dilate hδρ V (K := 4) (by norm_num) T₀ T h₀ hσ₀ hdir₀ hx₀ hx hσ hdir
  norm_num at this
  exact this

open InnerProductGeometry in
/-- **Chord ≤ arc, with a sign.** For unit `u, w`, `lineAngle u w ≤ θ` gives `σ = ±1` with
`‖u - σ • w‖ ≤ θ`: this converts the tree's `Kakeya.NonSlab.lineAngle` hypotheses into the
vector form the containment lemmas consume. -/
lemma exists_sign_norm_sub_le_of_lineAngle_le {u w : E3} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {θ : ℝ}
    (h : NonSlab.lineAngle u w ≤ θ) : ∃ σ : ℝ, |σ| = 1 ∧ ‖u - σ • w‖ ≤ θ := by
  have key : ∀ w' : E3, ‖w'‖ = 1 → ‖u - w'‖ ≤ InnerProductGeometry.angle u w' := by
    intro w' hw'
    have hsq :=
      norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle u w'
    rw [hu, hw'] at hsq
    have hcos := Real.one_sub_sq_div_two_le_cos (x := InnerProductGeometry.angle u w')
    have hθ0 := InnerProductGeometry.angle_nonneg u w'
    have hle : ‖u - w'‖ ^ 2 ≤ (InnerProductGeometry.angle u w') ^ 2 := by nlinarith [hsq, hcos]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hθ0 two_ne_zero).mp hle
  rcases le_total (InnerProductGeometry.angle u w) (InnerProductGeometry.angle u (-w)) with h1 | h1
  · refine ⟨1, by simp, ?_⟩
    rw [one_smul]
    have hmin : NonSlab.lineAngle u w = InnerProductGeometry.angle u w := min_eq_left h1
    exact (key w hw).trans (hmin ▸ h)
  · refine ⟨-1, by simp, ?_⟩
    rw [neg_one_smul]
    have hmin : NonSlab.lineAngle u w = InnerProductGeometry.angle u (-w) := min_eq_right h1
    exact (key (-w) (by rw [norm_neg, hw])).trans (hmin ▸ h)

/-! ### PB — the bush: why the exact reading cannot carry the angular clause -/

/-- The bush tube at axial offset `t`: the unit `δ`-tube through `x` with direction `v` whose
core runs from `x + (t - 1/2)v` to `x + (t + 1/2)v`. -/
noncomputable def bushTube (δ : NNReal) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) : Tube δ E3 :=
  Tube.mk' δ (x := x + (t - 1 / 2) • v) (y := x + (t + 1 / 2) • v) (by
    rw [dist_eq_norm, show x + (t - 1 / 2) • v - (x + (t + 1 / 2) • v) = -v by module,
      norm_neg, hv])

lemma bushTube_direction (δ : NNReal) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ x v hv t).direction = v := by
  change (x + (t + 1 / 2) • v) - (x + (t - 1 / 2) • v) = v
  module

lemma x_mem_bushTube (δ : NNReal) (x v : E3) (hv : ‖v‖ = 1) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    x ∈ (bushTube δ x v hv t).carrier := by
  change x ∈ ⋃ z ∈ segment ℝ (x + (t - 1 / 2) • v) (x + (t + 1 / 2) • v), Metric.closedBall z δ
  refine Set.mem_iUnion₂.mpr ⟨x, ?_, Metric.mem_closedBall_self δ.coe_nonneg⟩
  rw [segment_eq_image']
  refine ⟨1 / 2 - t, ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩, ?_⟩
  simp only
  module

/-- Two bush tubes at axial offsets `t < t'` with `t' - t > 2ρ` lie in no common exact
`ρ`-tube. -/
lemma bushTube_not_common {δ ρ : NNReal} (x v : E3) (hv : ‖v‖ = 1) {t t' : ℝ}
    (hlt : 2 * (ρ : ℝ) < t' - t) :
    ¬ ∃ W : Tube ρ E3, (bushTube δ x v hv t).toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
        (bushTube δ x v hv t').toConvexSpaceBody ≤ W.toConvexSpaceBody := by
  rintro ⟨W, hW0, hW1⟩
  have hx0 : (bushTube δ x v hv t).x ∈ W.carrier := hW0 (Tube.x_mem_carrier _)
  have hy1 : (bushTube δ x v hv t').y ∈ W.carrier := hW1 (Tube.y_mem_carrier _)
  have hb0 := Tube.carrier_subset_closedBall_midpoint _ W hx0
  have hb1 := Tube.carrier_subset_closedBall_midpoint _ W hy1
  rw [Metric.mem_closedBall] at hb0 hb1
  have hd : dist (bushTube δ x v hv t).x (bushTube δ x v hv t').y = 1 + (t' - t) := by
    change dist (x + (t - 1 / 2) • v) (x + (t' + 1 / 2) • v) = _
    rw [dist_eq_norm, show x + (t - 1 / 2) • v - (x + (t' + 1 / 2) • v) = -((1 + (t' - t)) • v) by
      module, norm_neg, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have htri := dist_triangle_right (bushTube δ x v hv t).x (bushTube δ x v hv t').y
    (midpoint ℝ W.x W.y)
  linarith

/-- **The bush obstruction.** For `n · sp ≤ 1/2`, `sp > 2ρ`, `4δ ≤ ρ`: there are `n` unit
`δ`-tubes through `x` with the common direction `v`, **pairwise in no common exact `ρ`-tube**
(so every exact-containment hierarchy at scale `ρ` puts them in `n` distinct nodes: two members
of one exact class are both contained in that class's node), all contained in the `4`-dilate of
the single `ρ`-tube `V` around `x` in direction `v`, with directions equal to `V`'s.

The exact per-class brackets therefore say nothing about the dilated class of `V`, which has
`≥ n` members through `x`; and the angular cone at `(x, v)` of radius `≥ 0` contains all `n`.
Taking `sp := 3ρ` and `n := ⌊1/(6ρ)⌋` makes `n` polynomially large in `1/ρ`, which is why no
`Cang ≤ δ^{-η}` can satisfy `Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult` in the
exact model. -/
theorem bush_obstruction {δ ρ : NNReal} (hδρ : 4 * (δ : ℝ) ≤ ρ) (x v : E3) (hv : ‖v‖ = 1)
    (n : ℕ) {sp : ℝ} (hsp : 2 * (ρ : ℝ) < sp) (hn : (n : ℝ) * sp ≤ 1 / 2) :
    ∃ (T : Fin n → Tube δ E3) (V : Tube ρ E3),
      (∀ i, x ∈ (T i).carrier) ∧
      (∀ i, (T i).direction = V.direction) ∧
      (∀ i j, i ≠ j → ¬ ∃ W : Tube ρ E3,
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          (T j).toConvexSpaceBody ≤ W.toConvexSpaceBody) ∧
      (∀ i, (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V 4) := by
  have hsp0 : 0 < sp := lt_of_le_of_lt (by positivity) hsp
  have hρ0 : (0 : ℝ) ≤ ρ := ρ.coe_nonneg
  have hδ0 : (0 : ℝ) ≤ δ := δ.coe_nonneg
  let T : Fin n → Tube δ E3 := fun i => bushTube δ x v hv ((i : ℕ) * sp)
  let V : Tube ρ E3 := bushTube ρ x v hv 0
  have hti : ∀ i : Fin n, |((i : ℕ) : ℝ) * sp| ≤ 1 / 2 := by
    intro i
    rw [abs_of_nonneg (by positivity)]
    calc ((i : ℕ) : ℝ) * sp ≤ (n : ℝ) * sp := by
          gcongr
          exact_mod_cast (le_of_lt i.isLt)
      _ ≤ 1 / 2 := hn
  refine ⟨T, V, fun i => x_mem_bushTube δ x v hv (hti i), fun i => ?_, ?_, ?_⟩
  · simp only [T, V, bushTube_direction]
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have : 2 * (ρ : ℝ) < ((j : ℕ) : ℝ) * sp - ((i : ℕ) : ℝ) * sp := by
        have h1 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
        nlinarith
      exact bushTube_not_common x v hv this
    · have : 2 * (ρ : ℝ) < ((i : ℕ) : ℝ) * sp - ((j : ℕ) : ℝ) * sp := by
        have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
        nlinarith
      intro ⟨W, hWi, hWj⟩
      exact bushTube_not_common x v hv this ⟨W, hWj, hWi⟩
  · intro i
    have hxV : dist x (V.center + (0 : ℝ) • V.direction) ≤ 0 := by
      have hc : V.center = x := by
        change midpoint ℝ (x + ((0 : ℝ) - 1 / 2) • v) (x + ((0 : ℝ) + 1 / 2) • v) = x
        rw [midpoint_eq_smul_add, invOf_eq_inv]
        module
      rw [hc, zero_smul, add_zero, dist_self]
    refine le_dilate_of_through_point V (K' := 4) (r := 0) (θ := 0) (by norm_num)
      (by norm_num) hxV (T i) (x_mem_bushTube δ x v hv (hti i)) (σ := 1) (by simp) ?_ (by linarith)
    simp only [T, V, bushTube_direction, one_smul, sub_self, norm_zero, le_refl]

/-! ### The loose hierarchy: GWZ Def 2.1 and Def 2.2 read up to an `O(1)` dilation -/

section Loose
variable {ι : Type*}

/-- GWZ Definition 2.1(i) in the **loose** model (`gwz.txt` l.177-182 read with l.163-166):
nodes are exact `ρ_k`-tubes, the classes partition `s` (they are the fibres of `assign`), and a
member lies in the `K`-dilate of its node with its direction within `ρ_k/4` of the node's axis.

`Tube.GridCoverSystem.tube_nested` is deliberately dropped: dilates of nested nodes are
not nested at a fixed factor, and no Section-9 consumer reads it. `nested` on the *assignments*
is kept, because a producer's band machinery needs it. -/
structure LooseGridCoverSystem {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E3) (N : ℕ) (K : ℝ) where
  indexSet : ℕ → Finset ι
  assign : ℕ → ι → ι
  tube : (k : ℕ) → ι → Tube (Tube.gridScale δ N k) E3
  assign_mem : ∀ k, k ≤ N → ∀ i ∈ s, assign k i ∈ indexSet k
  le_dilate_tube_assign : ∀ k, k ≤ N → ∀ i ∈ s,
    (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate (tube k (assign k i)) K
  dir_close_tube_assign : ∀ k, k ≤ N → ∀ i ∈ s, ∃ σ : ℝ, |σ| = 1 ∧
    ‖(T i).direction - σ • (tube k (assign k i)).direction‖ ≤ (Tube.gridScale δ N k : ℝ) / 4
  nested : ∀ k, k + 1 ≤ N → ∀ i ∈ s, ∀ j ∈ s,
    assign (k + 1) i = assign (k + 1) j → assign k i = assign k j

/-- GWZ Definition 2.1(ii)-(iii) in the loose model. Bounded overlap is counted against the
`(K+4)`-dilate of an arbitrary `ρ_k`-tube — the container `Kakeya.LooseUniform.cone_tube_le_dilate`
produces — which is what makes it usable for the angular clause; the class brackets are
unchanged. -/
structure LooseUniformTubeSet {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E3) (N : ℕ) (K : ℝ)
    (C : NNReal) where
  cover : LooseGridCoverSystem s T N K
  branchingN : ℕ → NNReal
  tube_injOn : ∀ k ≤ N, Set.InjOn (cover.tube k) (cover.indexSet k : Set ι)
  boundedOverlapDil : ∀ k ≤ N, ∀ V : Tube (Tube.gridScale δ N k) E3,
    (open scoped Classical in
      (cover.indexSet k).filter (fun j => ∃ i ∈ s, cover.assign k i = j ∧
        (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4))).card ≤ C
  card_class_le : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    ((Tube.coverClass s (cover.assign k) j).card : NNReal) ≤ C * branchingN k
  le_card_class : ∀ k ≤ N, ∀ j ∈ cover.indexSet k,
    branchingN k ≤ C * ((Tube.coverClass s (cover.assign k) j).card : NNReal)

/-- GWZ Definition 2.2 in the loose model: the six fields of
`ShadedTube.ShadedUniformTubeSet` over the loose tube hierarchy. The shade classes are
the same `ShadedTube.shadeClass` — classes are classes; only the geometry of what makes
a node a node has moved. -/
structure LooseShadedUniformTubeSet {δ : NNReal} (s : Finset ι) (V : ι → ShadedTube δ E3) (N : ℕ)
    (K : ℝ) (C : NNReal) where
  tubeUniform : LooseUniformTubeSet s (fun i => (V i).toTube) N K C
  branchingN : ℕ → NNReal
  localN : E3 → ℕ → NNReal
  card_shadeClass_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k) (tubeUniform.cover.assign k i) x).card
      : NNReal) ≤ C * localN x k
  le_card_shadeClass : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, ∀ i ∈ s, x ∈ (V i).shade →
    localN x k ≤
      C * ((ShadedTube.shadeClass s V (tubeUniform.cover.assign k)
        (tubeUniform.cover.assign k i) x).card : NNReal)
  branchingN_le : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, branchingN k ≤ C * localN x k
  le_branchingN : ∀ x ∈ (⋃ i ∈ s, (V i).shade), ∀ k ≤ N, localN x k ≤ C * branchingN k

open scoped Classical in
/-- **PC — GWZ l.2321-2322 composed, as a theorem of the loose datum.** At any point `x` and
direction `v`, the tubes shading `x` within angle `ρ ≤ ρ_k` of `v` number at most `C^5` times
the multiplicity of the class of any active level-`k` node. This is the clause the field
`Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult` carries, with `Cang = C^5`.

The proof is: (PA) the whole cone lies in the `(K+4)`-dilate of the node of any one of its
members; (Def 2.1(ii) loose) at most `C` classes have a member in that dilate; (Def 2.2)
each contributes at most `C · localN x k ≤ C² · branchingN k` members at `x`; and (Def 2.2
again) the multiplicity of the chosen class is at least `branchingN k / C²`.

Contrast `Kakeya.LooseUniform.bush_obstruction`: in the exact model step two fails, and no
constant works. -/
theorem angularCone_card_le_of_loose {δ : NNReal} {s : Finset ι} {Y : ι → ShadedTube δ E3}
    {N k : ℕ} {K : ℝ} {C : NNReal} (𝒱 : LooseShadedUniformTubeSet s Y N K C) (hK : 0 < K)
    (hC : 1 ≤ C) (hk : k ≤ N)
    (hδρ : 4 * (δ : ℝ) ≤ (Tube.gridScale δ N k : ℝ))
    {ρ : ℝ} (hρk : ρ ≤ (Tube.gridScale δ N k : ℝ))
    (hvol : ∀ i ∈ s, volume (Y i).shade ≠ 0)
    {j : ι} (hjne : (Tube.coverClass s (𝒱.tubeUniform.cover.assign k) j).Nonempty)
    (x v : E3) :
    ((({i ∈ s | x ∈ (Y i).shade ∧ NonSlab.lineAngle (Y i).direction v ≤ ρ}).card : ℕ) : ENNReal) ≤
      (C : ENNReal) ^ 5 *
        ShadedBody.multiplicity (Tube.coverClass s (𝒱.tubeUniform.cover.assign k) j)
          (fun i => (Y i).toShadedBody) := by
  set G := 𝒱.tubeUniform.cover with hG
  set cone : Finset ι := {i ∈ s | x ∈ (Y i).shade ∧ NonSlab.lineAngle (Y i).direction v ≤ ρ}
    with hcone
  set F := Tube.coverClass s (G.assign k) j with hF
  have hFs : F ⊆ s := fun i hi => (Finset.mem_filter.mp hi).1
  -- (iii): the multiplicity of the active class is at least `branchingN k / C²`
  have hne : volume (⋃ i ∈ F, ((fun i => (Y i).toShadedBody) i).shade) ≠ 0 := by
    obtain ⟨i', hi'⟩ := hjne
    intro h0
    exact hvol i' (hFs hi') (measure_mono_null (Set.subset_iUnion₂ (s := fun i _ =>
      ((fun i => (Y i).toShadedBody) i).shade) i' hi') h0)
  have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hC).ne'
  have hC2 : ((C : ENNReal) ^ 2) ≠ 0 := pow_ne_zero _ hC0
  have hC2top : ((C : ENNReal) ^ 2) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hpt : ∀ y ∈ ⋃ i ∈ F, ((fun i => (Y i).toShadedBody) i).shade,
      (𝒱.branchingN k : ENNReal) / (C : ENNReal) ^ 2 ≤
        (ShadedBody.pointwiseMultiplicity F (fun i => (Y i).toShadedBody) y : ENNReal) := by
    intro y hy
    obtain ⟨i', hi', hyi'⟩ := Set.mem_iUnion₂.mp hy
    have hi's : i' ∈ s := hFs hi'
    have hji' : G.assign k i' = j := (Finset.mem_filter.mp hi').2
    have hyi'' : y ∈ (Y i').shade := hyi'
    have hyU : y ∈ ⋃ i ∈ s, (Y i).shade := Set.mem_iUnion₂.mpr ⟨i', hi's, hyi''⟩
    have h1 := 𝒱.le_card_shadeClass y hyU k hk i' hi's hyi''
    have h2 := 𝒱.branchingN_le y hyU k hk
    rw [hji'] at h1
    have hcard : (ShadedTube.shadeClass s Y (G.assign k) j y).card =
        ShadedBody.pointwiseMultiplicity F (fun i => (Y i).toShadedBody) y := by
      simp only [ShadedTube.shadeClass, ShadedBody.pointwiseMultiplicity, hF]
    have hNN : 𝒱.branchingN k ≤
        C ^ 2 * (ShadedBody.pointwiseMultiplicity F (fun i => (Y i).toShadedBody) y : NNReal) := by
      rw [← hcard]
      calc 𝒱.branchingN k ≤ C * 𝒱.localN y k := h2
        _ ≤ C * (C * ((ShadedTube.shadeClass s Y (G.assign k) j y).card : NNReal)) := by gcongr
        _ = C ^ 2 * ((ShadedTube.shadeClass s Y (G.assign k) j y).card : NNReal) := by ring
    rw [ENNReal.div_le_iff hC2 hC2top, mul_comm]
    exact_mod_cast hNN
  have hmult : (𝒱.branchingN k : ENNReal) ≤
      (C : ENNReal) ^ 2 * ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) := by
    have hlow := ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity F
      (fun i => (Y i).toShadedBody) hne hpt
    calc (𝒱.branchingN k : ENNReal)
        = (C : ENNReal) ^ 2 * ((𝒱.branchingN k : ENNReal) / (C : ENNReal) ^ 2) :=
          (ENNReal.mul_div_cancel hC2 hC2top).symm
      _ ≤ (C : ENNReal) ^ 2 * ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) := by
          gcongr
  -- the cone is empty, or has a member `i₀`
  rcases cone.eq_empty_or_nonempty with hemp | ⟨i₀, hi₀⟩
  · rw [hemp]; simp
  obtain ⟨hi₀s, hxi₀, hang₀⟩ := Finset.mem_filter.mp hi₀
  set j₀ := G.assign k i₀ with hj₀
  set V₀ := G.tube k j₀ with hV₀
  have hxU : x ∈ ⋃ i ∈ s, (Y i).shade := Set.mem_iUnion₂.mpr ⟨i₀, hi₀s, hxi₀⟩
  -- (i): every cone tube lies in the `(K+4)`-dilate of the node of `i₀` (PA)
  have hcont : ∀ i ∈ cone, (Y i).toTube.toConvexSpaceBody ≤ Kakeya.Tube.dilate V₀ (K + 4) := by
    intro i hi
    obtain ⟨his, hxi, hang⟩ := Finset.mem_filter.mp hi
    have h2 : NonSlab.lineAngle (Y i).direction (Y i₀).direction ≤ 2 * ρ := by
      calc NonSlab.lineAngle (Y i).direction (Y i₀).direction
          ≤ NonSlab.lineAngle (Y i).direction v + NonSlab.lineAngle v (Y i₀).direction :=
            NonSlab.lineAngle_le_add _ _ _
        _ ≤ ρ + ρ := add_le_add hang (by rw [NonSlab.lineAngle_comm]; exact hang₀)
        _ = 2 * ρ := by ring
    obtain ⟨σ, hσ, hnorm⟩ := exists_sign_norm_sub_le_of_lineAngle_le
      (Tube.norm_direction (Y i).toTube) (Tube.norm_direction (Y i₀).toTube) h2
    obtain ⟨σ₀, hσ₀, hdir₀⟩ := G.dir_close_tube_assign k hk i₀ hi₀s
    exact cone_tube_le_dilate hδρ V₀ hK (Y i₀).toTube (Y i).toTube
      (G.le_dilate_tube_assign k hk i₀ hi₀s) hσ₀ hdir₀ ((Y i₀).shade_subset hxi₀)
      ((Y i).shade_subset hxi) hσ (hnorm.trans (by linarith))
  -- (ii): the classes met by the cone number at most `C`
  set P' : Finset ι := cone.image (G.assign k) with hP'
  have hP'card : (P'.card : NNReal) ≤ C := by
    have hbo := 𝒱.tubeUniform.boundedOverlapDil k hk V₀
    have hsub : P' ⊆ (G.indexSet k).filter (fun j' => ∃ i ∈ s, G.assign k i = j' ∧
        ((fun i => (Y i).toTube) i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V₀ (K + 4)) := by
      intro j' hj'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
      have his : i ∈ s := (Finset.mem_filter.mp hi).1
      exact Finset.mem_filter.mpr ⟨G.assign_mem k hk i his, i, his, rfl, hcont i hi⟩
    calc (P'.card : NNReal) ≤ _ := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ C := hbo
  have hcov : cone ⊆ P'.biUnion (fun j' => ShadedTube.shadeClass s Y (G.assign k) j' x) := by
    intro i hi
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_biUnion.mpr ⟨G.assign k i, Finset.mem_image_of_mem _ hi, ?_⟩
    have hmem : i ∈ Tube.coverClass s (G.assign k) (G.assign k i) := by
      simp [Tube.coverClass, his]
    simp only [ShadedTube.shadeClass, Finset.mem_filter]
    exact ⟨hmem, hxi⟩
  have hterm : ∀ j' ∈ P',
      ((ShadedTube.shadeClass s Y (G.assign k) j' x).card : NNReal) ≤ C * 𝒱.localN x k := by
    intro j' hj'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨his, hxi, -⟩ := Finset.mem_filter.mp hi
    exact 𝒱.card_shadeClass_le x hxU k hk i his hxi
  have hcardNN : (cone.card : NNReal) ≤ C ^ 3 * 𝒱.branchingN k := by
    calc (cone.card : NNReal)
        ≤ ((P'.biUnion (fun j' => ShadedTube.shadeClass s Y (G.assign k) j' x)).card : NNReal) := by
          exact_mod_cast Finset.card_le_card hcov
      _ ≤ ((∑ j' ∈ P', (ShadedTube.shadeClass s Y (G.assign k) j' x).card : ℕ) : NNReal) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ j' ∈ P', ((ShadedTube.shadeClass s Y (G.assign k) j' x).card : NNReal) := by
          push_cast; rfl
      _ ≤ ∑ _j' ∈ P', C * 𝒱.localN x k := Finset.sum_le_sum hterm
      _ = (P'.card : NNReal) * (C * 𝒱.localN x k) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * (C * 𝒱.localN x k) := by gcongr
      _ ≤ C * (C * (C * 𝒱.branchingN k)) := by gcongr; exact 𝒱.le_branchingN x hxU k hk
      _ = C ^ 3 * 𝒱.branchingN k := by ring
  calc ((cone.card : ℕ) : ENNReal) = ((cone.card : NNReal) : ENNReal) := by norm_cast
    _ ≤ ((C ^ 3 * 𝒱.branchingN k : NNReal) : ENNReal) := by exact_mod_cast hcardNN
    _ = (C : ENNReal) ^ 3 * (𝒱.branchingN k : ENNReal) := by push_cast; rfl
    _ ≤ (C : ENNReal) ^ 3 *
        ((C : ENNReal) ^ 2 * ShadedBody.multiplicity F (fun i => (Y i).toShadedBody)) := by
          gcongr
    _ = (C : ENNReal) ^ 5 * ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) := by ring

end Loose

end LooseUniform


/-! ### `PartitionBrackets`: the hierarchy data used by the Section 9 fibre lemmas

`Tube.PartitionBrackets`, `Tube.UniformTubeSet.toPartitionBrackets` and the
fibre lemmas are in `MainLemma2/PartitionBrackets.lean`, which precedes the
consumers `Kakeya.VeryNotSticky.SplitInputs` and
`Kakeya.VeryNotSticky.TangentialInputs` in the import graph.
`Kakeya.LooseUniform.LooseUniformTubeSet.toPartitionBrackets` depends on the
loose structure defined here. -/

end Kakeya


namespace Kakeya

namespace LooseUniform

variable {ι : Type*}

/-- The loose hierarchy of GWZ Def 2.1, forgetting its geometry. The two brackets are the same
fields; only the geometry of "is a node of" differs, and the fibre lemmas do not read it. -/
def LooseUniformTubeSet.toPartitionBrackets {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E3}
    {N : ℕ} {K : ℝ} {C : NNReal} (𝒰 : LooseUniformTubeSet s T N K C) :
    Tube.PartitionBrackets s N C where
  indexSet := 𝒰.cover.indexSet
  assign := 𝒰.cover.assign
  branchingN := 𝒰.branchingN
  assign_mem := 𝒰.cover.assign_mem
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

@[simp] lemma LooseUniformTubeSet.toPartitionBrackets_indexSet {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} {K : ℝ} {C : NNReal} (𝒰 : LooseUniformTubeSet s T N K C) :
    𝒰.toPartitionBrackets.indexSet = 𝒰.cover.indexSet := rfl

@[simp] lemma LooseUniformTubeSet.toPartitionBrackets_assign {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} {K : ℝ} {C : NNReal} (𝒰 : LooseUniformTubeSet s T N K C) :
    𝒰.toPartitionBrackets.assign = 𝒰.cover.assign := rfl

@[simp] lemma LooseUniformTubeSet.toPartitionBrackets_branchingN {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E3} {N : ℕ} {K : ℝ} {C : NNReal} (𝒰 : LooseUniformTubeSet s T N K C) :
    𝒰.toPartitionBrackets.branchingN = 𝒰.branchingN := rfl

end LooseUniform

/-! ### The angular clause and the fibre lemmas over `PartitionBrackets`

The seven fibre lemmas are in `MainLemma2/PartitionBrackets.lean`; what follows is the part
that mentions `Kakeya.LooseUniform.LooseShadedUniformTubeSet` and therefore stays here. -/

namespace VeryNotSticky

open MeasureTheory Metric Set ShadedBody Filter Topology

universe u


/-! ### The angular clause on a configuration: `angularFibre_le_fibreMult` from the loose datum

This is where the model change pays for itself. The field
`Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult` is
`Kakeya.LooseUniform.angularCone_card_le_of_loose` instantiated at `Y := cfg.T`,
`ρ := ρ₂*`, with `Cang := C^5`; the three side conditions come from the configuration
(`4δ ≤ ρ_k` from `Kakeya.VeryNotSticky.four_mul_delta_le_rho2Star` and the level pin,
`ρ₂* ≤ ρ_k` is the level pin itself, and the positivity of the shades from `shading_lb`).
In the exact model no such theorem exists — `Kakeya.LooseUniform.bush_obstruction`. -/

/-- `δ ≤ ρ₂`. This is the first of the three steps of
`Kakeya.VeryNotSticky.rho2Star_range`, isolated: the other two need the fixed-scale thresholds
`hscale`/`hnotslab`, which the angular clause does not. -/
lemma delta_le_rho2 (cfg : VeryNotSticky) : cfg.δ ≤ cfg.rho2 := by
  have hr₁0 : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hδb : cfg.δ * cfg.r₁ ≤ cfg.b := by
    calc cfg.δ * cfg.r₁ ≤ cfg.δ * 1 :=
          mul_le_mul_right (NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le) cfg.δ
      _ = cfg.δ := mul_one _
      _ ≤ cfg.b := cfg.hdims.1.trans cfg.hdims.2.1
  exact (le_div_iff₀ hr₁0).2 hδb

/-- **`4δ ≤ ρ₂*`**, the single geometric side condition of
`Kakeya.LooseUniform.cone_tube_le_dilate` at the split level. It has plenty of slack:
`ρ₂* = 2 · 2⁶ · C₀⁴ · ρ₂ ≥ 128 δ` for `1 ≤ C₀`, by `Kakeya.VeryNotSticky.delta_le_rho2` and
`Kakeya.NonSlab.bodyAngleConstant C₀ = 2⁶ C₀⁴`. -/
lemma four_mul_delta_le_rho2Star (cfg : VeryNotSticky) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    4 * (cfg.δ : ℝ) ≤ (cfg.rho2Star C₀ : ℝ) := by
  have hδρ2 : (cfg.δ : ℝ) ≤ (cfg.rho2 : ℝ) := by exact_mod_cast cfg.delta_le_rho2
  have hC : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC4 : (1 : ℝ) ≤ (C₀ : ℝ) ^ 4 := one_le_pow₀ hC
  have hδ0 : (0 : ℝ) ≤ (cfg.δ : ℝ) := cfg.δ.coe_nonneg
  have hρ0 : (0 : ℝ) ≤ (cfg.rho2 : ℝ) := cfg.rho2.coe_nonneg
  have heq : (cfg.rho2Star C₀ : ℝ) = 2 * (2 ^ 6 * (C₀ : ℝ) ^ 4) * (cfg.rho2 : ℝ) := by
    simp only [VeryNotSticky.rho2Star, NonSlab.bodyAngleConstant, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_ofNat]
  rw [heq]
  nlinarith [hδρ2, hC4, hδ0, hρ0]

/-- Every shade of the configuration has nonzero volume: `shading_lb` bounds it below by
`Cd⁻¹ · lam · |T|`, and each of the three factors is nonzero (`hCd`, `lam_ge` with `hδ`,
`Tube.le_volume` with `hδ`). This is `hvol` of
`Kakeya.LooseUniform.angularCone_card_le_of_loose`. -/
lemma volume_shade_ne_zero (cfg : VeryNotSticky) {i : cfg.ι} (hi : i ∈ cfg.s) :
    volume (cfg.T i).shade ≠ 0 := by
  have hcar : volume (cfg.T i).toShadedBody.carrier ≠ 0 := by
    set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn
    have hLpos : (Tube.le_volume.c n : ENNReal) * (cfg.δ : ENNReal) ^ (n - 1) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
        (pow_ne_zero _ (by exact_mod_cast cfg.hδ.ne'))
    exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr hLpos) (Tube.le_volume (cfg.T i).toTube)).ne'
  have hlam : cfg.lam ≠ 0 := by
    have hCd0 : 0 < cfg.Cd := lt_of_lt_of_le zero_lt_one cfg.hCd
    have hδη : 0 < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos cfg.hδ
    exact (lt_of_lt_of_le (mul_pos hCd0 hδη) cfg.lam_ge).ne'
  have hpos : ((cfg.Cd : ENNReal))⁻¹ *
      ((cfg.lam : ENNReal) * volume (cfg.T i).toShadedBody.carrier) ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top)
      (mul_ne_zero (by exact_mod_cast hlam) hcar)
  intro h0
  exact hpos (le_antisymm (by simpa [h0] using cfg.shading_lb i hi) bot_le)

open scoped Classical in
/-- **F-R18-3: the field `angularFibre_le_fibreMult` is a theorem of the loose datum.**

At every point `x`, every direction `v` and every active level-`k` node `j` of a loose
Definition 2.2 datum for `(𝕋, Y)`, the tubes of `𝕋_Y(x)` within angle `ρ₂*` of `v` number at
most `C^5` times the multiplicity of the class of `j`. The level is pinned only from below,
`ρ₂* ≤ ρ_k`, exactly as `Kakeya.VeryNotSticky.SplitInputs.gridScale_ge` pins it.

This is `Kakeya.LooseUniform.angularCone_card_le_of_loose` (PC) read at the configuration.
Its exact-model counterpart is false: `Kakeya.LooseUniform.bush_obstruction`. -/
theorem angularFibre_card_le_of_looseUniform (cfg : VeryNotSticky.{u}) {C₀ : NNReal}
    (hC₀ : 1 ≤ C₀) {N : ℕ} {K : ℝ} {C : NNReal}
    (𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T N K C)
    (hK : 0 < K) (hC : 1 ≤ C) {k : ℕ} (hk : k ≤ N)
    (hge : cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ N k)
    {j : cfg.ι} (hj : j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    (((cfg.angularFibre x v (cfg.rho2Star C₀ : ℝ)).card : ℕ) : ENNReal) ≤
      (C : ENNReal) ^ 5 *
        ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
          (fun i ↦ (cfg.T i).toShadedBody) := by
  have hgeR : (cfg.rho2Star C₀ : ℝ) ≤ (Tube.gridScale cfg.δ N k : ℝ) := by exact_mod_cast hge
  have h4 : 4 * (cfg.δ : ℝ) ≤ (Tube.gridScale cfg.δ N k : ℝ) :=
    le_trans (cfg.four_mul_delta_le_rho2Star hC₀) hgeR
  have hjne : (Tube.coverClass cfg.s (𝒱.tubeUniform.cover.assign k) j).Nonempty :=
    (Finset.mem_filter.mp hj).2
  exact LooseUniform.angularCone_card_le_of_loose 𝒱 hK hC hk h4 hgeR
    (fun i hi ↦ cfg.volume_shade_ne_zero hi) hjne x v

open scoped Classical in
/-- **GWZ Definition 2.1(i)'s containment is a `⪅`-containment**, not an exact one
(`gwz.txt` l.152-153): a member of `𝕋[T_ρ]` lies in a **bounded dilate** of its parent, and the
standard uniformiser produces `T ⊆ C · T_ρ` — that is what `Kakeya.Tube.tubeOverlapCoreClose`
says, at `C 3 ≈ 101`, not at `1`. This is that bound, named once, `δ`-free, `cfg`-free, and with
its **own** symbol: it is a different use of the convention from `edDilateConstant`'s, from
`bd.C₀`'s and from `Cpar`'s, so it is kept separate. The loose statements use the value `4`, and `Kakeya.LooseUniform.angularCone_card_le_of_loose` needs only `0 < K` of it. -/
noncomputable def edCoverDilateConstant : ℝ := 4

/-- `edCoverDilateConstant` is positive — the only property the loose cone count reads. -/
theorem edCoverDilateConstant_pos : 0 < edCoverDilateConstant := by
  rw [edCoverDilateConstant]; norm_num

/-- **Conjunct 6 of `Kakeya.VeryNotSticky.SideDataObligations`, proved CONDITIONALLY on a loose
datum, at the configuration's own constant.** Nothing in this tree produces that datum, so this
**discharges nothing** and conjunct 6 stays OPEN; see the closing note of the module docstring.

`Cang := C₀^5`, and the threshold `C₀^5 ≤ δ^{-η}` is
`Kakeya.VeryNotSticky.coe_C₀_pow_eight_le_rpow_neg_eta` with two powers to spare. Only the
lower level pin `ρ₂* ≤ ρ_k` is used; the upper pin `ρ_k ≤ δ^{-η} ρ₂*` is not needed.

Nothing here is an `∀ᶠ δ`: the statement holds at **every** `δ`, for every configuration
carrying the loose datum. `Kakeya.VeryNotSticky.eventually_conjunct6_of_looseUniform` is the
`∀ᶠ`-shaped restatement, for comparison with the existing conjunct. -/
theorem exists_Cang_angularFibre_le_of_looseUniform (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
      edCoverDilateConstant cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k) :
    ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
      ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
        ∀ x v : EuclideanSpace ℝ (Fin 3),
          (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
            (Cang : ENNReal) *
              ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                (fun i ↦ (cfg.T i).toShadedBody) := by
  refine ⟨cfg.C₀ ^ 5, ?_, ?_⟩
  · have h1 : (1 : ENNReal) ≤ (cfg.C₀ : ENNReal) := by exact_mod_cast cfg.hC₀
    calc ((cfg.C₀ ^ 5 : NNReal) : ENNReal) = (cfg.C₀ : ENNReal) ^ 5 := by push_cast; ring
      _ ≤ (cfg.C₀ : ENNReal) ^ 8 := pow_le_pow_right₀ h1 (by norm_num)
      _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) := cfg.coe_C₀_pow_eight_le_rpow_neg_eta
  · intro j hj x v
    have h := cfg.angularFibre_card_le_of_looseUniform bd.hC₀ 𝒱 edCoverDilateConstant_pos
      cfg.hC₀ hk hge hj x v
    calc (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal)
        ≤ (cfg.C₀ : ENNReal) ^ 5 *
            ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
              (fun i ↦ (cfg.T i).toShadedBody) := h
      _ = ((cfg.C₀ ^ 5 : NNReal) : ENNReal) *
            ShadedBody.multiplicity (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
              (fun i ↦ (cfg.T i).toShadedBody) := by push_cast; ring

open scoped Classical in
/-- **Conjunct 6 in the shape `Kakeya.VeryNotSticky.SideDataObligations` states it**, with the
two changes the loose model forces: the hierarchy is a `∀` binder
`Kakeya.LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
`Kakeya.VeryNotSticky.edCoverDilateConstant` `cfg.C₀`
in place of `cfg.splitHierarchy`, and the fibre/active-node vocabulary is read off
`Tube.PartitionBrackets`. Compare the existing conjunct: it is the same text with
`cfg.activeTubeNodes cfg.splitHierarchy k` / `cfg.tubeFibre cfg.splitHierarchy k j` in place of
these two, and no `𝒱` binder. -/
theorem eventually_conjunct6_of_looseUniform {exscal ϱ η : ℝ} (C₀bd : NNReal) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = d → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ 𝒱 : LooseUniform.LooseShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ)
          edCoverDilateConstant cfg.C₀,
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Cang : NNReal, (Cang : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) ∧
          ∀ j ∈ cfg.pbActiveTubeNodes 𝒱.tubeUniform.toPartitionBrackets k,
            ∀ x v : EuclideanSpace ℝ (Fin 3),
              (((cfg.angularFibre x v (cfg.rho2Star bd.C₀ : ℝ)).card : ℕ) : ENNReal) ≤
                (Cang : ENNReal) *
                  ShadedBody.multiplicity
                    (cfg.pbTubeFibre 𝒱.tubeUniform.toPartitionBrackets k j)
                    (fun i ↦ (cfg.T i).toShadedBody) :=
  Filter.Eventually.of_forall fun _ cfg bd _ _ _ _ _ _ 𝒱 _ hk hge _ ↦
    cfg.exists_Cang_angularFibre_le_of_looseUniform bd 𝒱 hk hge

end VeryNotSticky

end Kakeya

namespace Kakeya

namespace LooseUniform

/-! ### Non-vacuity of the loose datum: an explicit two-member witness

Everything above is a *conditional* fact about a hypothesis type. This section discharges the
one thing a `∀`-binder over an uninhabited type cannot be trusted without: it exhibits a
compiled inhabitant of `Kakeya.LooseUniform.LooseShadedUniformTubeSet` on a family of
**two** members with **non-constant branching**, and proves the cardinality.
-/

namespace NonVacuity

/-! #### The ambient unit vector -/

/-- The first coordinate direction of `E3`. -/
noncomputable def e₁ : E3 := EuclideanSpace.single 0 1

lemma norm_e₁ : ‖e₁‖ = 1 := by
  simp [e₁]

lemma e₁_ne_zero : e₁ ≠ 0 := fun h => by simpa [h] using norm_e₁

/-! #### Elementary facts about `Kakeya.LooseUniform.bushTube` -/

lemma bushTube_center (δ : NNReal) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ x v hv t).center = x + t • v := by
  change midpoint ℝ (x + (t - 1 / 2) • v) (x + (t + 1 / 2) • v) = x + t • v
  rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
  module

lemma bushTube_x_eq (δ : NNReal) (x v : E3) (hv : ‖v‖ = 1) (t : ℝ) :
    (bushTube δ x v hv t).x = x + (t - 1 / 2) • v := rfl

lemma mem_segment_bushTube (δ : NNReal) (x v : E3) (hv : ‖v‖ = 1) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    x ∈ segment ℝ (bushTube δ x v hv t).x (bushTube δ x v hv t).y := by
  rw [segment_eq_image']
  refine ⟨1 / 2 - t, ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩, ?_⟩
  change (x + (t - 1 / 2) • v) + (1 / 2 - t) • ((x + (t + 1 / 2) • v) - (x + (t - 1 / 2) • v)) = x
  module

/-- Distinct axial offsets give distinct bush tubes. -/
lemma bushTube_offset_injective {ρ : NNReal} {t t' : ℝ}
    (h : bushTube ρ 0 e₁ norm_e₁ t = bushTube ρ 0 e₁ norm_e₁ t') : t = t' := by
  have hx : (bushTube ρ 0 e₁ norm_e₁ t).x = (bushTube ρ 0 e₁ norm_e₁ t').x := by rw [h]
  rw [bushTube_x_eq, bushTube_x_eq, zero_add, zero_add] at hx
  have hz : (t - t') • e₁ = 0 := by
    rw [show t - t' = (t - 1 / 2) - (t' - 1 / 2) by ring, sub_smul, hx, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h1
  · linarith
  · exact absurd h1 e₁_ne_zero

/-- **Containment in the `4`-dilate of a coarser bush tube through the same point.** Both tubes
run through the origin in the direction `e₁`; the member's offset `t` keeps the origin on its
core, and the node's offset `t'` is small enough that the origin sits on the node's dilated
core. This is the only geometry the witness needs. -/
lemma bushTube_le_dilate_bushTube {δ ρ : NNReal} {t t' : ℝ}
    (ht : |t| ≤ 1 / 2) (ht' : |t'| ≤ 1) (hrad : 2 * (δ : ℝ) ≤ 4 * (ρ : ℝ)) :
    (bushTube δ 0 e₁ norm_e₁ t).toConvexSpaceBody ≤
      Kakeya.Tube.dilate (bushTube ρ 0 e₁ norm_e₁ t') 4 := by
  refine le_dilate_of_through_point (bushTube ρ 0 e₁ norm_e₁ t') (K' := 4) (r := 0) (θ := 0)
    (by norm_num) (s₀ := -t') (by rw [abs_neg]; linarith) ?_
    (bushTube δ 0 e₁ norm_e₁ t) (x_mem_bushTube δ 0 e₁ norm_e₁ ht) (σ := 1) (by norm_num)
    ?_ (by linarith)
  · rw [bushTube_center, bushTube_direction]
    rw [show (0 : E3) + t' • e₁ + (-t') • e₁ = 0 by module, dist_self]
  · rw [bushTube_direction, bushTube_direction, one_smul, sub_self, norm_zero]

/-! #### The two-member family -/

/-- The two axial offsets: `0` and `1/4`. -/
noncomputable def off (i : Fin 2) : ℝ := (i : ℝ) / 4

lemma off_abs_le (i : Fin 2) : |off i| ≤ 1 / 2 := by fin_cases i <;> norm_num [off]

lemma off_injective : Function.Injective off := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [off]

/-- **The witness family.** Two unit `δ`-tubes through the origin in the direction `e₁`, at
axial offsets `0` and `1/4` — so they are distinct tubes — each shaded by the ball
`closedBall 0 δ` around their common point. -/
noncomputable def wV (δ : NNReal) (i : Fin 2) : ShadedTube δ E3 where
  toTube := bushTube δ 0 e₁ norm_e₁ (off i)
  shade := Metric.closedBall 0 (δ : ℝ)
  measurableSet_shade := measurableSet_closedBall
  shade_subset :=
    (bushTube δ 0 e₁ norm_e₁ (off i)).closedBall_subset_carrier_of_mem_segment
      (mem_segment_bushTube δ 0 e₁ norm_e₁ (off_abs_le i))

@[simp] lemma wV_toTube (δ : NNReal) (i : Fin 2) :
    (wV δ i).toTube = bushTube δ 0 e₁ norm_e₁ (off i) := rfl

@[simp] lemma wV_shade (δ : NNReal) (i : Fin 2) :
    (wV δ i).shade = Metric.closedBall 0 (δ : ℝ) := rfl

/-- The two members are distinct tubes. -/
lemma wV_toTube_ne (δ : NNReal) : (wV δ 0).toTube ≠ (wV δ 1).toTube := by
  intro h
  have := off_injective (bushTube_offset_injective (by simpa using h))
  simp at this

/-- The index sets: one node at the coarse level `k = 0`, two nodes at the fine level `k = 1`. -/
def wIndex (k : ℕ) : Finset (Fin 2) := if k = 0 then {0} else Finset.univ

lemma card_wIndex_le_two (k : ℕ) : (wIndex k).card ≤ 2 := by
  unfold wIndex; split <;> simp

/-- The assignment: both members share the single coarse node; each is its own fine node. -/
def wAssign (k : ℕ) (i : Fin 2) : Fin 2 := if k = 0 then 0 else i

/-- The nodes: bush tubes of the grid radius `ρ_k`, through the origin in the direction `e₁`,
at offset `0` at the coarse level and at the member's own offset at the fine level. -/
noncomputable def wNode (δ : NNReal) (k : ℕ) (i : Fin 2) : Tube (Tube.gridScale δ 1 k) E3 :=
  bushTube (Tube.gridScale δ 1 k) 0 e₁ norm_e₁ (if k = 0 then 0 else off i)

/-- The branching numbers: `2` at the coarse level, `1` at the fine level. **Non-constant** —
this is what distinguishes the witness from a one-node or one-member degeneracy. -/
def wBranch (k : ℕ) : NNReal := if k = 0 then 2 else 1

lemma one_le_wBranch (k : ℕ) : 1 ≤ wBranch k := by unfold wBranch; split <;> norm_num

lemma wBranch_le_two (k : ℕ) : wBranch k ≤ 2 := by unfold wBranch; split <;> norm_num

lemma wBranch_zero_ne_wBranch_one : wBranch 0 ≠ wBranch 1 := by
  unfold wBranch; norm_num

/-! #### The class brackets -/

lemma mem_coverClass_self (k : ℕ) (i : Fin 2) :
    i ∈ Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) (wAssign k i) := by
  classical
  simp [Tube.coverClass]

lemma one_le_card_coverClass {k : ℕ} (hk : k ≤ 1) {j : Fin 2} (hj : j ∈ wIndex k) :
    1 ≤ (Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card := by
  refine Finset.card_pos.mpr ⟨j, ?_⟩
  have hjj : wAssign k j = j := by
    interval_cases k
    · have hj0 : j = 0 := by simpa [wIndex] using hj
      simp [wAssign, hj0]
    · simp [wAssign]
  simpa [hjj] using mem_coverClass_self k j

lemma card_finset_fin_two (t : Finset (Fin 2)) : t.card ≤ 2 := by
  simpa using Finset.card_le_univ t

lemma card_finset_fin_two_nnreal (t : Finset (Fin 2)) : (t.card : NNReal) ≤ 2 := by
  exact_mod_cast card_finset_fin_two t

lemma card_coverClass_le_two (k : ℕ) (j : Fin 2) :
    (Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card ≤ 2 :=
  card_finset_fin_two _

lemma two_le_two_mul_wBranch (k : ℕ) : (2 : NNReal) ≤ 2 * wBranch k :=
  le_mul_of_one_le_right (by norm_num) (one_le_wBranch k)

lemma shadeClass_eq_coverClass (δ : NNReal) (asg : Fin 2 → Fin 2) (j : Fin 2) {x : E3}
    (hx : x ∈ Metric.closedBall (0 : E3) (δ : ℝ)) :
    ShadedTube.shadeClass (Finset.univ : Finset (Fin 2)) (wV δ) asg j x
      = Tube.coverClass (Finset.univ : Finset (Fin 2)) asg j := by
  classical
  simp only [ShadedTube.shadeClass]
  exact Finset.filter_true_of_mem (fun i _ => by simpa using hx)

/-! #### The three loose structures, inhabited -/

/-- GWZ Definition 2.1(i) in the loose model, on the witness family. -/
noncomputable def wCover (δ : NNReal) (hδ : δ ≤ 1) :
    LooseGridCoverSystem (Finset.univ : Finset (Fin 2)) (fun i => (wV δ i).toTube) 1 4 where
  indexSet := wIndex
  assign := wAssign
  tube := wNode δ
  assign_mem := by
    intro k hk i _
    interval_cases k <;> simp [wIndex, wAssign]
  le_dilate_tube_assign := by
    intro k hk i _
    have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
    have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
    interval_cases k
    · have hnode : wNode δ 0 (wAssign 0 i) = bushTube (Tube.gridScale δ 1 0) 0 e₁ norm_e₁ 0 := by
        simp [wNode]
      rw [wV_toTube, hnode]
      refine bushTube_le_dilate_bushTube (off_abs_le i) (by norm_num) ?_
      rw [Tube.gridScale_zero]
      push_cast
      linarith
    · have hnode : wNode δ 1 (wAssign 1 i)
          = bushTube (Tube.gridScale δ 1 1) 0 e₁ norm_e₁ (off i) := by
        simp [wNode, wAssign]
      rw [wV_toTube, hnode]
      refine bushTube_le_dilate_bushTube (off_abs_le i) (by
        have := off_abs_le i; linarith) ?_
      rw [Tube.gridScale_self δ Nat.one_pos]
      linarith
  dir_close_tube_assign := by
    intro k hk i _
    refine ⟨1, by norm_num, ?_⟩
    have h1 : ((wV δ i).toTube).direction = e₁ := bushTube_direction δ 0 e₁ norm_e₁ (off i)
    have h2 : (wNode δ k (wAssign k i)).direction = e₁ :=
      bushTube_direction (Tube.gridScale δ 1 k) 0 e₁ norm_e₁ _
    rw [h1, h2, one_smul, sub_self, norm_zero]
    positivity
  nested := by
    intro k hk i _ j _ _
    have hk0 : k = 0 := by omega
    subst hk0
    simp [wAssign]

@[simp] lemma wCover_indexSet (δ : NNReal) (hδ : δ ≤ 1) : (wCover δ hδ).indexSet = wIndex := rfl
@[simp] lemma wCover_assign (δ : NNReal) (hδ : δ ≤ 1) : (wCover δ hδ).assign = wAssign := rfl
@[simp] lemma wCover_tube (δ : NNReal) (hδ : δ ≤ 1) : (wCover δ hδ).tube = wNode δ := rfl

/-- GWZ Definition 2.1(ii)-(iii) in the loose model, on the witness family, at `K = 4`,
`C = 2`, `N = 1`. -/
noncomputable def wUniform (δ : NNReal) (hδ : δ ≤ 1) :
    LooseUniformTubeSet (Finset.univ : Finset (Fin 2)) (fun i => (wV δ i).toTube) 1 4 2 where
  cover := wCover δ hδ
  branchingN := wBranch
  tube_injOn := by
    intro k hk
    interval_cases k
    · intro a ha b hb _
      have ha0 : a = 0 := by simpa [wIndex] using ha
      have hb0 : b = 0 := by simpa [wIndex] using hb
      rw [ha0, hb0]
    · intro a _ b _ hab
      simp only [wCover_tube] at hab
      have h1 : wNode δ 1 a = bushTube (Tube.gridScale δ 1 1) 0 e₁ norm_e₁ (off a) := by
        simp [wNode]
      have h2 : wNode δ 1 b = bushTube (Tube.gridScale δ 1 1) 0 e₁ norm_e₁ (off b) := by
        simp [wNode]
      rw [h1, h2] at hab
      exact off_injective (bushTube_offset_injective hab)
  boundedOverlapDil := by
    intro k hk V
    exact card_finset_fin_two_nnreal _
  card_class_le := by
    intro k hk j hj
    have h1 : ((Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card : NNReal)
        ≤ 2 := by exact_mod_cast card_coverClass_le_two k j
    calc ((Tube.coverClass (Finset.univ : Finset (Fin 2)) ((wCover δ hδ).assign k) j).card :
            NNReal)
        ≤ 2 := by rw [wCover_assign]; exact h1
      _ ≤ 2 * wBranch k := two_le_two_mul_wBranch k
  le_card_class := by
    intro k hk j hj
    rw [wCover_indexSet] at hj
    have h1 : (1 : NNReal)
        ≤ ((Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign k) j).card : NNReal) := by
      exact_mod_cast one_le_card_coverClass hk hj
    calc wBranch k ≤ 2 := wBranch_le_two k
      _ = 2 * 1 := by norm_num
      _ ≤ 2 * ((Tube.coverClass (Finset.univ : Finset (Fin 2)) ((wCover δ hδ).assign k) j).card :
            NNReal) := by rw [wCover_assign]; gcongr

@[simp] lemma wUniform_cover (δ : NNReal) (hδ : δ ≤ 1) :
    (wUniform δ hδ).cover = wCover δ hδ := rfl

@[simp] lemma wUniform_branchingN (δ : NNReal) (hδ : δ ≤ 1) :
    (wUniform δ hδ).branchingN = wBranch := rfl

/-- **GWZ Definition 2.2 in the loose model, INHABITED on a two-member family.** -/
noncomputable def wShaded (δ : NNReal) (hδ : δ ≤ 1) :
    LooseShadedUniformTubeSet (Finset.univ : Finset (Fin 2)) (wV δ) 1 4 2 where
  tubeUniform := wUniform δ hδ
  branchingN := wBranch
  localN := fun _ => wBranch
  card_shadeClass_le := by
    intro x hx k hk i _ _
    have hxb : x ∈ Metric.closedBall (0 : E3) (δ : ℝ) := by
      simp only [Set.mem_iUnion, wV_shade] at hx
      obtain ⟨i', _, hx'⟩ := hx
      exact hx'
    rw [shadeClass_eq_coverClass δ _ _ hxb]
    have h1 : ((Tube.coverClass (Finset.univ : Finset (Fin 2))
        ((wUniform δ hδ).cover.assign k) ((wUniform δ hδ).cover.assign k i)).card : NNReal)
        ≤ 2 := by
      rw [wUniform_cover, wCover_assign]
      exact_mod_cast card_coverClass_le_two k (wAssign k i)
    exact h1.trans (two_le_two_mul_wBranch k)
  le_card_shadeClass := by
    intro x hx k hk i _ _
    have hxb : x ∈ Metric.closedBall (0 : E3) (δ : ℝ) := by
      simp only [Set.mem_iUnion, wV_shade] at hx
      obtain ⟨i', _, hx'⟩ := hx
      exact hx'
    rw [shadeClass_eq_coverClass δ _ _ hxb]
    have h1 : (1 : NNReal) ≤ ((Tube.coverClass (Finset.univ : Finset (Fin 2))
        ((wUniform δ hδ).cover.assign k) ((wUniform δ hδ).cover.assign k i)).card : NNReal) := by
      rw [wUniform_cover, wCover_assign]
      exact_mod_cast Finset.card_pos.mpr ⟨i, mem_coverClass_self k i⟩
    calc wBranch k ≤ 2 := wBranch_le_two k
      _ = 2 * 1 := by norm_num
      _ ≤ 2 * _ := by gcongr
  branchingN_le := by
    intro x hx k hk
    exact (wBranch_le_two k).trans (two_le_two_mul_wBranch k)
  le_branchingN := by
    intro x hx k hk
    exact (wBranch_le_two k).trans (two_le_two_mul_wBranch k)

/-! #### What the witness proves -/

/-- The family has **two** members. -/
theorem card_wS : (Finset.univ : Finset (Fin 2)).card = 2 := by simp

/-- Every shade is nonempty; with `0 < δ` it has positive volume (below). -/
theorem shade_nonempty (δ : NNReal) (i : Fin 2) : ((wV δ i).shade).Nonempty :=
  ⟨0, by simp⟩

/-- The shades have positive volume whenever `δ > 0`: the witness is not supported on a null
set. -/
theorem volume_shade_pos {δ : NNReal} (hδ0 : 0 < δ) (i : Fin 2) :
    0 < volume (wV δ i).shade := by
  rw [wV_shade]
  exact measure_closedBall_pos volume 0 (by exact_mod_cast hδ0)

/-- Both index sets are nonempty, and the fine level has two nodes. -/
theorem card_indexSet (δ : NNReal) (hδ : δ ≤ 1) :
    ((wShaded δ hδ).tubeUniform.cover.indexSet 0).card = 1 ∧
      ((wShaded δ hδ).tubeUniform.cover.indexSet 1).card = 2 := by
  constructor <;> simp [wShaded, wUniform, wCover, wIndex]

/-- The branching number is **not constant**: `2` at the coarse level, `1` at the fine level. -/
theorem branchingN_ne (δ : NNReal) (hδ : δ ≤ 1) :
    (wShaded δ hδ).branchingN 0 ≠ (wShaded δ hδ).branchingN 1 := by
  simpa [wShaded] using wBranch_zero_ne_wBranch_one

/-- The coarse class is **genuinely two-membered**: the level-`0` bracket
`card_class_le`/`le_card_class` is loaded with a class of size `2`, not a singleton. -/
theorem card_coverClass_zero :
    (Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign 0) 0).card = 2 := by
  have hsub : (Finset.univ : Finset (Fin 2))
      ⊆ Tube.coverClass (Finset.univ : Finset (Fin 2)) (wAssign 0) 0 := by
    intro i _
    have h := mem_coverClass_self 0 i
    rwa [show wAssign 0 i = (0 : Fin 2) from by simp [wAssign]] at h
  exact le_antisymm (card_finset_fin_two _) (by simpa using Finset.card_le_card hsub)

/-- And the **shade** class at the common point is two-membered too, so the Definition-2.2
brackets of the witness are loaded at a point of `U(𝕋, Y)` rather than vacuously. -/
theorem card_shadeClass_zero (δ : NNReal) :
    (ShadedTube.shadeClass (Finset.univ : Finset (Fin 2)) (wV δ) (wAssign 0) 0 (0 : E3)).card
      = 2 := by
  rw [shadeClass_eq_coverClass δ (wAssign 0) 0 (Metric.mem_closedBall_self δ.coe_nonneg),
    card_coverClass_zero]

/-- **THE NON-VACUITY WITNESS.** For every scale `δ ≤ 1`, the loose Definition 2.2 datum
`Kakeya.LooseUniform.LooseShadedUniformTubeSet` is inhabited on a family of **two** distinct
shaded tubes with nonempty shades, at `N = 1`, `K = 4`, `C = 2`. Hence no statement of the form
`∀ 𝒱 : LooseShadedUniformTubeSet s V N K C, P` is vacuously true for lack of an inhabitant, and
the inhabitant is not the degenerate `s = ∅` / `indexSet = ∅` one: `s.card = 2`, both index sets
are nonempty, both shades are nonempty, and the branching number is non-constant. -/
theorem exists_looseShadedUniformTubeSet_card_two {δ : NNReal} (hδ : δ ≤ 1) :
    ∃ (s : Finset (Fin 2)) (V : Fin 2 → ShadedTube δ E3),
      2 ≤ s.card ∧ (∀ i ∈ s, ((V i).shade).Nonempty) ∧ (V 0).toTube ≠ (V 1).toTube ∧
        Nonempty (LooseShadedUniformTubeSet s V 1 4 2) :=
  ⟨Finset.univ, wV δ, by simp, fun i _ => shade_nonempty δ i, wV_toTube_ne δ,
    ⟨wShaded δ hδ⟩⟩

open scoped Classical in
/-- **The conditional angular bound has a live call site.** Every hypothesis of
`Kakeya.LooseUniform.angularCone_card_le_of_loose` holds on the witness at the coarse level
`k = 0` whenever `0 < δ` and `4δ ≤ 1`, so that lemma is not merely a true implication with an
unreachable antecedent: it fires here, on a two-member family with nonempty shades. -/
theorem angularCone_card_le_on_witness {δ : NNReal} (hδ0 : 0 < δ) (hδ4 : 4 * (δ : ℝ) ≤ 1)
    (hδ1 : δ ≤ 1) {ρ : ℝ} (hρ : ρ ≤ 1) (x v : E3) :
    ((({i ∈ (Finset.univ : Finset (Fin 2)) |
          x ∈ (wV δ i).shade ∧ NonSlab.lineAngle (wV δ i).direction v ≤ ρ}).card : ℕ) : ENNReal)
      ≤ ((2 : NNReal) : ENNReal) ^ 5 *
        ShadedBody.multiplicity
          (Tube.coverClass (Finset.univ : Finset (Fin 2))
            ((wShaded δ hδ1).tubeUniform.cover.assign 0) 0)
          (fun i => (wV δ i).toShadedBody) := by
  refine angularCone_card_le_of_loose (wShaded δ hδ1) (by norm_num) (by norm_num)
    (Nat.zero_le 1) ?_ ?_ ?_ ?_ x v
  · rw [Tube.gridScale_zero]; push_cast; linarith
  · rw [Tube.gridScale_zero]; push_cast; linarith
  · intro i _
    exact (volume_shade_pos hδ0 i).ne'
  · exact ⟨0, mem_coverClass_self 0 0⟩

/-- **`LooseUniformTubeSet` is inhabited on a NONEMPTY family**: two members, at `N = 1`,
`K = 4`, `C = 2`. This gives a nonempty family satisfying the hypotheses. It is still **not**
a producer: the family here is chosen for the witness, not supplied by Main Lemma 2. -/
theorem nonempty_looseUniformTubeSet_card_two {δ : NNReal} (hδ : δ ≤ 1) :
    ∃ (s : Finset (Fin 2)) (T : Fin 2 → Tube δ E3), 2 ≤ s.card ∧ T 0 ≠ T 1 ∧
      Nonempty (LooseUniformTubeSet s T 1 4 2) :=
  ⟨Finset.univ, fun i => (wV δ i).toTube, by simp, wV_toTube_ne δ, ⟨wUniform δ hδ⟩⟩

/-- `Tube.PartitionBrackets` is inhabited on the same two-member family. -/
noncomputable def wBrackets (δ : NNReal) (hδ : δ ≤ 1) :
    Tube.PartitionBrackets (Finset.univ : Finset (Fin 2)) 1 2 :=
  (wUniform δ hδ).toPartitionBrackets

/-- **The `PartitionBrackets` non-vacuity witness**, with the same two-member family and the
same non-constant branching. -/
theorem exists_partitionBrackets_card_two :
    ∃ (s : Finset (Fin 2)) (B : Tube.PartitionBrackets s 1 2),
      2 ≤ s.card ∧ (B.indexSet 1).card = 2 ∧ B.branchingN 0 ≠ B.branchingN 1 :=
  ⟨Finset.univ, wBrackets 1 le_rfl, by simp, by simp [wBrackets, wUniform, wCover, wIndex],
    by simpa [wBrackets, wUniform] using wBranch_zero_ne_wBranch_one⟩

end NonVacuity

end LooseUniform

end Kakeya
