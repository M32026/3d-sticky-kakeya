import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Direction constraint from A-carrier containment

Given a source δ-tube whose carrier is contained in the A-dilated carrier of a
coarse ρ-tube, bound the transverse component of the source direction.

## Main results

- `gwz_point_transverse_bound`: every point on the source unit segment has
  transverse distance at most `A*ρ - δ` from the parent axis.
- `gwz_direction_constraint`: the transverse component of the source direction
  is bounded by `2*(A*ρ - δ)`.

These lemmas feed the tiling hCovers proof: when a tile is centered at the
source midpoint and aligned with the parent direction, the transverse budget
`‖w_perp‖/2 ≤ A*ρ - δ` satisfies `aligned_tube_containment`.

## Proof sketch

Every point in the A-dilated carrier is within distance `A*ρ` of the parent
axis (the line through the parent midpoint in the parent direction).  For a
point `y` on the source segment, pushing outward by `δ` in the transverse
direction gives a point in the source carrier (hence in the A-carrier), whose
transverse distance is `‖y_perp‖ + δ`.  Thus `‖y_perp‖ + δ ≤ A*ρ`, giving
`‖y_perp‖ ≤ A*ρ - δ`.  Applying this to both endpoints and using the triangle
inequality gives the direction bound.

## Whiteprint node

This module supports the StrictFiberCover tiling pillar.
-/

noncomputable section

open Metric Set InnerProductSpace

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Homothety scales distances by factor A. -/
lemma homothety_dist {m : Point3} {A : ℝ} (hA : 0 < A) (x y : Point3) :
    dist (AffineMap.homothety m A x) (AffineMap.homothety m A y) = A * dist x y := by
  have h1 : (AffineMap.homothety m A x) - (AffineMap.homothety m A y) = A • (x - y) := by
    simp [AffineMap.homothety_apply, smul_sub]
  have h2 : ‖(AffineMap.homothety m A x) - (AffineMap.homothety m A y)‖ = A * ‖x - y‖ := by
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hA]
  simpa [dist_eq_norm] using h2

/-- The unit segment of a tube is compact. -/
lemma isCompact_unitSegment {b v : Point3} : IsCompact (unitSegment b v) := by
  apply IsCompact.image isCompact_Icc
  exact continuous_const.add (continuous_id.smul continuous_const)

/--
For any point x and any point q on the line through m in direction v, the
transverse component of x relative to this line has norm at most dist(x, q).
-/
lemma perp_norm_le_dist_to_line_point
    {m v : Point3} (hv : ‖v‖ = 1) (x q : Point3) (t : ℝ) (ht : q = m + t • v) :
    ‖(x - m) - inner ℝ (x - m) v • v‖ ≤ dist x q := by
  let x_perp : Point3 := (x - m) - inner ℝ (x - m) v • v
  have h_perp : inner ℝ x_perp v = 0 := by
    dsimp only [x_perp]
    have h : inner ℝ ((x - m) - inner ℝ (x - m) v • v) v =
        inner ℝ (x - m) v - inner ℝ (inner ℝ (x - m) v • v) v := by
      rw [inner_sub_left]
    rw [h]
    have h2 : inner ℝ (inner ℝ (x - m) v • v) v = inner ℝ (x - m) v := by
      simp [inner_smul_left, hv]
    rw [h2] <;> ring
  have h_decomp : x - q = x_perp + (inner ℝ (x - m) v - t) • v := by
    have hq : q - m = t • v := by
      rw [ht]; simp [sub_smul]
    have h : x - q = (x - m) - (q - m) := by abel
    rw [h, hq]
    dsimp only [x_perp]; simp [sub_smul]
  have h_orth : inner ℝ x_perp ((inner ℝ (x - m) v - t) • v) = 0 := by
    rw [inner_smul_right, h_perp] <;> ring
  let y : Point3 := (inner ℝ (x - m) v - t) • v
  have h_orth2 : inner ℝ y x_perp = 0 := by
    have h_comm : inner ℝ y x_perp = inner ℝ x_perp y :=
      real_inner_comm x_perp y
    rw [h_comm, h_orth]
  have h_pyth : ‖x - q‖ ^ 2 = ‖x_perp‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [h_decomp]
    have h1 : ‖x_perp + y‖ ^ 2 =
        inner ℝ (x_perp + y) (x_perp + y) :=
      (inner_self_eq_norm_sq_to_K (x_perp + y)).symm
    rw [h1]
    have h2 : inner ℝ (x_perp + y) (x_perp + y) =
        inner ℝ x_perp x_perp + inner ℝ x_perp y + inner ℝ y x_perp + inner ℝ y y := by
      rw [inner_add_left, inner_add_right, inner_add_right] <;> abel
    rw [h2, h_orth, h_orth2]
    have h3 : inner ℝ x_perp x_perp = ‖x_perp‖ ^ 2 :=
      inner_self_eq_norm_sq_to_K x_perp
    have h4 : inner ℝ y y = ‖y‖ ^ 2 :=
      inner_self_eq_norm_sq_to_K y
    rw [h3, h4] <;> ring
  have h3 : ‖x_perp‖ ^ 2 ≤ ‖x - q‖ ^ 2 := by
    rw [h_pyth]
    have h4 : 0 ≤ ‖y‖ ^ 2 := by positivity
    linarith
  have h4 : 0 ≤ ‖x - q‖ := by positivity
  have h5 : 0 ≤ ‖x_perp‖ := by positivity
  by_cases h6 : ‖x_perp‖ ≤ ‖x - q‖
  · exact h6
  · have h7 : ‖x - q‖ < ‖x_perp‖ := by linarith
    have h8 : ‖x - q‖ ^ 2 < ‖x_perp‖ ^ 2 := by nlinarith
    linarith

/--
Every point in the A-dilated carrier has transverse distance at most Aρ from
the parent axis.
-/
lemma acarrier_transverse_bound
    {ρ A : ℝ} (hρ : 0 < ρ) (hA : 0 < A)
    (parentTube : DeltaTube ρ)
    (x : Point3)
    (hx : x ∈ wz2PaperCenteredDilatedCarrier A parentTube) :
    ‖(x - wz2PaperTubeMidpoint parentTube) -
        inner ℝ (x - wz2PaperTubeMidpoint parentTube) parentTube.direction • parentTube.direction‖ ≤ A * ρ := by
  let m : Point3 := wz2PaperTubeMidpoint parentTube
  let v : Point3 := parentTube.direction
  let hv : ‖v‖ = 1 := parentTube.direction_unit
  rcases hx with ⟨z, hz, rfl⟩
  have hz' : z ∈ parentTube.carrier := hz
  have hcompact : IsCompact (unitSegment parentTube.base v) := isCompact_unitSegment
  have h_exists : ∃ (p : Point3), p ∈ unitSegment parentTube.base v ∧ dist z p ≤ ρ := by
    have h_eq : parentTube.carrier = ⋃ p ∈ unitSegment parentTube.base v, Metric.closedBall p ρ :=
      hcompact.cthickening_eq_biUnion_closedBall (by linarith)
    rw [h_eq] at hz'
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using hz'
  rcases h_exists with ⟨p, hp, hdist⟩
  rcases hp with ⟨s, hs, rfl⟩
  let q : Point3 := AffineMap.homothety m A (parentTube.base + s • v)
  let t : ℝ := A * (s - 1 / 2)
  have hm : m = parentTube.base + (1 / 2 : ℝ) • v := by rfl
  have hq_line : q = m + t • v := by
    have h1 : q = A • ((parentTube.base + s • v) - m) + m := by
      simp [q, AffineMap.homothety_apply] <;> abel
    rw [h1]
    have h2 : (parentTube.base + s • v) - m = (s - 1 / 2 : ℝ) • v := by
      rw [hm]; simp [sub_smul]
    rw [h2]
    have h3 : A • ((s - 1 / 2 : ℝ) • v) = t • v := by
      rw [smul_smul] <;> dsimp only [t] <;> ring
    rw [h3] <;> abel
  have hdist2 : dist (AffineMap.homothety m A z) q = A * dist z (parentTube.base + s • v) :=
    homothety_dist hA z (parentTube.base + s • v)
  have hdist3 : dist (AffineMap.homothety m A z) q ≤ A * ρ := by
    rw [hdist2]
    exact mul_le_mul_of_nonneg_left hdist (by positivity)
  exact perp_norm_le_dist_to_line_point hv (AffineMap.homothety m A z) q t hq_line |>.trans hdist3

/--
Transverse norm bound: every point on the source unit segment has distance at
most `A*ρ - δ` from the parent axis.
-/
lemma gwz_point_transverse_bound
    {δ ρ A : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 1 ≤ A)
    (hδle : δ ≤ A * ρ)
    (sourceTube : DeltaTube δ)
    (parentTube : DeltaTube ρ)
    (h_containment : sourceTube.carrier ⊆ wz2PaperCenteredDilatedCarrier A parentTube)
    (y : Point3)
    (hy : y ∈ unitSegment sourceTube.base sourceTube.direction) :
    ‖(y - wz2PaperTubeMidpoint parentTube) -
        inner ℝ (y - wz2PaperTubeMidpoint parentTube) parentTube.direction • parentTube.direction‖ ≤
      A * ρ - δ := by
  let m : Point3 := wz2PaperTubeMidpoint parentTube
  let v : Point3 := parentTube.direction
  let y_perp : Point3 := (y - m) - inner ℝ (y - m) v • v
  let r : ℝ := ‖y_perp‖
  have hA_pos : 0 < A := by linarith
  by_cases hr : r = 0
  · rw [show ‖y_perp‖ = 0 from hr] <;> linarith
  · have hr_pos : 0 < r := by
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr)
    let u : Point3 := (1 / r) • y_perp
    have hu_norm : ‖u‖ = 1 := by
      dsimp only [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / r))]
      <;> field_simp [hr_pos.ne'] <;> ring
    have h_yperp_perp : inner ℝ y_perp v = 0 := by
      dsimp only [y_perp]
      have h : inner ℝ ((y - m) - inner ℝ (y - m) v • v) v =
          inner ℝ (y - m) v - inner ℝ (inner ℝ (y - m) v • v) v := by
        rw [inner_sub_left]
      rw [h]
      have h21 : inner ℝ (inner ℝ (y - m) v • v) v = (inner ℝ (y - m) v) * inner ℝ v v := by
        have h : ∀ (c : ℝ) (x y : Point3), inner ℝ (c • x) y = c * inner ℝ x y := by
          intro c x y
          simpa [inner_smul_left] using rfl
        exact h (inner ℝ (y - m) v) v v
      rw [h21]
      have h22 : inner ℝ v v = ‖v‖ ^ 2 :=
        inner_self_eq_norm_sq_to_K v
      rw [h22, parentTube.direction_unit] <;> ring
    have h1u : y + δ • u ∈ sourceTube.carrier := by
      have h_eq : (y + δ • u) - y = δ • u := by abel
      have h_dist : dist (y + δ • u) y = δ := by
        rw [dist_eq_norm, h_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hu_norm] <;> ring
      exact Metric.mem_cthickening_of_dist_le (y + δ • u) y δ
        (unitSegment sourceTube.base sourceTube.direction) hy (by rw [h_dist])
    have h2u : y + δ • u ∈ wz2PaperCenteredDilatedCarrier A parentTube := h_containment h1u
    have h_perp_sum : ((y + δ • u) - m) - inner ℝ ((y + δ • u) - m) v • v = (1 + δ / r) • y_perp := by
      have h_inner : inner ℝ (y + δ • u - m) v = inner ℝ (y - m) v := by
        have h : inner ℝ (y + δ • u - m) v = inner ℝ (y - m) v + inner ℝ (δ • u) v := by
          rw [←inner_add_left] <;> abel
        rw [h]
        have h2 : inner ℝ (δ • u) v = 0 := by
          rw [inner_smul_left]
          have h3 : inner ℝ u v = 0 := by
            dsimp only [u]
            rw [inner_smul_left, h_yperp_perp] <;> ring
          rw [h3] <;> ring
        rw [h2] <;> ring
      have h_step1 : (y + δ • u) - m = (y - m) + δ • u := by abel
      have h_goal : ((y + δ • u) - m) - inner ℝ ((y + δ • u) - m) v • v = (1 + δ / r) • y_perp := by
        calc
          ((y + δ • u) - m) - inner ℝ ((y + δ • u) - m) v • v
            = (y - m) + δ • u - inner ℝ (y - m) v • v := by rw [h_inner, h_step1]
          _ = y_perp + δ • u := by dsimp only [y_perp] <;> abel
          _ = (1 + δ / r) • y_perp := by
            dsimp only [u]
            rw [smul_smul]
            <;> simp [add_smul] <;> abel
      exact h_goal
    have h3u := acarrier_transverse_bound hρ hA_pos parentTube (y + δ • u) h2u
    rw [h_perp_sum] at h3u
    have h4 : ‖(1 + δ / r) • y_perp‖ = r + δ := by
      rw [norm_smul, Real.norm_eq_abs]
      have h_pos : 0 ≤ 1 + δ / r := by positivity
      rw [abs_of_nonneg h_pos]
      have h : (1 + δ / r) * r = r + δ := by
        field_simp [hr_pos.ne'] <;> ring
      rw [h] <;> ring
    rw [h4] at h3u
    linarith

/--
Direction constraint: if a source δ-tube is contained in the A-dilated carrier
of a coarse ρ-tube, the transverse component of its direction is bounded by
`2*(A*ρ - δ)`.
-/
lemma gwz_direction_constraint
    {δ ρ A : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hA : 1 ≤ A)
    (hδle : δ ≤ A * ρ)
    (sourceTube : DeltaTube δ)
    (parentTube : DeltaTube ρ)
    (h_containment : sourceTube.carrier ⊆ wz2PaperCenteredDilatedCarrier A parentTube) :
    ‖sourceTube.direction -
        inner ℝ sourceTube.direction parentTube.direction • parentTube.direction‖ ≤
      2 * (A * ρ - δ) := by
  let v : Point3 := parentTube.direction
  let m : Point3 := wz2PaperTubeMidpoint parentTube
  let w : Point3 := sourceTube.direction
  let p : Point3 := wz2PaperTubeMidpoint sourceTube
  let trans (x : Point3) : Point3 := x - inner ℝ x v • v
  let y_plus : Point3 := p + (1 / 2 : ℝ) • w
  let y_minus : Point3 := p - (1 / 2 : ℝ) • w
  have h_p_def : p = sourceTube.base + (1 / 2 : ℝ) • w := by
    simp [p, wz2PaperTubeMidpoint] <;> rfl
  have hy_plus : y_plus ∈ unitSegment sourceTube.base sourceTube.direction := by
    have h9 : y_plus = p + (1 / 2 : ℝ) • w := by rfl
    have h_eq : y_plus = sourceTube.base + (1 : ℝ) • w := by
      rw [h9, h_p_def]
      have h10 : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w = (1 : ℝ) • w := by
        rw [←add_smul] <;> norm_num
      simpa [add_assoc] using congr_arg (fun x => sourceTube.base + x) h10
    rw [h_eq]
    exact ⟨1, by norm_num, by simp [w]⟩
  have hy_minus : y_minus ∈ unitSegment sourceTube.base sourceTube.direction := by
    have h_eq : y_minus = sourceTube.base + (0 : ℝ) • w := by
      dsimp only [y_minus]
      rw [h_p_def] <;> simp [add_smul] <;> abel
    rw [h_eq]
    exact ⟨0, by norm_num, by simp⟩
  have h_bound_plus : ‖trans (y_plus - m)‖ ≤ A * ρ - δ :=
    gwz_point_transverse_bound hδ hρ hA hδle sourceTube parentTube h_containment y_plus hy_plus
  have h_bound_minus : ‖trans (y_minus - m)‖ ≤ A * ρ - δ :=
    gwz_point_transverse_bound hδ hρ hA hδle sourceTube parentTube h_containment y_minus hy_minus
  have h1 : y_plus - y_minus = w := by
    have h9 : y_plus = p + (1 / 2 : ℝ) • w := by rfl
    have h10 : y_minus = p - (1 / 2 : ℝ) • w := by rfl
    rw [h9, h10]
    have h11 : (p + (1 / 2 : ℝ) • w) - (p - (1 / 2 : ℝ) • w) = (1 : ℝ) • w := by
      have h12 : (p + (1 / 2 : ℝ) • w) - (p - (1 / 2 : ℝ) • w) = (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w := by
        simp [sub_smul] <;> abel
      rw [h12]
      have h13 : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w = (1 : ℝ) • w := by
        rw [←add_smul] <;> norm_num
      exact h13
    rw [h11]
    simp
  have h4 : (y_plus - m) - (y_minus - m) = y_plus - y_minus := by abel
  have h2 : inner ℝ (y_plus - m) v - inner ℝ (y_minus - m) v = inner ℝ w v := by
    have h3 : inner ℝ (y_plus - m) v - inner ℝ (y_minus - m) v =
        inner ℝ ((y_plus - m) - (y_minus - m)) v := by
      rw [←inner_sub_left] <;> rfl
    rw [h3, h4, h1]
  have h_w_perp_eq : trans w = trans (y_plus - m) - trans (y_minus - m) := by
    dsimp only [trans]
    have h5 : (y_plus - m) - inner ℝ (y_plus - m) v • v -
        ((y_minus - m) - inner ℝ (y_minus - m) v • v) =
        (y_plus - y_minus) - (inner ℝ (y_plus - m) v - inner ℝ (y_minus - m) v) • v := by
      simp [sub_smul] <;> abel
    have h6 : (y_plus - y_minus) - (inner ℝ (y_plus - m) v - inner ℝ (y_minus - m) v) • v =
        w - inner ℝ w v • v := by
      rw [h1, h2] <;> rfl
    rw [h5, h6]
  have h_final : ‖trans w‖ ≤ 2 * (A * ρ - δ) := by
    rw [h_w_perp_eq]
    have h7 : ‖trans (y_plus - m) - trans (y_minus - m)‖ ≤
        ‖trans (y_plus - m)‖ + ‖trans (y_minus - m)‖ := norm_sub_le _ _
    have h8 : ‖trans (y_plus - m)‖ + ‖trans (y_minus - m)‖ ≤ (A * ρ - δ) + (A * ρ - δ) := by
      gcongr
    linarith
  exact h_final

end Kakeya.Assouad

end
