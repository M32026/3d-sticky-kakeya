module

public import MyLeanRepo.RadialBootstrapping.Basic

@[expose] public section

/-!
# Bounded Overlap of Direction-Separated Tubes

This module proves that a family of tubes with direction-separated axial lines,
all passing through a common point `y`, has bounded overlap outside `B(y, ξ)`.

Main results:
- `perp_component_bound` — perpendicular component bound for points in a tube
- `submoduleDirDist_eq_perp` — key identity relating projection norm to perp component

Whiteprint node: tube-families (bounded overlap sub-result)
-/

open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

-- ============================================================================
-- 1. Helper lemmas for R² = EuclideanSpace ℝ (Fin 2)
-- ============================================================================

lemma inner_fin2 (x y : Point) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  have h : inner ℝ x y = ∑ i : Fin 2, inner ℝ (x i) (y i) := PiLp.inner_apply x y
  rw [h, Fin.sum_univ_two]
  have h2 : ∀ (a b : ℝ), inner ℝ a b = a * b := by intro a b; exact Real.inner_apply a b
  rw [h2 (x 0) (y 0), h2 (x 1) (y 1)] <;> ring

lemma norm_sq_fin2 (x : Point) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  have h : inner ℝ x x = ‖x‖ ^ 2 := by exact real_inner_self_eq_norm_sq x
  rw [← h, inner_fin2] <;> ring

lemma coords_norm_one (u : Point) (hnorm : ‖u‖ = 1) : u 0 ^ 2 + u 1 ^ 2 = 1 := by
  have h : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := norm_sq_fin2 u
  have h2 : ‖u‖ ^ 2 = 1 := by rw [hnorm] <;> norm_num
  linarith

/-- Rotate a point in R² by 90 degrees counterclockwise. -/
def rot90 (p : Point) : Point :=
  WithLp.toLp 2 fun i : Fin 2 =>
    match i with
    | 0 => -(p 1)
    | 1 => p 0

lemma rot90_apply (p : Point) :
    (rot90 p) 0 = -(p 1) ∧ (rot90 p) 1 = p 0 := by
  constructor <;> rfl

lemma rot90_inner_self (u : Point) : inner ℝ u (rot90 u) = 0 := by
  rw [inner_fin2]
  have h := rot90_apply u
  rw [h.1, h.2] <;> ring

lemma rot90_norm (u : Point) : ‖rot90 u‖ = ‖u‖ := by
  have h : ‖rot90 u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_fin2, norm_sq_fin2]
    have h' := rot90_apply u
    rw [h'.1, h'.2] <;> ring
  have h1 : 0 ≤ ‖rot90 u‖ := by positivity
  have h2 : 0 ≤ ‖u‖ := by positivity
  nlinarith

lemma fourier_expansion (u : Point) (hnorm : ‖u‖ = 1) (x : Point) :
    x = inner ℝ x u • u + inner ℝ x (rot90 u) • rot90 u := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := coords_norm_one u hnorm
  set a := inner ℝ x u with ha
  set b := inner ℝ x (rot90 u) with hb
  have ha_def : a = x 0 * u 0 + x 1 * u 1 := by
    simp [ha, inner_fin2] <;> ring
  have hb_def : b = -(x 0 * u 1) + x 1 * u 0 := by
    simp [hb, inner_fin2, rot90_apply] <;> ring
  have h_rhs0 : (a • u + b • rot90 u) 0 = x 0 := by
    have h_rot0 : (rot90 u) 0 = -(u 1) := (rot90_apply u).1
    have h_eq : (a • u + b • rot90 u) 0 = a * u 0 + b * (-(u 1)) := by
      simp [h_rot0, Pi.add_apply, Pi.smul_apply]
      <;> ring
    rw [h_eq, ha_def, hb_def]
    have h : (x 0 * u 0 + x 1 * u 1) * u 0 + (-(x 0 * u 1) + x 1 * u 0) * (-(u 1)) = x 0 := by
      calc
        _ = x 0 * (u 0 ^ 2 + u 1 ^ 2) := by ring
        _ = x 0 * 1 := by rw [hu2]
        _ = x 0 := by ring
    exact h
  have h_rhs1 : (a • u + b • rot90 u) 1 = x 1 := by
    have h_rot1 : (rot90 u) 1 = u 0 := (rot90_apply u).2
    have h_eq : (a • u + b • rot90 u) 1 = a * u 1 + b * u 0 := by
      simp [h_rot1, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h_eq, ha_def, hb_def]
    have h : (x 0 * u 0 + x 1 * u 1) * u 1 + (-(x 0 * u 1) + x 1 * u 0) * u 0 = x 1 := by
      calc
        _ = x 1 * (u 0 ^ 2 + u 1 ^ 2) := by ring
        _ = x 1 * 1 := by rw [hu2]
        _ = x 1 := by ring
    exact h
  ext i
  fin_cases i <;> tauto

lemma sum_sq_inner (u v : Point) (hnorm_u : ‖u‖ = 1) (hnorm_v : ‖v‖ = 1) :
    (inner ℝ u v) ^ 2 + (inner ℝ (rot90 u) v) ^ 2 = 1 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := coords_norm_one u hnorm_u
  have hv2 : v 0 ^ 2 + v 1 ^ 2 = 1 := coords_norm_one v hnorm_v
  have h' := rot90_apply u
  have h_main : (inner ℝ u v) ^ 2 + (inner ℝ (rot90 u) v) ^ 2 =
      (u 0 * v 0 + u 1 * v 1) ^ 2 + (-(u 1) * v 0 + u 0 * v 1) ^ 2 := by
    rw [inner_fin2, inner_fin2]
    rw [h'.1, h'.2] <;> ring
  rw [h_main]
  nlinarith [hu2, hv2]

-- ============================================================================
-- 2. Geometric lemma: perpendicular component bound
-- ============================================================================

/-- If both `y` and `z` lie within distance `2r` of a line `L` with direction `V`,
then the perpendicular component of `z - y` relative to `V` has norm at most `4r`. -/
lemma perp_component_bound (r : ℝ) (hr : 0 < r)
    (L : Line2) (y z : Point)
    (hy : y ∈ tube (2 * r) L)
    (hz : z ∈ tube (2 * r) L) :
    ‖(z - y) - L.toAffine.direction.orthogonalProjectionFn (z - y)‖ ≤ 4 * r := by
  let V := L.toAffine.direction
  rcases Metric.mem_thickening_iff.mp hy with ⟨y', hy'L, hy'⟩
  rcases Metric.mem_thickening_iff.mp hz with ⟨z', hz'L, hz'⟩
  have h1 : z' - y' ∈ V := AffineSubspace.vsub_mem_direction hz'L hy'L
  have h2 : V.orthogonalProjectionFn (z' - y') = z' - y' := by
    have h3 : V.orthogonalProjectionOnto (z' - y') = ⟨z' - y', h1⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z' - y', h1⟩
    have h4 : (V.orthogonalProjectionOnto (z' - y') : Point) = z' - y' := by
      exact congr_arg (fun (x : V) => (x : Point)) h3
    exact h4
  have h_perp_orth : ∀ (x : Point), ‖x - V.orthogonalProjectionFn x‖ ≤ ‖x‖ := by
    intro x
    have h4 : Vᗮ.orthogonalProjectionFn x = x - V.orthogonalProjectionFn x := by
      exact Submodule.starProjection_orthogonal_val (K := V) x
    rw [← h4]
    exact Submodule.norm_starProjection_apply_le Vᗮ x
  have h4 : (z - y) - V.orthogonalProjectionFn (z - y) =
      ((z - z') - V.orthogonalProjectionFn (z - z')) +
      ((y' - y) - V.orthogonalProjectionFn (y' - y)) := by
    have h5 : z - y = (z - z') + (z' - y') + (y' - y) := by abel
    simp only [h5, map_add, h2] <;> abel
  rw [h4]
  have h5 : ‖z - z'‖ < 2 * r := by
    have h51 : dist z z' < 2 * r := hz'
    simpa [dist_eq_norm] using h51
  have h6 : ‖y' - y‖ < 2 * r := by
    have h61 : dist y y' < 2 * r := hy'
    have h62 : ‖y - y'‖ < 2 * r := by simpa [dist_eq_norm] using h61
    have h63 : ‖y' - y‖ = ‖y - y'‖ := norm_sub_rev y' y
    rw [h63]
    exact h62
  have h7 : ‖(z - z') - V.orthogonalProjectionFn (z - z')‖ +
        ‖(y' - y) - V.orthogonalProjectionFn (y' - y)‖ < 4 * r := by
    have h71 : ‖(z - z') - V.orthogonalProjectionFn (z - z')‖ ≤ ‖z - z'‖ := h_perp_orth _
    have h72 : ‖(y' - y) - V.orthogonalProjectionFn (y' - y)‖ ≤ ‖y' - y‖ := h_perp_orth _
    linarith
  have h_sum : ‖((z - z') - V.orthogonalProjectionFn (z - z')) +
        ((y' - y) - V.orthogonalProjectionFn (y' - y))‖ ≤
      ‖(z - z') - V.orthogonalProjectionFn (z - z')‖ +
        ‖(y' - y) - V.orthogonalProjectionFn (y' - y)‖ := norm_add_le _ _
  linarith

-- ============================================================================
-- 3. Projection formula for 1D subspaces
-- ============================================================================

/-- For a 1D subspace `V` spanned by unit vector `v`, the orthogonal projection
of `x` onto `V` is `inner(x, v) • v`. -/
lemma projection_one_dim (V : Submodule ℝ Point) (v : Point) (x : Point)
    (hvV : v ∈ V) (hnorm : ‖v‖ = 1)
    (hV : Module.finrank ℝ V = 1) :
    V.orthogonalProjectionFn x = inner ℝ x v • v := by
  let p : Point := inner ℝ x v • v
  have hpV : p ∈ V := V.smul_mem (inner ℝ x v) hvV
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hnorm
    simp at hnorm
  have h_span_le : Submodule.span ℝ ({v} : Set Point) ≤ V := by
    apply Submodule.span_le.mpr
    intro w hw
    simp only [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hvV
  have h_finrank_span : Module.finrank ℝ (Submodule.span ℝ ({v} : Set Point)) = 1 := by
    rw [finrank_span_singleton hv0] <;> norm_num
  have hV_eq : V = Submodule.span ℝ ({v} : Set Point) := by
    have h_eq : Submodule.span ℝ ({v} : Set Point) = V :=
      Submodule.eq_of_le_of_finrank_eq h_span_le (by rw [h_finrank_span, hV])
    exact h_eq.symm
  have h_orth : x - p ∈ Vᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    have h_w_span : w ∈ Submodule.span ℝ ({v} : Set Point) := by
      rw [← hV_eq] <;> exact hw
    rcases Submodule.mem_span_singleton.mp h_w_span with ⟨a, ha⟩
    have h_w_eq : w = a • v := Eq.symm ha
    have h_goal : inner ℝ (x - p) w = 0 := by
      rw [h_w_eq]
      have h_inner : inner ℝ (x - p) (a • v) = a * (inner ℝ (x - p) v) := by
        simp [inner_smul_right] <;> ring
      rw [h_inner]
      have h_p_inner : inner ℝ (x - p) v = 0 := by
        have h1 : inner ℝ (x - p) v = inner ℝ x v - inner ℝ p v := by
          rw [inner_sub_left]
        rw [h1]
        have h2 : inner ℝ p v = inner ℝ x v := by
          dsimp only [p]
          have h3 : inner ℝ ((inner ℝ x v) • v) v = (inner ℝ x v) * inner ℝ v v :=
            inner_smul_left v v (inner ℝ x v)
          rw [h3]
          have h4 : inner ℝ v v = 1 := by
            have h5 : inner ℝ v v = ‖v‖ ^ 2 := by exact real_inner_self_eq_norm_sq v
            rw [h5, hnorm] <;> norm_num
          rw [h4] <;> ring
        rw [h2] <;> ring
      rw [h_p_inner] <;> ring
    exact h_goal
  exact Submodule.eq_starProjection_of_mem_orthogonal hpV h_orth

-- ============================================================================
-- 4. Key identity in R²
-- ============================================================================

/-- Key identity: for 1D subspaces `V`, `W` of `R²` and a unit vector `u ∈ W`,
`submoduleDirDist V W = ‖u - V.orthogonalProjectionFn u‖`. -/
lemma submoduleDirDist_eq_perp (V W : Submodule ℝ Point)
    (hV : Module.finrank ℝ V = 1) (hW : Module.finrank ℝ W = 1)
    (u : Point) (hu : u ∈ W) (hnorm_u : ‖u‖ = 1) :
    submoduleDirDist V W = ‖u - V.orthogonalProjectionFn u‖ := by
  -- Pick unit vector v in V
  have hV_pos : 0 < Module.finrank ℝ V := by omega
  have h_exists : ∃ (v : Point), v ∈ V ∧ v ≠ 0 := by
    have h : (V : Set Point).Nonempty := by
      exact Submodule.nonempty V
    by_contra h2
    push Not at h2
    have hV_bot : V = (⊥ : Submodule ℝ Point) := by
      ext x
      simp only [Submodule.mem_bot]
      constructor
      · intro hx
        exact h2 x hx
      · intro hx
        rw [hx]
        exact Submodule.zero_mem V
    rw [hV_bot] at hV_pos
    simp at hV_pos <;> omega
  rcases h_exists with ⟨v, hvV, hv0⟩
  let v' : Point := (1 / ‖v‖) • v
  have hv'V : v' ∈ V := V.smul_mem (1 / ‖v‖) hvV
  have hnorm_v' : ‖v'‖ = 1 := by
    simp [v', norm_smul, hv0] <;> field_simp [hv0] <;> ring_nf <;> norm_num

  let c := inner ℝ u v'
  let d := inner ℝ (rot90 u) v'
  have hcd : c ^ 2 + d ^ 2 = 1 := sum_sq_inner u v' hnorm_u hnorm_v'

  -- Projection formulas
  have hprojV : ∀ (x : Point), V.orthogonalProjectionFn x = inner ℝ x v' • v' :=
    fun x => projection_one_dim V v' x hv'V hnorm_v' hV
  have hprojW : ∀ (x : Point), W.orthogonalProjectionFn x = inner ℝ x u • u :=
    fun x => projection_one_dim W u x hu hnorm_u hW

  -- Show that for all x, ‖proj_V x - proj_W x‖^2 = (1 - c^2) * ‖x‖^2
  have h_main : ∀ (x : Point), ‖V.orthogonalProjectionFn x - W.orthogonalProjectionFn x‖ ^ 2 =
        (1 - c ^ 2) * ‖x‖ ^ 2 := by
    intro x
    rw [hprojV x, hprojW x]
    set a := inner ℝ x u with ha
    set b := inner ℝ x (rot90 u) with hb
    have h_x : x = a • u + b • rot90 u := fourier_expansion u hnorm_u x
    have h_inner_v : inner ℝ x v' = a * c + b * d := by
      rw [h_x]
      simp [inner_add_left, inner_smul_left, c, d] <;> ring
    have h_norm2 : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [h_x]
      have h_orth : inner ℝ (a • u) (b • rot90 u) = 0 := by
        simp [inner_smul_left, inner_smul_right, rot90_inner_self] <;> ring
      have h_norm_add : ‖a • u + b • rot90 u‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • rot90 u‖ ^ 2 := by
        have h_eq : inner ℝ (a • u) (b • rot90 u) = 0 := h_orth
        have h : ‖a • u + b • rot90 u‖ * ‖a • u + b • rot90 u‖ =
            ‖a • u‖ * ‖a • u‖ + ‖b • rot90 u‖ * ‖b • rot90 u‖ :=
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • u) (b • rot90 u) h_eq
        have h' : ‖a • u + b • rot90 u‖ ^ 2 = ‖a • u + b • rot90 u‖ * ‖a • u + b • rot90 u‖ := by ring
        rw [h']
        have h'' : ‖a • u‖ ^ 2 = ‖a • u‖ * ‖a • u‖ := by ring
        have h''' : ‖b • rot90 u‖ ^ 2 = ‖b • rot90 u‖ * ‖b • rot90 u‖ := by ring
        rw [h'', h''']
        exact h
      rw [h_norm_add]
      simp [norm_smul, hnorm_u, rot90_norm, hnorm_u] <;> ring
    have h_goal : ‖(a * c + b * d) • v' - a • u‖ ^ 2 = (1 - c ^ 2) * (a ^ 2 + b ^ 2) := by
      have h_inner_vu : inner ℝ v' u = c := by
        dsimp only [c]
        have h_comm : inner ℝ v' u = inner ℝ u v' := by
          exact real_inner_comm u v'
        exact h_comm
      have h : ‖(a * c + b * d) • v' - a • u‖ ^ 2 =
          (a * c + b * d) ^ 2 + a ^ 2 - 2 * (a * c + b * d) * a * c := by
        have h2 : ‖(a * c + b * d) • v' - a • u‖ ^ 2 =
            ‖(a * c + b * d) • v'‖ ^ 2 + ‖a • u‖ ^ 2 -
            2 * inner ℝ ((a * c + b * d) • v') (a • u) := by
          have h3 := norm_sub_sq_real ((a * c + b * d) • v') (a • u)
          linarith
        rw [h2]
        have h4 : inner ℝ ((a * c + b * d) • v') (a • u) = (a * c + b * d) * a * c := by
          simp [inner_smul_left, inner_smul_right, h_inner_vu] <;> ring
        rw [h4]
        simp [norm_smul, hnorm_v', hnorm_u] <;> ring
      rw [h]
      have h5 : d ^ 2 = 1 - c ^ 2 := by nlinarith [hcd]
      have h_goal2 : (a * c + b * d) ^ 2 + a ^ 2 - 2 * (a * c + b * d) * a * c = (1 - c ^ 2) * (a ^ 2 + b ^ 2) := by
        have h6 : d ^ 2 = 1 - c ^ 2 := h5
        nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c + b * d)]
      exact h_goal2
    rw [h_inner_v, h_norm2]
    exact h_goal

  have h1 : 0 ≤ 1 - c ^ 2 := by nlinarith [hcd]

  -- Operator norm upper bound
  have h_bound : ∀ (x : Point), ‖(submoduleProj V - submoduleProj W) x‖ ≤ Real.sqrt (1 - c ^ 2) * ‖x‖ := by
    intro x
    have h2 : ‖(submoduleProj V - submoduleProj W) x‖ ^ 2 = (1 - c ^ 2) * ‖x‖ ^ 2 := by
      have h_eq : (submoduleProj V - submoduleProj W) x = V.orthogonalProjectionFn x - W.orthogonalProjectionFn x := by rfl
      rw [h_eq]
      exact h_main x
    have h3 : (Real.sqrt (1 - c ^ 2) * ‖x‖) ^ 2 = (1 - c ^ 2) * ‖x‖ ^ 2 := by
      have h4 : (Real.sqrt (1 - c ^ 2)) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt h1
      calc
        (Real.sqrt (1 - c ^ 2) * ‖x‖) ^ 2
          = (Real.sqrt (1 - c ^ 2)) ^ 2 * ‖x‖ ^ 2 := by ring
        _ = (1 - c ^ 2) * ‖x‖ ^ 2 := by rw [h4] <;> ring
    have h5 : ‖(submoduleProj V - submoduleProj W) x‖ ^ 2 = (Real.sqrt (1 - c ^ 2) * ‖x‖) ^ 2 := by
      rw [h2, h3]
    have h6 : 0 ≤ ‖(submoduleProj V - submoduleProj W) x‖ := by positivity
    have h7 : 0 ≤ Real.sqrt (1 - c ^ 2) * ‖x‖ := by positivity
    nlinarith
  have h_upper : ‖submoduleProj V - submoduleProj W‖ ≤ Real.sqrt (1 - c ^ 2) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) h_bound

  -- Helper: norm of u - proj_V u squared
  have h_perp_sq : ‖u - V.orthogonalProjectionFn u‖ ^ 2 = 1 - c ^ 2 := by
    have h5 : ‖V.orthogonalProjectionFn u - W.orthogonalProjectionFn u‖ ^ 2 = 1 - c ^ 2 := by
      have h51 := h_main u
      rw [hnorm_u] at h51
      ring_nf at h51 ⊢
      exact h51
    have h6 : ‖V.orthogonalProjectionFn u - W.orthogonalProjectionFn u‖ = ‖u - V.orthogonalProjectionFn u‖ := by
      rw [hprojW u]
      simp [hnorm_u]
      <;> rw [norm_sub_rev]
    have h7 : ‖V.orthogonalProjectionFn u - W.orthogonalProjectionFn u‖ ^ 2 = ‖u - V.orthogonalProjectionFn u‖ ^ 2 := by
      rw [h6]
    rw [h7] at h5
    exact h5

  -- Operator norm lower bound: evaluate at u
  have h4 : ‖(submoduleProj V - submoduleProj W) u‖ ^ 2 = 1 - c ^ 2 := by
    have h_eq : (submoduleProj V - submoduleProj W) u = V.orthogonalProjectionFn u - W.orthogonalProjectionFn u := by rfl
    rw [h_eq]
    have h6 : ‖V.orthogonalProjectionFn u - W.orthogonalProjectionFn u‖ = ‖u - V.orthogonalProjectionFn u‖ := by
      rw [hprojW u] <;> simp [hnorm_u] <;> rw [norm_sub_rev]
    have h7 : ‖V.orthogonalProjectionFn u - W.orthogonalProjectionFn u‖ ^ 2 = ‖u - V.orthogonalProjectionFn u‖ ^ 2 := by rw [h6]
    rw [h7]
    exact h_perp_sq
  have h5 : 0 ≤ ‖(submoduleProj V - submoduleProj W) u‖ := by positivity
  have h6 : ‖(submoduleProj V - submoduleProj W) u‖ = Real.sqrt (1 - c ^ 2) := by
    have h7 : ‖(submoduleProj V - submoduleProj W) u‖ ^ 2 = (Real.sqrt (1 - c ^ 2)) ^ 2 := by
      rw [h4, Real.sq_sqrt h1]
    have h8 : 0 ≤ ‖(submoduleProj V - submoduleProj W) u‖ := by positivity
    nlinarith [Real.sqrt_nonneg (1 - c ^ 2)]
  have h7 : ‖(submoduleProj V - submoduleProj W) u‖ ≤
      ‖submoduleProj V - submoduleProj W‖ * ‖u‖ :=
    (submoduleProj V - submoduleProj W).le_opNorm u
  rw [hnorm_u] at h7
  have h_lower : Real.sqrt (1 - c ^ 2) ≤ ‖submoduleProj V - submoduleProj W‖ := by
    linarith [h6, h7]

  have h_op_norm : ‖submoduleProj V - submoduleProj W‖ = Real.sqrt (1 - c ^ 2) :=
    le_antisymm h_upper h_lower

  -- Perp component norm
  have h_perp : ‖u - V.orthogonalProjectionFn u‖ = Real.sqrt (1 - c ^ 2) := by
    have h13 : 0 ≤ ‖u - V.orthogonalProjectionFn u‖ := by positivity
    have h14 : ‖u - V.orthogonalProjectionFn u‖ ^ 2 = (Real.sqrt (1 - c ^ 2)) ^ 2 := by
      rw [h_perp_sq, Real.sq_sqrt h1]
    nlinarith [Real.sqrt_nonneg (1 - c ^ 2)]

  rw [submoduleDirDist, h_op_norm, h_perp]

-- ============================================================================
-- 5. Direction closeness corollary
-- ============================================================================

/-- If both `y` and `z` lie in the `2r`-tube of line `L`, then the direction
of `L` is close to the direction of `z - y`:
`submoduleDirDist(V, span(z-y)) ≤ 4r / ‖z-y‖`. -/
lemma direction_closeness (r : ℝ) (hr : 0 < r)
    (L : Line2) (y z : Point) (hne : z ≠ y)
    (hy : y ∈ tube (2 * r) L) (hz : z ∈ tube (2 * r) L) :
    submoduleDirDist L.toAffine.direction (Submodule.span ℝ {z - y}) ≤
      4 * r / ‖z - y‖ := by
  let V := L.toAffine.direction
  let w : Point := z - y
  have hw0 : w ≠ 0 := by
    intro h
    have h' : z - y = 0 := h
    exact hne (sub_eq_zero.mp h')
  have hnorm_w : 0 < ‖w‖ := by
    exact norm_pos_iff.mpr hw0
  let u : Point := (1 / ‖w‖) • w
  have hnu : ‖u‖ = 1 := by
    simp [u, norm_smul, hnorm_w.ne'] <;> field_simp [hnorm_w.ne'] <;> ring_nf <;> norm_num
  have huW : u ∈ Submodule.span ℝ {w} := by
    rw [Submodule.mem_span_singleton]
    refine' ⟨1 / ‖w‖, _⟩
    <;> simp [u] <;> ring
  have hW1 : Module.finrank ℝ (Submodule.span ℝ {w}) = 1 := by
    rw [finrank_span_singleton hw0] <;> norm_num
  have h_perp : ‖w - V.orthogonalProjectionFn w‖ ≤ 4 * r :=
    perp_component_bound r hr L y z hy hz
  have h_id : submoduleDirDist V (Submodule.span ℝ {w}) =
      ‖u - V.orthogonalProjectionFn u‖ :=
    submoduleDirDist_eq_perp V (Submodule.span ℝ {w}) L.2 hW1 u huW hnu
  rw [h_id]
  have h_scale : ‖u - V.orthogonalProjectionFn u‖ =
      ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ := by
    have h_proj_eq : ∀ (x : Point), V.orthogonalProjectionFn x = submoduleProj V x := by
      intro x
      have h_fn : V.orthogonalProjectionFn x = (V.orthogonalProjectionOnto x : Point) :=
        Submodule.orthogonalProjectionFn_eq x
      have h_clm : submoduleProj V x = (V.orthogonalProjectionOnto x : Point) := by rfl
      rw [h_fn, h_clm]
    have h1 : V.orthogonalProjectionFn u = (1 / ‖w‖) • V.orthogonalProjectionFn w := by
      rw [h_proj_eq u, h_proj_eq w]
      exact (submoduleProj V).map_smul (1 / ‖w‖) w
    rw [h1]
    have h2 : u - (1 / ‖w‖) • V.orthogonalProjectionFn w =
        (1 / ‖w‖) • (w - V.orthogonalProjectionFn w) := by
      calc
        u - (1 / ‖w‖) • V.orthogonalProjectionFn w
          = (1 / ‖w‖) • w - (1 / ‖w‖) • V.orthogonalProjectionFn w := by rfl
        _ = (1 / ‖w‖) • (w - V.orthogonalProjectionFn w) := by
          exact (smul_sub (1 / ‖w‖) w (V.orthogonalProjectionFn w)).symm
    rw [h2, norm_smul]
    have h_abs : |1 / ‖w‖| = 1 / ‖w‖ := by
      rw [abs_of_pos (by positivity)]
    have h_goal : |1 / ‖w‖| * ‖w - V.orthogonalProjectionFn w‖ =
        ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ := by
      rw [h_abs]
      <;> field_simp [hnorm_w.ne'] <;> ring
    exact h_goal
  rw [h_scale]
  have h3 : ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ ≤ (4 * r) / ‖w‖ := by
    gcongr
    <;> linarith
  exact h3

end RadialBootstrapping
