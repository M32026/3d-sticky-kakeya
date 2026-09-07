module

/-
  FullMetricOverlap.lean

  Bounded overlap for the full-metric-separated tubeFamily.

  Key result: `tubeFamily_overlap_bound`
  For x, y at distance ξ, the number of lines L ∈ tubeFamily r with
  x, y ∈ tube(2r, L) is at most C / ξ.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.BoundedOverlapHelpers
public import MyLeanRepo.RadialBootstrapping.TubeFamilies

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

/-- Membership criterion for grid lines: x ∈ tube(2r, lineOfAngleOffset θ a)
    iff |dot x (normalVec θ) - a| < 2r. -/
lemma grid_tube_member (θ a r : ℝ) (hr : 0 < r) (x : Point) :
    x ∈ tube (2 * r) (lineOfAngleOffset θ a) ↔
      |dot x (normalVec θ) - a| < 2 * r := by
  let L := lineOfAngleOffset θ a
  constructor
  · intro hx
    rcases (Metric.mem_thickening_iff (E := L.toSet) (x := x)).mp hx
      with ⟨z, hz, hdist⟩
    have h_dot_eq : dot z (normalVec θ) = a :=
      lineOfAngleOffset_dot_eq θ a hz
    have h : |dot x (normalVec θ) - a| ≤ ‖x - z‖ := by
      have h7 : dot x (normalVec θ) - a = dot (x - z) (normalVec θ) := by
        rw [dot_sub_left, h_dot_eq] <;> ring
      rw [h7]
      have h8 : |dot (x - z) (normalVec θ)| ≤ ‖x - z‖ * ‖normalVec θ‖ :=
        abs_dot_le_norm (x - z) (normalVec θ)
      rw [normalVec_norm θ] at h8 <;> linarith
    have h9 : ‖x - z‖ < 2 * r := by simpa [dist_eq_norm] using hdist
    linarith
  · intro h
    rcases lineOfAngleOffset_projection θ a x with ⟨q, hq_mem, hq_norm⟩
    have h' : ‖x - q‖ < 2 * r := by
      rw [hq_norm]; exact h
    have h'' : dist x q < 2 * r := by
      simpa [dist_eq_norm] using h'
    exact (Metric.mem_thickening_iff (E := L.toSet) (x := x)).mpr
      ⟨q, hq_mem, h''⟩

/-- arcsin x ≤ (π/2) * x for 0 ≤ x ≤ 1. -/
lemma arcsin_le_pi_div_two_mul (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  have h1 : 0 ≤ Real.arcsin x := Real.arcsin_nonneg.mpr hx1
  have h2 : Real.arcsin x ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have h3 : -1 ≤ x := by linarith
  have h4 : Real.sin (Real.arcsin x) = x := Real.sin_arcsin h3 hx2
  have h5 : (2 / Real.pi) * (Real.arcsin x) ≤ Real.sin (Real.arcsin x) :=
    Real.mul_le_sin h1 h2
  rw [h4] at h5
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h6 : (2 / Real.pi) * (Real.arcsin x) ≤ x := h5
  have h7 : (Real.pi / 2) * ((2 / Real.pi) * Real.arcsin x) = Real.arcsin x := by
    have h9 : (Real.pi / 2) * (2 / Real.pi) = 1 := by
      field_simp [hpi_pos.ne'] <;> ring
    rw [← mul_assoc, h9, one_mul]
  have h10 : (Real.pi / 2) * ((2 / Real.pi) * Real.arcsin x) ≤ (Real.pi / 2) * x := by
    gcongr
  rw [h7] at h10
  exact h10

/-- Count grid angles in an open interval of length L. -/
lemma angle_grid_count_le (r : ℝ) (hr : 0 < r) (L : ℝ) (hL : 0 ≤ L)
    (a b : ℝ) (h_len : b - a ≤ L) :
    ((angleSet r).filter (fun k : ℕ => a < angleVal r k ∧ angleVal r k < b)).card ≤
      Nat.ceil (L * (numAngles r : ℝ) / Real.pi) + 1 := by
  set nθ : ℕ := numAngles r with hnθ
  have hΔ_pos : 0 < delta r := by dsimp only [delta]; positivity
  have h_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]
    apply Nat.ceil_pos.mpr
    exact div_pos Real.pi_pos hΔ_pos
  let s : ℝ := Real.pi / (nθ : ℝ)
  have hs_pos : 0 < s := by positivity
  let S := (angleSet r).filter (fun k : ℕ => a < angleVal r k ∧ angleVal r k < b)
  by_cases h_empty : S.Nonempty
  · let k_min := S.min' h_empty
    let k_max := S.max' h_empty
    have h_kmin_mem : k_min ∈ S := Finset.min'_mem S h_empty
    have h_kmax_mem : k_max ∈ S := Finset.max'_mem S h_empty
    have h1 : k_min ≤ k_max := Finset.min'_le S k_max h_kmax_mem
    have h2 : S ⊆ Finset.Icc k_min k_max := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
    have h3 : S.card ≤ (Finset.Icc k_min k_max).card := Finset.card_le_card h2
    have h4 : angleVal r k_max - angleVal r k_min ≤ b - a := by
      have h_amin : a < angleVal r k_min := (Finset.mem_filter.mp h_kmin_mem).2.1
      have h_bmax : angleVal r k_max < b := (Finset.mem_filter.mp h_kmax_mem).2.2
      linarith
    have h5 : angleVal r k_max - angleVal r k_min = ((k_max : ℝ) - (k_min : ℝ)) * s := by
      simp [angleVal, s] <;> ring
    have h6 : ((k_max : ℝ) - (k_min : ℝ)) * s ≤ L := by linarith [h4, h_len, h5]
    have h7 : (k_max : ℝ) - (k_min : ℝ) ≤ L / s := by
      calc (k_max : ℝ) - (k_min : ℝ)
        = (((k_max : ℝ) - (k_min : ℝ)) * s) / s := by field_simp [hs_pos.ne'] <;> ring
      _ ≤ L / s := by gcongr
    have h8 : L / s = L * (nθ : ℝ) / Real.pi := by
      simp [s] <;> field_simp [h_pos.ne'] <;> ring
    have h9 : (k_max : ℝ) - (k_min : ℝ) ≤ L * (nθ : ℝ) / Real.pi := by
      rw [h8] at h7; exact h7
    have h10 : (k_max : ℝ) - (k_min : ℝ) ≤ (Nat.ceil (L * (nθ : ℝ) / Real.pi) : ℝ) := by
      calc (k_max : ℝ) - (k_min : ℝ)
        ≤ L * (nθ : ℝ) / Real.pi := h9
      _ ≤ (Nat.ceil (L * (nθ : ℝ) / Real.pi) : ℝ) := Nat.le_ceil _
    have h11 : k_max - k_min ≤ Nat.ceil (L * (nθ : ℝ) / Real.pi) := by
      exact_mod_cast h10
    have h12 : (Finset.Icc k_min k_max).card = k_max - k_min + 1 := by
      rw [Nat.card_Icc] <;> omega
    rw [h12] at h3
    have h13 : S.card ≤ k_max - k_min + 1 := h3
    have h14 : k_max - k_min + 1 ≤ Nat.ceil (L * (nθ : ℝ) / Real.pi) + 1 := by omega
    exact le_trans h13 h14
  · have hS : S = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    have h : S.card = 0 := by rw [hS] <;> simp
    rw [h] <;> omega

/-- Strict version: if both y,z lie in the open 2r-tube of L, then
    direction distance is strictly less than 4r/‖z-y‖. -/
lemma direction_closeness_strict (r : ℝ) (hr : 0 < r)
    (L : Line2) (y z : Point) (hne : z ≠ y)
    (hy : y ∈ tube (2 * r) L) (hz : z ∈ tube (2 * r) L) :
    submoduleDirDist L.toAffine.direction (Submodule.span ℝ {z - y}) <
      4 * r / ‖z - y‖ := by
  let V := L.toAffine.direction
  let w : Point := z - y
  have hw0 : w ≠ 0 := by
    intro h; exact hne (sub_eq_zero.mp h)
  have hnorm_w : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let u : Point := (1 / ‖w‖) • w
  have hnu : ‖u‖ = 1 := by
    simp [u, norm_smul, hnorm_w.ne'] <;> field_simp [hnorm_w.ne'] <;> ring_nf <;> norm_num
  have huW : u ∈ Submodule.span ℝ {w} := by
    rw [Submodule.mem_span_singleton]; refine' ⟨1 / ‖w‖, _⟩; simp [u] <;> ring
  have hW1 : Module.finrank ℝ (Submodule.span ℝ {w}) = 1 := by
    rw [finrank_span_singleton hw0] <;> norm_num
  have h_perp_orth : ∀ (x : Point), ‖x - V.orthogonalProjectionFn x‖ ≤ ‖x‖ := by
    intro x
    have h4 : Vᗮ.orthogonalProjectionFn x = x - V.orthogonalProjectionFn x :=
      Submodule.starProjection_orthogonal_val (K := V) x
    rw [← h4]; exact Submodule.norm_starProjection_apply_le Vᗮ x
  rcases Metric.mem_thickening_iff.mp hy with ⟨y', hy'L, hy'⟩
  rcases Metric.mem_thickening_iff.mp hz with ⟨z', hz'L, hz'⟩
  have h1 : z' - y' ∈ V := AffineSubspace.vsub_mem_direction hz'L hy'L
  have h2 : V.orthogonalProjectionFn (z' - y') = z' - y' := by
    have h3 : V.orthogonalProjectionOnto (z' - y') = ⟨z' - y', h1⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨z' - y', h1⟩
    have h4 : (V.orthogonalProjectionOnto (z' - y') : Point) = z' - y' :=
      congr_arg (fun (x : V) => (x : Point)) h3
    exact h4
  have h4 : (z - y) - V.orthogonalProjectionFn (z - y) =
      ((z - z') - V.orthogonalProjectionFn (z - z')) +
      ((y' - y) - V.orthogonalProjectionFn (y' - y)) := by
    have h5 : z - y = (z - z') + (z' - y') + (y' - y) := by abel
    simp only [h5, map_add, h2] <;> abel
  have h5 : ‖z - z'‖ < 2 * r := by
    have h51 : dist z z' < 2 * r := hz'
    simpa [dist_eq_norm] using h51
  have h6 : ‖y' - y‖ < 2 * r := by
    have h61 : dist y y' < 2 * r := hy'
    have h62 : ‖y - y'‖ < 2 * r := by simpa [dist_eq_norm] using h61
    have h63 : ‖y' - y‖ = ‖y - y'‖ := norm_sub_rev y' y
    rw [h63]; exact h62
  have h7 : ‖(z - z') - V.orthogonalProjectionFn (z - z')‖ +
        ‖(y' - y) - V.orthogonalProjectionFn (y' - y)‖ < 4 * r := by
    have h71 : ‖(z - z') - V.orthogonalProjectionFn (z - z')‖ ≤ ‖z - z'‖ := h_perp_orth _
    have h72 : ‖(y' - y) - V.orthogonalProjectionFn (y' - y)‖ ≤ ‖y' - y‖ := h_perp_orth _
    linarith
  have h_sum : ‖((z - z') - V.orthogonalProjectionFn (z - z')) +
        ((y' - y) - V.orthogonalProjectionFn (y' - y))‖ ≤
      ‖(z - z') - V.orthogonalProjectionFn (z - z')‖ +
      ‖(y' - y) - V.orthogonalProjectionFn (y' - y)‖ := norm_add_le _ _
  have h_perp : ‖w - V.orthogonalProjectionFn w‖ < 4 * r := by
    rw [h4] at *
    <;> linarith
  have h_id : submoduleDirDist V (Submodule.span ℝ {w}) =
      ‖u - V.orthogonalProjectionFn u‖ :=
    submoduleDirDist_eq_perp V (Submodule.span ℝ {w}) L.2 hW1 u huW hnu
  rw [h_id]
  have h_proj_eq : ∀ (x : Point), V.orthogonalProjectionFn x = submoduleProj V x := by
    intro x
    have h_fn : V.orthogonalProjectionFn x = (V.orthogonalProjectionOnto x : Point) :=
      Submodule.orthogonalProjectionFn_eq x
    have h_clm : submoduleProj V x = (V.orthogonalProjectionOnto x : Point) := by rfl
    rw [h_fn, h_clm]
  have h1 : V.orthogonalProjectionFn u = (1 / ‖w‖) • V.orthogonalProjectionFn w := by
    rw [h_proj_eq u, h_proj_eq w]
    exact (submoduleProj V).map_smul (1 / ‖w‖) w
  have h_scale : ‖u - V.orthogonalProjectionFn u‖ =
      ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ := by
    rw [h1]
    have h2 : u - (1 / ‖w‖) • V.orthogonalProjectionFn w =
        (1 / ‖w‖) • (w - V.orthogonalProjectionFn w) := by
      calc u - (1 / ‖w‖) • V.orthogonalProjectionFn w
        = (1 / ‖w‖) • w - (1 / ‖w‖) • V.orthogonalProjectionFn w := by rfl
      _ = (1 / ‖w‖) • (w - V.orthogonalProjectionFn w) := by
        exact (smul_sub (1 / ‖w‖) w (V.orthogonalProjectionFn w)).symm
    rw [h2]
    have h3 : ‖(1 / ‖w‖) • (w - V.orthogonalProjectionFn w)‖ =
        ‖(1 / ‖w‖ : ℝ)‖ * ‖w - V.orthogonalProjectionFn w‖ := norm_smul _ _
    rw [h3]
    have h4 : ‖(1 / ‖w‖ : ℝ)‖ = 1 / ‖w‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h4] <;> field_simp [hnorm_w.ne'] <;> ring
  rw [h_scale]
  have h3 : ‖w - V.orthogonalProjectionFn w‖ / ‖w‖ < (4 * r) / ‖w‖ := by
    gcongr
    <;> linarith
  exact h3

/-- Direction distance between line with normal angle θ and span of u=(cos φ, sin φ)
    equals |cos(θ - φ)|. -/
lemma dirDist_lineOfAngle_span (θ φ : ℝ) (u : Point)
    (hu_norm : ‖u‖ = 1) (hcos : u 0 = Real.cos φ) (hsin : u 1 = Real.sin φ) :
    submoduleDirDist (lineOfAngleOffset θ 0).toAffine.direction (Submodule.span ℝ {u}) =
      |Real.cos (θ - φ)| := by
  let V := (lineOfAngleOffset θ 0).toAffine.direction
  let v := dirVec θ
  have hvV : v ∈ V := by
    have h_dir : V = (lineOfAngleOffset θ 0).toAffine.direction := by rfl
    rw [h_dir]
    have h : (lineOfAngleOffset θ 0).toAffine.direction = Submodule.span ℝ {dirVec θ} :=
      lineOfAngleOffset_aff_direction θ 0
    rw [h]
    have h_span : ({dirVec θ} : Set Point) ⊆ Submodule.span ℝ {dirVec θ} := Submodule.subset_span
    have hv_in : v ∈ ({dirVec θ} : Set Point) := by
      simp only [Set.mem_singleton_iff] <;> rfl
    exact h_span hv_in
  have hv_norm : ‖v‖ = 1 := norm_dirVec θ
  have hV : Module.finrank ℝ V = 1 := lineOfAngleOffset_finrank θ 0
  have hW1 : Module.finrank ℝ (Submodule.span ℝ {u}) = 1 := by
    have h_u_ne_zero : u ≠ 0 := by
      intro h
      rw [h] at hu_norm
      simp at hu_norm <;> norm_num at hu_norm <;> linarith
    exact finrank_span_singleton h_u_ne_zero
  have hu_mem : u ∈ Submodule.span ℝ {u} :=
    Submodule.subset_span (show u ∈ ({u} : Set Point) from by simp)
  have h_id : submoduleDirDist V (Submodule.span ℝ {u}) = ‖u - V.orthogonalProjectionFn u‖ :=
    submoduleDirDist_eq_perp V (Submodule.span ℝ {u}) hV hW1 u hu_mem hu_norm
  have hproj : V.orthogonalProjectionFn u = inner ℝ u v • v :=
    projection_one_dim V v u hvV hv_norm hV
  have h_inner : inner ℝ u v = -Real.sin (θ - φ) := by
    rw [inner_fin2]
    rw [hcos, hsin, dirVec_component0 θ, dirVec_component1 θ]
    <;> rw [Real.sin_sub] <;> ring
  have h_main : ‖u - inner ℝ u v • v‖ = Real.sqrt (1 - (inner ℝ u v) ^ 2) := by
    have h_norm : ‖u - inner ℝ u v • v‖ ^ 2 = 1 - (inner ℝ u v) ^ 2 := by
      have h51 := norm_sub_sq_real u (inner ℝ u v • v)
      have h5 : ‖u - inner ℝ u v • v‖ ^ 2 =
          ‖u‖ ^ 2 + ‖inner ℝ u v • v‖ ^ 2 - 2 * inner ℝ u (inner ℝ u v • v) := by linarith
      rw [h5]
      have h7 : ‖inner ℝ u v • v‖ ^ 2 = (inner ℝ u v) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, hv_norm] <;> simp [sq_abs]
      have h8 : inner ℝ u (inner ℝ u v • v) = (inner ℝ u v) ^ 2 := by
        rw [inner_smul_right] <;> ring
      rw [h7, h8, hu_norm] <;> ring
    have h_nonneg : 0 ≤ ‖u - inner ℝ u v • v‖ := by positivity
    rw [← Real.sqrt_sq h_nonneg, h_norm]
  calc
    submoduleDirDist V (Submodule.span ℝ {u})
      = ‖u - V.orthogonalProjectionFn u‖ := h_id
    _ = ‖u - inner ℝ u v • v‖ := by rw [hproj]
    _ = Real.sqrt (1 - (inner ℝ u v) ^ 2) := h_main
    _ = Real.sqrt (1 - Real.sin (θ - φ) ^ 2) := by rw [h_inner] <;> ring_nf
    _ = Real.sqrt (Real.cos (θ - φ) ^ 2) := by
      have h12 : Real.sin (θ - φ) ^ 2 + Real.cos (θ - φ) ^ 2 = 1 := by
        have h13 := Real.cos_sq_add_sin_sq (θ - φ)
        linarith
      have h13 : 1 - Real.sin (θ - φ) ^ 2 = Real.cos (θ - φ) ^ 2 := by linarith
      rw [h13]
    _ = |Real.cos (θ - φ)| := by rw [Real.sqrt_sq_eq_abs]

/-- If |sin t| < c with 0 ≤ c ≤ 1, then there exists m : ℤ such that
    |t - m*π| < arcsin(c). -/
lemma sin_lt_implies_near_multiple_pi (t c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (h : |Real.sin t| < c) :
    ∃ (m : ℤ), |t - (m : ℝ) * Real.pi| < Real.arcsin c := by
  let m : ℤ := Int.floor (t / Real.pi + 1 / 2)
  let t' := t - (m : ℝ) * Real.pi
  have h1 : -Real.pi / 2 ≤ t' := by
    have h2 : (m : ℝ) ≤ t / Real.pi + 1 / 2 := Int.floor_le _
    have h3 : (m : ℝ) * Real.pi ≤ t + Real.pi / 2 := by
      have h4 : 0 < Real.pi := Real.pi_pos
      calc (m : ℝ) * Real.pi
        ≤ (t / Real.pi + 1 / 2) * Real.pi := by gcongr
      _ = t + Real.pi / 2 := by
        field_simp [h4.ne'] <;> ring
    have h5 : t - (m : ℝ) * Real.pi ≥ -Real.pi / 2 := by linarith
    exact h5
  have h2 : t' ≤ Real.pi / 2 := by
    have h3 : t / Real.pi + 1 / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one _
    have h4 : t + Real.pi / 2 < (m : ℝ) * Real.pi + Real.pi := by
      have h5 : 0 < Real.pi := Real.pi_pos
      calc t + Real.pi / 2
        = (t / Real.pi + 1 / 2) * Real.pi := by field_simp [h5.ne'] <;> ring
      _ < ((m : ℝ) + 1) * Real.pi := by gcongr
      _ = (m : ℝ) * Real.pi + Real.pi := by ring
    have h6 : t - (m : ℝ) * Real.pi < Real.pi / 2 := by linarith
    exact h6.le
  have h3 : |Real.sin t'| = |Real.sin t| := by
    have h4 : Real.sin t' = Real.sin (t + (-m : ℤ) * Real.pi) := by
      have h5 : t' = t + (-m : ℤ) * Real.pi := by
        simp [t'] <;> ring
      rw [h5]
    rw [h4]
    have h5 : Real.sin (t + (-m : ℤ) * Real.pi) =
        (-1 : ℝ) ^ (-m : ℤ) * Real.sin t := Real.sin_add_int_mul_pi t (-m)
    rw [h5, abs_mul]
    have h6 : |(-1 : ℝ) ^ (-m : ℤ)| = 1 := by
      rw [abs_zpow]
      <;> norm_num
    rw [h6, one_mul]
  have h4 : |Real.sin t'| < c := by rw [h3]; exact h
  have h_abs_sin_eq : |Real.sin t'| = Real.sin |t'| := by
    by_cases h9 : 0 ≤ t'
    · have h10 : |t'| = t' := abs_of_nonneg h9
      rw [h10]
      have h11 : 0 ≤ Real.sin t' := Real.sin_nonneg_of_nonneg_of_le_pi h9 (by linarith)
      rw [abs_of_nonneg h11]
    · have h10 : t' < 0 := by linarith
      have h11 : |t'| = -t' := abs_of_neg h10
      rw [h11]
      have h12 : Real.sin (-t') = -Real.sin t' := by rw [Real.sin_neg]
      rw [h12]
      have h13 : Real.sin t' ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
      rw [abs_of_nonpos h13] <;> ring
  have h5 : Real.sin |t'| < c := by
    rw [← h_abs_sin_eq]; exact h4
  have h6 : 0 ≤ |t'| := by positivity
  have h7 : |t'| ≤ Real.pi / 2 := by rw [abs_le] <;> constructor <;> linarith
  have hα : 0 ≤ Real.arcsin c := Real.arcsin_nonneg.mpr hc
  have hα' : -(Real.pi / 2) ≤ Real.arcsin c := by linarith [Real.pi_pos]
  have h_sinα : Real.sin (Real.arcsin c) = c := Real.sin_arcsin (by linarith) hc1
  have h8 : |t'| < Real.arcsin c := by
    by_contra h9
    have h10 : Real.arcsin c ≤ |t'| := by linarith
    have h11 : Real.sin (Real.arcsin c) ≤ Real.sin |t'| :=
      Real.sin_le_sin_of_le_of_le_pi_div_two hα' h7 h10
    rw [h_sinα] at h11
    linarith [h5]
  exact ⟨m, by simpa [t'] using h8⟩

/-- If n : ℤ satisfies -3/2 < (n : ℝ) < 3/2, then n ∈ {-1, 0, 1}. -/
lemma int_in_short_interval (n : ℤ) (h1 : -3 / 2 < (n : ℝ)) (h2 : (n : ℝ) < 3 / 2) :
    n = -1 ∨ n = 0 ∨ n = 1 := by
  have h3 : n ≥ -1 := by
    by_contra h4
    have h5 : n ≤ -2 := by omega
    have h6 : (n : ℝ) ≤ -2 := by exact_mod_cast h5
    linarith [h1]
  have h4 : n ≤ 1 := by
    by_contra h5
    have h6 : n ≥ 2 := by omega
    have h7 : (n : ℝ) ≥ 2 := by exact_mod_cast h6
    linarith [h2]
  have h5 : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  exact h5

/-- Count valid angles: given a partition of valid_angles by m-value,
    bound the total count by 3 * (ceil_bound + 1). -/
lemma angle_count_lemma (nθ : ℕ) (α : ℝ) (valid_angles : Finset ℕ)
    (F : ℤ → Finset ℕ)
    (h_per_m : ∀ (mval : ℤ), mval ∈ ({-1, 0, 1} : Finset ℤ) →
      ((F mval).card : ℝ) ≤ (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1)
    (h_angle_card : valid_angles.card ≤
      ∑ mval ∈ ({-1, 0, 1} : Finset ℤ), (F mval).card) :
    (valid_angles.card : ℝ) ≤
      3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) := by
  let M_finset : Finset ℤ := ({-1, 0, 1} : Finset ℤ)
  let X : ℝ := (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1
  have h7 : (valid_angles.card : ℝ) ≤ ∑ mval ∈ M_finset, ((F mval).card : ℝ) := by
    have h71 : (valid_angles.card : ℝ) ≤ ↑(∑ mval ∈ M_finset, (F mval).card) := by
      exact_mod_cast h_angle_card
    have h_sum_cast : (↑(∑ mval ∈ M_finset, (F mval).card) : ℝ) =
        ∑ mval ∈ M_finset, ((F mval).card : ℝ) := by
      rw [Nat.cast_sum]
    rw [h_sum_cast] at h71
    exact h71
  have h8 : ∑ mval ∈ M_finset, ((F mval).card : ℝ) ≤ ∑ mval ∈ M_finset, X := by
    exact Finset.sum_le_sum (fun mval _ => h_per_m mval ‹_›)
  have h91 : M_finset.card = 3 := by decide
  have h9 : ∑ mval ∈ M_finset, X = 3 * X := by
    rw [Finset.sum_const, h91] <;> ring
  rw [h9] at h8
  exact le_trans h7 h8

/-- Bound on numAngles: `↑(numAngles r) ≤ Real.pi / Δ + 1`. -/
lemma nθ_bound_lemma (r : ℝ) (hr : 0 < r) (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (h_eq : Δ = r / 10) (nθ : ℕ) (hnθ_eq : nθ = Nat.ceil (Real.pi / Δ)) :
    (nθ : ℝ) ≤ Real.pi / Δ + 1 := by
  rw [hnθ_eq]
  have hpos : 0 ≤ Real.pi / Δ := div_nonneg Real.pi_pos.le hΔ_pos.le
  have h_main : (Nat.ceil (Real.pi / Δ) : ℝ) < Real.pi / Δ + 1 :=
    Nat.ceil_lt_add_one hpos
  exact h_main.le

/-- At most 41 offset grid points lie in an open interval of length 4r. -/
lemma offset_packing_bound (r : ℝ) (hr : 0 < r) (a0 : ℝ) :
    ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card ≤ 41 := by
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  let S := (offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)
  by_cases h_empty : S.Nonempty
  · let j_min := S.min' h_empty
    let j_max := S.max' h_empty
    have h_jmin_mem : j_min ∈ S := Finset.min'_mem S h_empty
    have h_jmax_mem : j_max ∈ S := Finset.max'_mem S h_empty
    have h1 : j_min ≤ j_max := Finset.min'_le S j_max h_jmax_mem
    have h2 : S ⊆ Finset.Icc j_min j_max := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
    have h3 : |offsetVal r j_min - a0| < 2 * r := (Finset.mem_filter.mp h_jmin_mem).2
    have h4 : |offsetVal r j_max - a0| < 2 * r := (Finset.mem_filter.mp h_jmax_mem).2
    have h5 : offsetVal r j_max - offsetVal r j_min < 4 * r := by
      have h31 : a0 - 2 * r < offsetVal r j_min := by linarith [abs_lt.mp h3]
      have h41 : offsetVal r j_max < a0 + 2 * r := by linarith [abs_lt.mp h4]
      linarith
    have h6 : ((j_max : ℝ) - (j_min : ℝ)) * Δ < 4 * r := by
      have h7 : offsetVal r j_max - offsetVal r j_min = ((j_max : ℝ) - (j_min : ℝ)) * Δ := by
        simp [offsetVal] <;> ring
      rw [h7] at h5; exact h5
    have h8 : (j_max : ℝ) - (j_min : ℝ) < 40 := by
      have h9 : Δ = r / 10 := by dsimp only [Δ, delta] <;> ring
      rw [h9] at h6
      have h10 : 0 < r := hr
      have h11 : ((j_max : ℝ) - (j_min : ℝ)) * (r / 10) < 4 * r := h6
      have h12 : (j_max : ℝ) - (j_min : ℝ) < 40 := by
        nlinarith
      exact h12
    have h13 : j_max - j_min ≤ 39 := by
      by_contra h14
      have h15 : j_max - j_min ≥ 40 := by omega
      have h16 : (j_max : ℝ) - (j_min : ℝ) ≥ 40 := by exact_mod_cast h15
      linarith [h8]
    have h14 : S.card ≤ (Finset.Icc j_min j_max).card := Finset.card_le_card h2
    have h15 : (Finset.Icc j_min j_max).card = j_max - j_min + 1 := by
      rw [Nat.card_Icc] <;> omega
    have h16 : S.card ≤ 41 := by
      calc S.card
        ≤ (Finset.Icc j_min j_max).card := h14
      _ = j_max - j_min + 1 := h15
      _ ≤ 39 + 1 := by gcongr
      _ = 40 := by norm_num
      _ ≤ 41 := by norm_num
    exact h16
  · have hS : S = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h_empty
    have h_goal : S.card ≤ 41 := by
      calc S.card
        = 0 := by rw [hS] <;> simp
      _ ≤ 41 := by norm_num
    exact h_goal

set_option maxHeartbeats 500000

/-- Bounded overlap for tubeFamily: at most 20000/ξ lines contain both x and y
    in their 2r-tubes, where ξ = dist(x,y), assuming x,y in unit ball. -/
lemma tubeFamily_overlap_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ) (h_small : 4 * r / ξ ≤ 1)
    (x y : Point) (hxy : ξ ≤ dist x y)
    (hxBall : x ∈ Metric.closedBall (0 : Point) 1)
    (hyBall : y ∈ Metric.closedBall (0 : Point) 1) :
    (((tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card : ℝ) ≤
      20000 / ξ := by
  set ξ' : ℝ := dist x y with hξ'_def
  have hξ'_pos : 0 < ξ' := by have h : 0 < ξ := hξ; linarith [hxy]
  have hξ'_le : ξ ≤ ξ' := hxy
  have hξ'_le_two : ξ' ≤ 2 := by
    have h1 : dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
    have h2 : dist x 0 ≤ 1 := by simpa [Metric.mem_closedBall] using hxBall
    have h3 : dist y 0 ≤ 1 := by simpa [Metric.mem_closedBall] using hyBall
    have h4 : dist 0 y = dist y 0 := dist_comm 0 y
    rw [h4] at h1
    have h5 : dist x 0 + dist y 0 ≤ 2 := by
      have h6 : dist x 0 + dist y 0 ≤ 1 + 1 := add_le_add h2 h3
      norm_num at h6 ⊢ <;> exact h6
    exact le_trans h1 h5
  have h_small' : 4 * r / ξ' ≤ 1 := by
    have h : 4 * r / ξ' ≤ 4 * r / ξ := by gcongr <;> linarith
    exact h.trans h_small
  set Δ : ℝ := delta r with hΔ
  have hΔ_pos : 0 < Δ := by dsimp only [Δ, delta]; positivity
  set nθ : ℕ := numAngles r with hnθ
  have h_nθ_pos : 0 < nθ := by
    dsimp only [nθ, numAngles]; apply Nat.ceil_pos.mpr
    exact div_pos Real.pi_pos hΔ_pos

  -- Find φ such that u = (x-y)/ξ' = (cos φ, sin φ)
  let v : Point := x - y
  have hnorm_v : ‖v‖ = ξ' := by simp [v, hξ'_def, dist_eq_norm]
  let u : Point := (1 / ξ') • v
  have hu_norm : ‖u‖ = 1 := by
    have h : ‖u‖ = |1 / ξ'| * ‖v‖ := by simpa [u, norm_smul] using rfl
    rw [h, abs_of_pos (by positivity), hnorm_v]
    <;> field_simp [hξ'_pos.ne'] <;> ring
  have h_norm2 : ‖u‖ ^ 2 = ∑ i : Fin 2, (u i)^2 := EuclideanSpace.real_norm_sq_eq u
  have h_sum : (∑ i : Fin 2, (u i)^2) = u 0 ^ 2 + u 1 ^ 2 := by
    simp [Fin.sum_univ_two] <;> ring
  have hu1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have h : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by rw [h_norm2, h_sum]
    have h2 : ‖u‖ ^ 2 = 1 := by rw [hu_norm] <;> norm_num
    linarith [h, h2]
  have h_u0_abs : -1 ≤ u 0 ∧ u 0 ≤ 1 := by
    have h : u 0 ^ 2 ≤ 1 := by nlinarith
    constructor <;> nlinarith
  let φ : ℝ := if 0 ≤ u 1 then Real.arccos (u 0) else -Real.arccos (u 0)
  have hcos : Real.cos φ = u 0 := by
    simp only [φ]; split_ifs with h
    · rw [Real.cos_arccos] <;> linarith [h_u0_abs]
    · rw [Real.cos_neg, Real.cos_arccos] <;> linarith [h_u0_abs]
  have hsin : Real.sin φ = u 1 := by
    simp only [φ]; split_ifs with h
    · have h_pos : 0 ≤ u 1 := h
      have h_sin_arccos : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - u 0 ^ 2) := Real.sin_arccos (u 0)
      rw [h_sin_arccos]
      have h2 : u 1 ^ 2 = 1 - u 0 ^ 2 := by nlinarith
      have h3 : Real.sqrt (1 - u 0 ^ 2) = u 1 := by
        have h4 : Real.sqrt (1 - u 0 ^ 2) = Real.sqrt (u 1 ^ 2) := by rw [h2]
        rw [h4, Real.sqrt_sq h_pos]
      rw [h3]
    · have h_neg : u 1 < 0 := by linarith
      rw [Real.sin_neg]
      have h_sin_arccos : Real.sin (Real.arccos (u 0)) = Real.sqrt (1 - u 0 ^ 2) := Real.sin_arccos (u 0)
      rw [h_sin_arccos]
      have h2 : u 1 ^ 2 = 1 - u 0 ^ 2 := by nlinarith
      have h3 : Real.sqrt (1 - u 0 ^ 2) = -u 1 := by
        have h41 : 0 ≤ -u 1 := by linarith
        have h4 : Real.sqrt (1 - u 0 ^ 2) = Real.sqrt ((-u 1) ^ 2) := by
          have h5 : 1 - u 0 ^ 2 = (-u 1) ^ 2 := by nlinarith
          rw [h5]
        rw [h4, Real.sqrt_sq h41]
      rw [h3] <;> ring

  let c : ℝ := 4 * r / ξ'
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le_one : c ≤ 1 := h_small'
  let α : ℝ := Real.arcsin c
  have hα_nonneg : 0 ≤ α := Real.arcsin_nonneg.mpr hc_nonneg
  have hα_le : α ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two c
  have h_sinα : Real.sin α = c := Real.sin_arcsin (by linarith) hc_le_one
  have hL_angle : 2 * α ≤ 4 * Real.pi * r / ξ' := by
    have h1 : α ≤ (Real.pi / 2) * c := arcsin_le_pi_div_two_mul c hc_nonneg hc_le_one
    have h2 : 2 * α ≤ 2 * ((Real.pi / 2) * c) := by gcongr
    have h3 : 2 * ((Real.pi / 2) * c) = Real.pi * c := by ring
    have h4 : Real.pi * c = 4 * Real.pi * r / ξ' := by dsimp only [c] <;> ring
    linarith

  -- θ0 in [0, π), congruent to φ + π/2 mod π
  let θ0_raw : ℝ := φ + Real.pi / 2
  let nπ : ℤ := Int.floor (θ0_raw / Real.pi)
  let θ0 : ℝ := θ0_raw - (nπ : ℝ) * Real.pi
  have hθ0_nonneg : 0 ≤ θ0 := by
    have h : (nπ : ℝ) ≤ θ0_raw / Real.pi := Int.floor_le (θ0_raw / Real.pi)
    have h2 : (nπ : ℝ) * Real.pi ≤ θ0_raw := by
      calc (nπ : ℝ) * Real.pi
        ≤ (θ0_raw / Real.pi) * Real.pi := by gcongr
      _ = θ0_raw := by field_simp [Real.pi_pos.ne'] <;> ring
    linarith [show θ0 = θ0_raw - (nπ : ℝ) * Real.pi from rfl]
  have hθ0_lt_pi : θ0 < Real.pi := by
    have h : θ0_raw / Real.pi < (nπ : ℝ) + 1 := Int.lt_floor_add_one (θ0_raw / Real.pi)
    have h2 : θ0_raw < ((nπ : ℝ) + 1) * Real.pi := by
      calc θ0_raw
        = (θ0_raw / Real.pi) * Real.pi := by field_simp [Real.pi_pos.ne'] <;> ring
      _ < ((nπ : ℝ) + 1) * Real.pi := by gcongr
    linarith [show θ0 = θ0_raw - (nπ : ℝ) * Real.pi from rfl]

  have h_sin_eq : ∀ (θ : ℝ), |Real.sin (θ - θ0)| = |Real.cos (θ - φ)| := by
    intro θ
    have h5 : θ - θ0 = θ - φ - Real.pi / 2 + (nπ : ℝ) * Real.pi := by
      simp [θ0] <;> ring
    rw [h5]
    have h6 : Real.sin (θ - φ - Real.pi / 2 + (nπ : ℝ) * Real.pi) =
        (-1 : ℝ) ^ (nπ : ℤ) * Real.sin (θ - φ - Real.pi / 2) := by
      rw [Real.sin_add_int_mul_pi]
    rw [h6]
    have h7 : |(-1 : ℝ) ^ (nπ : ℤ)| = 1 := by
      rw [abs_zpow] <;> norm_num
    have h8 : Real.sin (θ - φ - Real.pi / 2) = -Real.cos (θ - φ) := by
      rw [Real.sin_sub]
      <;> simp [Real.cos_pi_div_two, Real.sin_pi_div_two] <;> ring
    rw [h8, abs_mul, h7, one_mul, abs_neg]

  -- Valid angles: |sin(angleVal r k - θ0)| < c
  let valid_angles : Finset ℕ := (angleSet r).filter (fun k => |Real.sin (angleVal r k - θ0)| < c)

  -- For each valid angle, find m : ℤ with |angleVal r k - θ0 - m*π| < α
  have h_exists : ∀ (k : ℕ), k ∈ valid_angles →
      ∃ (m : ℤ), |angleVal r k - θ0 - (m : ℝ) * Real.pi| < α := by
    intro k hk
    have h : |Real.sin (angleVal r k - θ0)| < c := (Finset.mem_filter.mp hk).2
    exact sin_lt_implies_near_multiple_pi (angleVal r k - θ0) c hc_nonneg hc_le_one h
  have h_exists_total : ∀ (k : ℕ), ∃ (m : ℤ), k ∈ valid_angles →
      |angleVal r k - θ0 - (m : ℝ) * Real.pi| < α := by
    intro k
    by_cases hk : k ∈ valid_angles
    · rcases h_exists k hk with ⟨m, hm⟩
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => False.elim (hk h)⟩
  choose m hm using h_exists_total

  -- m ∈ {-1, 0, 1} because angleVal r k - θ0 ∈ (-π, π) and α ≤ π/2
  have h_m_range : ∀ k ∈ valid_angles, m k ∈ ({-1, 0, 1} : Finset ℤ) := by
    intro k hk
    have h_k2 : k ∈ angleSet r := (Finset.mem_filter.mp hk).1
    have h_k3 : k < nθ := by
      simp only [angleSet] at h_k2 <;> exact Finset.mem_range.mp h_k2
    have h_k_pos : 0 < (nθ : ℝ) := by exact_mod_cast h_nθ_pos
    have h_ang_nonneg : 0 ≤ angleVal r k := by
      have h : angleVal r k = (k : ℝ) * Real.pi / (nθ : ℝ) := by simp [angleVal] <;> ring
      rw [h]; positivity
    have h_ang_lt : angleVal r k < Real.pi := by
      have h : angleVal r k = (k : ℝ) * Real.pi / (nθ : ℝ) := by simp [angleVal] <;> ring
      rw [h]
      have h4 : (k : ℝ) < (nθ : ℝ) := by exact_mod_cast h_k3
      have h5 : (k : ℝ) * Real.pi < (nθ : ℝ) * Real.pi := mul_lt_mul_of_pos_right h4 Real.pi_pos
      calc (k : ℝ) * Real.pi / (nθ : ℝ)
        < ((nθ : ℝ) * Real.pi) / (nθ : ℝ) := by gcongr
      _ = Real.pi := by field_simp [h_k_pos.ne'] <;> ring
    have h_t1 : -Real.pi < angleVal r k - θ0 := by linarith [hθ0_lt_pi]
    have h_t2 : angleVal r k - θ0 < Real.pi := by linarith [hθ0_nonneg]
    have h_m1 : |angleVal r k - θ0 - (m k : ℝ) * Real.pi| < α := hm k hk
    have h_m4 : (m k : ℝ) * Real.pi - α < angleVal r k - θ0 := by linarith [abs_lt.mp h_m1]
    have h_m5 : angleVal r k - θ0 < (m k : ℝ) * Real.pi + α := by linarith [abs_lt.mp h_m1]
    have h_m6 : (m k : ℝ) * Real.pi < Real.pi + α := by linarith
    have h_m7 : -Real.pi - α < (m k : ℝ) * Real.pi := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have h_m8 : (m k : ℝ) < 1 + α / Real.pi := by
      have h : (m k : ℝ) * Real.pi < Real.pi + α := h_m6
      calc (m k : ℝ)
        = ((m k : ℝ) * Real.pi) / Real.pi := by field_simp [hpi.ne'] <;> ring
      _ < (Real.pi + α) / Real.pi := by gcongr
      _ = 1 + α / Real.pi := by field_simp [hpi.ne'] <;> ring
    have h_m9 : -1 - α / Real.pi < (m k : ℝ) := by
      have h : -Real.pi - α < (m k : ℝ) * Real.pi := h_m7
      calc -1 - α / Real.pi
        = (-Real.pi - α) / Real.pi := by field_simp [hpi.ne'] <;> ring
      _ < ((m k : ℝ) * Real.pi) / Real.pi := by gcongr
      _ = (m k : ℝ) := by field_simp [hpi.ne'] <;> ring
    have h_m10 : (m k : ℝ) < 3 / 2 := by
      have hα2 : α / Real.pi ≤ 1 / 2 := by
        have h : α ≤ Real.pi / 2 := hα_le
        have hpi : 0 < Real.pi := Real.pi_pos
        calc α / Real.pi
          ≤ (Real.pi / 2) / Real.pi := by gcongr
        _ = 1 / 2 := by field_simp [hpi.ne'] <;> ring
      linarith [h_m8, hα2]
    have h_m11 : -3 / 2 < (m k : ℝ) := by
      have hα2 : α / Real.pi ≤ 1 / 2 := by
        have h : α ≤ Real.pi / 2 := hα_le
        have hpi : 0 < Real.pi := Real.pi_pos
        calc α / Real.pi
          ≤ (Real.pi / 2) / Real.pi := by gcongr
        _ = 1 / 2 := by field_simp [hpi.ne'] <;> ring
      linarith [h_m9, hα2]
    have h_m12 : m k = -1 ∨ m k = 0 ∨ m k = 1 :=
      int_in_short_interval (m k) h_m11 h_m10
    rcases h_m12 with (h13 | h13 | h13)
    · have h14 : (-1 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14
    · have h14 : (0 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14
    · have h14 : (1 : ℤ) ∈ ({-1, 0, 1} : Finset ℤ) := by decide
      exact h13.symm ▸ h14

  -- Per-m angle count using angle_grid_count_le
  have h2α_pos : 0 ≤ 2 * α := by positivity
  have h_per_m : ∀ (mval : ℤ), mval ∈ ({-1, 0, 1} : Finset ℤ) →
      ((valid_angles.filter (fun k => m k = mval)).card : ℝ) ≤
        (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1 := by
    intro mval _
    let S_m := valid_angles.filter (fun k => m k = mval)
    have h1 : ∀ k ∈ S_m, angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α) := by
      intro k hk
      have h2 : k ∈ valid_angles := (Finset.mem_filter.mp hk).1
      have h3 : m k = mval := (Finset.mem_filter.mp hk).2
      have h4 : |angleVal r k - θ0 - (m k : ℝ) * Real.pi| < α := hm k h2
      rw [h3] at h4
      have h4' : -α < angleVal r k - θ0 - (mval : ℝ) * Real.pi ∧
          angleVal r k - θ0 - (mval : ℝ) * Real.pi < α := abs_lt.mp h4
      simp only [Set.mem_Ioo]
      constructor
      · linarith [h4'.1]
      · linarith [h4'.2]
    have h2 : S_m ⊆ (angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α)) := by
      intro k hk
      have h3 : k ∈ valid_angles := (Finset.mem_filter.mp hk).1
      have h4 : k ∈ angleSet r := (Finset.mem_filter.mp h3).1
      exact Finset.mem_filter.mpr ⟨h4, h1 k hk⟩
    have h3 : S_m.card ≤ ((angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α))).card :=
      Finset.card_le_card h2
    have h4 : ((angleSet r).filter (fun k => angleVal r k ∈ Set.Ioo ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α))).card ≤
        Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) + 1 :=
      angle_grid_count_le r hr (2 * α) h2α_pos ((mval : ℝ) * Real.pi + θ0 - α) ((mval : ℝ) * Real.pi + θ0 + α) (by linarith)
    have h5 : S_m.card ≤ Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) + 1 :=
      le_trans h3 h4
    exact_mod_cast h5

  -- Total angle count via partition by m
  let M_finset : Finset ℤ := ({-1, 0, 1} : Finset ℤ)
  have h_partition : valid_angles ⊆ Finset.biUnion M_finset (fun mval => valid_angles.filter (fun k => m k = mval)) := by
    intro k hk
    have h5 : m k ∈ M_finset := h_m_range k hk
    exact Finset.mem_biUnion.mpr ⟨m k, h5, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
  have h_disj : ∀ m1 m2 : ℤ, m1 ≠ m2 → Disjoint (valid_angles.filter (fun k => m k = m1)) (valid_angles.filter (fun k => m k = m2)) := by
    intro m1 m2 hne
    rw [Finset.disjoint_left]
    intro k hk1
    have h_eq1 : m k = m1 := (Finset.mem_filter.mp hk1).2
    intro hk2
    have h_eq2 : m k = m2 := (Finset.mem_filter.mp hk2).2
    have h_cont : m1 = m2 := by rw [← h_eq1, h_eq2]
    exact hne h_cont
  have h_angle_card : valid_angles.card ≤ ∑ mval ∈ M_finset, (valid_angles.filter (fun k => m k = mval)).card := by
    have h5 : valid_angles.card ≤ (Finset.biUnion M_finset (fun mval => valid_angles.filter (fun k => m k = mval))).card :=
      Finset.card_le_card h_partition
    have h6 : (Finset.biUnion M_finset (fun mval => valid_angles.filter (fun k => m k = mval))).card =
        ∑ mval ∈ M_finset, (valid_angles.filter (fun k => m k = mval)).card := by
      rw [Finset.card_biUnion (fun i _ j _ hne => h_disj i j hne)]
    rw [h6] at h5
    exact h5
  have h_angle_count : (valid_angles.card : ℝ) ≤
      3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) :=
    angle_count_lemma nθ α valid_angles
      (fun mval => valid_angles.filter (fun k => m k = mval))
      h_per_m
      h_angle_card

  -- Clear heavy hypotheses to avoid context bloat
  clear h_per_m h_disj h_partition h_angle_card h_exists hm m h_m_range

  -- nθ bound
  have h_nθ_eq : nθ = Nat.ceil (Real.pi / Δ) := by
    dsimp only [nθ, numAngles] <;> rfl
  have h_nθ_le : (nθ : ℝ) ≤ Real.pi / Δ + 1 :=
    nθ_bound_lemma r hr Δ hΔ_pos (by rfl) nθ h_nθ_eq

  -- Ceil bound
  have h_ceil : Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) ≤
      Nat.ceil ((40 * Real.pi + 4) / ξ') := by
    have h_pos3 : 0 ≤ (nθ : ℝ) / Real.pi := by positivity
    have h1 : (2 * α) * (nθ : ℝ) / Real.pi ≤ (4 * Real.pi * r / ξ') * (nθ : ℝ) / Real.pi := by
      have h : (2 * α) * ((nθ : ℝ) / Real.pi) ≤ (4 * Real.pi * r / ξ') * ((nθ : ℝ) / Real.pi) :=
        mul_le_mul_of_nonneg_right hL_angle h_pos3
      have h_goal : (2 * α) * (nθ : ℝ) / Real.pi = (2 * α) * ((nθ : ℝ) / Real.pi) := by ring
      have h_rhs : (4 * Real.pi * r / ξ') * (nθ : ℝ) / Real.pi = (4 * Real.pi * r / ξ') * ((nθ : ℝ) / Real.pi) := by ring
      rw [h_goal, h_rhs]
      exact h
    have h2 : (4 * Real.pi * r / ξ') * (nθ : ℝ) / Real.pi = (4 * r / ξ') * (nθ : ℝ) := by
      field_simp [Real.pi_pos.ne'] <;> ring
    rw [h2] at h1
    have h_pos4 : 0 ≤ 4 * r / ξ' := by positivity
    have h3 : (4 * r / ξ') * (nθ : ℝ) ≤ (4 * r / ξ') * (Real.pi / Δ + 1) :=
      mul_le_mul_of_nonneg_left h_nθ_le h_pos4
    have h41 : Real.pi / Δ = 10 * Real.pi / r := by
      dsimp only [Δ, delta]
      field_simp [hr.ne'] <;> ring
    have h4 : (4 * r / ξ') * (Real.pi / Δ + 1) = (40 * Real.pi + 4 * r) / ξ' := by
      rw [h41]
      have h43 : 10 * Real.pi / r + 1 = (10 * Real.pi + r) / r := by
        field_simp [hr.ne'] <;> ring
      rw [h43]
      field_simp [hr.ne', hξ'_pos.ne'] <;> ring
    have h5 : (40 * Real.pi + 4 * r) / ξ' ≤ (40 * Real.pi + 4) / ξ' := by
      have h51 : 4 * r ≤ 4 := by linarith [hr1]
      have h52 : 40 * Real.pi + 4 * r ≤ 40 * Real.pi + 4 := by linarith
      exact div_le_div_of_nonneg_right h52 hξ'_pos.le
    have h6 : (2 * α) * (nθ : ℝ) / Real.pi ≤ (40 * Real.pi + 4) / ξ' := by
      calc (2 * α) * (nθ : ℝ) / Real.pi
        ≤ (4 * r / ξ') * (nθ : ℝ) := h1
      _ ≤ (4 * r / ξ') * (Real.pi / Δ + 1) := h3
      _ = (40 * Real.pi + 4 * r) / ξ' := h4
      _ ≤ (40 * Real.pi + 4) / ξ' := h5
    exact Nat.ceil_mono h6

  -- Angle count numeric bound
  have h_angle_count2 : (valid_angles.card : ℝ) ≤ (120 * Real.pi + 24) / ξ := by
    set X : ℝ := (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1 with hX
    have h7 : (valid_angles.card : ℝ) ≤ 3 * X := h_angle_count
    have h8 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) < (40 * Real.pi + 4) / ξ' + 1 := by
      have h9 : (Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) ≤
          (Nat.ceil ((40 * Real.pi + 4) / ξ') : ℝ) := by exact_mod_cast h_ceil
      have h_pos : 0 ≤ (40 * Real.pi + 4) / ξ' := by positivity
      have h10 : (Nat.ceil ((40 * Real.pi + 4) / ξ') : ℝ) < (40 * Real.pi + 4) / ξ' + 1 :=
        Nat.ceil_lt_add_one h_pos
      linarith
    have h9 : (valid_angles.card : ℝ) ≤ 3 * ((40 * Real.pi + 4) / ξ' + 2) := by
      have h10 : 3 * X = 3 * ((Nat.ceil ((2 * α) * (nθ : ℝ) / Real.pi) : ℝ) + 1) := by
        simp [hX] <;> ring
      rw [h10] at h7
      linarith
    have h10 : 3 * ((40 * Real.pi + 4) / ξ' + 2) = 3 * (40 * Real.pi + 4) / ξ' + 6 := by ring
    rw [h10] at h9
    have h11 : 6 ≤ 12 / ξ' := by
      have h12 : ξ' ≤ 2 := hξ'_le_two
      have h13 : 0 < ξ' := hξ'_pos
      have h14 : 6 * ξ' ≤ 12 := by linarith
      calc (6 : ℝ)
        = 6 * ξ' / ξ' := by field_simp [h13.ne'] <;> ring
      _ ≤ 12 / ξ' := by gcongr
    have h13 : 3 * (40 * Real.pi + 4) / ξ' + 6 ≤ 3 * (40 * Real.pi + 4) / ξ' + 12 / ξ' := by gcongr
    have h14 : 3 * (40 * Real.pi + 4) / ξ' + 12 / ξ' = (120 * Real.pi + 24) / ξ' := by ring
    have h15 : (120 * Real.pi + 24) / ξ' ≤ (120 * Real.pi + 24) / ξ := by
      have h16 : ξ ≤ ξ' := hξ'_le
      have h17 : 0 ≤ 120 * Real.pi + 24 := by positivity
      exact div_le_div_of_nonneg_left h17 hξ h16
    linarith

  -- For each valid angle, at most 41 offsets
  have h_offset_count : ∀ (k : ℕ), k ∈ valid_angles →
      ((offsetSet r).filter (fun j =>
        x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
        y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)))).card ≤ 41 := by
    intro k _
    let a0 := dot x (normalVec (angleVal r k))
    let S_off := (offsetSet r).filter (fun j =>
      x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
      y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)))
    have h1 : ∀ j ∈ S_off, |offsetVal r j - a0| < 2 * r := by
      intro j hj
      have h2 : |a0 - offsetVal r j| < 2 * r :=
        grid_tube_member (angleVal r k) (offsetVal r j) r hr x |>.mp
          (Finset.mem_filter.mp hj).2.1
      have h3 : |offsetVal r j - a0| = |a0 - offsetVal r j| := by
        rw [abs_sub_comm]
      rw [h3]
      exact h2
    have h2 : S_off ⊆ (offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, h1 j hj⟩
    have h3 : S_off.card ≤ ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card :=
      Finset.card_le_card h2
    have h5 : ((offsetSet r).filter (fun j => |offsetVal r j - a0| < 2 * r)).card ≤ 41 :=
      offset_packing_bound r hr a0
    linarith

  -- Preimage: pairs (k,j) whose line contains both x,y
  let preimage : Finset (ℕ × ℕ) := (angleSet r ×ˢ offsetSet r).filter (fun ⟨k, j⟩ =>
    x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
    y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)))
  let f : ℕ × ℕ → Line2 := fun ⟨k, j⟩ => lineOfAngleOffset (angleVal r k) (offsetVal r j)

  have h_main_card : (((tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card : ℝ) ≤
      (preimage.card : ℝ) := by
    have h_image : (tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L) ⊆
        preimage.image f := by
      intro L hL
      have hL_in : L ∈ tubeFamily r := (Finset.mem_filter.mp hL).1
      have hL_cond := (Finset.mem_filter.mp hL).2
      rcases Finset.mem_image.mp hL_in with ⟨⟨k, j⟩, hkj, rfl⟩
      have h_in_pre : (k, j) ∈ preimage := Finset.mem_filter.mpr ⟨hkj, hL_cond⟩
      exact Finset.mem_image.mpr ⟨(k, j), h_in_pre, rfl⟩
    have h1 : ((tubeFamily r).filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card ≤
        (preimage.image f).card := Finset.card_le_card h_image
    have h2 : (preimage.image f).card ≤ preimage.card := Finset.card_image_le
    exact_mod_cast le_trans h1 h2

  -- Key: preimage angles are valid angles (direction closeness)
  let P : ℕ → ℕ → Prop := fun k j =>
    x ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j)) ∧
    y ∈ tube (2 * r) (lineOfAngleOffset (angleVal r k) (offsetVal r j))

  have h_preimage_valid : ∀ (k j : ℕ), (k, j) ∈ preimage → k ∈ valid_angles := by
    intro k j hkj
    have h_kj_in : (k, j) ∈ angleSet r ×ˢ offsetSet r := (Finset.mem_filter.mp hkj).1
    have h_k_ang : k ∈ angleSet r := (Finset.mem_product.mp h_kj_in).1
    have hP : P k j := (Finset.mem_filter.mp hkj).2
    let L_k := lineOfAngleOffset (angleVal r k) (offsetVal r j)
    have hxL : x ∈ tube (2 * r) L_k := hP.1
    have hyL : y ∈ tube (2 * r) L_k := hP.2
    have hne : y ≠ x := by
      intro h
      have h' : ξ' = 0 := by
        simp [hξ'_def, h, dist_eq_norm]
      exact hξ'_pos.ne' h'
    have hne' : x ≠ y := hne.symm
    have h_dir : submoduleDirDist L_k.toAffine.direction (Submodule.span ℝ {x - y}) < c := by
      have h := direction_closeness_strict r hr L_k y x hne' hyL hxL
      simpa [c, hξ'_def, dist_eq_norm] using h
    have h_Lk_def : L_k = lineOfAngleOffset (angleVal r k) (offsetVal r j) := by rfl
    have h_dir_same : L_k.toAffine.direction = (lineOfAngleOffset (angleVal r k) 0).toAffine.direction := by
      have h1 : L_k.toAffine.direction = Submodule.span ℝ {dirVec (angleVal r k)} := by
        rw [h_Lk_def]
        exact lineOfAngleOffset_aff_direction (angleVal r k) (offsetVal r j)
      have h2 : (lineOfAngleOffset (angleVal r k) 0).toAffine.direction = Submodule.span ℝ {dirVec (angleVal r k)} :=
        lineOfAngleOffset_aff_direction (angleVal r k) 0
      exact Eq.trans h1 h2.symm
    rw [h_dir_same] at h_dir
    have h9 : u = (1 / ξ') • (x - y) := by simp [u] <;> rfl
    have h10 : IsUnit (1 / ξ') := by
      apply IsUnit.mk0
      positivity
    have h_span : Submodule.span ℝ {x - y} = Submodule.span ℝ {u} := by
      have h11 : Submodule.span ℝ {u} = Submodule.span ℝ {(1 / ξ') • (x - y)} := by
        congr 1 <;> simp [u, h9] <;> abel
      rw [h11]
      exact (Submodule.span_singleton_smul_eq h10 (x - y)).symm
    rw [h_span] at h_dir
    have h_eq : submoduleDirDist (lineOfAngleOffset (angleVal r k) 0).toAffine.direction (Submodule.span ℝ {u}) =
        |Real.cos (angleVal r k - φ)| :=
      dirDist_lineOfAngle_span (angleVal r k) φ u hu_norm hcos.symm hsin.symm
    rw [h_eq] at h_dir
    have h_final : |Real.sin (angleVal r k - θ0)| < c := by
      rw [h_sin_eq (angleVal r k)]
      exact h_dir
    exact Finset.mem_filter.mpr ⟨h_k_ang, h_final⟩

  have h_preimage_eq : preimage = (valid_angles ×ˢ offsetSet r).filter (fun ⟨k, j⟩ => P k j) := by
    ext ⟨k, j⟩
    simp only [preimage, P, Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      have h1 : (k ∈ angleSet r ∧ j ∈ offsetSet r) ∧ P k j := h
      have h2 : P k j := h1.2
      have h_in_prod : (k, j) ∈ angleSet r ×ˢ offsetSet r := Finset.mem_product.mpr h1.1
      have h3 : k ∈ valid_angles := h_preimage_valid k j (Finset.mem_filter.mpr ⟨h_in_prod, h2⟩)
      have h4 : j ∈ offsetSet r := h1.1.2
      exact ⟨⟨h3, h4⟩, h2⟩
    · intro h
      have h1 : (k ∈ valid_angles ∧ j ∈ offsetSet r) ∧ P k j := h
      have h2 : P k j := h1.2
      have h3 : k ∈ angleSet r := (Finset.mem_filter.mp h1.1.1).1
      have h4 : j ∈ offsetSet r := h1.1.2
      exact ⟨⟨h3, h4⟩, h2⟩

  have h_preimage_bound : (preimage.card : ℝ) ≤ (valid_angles.card : ℝ) * 41 := by
    rw [h_preimage_eq]
    let Q : ℕ → Finset ℕ := fun k => (offsetSet r).filter (fun j => P k j)
    have h21 : (valid_angles ×ˢ offsetSet r).filter (fun ⟨k, j⟩ => P k j) =
        Finset.biUnion valid_angles (fun k => {k} ×ˢ Q k) := by
      ext ⟨k, j⟩
      simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_singleton, Finset.mem_product]
      constructor
      · intro h
        exact ⟨k, h.1.1, rfl, h.1.2, h.2⟩
      · rintro ⟨k', hk', rfl, hj, hP⟩
        exact ⟨⟨hk', hj⟩, hP⟩
    rw [h21]
    have h22 : ∀ k1 k2 : ℕ, k1 ≠ k2 → Disjoint ({k1} ×ˢ Q k1) ({k2} ×ˢ Q k2) := by
      intro k1 k2 hne
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : x.1 ∈ {k1} := (Finset.mem_product.mp hx1).1
      have h1' : x.1 = k1 := Finset.mem_singleton.mp h1
      have h2 : x.1 ∈ {k2} := (Finset.mem_product.mp hx2).1
      have h2' : x.1 = k2 := Finset.mem_singleton.mp h2
      have h3 : k1 = k2 := by rw [←h1', h2']
      exact hne h3
    have h22' : Set.PairwiseDisjoint (valid_angles : Set ℕ) (fun k => {k} ×ˢ Q k) := by
      intro k1 _ k2 _ hne
      exact h22 k1 k2 hne
    rw [Finset.card_biUnion h22']
    have h23 : ∑ k ∈ valid_angles, ({k} ×ˢ Q k).card = ∑ k ∈ valid_angles, (Q k).card := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.card_product]
      <;> simp
    rw [h23]
    have h24 : ∑ k ∈ valid_angles, (Q k).card ≤ ∑ k ∈ valid_angles, (41 : ℕ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact h_offset_count k hk
    have h25 : ∑ k ∈ valid_angles, (41 : ℕ) = valid_angles.card * 41 := by
      simp [Finset.sum_const, mul_comm] <;> ring
    rw [h25] at h24
    exact_mod_cast h24

  -- Final bound
  have h_final : (preimage.card : ℝ) ≤ ((120 * Real.pi + 24) / ξ) * 41 := by
    calc (preimage.card : ℝ)
      ≤ (valid_angles.card : ℝ) * 41 := h_preimage_bound
    _ ≤ ((120 * Real.pi + 24) / ξ) * 41 := by gcongr

  have h_const : (120 * Real.pi + 24) * 41 < 20000 := by
    have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
    nlinarith [Real.pi_pos]

  have h_final2 : (preimage.card : ℝ) < 20000 / ξ := by
    have h5 : (preimage.card : ℝ) ≤ ((120 * Real.pi + 24) / ξ) * 41 := h_final
    have h6 : ((120 * Real.pi + 24) / ξ) * 41 < 20000 / ξ := by
      have h7 : 0 < ξ := hξ
      have h8 : (120 * Real.pi + 24) * 41 < 20000 := h_const
      have h9 : ((120 * Real.pi + 24) / ξ) * 41 = ((120 * Real.pi + 24) * 41) / ξ := by ring
      rw [h9]
      gcongr
    linarith

  have h_final3 : (preimage.card : ℝ) ≤ 20000 / ξ := by
    exact h_final2.le

  exact h_main_card.trans h_final3

end RadialBootstrapping

end
