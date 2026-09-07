import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoveringConstruction
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.ImageGeometry
import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ Lemma 8 anisotropic rediscretization: package the three-tube image cover
with the bounded-base certificate required by `IsProjectionExtremalPair`.
-/

namespace Kakeya.Assouad

/--
Given a meeting point between the axis and the extended slab, construct clipped
endpoint parameters t1, t2 that themselves lie in the extended slab.

This strengthens `axis_slab_parameter_bounds_clipped` by certifying the
z-coordinate membership of the clipped endpoints, which is needed to transfer
the source unit-ball bound to target basepoints via
`anisotropicImage_tube_axis_norm_le_two`.
-/
lemma axis_slab_clipped_with_z_of_meet
    {base dir : Point3} {c d delta : ℝ}
    (hdelta : 0 ≤ delta) (hcd : c < d)
    (hdir_unit : ‖dir‖ = 1) (hdir_z : 1 / 2 ≤ |dir 2|)
    (t_meet : ℝ) (ht_meet1 : t_meet ∈ Set.Icc (0 : ℝ) 1)
    (ht_meet2 : (base + t_meet • dir) 2 ∈ Set.Icc (c - delta) (d + delta)) :
    ∃ t1 t2 : ℝ,
      t1 ∈ Set.Icc (0 : ℝ) 1 ∧
      t2 ∈ Set.Icc (0 : ℝ) 1 ∧
      t1 ≤ t2 ∧
      (base + t1 • dir) 2 ∈ Set.Icc (c - delta) (d + delta) ∧
      (base + t2 • dir) 2 ∈ Set.Icc (c - delta) (d + delta) ∧
      (∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta) →
        t ∈ Set.Icc t1 t2) ∧
      (t2 - t1) * |dir 2| ≤ d - c + 2 * delta := by
  have hdir2_ne : dir 2 ≠ 0 := by
    intro h
    rw [h] at hdir_z
    norm_num at hdir_z
  let a : ℝ := (c - delta - base 2) / dir 2
  let b : ℝ := (d + delta - base 2) / dir 2
  let lo : ℝ := min a b
  let hi : ℝ := max a b
  have h_lo_le_hi : lo ≤ hi := min_le_max
  have h_iff : ∀ (t : ℝ), (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta) ↔ t ∈ Set.Icc lo hi := by
    intro t
    have hz : (base + t • dir) 2 = base 2 + t * dir 2 := by simp
    rw [hz]
    constructor
    · intro h
      have h1 : c - delta ≤ base 2 + t * dir 2 := h.1
      have h2 : base 2 + t * dir 2 ≤ d + delta := h.2
      by_cases hpos : 0 < dir 2
      · have h_ab : a ≤ b := by
          have h : (c - delta : ℝ) ≤ d + delta := by linarith
          have h' : (c - delta - base 2) ≤ (d + delta - base 2) := by linarith
          exact div_le_div_of_nonneg_right h' (by linarith)
        have hlo : lo = a := by
          rw [show lo = min a b from rfl, min_eq_left h_ab]
        have hhi : hi = b := by
          rw [show hi = max a b from rfl, max_eq_right h_ab]
        rw [hlo, hhi]
        have h3 : a ≤ t := by
          have h4 : (t - a) * dir 2 ≥ 0 := by
            have h5 : (t - a) * dir 2 = (base 2 + t * dir 2) - (c - delta) := by
              simp [a] <;> field_simp [hdir2_ne] <;> ring
            rw [h5] <;> linarith
          nlinarith
        have h6 : t ≤ b := by
          have h7 : (b - t) * dir 2 ≥ 0 := by
            have h8 : (b - t) * dir 2 = (d + delta) - (base 2 + t * dir 2) := by
              simp [b] <;> field_simp [hdir2_ne] <;> ring
            rw [h8] <;> linarith
          nlinarith
        exact ⟨h3, h6⟩
      · have hneg : dir 2 < 0 := by
          by_contra h
          have : dir 2 = 0 := by linarith
          exact hdir2_ne this
        have h_ba : b ≤ a := by
          have h : (c - delta - base 2) ≤ (d + delta - base 2) := by linarith
          have h' : ((d + delta - base 2) - (c - delta - base 2)) ≥ 0 := by linarith
          have h'' : (((d + delta - base 2) - (c - delta - base 2)) / dir 2) ≤ 0 := by
            exact div_nonpos_of_nonneg_of_nonpos h' (by linarith)
          have h3 : b - a = (((d + delta - base 2) - (c - delta - base 2)) / dir 2) := by
            simp [a, b] <;> field_simp [hdir2_ne] <;> ring
          linarith
        have hlo : lo = b := by
          rw [show lo = min a b from rfl, min_eq_right h_ba]
        have hhi : hi = a := by
          rw [show hi = max a b from rfl, max_eq_left h_ba]
        rw [hlo, hhi]
        have h3 : b ≤ t := by
          have h4 : (t - b) * dir 2 ≤ 0 := by
            have h5 : (t - b) * dir 2 = (base 2 + t * dir 2) - (d + delta) := by
              simp [b] <;> field_simp [hdir2_ne] <;> ring
            rw [h5] <;> linarith
          nlinarith
        have h6 : t ≤ a := by
          have h7 : (a - t) * dir 2 ≤ 0 := by
            have h8 : (a - t) * dir 2 = (c - delta) - (base 2 + t * dir 2) := by
              simp [a] <;> field_simp [hdir2_ne] <;> ring
            rw [h8] <;> linarith
          nlinarith
        exact ⟨h3, h6⟩
    · intro h
      have h1 : lo ≤ t := h.1
      have h2 : t ≤ hi := h.2
      by_cases hpos : 0 < dir 2
      · have h_ab : a ≤ b := by
          have h : (c - delta : ℝ) ≤ d + delta := by linarith
          have h' : (c - delta - base 2) ≤ (d + delta - base 2) := by linarith
          exact div_le_div_of_nonneg_right h' (by linarith)
        have hlo : lo = a := by
          rw [show lo = min a b from rfl, min_eq_left h_ab]
        have hhi : hi = b := by
          rw [show hi = max a b from rfl, max_eq_right h_ab]
        rw [hlo] at h1
        rw [hhi] at h2
        have h3 : c - delta ≤ base 2 + t * dir 2 := by
          have h4 : (t - a) * dir 2 ≥ 0 := by exact mul_nonneg (by linarith) (by linarith)
          have h5 : (t - a) * dir 2 = (base 2 + t * dir 2) - (c - delta) := by
            simp [a] <;> field_simp [hdir2_ne] <;> ring
          linarith
        have h6 : base 2 + t * dir 2 ≤ d + delta := by
          have h7 : (b - t) * dir 2 ≥ 0 := by exact mul_nonneg (by linarith) (by linarith)
          have h8 : (b - t) * dir 2 = (d + delta) - (base 2 + t * dir 2) := by
            simp [b] <;> field_simp [hdir2_ne] <;> ring
          linarith
        exact ⟨h3, h6⟩
      · have hneg : dir 2 < 0 := by
          by_contra h
          have : dir 2 = 0 := by linarith
          exact hdir2_ne this
        have h_ba : b ≤ a := by
          have h : (c - delta - base 2) ≤ (d + delta - base 2) := by linarith
          have h' : ((d + delta - base 2) - (c - delta - base 2)) ≥ 0 := by linarith
          have h'' : (((d + delta - base 2) - (c - delta - base 2)) / dir 2) ≤ 0 := by
            exact div_nonpos_of_nonneg_of_nonpos h' (by linarith)
          have h3 : b - a = (((d + delta - base 2) - (c - delta - base 2)) / dir 2) := by
            simp [a, b] <;> field_simp [hdir2_ne] <;> ring
          linarith
        have hlo : lo = b := by
          rw [show lo = min a b from rfl, min_eq_right h_ba]
        have hhi : hi = a := by
          rw [show hi = max a b from rfl, max_eq_left h_ba]
        rw [hlo] at h1
        rw [hhi] at h2
        have h3 : c - delta ≤ base 2 + t * dir 2 := by
          have h4 : (a - t) * dir 2 ≤ 0 := by exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          have h5 : (a - t) * dir 2 = (c - delta) - (base 2 + t * dir 2) := by
            simp [a] <;> field_simp [hdir2_ne] <;> ring
          linarith
        have h6 : base 2 + t * dir 2 ≤ d + delta := by
          have h7 : (t - b) * dir 2 ≤ 0 := by exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          have h8 : (t - b) * dir 2 = (base 2 + t * dir 2) - (d + delta) := by
            simp [b] <;> field_simp [hdir2_ne] <;> ring
          linarith
        exact ⟨h3, h6⟩
  have h_meet_in_interval : t_meet ∈ Set.Icc lo hi := (h_iff t_meet).mp ht_meet2
  let t1 : ℝ := max 0 lo
  let t2 : ℝ := min 1 hi
  have h_t1_in : t1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_max_left _ _
    · have h : t1 ≤ t_meet := max_le ht_meet1.1 h_meet_in_interval.1
      linarith [ht_meet1.2]
  have h_t2_in : t2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have h : t_meet ≤ t2 := le_min ht_meet1.2 h_meet_in_interval.2
      linarith [ht_meet1.1]
    · exact min_le_left _ _
  have h_t1_le_t2 : t1 ≤ t2 := by
    have h1 : t1 ≤ t_meet := max_le ht_meet1.1 h_meet_in_interval.1
    have h2 : t_meet ≤ t2 := le_min ht_meet1.2 h_meet_in_interval.2
    linarith
  have h_t1_in_lohi : t1 ∈ Set.Icc lo hi := by
    constructor
    · exact le_max_right _ _
    · have h : t1 ≤ t_meet := max_le ht_meet1.1 h_meet_in_interval.1
      linarith [h_meet_in_interval.2]
  have h_t2_in_lohi : t2 ∈ Set.Icc lo hi := by
    constructor
    · have h : t_meet ≤ t2 := le_min ht_meet1.2 h_meet_in_interval.2
      linarith [h_meet_in_interval.1]
    · exact min_le_right _ _
  have h_z1 : (base + t1 • dir) 2 ∈ Set.Icc (c - delta) (d + delta) :=
    (h_iff t1).mpr h_t1_in_lohi
  have h_z2 : (base + t2 • dir) 2 ∈ Set.Icc (c - delta) (d + delta) :=
    (h_iff t2).mpr h_t2_in_lohi
  have h_bounds : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      (base + t • dir) 2 ∈ Set.Icc (c - delta) (d + delta) →
      t ∈ Set.Icc t1 t2 := by
    intro t ht hz
    have h_t_in_lohi : t ∈ Set.Icc lo hi := (h_iff t).mp hz
    exact ⟨max_le ht.1 h_t_in_lohi.1, le_min ht.2 h_t_in_lohi.2⟩
  have h_width : (t2 - t1) * |dir 2| ≤ d - c + 2 * delta := by
    have h1 : t2 - t1 ≤ hi - lo := by
      have h2 : t2 ≤ hi := min_le_right _ _
      have h3 : lo ≤ t1 := le_max_right _ _
      linarith
    have h4 : (hi - lo) * |dir 2| = d - c + 2 * delta := by
      by_cases hpos : 0 < dir 2
      · have h_ab : a ≤ b := by
          have h : (c - delta : ℝ) ≤ d + delta := by linarith
          have h' : (c - delta - base 2) ≤ (d + delta - base 2) := by linarith
          exact div_le_div_of_nonneg_right h' (by linarith)
        have hlo : lo = a := by
          rw [show lo = min a b from rfl, min_eq_left h_ab]
        have hhi : hi = b := by
          rw [show hi = max a b from rfl, max_eq_right h_ab]
        rw [hlo, hhi]
        have habs : |dir 2| = dir 2 := abs_of_pos hpos
        rw [habs]
        simp [a, b] <;> field_simp [hdir2_ne] <;> ring
      · have hneg : dir 2 < 0 := by
          by_contra h
          have : dir 2 = 0 := by linarith
          exact hdir2_ne this
        have h_ba : b ≤ a := by
          have h : (c - delta - base 2) ≤ (d + delta - base 2) := by linarith
          have h' : ((d + delta - base 2) - (c - delta - base 2)) ≥ 0 := by linarith
          have h'' : (((d + delta - base 2) - (c - delta - base 2)) / dir 2) ≤ 0 := by
            exact div_nonpos_of_nonneg_of_nonpos h' (by linarith)
          have h3 : b - a = (((d + delta - base 2) - (c - delta - base 2)) / dir 2) := by
            simp [a, b] <;> field_simp [hdir2_ne] <;> ring
          linarith
        have hlo : lo = b := by
          rw [show lo = min a b from rfl, min_eq_right h_ba]
        have hhi : hi = a := by
          rw [show hi = max a b from rfl, max_eq_left h_ba]
        rw [hlo, hhi]
        have habs : |dir 2| = -dir 2 := abs_of_neg hneg
        rw [habs]
        simp [a, b] <;> field_simp [hdir2_ne] <;> ring
    have h5 : (t2 - t1) * |dir 2| ≤ (hi - lo) * |dir 2| := by
      gcongr <;> exact abs_nonneg _
    rw [h4] at h5
    exact h5
  exact ⟨t1, t2, h_t1_in, h_t2_in, h_t1_le_t2, h_z1, h_z2, h_bounds, h_width⟩

/--
Bounded version of `cover_tube_image_three_rho_tubes`.

Covers the anisotropic image of a δ-tube slab intersection with 3 ρ-tubes,
and certifies that every covering tube basepoint has norm at most 3.
-/
lemma bounded_cover_tube_image_three_rho_tubes
    {δ c d g_mid K S rho : ℝ}
    (hdelta : 0 < δ) (hcd : c < d)
    (T : Kakeya.DeltaTube δ)
    (hdir_z : 1 / 2 ≤ |T.direction 2|)
    (hg : |g_mid| ≤ 1) (hK : |K| ≤ 1)
    (hS_eq : S = 2 / (d - c))
    (h_dc : d - c ≤ 1 / 25)
    (hdelta_small : δ ≤ 1 / 100)
    (hrho_small : 2 * δ / (d - c) ≤ 1 / 4)
    (hrho_eq : rho = S * δ)
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    (m : ℝ) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hK_def : K = m * (d - c) / 2)
    (hg_mid_def : g_mid = g (c + (d - c) / 2))
    (hT_ball : T.IsInUnitBall)
    (hseg : BoundedThreeSegmentCoverStatement) :
    ∃ (T1 T2 T3 : Kakeya.DeltaTube rho),
      (fun p : Point3 =>
        point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)) ''
        (T.carrier ∩ horizontalSlab c d) ⊆
      T1.carrier ∪ T2.carrier ∪ T3.carrier ∧
      (1 / 2 : ℝ) ≤ |T1.direction 2| ∧
      (1 / 2 : ℝ) ≤ |T2.direction 2| ∧
      (1 / 2 : ℝ) ≤ |T3.direction 2| ∧
      ‖T1.base‖ ≤ 3 ∧ ‖T2.base‖ ≤ 3 ∧ ‖T3.base‖ ≤ 3 := by
  let Φ : Point3 → Point3 := fun p =>
    point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)
  let A : Point3 → Point3 := fun p =>
    point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2)
  have hS_pos : 0 < S := by
    rw [hS_eq] <;> positivity
  have hS2 : 2 ≤ S := by
    rw [hS_eq]
    have h_pos : 0 < d - c := by linarith [hcd]
    have h_le : d - c ≤ 1 / 25 := h_dc
    have h : 2 / (d - c) ≥ 50 := by
      calc 2 / (d - c) ≥ 2 / (1 / 25 : ℝ) := by gcongr
        _ = 50 := by norm_num
    linarith
  have h_dist_bound : ∀ (x y : Point3), dist (Φ x) (Φ y) ≤ S * dist x y := by
    intro x y
    have h2 : Φ x - Φ y = A (x - y) := by
      ext i
      fin_cases i <;> simp [Φ, A, point3, Fin.sum_univ_succ] <;> ring
    have h3 : dist (Φ x) (Φ y) = ‖Φ x - Φ y‖ := by rw [dist_eq_norm]
    rw [h3, h2]
    have h4 : ‖A (x - y)‖ ≤ S * ‖x - y‖ := anisotropicMap_opNorm_bound hg hK hS2 (x - y)
    have h5 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    rw [h5] at *
    exact h4
  let axis := Kakeya.unitSegment T.base T.direction
  let E := axis ∩ horizontalSlab (c - δ) (d + δ)
  have h1 : T.carrier ∩ horizontalSlab c d ⊆ Metric.cthickening δ E := by
    intro x hx
    have hx1 : x ∈ T.carrier := hx.1
    have hx2 : x ∈ horizontalSlab c d := hx.2
    have h_xz : x 2 ∈ Set.Icc c d := hx2
    have h_axis_compact : IsCompact axis := by
      exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
    have hTcar : T.carrier = Metric.cthickening δ axis := by rfl
    rw [hTcar] at hx1
    have h_eq : Metric.cthickening δ axis = ⋃ y ∈ axis, Metric.closedBall y δ :=
      h_axis_compact.cthickening_eq_biUnion_closedBall (by positivity)
    rw [h_eq] at hx1
    have h_exists : ∃ y, y ∈ axis ∧ dist x y ≤ δ := by
      simpa [Set.mem_iUnion, Metric.closedBall] using hx1
    rcases h_exists with ⟨y, hy_axis, hdist⟩
    have h_yz : |y 2 - x 2| ≤ dist y x := by
      let v := y - x
      have h1 : (v 2)^2 ≤ ‖v‖^2 := by
        have h2 : ‖v‖^2 = ∑ i : Fin 3, (v i)^2 := by
          simpa using EuclideanSpace.real_norm_sq_eq v
        rw [h2]
        have h3 : (v 2)^2 ≤ ∑ i : Fin 3, (v i)^2 := by
          have h4 : (2 : Fin 3) ∈ Finset.univ := by simp
          exact Finset.single_le_sum (fun i _ => sq_nonneg (v i)) h4
        exact h3
      have h4 : |v 2| ≤ ‖v‖ := by
        have h5 : (|v 2|)^2 ≤ ‖v‖^2 := by
          rw [sq_abs] <;> exact h1
        have h6 : 0 ≤ |v 2| := abs_nonneg (v 2)
        have h7 : 0 ≤ ‖v‖ := norm_nonneg v
        nlinarith
      have h5 : |y 2 - x 2| = |v 2| := by
        have h6 : v 2 = y 2 - x 2 := by simp [v]
        rw [h6]
      rw [h5]
      simpa [dist_eq_norm, v] using h4
    have h_yz2 : y 2 ∈ Set.Icc (c - δ) (d + δ) := by
      have h_x1 : c ≤ x 2 := h_xz.1
      have h_x2 : x 2 ≤ d := h_xz.2
      have hdist' : dist y x ≤ δ := by rwa [dist_comm] at hdist
      have h : |y 2 - x 2| ≤ δ := by calc
          |y 2 - x 2| ≤ dist y x := h_yz
          _ ≤ δ := hdist'
      rw [abs_le] at h
      exact ⟨by linarith, by linarith⟩
    have hy_E : y ∈ E := ⟨hy_axis, h_yz2⟩
    exact Metric.mem_cthickening_of_dist_le x y δ E hy_E hdist
  have h_axis_compact : IsCompact axis := by
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have h_slab_closed : IsClosed (horizontalSlab (c - δ) (d + δ)) := by
    have h_cont : Continuous (fun x : Point3 => x 2) :=
      PiLp.continuous_apply (p := 2) (β := fun (_ : Fin 3) => ℝ) (2 : Fin 3)
    have h_ic : IsClosed (Set.Icc (c - δ) (d + δ)) := isClosed_Icc
    have h_pre : IsClosed ((fun x : Point3 => x 2) ⁻¹' Set.Icc (c - δ) (d + δ)) := h_ic.preimage h_cont
    have h_eq : horizontalSlab (c - δ) (d + δ) = (fun x : Point3 => x 2) ⁻¹' Set.Icc (c - δ) (d + δ) := by
      ext x; simp [horizontalSlab] <;> rfl
    rw [h_eq]
    exact h_pre
  have hE_compact : IsCompact E := h_axis_compact.inter_right h_slab_closed
  have h2 : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ Metric.cthickening (S * δ) (Φ '' E) := by
    have h21 : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ Φ '' Metric.cthickening δ E := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, h1 hw, rfl⟩
    have h22 : Φ '' Metric.cthickening δ E ⊆ Metric.cthickening (S * δ) (Φ '' E) :=
      image_cthickening_bound (by positivity) (by positivity) hE_compact h_dist_bound
    exact h21.trans h22
  let dir := T.direction
  let base := T.base
  have hdir_unit : ‖dir‖ = 1 := T.direction_unit
  have hΦ_affine : ∀ (t : ℝ), Φ (base + t • dir) = Φ base + t • (point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)) := by
    intro t
    ext i
    fin_cases i <;> simp [Φ, point3, smul_add, add_smul] <;> ring
  let Ad := point3 (dir 0 + g_mid * dir 1) (K * dir 1) (S * dir 2)
  have h_dc25 : d - c ≤ 1 / 25 := by linarith
  have hS : S = 2 / (d - c) := hS_eq
  have hAd_vert : (1 / 2 : ℝ) ≤ |Ad 2| / ‖Ad‖ := by
    have h_vert := anisotropicMap_preservesVerticalChart g hg_norm c d m hcd hm_pos hm_le_one h_dc25 h_sub dir hdir_unit hdir_z
    simpa [Ad, hK_def, hg_mid_def, hS] using h_vert
  have hΦ_eq : Φ = anisotropicRescalingMap g c d m := by
    funext p
    ext i
    fin_cases i
    · simp [Φ, anisotropicRescalingMap, point3, hg_mid_def, EuclideanSpace.single_apply] <;> ring
    · simp [Φ, anisotropicRescalingMap, point3, hK_def, EuclideanSpace.single_apply] <;> ring
    · simp [Φ, anisotropicRescalingMap, point3, hS_eq, EuclideanSpace.single_apply] <;> field_simp [hcd.ne'] <;> ring
  by_cases hmeet : ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      (base + t • dir) 2 ∈ Set.Icc (c - δ) (d + δ)
  · -- Non-degenerate case: axis meets extended slab
    rcases hmeet with ⟨t_meet, ht_meet1, ht_meet2⟩
    rcases axis_slab_clipped_with_z_of_meet (by linarith) hcd hdir_unit hdir_z t_meet ht_meet1 ht_meet2
      with ⟨t1, t2, ht1_mem, ht2_mem, h_t1_le_t2, h_z1, h_z2, h_bounds, h_width⟩
    let P := Φ (base + t1 • dir)
    let Q := Φ (base + t2 • dir)
    have h11 : Q = Φ base + t2 • Ad := by
      simpa [Q, Ad] using hΦ_affine t2
    have h12 : P = Φ base + t1 • Ad := by
      simpa [P, Ad] using hΦ_affine t1
    have h1 : Q - P = (t2 - t1) • Ad := by
      rw [h11, h12]
      simp [sub_smul, smul_sub] <;> abel
    have hP_norm : ‖P‖ ≤ 2 := by
      rw [show P = anisotropicRescalingMap g c d m (base + t1 • dir) from by rw [←hΦ_eq]]
      exact anisotropicImage_tube_axis_norm_le_two hg_norm (by linarith) hcd (by linarith) hm_le_one h_dc hrho_small h_sub T hT_ball ht1_mem h_z1
    have hQ_norm : ‖Q‖ ≤ 2 := by
      rw [show Q = anisotropicRescalingMap g c d m (base + t2 • dir) from by rw [←hΦ_eq]]
      exact anisotropicImage_tube_axis_norm_le_two hg_norm (by linarith) hcd (by linarith) hm_le_one h_dc hrho_small h_sub T hT_ball ht2_mem h_z2
    have h_len : dist P Q < 3 := by
      have h2 : dist P Q = ‖P - Q‖ := by rw [dist_eq_norm]
      have h2' : ‖P - Q‖ = ‖Q - P‖ := norm_sub_rev P Q
      rw [h2, h2', h1]
      have h3 : ‖(t2 - t1) • Ad‖ = |t2 - t1| * ‖Ad‖ := by
        simpa using norm_smul (t2 - t1) Ad
      rw [h3]
      have h4 : |t2 - t1| = t2 - t1 := by
        rw [abs_of_nonneg] <;> linarith
      rw [h4]
      have h8 : 0 < |dir 2| := by linarith [hdir_z]
      have h6 : t2 - t1 ≤ (d - c + 2 * δ) / |dir 2| := by
        have h7 : (t2 - t1) * |dir 2| ≤ d - c + 2 * δ := h_width
        have h9 : t2 - t1 ≤ (d - c + 2 * δ) / |dir 2| := by
          calc
            t2 - t1 = ((t2 - t1) * |dir 2|) / |dir 2| := by
              field_simp [h8.ne'] <;> ring
            _ ≤ (d - c + 2 * δ) / |dir 2| := by gcongr
        exact h9
      have h5 : (t2 - t1) * ‖Ad‖ ≤ ((d - c + 2 * δ) / |dir 2|) * ‖Ad‖ := by
        gcongr <;> positivity
      exact h5.trans_lt (extended_image_axis_lt_3 hdelta hcd hdir_unit hdir_z hg hK hS_eq h_dc hdelta_small hrho_small)
    have hvert : P = Q ∨ (1 / 2 : ℝ) ≤ |(Q - P) 2| / ‖Q - P‖ := by
      by_cases h_eq : t1 = t2
      · have hQP : Q - P = 0 := by
          rw [h1, h_eq, sub_self, zero_smul]
        have hPQ : P = Q := by
          have h : Q - P = 0 := hQP
          have hQ : Q = P := by simpa [sub_eq_zero] using h
          exact hQ.symm
        exact Or.inl hPQ
      · have h_lt : t1 < t2 := by
          by_cases h : t1 < t2
          · exact h
          · have h' : t1 = t2 := by linarith
            exact False.elim (h_eq h')
        have h_pos : 0 < t2 - t1 := by linarith
        have h2 : (Q - P) 2 = (t2 - t1) * Ad 2 := by
          rw [h1] <;> simp
        have h3 : ‖Q - P‖ = (t2 - t1) * ‖Ad‖ := by
          calc ‖Q - P‖
            = ‖(t2 - t1) • Ad‖ := by rw [h1]
          _ = |t2 - t1| * ‖Ad‖ := by simpa [norm_smul] using rfl
          _ = (t2 - t1) * ‖Ad‖ := by rw [abs_of_pos h_pos]
        have h4 : |(Q - P) 2| / ‖Q - P‖ = |Ad 2| / ‖Ad‖ := by
          rw [h2, h3]
          have h5 : |(t2 - t1) * Ad 2| = (t2 - t1) * |Ad 2| := by
            rw [abs_mul, abs_of_pos h_pos]
          rw [h5]
          <;> field_simp [h_pos.ne'] <;> ring
        rw [h4]
        exact Or.inr hAd_vert
    rcases hseg P Q h_len hvert with ⟨bases, direction, hd'_unit, hd'_vert, hbase_norm, hcover⟩
    have hbase_le_three : ∀ k : Fin 3, ‖bases k‖ ≤ 3 := by
      intro k
      have h : ‖bases k‖ ≤ max ‖P‖ ‖Q‖ + 1 := hbase_norm k
      have hmax : max ‖P‖ ‖Q‖ ≤ 2 := by
        apply max_le <;> linarith [hP_norm, hQ_norm]
      linarith
    have h_image_subset : Φ '' E ⊆
        ⋃ k : Fin 3, Kakeya.unitSegment (bases k) direction := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      have hy_axis : y ∈ axis := hy.1
      have hy_slab : y 2 ∈ Set.Icc (c - δ) (d + δ) := hy.2
      rcases hy_axis with ⟨t, ht, rfl⟩
      have h_t_in : t ∈ Set.Icc t1 t2 := h_bounds t ht hy_slab
      by_cases h_eq : t1 = t2
      · have h_t : t = t1 := by
          have h_t1 : t1 ≤ t := h_t_in.1
          have h_t2 : t ≤ t2 := h_t_in.2
          linarith
        have h_goal : Φ (base + t • dir) = P := by
          have h : Φ (base + t • dir) = Φ (base + t1 • dir) := by rw [h_t]
          simpa [P] using h
        rw [h_goal]
        exact hcover P ⟨0, by norm_num, by simp⟩
      · have h_t1_lt_t2 : t1 < t2 := by
          by_cases h : t1 < t2
          · exact h
          · have h' : t1 = t2 := by linarith
            exact False.elim (h_eq h')
        let s : ℝ := (t - t1) / (t2 - t1)
        have hs_in : s ∈ Set.Icc (0 : ℝ) 1 := by
          have h_pos : 0 < t2 - t1 := by linarith
          have h1 : 0 ≤ s := by
            apply div_nonneg <;> linarith [h_t_in.1]
          have h2 : s ≤ 1 := by
            rw [div_le_one (by linarith)] <;> linarith [h_t_in.2]
          exact ⟨h1, h2⟩
        have h_affine : Φ (base + t • dir) = P + s • (Q - P) := by
          have h13 : Φ (base + t • dir) = Φ base + t • Ad := by
            simpa [Ad] using hΦ_affine t
          have h14 : P + s • (Q - P) = Φ base + t • Ad := by
            rw [h12, h11]
            have h_sub : (Φ base + t2 • Ad) - (Φ base + t1 • Ad) = (t2 - t1) • Ad := by
              simp [sub_smul] <;> abel
            have h_smul : s • ((Φ base + t2 • Ad) - (Φ base + t1 • Ad)) = (s * (t2 - t1)) • Ad := by
              rw [h_sub, smul_smul]
            have h15 : (Φ base + t1 • Ad) + s • ((Φ base + t2 • Ad) - (Φ base + t1 • Ad)) =
                Φ base + (t1 + s * (t2 - t1)) • Ad := by
              rw [h_smul]
              simp [add_smul] <;> abel
            rw [h15]
            have h16 : t1 + s * (t2 - t1) = t := by
              simp [s] <;> field_simp [h_t1_lt_t2.ne'] <;> ring
            rw [h16]
          exact h13.trans h14.symm
        rw [h_affine]
        exact hcover (P + s • (Q - P)) ⟨s, hs_in, rfl⟩
    let T1 : Kakeya.DeltaTube rho := ⟨bases 0, direction, hd'_unit⟩
    let T2 : Kakeya.DeltaTube rho := ⟨bases 1, direction, hd'_unit⟩
    let T3 : Kakeya.DeltaTube rho := ⟨bases 2, direction, hd'_unit⟩
    have h7 : S * δ ≤ rho := by rw [hrho_eq]
    have h_radius_mono : ∀ (E : Set Point3), Metric.cthickening (S * δ) E ⊆ Metric.cthickening rho E := by
      intro E x hx
      rw [Metric.cthickening_eq_preimage_infEDist] at hx ⊢
      have h2 : ENNReal.ofReal (S * δ) ≤ ENNReal.ofReal rho := ENNReal.ofReal_le_ofReal h7
      exact hx.trans h2
    have h_union_eq : (⋃ k : Fin 3, Kakeya.unitSegment (bases k) direction) =
        Kakeya.unitSegment (bases 0) direction ∪
        Kakeya.unitSegment (bases 1) direction ∪
        Kakeya.unitSegment (bases 2) direction := by
      ext x
      simp [Fin.forall_fin_succ, Fin.exists_fin_succ] <;> tauto
    have h5 : Metric.cthickening (S * δ) (Φ '' E) ⊆
        Metric.cthickening (S * δ) (⋃ k : Fin 3, Kakeya.unitSegment (bases k) direction) :=
      Metric.cthickening_subset_of_subset (S * δ) h_image_subset
    have h6 : Metric.cthickening (S * δ) (⋃ k : Fin 3, Kakeya.unitSegment (bases k) direction) =
        Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 0) direction) ∪
        Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 1) direction) ∪
        Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 2) direction) := by
      rw [h_union_eq, Metric.cthickening_union, Metric.cthickening_union]
    have h8 : Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 0) direction) ⊆ T1.carrier := by
      have h9 : T1.carrier = Metric.cthickening rho (Kakeya.unitSegment (bases 0) direction) := by rfl
      rw [h9]
      exact h_radius_mono (Kakeya.unitSegment (bases 0) direction)
    have h9 : Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 1) direction) ⊆ T2.carrier := by
      have h10 : T2.carrier = Metric.cthickening rho (Kakeya.unitSegment (bases 1) direction) := by rfl
      rw [h10]
      exact h_radius_mono (Kakeya.unitSegment (bases 1) direction)
    have h10 : Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 2) direction) ⊆ T3.carrier := by
      have h11 : T3.carrier = Metric.cthickening rho (Kakeya.unitSegment (bases 2) direction) := by rfl
      rw [h11]
      exact h_radius_mono (Kakeya.unitSegment (bases 2) direction)
    have h_final : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ T1.carrier ∪ T2.carrier ∪ T3.carrier := by
      calc Φ '' (T.carrier ∩ horizontalSlab c d)
        ⊆ Metric.cthickening (S * δ) (Φ '' E) := h2
      _ ⊆ Metric.cthickening (S * δ) (⋃ k : Fin 3, Kakeya.unitSegment (bases k) direction) := h5
      _ = Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 0) direction) ∪
            Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 1) direction) ∪
            Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 2) direction) := h6
      _ ⊆ T1.carrier ∪ T2.carrier ∪ T3.carrier := by
        intro z hz
        by_cases h1 : z ∈ Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 0) direction)
        · exact Or.inl (Or.inl (h8 h1))
        · by_cases h2 : z ∈ Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 1) direction)
          · exact Or.inl (Or.inr (h9 h2))
          · have h3 : z ∈ Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 2) direction) := by
              have h4 : z ∈ (Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 0) direction)) ∪
                  (Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 1) direction)) ∪
                  (Metric.cthickening (S * δ) (Kakeya.unitSegment (bases 2) direction)) := hz
              simp only [Set.mem_union] at h4
              tauto
            exact Or.inr (h10 h3)
    exact ⟨T1, T2, T3, h_final, hd'_vert, hd'_vert, hd'_vert,
      hbase_le_three 0, hbase_le_three 1, hbase_le_three 2⟩
  · -- Degenerate case: axis misses extended slab
    have hE_empty : E = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hy
      have hy_axis : y ∈ axis := hy.1
      have hy_slab : y 2 ∈ Set.Icc (c - δ) (d + δ) := hy.2
      rcases hy_axis with ⟨t, ht, rfl⟩
      exact hmeet ⟨t, ht, hy_slab⟩
    have h_source_empty : Φ '' (T.carrier ∩ horizontalSlab c d) = ∅ := by
      have h : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ Metric.cthickening (S * δ) (Φ '' E) := h2
      rw [hE_empty] at h
      simpa using h
    let d' : Point3 := EuclideanSpace.single 2 1
    have hd'_unit : ‖d'‖ = 1 := by simp [d'] <;> norm_num
    have hd'_vert : (1 / 2 : ℝ) ≤ |d' 2| := by simp [d'] <;> norm_num
    let T1 : Kakeya.DeltaTube rho := ⟨0, d', hd'_unit⟩
    let T2 : Kakeya.DeltaTube rho := ⟨0, d', hd'_unit⟩
    let T3 : Kakeya.DeltaTube rho := ⟨0, d', hd'_unit⟩
    have h_final : Φ '' (T.carrier ∩ horizontalSlab c d) ⊆ T1.carrier ∪ T2.carrier ∪ T3.carrier := by
      rw [h_source_empty]
      <;> simp
    have h_base_zero : ‖(0 : Point3)‖ ≤ 3 := by
      have h : ‖(0 : Point3)‖ = 0 := norm_zero
      rw [h] <;> norm_num
    exact ⟨T1, T2, T3, h_final, hd'_vert, hd'_vert, hd'_vert, h_base_zero, h_base_zero, h_base_zero⟩

theorem bounded_three_tube_image_cover :
    BoundedThreeTubeImageCoverStatement := by
  intro hseg delta c d m rho hdelta hcd h_dc hdelta_small hrho_small hrho_eq hm_pos hm_le_one h_sub F hF_ball hvert g hg_norm
  set g_mid : ℝ := g (c + (d - c) / 2) with hg_mid_def
  set K : ℝ := m * (d - c) / 2 with hK_def
  set S : ℝ := 2 / (d - c) with hS_def
  have hg_mid : |g_mid| ≤ 1 := by
    have h_mid_in_Icc : c + (d - c) / 2 ∈ Set.Icc c d := by
      exact ⟨by linarith, by linarith⟩
    have h_mid_in' : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 := h_sub h_mid_in_Icc
    exact (hg_norm (c + (d - c) / 2) h_mid_in').1
  have hK_nonneg : 0 ≤ K := by positivity
  have hK_le : K ≤ 1 / 50 := by
    rw [hK_def]
    calc
      m * (d - c) / 2
          ≤ 1 * (d - c) / 2 := by gcongr
      _ = (d - c) / 2 := by ring
      _ ≤ (1 / 25 : ℝ) / 2 := by gcongr
      _ = 1 / 50 := by norm_num
  have hK : |K| ≤ 1 := by
    rw [abs_of_nonneg hK_nonneg]
    linarith
  have hS_eq : S = 2 / (d - c) := hS_def
  have hrho_eq' : rho = S * delta := by
    rw [hS_def, hrho_eq] <;> ring
  have h_main : ∀ i : Fin F.card,
      ∃ T1 T2 T3 : Kakeya.DeltaTube rho,
        (fun p : Point3 =>
          point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)) ''
          ((F.tube i).carrier ∩ horizontalSlab c d) ⊆
        T1.carrier ∪ T2.carrier ∪ T3.carrier ∧
        (1 / 2 : ℝ) ≤ |T1.direction (2 : Fin 3)| ∧
        (1 / 2 : ℝ) ≤ |T2.direction (2 : Fin 3)| ∧
        (1 / 2 : ℝ) ≤ |T3.direction (2 : Fin 3)| ∧
        ‖T1.base‖ ≤ 3 ∧ ‖T2.base‖ ≤ 3 ∧ ‖T3.base‖ ≤ 3 := by
    intro i
    exact bounded_cover_tube_image_three_rho_tubes
      hdelta hcd (F.tube i) (hvert i) hg_mid hK hS_eq h_dc hdelta_small hrho_small hrho_eq'
      g hg_norm m hm_pos hm_le_one h_sub hK_def hg_mid_def (hF_ball i) hseg
  choose T1 T2 T3 hprops using h_main
  let tube : Fin F.card → Fin 3 → Kakeya.DeltaTube rho := fun i k =>
    Fin.cases (T1 i)
      (fun j : Fin 2 => Fin.cases (T2 i) (fun _ : Fin 1 => T3 i) j) k
  let targetUnion (i : Fin F.card) : Set Point3 :=
    ⋃ k : Fin 3, (tube i k).carrier
  have h1_sub : ∀ i, (T1 i).carrier ⊆ targetUnion i := by
    intro i x hx
    exact Set.mem_iUnion.mpr ⟨0, hx⟩
  have h2_sub : ∀ i, (T2 i).carrier ⊆ targetUnion i := by
    intro i x hx
    exact Set.mem_iUnion.mpr ⟨1, hx⟩
  have h3_sub : ∀ i, (T3 i).carrier ⊆ targetUnion i := by
    intro i x hx
    exact Set.mem_iUnion.mpr ⟨2, hx⟩
  have h_cover_sub :
      ∀ i, (T1 i).carrier ∪ (T2 i).carrier ∪ (T3 i).carrier ⊆ targetUnion i := by
    intro i
    exact Set.union_subset
      (Set.union_subset (h1_sub i) (h2_sub i)) (h3_sub i)
  have h_vertical : ∀ (i : Fin F.card) (k : Fin 3),
      (1 / 2 : ℝ) ≤ |(tube i k).direction (2 : Fin 3)| := by
    intro i k
    have h1 : (1 / 2 : ℝ) ≤ |(T1 i).direction (2 : Fin 3)| :=
      (hprops i).2.1
    have h2 : (1 / 2 : ℝ) ≤ |(T2 i).direction (2 : Fin 3)| :=
      (hprops i).2.2.1
    have h3 : (1 / 2 : ℝ) ≤ |(T3 i).direction (2 : Fin 3)| :=
      (hprops i).2.2.2.1
    exact Fin.cases h1
      (fun j : Fin 2 => Fin.cases h2 (fun _ : Fin 1 => h3) j) k
  have h_bases : ∀ (i : Fin F.card) (k : Fin 3), ‖(tube i k).base‖ ≤ 3 := by
    intro i k
    have h1 : ‖(T1 i).base‖ ≤ 3 := (hprops i).2.2.2.2.1
    have h2 : ‖(T2 i).base‖ ≤ 3 := (hprops i).2.2.2.2.2.1
    have h3 : ‖(T3 i).base‖ ≤ 3 := (hprops i).2.2.2.2.2.2
    exact Fin.cases h1
      (fun j : Fin 2 => Fin.cases h2 (fun _ : Fin 1 => h3) j) k
  let W : ThreeTubeImageCover (rho := rho) F
      (anisotropicRescalingMap g c d m)
      (fun i => (F.tube i).carrier ∩ horizontalSlab c d) :=
    {
      tube := tube
      covered := by
        intro i
        have hcov :
            (fun p : Point3 =>
              point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)) ''
              ((F.tube i).carrier ∩ horizontalSlab c d) ⊆
              (T1 i).carrier ∪ (T2 i).carrier ∪ (T3 i).carrier :=
            (hprops i).1
        have hPhi_eq : (fun p : Point3 =>
              point3 (p 0 + g_mid * p 1) (K * p 1) (S * p 2 - S * c - 1)) =
            anisotropicRescalingMap g c d m := by
          funext p
          ext i
          fin_cases i <;> simp [anisotropicRescalingMap, point3, hg_mid_def, hK_def, hS_def, EuclideanSpace.single_apply] <;> field_simp [hcd.ne'] <;> ring
        rw [hPhi_eq] at hcov
        exact hcov.trans (h_cover_sub i)
      vertical := h_vertical
    }
  exact ⟨W, h_bases⟩

end Kakeya.Assouad
