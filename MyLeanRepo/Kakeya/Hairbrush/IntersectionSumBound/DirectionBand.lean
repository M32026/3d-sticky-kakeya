import MyLeanRepo.Kakeya.Hairbrush.IntersectionSumBound.Preparations

/-!
# Direction band containment and geometric bounds

Extracts from IntersectionSumBound: coordinate containment bounds and convex set construction.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Hairbrush

lemma direction_band_containment_bounds
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T : Kakeya.DeltaTube δ) (n : Point3)
    (C0 σ : ℝ) (hC0 : 0 ≤ C0) (hσ2 : 2 * σ ≤ Real.pi / 2)
    (v e2 e3 : Point3) (hv : ‖v‖ = 1) (he2_unit : ‖e2‖ = 1) (he3_unit : ‖e3‖ = 1)
    (hv_e2 : inner ℝ v e2 = 0) (hv_e3 : inner ℝ v e3 = 0)
    (h_e2_bound : ∀ (u : Point3), ‖u‖ = 1 → |inner ℝ u n| ≤ C0 * δ → |inner ℝ u e2| ≤ 4 * C0 * δ)
    (hv_eq : v = T.direction)
    (c : Point3) (hc_eq : c = T.base + (1 / 2 : ℝ) • v)
    (h0 h1 h2 : ℝ)
    (hh0 : 3 / 2 + 3 * δ ≤ h0)
    (hh1 : (4 * C0 + 3) * δ ≤ h1)
    (hh2 : 2 * σ + 3 * δ ≤ h2)
    (U : Kakeya.DeltaTube δ)
    (hplane_U : |inner ℝ U.direction n| ≤ C0 * δ)
    (hangle_U : effectiveAngle T U ≤ 2 * σ)
    (hinter_U : (T.carrier ∩ U.carrier).Nonempty)
    (x : Point3) (hx : x ∈ U.carrier) :
    |inner ℝ (x - c) v| ≤ h0 ∧
    |inner ℝ (x - c) e2| ≤ h1 ∧
    |inner ℝ (x - c) e3| ≤ h2 := by
  have h_decomp : ∀ (V : Kakeya.DeltaTube δ) (x : Point3), x ∈ V.carrier →
      ∃ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (z : Point3) (hz : ‖z‖ ≤ δ),
        x = V.base + t • V.direction + z := by
    intro V x hx
    have hδ' : 0 ≤ δ := by linarith
    have h_compact : IsCompact (unitSegment V.base V.direction) :=
      isCompact_Icc.image (by fun_prop)
    have h_closed : IsClosed (unitSegment V.base V.direction) := h_compact.isClosed
    have h_closure : closure (unitSegment V.base V.direction) = unitSegment V.base V.direction :=
      h_closed.closure_eq
    have h1 : ∃ p ∈ unitSegment V.base V.direction, dist x p ≤ δ := by
      have h2 : x ∈ Metric.cthickening δ (unitSegment V.base V.direction) := hx
      rw [Metric.cthickening_eq_biUnion_closedBall (unitSegment V.base V.direction) hδ'] at h2
      rw [h_closure] at h2
      simpa [Set.mem_iUnion, Metric.mem_closedBall] using h2
    rcases h1 with ⟨p, hp, hdist⟩
    have h2 : ∃ t ∈ Set.Icc (0 : ℝ) 1, p = V.base + t • V.direction := by
      have h3 : p ∈ (fun t : ℝ => V.base + t • V.direction) '' Set.Icc 0 1 := by
        simpa [unitSegment] using hp
      rcases h3 with ⟨t, ht, hpt⟩
      exact ⟨t, ht, hpt.symm⟩
    rcases h2 with ⟨t, ht, rfl⟩
    refine ⟨t, ht, x - (V.base + t • V.direction), ?_, ?_⟩
    · simpa [dist_eq_norm] using hdist
    · abel
  have h_e2_U : |inner ℝ U.direction e2| ≤ 4 * C0 * δ :=
    h_e2_bound U.direction U.direction_unit hplane_U
  have h_perp_U : ‖U.direction - inner ℝ v U.direction • v‖ ≤ 2 * σ := by
    have h := perp_component_bound T U σ hangle_U hσ2
    have h5 : inner ℝ v U.direction = inner ℝ T.direction U.direction := by rw [hv_eq]
    rw [h5, hv_eq]
    exact h
  have h_e3_U : |inner ℝ U.direction e3| ≤ 2 * σ := by
    have h1 : inner ℝ (U.direction - inner ℝ v U.direction • v) e3 = inner ℝ U.direction e3 := by
      have h2 : inner ℝ (U.direction - inner ℝ v U.direction • v) e3 =
          inner ℝ U.direction e3 - inner ℝ (inner ℝ v U.direction • v) e3 := by
        rw [inner_sub_left] <;> ring
      rw [h2]
      have h3 : inner ℝ (inner ℝ v U.direction • v) e3 = (inner ℝ v U.direction) * inner ℝ v e3 := by
        exact real_inner_smul_left v e3 (inner ℝ v U.direction)
      rw [h3, hv_e3] <;> ring
    rw [←h1]
    have h2 : |inner ℝ (U.direction - inner ℝ v U.direction • v) e3| ≤
        ‖U.direction - inner ℝ v U.direction • v‖ * ‖e3‖ := by
      exact abs_real_inner_le_norm _ _
    rw [he3_unit] at h2
    linarith [h_perp_U]
  rcases hinter_U with ⟨y, hy_T, hy_U⟩
  rcases h_decomp T y hy_T with ⟨s, hs, z_T, hz_T, h_y_T⟩
  rcases h_decomp U y hy_U with ⟨t, ht, z_y, hz_y, h_y_U⟩
  rcases h_decomp U x hx with ⟨r, hr, z_x, hz_x, h_x_U⟩
  have h_x_sub : x - y = (r - t) • U.direction + (z_x - z_y) := by
    rw [h_x_U, h_y_U]
    have h : (U.base + r • U.direction + z_x) - (U.base + t • U.direction + z_y) =
        (r • U.direction - t • U.direction) + (z_x - z_y) := by abel
    rw [h]
    have h2 : r • U.direction - t • U.direction = (r - t) • U.direction := by
      rw [←sub_smul]
    rw [h2]
  have h_y_sub : y - T.base = s • v + z_T := by
    rw [h_y_T]
    have h : (T.base + s • T.direction + z_T) - T.base = s • T.direction + z_T := by abel
    rw [h, ←hv_eq]
  have h_x_base : x - T.base = (r - t) • U.direction + (z_x - z_y) + s • v + z_T := by
    calc x - T.base = (x - y) + (y - T.base) := by abel
      _ = (r - t) • U.direction + (z_x - z_y) + (s • v + z_T) := by rw [h_x_sub, h_y_sub] <;> abel
      _ = (r - t) • U.direction + (z_x - z_y) + s • v + z_T := by abel
  have h_rt_bound : |r - t| ≤ 1 := by
    have hr1 : 0 ≤ r := hr.1
    have hr2 : r ≤ 1 := hr.2
    have ht1 : 0 ≤ t := ht.1
    have ht2 : t ≤ 1 := ht.2
    rw [abs_le]
    constructor <;> linarith
  have h_vv : inner ℝ v v = 1 := by
    have h5 : inner ℝ v v = ‖v‖ ^ 2 := by
      exact real_inner_self_eq_norm_sq v
    rw [h5, hv] <;> norm_num
  -- General inner product expansion
  have h_expand4 : ∀ (a b c d : Point3) (w : Point3),
      inner ℝ (a + b + c + d) w = inner ℝ a w + inner ℝ b w + inner ℝ c w + inner ℝ d w := by
    intro a b c d w
    have h_eq : a + b + c + d = (a + b) + (c + d) := by abel
    rw [h_eq]
    rw [inner_add_left, inner_add_left, inner_add_left] <;> abel
  have h_tri : ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := by
    intro x y
    exact abs_add_le x y
  -- v-coordinate bound
  have h_v1 : |inner ℝ (x - T.base) v - 1 / 2| ≤ 3 / 2 + 3 * δ := by
    have h_expand : inner ℝ (x - T.base) v =
        (r - t) * inner ℝ U.direction v + inner ℝ (z_x - z_y) v + s + inner ℝ z_T v := by
      rw [h_x_base]
      have h := h_expand4 ((r - t) • U.direction) (z_x - z_y) (s • v) z_T v
      rw [h]
      have h_smul1 : inner ℝ ((r - t) • U.direction) v = (r - t) * inner ℝ U.direction v := by
        simpa [inner_smul_left] using rfl
      have h_smul2 : inner ℝ (s • v) v = s * inner ℝ v v := by
        simpa [inner_smul_left] using rfl
      rw [h_smul1, h_smul2, h_vv] <;> ring
    rw [h_expand]
    have h_a : |(r - t) * inner ℝ U.direction v| ≤ 1 := by
      have h_b : |inner ℝ U.direction v| ≤ 1 := by
        have h_c := abs_real_inner_le_norm U.direction v
        rw [U.direction_unit, hv] at h_c <;> norm_num at h_c ⊢ <;> exact h_c
      calc |(r - t) * inner ℝ U.direction v|
        = |r - t| * |inner ℝ U.direction v| := by rw [abs_mul]
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    have h_b : |inner ℝ (z_x - z_y) v| ≤ 2 * δ := by
      have h_c : |inner ℝ (z_x - z_y) v| ≤ ‖z_x - z_y‖ * ‖v‖ := abs_real_inner_le_norm _ _
      rw [hv] at h_c
      have h_d : ‖z_x - z_y‖ ≤ ‖z_x‖ + ‖z_y‖ := norm_sub_le _ _
      linarith [hz_x, hz_y]
    have h_c : |inner ℝ z_T v| ≤ δ := by
      have h_d : |inner ℝ z_T v| ≤ ‖z_T‖ * ‖v‖ := abs_real_inner_le_norm _ _
      rw [hv] at h_d; linarith [hz_T]
    have hs1 : 0 ≤ s := hs.1
    have hs2 : s ≤ 1 := hs.2
    have h_tri : ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := by
      intro x y
      exact abs_add_le x y
    have h_abs : |(r - t) * inner ℝ U.direction v + inner ℝ (z_x - z_y) v + s + inner ℝ z_T v - 1 / 2| ≤
        |(r - t) * inner ℝ U.direction v| + |inner ℝ (z_x - z_y) v| + |s - 1 / 2| + |inner ℝ z_T v| := by
      set a := (r - t) * inner ℝ U.direction v
      set b := inner ℝ (z_x - z_y) v
      set d := inner ℝ z_T v
      have h_eq : a + b + s + d - 1 / 2 = a + (b + ((s - 1 / 2) + d)) := by ring
      rw [h_eq]
      have h1' := h_tri a (b + ((s - 1 / 2) + d))
      have h2' := h_tri b ((s - 1 / 2) + d)
      have h3' := h_tri (s - 1 / 2) d
      linarith
    have h_s_half : |s - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le] <;> constructor <;> linarith
    linarith
  have h_v2 : 3 / 2 + 3 * δ ≤ h0 := hh0
  have h_v_final : |inner ℝ (x - c) v| ≤ h0 := by
    have h_eq : inner ℝ (x - c) v = inner ℝ (x - T.base) v - 1 / 2 := by
      rw [hc_eq]
      have h_sub : x - (T.base + (1 / 2 : ℝ) • v) = (x - T.base) - (1 / 2 : ℝ) • v := by abel
      rw [h_sub]
      have h1 : inner ℝ ((x - T.base) - (1 / 2 : ℝ) • v) v =
          inner ℝ (x - T.base) v - inner ℝ ((1 / 2 : ℝ) • v) v := by
        rw [inner_sub_left]
      rw [h1]
      have h_smul : inner ℝ ((1 / 2 : ℝ) • v) v = (1 / 2 : ℝ) * inner ℝ v v := by
        simpa [inner_smul_left] using rfl
      rw [h_smul, h_vv] <;> ring
    rw [h_eq]
    exact le_trans h_v1 h_v2
  -- e2-coordinate bound
  have h_e21 : |inner ℝ (x - T.base) e2| ≤ (4 * C0 + 3) * δ := by
    have h_expand : inner ℝ (x - T.base) e2 =
        (r - t) * inner ℝ U.direction e2 + inner ℝ (z_x - z_y) e2 + inner ℝ z_T e2 := by
      rw [h_x_base]
      have h := h_expand4 ((r - t) • U.direction) (z_x - z_y) (s • v) z_T e2
      rw [h]
      simp [inner_smul_left, hv_e2] <;> ring
    rw [h_expand]
    have h_a : |(r - t) * inner ℝ U.direction e2| ≤ 4 * C0 * δ := by
      calc |(r - t) * inner ℝ U.direction e2|
        = |r - t| * |inner ℝ U.direction e2| := by rw [abs_mul]
        _ ≤ 1 * (4 * C0 * δ) := by gcongr
        _ = 4 * C0 * δ := by ring
    have h_b : |inner ℝ (z_x - z_y) e2| ≤ 2 * δ := by
      have h_c : |inner ℝ (z_x - z_y) e2| ≤ ‖z_x - z_y‖ * ‖e2‖ := abs_real_inner_le_norm _ _
      rw [he2_unit] at h_c
      have h_d : ‖z_x - z_y‖ ≤ ‖z_x‖ + ‖z_y‖ := norm_sub_le _ _
      linarith [hz_x, hz_y]
    have h_c : |inner ℝ z_T e2| ≤ δ := by
      have h_d : |inner ℝ z_T e2| ≤ ‖z_T‖ * ‖e2‖ := abs_real_inner_le_norm _ _
      rw [he2_unit] at h_d; linarith [hz_T]
    have h1 := h_tri ((r - t) * inner ℝ U.direction e2) (inner ℝ (z_x - z_y) e2 + inner ℝ z_T e2)
    have h2 := h_tri (inner ℝ (z_x - z_y) e2) (inner ℝ z_T e2)
    have h_abs : |(r - t) * inner ℝ U.direction e2 + inner ℝ (z_x - z_y) e2 + inner ℝ z_T e2| ≤
        |(r - t) * inner ℝ U.direction e2| + |inner ℝ (z_x - z_y) e2| + |inner ℝ z_T e2| := by
      have h_eq : (r - t) * inner ℝ U.direction e2 + inner ℝ (z_x - z_y) e2 + inner ℝ z_T e2 =
          (r - t) * inner ℝ U.direction e2 + (inner ℝ (z_x - z_y) e2 + inner ℝ z_T e2) := by ring
      rw [h_eq]
      linarith
    linarith
  have h_e22 : (4 * C0 + 3) * δ ≤ h1 := hh1
  have h_e2_final : |inner ℝ (x - c) e2| ≤ h1 := by
    have h_eq : inner ℝ (x - c) e2 = inner ℝ (x - T.base) e2 := by
      rw [hc_eq]
      have h_sub : x - (T.base + (1 / 2 : ℝ) • v) = (x - T.base) - (1 / 2 : ℝ) • v := by abel
      rw [h_sub, inner_sub_left, inner_smul_left, hv_e2] <;> ring
    rw [h_eq]
    linarith
  -- e3-coordinate bound
  have h_e31 : |inner ℝ (x - T.base) e3| ≤ 2 * σ + 3 * δ := by
    have h_expand : inner ℝ (x - T.base) e3 =
        (r - t) * inner ℝ U.direction e3 + inner ℝ (z_x - z_y) e3 + inner ℝ z_T e3 := by
      rw [h_x_base]
      have h := h_expand4 ((r - t) • U.direction) (z_x - z_y) (s • v) z_T e3
      rw [h]
      simp [inner_smul_left, hv_e3] <;> ring
    rw [h_expand]
    have h_a : |(r - t) * inner ℝ U.direction e3| ≤ 2 * σ := by
      calc |(r - t) * inner ℝ U.direction e3|
        = |r - t| * |inner ℝ U.direction e3| := by rw [abs_mul]
        _ ≤ 1 * (2 * σ) := by gcongr
        _ = 2 * σ := by ring
    have h_b : |inner ℝ (z_x - z_y) e3| ≤ 2 * δ := by
      have h_c : |inner ℝ (z_x - z_y) e3| ≤ ‖z_x - z_y‖ * ‖e3‖ := abs_real_inner_le_norm _ _
      rw [he3_unit] at h_c
      have h_d : ‖z_x - z_y‖ ≤ ‖z_x‖ + ‖z_y‖ := norm_sub_le _ _
      linarith [hz_x, hz_y]
    have h_c : |inner ℝ z_T e3| ≤ δ := by
      have h_d : |inner ℝ z_T e3| ≤ ‖z_T‖ * ‖e3‖ := abs_real_inner_le_norm _ _
      rw [he3_unit] at h_d; linarith [hz_T]
    have h1 := h_tri ((r - t) * inner ℝ U.direction e3) (inner ℝ (z_x - z_y) e3 + inner ℝ z_T e3)
    have h2 := h_tri (inner ℝ (z_x - z_y) e3) (inner ℝ z_T e3)
    have h_abs : |(r - t) * inner ℝ U.direction e3 + inner ℝ (z_x - z_y) e3 + inner ℝ z_T e3| ≤
        |(r - t) * inner ℝ U.direction e3| + |inner ℝ (z_x - z_y) e3| + |inner ℝ z_T e3| := by
      have h_eq : (r - t) * inner ℝ U.direction e3 + inner ℝ (z_x - z_y) e3 + inner ℝ z_T e3 =
          (r - t) * inner ℝ U.direction e3 + (inner ℝ (z_x - z_y) e3 + inner ℝ z_T e3) := by ring
      rw [h_eq]
      linarith
    linarith
  have h_e32 : 2 * σ + 3 * δ ≤ h2 := hh2
  have h_e3_final : |inner ℝ (x - c) e3| ≤ h2 := by
    have h_eq : inner ℝ (x - c) e3 = inner ℝ (x - T.base) e3 := by
      rw [hc_eq]
      have h_sub : x - (T.base + (1 / 2 : ℝ) • v) = (x - T.base) - (1 / 2 : ℝ) • v := by abel
      rw [h_sub, inner_sub_left, inner_smul_left, hv_e3] <;> ring
    rw [h_eq]
    linarith
  exact ⟨h_v_final, h_e2_final, h_e3_final⟩

/--
Geometric packing lemma: existence of a convex set W containing every
tube U that intersects T, lies in the C₀δ-plane neighborhood of n, and has
effectiveAngle ≤ 2σ.  The volume of W is O((C₀+1) · max(σ,δ) · δ).

Build a box aligned with an orthonormal basis (v, e2, e3) where e2 is aligned
with the projection of n onto v⊥.  Dimensions: 9 × 16(C₀+1)δ × 10·max(σ,δ).
-/
lemma direction_band_geometric
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T : Kakeya.DeltaTube δ) (n : Point3) (hn : ‖n‖ = 1)
    (C0 σ : ℝ) (hC0 : 0 ≤ C0) (hσ1 : 0 ≤ σ) (hσ2 : 2 * σ ≤ Real.pi / 2)
    (h_plane_T : |inner ℝ T.direction n| ≤ C0 * δ) :
    ∃ (W : Set Point3), Convex ℝ W ∧
      (∀ (U : Kakeya.DeltaTube δ),
        |inner ℝ U.direction n| ≤ C0 * δ →
        effectiveAngle T U ≤ 2 * σ →
        (T.carrier ∩ U.carrier).Nonempty →
        U.carrier ⊆ W) ∧
      MeasureTheory.volume W ≤
        ENNReal.ofReal (2000 * (C0 + 1) * max σ δ * δ) := by
  let v := T.direction
  have hv : ‖v‖ = 1 := T.direction_unit
  have h_plane_v : |inner ℝ v n| ≤ C0 * δ := h_plane_T
  rcases direction_band_onb hδ v n hv hn C0 hC0 h_plane_v with
    ⟨A, e2, e3, hA_v, hA_e2, hA_e3, he2_unit, he3_unit, hv_e2, hv_e3, he2_e3, h_e2_bound⟩
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  -- Coordinate formulas
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z v := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = v := by
      have h7 : A (A.symm e0_std) = A v := by rw [A.apply_symm_apply, hA_v]
      exact A.injective h7
    rw [h6]
  have hcoord1 : ∀ (z : Point3), (A z) 1 = inner ℝ z e2 := by
    intro z
    have h : (A z) 1 = inner ℝ (A z) e1_std := by
      have h2 : inner ℝ (A z) e1_std = (1 : ℝ) * (A z) 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e1_std = inner ℝ z (A.symm e1_std) := by
      have h4 := A.inner_map_map z (A.symm e1_std)
      have h5 : A (A.symm e1_std) = e1_std := A.apply_symm_apply e1_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e1_std = e2 := by
      have h7 : A (A.symm e1_std) = A e2 := by rw [A.apply_symm_apply, hA_e2]
      exact A.injective h7
    rw [h6]
  have hcoord2 : ∀ (z : Point3), (A z) 2 = inner ℝ z e3 := by
    intro z
    have h : (A z) 2 = inner ℝ (A z) e2_std := by
      have h2 : inner ℝ (A z) e2_std = (1 : ℝ) * (A z) 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e2_std = inner ℝ z (A.symm e2_std) := by
      have h4 := A.inner_map_map z (A.symm e2_std)
      have h5 : A (A.symm e2_std) = e2_std := A.apply_symm_apply e2_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e2_std = e3 := by
      have h7 : A (A.symm e2_std) = A e3 := by rw [A.apply_symm_apply, hA_e3]
      exact A.injective h7
    rw [h6]
  -- Define the box W
  let c : Point3 := T.base + (1 / 2 : ℝ) • v
  let h0 : ℝ := 9 / 2
  let h1 : ℝ := 8 * (C0 + 1) * δ
  let h2 : ℝ := 5 * max σ δ
  let W : Set Point3 := {x |
    |inner ℝ (x - c) v| ≤ h0 ∧
    |inner ℝ (x - c) e2| ≤ h1 ∧
    |inner ℝ (x - c) e3| ≤ h2}
  have hW_conv : Convex ℝ W := by
    intro x hx y hy a b ha hb hab
    have hxa1 : |inner ℝ (x - c) v| ≤ h0 := hx.1
    have hya1 : |inner ℝ (y - c) v| ≤ h0 := hy.1
    have hxa2 : |inner ℝ (x - c) e2| ≤ h1 := hx.2.1
    have hya2 : |inner ℝ (y - c) e2| ≤ h1 := hy.2.1
    have hxa3 : |inner ℝ (x - c) e3| ≤ h2 := hx.2.2
    have hya3 : |inner ℝ (y - c) e3| ≤ h2 := hy.2.2
    have h_tri : ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := by
      intro x y
      exact abs_add_le x y
    have h_abs_a : 0 ≤ a := ha
    have h_abs_b : 0 ≤ b := hb
    have h_sum : a + b = 1 := hab
    have h_eq : (a • x + b • y) - c = a • (x - c) + b • (y - c) := by
      have h2 : a • c + b • c = c := by
        have h3 : a • c + b • c = (a + b) • c := by rw [←add_smul] <;> ring
        rw [h3, h_sum] <;> simp
      have h4 : (a • x + b • y) - c = (a • x + b • y) - (a • c + b • c) := by
        exact congr_arg (fun z : Point3 => (a • x + b • y) - z) h2.symm
      rw [h4]
      have h5 : (a • x + b • y) - (a • c + b • c) = a • x - a • c + (b • y - b • c) := by abel
      rw [h5]
      have h6 : a • x - a • c = a • (x - c) := by rw [←smul_sub] <;> ring
      have h7 : b • y - b • c = b • (y - c) := by rw [←smul_sub] <;> ring
      rw [h6, h7] <;> abel
    have h_inner_v : inner ℝ ((a • x + b • y) - c) v = a * inner ℝ (x - c) v + b * inner ℝ (y - c) v := by
      have h_eq2 : (a • x + b • y) - c = a • (x - c) + b • (y - c) := h_eq
      rw [h_eq2]
      have h_i1 : inner ℝ (a • (x - c) + b • (y - c)) v =
          inner ℝ (a • (x - c)) v + inner ℝ (b • (y - c)) v := by
        rw [inner_add_left]
      rw [h_i1]
      have h_i2 : inner ℝ (a • (x - c)) v = a * inner ℝ (x - c) v := by
        simp [inner_smul_left] <;> ring
      have h_i3 : inner ℝ (b • (y - c)) v = b * inner ℝ (y - c) v := by
        simp [inner_smul_left] <;> ring
      rw [h_i2, h_i3] <;> ring
    have h_abs1 : |a * inner ℝ (x - c) v + b * inner ℝ (y - c) v| ≤
        a * |inner ℝ (x - c) v| + b * |inner ℝ (y - c) v| := by
      calc |a * inner ℝ (x - c) v + b * inner ℝ (y - c) v|
        ≤ |a * inner ℝ (x - c) v| + |b * inner ℝ (y - c) v| := h_tri (a * inner ℝ (x - c) v) (b * inner ℝ (y - c) v)
      _ = a * |inner ℝ (x - c) v| + b * |inner ℝ (y - c) v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h_abs_a, abs_of_nonneg h_abs_b] <;> ring
    have h_bound_v : |inner ℝ ((a • x + b • y) - c) v| ≤ h0 := by
      rw [h_inner_v]
      calc |a * inner ℝ (x - c) v + b * inner ℝ (y - c) v|
        ≤ a * |inner ℝ (x - c) v| + b * |inner ℝ (y - c) v| := h_abs1
      _ ≤ a * h0 + b * h0 := by gcongr
      _ = h0 := by rw [←add_mul, hab] <;> ring
    have h_inner_e2 : inner ℝ ((a • x + b • y) - c) e2 = a * inner ℝ (x - c) e2 + b * inner ℝ (y - c) e2 := by
      have h_eq2 : (a • x + b • y) - c = a • (x - c) + b • (y - c) := h_eq
      rw [h_eq2]
      have h_i1 : inner ℝ (a • (x - c) + b • (y - c)) e2 =
          inner ℝ (a • (x - c)) e2 + inner ℝ (b • (y - c)) e2 := by
        rw [inner_add_left]
      rw [h_i1]
      have h_i2 : inner ℝ (a • (x - c)) e2 = a * inner ℝ (x - c) e2 := by
        simp [inner_smul_left] <;> ring
      have h_i3 : inner ℝ (b • (y - c)) e2 = b * inner ℝ (y - c) e2 := by
        simp [inner_smul_left] <;> ring
      rw [h_i2, h_i3] <;> ring
    have h_abs2 : |a * inner ℝ (x - c) e2 + b * inner ℝ (y - c) e2| ≤
        a * |inner ℝ (x - c) e2| + b * |inner ℝ (y - c) e2| := by
      calc |a * inner ℝ (x - c) e2 + b * inner ℝ (y - c) e2|
        ≤ |a * inner ℝ (x - c) e2| + |b * inner ℝ (y - c) e2| := h_tri _ _
      _ = a * |inner ℝ (x - c) e2| + b * |inner ℝ (y - c) e2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h_abs_a, abs_of_nonneg h_abs_b] <;> ring
    have h_bound_e2 : |inner ℝ ((a • x + b • y) - c) e2| ≤ h1 := by
      rw [h_inner_e2]
      calc |a * inner ℝ (x - c) e2 + b * inner ℝ (y - c) e2|
        ≤ a * |inner ℝ (x - c) e2| + b * |inner ℝ (y - c) e2| := h_abs2
      _ ≤ a * h1 + b * h1 := by gcongr
      _ = h1 := by rw [←add_mul, hab] <;> ring
    have h_inner_e3 : inner ℝ ((a • x + b • y) - c) e3 = a * inner ℝ (x - c) e3 + b * inner ℝ (y - c) e3 := by
      have h_eq2 : (a • x + b • y) - c = a • (x - c) + b • (y - c) := h_eq
      rw [h_eq2]
      have h_i1 : inner ℝ (a • (x - c) + b • (y - c)) e3 =
          inner ℝ (a • (x - c)) e3 + inner ℝ (b • (y - c)) e3 := by
        rw [inner_add_left]
      rw [h_i1]
      have h_i2 : inner ℝ (a • (x - c)) e3 = a * inner ℝ (x - c) e3 := by
        simp [inner_smul_left] <;> ring
      have h_i3 : inner ℝ (b • (y - c)) e3 = b * inner ℝ (y - c) e3 := by
        simp [inner_smul_left] <;> ring
      rw [h_i2, h_i3] <;> ring
    have h_abs3 : |a * inner ℝ (x - c) e3 + b * inner ℝ (y - c) e3| ≤
        a * |inner ℝ (x - c) e3| + b * |inner ℝ (y - c) e3| := by
      calc |a * inner ℝ (x - c) e3 + b * inner ℝ (y - c) e3|
        ≤ |a * inner ℝ (x - c) e3| + |b * inner ℝ (y - c) e3| := h_tri _ _
      _ = a * |inner ℝ (x - c) e3| + b * |inner ℝ (y - c) e3| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h_abs_a, abs_of_nonneg h_abs_b] <;> ring
    have h_bound_e3 : |inner ℝ ((a • x + b • y) - c) e3| ≤ h2 := by
      rw [h_inner_e3]
      calc |a * inner ℝ (x - c) e3 + b * inner ℝ (y - c) e3|
        ≤ a * |inner ℝ (x - c) e3| + b * |inner ℝ (y - c) e3| := h_abs3
      _ ≤ a * h2 + b * h2 := by gcongr
      _ = h2 := by rw [←add_mul, hab] <;> ring
    exact ⟨h_bound_v, h_bound_e2, h_bound_e3⟩
  have hW_meas : MeasurableSet W := by
    have h_cont1 : Continuous (fun x : Point3 => inner ℝ (x - c) v) := by fun_prop
    have h_cont2 : Continuous (fun x : Point3 => inner ℝ (x - c) e2) := by fun_prop
    have h_cont3 : Continuous (fun x : Point3 => inner ℝ (x - c) e3) := by fun_prop
    have h1_closed : IsClosed (Set.Icc (-h0) h0) := isClosed_Icc
    have h2_closed : IsClosed (Set.Icc (-h1) h1) := isClosed_Icc
    have h3_closed : IsClosed (Set.Icc (-h2) h2) := isClosed_Icc
    have h_isclosed1 : IsClosed {x : Point3 | |inner ℝ (x - c) v| ≤ h0} := by
      have h_eq : {x : Point3 | |inner ℝ (x - c) v| ≤ h0} =
          (fun x : Point3 => inner ℝ (x - c) v) ⁻¹' Set.Icc (-h0) h0 := by
        ext x; simp [abs_le]
      rw [h_eq]
      exact h1_closed.preimage h_cont1
    have h_isclosed2 : IsClosed {x : Point3 | |inner ℝ (x - c) e2| ≤ h1} := by
      have h_eq : {x : Point3 | |inner ℝ (x - c) e2| ≤ h1} =
          (fun x : Point3 => inner ℝ (x - c) e2) ⁻¹' Set.Icc (-h1) h1 := by
        ext x; simp [abs_le]
      rw [h_eq]
      exact h2_closed.preimage h_cont2
    have h_isclosed3 : IsClosed {x : Point3 | |inner ℝ (x - c) e3| ≤ h2} := by
      have h_eq : {x : Point3 | |inner ℝ (x - c) e3| ≤ h2} =
          (fun x : Point3 => inner ℝ (x - c) e3) ⁻¹' Set.Icc (-h2) h2 := by
        ext x; simp [abs_le]
      rw [h_eq]
      exact h3_closed.preimage h_cont3
    have h4 : IsClosed W := by
      convert h_isclosed1.inter (h_isclosed2.inter h_isclosed3) using 1
      ext x; simp [W] <;> tauto
    exact h4.measurableSet
  -- Containment proof
  have h_containment : ∀ (U : Kakeya.DeltaTube δ),
      |inner ℝ U.direction n| ≤ C0 * δ →
      effectiveAngle T U ≤ 2 * σ →
      (T.carrier ∩ U.carrier).Nonempty →
      U.carrier ⊆ W := by
    intro U hplane_U hangle_U hinter_U
    intro x hx
    have h_bounds := direction_band_containment_bounds
      hδ hδ1 T n C0 σ hC0 hσ2 v e2 e3 hv he2_unit he3_unit hv_e2 hv_e3
      h_e2_bound (by rfl) c (by rfl) h0 h1 h2
      (by have h9 : h0 = 9 / 2 := rfl; rw [h9]; linarith [hδ1])
      (by have h9 : h1 = 8 * (C0 + 1) * δ := rfl; rw [h9]; nlinarith)
      (by have h9 : h2 = 5 * max σ δ := rfl; rw [h9];
          have h_a : 2 * σ ≤ 2 * max σ δ := by have h_b : σ ≤ max σ δ := le_max_left σ δ; gcongr
          have h_c : 3 * δ ≤ 3 * max σ δ := by have h_d : δ ≤ max σ δ := le_max_right σ δ; gcongr
          linarith)
      U hplane_U hangle_U hinter_U x hx
    simpa [W] using h_bounds
  -- Volume bound
  let d0 : ℝ := 9
  let d1 : ℝ := 16 * (C0 + 1) * δ
  let d2 : ℝ := 10 * max σ δ
  have hd0 : 0 ≤ d0 := by positivity
  have hd1 : 0 ≤ d1 := by positivity
  have hd2 : 0 ≤ d2 := by positivity
  have h_abs_sub : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
    intro a b
    have h1 := IsAbsoluteValue.abv_add abs a (-b)
    have h2 : |(-b)| = |b| := by simp
    rw [h2] at h1
    have h3 : a + (-b) = a - b := by ring
    rw [h3] at h1
    exact h1
  have h_diff0 : ∀ (x y : Point3), (A x) 0 - (A y) 0 =
      inner ℝ (x - c) v - inner ℝ (y - c) v := by
    intro x y
    rw [hcoord0 x, hcoord0 y]
    have h_i1 : inner ℝ x v = inner ℝ (x - c) v + inner ℝ c v := by
      rw [←inner_add_left, sub_add_cancel]
    have h_i2 : inner ℝ y v = inner ℝ (y - c) v + inner ℝ c v := by
      rw [←inner_add_left, sub_add_cancel]
    rw [h_i1, h_i2] <;> abel
  have h_diff1 : ∀ (x y : Point3), (A x) 1 - (A y) 1 =
      inner ℝ (x - c) e2 - inner ℝ (y - c) e2 := by
    intro x y
    rw [hcoord1 x, hcoord1 y]
    have h_i1 : inner ℝ x e2 = inner ℝ (x - c) e2 + inner ℝ c e2 := by
      rw [←inner_add_left, sub_add_cancel]
    have h_i2 : inner ℝ y e2 = inner ℝ (y - c) e2 + inner ℝ c e2 := by
      rw [←inner_add_left, sub_add_cancel]
    rw [h_i1, h_i2] <;> abel
  have h_diff2 : ∀ (x y : Point3), (A x) 2 - (A y) 2 =
      inner ℝ (x - c) e3 - inner ℝ (y - c) e3 := by
    intro x y
    rw [hcoord2 x, hcoord2 y]
    have h_i1 : inner ℝ x e3 = inner ℝ (x - c) e3 + inner ℝ c e3 := by
      rw [←inner_add_left, sub_add_cancel]
    have h_i2 : inner ℝ y e3 = inner ℝ (y - c) e3 + inner ℝ c e3 := by
      rw [←inner_add_left, sub_add_cancel]
    rw [h_i1, h_i2] <;> abel
  have h_d0_eq : d0 = 2 * h0 := by dsimp only [d0, h0] <;> norm_num
  have h_d1_eq : d1 = 2 * h1 := by dsimp only [d1, h1] <;> ring
  have h_d2_eq : d2 = 2 * h2 := by dsimp only [d2, h2] <;> ring
  have h_diam0 : ∀ x y, x ∈ W → y ∈ W → |(A x) 0 - (A y) 0| ≤ d0 := by
    intro x y hx hy
    have hxa : |inner ℝ (x - c) v| ≤ h0 := hx.1
    have hya : |inner ℝ (y - c) v| ≤ h0 := hy.1
    rw [h_diff0 x y, h_d0_eq]
    have h_tri := h_abs_sub (inner ℝ (x - c) v) (inner ℝ (y - c) v)
    linarith
  have h_diam1 : ∀ x y, x ∈ W → y ∈ W → |(A x) 1 - (A y) 1| ≤ d1 := by
    intro x y hx hy
    have hxa : |inner ℝ (x - c) e2| ≤ h1 := hx.2.1
    have hya : |inner ℝ (y - c) e2| ≤ h1 := hy.2.1
    rw [h_diff1 x y, h_d1_eq]
    have h_tri := h_abs_sub (inner ℝ (x - c) e2) (inner ℝ (y - c) e2)
    linarith
  have h_diam2 : ∀ x y, x ∈ W → y ∈ W → |(A x) 2 - (A y) 2| ≤ d2 := by
    intro x y hx hy
    have hxa : |inner ℝ (x - c) e3| ≤ h2 := hx.2.2
    have hya : |inner ℝ (y - c) e3| ≤ h2 := hy.2.2
    rw [h_diff2 x y, h_d2_eq]
    have h_tri := h_abs_sub (inner ℝ (x - c) e3) (inner ℝ (y - c) e3)
    linarith
  have h_vol : MeasureTheory.volume W ≤ ENNReal.ofReal (d0 * d1 * d2) :=
    volume_diameter_bound hW_meas A d0 d1 d2 hd0 hd1 hd2 h_diam0 h_diam1 h_diam2
  have h_final : d0 * d1 * d2 ≤ 2000 * (C0 + 1) * max σ δ * δ := by
    dsimp only [d0, d1, d2]
    have h_pos : 0 ≤ δ := by linarith
    ring_nf
    nlinarith
  have h_vol2 : MeasureTheory.volume W ≤ ENNReal.ofReal (2000 * (C0 + 1) * max σ δ * δ) := by
    have h_nonneg : 0 ≤ 2000 * (C0 + 1) * max σ δ * δ := by positivity
    exact h_vol.trans (ENNReal.ofReal_le_ofReal h_final)
  exact ⟨W, hW_conv, h_containment, h_vol2⟩

end Kakeya.Hairbrush
