module

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.BoundedOverlapHelpers

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
open scoped Classical

noncomputable section

namespace RadialBootstrapping


-- ============================================================================
-- 6. Real packing lemma
-- ============================================================================

lemma real_packing_simple {s : Finset ℝ} {δ W : ℝ} (hδ : 0 < δ) (hW : 0 ≤ W)
    (hlo : ∀ x ∈ s, 0 ≤ x) (hhi : ∀ x ∈ s, x ≤ W)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → |x - y| ≥ δ) :
    s.card ≤ Nat.floor (W / δ) + 1 := by
  by_cases h_empty : s = ∅
  · rw [h_empty] <;> simp
  · have h_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let x_min := Finset.min' s h_nonempty
    have hx_min_mem : x_min ∈ s := Finset.min'_mem s h_nonempty
    have hx_min_lo : ∀ x ∈ s, x_min ≤ x := fun x hx => Finset.min'_le s x hx
    have h_xmin_ge0 : 0 ≤ x_min := hlo x_min hx_min_mem
    let f : ℝ → ℕ := fun x => Nat.floor ((x - x_min) / δ)
    have h_inj : Set.InjOn f (s : Set ℝ) := by
      intro x hx y hy h_eq
      by_contra h_ne
      have h3 : |x - y| ≥ δ := hsep x hx y hy h_ne
      by_cases hxy : x ≤ y
      · -- Case x ≤ y
        have h4 : y - x ≥ δ := by
          have h5 : |x - y| = y - x := by
            rw [abs_of_nonpos (show x - y ≤ 0 by linarith)] <;> linarith
          linarith
        have h_ymin : x_min ≤ y := hx_min_lo y hy
        have h6 : (y - x_min) / δ ≥ (x - x_min) / δ + 1 := by
          have h7 : (y - x_min) / δ - (x - x_min) / δ = (y - x) / δ := by
            field_simp [hδ.ne'] <;> ring
          have h8 : (y - x) / δ ≥ 1 := by
            calc (y - x) / δ ≥ δ / δ := by gcongr
                 _ = 1 := by field_simp [hδ.ne']
          linarith
        have h_xnonneg : 0 ≤ (x - x_min) / δ := by
          have h : 0 ≤ x - x_min := by linarith [hx_min_lo x hx]
          positivity
        have h_floor_le : (Nat.floor ((x - x_min) / δ) : ℝ) ≤ (x - x_min) / δ :=
          Nat.floor_le h_xnonneg
        have h12 : (Nat.floor ((x - x_min) / δ) : ℝ) + 1 ≤ (y - x_min) / δ := by linarith
        have h13 : 0 ≤ (y - x_min) / δ := by
          have h131 : 0 ≤ y - x_min := by linarith
          positivity
        have h14 : Nat.floor ((x - x_min) / δ) + 1 ≤ Nat.floor ((y - x_min) / δ) := by
          rw [Nat.le_floor_iff h13]
          simpa [Nat.cast_add] using h12
        have h10 : f y > f x := by
          dsimp only [f]
          exact h14
        rw [h_eq] at h10 <;> linarith
      · -- Case y < x
        have hxy' : y ≤ x := by linarith
        have h4 : x - y ≥ δ := by
          have h5 : |x - y| = x - y := by
            rw [abs_of_nonneg (show 0 ≤ x - y by linarith)] <;> linarith
          linarith
        have h_xmin : x_min ≤ x := hx_min_lo x hx
        have h6 : (x - x_min) / δ ≥ (y - x_min) / δ + 1 := by
          have h7 : (x - x_min) / δ - (y - x_min) / δ = (x - y) / δ := by
            field_simp [hδ.ne'] <;> ring
          have h8 : (x - y) / δ ≥ 1 := by
            calc (x - y) / δ ≥ δ / δ := by gcongr
                 _ = 1 := by field_simp [hδ.ne']
          linarith
        have h_ynonneg : 0 ≤ (y - x_min) / δ := by
          have h : 0 ≤ y - x_min := by linarith [hx_min_lo y hy]
          positivity
        have h_floor_le : (Nat.floor ((y - x_min) / δ) : ℝ) ≤ (y - x_min) / δ :=
          Nat.floor_le h_ynonneg
        have h12 : (Nat.floor ((y - x_min) / δ) : ℝ) + 1 ≤ (x - x_min) / δ := by linarith
        have h13 : 0 ≤ (x - x_min) / δ := by
          have h131 : 0 ≤ x - x_min := by linarith
          positivity
        have h14 : Nat.floor ((y - x_min) / δ) + 1 ≤ Nat.floor ((x - x_min) / δ) := by
          rw [Nat.le_floor_iff h13]
          simpa [Nat.cast_add] using h12
        have h10 : f x > f y := by
          dsimp only [f]
          exact h14
        rw [h_eq] at h10 <;> linarith
    have h_image : (s.image f).card = s.card :=
      Finset.card_image_of_injOn h_inj
    have h_sub : s.image f ⊆ Finset.range (Nat.floor (W / δ) + 1) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      have h11 : 0 ≤ (x - x_min) / δ := by
        have h12 : 0 ≤ x - x_min := by linarith [hx_min_lo x hx]
        positivity
      have h13 : (x - x_min) / δ ≤ W / δ := by
        have h14 : x - x_min ≤ W := by linarith [hhi x hx, h_xmin_ge0]
        gcongr
      have h15 : f x < Nat.floor (W / δ) + 1 := by
        dsimp only [f]
        have h16 : Nat.floor ((x - x_min) / δ) ≤ Nat.floor (W / δ) := Nat.floor_mono h13
        exact Nat.lt_succ_of_le h16
      exact Finset.mem_range.mpr h15
    have h15 : (s.image f).card ≤ (Finset.range (Nat.floor (W / δ) + 1)).card :=
      Finset.card_le_card h_sub
    rw [h_image] at h15
    simpa using h15

-- ============================================================================
-- 7. arcsin bound: arcsin x ≤ (π/2) * x for x ∈ [0,1]
-- ============================================================================

lemma arcsin_le_pi_div_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  let y := Real.arcsin x
  have hy0 : 0 ≤ y := Real.arcsin_nonneg.mpr h0
  have hy1 : y ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two x
  have hsin : Real.sin y = x := Real.sin_arcsin (by linarith) h1
  have h_jordan : (2 / Real.pi) * y ≤ x := by
    have h : (2 / Real.pi) * y ≤ Real.sin y := Real.mul_le_sin hy0 hy1
    rw [hsin] at h; exact h
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h_goal : y ≤ (Real.pi / 2) * x := by
    calc y
      = (Real.pi / 2) * ((2 / Real.pi) * y) := by field_simp [hpi_pos.ne'] <;> ring
    _ ≤ (Real.pi / 2) * x := by gcongr
  exact h_goal

-- ============================================================================
-- 8. Main bounded overlap theorem
-- ============================================================================

/-- Given a 1-dimensional submodule, there exists a nonzero vector in it. -/
lemma exists_nonzero_in_submodule (V : Submodule ℝ Point)
    (hV : Module.finrank ℝ V = 1) : ∃ (v : Point), v ∈ V ∧ v ≠ 0 := by
  have hV_ne_bot : V ≠ (⊥ : Submodule ℝ Point) := by
    intro h
    rw [h] at hV
    simp at hV
  by_contra h
  push Not at h
  have hV_bot : V = (⊥ : Submodule ℝ Point) := by
    ext x
    simp only [Submodule.mem_bot]
    constructor
    · intro hx
      exact h x hx
    · intro hx
      rw [hx]
      exact Submodule.zero_mem V
  exact hV_ne_bot hV_bot

/-- Given a 1D submodule V and a vector u₀, there exists a unit vector in V
with non-negative inner product with u₀. -/
lemma exists_unit_vector_with_inner_nonneg (V : Submodule ℝ Point)
    (hV : Module.finrank ℝ V = 1) (u₀ : Point) :
    ∃ (u : Point), u ∈ V ∧ ‖u‖ = 1 ∧ 0 ≤ inner ℝ u u₀ := by
  have h_exists : ∃ (v : Point), v ∈ V ∧ v ≠ 0 := exists_nonzero_in_submodule V hV
  rcases h_exists with ⟨v, hvV, hvne⟩
  let v' : Point := (1 / ‖v‖) • v
  have hv'V : v' ∈ V := V.smul_mem (1 / ‖v‖) hvV
  have hnorm_v' : ‖v'‖ = 1 := by
    simp [v', norm_smul, hvne] <;> field_simp [hvne] <;> ring_nf <;> norm_num
  by_cases h : inner ℝ v' u₀ ≥ 0
  · exact ⟨v', hv'V, hnorm_v', h⟩
  · have h' : 0 ≤ inner ℝ (-v') u₀ := by
      have h'' : inner ℝ (-v') u₀ = -inner ℝ v' u₀ := by simp [inner_neg_left]
      rw [h'']; linarith
    exact ⟨-v', V.neg_mem hv'V, by rw [norm_neg]; exact hnorm_v', h'⟩

/-- Choose a unit vector in the 1D submodule V with non-negative inner product with u₀. -/
def chooseUnitVector (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) (u₀ : Point) : Point :=
  Classical.choose (exists_unit_vector_with_inner_nonneg V hV u₀)

lemma chooseUnitVector_mem (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) (u₀ : Point) :
    chooseUnitVector V hV u₀ ∈ V :=
  (Classical.choose_spec (exists_unit_vector_with_inner_nonneg V hV u₀)).1

lemma chooseUnitVector_norm (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) (u₀ : Point) :
    ‖chooseUnitVector V hV u₀‖ = 1 :=
  (Classical.choose_spec (exists_unit_vector_with_inner_nonneg V hV u₀)).2.1

lemma chooseUnitVector_inner (V : Submodule ℝ Point) (hV : Module.finrank ℝ V = 1) (u₀ : Point) :
    0 ≤ inner ℝ (chooseUnitVector V hV u₀) u₀ :=
  (Classical.choose_spec (exists_unit_vector_with_inner_nonneg V hV u₀)).2.2

/-- Parseval identity for the orthonormal basis {u₀, rot90(u₀)}. -/
lemma parseval_two_d (u₀ : Point) (hnu₀ : ‖u₀‖ = 1) (u : Point) (hu_norm : ‖u‖ = 1) :
    (inner ℝ u u₀) ^ 2 + (inner ℝ u (rot90 u₀)) ^ 2 = 1 := by
  set a := inner ℝ u u₀ with ha
  set b := inner ℝ u (rot90 u₀) with hb
  have h_fourier : u = a • u₀ + b • rot90 u₀ := fourier_expansion u₀ hnu₀ u
  have h_orth : inner ℝ (a • u₀) (b • rot90 u₀) = 0 := by
    simp [ha, hb, inner_smul_left, inner_smul_right, rot90_inner_self] <;> ring
  have h_main : ‖u‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [h_fourier]
    have h := norm_add_sq_real (a • u₀) (b • rot90 u₀)
    rw [h, h_orth]
    have h1 : ‖a • u₀‖ ^ 2 = a ^ 2 := by
      simp [norm_smul, hnu₀] <;> ring
    have h2 : ‖b • rot90 u₀‖ ^ 2 = b ^ 2 := by
      have h_rot : ‖rot90 u₀‖ = 1 := by
        rw [rot90_norm u₀, hnu₀] <;> norm_num
      simp [norm_smul, h_rot] <;> ring
    rw [h1, h2] <;> ring
  rw [hu_norm] at h_main
  have h_final : a ^ 2 + b ^ 2 = 1 := by
    simpa [ha, hb] using h_main.symm
  exact h_final

/-- Angle coordinate identity: if `u` is a unit vector with `0 ≤ inner(u, u₀)`,
and `θ = arcsin(inner(u, rot90(u₀)))`, then `u = cos θ • u₀ + sin θ • rot90(u₀)`. -/
lemma angle_coordinate_identity (u₀ : Point) (hnu₀ : ‖u₀‖ = 1)
    (u : Point) (hu_norm : ‖u‖ = 1) (hu_inner : 0 ≤ inner ℝ u u₀)
    (θ : ℝ) (hθ_def : θ = Real.arcsin (inner ℝ u (rot90 u₀)))
    (hθ_bound : |θ| ≤ Real.pi / 2) :
    u = Real.cos θ • u₀ + Real.sin θ • rot90 u₀ := by
  have h_arg1 : -1 ≤ inner ℝ u (rot90 u₀) := by
    have h := abs_le.mp (abs_real_inner_le_norm u (rot90 u₀))
    have h9 : ‖rot90 u₀‖ = 1 := by
      rw [rot90_norm u₀, hnu₀] <;> norm_num
    have h10 : ‖u‖ = 1 := hu_norm
    rw [h10, h9] at h; linarith
  have h_arg2 : inner ℝ u (rot90 u₀) ≤ 1 := by
    have h := abs_le.mp (abs_real_inner_le_norm u (rot90 u₀))
    have h9 : ‖rot90 u₀‖ = 1 := by
      rw [rot90_norm u₀, hnu₀] <;> norm_num
    have h10 : ‖u‖ = 1 := hu_norm
    rw [h10, h9] at h; linarith
  have h_sin : Real.sin θ = inner ℝ u (rot90 u₀) := by
    rw [hθ_def, Real.sin_arcsin h_arg1 h_arg2]
  have h_fourier : u = inner ℝ u u₀ • u₀ + inner ℝ u (rot90 u₀) • rot90 u₀ :=
    fourier_expansion u₀ hnu₀ u
  have h_norm_sq : (inner ℝ u u₀) ^ 2 + (inner ℝ u (rot90 u₀)) ^ 2 = 1 :=
    parseval_two_d u₀ hnu₀ u hu_norm
  have h_cos_sq : Real.cos θ ^ 2 = (inner ℝ u u₀) ^ 2 := by
    have h1 : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    rw [h_sin] at h1; linarith
  have h_cos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_le.mp hθ_bound], by linarith [abs_le.mp hθ_bound]⟩
  have h_cos : Real.cos θ = inner ℝ u u₀ := by
    nlinarith [h_cos_sq, h_cos_nonneg, hu_inner]
  rw [h_cos, h_sin]
  exact h_fourier

/-- **Bounded overlap pair**: If a family of lines is `(r/ξ)`-separated in
direction distance, and `dist(x,y) ≥ ξ`, then at most `13` lines have both
`x` and `y` in their `2r`-tubes (assuming `4r/ξ ≤ 1`). -/
lemma bounded_overlap_pair
    {T : Finset Line2} {r ξ : ℝ} (hr : 0 < r) (hξ : 0 < ξ)
    (h_sep : ∀ L1 ∈ T, ∀ L2 ∈ T, L1 ≠ L2 → lineDirDist L1 L2 ≥ r / ξ)
    {x y : Point} (hxy : ξ ≤ dist x y)
    (h_small : 4 * r / ξ ≤ 1) :
    (T.filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)).card ≤ 13 := by
  classical
  let S := T.filter (fun L => x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L)
  have hS_sub : S ⊆ T := Finset.filter_subset _ _
  have hS_prop : ∀ L ∈ S, x ∈ tube (2 * r) L ∧ y ∈ tube (2 * r) L := by
    intro L hL; exact (Finset.mem_filter.mp hL).2
  by_cases hS_empty : S = ∅
  · have h_card : S.card = 0 := by rw [hS_empty]; simp
    have h_goal : S.card ≤ 13 := by rw [h_card]; norm_num
    exact h_goal
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hxy_ne : x ≠ y := by
      intro h; rw [h] at hxy; simp at hxy <;> linarith
    let w : Point := y - x
    have hw_ne : w ≠ 0 := by
      intro h
      have h' : y - x = 0 := h
      have h_eq : y = x := by simpa [sub_eq_zero] using h'
      exact hxy_ne h_eq.symm
    have hnorm_w : ‖w‖ ≥ ξ := by
      have hrev : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      rw [hrev]
      simpa [w, dist_eq_norm] using hxy
    let V₀ := Submodule.span ℝ {w}
    have hV₀ : Module.finrank ℝ V₀ = 1 := by
      rw [finrank_span_singleton hw_ne] <;> norm_num
    let u₀ : Point := (1 / ‖w‖) • w
    have hnu₀ : ‖u₀‖ = 1 := by
      simp [u₀, norm_smul, hnorm_w] <;> field_simp [hnorm_w] <;> ring_nf <;> norm_num
    have hu₀V : u₀ ∈ V₀ := by
      rw [Submodule.mem_span_singleton]; refine' ⟨1 / ‖w‖, _⟩ <;> simp [u₀] <;> ring
    let R := 4 * r / ξ
    have hR0 : 0 ≤ R := by positivity
    have hR1 : R ≤ 1 := h_small
    let δ := r / ξ
    have hδ0 : 0 < δ := by positivity
    have h_close : ∀ L ∈ S, submoduleDirDist L.toAffine.direction V₀ ≤ R := by
      intro L hL
      have h1 := hS_prop L hL
      have h2 := direction_closeness r hr L x y hxy_ne.symm h1.1 h1.2
      have h3 : ‖w‖ ≥ ξ := hnorm_w
      have h4 : 4 * r / ‖w‖ ≤ 4 * r / ξ := by gcongr
      exact h2.trans h4
    -- Choose unit vector u_L in direction of L with inner(u_L, u₀) ≥ 0
    let choose_u (L : Line2) : Point := chooseUnitVector L.toAffine.direction L.2 u₀
    have hchoose_mem : ∀ L ∈ S, choose_u L ∈ L.toAffine.direction :=
      fun L _ => chooseUnitVector_mem L.toAffine.direction L.2 u₀
    have hchoose_norm : ∀ L ∈ S, ‖choose_u L‖ = 1 :=
      fun L _ => chooseUnitVector_norm L.toAffine.direction L.2 u₀
    have hchoose_inner : ∀ L ∈ S, 0 ≤ inner ℝ (choose_u L) u₀ :=
      fun L _ => chooseUnitVector_inner L.toAffine.direction L.2 u₀
    -- Angle coordinate θ(L) = arcsin(inner(u_L, rot90(u₀)))
    let θ : Line2 → ℝ := fun L => Real.arcsin (inner ℝ (choose_u L) (rot90 u₀))
    have hθ_range : ∀ L ∈ S, |θ L| ≤ Real.arcsin R := by
      intro L hL
      have h1 : submoduleDirDist L.toAffine.direction V₀ =
          ‖u₀ - L.toAffine.direction.orthogonalProjectionFn u₀‖ :=
        submoduleDirDist_eq_perp L.toAffine.direction V₀ L.2 hV₀ u₀ hu₀V hnu₀
      have h2 : submoduleDirDist L.toAffine.direction V₀ ≤ R := h_close L hL
      have h2' : ‖u₀ - L.toAffine.direction.orthogonalProjectionFn u₀‖ ≤ R := by
        rw [←h1]; exact h2
      have hproj : L.toAffine.direction.orthogonalProjectionFn u₀ =
          inner ℝ u₀ (choose_u L) • choose_u L :=
        projection_one_dim L.toAffine.direction (choose_u L) u₀
          (hchoose_mem L hL) (hchoose_norm L hL) L.2
      rw [hproj] at h2'
      set c := inner ℝ u₀ (choose_u L) with hc
      have h3 : ‖u₀ - c • choose_u L‖ ^ 2 = 1 - c ^ 2 := by
        have h4 := norm_sub_sq_real u₀ (c • choose_u L)
        rw [h4]
        have h5 : inner ℝ u₀ (c • choose_u L) = c ^ 2 := by
          rw [inner_smul_right, hc] <;> ring
        have h6 : ‖c • choose_u L‖ ^ 2 = c ^ 2 := by
          have h7 : ‖c • choose_u L‖ = |c| * ‖choose_u L‖ := norm_smul c (choose_u L)
          rw [h7, hchoose_norm L hL] <;> simp [abs_pow] <;> ring
        rw [h5, h6, hnu₀] <;> ring
      have h2_sq : ‖u₀ - c • choose_u L‖ ^ 2 ≤ R ^ 2 := by
        have hR_nonneg : 0 ≤ R := hR0
        nlinarith [h2', norm_nonneg (u₀ - c • choose_u L)]
      rw [h3] at h2_sq
      have h4 : 1 - c ^ 2 ≤ R ^ 2 := h2_sq
      have h_comm : inner ℝ (choose_u L) u₀ = inner ℝ u₀ (choose_u L) := by exact real_inner_comm u₀ (choose_u L)
      have h5 : (inner ℝ (choose_u L) (rot90 u₀)) ^ 2 = 1 - c ^ 2 := by
        have h_parseval := parseval_two_d u₀ hnu₀ (choose_u L) (hchoose_norm L hL)
        rw [h_comm] at h_parseval
        linarith
      have h6 : (inner ℝ (choose_u L) (rot90 u₀)) ^ 2 ≤ R ^ 2 := by linarith
      have h7 : |inner ℝ (choose_u L) (rot90 u₀)| ≤ R := by
        let x := inner ℝ (choose_u L) (rot90 u₀)
        have h_abs_sq : |x| ^ 2 = x ^ 2 := by
          have h : |x| ^ 2 = |x ^ 2| := by exact pow_abs x 2
          rw [h]
          have h2 : 0 ≤ x ^ 2 := by positivity
          rw [abs_of_nonneg h2]
        have h : |x| ^ 2 ≤ R ^ 2 := by rw [h_abs_sq]; exact h6
        have hR_nonneg : 0 ≤ R := hR0
        by_contra h9
        have h10 : |x| > R := by linarith
        have h11 : |x| ^ 2 > R ^ 2 := by gcongr
        linarith
      set z := inner ℝ (choose_u L) (rot90 u₀) with hz
      have hz_abs : |z| ≤ R := h7
      have hz1 : -1 ≤ z := by
        have h_cs := abs_real_inner_le_norm (choose_u L) (rot90 u₀)
        have h_rot : ‖rot90 u₀‖ = 1 := by
          rw [rot90_norm u₀, hnu₀] <;> norm_num
        rw [hchoose_norm L hL, h_rot] at h_cs
        linarith [abs_le.mp h_cs]
      have hz2 : z ≤ 1 := by
        have h_cs := abs_real_inner_le_norm (choose_u L) (rot90 u₀)
        have h_rot : ‖rot90 u₀‖ = 1 := by
          rw [rot90_norm u₀, hnu₀] <;> norm_num
        rw [hchoose_norm L hL, h_rot] at h_cs
        linarith [abs_le.mp h_cs]
      have h11 : |Real.arcsin z| ≤ Real.arcsin R := by
        by_cases h_nonneg : 0 ≤ z
        · have h12 : 0 ≤ Real.arcsin z := Real.arcsin_nonneg.mpr h_nonneg
          have h13 : z ≤ R := by linarith [abs_le.mp hz_abs]
          have h14 : Real.arcsin z ≤ Real.arcsin R := Real.arcsin_le_arcsin h13
          rw [abs_of_nonneg h12] <;> exact h14
        · have h_neg : z < 0 := by linarith
          have h14 : 0 ≤ -z := by linarith
          have h15 : -z ≤ R := by linarith [abs_le.mp hz_abs]
          have h16 : Real.arcsin z = -Real.arcsin (-z) := by
            rw [←Real.arcsin_neg] <;> ring_nf
          rw [h16]
          have h17 : 0 ≤ Real.arcsin (-z) := Real.arcsin_nonneg.mpr h14
          rw [abs_neg, abs_of_nonneg h17]
          have h18 : -z ≤ R := by linarith [abs_le.mp hz_abs]
          exact Real.arcsin_le_arcsin h18
      simpa [θ, hz] using h11
    -- Pairwise angular separation: |θ(L1) - θ(L2)| ≥ δ
    have hθ_sep : ∀ L1 ∈ S, ∀ L2 ∈ S, L1 ≠ L2 → |θ L1 - θ L2| ≥ δ := by
      intro L1 hL1 L2 hL2 hne
      have h1 : lineDirDist L1 L2 ≥ δ := h_sep L1 (hS_sub hL1) L2 (hS_sub hL2) hne
      let u1 := choose_u L1
      let u2 := choose_u L2
      have hproj1 : L1.toAffine.direction.orthogonalProjectionFn u2 =
          inner ℝ u2 u1 • u1 :=
        projection_one_dim L1.toAffine.direction u1 u2
          (hchoose_mem L1 hL1) (hchoose_norm L1 hL1) L1.2
      have h_id : submoduleDirDist L1.toAffine.direction L2.toAffine.direction =
          ‖u2 - L1.toAffine.direction.orthogonalProjectionFn u2‖ :=
        submoduleDirDist_eq_perp L1.toAffine.direction L2.toAffine.direction
          L1.2 L2.2 u2 (hchoose_mem L2 hL2) (hchoose_norm L2 hL2)
      have h1' : submoduleDirDist L1.toAffine.direction L2.toAffine.direction ≥ δ := by
        simpa [lineDirDist] using h1
      have h1_dist : ‖u2 - L1.toAffine.direction.orthogonalProjectionFn u2‖ ≥ δ := by
        rw [←h_id]; exact h1'
      have h1_dist2 : ‖u2 - inner ℝ u2 u1 • u1‖ ≥ δ := by
        rw [hproj1] at h1_dist; exact h1_dist
      set d := inner ℝ u2 u1 with hd
      have h_norm : ‖u2 - d • u1‖ ^ 2 = 1 - d ^ 2 := by
        have h4 := norm_sub_sq_real u2 (d • u1)
        rw [h4]
        have h5 : inner ℝ u2 (d • u1) = d ^ 2 := by
          rw [inner_smul_right, hd] <;> ring
        have h6 : ‖d • u1‖ ^ 2 = d ^ 2 := by
          have h7 : ‖d • u1‖ = |d| * ‖u1‖ := norm_smul d u1
          rw [h7, hchoose_norm L1 hL1] <;> simp [abs_pow] <;> ring
        rw [h5, h6, hchoose_norm L2 hL2] <;> ring
      have h1_sq : ‖u2 - d • u1‖ ^ 2 ≥ δ ^ 2 := by
        have hδ_nonneg : 0 ≤ δ := by positivity
        have h_nonneg : 0 ≤ ‖u2 - d • u1‖ := norm_nonneg _
        gcongr
      have h_sin2 : 1 - d ^ 2 ≥ δ ^ 2 := by
        rw [h_norm] at h1_sq; exact h1_sq
      have hθ_bound1 : |θ L1| ≤ Real.pi / 2 := by
        have h3 : |θ L1| ≤ Real.arcsin R := hθ_range L1 hL1
        have h4 : Real.arcsin R ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two R
        calc |θ L1| ≤ Real.arcsin R := h3
             _ ≤ Real.pi / 2 := h4
      have hθ_bound2 : |θ L2| ≤ Real.pi / 2 := by
        have h3 : |θ L2| ≤ Real.arcsin R := hθ_range L2 hL2
        have h4 : Real.arcsin R ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two R
        calc |θ L2| ≤ Real.arcsin R := h3
             _ ≤ Real.pi / 2 := h4
      have h_f1 : u1 = Real.cos (θ L1) • u₀ + Real.sin (θ L1) • rot90 u₀ :=
        angle_coordinate_identity u₀ hnu₀ u1 (hchoose_norm L1 hL1)
          (hchoose_inner L1 hL1) (θ L1) rfl hθ_bound1
      have h_f2 : u2 = Real.cos (θ L2) • u₀ + Real.sin (θ L2) • rot90 u₀ :=
        angle_coordinate_identity u₀ hnu₀ u2 (hchoose_norm L2 hL2)
          (hchoose_inner L2 hL2) (θ L2) rfl hθ_bound2
      have h_cos_diff : Real.cos (θ L2 - θ L1) = inner ℝ u2 u1 := by
        rw [h_f1, h_f2]
        set c1 := Real.cos (θ L1) with hc1
        set s1 := Real.sin (θ L1) with hs1
        set c2 := Real.cos (θ L2) with hc2
        set s2 := Real.sin (θ L2) with hs2
        have h_rot90_self : inner ℝ (rot90 u₀) (rot90 u₀) = 1 := by
          have h : inner ℝ (rot90 u₀) (rot90 u₀) = ‖rot90 u₀‖ ^ 2 := by exact real_inner_self_eq_norm_sq (rot90 u₀)
          rw [h]
          have h2 : ‖rot90 u₀‖ = 1 := by
            rw [rot90_norm u₀, hnu₀] <;> norm_num
          rw [h2] <;> norm_num
        have h_u0_self : inner ℝ u₀ u₀ = 1 := by
          have h : inner ℝ u₀ u₀ = ‖u₀‖ ^ 2 := by exact real_inner_self_eq_norm_sq u₀
          rw [h, hnu₀] <;> norm_num
        have h_cross1 : inner ℝ u₀ (rot90 u₀) = 0 := rot90_inner_self u₀
        have h_cross2 : inner ℝ (rot90 u₀) u₀ = 0 := by
          have h_comm : inner ℝ (rot90 u₀) u₀ = inner ℝ u₀ (rot90 u₀) := by exact real_inner_comm u₀ (rot90 u₀)
          rw [h_comm]; exact h_cross1
        have h_expand : inner ℝ (c2 • u₀ + s2 • rot90 u₀) (c1 • u₀ + s1 • rot90 u₀) =
            c2 * c1 + s2 * s1 := by
          have h_rot_norm : ‖rot90 u₀‖ ^ 2 = 1 := by
            have h2 : ‖rot90 u₀‖ = 1 := by
              rw [rot90_norm u₀, hnu₀] <;> norm_num
            rw [h2] <;> norm_num
          simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
            h_u0_self, h_rot90_self, h_cross1, h_cross2, hnu₀, h_rot_norm] <;> ring
        rw [h_expand]
        have h_cos_sub : Real.cos (θ L2 - θ L1) = c2 * c1 + s2 * s1 := by
          simp [hc1, hs1, hc2, hs2, Real.cos_sub] <;> ring
        exact h_cos_sub
      have h_sin_diff2 : Real.sin (θ L2 - θ L1) ^ 2 = 1 - (inner ℝ u2 u1) ^ 2 := by
        have h_eq : Real.sin (θ L2 - θ L1) ^ 2 + Real.cos (θ L2 - θ L1) ^ 2 = 1 :=
          Real.sin_sq_add_cos_sq (θ L2 - θ L1)
        have h : Real.sin (θ L2 - θ L1) ^ 2 = 1 - Real.cos (θ L2 - θ L1) ^ 2 := by linarith
        rw [h, h_cos_diff] <;> ring
      have h11 : Real.sin (θ L2 - θ L1) ^ 2 ≥ δ ^ 2 := by
        rw [h_sin_diff2]; exact h_sin2
      have h12 : |Real.sin (θ L2 - θ L1)| ≥ δ := by
        let x := Real.sin (θ L2 - θ L1)
        have h_abs_sq : |x| ^ 2 = x ^ 2 := by
          have h : |x| ^ 2 = |x ^ 2| := by exact pow_abs x 2
          rw [h]
          have h2 : 0 ≤ x ^ 2 := by positivity
          rw [abs_of_nonneg h2]
        have h : |x| ^ 2 ≥ δ ^ 2 := by rw [h_abs_sq]; exact h11
        have hδ_pos : 0 < δ := hδ0
        by_contra h13
        have h14 : |x| < δ := by linarith
        have h15 : |x| ^ 2 < δ ^ 2 := by gcongr
        linarith
      have h14 : |Real.sin (θ L2 - θ L1)| ≤ |θ L2 - θ L1| := by exact Real.abs_sin_le_abs
      have h15 : |θ L2 - θ L1| ≥ δ := by linarith
      have h16 : |θ L1 - θ L2| = |θ L2 - θ L1| := by
        rw [show θ L1 - θ L2 = -(θ L2 - θ L1) by abel]; rw [abs_neg]
      rw [h16]; exact h15
    -- Shift angles to [0, 2*arcsin(R)] and pack
    let α := Real.arcsin R
    have hα0 : 0 ≤ α := Real.arcsin_nonneg.mpr hR0
    have hα_le : α ≤ (Real.pi / 2) * R := arcsin_le_pi_div_two_mul hR0 hR1
    let φ : Line2 → ℝ := fun L => θ L + α
    have hφ0 : ∀ L ∈ S, 0 ≤ φ L := by
      intro L hL; have h : |θ L| ≤ α := hθ_range L hL; linarith [abs_le.mp h]
    have hφ1 : ∀ L ∈ S, φ L ≤ 2 * α := by
      intro L hL; have h : |θ L| ≤ α := hθ_range L hL; linarith [abs_le.mp h]
    have hφ_sep : ∀ L1 ∈ S, ∀ L2 ∈ S, L1 ≠ L2 → |φ L1 - φ L2| ≥ δ := by
      intro L1 hL1 L2 hL2 hne
      have h : φ L1 - φ L2 = θ L1 - θ L2 := by simp [φ] <;> abel
      rw [h]; exact hθ_sep L1 hL1 L2 hL2 hne
    let s : Finset ℝ := S.image φ
    have h_inj : Set.InjOn φ (S : Set Line2) := by
      intro L1 hL1 L2 hL2 h
      by_contra hne
      have h5 : |φ L1 - φ L2| ≥ δ := hφ_sep L1 hL1 L2 hL2 hne
      rw [h] at h5
      have h6 : (0 : ℝ) ≥ δ := by simpa using h5
      linarith [hδ0]
    have h_card : s.card = S.card := Finset.card_image_of_injOn h_inj
    have hlo_s : ∀ x ∈ s, 0 ≤ x := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨L, hL, rfl⟩
      exact hφ0 L hL
    have hhi_s : ∀ x ∈ s, x ≤ 2 * α := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨L, hL, rfl⟩
      exact hφ1 L hL
    have hsep_s : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → |x - y| ≥ δ := by
      intro x hx y hy hne
      rcases Finset.mem_image.mp hx with ⟨L1, hL1, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨L2, hL2, rfl⟩
      have hL1neL2 : L1 ≠ L2 := by intro h; apply hne; rw [h]
      exact hφ_sep L1 hL1 L2 hL2 hL1neL2
    have h_main : s.card ≤ Nat.floor ((2 * α) / δ) + 1 :=
      real_packing_simple hδ0 (by positivity) hlo_s hhi_s hsep_s
    rw [h_card] at h_main
    have h_bound : (2 * α) / δ ≤ 4 * Real.pi := by
      have h9 : 2 * α ≤ 2 * ((Real.pi / 2) * R) := by gcongr
      have h10 : 2 * ((Real.pi / 2) * R) = Real.pi * R := by ring
      have h11 : 2 * α ≤ Real.pi * R := by linarith
      have h12 : (2 * α) / δ ≤ (Real.pi * R) / δ := by gcongr
      have h13 : (Real.pi * R) / δ = 4 * Real.pi := by
        dsimp only [R, δ]
        field_simp [hr.ne', hξ.ne'] <;> ring
      rw [h13] at h12; exact h12
    have h14 : Nat.floor ((2 * α) / δ) ≤ Nat.floor (4 * Real.pi) := Nat.floor_mono h_bound
    have h15 : Nat.floor (4 * Real.pi) = 12 := by
      have h_pos : 0 ≤ 4 * Real.pi := by positivity
      have h16 : (12 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
      have h18 : 4 * Real.pi < (13 : ℝ) := by
        have h19 : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
        linarith
      have h1 : 12 ≤ Nat.floor (4 * Real.pi) := by
        rw [Nat.le_floor_iff h_pos] <;> exact_mod_cast h16
      have h2 : Nat.floor (4 * Real.pi) < 13 := by
        have h3 : (Nat.floor (4 * Real.pi) : ℝ) ≤ 4 * Real.pi := Nat.floor_le h_pos
        have h4 : (Nat.floor (4 * Real.pi) : ℝ) < 13 := by linarith
        exact_mod_cast h4
      omega
    rw [h15] at h14
    linarith

end RadialBootstrapping
