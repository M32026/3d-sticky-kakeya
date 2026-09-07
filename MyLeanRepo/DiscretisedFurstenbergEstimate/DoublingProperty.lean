module

/-
  Doubling property for EuclideanPlane.

  Provides:
  - `externalCoveringNumber_doubling`: general doubling lemma
  - `ball_361_cover`: ball of radius 9δ covered by 361 balls of radius δ
  - `euclidean_plane_doubling`: Ncover δ F ≤ 361 * Ncover (9δ) F

  A ball of radius 9δ is covered by a 19×19 grid of balls of radius δ:
  coordinate distance ≤ δ/2, so L² distance ≤ δ/√2 < δ.

  Whiteprint node: doubling_property
  Dependencies: CoveringUtils
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CoveringUtils

open DirecretisedFurstenbergEstimate

abbrev Plane := EuclideanSpace ℝ (Fin 2)

section GeneralDoubling

variable {X : Type*} [PseudoMetricSpace X]

/-- General doubling lemma: if every ball of radius R can be covered by C_d
    balls of radius r, then Ncover(r, F) ≤ C_d * Ncover(R, F). -/
lemma externalCoveringNumber_doubling
    {r R : NNReal} {C_d : ℕ} (hC_d_pos : 0 < C_d)
    (h_ball_cover : ∀ (c : X), ∃ (S : Finset X), S.card = C_d ∧
        Metric.closedBall c (R : ℝ) ⊆ ⋃ s ∈ S, Metric.closedBall s (r : ℝ))
    {F : Set X} :
    Metric.externalCoveringNumber r F ≤ (C_d : ENat) * Metric.externalCoveringNumber R F := by
  classical
  by_cases h_top : Metric.externalCoveringNumber R F = ⊤
  · rw [h_top]
    have h : (C_d : ENat) * ⊤ = ⊤ := by
      simp [hC_d_pos.ne']
    rw [h] <;> exact le_top
  · have h_fin : Metric.externalCoveringNumber R F < ⊤ := lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq h_fin with ⟨C, hC, h_eqC⟩
    choose S hS_card hS_cover using fun c => h_ball_cover c
    have hC_finite : C.Finite := by
      have h : C.encard < ⊤ := by rw [h_eqC]; exact h_fin
      exact Set.encard_lt_top_iff.mp h
    let C_fin : Finset X := hC_finite.toFinset
    have hC_fin_coe : (C_fin : Set X) = C := hC_finite.coe_toFinset
    let C'_fin : Finset X := C_fin.biUnion (fun c => S c)
    let C' : Set X := (C'_fin : Set X)
    have hC'_cover : Metric.IsCover r F C' := by
      intro x hx
      rcases hC hx with ⟨c, hc, hed⟩
      have h_dist : dist x c ≤ (R : ℝ) := by
        have h_ed : edist x c ≤ ↑R := hed
        rw [edist_dist] at h_ed
        exact_mod_cast h_ed
      have h_in_ball : x ∈ Metric.closedBall c (R : ℝ) := by
        simpa [Metric.mem_closedBall] using h_dist
      have h9 : x ∈ (⋃ s ∈ (S c : Set X), Metric.closedBall s (r : ℝ)) :=
        hS_cover c h_in_ball
      have h10 : ∃ (s : X), s ∈ (S c : Set X) ∧ x ∈ Metric.closedBall s (r : ℝ) := by
        simpa [Set.mem_iUnion] using h9
      rcases h10 with ⟨s, hs_in_S, hsin⟩
      have h2 : c ∈ C_fin := by
        simpa [C_fin, hC_fin_coe] using hc
      have h_s_in_C' : s ∈ C' := by
        exact Finset.mem_biUnion.mpr ⟨c, h2, hs_in_S⟩
      have h_dist_s : dist x s ≤ (r : ℝ) := by
        simpa [Metric.mem_closedBall] using hsin
      have h_edist : edist x s ≤ ↑r := by
        rw [edist_dist]
        exact_mod_cast h_dist_s
      exact ⟨s, h_s_in_C', h_edist⟩
    have h1 : Metric.externalCoveringNumber r F ≤ C'.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hC'_cover
    have h_card : C'_fin.card ≤ C_fin.card * C_d := by
      calc C'_fin.card
        ≤ ∑ c ∈ C_fin, (S c).card := Finset.card_biUnion_le
        _ = ∑ c ∈ C_fin, C_d := by
          apply Finset.sum_congr rfl
          intro c _
          exact hS_card c
        _ = C_fin.card * C_d := by
          simp [Finset.sum_const] <;> ring
    have h5 : C'.encard = ↑C'_fin.card := by
      have h51 : C' = (C'_fin : Set X) := rfl
      rw [h51]
      simp
    have h6 : C.encard = ↑C_fin.card := by
      have h7 : (C_fin : Set X) = C := hC_fin_coe
      have h8 : C.encard = (C_fin : Set X).encard := by rw [h7]
      rw [h8]
      simp
    have h_encard : C'.encard ≤ (C_d : ENat) * C.encard := by
      rw [h5, h6]
      have h7 : ↑C'_fin.card ≤ (C_d : ENat) * ↑C_fin.card := by
        exact_mod_cast (show C'_fin.card ≤ C_d * C_fin.card from by linarith [h_card])
      exact h7
    have h7 : Metric.externalCoveringNumber r F ≤ (C_d : ENat) * C.encard :=
      le_trans h1 h_encard
    rw [h_eqC] at h7
    exact h7

end GeneralDoubling

section EuclideanPlane

/-- Norm squared formula for EuclideanPlane. -/
private lemma plane_norm_sq (z : Plane) : ‖z‖^2 = (z 0)^2 + (z 1)^2 := by
  have h : ‖z‖ = Real.sqrt ((z 0)^2 + (z 1)^2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
  rw [h]
  have hpos : 0 ≤ (z 0)^2 + (z 1)^2 := by positivity
  rw [Real.sq_sqrt hpos]

/-- Coordinate bound from L2 norm in EuclideanPlane. -/
private lemma coord_le_norm (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  have h1 : (z i)^2 ≤ ‖z‖^2 := by
    rw [plane_norm_sq z]
    fin_cases i <;> simp [Fin.sum_univ_two] <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have h2 : 0 ≤ ‖z‖ := by positivity
  exact abs_le_of_sq_le_sq h1 h2


/-- A closed ball of radius 9δ in EuclideanPlane can be covered by 361 closed
    balls of radius δ (19×19 grid with spacing δ). -/
lemma ball_361_cover (δ : ℝ) (hδ_pos : 0 < δ) (c : Plane) :
    ∃ (S : Finset Plane), S.card = 361 ∧
      Metric.closedBall c (9 * δ) ⊆ ⋃ s ∈ S, Metric.closedBall s δ := by
  let grid : Finset (ℤ × ℤ) := Finset.Icc (-9) 9 ×ˢ Finset.Icc (-9) 9
  have hgrid_card : grid.card = 361 := by
    simp [grid, Finset.card_product] <;> decide
  let center (p : ℤ × ℤ) : Plane :=
    c + WithLp.toLp (2 : ENNReal) (fun i : Fin 2 =>
      if i = 0 then (p.1 : ℝ) * δ else (p.2 : ℝ) * δ)
  let S : Finset Plane := grid.image center
  have h_inj : Function.Injective center := by
    intro p1 p2 h
    have h0 : (p1.1 : ℝ) * δ = (p2.1 : ℝ) * δ := by
      have h_eq := congr_arg (fun (x : Plane) => x 0) h
      simpa [center] using h_eq
    have h1 : (p1.2 : ℝ) * δ = (p2.2 : ℝ) * δ := by
      have h_eq := congr_arg (fun (x : Plane) => x 1) h
      simpa [center] using h_eq
    have hp1 : p1.1 = p2.1 := by
      have h_eq2 : (p1.1 : ℝ) = (p2.1 : ℝ) := by
        apply (mul_right_inj' hδ_pos.ne').mp
        linarith
      exact_mod_cast h_eq2
    have hp2 : p1.2 = p2.2 := by
      have h_eq2 : (p1.2 : ℝ) = (p2.2 : ℝ) := by
        apply (mul_right_inj' hδ_pos.ne').mp
        linarith
      exact_mod_cast h_eq2
    exact Prod.ext hp1 hp2
  have hS_card : S.card = grid.card :=
    Finset.card_image_of_injective _ h_inj
  refine' ⟨S, by rw [hS_card, hgrid_card] <;> norm_num, _⟩
  intro x hx
  set y : Plane := x - c with hy_def
  have hdist : ‖y‖ ≤ 9 * δ := by
    have h : dist x c ≤ 9 * δ := by simpa [Metric.mem_closedBall] using hx
    simpa [dist_eq_norm, hy_def] using h
  have h0_norm : |y 0| ≤ ‖y‖ := coord_le_norm y 0
  have h1_norm : |y 1| ≤ ‖y‖ := coord_le_norm y 1
  have h0 : |y 0| ≤ 9 * δ := by linarith
  have h1 : |y 1| ≤ 9 * δ := by linarith
  let z0 : ℝ := y 0 / δ
  let z1 : ℝ := y 1 / δ
  let i : ℤ := ⌊z0 + 1 / 2⌋
  let j : ℤ := ⌊z1 + 1 / 2⌋
  have h_z0_bounds : -9 ≤ z0 ∧ z0 ≤ 9 := by
    have h_y0_lower : -9 * δ ≤ y 0 := by linarith [abs_le.mp h0]
    have h_y0_upper : y 0 ≤ 9 * δ := by linarith [abs_le.mp h0]
    constructor
    · have h : (-9 * δ) / δ ≤ y 0 / δ := div_le_div_of_nonneg_right h_y0_lower (by linarith)
      have h2 : (-9 * δ) / δ = -9 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    · have h : y 0 / δ ≤ (9 * δ) / δ := by gcongr
      have h2 : (9 * δ) / δ = 9 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h2] at h
      exact h
  have h_z1_bounds : -9 ≤ z1 ∧ z1 ≤ 9 := by
    have h_y1_lower : -9 * δ ≤ y 1 := by linarith [abs_le.mp h1]
    have h_y1_upper : y 1 ≤ 9 * δ := by linarith [abs_le.mp h1]
    constructor
    · have h : (-9 * δ) / δ ≤ y 1 / δ := div_le_div_of_nonneg_right h_y1_lower (by linarith)
      have h2 : (-9 * δ) / δ = -9 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    · have h : y 1 / δ ≤ (9 * δ) / δ := by gcongr
      have h2 : (9 * δ) / δ = 9 := by field_simp [hδ_pos.ne'] <;> ring
      rw [h2] at h
      exact h
  have h_i1 : z0 - 1 / 2 < (i : ℝ) := by
    have h := Int.lt_floor_add_one (z0 + 1 / 2)
    linarith
  have h_i2 : (i : ℝ) ≤ z0 + 1 / 2 := Int.floor_le (z0 + 1 / 2)
  have h_j1 : z1 - 1 / 2 < (j : ℝ) := by
    have h := Int.lt_floor_add_one (z1 + 1 / 2)
    linarith
  have h_j2 : (j : ℝ) ≤ z1 + 1 / 2 := Int.floor_le (z1 + 1 / 2)
  have hi_range : -9 ≤ i ∧ i ≤ 9 := by
    constructor
    · by_contra h; have h' : i ≤ -10 := by linarith
      have h'' : (i : ℝ) ≤ -10 := by exact_mod_cast h'
      linarith
    · by_contra h; have h' : i ≥ 10 := by linarith
      have h'' : (i : ℝ) ≥ 10 := by exact_mod_cast h'
      linarith
  have hj_range : -9 ≤ j ∧ j ≤ 9 := by
    constructor
    · by_contra h; have h' : j ≤ -10 := by linarith
      have h'' : (j : ℝ) ≤ -10 := by exact_mod_cast h'
      linarith
    · by_contra h; have h' : j ≥ 10 := by linarith
      have h'' : (j : ℝ) ≥ 10 := by exact_mod_cast h'
      linarith
  have h_ij_in_grid : (i, j) ∈ grid := by
    simp [grid, Finset.mem_product, Finset.mem_Icc] <;> omega
  let s : Plane := center (i, j)
  have hs_in_S : s ∈ S := by
    apply Finset.mem_image.mpr
    exact ⟨(i, j), h_ij_in_grid, rfl⟩
  have h_s0 : s 0 = c 0 + (i : ℝ) * δ := by
    simp [s, center] <;> ring
  have h_s1 : s 1 = c 1 + (j : ℝ) * δ := by
    simp [s, center] <;> ring
  have hdi : |y 0 - (i : ℝ) * δ| ≤ δ / 2 := by
    have h_eq : y 0 - (i : ℝ) * δ = δ * (z0 - (i : ℝ)) := by
      simp [z0] <;> field_simp [hδ_pos.ne'] <;> ring
    rw [h_eq]
    have h_lower : -1 / 2 ≤ z0 - (i : ℝ) := by linarith
    have h_upper : z0 - (i : ℝ) < 1 / 2 := by linarith
    have h3 : -(δ / 2) ≤ δ * (z0 - (i : ℝ)) := by
      have h4 : δ * (z0 - (i : ℝ)) ≥ δ * (-1 / 2) := mul_le_mul_of_nonneg_left h_lower (by linarith)
      have h5 : δ * (-1 / 2) = -(δ / 2) := by ring
      rw [h5] at h4
      exact h4
    have h6 : δ * (z0 - (i : ℝ)) ≤ δ / 2 := by
      have h7 : δ * (z0 - (i : ℝ)) < δ * (1 / 2) := mul_lt_mul_of_pos_left h_upper hδ_pos
      linarith
    exact abs_le.mpr ⟨h3, h6⟩
  have hdj : |y 1 - (j : ℝ) * δ| ≤ δ / 2 := by
    have h_eq : y 1 - (j : ℝ) * δ = δ * (z1 - (j : ℝ)) := by
      simp [z1] <;> field_simp [hδ_pos.ne'] <;> ring
    rw [h_eq]
    have h_lower : -1 / 2 ≤ z1 - (j : ℝ) := by linarith
    have h_upper : z1 - (j : ℝ) < 1 / 2 := by linarith
    have h3 : -(δ / 2) ≤ δ * (z1 - (j : ℝ)) := by
      have h4 : δ * (z1 - (j : ℝ)) ≥ δ * (-1 / 2) := mul_le_mul_of_nonneg_left h_lower (by linarith)
      have h5 : δ * (-1 / 2) = -(δ / 2) := by ring
      rw [h5] at h4
      exact h4
    have h6 : δ * (z1 - (j : ℝ)) ≤ δ / 2 := by
      have h7 : δ * (z1 - (j : ℝ)) < δ * (1 / 2) := mul_lt_mul_of_pos_left h_upper hδ_pos
      linarith
    exact abs_le.mpr ⟨h3, h6⟩
  have h_xs0 : |x 0 - s 0| ≤ δ / 2 := by
    rw [h_s0]
    have h : x 0 - (c 0 + (i : ℝ) * δ) = y 0 - (i : ℝ) * δ := by
      simp [hy_def] <;> ring
    rw [h]
    exact hdi
  have h_xs1 : |x 1 - s 1| ≤ δ / 2 := by
    rw [h_s1]
    have h : x 1 - (c 1 + (j : ℝ) * δ) = y 1 - (j : ℝ) * δ := by
      simp [hy_def] <;> ring
    rw [h]
    exact hdj
  have h0' : (x 0 - s 0)^2 ≤ (δ / 2)^2 := by
    have h7 : |x 0 - s 0| ≤ δ / 2 := h_xs0
    have h8 : |x 0 - s 0|^2 ≤ (δ / 2)^2 := by gcongr
    have h9 : (x 0 - s 0)^2 = |x 0 - s 0|^2 := by rw [sq_abs]
    rw [h9]; exact h8
  have h1' : (x 1 - s 1)^2 ≤ (δ / 2)^2 := by
    have h7 : |x 1 - s 1| ≤ δ / 2 := h_xs1
    have h8 : |x 1 - s 1|^2 ≤ (δ / 2)^2 := by gcongr
    have h9 : (x 1 - s 1)^2 = |x 1 - s 1|^2 := by rw [sq_abs]
    rw [h9]; exact h8
  have h2 : ‖x - s‖^2 = (x 0 - s 0)^2 + (x 1 - s 1)^2 := plane_norm_sq (x - s)
  have h3 : ‖x - s‖^2 ≤ δ^2 / 2 := by
    rw [h2]
    have h4 : (x 0 - s 0)^2 + (x 1 - s 1)^2 ≤ (δ / 2)^2 + (δ / 2)^2 := by
      exact add_le_add h0' h1'
    have h5 : (δ / 2)^2 + (δ / 2)^2 = δ^2 / 2 := by ring
    linarith
  have h4 : 0 ≤ ‖x - s‖ := by positivity
  have h5 : ‖x - s‖ ≤ δ := by
    have h6 : ‖x - s‖^2 ≤ δ^2 := by
      have h7 : δ^2 / 2 ≤ δ^2 := by
        have h8 : 0 ≤ δ^2 := by positivity
        linarith
      calc ‖x - s‖^2 ≤ δ^2 / 2 := h3
           _ ≤ δ^2 := h7
    have h9 : 0 ≤ δ := by positivity
    by_contra h10
    have h11 : δ < ‖x - s‖ := by linarith
    have h12 : δ^2 < ‖x - s‖^2 := by
      calc δ^2 = δ * δ := by ring
        _ < ‖x - s‖ * ‖x - s‖ := by gcongr
        _ = ‖x - s‖^2 := by ring
    linarith [h6]

  have hdist_s : dist x s ≤ δ := by
    simpa [dist_eq_norm] using h5
  have h_final : x ∈ Metric.closedBall s δ := by
    simpa [Metric.mem_closedBall] using hdist_s
  simpa [Set.mem_iUnion] using ⟨s, hs_in_S, h_final⟩

/-- Doubling property for EuclideanPlane: Ncover δ F ≤ 361 * Ncover (9δ) F.
    Holds for all sets F (unbounded case is trivial since RHS = ⊤). -/
theorem euclidean_plane_doubling (δ : ℝ) (hδ_pos : 0 < δ) (F : Set Plane) :
    (Metric.externalCoveringNumber δ.toNNReal F : ENNReal) ≤
      (361 : ENNReal) * (Metric.externalCoveringNumber (9 * δ).toNNReal F : ENNReal) := by
  let r : NNReal := δ.toNNReal
  let R : NNReal := (9 * δ).toNNReal
  have hr : (r : ℝ) = δ := by
    simp [r, NNReal.coe_mk] <;> linarith
  have hR : (R : ℝ) = 9 * δ := by
    simp [R, NNReal.coe_mk] <;> linarith
  have h_ball_cover : ∀ (c : Plane), ∃ (S : Finset Plane), S.card = 361 ∧
      Metric.closedBall c (R : ℝ) ⊆ ⋃ s ∈ S, Metric.closedBall s (r : ℝ) := by
    intro c
    rw [hR, hr]
    exact ball_361_cover δ hδ_pos c
  have h_enat : Metric.externalCoveringNumber r F ≤
      (361 : ENat) * Metric.externalCoveringNumber R F :=
    externalCoveringNumber_doubling (hC_d_pos := by norm_num) h_ball_cover
  exact_mod_cast h_enat

end EuclideanPlane

end DiscretisedFurstenbergEstimate.CoveringUtils

end
