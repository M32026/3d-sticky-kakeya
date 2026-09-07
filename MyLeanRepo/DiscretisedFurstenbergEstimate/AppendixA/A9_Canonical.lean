module

/-
  A9 canonical implementation: affine shear F(x,y) = (x - σ₀·y - h₀, y),
  producing dyadic A9 output from A8 input.

  Whiteprint node: appendix_a_alternative / affine_normalization
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_PerSquareBuild
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.PhysicalToYSSet

@[expose] public section


open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate

open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils
open TubesAndSlopes

namespace AppendixA

def A9_affine_normalize
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_eq : δ = Δ ^ 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (hΔ_cover : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    (hΔ_packing : Δ ^ (10 * ε) ≤ 1 / 144)
    (hΔ_small : 7 * Δ ≤ 1)
    (hΔ_coarse_absorb : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε))
    (hΔ_fine_absorb : (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) ≤ Real.rpow Δ (-453 * ε))
    (a8 : A8_Output Δ δ s t ε) :
    A9_Output Δ δ s t ε := by
  let T0 := a8.T0_norm
  let σ₀ := tubeSlope T0
  let h₀ := tubeIntercept T0
  -- Shear WITH h₀: F(x,y) = (x - σ₀*y - h₀, y), maps T0 to vertical x'=0
  let F : Plane → Plane := AffineNormalization.normalizeMap σ₀ h₀
  let Finv : Plane → Plane := AffineNormalization.denormalizeMap σ₀ h₀
  have hF_inj : Function.Injective F :=
    AffineNormalization.normalizeMap_injective σ₀ h₀
  have hFinv_F : ∀ p, Finv (F p) = p :=
    AffineNormalization.normalizeMap_left_inverse σ₀ h₀
  have hFinv_inj : Function.Injective Finv :=
    (AffineNormalization.normalizeMap_right_inverse σ₀ h₀).injective
  have hδ_pos : 0 < δ := by rw [hδ_eq] <;> positivity

  let τ : ℝ := min (t - s) 1
  have hτ_pos : 0 < τ := by
    have h1 : 0 < t - s := by linarith
    exact lt_min h1 (by norm_num)
  have hτ_le_one : τ ≤ 1 := min_le_right _ _
  have hτ_le_t_sub_s : τ ≤ t - s := min_le_left _ _

  let Q0 := a8.Q0

  /- Per-square construction (physical coordinates) -/
  let perSquare' (Q : CoarseSquare Δ) (hQ : Q ∈ Q0) :
      A9_SquareData Δ δ s t ε Q :=
    A9_buildSquareData Δ δ s t ε hΔ_pos hΔ_lt_half hδ_eq hs hs1 hst hε_pos
      hΔ_cover hΔ_packing hΔ_small hΔ_coarse_absorb hΔ_fine_absorb a8 Q hQ


  have h_near49 : ∀ Q ∈ Q0,
      |Δ * ((Q.1 : ℝ) + 1 / 2) - σ₀ * Δ * ((Q.2 : ℝ) + 1 / 2) - h₀| ≤ 49 * Δ := by
    intro Q hQ
    let sq8 := a8.perSquare Q hQ
    have hP_nonempty : sq8.P'_Q.Nonempty := by
      have h1 : 0 < (sq8.P'_Q.card : ℝ) := by
        have h2 : 0 < Real.rpow Δ (-t + 44 * ε) := Real.rpow_pos_of_pos hΔ_pos _
        exact lt_of_lt_of_le h2 sq8.hP'_Q_card_lower
      exact Finset.card_pos.mp (by exact_mod_cast h1)
    rcases hP_nonempty with ⟨p, hp⟩
    have hT_nonempty : (sq8.fineTubes p).Nonempty := by
      have h2 : (0 : ℝ) < Real.rpow Δ (-s + 40 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h3 : (0 : ℝ) < (sq8.fineTubes p).card := by
        calc (0 : ℝ)
          < Real.rpow Δ (-s + 40 * ε) := h2
        _ ≤ (sq8.fineTubes p).card := sq8.hfine_card_lower p hp
      exact Finset.card_pos.mp (by exact_mod_cast h3)
    rcases hT_nonempty with ⟨T, hT⟩
    let p_orig := sq8.originalOfNorm p
    have hp_in_PQ : p_orig ∈ sq8.a4.base.P_Q := sq8.h_originalOfNorm p hp
    have hp_in_square : p_orig ∈ squareSet Δ Q := sq8.a4.base.hP_Q_in_square hp_in_PQ
    have hp_near_square : p_orig ∈ Metric.cthickening (2 * Δ) (squareSet Δ Q) :=
      have h2Δ : 0 ≤ 2 * Δ := by positivity
      have hdist : dist p_orig p_orig ≤ 2 * Δ := by
        rw [dist_self] <;> positivity
      Metric.mem_cthickening_of_dist_le p_orig p_orig (2 * Δ) (squareSet Δ Q) hp_in_square hdist
    have hp_on_T : p_orig ∈ Metric.cthickening (2 * δ) (T.1 : Set Plane) := sq8.hfine_inc p hp T hT
    have h_in_parent : InParent Δ hΔ_pos T T0 := by
      have h_eq : sq8.fineTubes p = pointFiber Δ hΔ_pos sq8.a4.base.T_Q (sq8.originalOfNorm p) T0 :=
        sq8.hfine_eq_pointFiber p hp
      rw [h_eq] at hT
      have h_in_filter : T ∈ (sq8.a4.base.T_Q (sq8.originalOfNorm p)).filter (fun T' => InParent Δ hΔ_pos T' T0) := hT
      exact (Finset.mem_filter.mp h_in_filter).2
    have hT_slope_bound : |tubeSlope T| ≤ 1 := (sq8.h_tube_param_bounds p hp T hT).1
    have hT_intercept_bound : |tubeIntercept T| ≤ 3 := (sq8.h_tube_param_bounds p hp T hT).2
    have hT_dirV : (LemmaE.getDirV T) 1 ≠ 0 := sq8.h_dirV_nonzero p hp T hT
    have hp_in_ball : p_orig ∈ Metric.closedBall 0 (Real.sqrt 2) := sq8.a4.base.hP_Q_in_ball hp_in_PQ
    have hnorm : ‖p_orig‖ ≤ Real.sqrt 2 := by simpa [Metric.mem_closedBall] using hp_in_ball
    have hpy_abs : |p_orig 1| ≤ Real.sqrt 2 := by
      have h : |p_orig 1| ≤ ‖p_orig‖ := by exact TubesAndSlopes.coord_abs_le_norm p_orig 1
      linarith
    have hpy1 : p_orig 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := hp_in_square.2
    have hy_Q_bounds : squareY Δ Q ∈ Set.Icc (-2 : ℝ) 2 := by
      have h_yQ : squareY Δ Q = Δ * (Q.2 : ℝ) := by simp [squareY] <;> ring
      rw [h_yQ]
      rcases hpy1 with ⟨hlo, hhi⟩
      have h_upper : Δ * (Q.2 : ℝ) ≤ 2 := by
        have h : Δ * (Q.2 : ℝ) ≤ p_orig 1 := hlo
        have h2 : p_orig 1 ≤ Real.sqrt 2 := (abs_le.mp hpy_abs).2
        have h_sqrt2_lt_2 : Real.sqrt 2 < (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
        linarith [h_sqrt2_lt_2]
      have h_lower : -2 ≤ Δ * (Q.2 : ℝ) := by
        have h3 : p_orig 1 < Δ * ((Q.2 : ℝ) + 1) := hhi
        have h4 : -Real.sqrt 2 ≤ p_orig 1 := (abs_le.mp hpy_abs).1
        have h5 : Δ * (Q.2 : ℝ) > -Real.sqrt 2 - Δ := by linarith
        have h6 : -Real.sqrt 2 - Δ ≥ -2 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        linarith
      exact ⟨h_lower, by linarith⟩
    have hσ0_bound : |σ₀| ≤ 1 := by
      have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
      have h4 : |tubeSlope a8.a7.T0| ≤ 1 := a8.a7.hT0_slope_bound
      have h5 : σ₀ = tubeSlope a8.a7.T0 := by
        simp [σ₀, T0, hT0_eq] <;> rfl
      rw [h5]; exact h4
    have h0_bound : |h₀| ≤ 3 := by
      have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
      have h4 : |tubeIntercept a8.a7.T0| ≤ 3 := a8.a7.hT0_intercept_bound
      have h5 : h₀ = tubeIntercept a8.a7.T0 := by
        simp [h₀, T0, hT0_eq] <;> rfl
      rw [h5]; exact h4
    have hT0_dirV : (LemmaE.getDirV T0) 1 ≠ 0 := by
      have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
      rw [hT0_eq]
      exact a8.a7.hT0_dirV_nonzero
    exact center_near_T0_inParent Δ δ hΔ_pos hδ_eq (by linarith) T0 T σ₀ h₀ rfl rfl
      hσ0_bound h0_bound
      hT0_dirV hT_dirV hT_slope_bound hT_intercept_bound
      Q p_orig hp_near_square hp_on_T h_in_parent hy_Q_bounds

  have h_near : ∀ Q ∈ Q0,
      |Δ * ((Q.1 : ℝ) + 1 / 2) - σ₀ * Δ * ((Q.2 : ℝ) + 1 / 2) - h₀| ≤ 59 * Δ := by
    intro Q hQ
    have h49 := h_near49 Q hQ
    linarith

  have hY_bounded_fiber : ∀ y : ℝ,
      (Q0.attach.filter fun Q' =>
        (perSquare' Q'.val Q'.property).y_Q = y).card ≤ 120 := by
    have h100 := A9_hY_bounded_fiber_with_near Δ δ s t ε hΔ_pos Q0 perSquare' σ₀ h₀ 49 (by norm_num) (by norm_num) h_near49
    intro y
    exact le_trans (h100 y) (by norm_num)

  have hσ0_bound : |σ₀| ≤ 1 := by
    have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
    have h4 : |tubeSlope a8.a7.T0| ≤ 1 := a8.a7.hT0_slope_bound
    have h5 : σ₀ = tubeSlope a8.a7.T0 := by
      simp [σ₀, T0, hT0_eq] <;> rfl
    rw [h5]; exact h4

  have h0_bound : |h₀| ≤ 3 := by
    have hT0_eq : T0 = a8.a7.T0 := a8.hT0_norm_eq
    have h4 : |tubeIntercept a8.a7.T0| ≤ 3 := a8.a7.hT0_intercept_bound
    have h5 : h₀ = tubeIntercept a8.a7.T0 := by
      simp [h₀, T0, hT0_eq] <;> rfl
    rw [h5]; exact h4

  have hY_sset : IsDeltaSSet Δ τ (Real.rpow Δ (-378 * ε))
      (⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
        {(perSquare' Q hQ).y_Q}) := by
    let u : ℝ := t - s
    have hu_pos : 0 < u := by linarith
    let Y_set : Set ℝ := (fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) '' (Q0 : Set (CoarseSquare Δ))
    let Y_old : Set ℝ := ⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0), {(perSquare' Q hQ).y_Q}
    have hY_eq : Y_old = Y_set := by
      ext y
      simp only [Y_old, Y_set, Set.mem_iUnion₂, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · rintro ⟨Q, hQ, rfl⟩
        have h_yq : (perSquare' Q hQ).y_Q = Δ * (Q.2 : ℝ) := by
          have h := (perSquare' Q hQ).hy_Q_eq
          simpa [squareY] using h
        exact ⟨Q, hQ, h_yq⟩
      · rintro ⟨Q, hQ, rfl⟩
        have h_yq : (perSquare' Q hQ).y_Q = Δ * (Q.2 : ℝ) := by
          have h := (perSquare' Q hQ).hy_Q_eq
          simpa [squareY] using h
        exact ⟨Q, hQ, h_yq.symm⟩
    have h_near_phys : ∀ p ∈ a8.a7.Q0_phys, |p 0 - σ₀ * p 1 - h₀| ≤ 59 * Δ := by
      intro p hp
      have hQ0_eq : Q0 = a8.a7.Q0 := a8.hQ0_eq
      have h_phys_eq : a8.a7.Q0_phys = Q0.image (Lagoon.squareCenter Δ) := by
        rw [a8.a7.hQ0_phys_eq, hQ0_eq]
      have hpe : p ∈ (Q0.image (Lagoon.squareCenter Δ) : Set Plane) := by
        rw [h_phys_eq] at hp
        exact hp
      rcases Finset.mem_image.mp hpe with ⟨Q, hQ, rfl⟩
      have h_sc0 : (Lagoon.squareCenter Δ Q) 0 = Δ * ((Q.1 : ℝ) + 1 / 2) := Lagoon.squareCenter_zero Δ Q
      have h_sc1 : (Lagoon.squareCenter Δ Q) 1 = Δ * ((Q.2 : ℝ) + 1 / 2) := Lagoon.squareCenter_one Δ Q
      rw [h_sc0, h_sc1]
      have h := h_near Q hQ
      ring_nf at h ⊢
      exact h
    have h_fiber : ∀ y : ℝ, (Q0.filter fun Q => Δ * (Q.2 : ℝ) = y).card ≤ 120 := by
      intro y
      have h_yq_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
          (perSquare' Q hQ).y_Q = Δ * (Q.2 : ℝ) := by
        intro Q hQ
        have h := (perSquare' Q hQ).hy_Q_eq
        simpa [squareY] using h
      let S : Finset (CoarseSquare Δ) := Q0.filter fun Q => Δ * (Q.2 : ℝ) = y
      let S' : Finset {Q // Q ∈ Q0} := Q0.attach.filter fun Q' =>
          (perSquare' Q'.val Q'.property).y_Q = y
      have h_image : S'.image Subtype.val = S := by
        ext Q
        simp only [S, S', Finset.mem_image, Finset.mem_filter, Finset.mem_attach]
        constructor
        · rintro ⟨Q', hQ1, rfl⟩
          have h_yq : (perSquare' Q'.val Q'.property).y_Q = y := hQ1.2
          have hcond : Δ * (Q'.val.2 : ℝ) = y := by
            have h_eq : (perSquare' Q'.val Q'.property).y_Q = Δ * (Q'.val.2 : ℝ) := h_yq_eq Q'.val Q'.property
            rw [h_eq] at h_yq
            exact h_yq
          exact ⟨Q'.property, hcond⟩
        · rintro ⟨hQ1, hcond⟩
          have h_yq : (perSquare' Q hQ1).y_Q = y := by
            rw [h_yq_eq Q hQ1, hcond]
          exact ⟨⟨Q, hQ1⟩, ⟨by simp, h_yq⟩, rfl⟩
      have h_card : S'.card = S.card := by
        rw [←h_image]
        rw [Finset.card_image_of_injective S' Subtype.val_injective]
      have h_card2 : S.card = S'.card := h_card.symm
      rw [h_card2]
      exact hY_bounded_fiber y
    have hY_bounded : Y_set ⊆ Set.Icc (-2 : ℝ) 2 := by
      intro y hy
      rcases hy with ⟨Q, hQ, rfl⟩
      have h_yq : (fun Q : CoarseSquare Δ => Δ * (Q.2 : ℝ)) Q = (perSquare' Q hQ).y_Q := by
        have h := (perSquare' Q hQ).hy_Q_eq
        simpa [squareY] using h.symm
      rw [h_yq]
      exact (perSquare' Q hQ).hy_Q_bounds
    have h_u_lt_two : u < 2 := by
      dsimp only [u]
      linarith [ht2, hs]
    have h_umnτ_nonneg : 0 ≤ u - τ := by linarith [hτ_le_t_sub_s]
    have h61_u_le : (61 : ℝ)^u ≤ (61 : ℝ)^(2 : ℝ) := by
      gcongr <;> linarith
    have h4_umnτ_le : (4 : ℝ)^(u - τ) ≤ (4 : ℝ)^(2 : ℝ) := by
      gcongr <;> linarith
    have h_num_bound : 3 * (120 : ℝ) * (61 : ℝ)^u * (4 : ℝ)^(u - τ) ≤ (2 * 10^13 : ℝ) := by
      calc
        3 * (120 : ℝ) * (61 : ℝ)^u * (4 : ℝ)^(u - τ)
          ≤ 3 * (120 : ℝ) * (61 : ℝ)^(2 : ℝ) * (4 : ℝ)^(2 : ℝ) := by gcongr <;> linarith
        _ = (21432960 : ℝ) := by norm_num
        _ ≤ (2 * 10^13 : ℝ) := by norm_num
    let C_Y : ℝ := Real.rpow Δ (-378 * ε)
    have hC_Y_pos : 0 < C_Y := Real.rpow_pos_of_pos hΔ_pos _
    have hC_Y_ge_one : 1 ≤ C_Y := by
      dsimp only [C_Y]
      have h1 : Real.rpow Δ (378 * ε) < 1 := Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
      have h2 : Real.rpow Δ (-378 * ε) = (Real.rpow Δ (378 * ε))⁻¹ := by
        have h3 : (-378 * ε) = -(378 * ε) := by ring
        rw [h3]
        exact Real.rpow_neg hΔ_pos.le (y := 378 * ε)
      rw [h2]
      have h4 : 0 < Real.rpow Δ (378 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact one_le_inv₀ h4 |>.mpr (by linarith)
    have h_absorb : 3 * (120 : ℝ) * (Real.rpow Δ (-377 * ε)) * (61 : ℝ)^u * (2 * (2 : ℝ))^(u - τ) ≤ C_Y := by
      dsimp only [C_Y]
      have h4_eq : (2 * (2 : ℝ)) = (4 : ℝ) := by norm_num
      rw [h4_eq]
      have h_rpow_add : Real.rpow Δ (-ε) * Real.rpow Δ (-377 * ε) = Real.rpow Δ (-378 * ε) := by
        have h := Real.rpow_add hΔ_pos (-ε) (-377 * ε)
        have h_sum : (-ε) + (-377 * ε) = -378 * ε := by ring
        rw [h_sum] at h
        exact h.symm
      have h : 3 * (120 : ℝ) * (61 : ℝ)^u * (4 : ℝ)^(u - τ) ≤ Real.rpow Δ (-ε) := by
        calc
          3 * (120 : ℝ) * (61 : ℝ)^u * (4 : ℝ)^(u - τ)
            ≤ (2 * 10^13 : ℝ) := h_num_bound
          _ ≤ Real.rpow Δ (-ε) := hΔ_coarse_absorb
      have h_pos : 0 < Real.rpow Δ (-377 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h' : 3 * (120 : ℝ) * (Real.rpow Δ (-377 * ε)) * (61 : ℝ)^u * (4 : ℝ)^(u - τ) ≤
          Real.rpow Δ (-ε) * Real.rpow Δ (-377 * ε) := by
        calc
          3 * (120 : ℝ) * (Real.rpow Δ (-377 * ε)) * (61 : ℝ)^u * (4 : ℝ)^(u - τ)
            = (3 * (120 : ℝ) * (61 : ℝ)^u * (4 : ℝ)^(u - τ)) * Real.rpow Δ (-377 * ε) := by ring
          _ ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-377 * ε) := by
            gcongr
      exact le_trans h' h_rpow_add.le
    have hQ0_eq : Q0 = a8.a7.Q0 := a8.hQ0_eq
    have h_phys_eq' : a8.a7.Q0_phys = Finset.image (Lagoon.squareCenter Δ) Q0 := by
      rw [a8.a7.hQ0_phys_eq, hQ0_eq]
    have h_main : IsDeltaSSet Δ τ C_Y Y_set := by
      exact physical_sset_to_y_sset
        hΔ_pos (by linarith) hu_pos hτ_pos hτ_le_t_sub_s hτ_le_one
        Q0 a8.a7.Q0_phys h_phys_eq' a8.a7.hQ0_phys_sset
        σ₀ h₀ hσ0_bound (59 * Δ) (by positivity) (by linarith)
        h_near_phys 120 (by norm_num) h_fiber
        2 (by norm_num) (by norm_num) hY_bounded
        hC_Y_pos hC_Y_ge_one h_absorb
    have h_goal_set : (⋃ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
        {(perSquare' Q hQ).y_Q}) = Y_set := hY_eq
    rw [h_goal_set]
    exact h_main

  let U : Set FineTube := ↑(Q0.attach.biUnion (fun Q' =>
    let hQ := Q'.property
    let sq := perSquare' Q'.val hQ
    sq.P_norm_Q.biUnion (fun p =>
      sq.fineTubes_norm p |>.image (sq.fineTubeOfCell p))))

  have hU_param_bounds : ∀ T ∈ U, |tubeSlope T| ≤ 7 * Δ ∧ |tubeIntercept T| ≤ 7 * Δ := by
    intro T hT
    have hT_finset : T ∈ (Q0.attach.biUnion (fun Q' =>
        let hQ := Q'.property
        let sq := perSquare' Q'.val hQ
        sq.P_norm_Q.biUnion (fun p =>
          sq.fineTubes_norm p |>.image (sq.fineTubeOfCell p)))) := by
      simpa [U, Finset.mem_coe] using hT
    rcases Finset.mem_biUnion.mp hT_finset with ⟨Q_sub, hQ_sub, hT_in_biUnion⟩
    let Q' := Q_sub.val
    let hQ' := Q_sub.property
    let sq := perSquare' Q' hQ'
    rcases Finset.mem_biUnion.mp hT_in_biUnion with ⟨p, hp, hT_in_image⟩
    rcases Finset.mem_image.mp hT_in_image with ⟨cell, hcell, rfl⟩
    have h_bounds := sq.hfine_cell_bounds p hp cell hcell
    have h_fineTube_def : sq.fineTubeOfCell p cell =
        makeAffineLine (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2 := by rfl
    have h_params : affineLineParams (sq.fineTubeOfCell p cell) = paramsOfDyadicCell δ cell := by
      rw [h_fineTube_def, makeAffineLine_params] <;> rfl
    have h_slope_eq : tubeSlope (sq.fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).1 := by
      simpa [tubeSlope] using congr_arg Prod.fst h_params
    have h_intercept_eq : tubeIntercept (sq.fineTubeOfCell p cell) = (paramsOfDyadicCell δ cell).2 := by
      simpa [tubeIntercept] using congr_arg Prod.snd h_params
    rw [h_slope_eq, h_intercept_eq]
    exact h_bounds

  have hU_v1 : ∀ T ∈ U, (LemmaE.getDirV T) 1 ≠ 0 := by
    intro T hT
    have hT_finset : T ∈ (Q0.attach.biUnion (fun Q' =>
        let hQ := Q'.property
        let sq := perSquare' Q'.val hQ
        sq.P_norm_Q.biUnion (fun p =>
          sq.fineTubes_norm p |>.image (sq.fineTubeOfCell p)))) := by
      simpa [U, Finset.mem_coe] using hT
    rcases Finset.mem_biUnion.mp hT_finset with ⟨Q_sub, hQ_sub, hT_in_biUnion⟩
    let Q' := Q_sub.val
    let hQ' := Q_sub.property
    let sq := perSquare' Q' hQ'
    rcases Finset.mem_biUnion.mp hT_in_biUnion with ⟨p, hp, hT_in_image⟩
    rcases Finset.mem_image.mp hT_in_image with ⟨cell, hcell, rfl⟩
    have h_fineTube_def : sq.fineTubeOfCell p cell =
        makeAffineLine (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2 := by rfl
    rw [h_fineTube_def]
    exact makeAffineLine_v1 (paramsOfDyadicCell δ cell).1 (paramsOfDyadicCell δ cell).2

  have h_total_fine_upper : Metric.externalCoveringNumber Δ.toNNReal U <
      ENNReal.ofReal (Real.rpow Δ (-2 * s - ε)) :=
    A9_total_fine_upper Δ s ε hΔ_pos hΔ_lt_half hΔ_cover U hU_param_bounds hU_v1

  have h_metric_transfer : ∀ (T1 T2 : FineTube),
      ((LemmaE.getDirV T1) 1 ≠ 0 ∧ |tubeSlope T1| ≤ 1 ∧ |tubeIntercept T1| ≤ 3) →
      ((LemmaE.getDirV T2) 1 ≠ 0 ∧ |tubeSlope T2| ≤ 1 ∧ |tubeIntercept T2| ≤ 3) →
      dist (tubeSlope T1, tubeIntercept T1) (tubeSlope T2, tubeIntercept T2) ≤
        8 * dist T1 T2 := by
    intro T1 T2 h1 h2
    exact A9Support.bounded_metric_transfer T1 T2 h1.1 h2.1 h1.2.1 h2.2.1 h1.2.2 h2.2.2

  have h_total_fine_cells := A9_total_fine_cells_bound Δ δ s t ε Q0 perSquare'

  -- Improved cardinal bound via distinct globalFiber(T0)
  set a7 : A7_Output Δ δ s t ε := a8.a7 with ha7
  set a5 : A5_Output Δ δ s t ε := a7.a5 with ha5
  set T0_a5 : CoarseTube := a7.T0 with hT0_a5_def
  have hT0_eq : T0 = T0_a5 := a8.hT0_norm_eq

  have hQ0_sub : Q0 ⊆ a5.Qset := by
    intro Q hQ
    have hQ' : Q ∈ a7.Q0 := by
      have h_eq : Q0 = a7.Q0 := a8.hQ0_eq
      rw [h_eq] at hQ
      exact hQ
    exact a7.hQ0_sub hQ'

  have hT0_in_Cglobal : T0_a5 ∈ a5.C_global := a7.hT0_in_Cglobal

  -- Cell map: fine tube → its δ-cell in sheared parameter space
  let g : FineTube → DyadicTubeCell δ := fun T =>
    dyadicCellOfParams δ hδ_pos (tubeSlope T - σ₀, tubeIntercept T - h₀)

  -- Every fine tube in any pointFiber(p, T0) is in globalFiber(T0)
  have h_fiber_sub_global : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0) (p : Plane) (hp : p ∈ (perSquare' Q hQ).P_norm_Q) (T : FineTube),
      T ∈ (perSquare' Q hQ).T_Q ((perSquare' Q hQ).unnormalize p) →
      InParent Δ hΔ_pos T T0 →
      T ∈ globalFiber Δ hΔ_pos a5.T_global T0_a5 := by
    intro Q hQ p hp T hT_in_TQ h_in_parent
    have hQ_in_set : Q ∈ a5.Qset := hQ0_sub hQ
    have hQ' : Q ∈ a7.Q0 := by
      have h_eq : Q0 = a7.Q0 := a8.hQ0_eq
      exact h_eq ▸ hQ
    have h_a4_eq : (perSquare' Q hQ).a4 = a5.perSquare Q hQ_in_set :=
      a8.h_perSquare_a4 Q hQ'
    have h_unnorm_in_PQ : (perSquare' Q hQ).unnormalize p ∈ (a5.perSquare Q hQ_in_set).base.P_Q := by
      have h1 : (perSquare' Q hQ).unnormalize p ∈ (perSquare' Q hQ).a4.base.P_Q :=
        (perSquare' Q hQ).hunnormalize_in_a4PQ p hp
      rw [h_a4_eq] at h1
      exact h1
    have hT_Q_eq : (perSquare' Q hQ).T_Q = (a5.perSquare Q hQ_in_set).base.T_Q := by
      have h1 : (perSquare' Q hQ).T_Q = (perSquare' Q hQ).a4.base.T_Q := (perSquare' Q hQ).hT_Q_eq
      rw [h1, h_a4_eq]
    rw [hT_Q_eq] at hT_in_TQ
    have hT_in_fullFamily : T ∈ a5FullFineFamily Δ δ s t ε a5.Qset a5.perSquare := by
      let Q' : {x // x ∈ a5.Qset} := ⟨Q, hQ_in_set⟩
      have hQ'_mem : Q' ∈ a5.Qset.attach := by simp [Q']
      have h_inner : T ∈ (a5.perSquare Q'.val Q'.property).base.P_Q.biUnion
          (fun p => (a5.perSquare Q'.val Q'.property).base.T_Q p) :=
        Finset.mem_biUnion.mpr ⟨(perSquare' Q hQ).unnormalize p, h_unnorm_in_PQ, hT_in_TQ⟩
      exact Finset.mem_biUnion.mpr ⟨Q', hQ'_mem, h_inner⟩
    have hT_in_Tfull : T ∈ a5.T_full := a5.h_local_sub_T_full hT_in_fullFamily
    have h_parent_in_img : parentCell Δ hΔ_pos T ∈ a5.C_global.image (parentCell Δ hΔ_pos) := by
      have h1 : parentCell Δ hΔ_pos T = parentCell Δ hΔ_pos T0 := h_in_parent
      rw [h1, hT0_eq]
      exact Finset.mem_image.mpr ⟨T0_a5, hT0_in_Cglobal, rfl⟩
    have hT_in_Tglobal : T ∈ a5.T_global := by
      rw [a5.hT_selected_eq]
      exact Finset.mem_filter.mpr ⟨hT_in_Tfull, h_parent_in_img⟩
    have h_in_parent_a5 : InParent Δ hΔ_pos T T0_a5 := by
      rw [hT0_eq] at h_in_parent
      exact h_in_parent
    exact Finset.mem_filter.mpr ⟨hT_in_Tglobal, h_in_parent_a5⟩

  -- allCells ⊆ g '' globalFiber(T0)
  have h_allCells_sub_image :
      (Q0.attach.biUnion (fun Q' =>
        (perSquare' Q'.val Q'.property).P_norm_Q.biUnion (fun p =>
          (perSquare' Q'.val Q'.property).fineTubes_norm p))) ⊆
      (globalFiber Δ hΔ_pos a5.T_global T0_a5).image g := by
    intro cell hcell
    rcases Finset.mem_biUnion.mp hcell with ⟨Q', hQ', cell_in_inner⟩
    let sq := perSquare' Q'.val Q'.property
    rcases Finset.mem_biUnion.mp cell_in_inner with ⟨p, hp, cell_in_fine⟩
    rcases sq.hfine_cell_origin p hp cell cell_in_fine with ⟨T, hT_in_TQ, h_in_parent, rfl⟩
    have hsq_T0 : sq.T0 = T0 := by
      dsimp only [sq, perSquare']
      exact a8.hT0_norm_eq.symm
    have h_in_parent' : InParent Δ hΔ_pos T T0 := by
      rw [hsq_T0] at h_in_parent
      exact h_in_parent
    have hT_in_global : T ∈ globalFiber Δ hΔ_pos a5.T_global T0_a5 :=
      h_fiber_sub_global Q'.val Q'.property p hp T hT_in_TQ h_in_parent'
    exact Finset.mem_image.mpr ⟨T, hT_in_global, rfl⟩

  have h5 : a5.N ≤ Real.rpow Δ (-2 * s - 214 * ε) := a5.hN_upper

  have h_allCells_card_upper :
      (Q0.attach.biUnion (fun Q' =>
        (perSquare' Q'.val Q'.property).P_norm_Q.biUnion (fun p =>
          (perSquare' Q'.val Q'.property).fineTubes_norm p))).card ≤
      2 * Real.rpow Δ (-(2 * s + 214 * ε)) := by
    have h1 : (Q0.attach.biUnion (fun Q' =>
        (perSquare' Q'.val Q'.property).P_norm_Q.biUnion (fun p =>
          (perSquare' Q'.val Q'.property).fineTubes_norm p))).card ≤
        ((globalFiber Δ hΔ_pos a5.T_global T0_a5).image g).card :=
      Finset.card_le_card h_allCells_sub_image
    have h2 : ((globalFiber Δ hΔ_pos a5.T_global T0_a5).image g).card ≤
        (globalFiber Δ hΔ_pos a5.T_global T0_a5).card :=
      Finset.card_image_le
    have h3 : ((globalFiber Δ hΔ_pos a5.T_global T0_a5).card : ℝ) ≤ a5.N :=
      a5.hG4_upper T0_a5 hT0_in_Cglobal
    have h_exp : Real.rpow Δ (-2 * s - 214 * ε) = Real.rpow Δ (-(2 * s + 214 * ε)) := by
      congr 1 <;> ring
    have h5' : a5.N ≤ Real.rpow Δ (-(2 * s + 214 * ε)) := by
      rw [←h_exp]; exact h5
    calc ((Q0.attach.biUnion (fun Q' =>
        (perSquare' Q'.val Q'.property).P_norm_Q.biUnion (fun p =>
          (perSquare' Q'.val Q'.property).fineTubes_norm p))).card : ℝ)
      ≤ ((globalFiber Δ hΔ_pos a5.T_global T0_a5).image g).card := by exact_mod_cast h1
    _ ≤ (globalFiber Δ hΔ_pos a5.T_global T0_a5).card := by exact_mod_cast h2
    _ ≤ a5.N := h3
    _ ≤ Real.rpow Δ (-(2 * s + 214 * ε)) := h5'
    _ ≤ 2 * Real.rpow Δ (-(2 * s + 214 * ε)) := by
      have h_pos : 0 < Real.rpow Δ (-(2 * s + 214 * ε)) := Real.rpow_pos_of_pos hΔ_pos _
      linarith

  exact
    { a8 := a8
      Q0 := Q0
      perSquare := perSquare'
      σ₀ := σ₀
      h₀ := h₀
      hσ₀_eq := by rfl
      h₀_eq := by rfl
      shear := F
      hshear_eq := by
        intro p
        simp [F, AffineNormalization.normalizeMap] <;> ring_nf <;> constructor <;> rfl
      τ := τ
      hτ_pos := hτ_pos
      hτ_le_one := hτ_le_one
      hτ_le_t_sub_s := hτ_le_t_sub_s
      hQ0_sset := by
        have h_eq : Q0 = a8.a7.Q0 := a8.hQ0_eq
        rw [h_eq]
        exact a8.a7.hQ0_sset
      hY_bounded_fiber := hY_bounded_fiber
      hY_sset := hY_sset
      h_near := h_near
      h_total_fine_upper := h_total_fine_upper
      h_metric_transfer := h_metric_transfer
      h_total_fine_cells := h_total_fine_cells
      h_allCells_card_upper := h_allCells_card_upper }
