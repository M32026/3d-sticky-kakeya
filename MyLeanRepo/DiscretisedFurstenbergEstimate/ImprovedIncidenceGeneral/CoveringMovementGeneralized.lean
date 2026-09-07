module

/-
  Generalized covering movement bound.

  Generalizes `covering_movement_global` to accept an arbitrary slope bound B
  instead of hardcoding |slope| ≤ 1.

  For B=1, the constant reduces to the original:
    L(1) = 4+1+3 = 8
    D_grid(1) = 4*8*(C_move+1) = 32*(C_move+1)
    K_pack(1) = (2*ceil(32*(C_move+1))+1)^2

  For B=3/2 (snapped tubes):
    L(3/2) = 4 + 3/2 + 3*(9/4) = 49/4
    D_grid = 4*(49/4)*(C_move+1) = 49*(C_move+1)

  Dependencies: CoveringMovement (for grid_packing_bound),
                SnapTransfer (for slope_lipschitz_general),
                CoordinatePartition (for swapLine)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringMovement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnapTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate
open DyadicCardToNcover (toAffineLine)
open CoordinatePartition (swapLine swapLine_isometry swapLine_params_eq
  swapCoords swapLine_set_eq)
open AffineLineLipschitzTransfer

/-- Generalized forward Lipschitz: dist(params) ≤ (4+B+3*B^2) * dist(line).

    Requires |a_i| ≤ B and |b_i| ≤ 3.
    For B=1, constant = 8, matching affineLineParams_lipschitz_upper. -/
lemma affineLineParams_lipschitz_upper_generalized
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (LemmaE.getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (LemmaE.getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |(LemmaE.affineLineParams ℓ₁).1| ≤ B)
    (ha2 : |(LemmaE.affineLineParams ℓ₂).1| ≤ B)
    (hb1 : |(LemmaE.affineLineParams ℓ₁).2| ≤ 3)
    (hb2 : |(LemmaE.affineLineParams ℓ₂).2| ≤ 3) :
    dist (LemmaE.affineLineParams ℓ₁) (LemmaE.affineLineParams ℓ₂) ≤
      (4 + B + 3 * B^2) * dist ℓ₁ ℓ₂ := by
  set a1 := (LemmaE.affineLineParams ℓ₁).1 with ha1_def
  set a2 := (LemmaE.affineLineParams ℓ₂).1 with ha2_def
  set b1 := (LemmaE.affineLineParams ℓ₁).2 with hb1_def
  set b2 := (LemmaE.affineLineParams ℓ₂).2 with hb2_def
  set d := dist ℓ₁ ℓ₂ with hd_def
  set o := ‖ℓ₁.offset - ℓ₂.offset‖ with ho_def
  set p := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ with hp_def
  have h_p_nonneg : 0 ≤ p := norm_nonneg _
  have h_o_le_d : o ≤ d := by
    have h : d = p + o := by simp [AffineLine.dist, ho_def, hp_def] <;> rfl
    linarith [h_p_nonneg]
  have h_d_nonneg : 0 ≤ d := dist_nonneg

  have h_a : |a1 - a2| ≤ (1 + B^2) * d :=
    SnapTransfer.slope_lipschitz_general hB_nonneg ℓ₁ ℓ₂ hv1 hv2 ha1 ha2

  have hb1_eq : b1 = ℓ₁.offset 0 - a1 * ℓ₁.offset 1 := by
    simp [LemmaE.affineLineParams, ha1_def, hb1_def, hv1] <;> aesop
  have hb2_eq : b2 = ℓ₂.offset 0 - a2 * ℓ₂.offset 1 := by
    simp [LemmaE.affineLineParams, ha2_def, hb2_def, hv2] <;> aesop

  have h_off2_1 : |ℓ₂.offset 1| ≤ 3 := by
    have h : |ℓ₂.offset 1| ≤ ‖ℓ₂.offset‖ := TubesAndSlopes.coord_abs_le_norm ℓ₂.offset 1
    have h2 : ‖ℓ₂.offset‖ ≤ |b2| := offset_norm_le_abs_b ℓ₂ hv2
    exact le_trans h (le_trans h2 hb2)

  have h_off0_diff : |ℓ₁.offset 0 - ℓ₂.offset 0| ≤ o :=
    TubesAndSlopes.coord_abs_le_norm (ℓ₁.offset - ℓ₂.offset) 0
  have h_off1_diff : |ℓ₁.offset 1 - ℓ₂.offset 1| ≤ o :=
    TubesAndSlopes.coord_abs_le_norm (ℓ₁.offset - ℓ₂.offset) 1

  have h_b : |b1 - b2| ≤ (4 + B + 3 * B^2) * d := by
    rw [hb1_eq, hb2_eq]
    set x := ℓ₁.offset 0 - ℓ₂.offset 0 with hx_def
    set y := a1 * (ℓ₁.offset 1 - ℓ₂.offset 1) + (a1 - a2) * ℓ₂.offset 1 with hy_def
    have h_alg : (ℓ₁.offset 0 - a1 * ℓ₁.offset 1) - (ℓ₂.offset 0 - a2 * ℓ₂.offset 1) = x - y := by
      simp [hx_def, hy_def] <;> ring
    rw [h_alg]
    have h_abs1 : |x - y| ≤ |x| + |y| := by exact real_abs_sub x y
    have h_abs2 : |y| ≤ |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := by
      have h : |y| ≤ |a1 * (ℓ₁.offset 1 - ℓ₂.offset 1)| + |(a1 - a2) * ℓ₂.offset 1| := by exact real_abs_add (a1 * (ℓ₁.offset.ofLp 1 - ℓ₂.offset.ofLp 1)) ((a1 - a2) * ℓ₂.offset.ofLp 1)
      have h2 : |a1 * (ℓ₁.offset 1 - ℓ₂.offset 1)| = |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| := by rw [abs_mul]
      have h3 : |(a1 - a2) * ℓ₂.offset 1| = |a1 - a2| * |ℓ₂.offset 1| := by rw [abs_mul]
      linarith
    have h_tri : |x - y| ≤ |x| + |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := by
      linarith [h_abs1, h_abs2]
    have h_main : |x - y| ≤ (1 + B) * o + 3 * (1 + B^2) * d := by
      calc |x - y|
        ≤ |x| + |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := h_tri
      _ ≤ o + B * o + ((1 + B^2) * d) * 3 := by
          gcongr <;> linarith [ha1, h_off0_diff, h_off1_diff, h_a, h_off2_1]
      _ = (1 + B) * o + 3 * (1 + B^2) * d := by ring
    have h_final : (1 + B) * o + 3 * (1 + B^2) * d ≤ (4 + B + 3 * B^2) * d := by
      have h4 : (1 + B) * o ≤ (1 + B) * d := by gcongr
      linarith
    linarith

  have h_goal_a : |a1 - a2| ≤ (4 + B + 3 * B^2) * d := by
    have h : |a1 - a2| ≤ (1 + B^2) * d := h_a
    have h2 : (1 + B^2) * d ≤ (4 + B + 3 * B^2) * d := by
      gcongr <;> nlinarith
    linarith

  have h_main : dist (a1, b1) (a2, b2) ≤ (4 + B + 3 * B^2) * d := by
    simp only [Prod.dist_eq, max_le_iff]
    exact ⟨h_goal_a, h_b⟩
  exact h_main

/-- Generalized global covering movement bound.

    Accepts an arbitrary slope bound B (instead of hardcoding 1).
    D_grid = 4 * (4+B+3*B^2) * (C_move+1)
    K_pack = (2 * ceil(D_grid) + 1)^2
-/
lemma covering_movement_global_generalized
    {n : ℕ} {δ : ℝ} {C_move B : ℝ}
    (hδ_pos : 0 < δ)
    (hC_move_nonneg : 0 ≤ C_move)
    (hB_nonneg : 0 ≤ B)
    (h_scale : δ < 2 * dyadicDelta n)
    (T_oriented : Set AffineLine)
    (T₀ : Finset (DyadicTube n))
    (hm : ∀ T ∈ T₀, |T.slope| ≤ B)
    (hb : ∀ T ∈ T₀, |T.intercept| ≤ 3)
    (h_prov : ∀ U ∈ T₀, ∃ ℓ ∈ T_oriented,
        dist (toAffineLine U) ℓ ≤ C_move * δ) :
    (T₀.card : ENNReal) ≤
      (2 * Nat.ceil (4 * (4 + B + 3 * B^2) * (C_move + 1)) + 1)^2 *
        Metric.externalCoveringNumber δ.toNNReal T_oriented := by
  classical
  set δ_n := dyadicDelta n with hδ_n_def
  have hδ_n_pos : 0 < δ_n := dyadicDelta_pos n
  set R : ℝ := (C_move + 1) * δ with hR_def
  set L : ℝ := 4 + B + 3 * B^2 with hL_def
  set D_grid : ℝ := 4 * L * (C_move + 1) with hD_grid_def
  set K1 : ℕ := Nat.ceil D_grid with hK1_def
  set K_pack : ℕ := (2 * K1 + 1)^2 with hK_pack_def

  let swapped (U : DyadicTube n) := swapLine (toAffineLine U)

  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal T_oriented = ⊤
  · rw [h_top] <;> simp

  · have h_lt_top : Metric.externalCoveringNumber δ.toNNReal T_oriented < ⊤ := by exact Ne.lt_top' fun a => h_top (id (Eq.symm a))
    let ι := {C : Set AffineLine // Metric.IsCover δ.toNNReal T_oriented C}
    have hι_nonempty : Nonempty ι := by
      refine ⟨⟨T_oriented, ?_⟩⟩
      intro x hx
      exact ⟨x, hx, by simp [Metric.IsCover, edist_dist]⟩
    let f : ι → ℕ∞ := fun C => C.val.encard
    have h_exists : ∃ (C : ι), f C = ⨅ (x : ι), f x := ENat.exists_eq_iInf f
    rcases h_exists with ⟨C_min, hC_min_eq⟩
    have h_ext_def : Metric.externalCoveringNumber δ.toNNReal T_oriented = ⨅ (C : ι), f C := by
      have h : Metric.externalCoveringNumber δ.toNNReal T_oriented =
          ⨅ (C : Set AffineLine) (_ : Metric.IsCover δ.toNNReal T_oriented C), C.encard := by rfl
      rw [h]
      have h2 : (⨅ (C : Set AffineLine) (_ : Metric.IsCover δ.toNNReal T_oriented C), C.encard) =
          ⨅ (C : ι), f C := by rw [iInf_subtype] <;> rfl
      rw [h2]
    have h_encard_eq : (C_min.val).encard = Metric.externalCoveringNumber δ.toNNReal T_oriented := by
      have h10 : f C_min = Metric.externalCoveringNumber δ.toNNReal T_oriented := by
        rw [hC_min_eq, h_ext_def]
      simpa [f] using h10
    have h_fin : (C_min.val).Finite := by
      have h : (C_min.val).encard < ⊤ := by
        rw [h_encard_eq] <;> exact h_lt_top
      exact Set.encard_lt_top_iff.mp h
    let C_finset : Finset AffineLine := h_fin.toFinset
    have hC_coe : (C_finset : Set AffineLine) = C_min.val := by exact Set.Finite.coe_toFinset h_fin
    have h_cover : ∀ ℓ ∈ T_oriented, ∃ c ∈ C_finset, dist ℓ c ≤ δ := by
      intro ℓ hℓ
      have h := C_min.property hℓ
      rcases h with ⟨c, hc, hedist⟩
      have hdist : dist ℓ c ≤ δ := by
        have h_edist : edist ℓ c ≤ ↑δ.toNNReal := hedist
        have h_eq : edist ℓ c = ENNReal.ofReal (dist ℓ c) := by rw [edist_dist]
        rw [h_eq] at h_edist
        exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h_edist
      have hcin : c ∈ C_finset := by
        have h : c ∈ (C_finset : Set AffineLine) := by rw [hC_coe] <;> exact hc
        exact h
      exact ⟨c, hcin, hdist⟩

    have h_choose : ∀ (U : DyadicTube n), U ∈ T₀ →
        ∃ (c : AffineLine), c ∈ C_finset ∧ dist (toAffineLine U) c ≤ R := by
      intro U hU
      rcases h_prov U hU with ⟨ℓ, hℓ, hdist1⟩
      rcases h_cover ℓ hℓ with ⟨c, hc, hdist2⟩
      refine ⟨c, hc, ?_⟩
      have h_tri : dist (toAffineLine U) c ≤ dist (toAffineLine U) ℓ + dist ℓ c := dist_triangle _ _ _
      have h_sum : dist (toAffineLine U) ℓ + dist ℓ c ≤ C_move * δ + δ := by
        exact add_le_add hdist1 hdist2
      have h_eq : C_move * δ + δ = (C_move + 1) * δ := by ring
      rw [h_eq] at h_sum
      exact le_trans h_tri h_sum

    have h_affine_nonempty : Nonempty AffineLine :=
      ⟨toAffineLine (DyadicTube.mk (n := n) 0 0)⟩
    let chooseCenter : DyadicTube n → AffineLine := fun U =>
      if hU : U ∈ T₀ then (h_choose U hU).choose else Classical.choice h_affine_nonempty
    have hc1 : ∀ U ∈ T₀, chooseCenter U ∈ C_finset := by
      intro U hU
      have h9 : chooseCenter U = (h_choose U hU).choose := by
        simp [chooseCenter, hU]
      rw [h9]
      exact (h_choose U hU).choose_spec.1
    have hc2 : ∀ U ∈ T₀, dist (toAffineLine U) (chooseCenter U) ≤ R := by
      intro U hU
      have h9 : chooseCenter U = (h_choose U hU).choose := by
        simp [chooseCenter, hU]
      rw [h9]
      exact (h_choose U hU).choose_spec.2

    have h_fiber_bound : ∀ (center : AffineLine), center ∈ C_finset →
        (T₀.filter fun U => chooseCenter U = center).card ≤ K_pack := by
      intro center hc
      let F := T₀.filter fun U => chooseCenter U = center
      have hF_sub : F ⊆ T₀ := Finset.filter_subset _ _
      have h_dist_bound : ∀ U ∈ F, dist (toAffineLine U) center ≤ R := by
        intro U hU
        have hU' : U ∈ T₀ := hF_sub hU
        have h_eq : chooseCenter U = center := (Finset.mem_filter.mp hU).2
        have h : dist (toAffineLine U) (chooseCenter U) ≤ R := hc2 U hU'
        rw [h_eq] at h
        exact h
      have h_int_bound : ∀ (U1 : DyadicTube n), U1 ∈ F →
          ∀ (U2 : DyadicTube n), U2 ∈ F →
          |(U1.a : ℝ) - U2.a| ≤ D_grid ∧ |(U1.b : ℝ) - U2.b| ≤ D_grid := by
        intro U1 hU1 U2 hU2
        have hU1' : U1 ∈ T₀ := hF_sub hU1
        have hU2' : U2 ∈ T₀ := hF_sub hU2
        have h_d1 : dist (toAffineLine U1) center ≤ R := h_dist_bound U1 hU1
        have h_d2 : dist (toAffineLine U2) center ≤ R := h_dist_bound U2 hU2
        have h_dist12 : dist (toAffineLine U1) (toAffineLine U2) ≤ 2 * R := by
          have h_tri : dist (toAffineLine U1) (toAffineLine U2) ≤
              dist (toAffineLine U1) center + dist center (toAffineLine U2) := dist_triangle _ _ _
          have h_comm : dist center (toAffineLine U2) = dist (toAffineLine U2) center := dist_comm _ _
          rw [h_comm] at h_tri
          linarith
        have h_iso : dist (swapped U1) (swapped U2) = dist (toAffineLine U1) (toAffineLine U2) :=
          swapLine_isometry.dist_eq (toAffineLine U1) (toAffineLine U2)
        have h_dir1 : (LemmaE.getDirV (swapped U1)) 1 ≠ 0 :=
          swapLine_getDirV_y_ne_zero U1.slope U1.intercept
        have h_dir2 : (LemmaE.getDirV (swapped U2)) 1 ≠ 0 :=
          swapLine_getDirV_y_ne_zero U2.slope U2.intercept
        have h_params1 : LemmaE.affineLineParams (swapped U1) = (U1.slope, U1.intercept) :=
          swapLine_params_eq U1.slope U1.intercept
        have h_params2 : LemmaE.affineLineParams (swapped U2) = (U2.slope, U2.intercept) :=
          swapLine_params_eq U2.slope U2.intercept
        have h_ha1 : |(LemmaE.affineLineParams (swapped U1)).1| ≤ B := by
          rw [h_params1] <;> exact hm U1 hU1'
        have h_ha2 : |(LemmaE.affineLineParams (swapped U2)).1| ≤ B := by
          rw [h_params2] <;> exact hm U2 hU2'
        have h_hb1 : |(LemmaE.affineLineParams (swapped U1)).2| ≤ 3 := by
          rw [h_params1] <;> exact hb U1 hU1'
        have h_hb2 : |(LemmaE.affineLineParams (swapped U2)).2| ≤ 3 := by
          rw [h_params2] <;> exact hb U2 hU2'
        have h_lip : dist (LemmaE.affineLineParams (swapped U1))
            (LemmaE.affineLineParams (swapped U2)) ≤
            L * dist (swapped U1) (swapped U2) :=
          affineLineParams_lipschitz_upper_generalized hB_nonneg
            (swapped U1) (swapped U2) h_dir1 h_dir2 h_ha1 h_ha2 h_hb1 h_hb2
        rw [h_iso] at h_lip
        have h_param_dist : dist (LemmaE.affineLineParams (swapped U1))
            (LemmaE.affineLineParams (swapped U2)) ≤ L * (2 * R) :=
          calc _ ≤ L * dist (toAffineLine U1) (toAffineLine U2) := h_lip
               _ ≤ L * (2 * R) := by gcongr
        have h_slope_abs : |(LemmaE.affineLineParams (swapped U1)).1 -
            (LemmaE.affineLineParams (swapped U2)).1| ≤
            dist (LemmaE.affineLineParams (swapped U1)) (LemmaE.affineLineParams (swapped U2)) := by
          exact le_max_left _ _
        have h_intercept_abs : |(LemmaE.affineLineParams (swapped U1)).2 -
            (LemmaE.affineLineParams (swapped U2)).2| ≤
            dist (LemmaE.affineLineParams (swapped U1)) (LemmaE.affineLineParams (swapped U2)) := by
          exact le_max_right _ _
        have h_slope_real : |U1.slope - U2.slope| ≤ L * (2 * R) := by
          have h1 : |(LemmaE.affineLineParams (swapped U1)).1 -
              (LemmaE.affineLineParams (swapped U2)).1| ≤ L * (2 * R) :=
            le_trans h_slope_abs h_param_dist
          rw [h_params1, h_params2] at h1
          exact h1
        have h_intercept_real : |U1.intercept - U2.intercept| ≤ L * (2 * R) := by
          have h1 : |(LemmaE.affineLineParams (swapped U1)).2 -
              (LemmaE.affineLineParams (swapped U2)).2| ≤ L * (2 * R) :=
            le_trans h_intercept_abs h_param_dist
          rw [h_params1, h_params2] at h1
          exact h1
        have h_slope_def : U1.slope - U2.slope = δ_n * ((U1.a : ℝ) - U2.a) := by
          simp [DyadicTube.slope, hδ_n_def] <;> ring
        have h_intercept_def : U1.intercept - U2.intercept = δ_n * ((U1.b : ℝ) - U2.b) := by
          simp [DyadicTube.intercept, hδ_n_def] <;> ring
        rw [h_slope_def] at h_slope_real
        rw [h_intercept_def] at h_intercept_real
        have h_pos : 0 < δ_n := hδ_n_pos
        have h_a : |(U1.a : ℝ) - U2.a| ≤ (L * (2 * R)) / δ_n := by
          have h : δ_n * |(U1.a : ℝ) - U2.a| ≤ L * (2 * R) := by
            have h3 : |δ_n * ((U1.a : ℝ) - U2.a)| = δ_n * |(U1.a : ℝ) - U2.a| := by
              rw [abs_mul, abs_of_pos h_pos]
            rw [h3] at h_slope_real
            exact h_slope_real
          calc |(U1.a : ℝ) - U2.a|
            = (δ_n * |(U1.a : ℝ) - U2.a|) / δ_n := by field_simp [h_pos.ne'] <;> ring
          _ ≤ (L * (2 * R)) / δ_n := by gcongr
        have h_b : |(U1.b : ℝ) - U2.b| ≤ (L * (2 * R)) / δ_n := by
          have h : δ_n * |(U1.b : ℝ) - U2.b| ≤ L * (2 * R) := by
            have h3 : |δ_n * ((U1.b : ℝ) - U2.b)| = δ_n * |(U1.b : ℝ) - U2.b| := by
              rw [abs_mul, abs_of_pos h_pos]
            rw [h3] at h_intercept_real
            exact h_intercept_real
          calc |(U1.b : ℝ) - U2.b|
            = (δ_n * |(U1.b : ℝ) - U2.b|) / δ_n := by field_simp [h_pos.ne'] <;> ring
          _ ≤ (L * (2 * R)) / δ_n := by gcongr
        have h_bound : (L * (2 * R)) / δ_n ≤ D_grid := by
          have hR : R = (C_move + 1) * δ := by rfl
          rw [hR, hD_grid_def]
          have h_pos2 : 0 < δ_n := hδ_n_pos
          have h9 : δ / δ_n < 2 := by
            have h10 : δ < 2 * δ_n := h_scale
            have h11 : δ / δ_n < (2 * δ_n) / δ_n := by gcongr
            have h12 : (2 * δ_n) / δ_n = 2 := by
              field_simp [h_pos2.ne'] <;> ring
            rw [h12] at h11
            exact h11
          have h11 : 0 ≤ C_move + 1 := by linarith
          calc (L * (2 * ((C_move + 1) * δ))) / δ_n
            = 2 * L * (C_move + 1) * (δ / δ_n) := by ring_nf
          _ ≤ 2 * L * (C_move + 1) * 2 := by gcongr <;> linarith
          _ = 4 * L * (C_move + 1) := by ring
        exact ⟨le_trans h_a h_bound, le_trans h_b h_bound⟩
      let S : Finset (ℤ × ℤ) := F.image (fun U => (U.a, U.b))
      have h_inj : Set.InjOn (fun U : DyadicTube n => (U.a, U.b)) F := by
        intro U1 _ U2 _ h
        have h_all : U1.a = U2.a ∧ U1.b = U2.b := by
          simpa [Prod.ext_iff] using h
        rcases U1 with ⟨a1, b1⟩
        rcases U2 with ⟨a2, b2⟩
        have h_a : a1 = a2 := by simpa using h_all.1
        have h_b : b1 = b2 := by simpa using h_all.2
        congr
      have hS_card : S.card = F.card := by
        rw [Finset.card_image_of_injOn h_inj]
      have hS_bound : ∀ (x : ℤ × ℤ), x ∈ S → ∀ (y : ℤ × ℤ), y ∈ S →
          |(x.1 : ℝ) - y.1| ≤ D_grid ∧ |(x.2 : ℝ) - y.2| ≤ D_grid := by
        intro x hx y hy
        rcases Finset.mem_image.mp hx with ⟨U1, hU1, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨U2, hU2, rfl⟩
        exact h_int_bound U1 hU1 U2 hU2
      have h_grid : S.card ≤ K_pack := by
        have h : S.card ≤ (2 * Nat.ceil D_grid + 1)^2 :=
          grid_packing_bound (by positivity) hS_bound
        have h9 : Nat.ceil D_grid = K1 := by
          rw [hK1_def] <;> rfl
        rw [h9] at h
        exact h
      rw [hS_card] at h_grid
      exact h_grid

    have h_main : T₀.card ≤ K_pack * C_finset.card := by
      have h_union : T₀ = C_finset.biUnion (fun center => T₀.filter fun U => chooseCenter U = center) := by
        ext U
        simp only [Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · intro hU
          exact ⟨chooseCenter U, hc1 U hU, hU, rfl⟩
        · rintro ⟨center, _, hU, _⟩
          exact hU
      rw [h_union]
      have h_sum : (C_finset.biUnion (fun center => T₀.filter fun U => chooseCenter U = center)).card ≤
          ∑ center ∈ C_finset, (T₀.filter fun U => chooseCenter U = center).card :=
        Finset.card_biUnion_le
      calc _ ≤ ∑ center ∈ C_finset, (T₀.filter fun U => chooseCenter U = center).card := h_sum
           _ ≤ ∑ center ∈ C_finset, K_pack := by
             gcongr with center hc
             exact h_fiber_bound center hc
           _ = K_pack * C_finset.card := by
             rw [Finset.sum_const] <;> ring

    have h_final : (T₀.card : ENNReal) ≤ (K_pack : ENNReal) * (C_finset.card : ENNReal) := by
      exact_mod_cast h_main
    have hC_card : (C_finset.card : ENNReal) = Metric.externalCoveringNumber δ.toNNReal T_oriented := by
      have h1 : (C_min.val).encard = ↑C_finset.card := by
        rw [← hC_coe]
        simp [Set.encard]
      have h2 : (C_finset.card : ENNReal) = (C_min.val).encard := by
        exact_mod_cast h1.symm
      rw [h2, h_encard_eq]
    rw [hC_card] at h_final
    simpa [hK_pack_def] using h_final

end DirecretisedFurstenbergEstimate

end
