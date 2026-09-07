module

/-
  GoodCaseImprovedIncidence — Prove the improved coarse incidence bound
  in the good first-scale case using density transfer and the geometric bridge.

  Route:
  1. hcfg.h_good gives IsRegularBetweenScales config.pointSet δ_coarse 1 t_j C C
  2. Density transfer (c = 1/(9K)) gives IsRegularBetweenScales P_selected δ_coarse 1 t_j (9KC) C
  3. square_root_regular_from_unit_between_scales → IsSquareRootRegular
  4. Keep exponent u = t_j, weaken constants to δ^{-εReg}
  5. Translate by centerTranslation
  6. Call coarse_incidence_geometric_bridge

  Whiteprint node: combining_theorem_rework / good_case_improved_incidence
  Status: Complete. Integrated on the active coarse-good path of inductive_step_core_v2.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCaseDensityHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.IncidenceHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseIncidenceGeometricBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseIncidenceWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BetweenScalesToSset
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.GoodTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open InductionConfigurations

/-! ========================================================================
   Main lemma: good-case improved incidence bound
   ======================================================================== -/

/-- Given good-scale regularity and B1 bridge output, prove the improved
    coarse incidence bound via density transfer + geometric bridge. -/
lemma good_case_improved_incidence
    {k m M MΔ : ℕ} {s t t_j εReg η C_between CΔ C_cfg K : ℝ}
    (hnm : m ≤ k)
    (config : CTNiceConfiguration k s C_cfg M)
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (P : Finset (DyadicSquare k))
    (hP_sub : P ⊆ config.P₀)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hP_nonempty : P.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ k : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ k : ℤ))
    (h_good : IsRegularBetweenScales config.pointSet (dyadicDelta m) 1 t_j C_between C_between)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Uniform regular incidence estimate body at exact scale δ
    (h_est_body : RegularIncidenceAtScale (canonicalWideCarrier m) s t εReg η (dyadicDelta m))
    (hu_t : t ≤ t_j) (htj_two : t_j ≤ 2) (hs1 : s < 1) (hst : s < t)
    -- Constant weakenings
    (hK_pos : 0 < K) (hC_between_pos : 0 < C_between)
    (hC_ge1 : 1 ≤ 9 * K * C_between)
    (hC_weaken1 : 9 * K * C_between ≤ Real.rpow (dyadicDelta m) (-εReg))
    (hC_weaken2 : C_between ≤ Real.rpow (dyadicDelta m) (-εReg))
    (hCΔ_weaken : CΔ ≤ Real.rpow (dyadicDelta m) (-εReg))
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η) :
    (coarseConfig.T₀.card : ENNReal) ≥
      ENNReal.ofReal (Real.rpow (dyadicDelta m) (-(2 * s + η))) := by
  let δ := dyadicDelta m
  have hδ_pos : 0 < δ := dyadicDelta_pos m
  let P_selected : Set EuclideanPlane := ⋃ p ∈ P, (p.toSet : Set EuclideanPlane)
  let u : ℝ := t_j

  -- P_selected ⊆ config.pointSet
  have hPsel_sub : P_selected ⊆ config.pointSet := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    have h_p_in_P0 : p ∈ config.P₀ := hP_sub hp
    exact Set.mem_iUnion₂.mpr ⟨p, h_p_in_P0, hxp⟩

  -- P_selected ⊆ dyadicSquare 1 0 0
  have h_config_unit : config.pointSet ⊆ dyadicSquare 1 0 0 :=
    pointSet_sub_dyadicSquare1 h_squares_unit
  have hPsel_unit : P_selected ⊆ dyadicSquare 1 0 0 :=
    Set.Subset.trans hPsel_sub h_config_unit

  -- P_selected ⊆ coarseConfig.pointSet
  have hPsel_coarse : P_selected ⊆ coarseConfig.pointSet := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    let Q : DyadicSquare m := InductionConfigurations.containingSquare hnm p
    have hQ_in : Q ∈ coarseConfig.P₀ := by
      rw [hcoarse_P_eq]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_contain : InductionConfigurations.squareContained hnm p Q :=
      (InductionConfigurations.containingSquare_iff hnm p Q).mp rfl
    have h_p_sub_Q : (p.toSet : Set EuclideanPlane) ⊆ (Q.toSet : Set EuclideanPlane) :=
      DiscretisedFurstenbergEstimate.InductionOnScales.squareContained_toSet_subset hnm h_contain
    have hxQ : x ∈ Q.toSet := h_p_sub_Q hxp
    exact Set.mem_iUnion₂.mpr ⟨Q, hQ_in, hxQ⟩

  -- Density c = 1/(9K)
  have hK_pos' : 0 < K := hK_pos
  have h9K_pos : 0 < 9 * K := by positivity
  let c : ℝ := 1 / (9 * K)
  have hc_pos : 0 < c := by positivity

  -- Covering bounds
  let S_card : ℕ := (config.P₀.image (InductionConfigurations.containingSquare hnm)).card
  have h_upper : (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal) ≤
      (S_card : ENNReal) :=
    cover_config_pointSet_upper hnm config
  have h_lower : (coarseConfig.P₀.card : ENNReal) / 9 ≤
      Metric.externalCoveringNumber δ.toNNReal P_selected :=
    cover_P_selected_lower hnm config coarseConfig P hP_sub hcoarse_P_eq hP_nonempty
  have h_card : (S_card : ENNReal) ≤ ENNReal.ofReal K * (coarseConfig.P₀.card : ENNReal) := by
    have h : (S_card : ℝ) ≤ K * (coarseConfig.P₀.card : ℝ) := by exact_mod_cast h_card_bound
    have h' : (S_card : ENNReal) = ENNReal.ofReal (S_card : ℝ) := by simp
    rw [h']
    have h'' : ENNReal.ofReal (S_card : ℝ) ≤ ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h
    have h3 : ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) =
        ENNReal.ofReal K * (coarseConfig.P₀.card : ENNReal) := by
      have h4 : ENNReal.ofReal (K * (coarseConfig.P₀.card : ℝ)) =
          ENNReal.ofReal K * ENNReal.ofReal ((coarseConfig.P₀.card : ℝ)) := by
        rw [← ENNReal.ofReal_mul] <;> positivity
      rw [h4]
      have h5 : ENNReal.ofReal ((coarseConfig.P₀.card : ℝ)) = (coarseConfig.P₀.card : ENNReal) := by
        simp
      rw [h5]
    rw [h3] at h''
    exact h''

  -- Density: c * cover(full) ≤ cover(selected)
  have h_density_cover : ENNReal.ofReal c *
      (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal P_selected : ENNReal) := by
    let S_card := (config.P₀.image (InductionConfigurations.containingSquare hnm)).card
    have h1 : (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal) ≤ (↑S_card : ENNReal) := h_upper
    have h2 : (↑S_card : ENNReal) ≤ ENNReal.ofReal K * (coarseConfig.P₀.card : ENNReal) := h_card
    have h_cK : ENNReal.ofReal c * ENNReal.ofReal K = ENNReal.ofReal (1 / 9 : ℝ) := by
      have h_eq1 : ENNReal.ofReal c * ENNReal.ofReal K = ENNReal.ofReal (c * K) := by
        rw [← ENNReal.ofReal_mul] <;> positivity
      rw [h_eq1]
      have h_eq2 : c * K = 1 / 9 := by
        dsimp only [c]
        field_simp [h9K_pos.ne'] <;> ring
      rw [h_eq2]
      <;> rfl
    calc ENNReal.ofReal c * (Metric.externalCoveringNumber δ.toNNReal config.pointSet : ENNReal)
      ≤ ENNReal.ofReal c * (↑S_card : ENNReal) := by gcongr
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal K * (coarseConfig.P₀.card : ENNReal)) := by gcongr
    _ = (ENNReal.ofReal c * ENNReal.ofReal K) * (coarseConfig.P₀.card : ENNReal) := by ring
    _ = ENNReal.ofReal (1 / 9 : ℝ) * (coarseConfig.P₀.card : ENNReal) := by rw [h_cK]
    _ = (coarseConfig.P₀.card : ENNReal) / 9 := by
      have h_eq : ENNReal.ofReal (1 / 9 : ℝ) = (9 : ENNReal)⁻¹ := by
        have h1 : ENNReal.ofReal (1 / 9 : ℝ) = (ENNReal.ofReal (9 : ℝ))⁻¹ := by
          have h11 : (1 / 9 : ℝ) = (9 : ℝ)⁻¹ := by norm_num
          rw [h11, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 9)]
        have h2 : ENNReal.ofReal (9 : ℝ) = (9 : ENNReal) := by simp
        rw [h1, h2]
      rw [h_eq, div_eq_mul_inv, mul_comm] <;> rfl
    _ ≤ (Metric.externalCoveringNumber δ.toNNReal P_selected : ENNReal) := h_lower

  -- Density condition for subset_with_density
  have h_density : ∀ (i j : ℤ), (config.pointSet ∩ dyadicSquare 1 i j).Nonempty →
      ENNReal.ofReal c *
        Metric.externalCoveringNumber (δ / 1).toNNReal
          (homothetyS 1 i j '' (config.pointSet ∩ dyadicSquare 1 i j)) ≤
      Metric.externalCoveringNumber (δ / 1).toNNReal
          (homothetyS 1 i j '' (P_selected ∩ dyadicSquare 1 i j)) := by
    intro i j hnonempty
    by_cases h_ij : i = 0 ∧ j = 0
    · -- Case (i,j) = (0,0)
      rcases h_ij with ⟨rfl, rfl⟩
      have h_hom_id : homothetyS 1 0 0 = id := by
        funext x
        simp [homothetyS]
        <;> ext k <;> fin_cases k <;> simp <;> ring
      have h_full_inter : config.pointSet ∩ dyadicSquare 1 0 0 = config.pointSet := by
        rw [Set.inter_comm, Set.inter_eq_right.mpr h_config_unit]
      have h_sel_inter : P_selected ∩ dyadicSquare 1 0 0 = P_selected := by
        rw [Set.inter_comm, Set.inter_eq_right.mpr hPsel_unit]
      simp only [h_hom_id, h_full_inter, h_sel_inter, Set.image_id]
      simpa using h_density_cover
    · -- Case (i,j) ≠ (0,0): intersection is empty
      have h_disj : Disjoint (config.pointSet : Set EuclideanPlane) (dyadicSquare 1 i j : Set EuclideanPlane) := by
        have h1 : config.pointSet ⊆ dyadicSquare 1 0 0 := h_config_unit
        have h2 : Disjoint (dyadicSquare 1 0 0) (dyadicSquare 1 i j) := by
          simp only [dyadicSquare, Set.disjoint_left, Set.mem_setOf_eq]
          intro x h1 h2
          have h_ne : i ≠ 0 ∨ j ≠ 0 := by tauto
          rcases h_ne with (h_i | h_j)
          · have h_i1 : (0 : ℝ) ≤ x 0 ∧ x 0 < (1 : ℝ) := by simpa [Set.mem_Ico] using h1.1
            have h_i2 : (i : ℝ) ≤ x 0 ∧ x 0 < (i : ℝ) + 1 := by simpa [Set.mem_Ico] using h2.1
            have h_i_int : i ≤ -1 ∨ i ≥ 1 := by omega
            rcases h_i_int with (h_lt | h_gt)
            · have h_i3 : (i : ℝ) ≤ -1 := by exact_mod_cast h_lt
              linarith [h_i1.1, h_i2.2, h_i3]
            · have h_i4 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h_gt
              linarith [h_i1.2, h_i2.1, h_i4]
          · have h_j1 : (0 : ℝ) ≤ x 1 ∧ x 1 < (1 : ℝ) := by simpa [Set.mem_Ico] using h1.2
            have h_j2 : (j : ℝ) ≤ x 1 ∧ x 1 < (j : ℝ) + 1 := by simpa [Set.mem_Ico] using h2.2
            have h_j_int : j ≤ -1 ∨ j ≥ 1 := by omega
            rcases h_j_int with (h_lt | h_gt)
            · have h_j3 : (j : ℝ) ≤ -1 := by exact_mod_cast h_lt
              linarith [h_j1.1, h_j2.2, h_j3]
            · have h_j4 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h_gt
              linarith [h_j1.2, h_j2.1, h_j4]
        exact Disjoint.mono_left h1 h2
      have h_empty : config.pointSet ∩ dyadicSquare 1 i j = ∅ := by
        exact Set.disjoint_iff_inter_eq_empty.mp h_disj
      rw [h_empty] at hnonempty
      simp at hnonempty

  -- Transfer regularity
  have h_reg_transfer : IsRegularBetweenScales P_selected δ 1 t_j (C_between / c) C_between :=
    IsRegularBetweenScales.subset_with_density h_good hPsel_sub hc_pos h_density

  have hC_div : C_between / c = 9 * K * C_between := by
    simp [c] <;> field_simp [h9K_pos.ne'] <;> ring
  rw [hC_div] at h_reg_transfer

  -- P_selected is nonempty
  have hPsel_nonempty : P_selected.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    let δk := dyadicDelta k
    have hδk_pos : 0 < δk := dyadicDelta_pos k
    let x : EuclideanPlane := WithLp.toLp (2 : ENNReal)
        (fun i : Fin 2 => if i = 0 then (p.i : ℝ) * δk + δk / 2 else (p.j : ℝ) * δk + δk / 2)
    have hx0 : x 0 = (p.i : ℝ) * δk + δk / 2 := by
      simp [x] <;> rfl
    have hx1 : x 1 = (p.j : ℝ) * δk + δk / 2 := by
      simp [x] <;> rfl
    have hx_in : x ∈ (p.toSet : Set EuclideanPlane) := by
      have h_goal : (p.i : ℝ) * δk ≤ x 0 ∧ x 0 < ((p.i : ℝ) + 1) * δk ∧
                      (p.j : ℝ) * δk ≤ x 1 ∧ x 1 < ((p.j : ℝ) + 1) * δk := by
        exact ⟨by rw [hx0]; linarith, by rw [hx0]; linarith,
                 by rw [hx1]; linarith, by rw [hx1]; linarith⟩
      simpa [DyadicSquare.toSet] using h_goal
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨p, hp, hx_in⟩⟩

  -- Convert to IsSquareRootRegular
  have h_sqrt_reg : IsSquareRootRegular δ t_j (9 * K * C_between) C_between P_selected :=
    square_root_regular_from_unit_between_scales h_reg_transfer hPsel_unit hPsel_nonempty

  -- Weaken constants to δ^{-εReg}
  have h_reg_final : IsSquareRootRegular δ u
      (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P_selected :=
    IsSquareRootRegular.weaken_CK h_sqrt_reg hC_weaken1 hC_weaken2
      (Real.rpow_pos_of_pos hδ_pos _) (Real.rpow_pos_of_pos hδ_pos _)

  -- Translate
  let P_orig : Set EuclideanPlane := translationEquiv centerTranslation '' P_selected
  have hP_orig_regular : IsSquareRootRegular δ u
      (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P_orig :=
    isSquareRootRegular_translate h_reg_final
  have hP_orig_ball : P_orig ⊆ Metric.closedBall 0 1 :=
    unit_square_translate_sub_ball hPsel_unit
  have hP_orig_sub : P_orig ⊆ translatedCoarsePointSet coarseConfig := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have h_y_in_coarse : y ∈ coarseConfig.pointSet := hPsel_coarse hy
    exact ⟨y, h_y_in_coarse, rfl⟩

  -- Call geometric bridge
  exact coarse_incidence_geometric_bridge
    (coarseConfig := coarseConfig)
    (h_slope_coarse := h_slope_coarse)
    (hεReg_pos := hεReg_pos)
    (hη_pos := hη_pos)
    (δ := δ)
    (hδ_pos := hδ_pos)
    (h_est_body := h_est_body)
    (hu_t := hu_t)
    (hu_two := htj_two)
    (hδ_eq := by rfl)
    (P_orig := P_orig)
    (hP_sub := hP_orig_sub)
    (hP_ball := hP_orig_ball)
    (hP_regular := hP_orig_regular)
    (hCΔ_weaken := hCΔ_weaken)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
