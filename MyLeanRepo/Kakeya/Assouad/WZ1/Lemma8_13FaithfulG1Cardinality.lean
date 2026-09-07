import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulKaufmanArithmetic

/-!
# Cardinality bound for finalG₁ in faithful Lemma 8.13 Kaufman input
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable section

/-- The final active `G₁` projection has at least `directionKappa / angularScale`
points. -/
lemma wz1Lemma8_13FaithfulG1_cardinality_bound
    (delta epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (input : WZ1Lemma8_13ResidualInput delta epsilon (wz1Lemma8_13FaithfulEta epsilon))
    (hdelta : 0 < delta)
    (affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta)
    (coarsening : WZ1FrostmanCoarseningData
        affine.normalizedF
        (wz1Lemma8_13FaithfulFineScale input)
        (wz1Lemma8_13FaithfulAngularScale input)
        1 (ENNReal.ofReal affine.fineConstant))
    (representatives : WZ1Lemma8_13ActualRepresentativeData
      (G₁ := affine.normalizedG₁)
      (G₂ := affine.normalizedG₂)
      coarsening
      (Kakeya.realRpowENN delta (wz1Lemma8_13FaithfulEta epsilon) / 16)
      affine.normalizedH) :
    wz1Lemma8_13FaithfulDirectionKappa delta epsilon /
        wz1Lemma8_13FaithfulAngularScale input ≤
      ((wz1ActiveTripleProjection representatives.normalizedH 1).card : ℝ) := by
  let eta : ℝ := wz1Lemma8_13FaithfulEta epsilon
  let epsilon1 : ℝ := wz1Lemma8_13FaithfulEpsilonOne epsilon
  let finalH : Finset (Point2 × Point2 × Point2) := representatives.normalizedH
  let finalG₁ : DiscreteSet 2 := wz1ActiveTripleProjection finalH 1
  let selectionScale : ℝ := wz1Lemma8_13FaithfulSelectionScale input
  let angularScale : ℝ := wz1Lemma8_13FaithfulAngularScale input
  let directionKappa : ℝ := wz1Lemma8_13FaithfulDirectionKappa delta epsilon
  set c_ennreal : ENNReal := Kakeya.realRpowENN delta eta / 256 with hc_ennreal_def
  set c_real : ℝ := Real.rpow delta eta / 256 with hc_real_def

  have heta_pos : 0 < eta := by
    dsimp only [eta, wz1Lemma8_13FaithfulEta]; positivity

  -- density /16 /16 = density /256 in ENNReal
  have h_density_eq : (Kakeya.realRpowENN delta eta / 16 / 16) = c_ennreal := by
    have h16_ne_zero : (16 : ENNReal) ≠ 0 := by norm_num
    have h16_ne_top : (16 : ENNReal) ≠ ⊤ := by norm_num
    have h_inv : ((16 : ENNReal) * (16 : ENNReal))⁻¹ = (16 : ENNReal)⁻¹ * (16 : ENNReal)⁻¹ :=
      ENNReal.mul_inv (Or.inl h16_ne_zero) (Or.inl h16_ne_top)
    dsimp only [c_ennreal]
    calc
      Kakeya.realRpowENN delta eta / 16 / 16
        = Kakeya.realRpowENN delta eta * (16 : ENNReal)⁻¹ * (16 : ENNReal)⁻¹ := by
          simp [div_eq_mul_inv] <;> ring
      _ = Kakeya.realRpowENN delta eta * (((16 : ENNReal) * (16 : ENNReal))⁻¹) := by
          rw [h_inv] <;> ring
      _ = Kakeya.realRpowENN delta eta * (256 : ENNReal)⁻¹ := by norm_num
      _ = Kakeya.realRpowENN delta eta / 256 := by simp [div_eq_mul_inv]

  have h_uniform : WZ1UniformTripleDensity c_ennreal
      representatives.normalizedF affine.normalizedG₁ affine.normalizedG₂ finalH := by
    rw [← h_density_eq]; exact representatives.normalizedUniform

  have hH_nonempty : finalH.Nonempty := h_uniform.1
  rcases hH_nonempty with ⟨e0, he0⟩

  -- Fiber bound in ENNReal
  have h_fiber_enn : ((kaufmanSecondFiber finalH e0.1 e0.2.2).card : ENNReal) ≥
      c_ennreal * affine.normalizedG₁.enncard :=
    uniform_density_second_fiber_bound h_uniform e0 he0

  -- Fiber subset finalG₁
  have h_fiber_subset : kaufmanSecondFiber finalH e0.1 e0.2.2 ⊆ finalG₁ := by
    intro g hg
    rcases Finset.mem_image.mp hg with ⟨edge, hedge, h_eq⟩
    have hedge' : edge ∈ finalH := (Finset.mem_filter.mp hedge).1
    have hg_eq : g = edge.2.1 := Eq.symm h_eq
    rw [hg_eq]
    have h_finalG1_def2 : finalG₁ = finalH.image (fun e => e.2.1) := by rfl
    rw [h_finalG1_def2]
    exact Finset.mem_image.mpr ⟨edge, hedge', rfl⟩

  have h_fiber_card_le : (kaufmanSecondFiber finalH e0.1 e0.2.2).card ≤ finalG₁.card :=
    Finset.card_le_card h_fiber_subset

  -- Convert fiber bound to Real via toReal
  have h_rpow_eta_nonneg : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
  have hG1_card_nonneg : 0 ≤ (affine.normalizedG₁.card : ℝ) := by positivity
  have hc_real_nonneg : 0 ≤ c_real := by positivity

  have h_toReal_c : ENNReal.toReal c_ennreal = c_real := by
    dsimp only [c_ennreal, c_real]
    have h1 : Kakeya.realRpowENN delta eta = ENNReal.ofReal (Real.rpow delta eta) := by rfl
    rw [h1]
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal h_rpow_eta_nonneg]
    <;> norm_num

  have h_toReal_G1 : ENNReal.toReal affine.normalizedG₁.enncard = (affine.normalizedG₁.card : ℝ) := by
    simp [DiscreteSet.enncard]

  have h_c_ne_top : c_ennreal ≠ ⊤ := by
    dsimp only [c_ennreal]
    have h1 : Kakeya.realRpowENN delta eta ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    exact ENNReal.div_ne_top h1 (by norm_num)
  have h_rhs_ne_top : c_ennreal * affine.normalizedG₁.enncard ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact h_c_ne_top
    · simp [DiscreteSet.enncard]
  have h_lhs_ne_top : ((kaufmanSecondFiber finalH e0.1 e0.2.2).card : ENNReal) ≠ ⊤ := by simp
  have h_fiber_toReal : ENNReal.toReal ((kaufmanSecondFiber finalH e0.1 e0.2.2).card : ENNReal) ≥
      ENNReal.toReal (c_ennreal * affine.normalizedG₁.enncard) :=
    ENNReal.toReal_mono h_lhs_ne_top h_fiber_enn

  rw [ENNReal.toReal_mul] at h_fiber_toReal
  rw [h_toReal_c, h_toReal_G1] at h_fiber_toReal
  have h_fiber_lhs_toReal : ENNReal.toReal ((kaufmanSecondFiber finalH e0.1 e0.2.2).card : ENNReal) =
      ((kaufmanSecondFiber finalH e0.1 e0.2.2).card : ℝ) := by simp
  rw [h_fiber_lhs_toReal] at h_fiber_toReal

  have h_finalG1_real : (finalG₁.card : ℝ) ≥ c_real * (affine.normalizedG₁.card : ℝ) := by
    have h5 : (finalG₁.card : ℝ) ≥ ((kaufmanSecondFiber finalH e0.1 e0.2.2).card : ℝ) := by
      exact_mod_cast h_fiber_card_le
    linarith

  -- Source cardinality bound via toReal
  have h_source_card := affine.normalizedSource_cardinality
  have h_rpow1 : Kakeya.realRpowENN selectionScale 1 = ENNReal.ofReal selectionScale := by
    simp [Kakeya.realRpowENN, Real.rpow_one]

  have h_source_enn2 : ENNReal.ofReal (Real.rpow delta (3 * eta)) ≤
      (16 : ENNReal) * ENNReal.ofReal selectionScale * affine.normalizedG₁.enncard := by
    have h6 : Kakeya.realRpowENN delta (3 * eta) = ENNReal.ofReal (Real.rpow delta (3 * eta)) := by rfl
    have h7 := h_source_card
    rw [h6, h_rpow1] at h7
    exact h7

  have h_sel_pos : 0 < selectionScale := affine.selectionScale_pos
  have h_sel_nonneg : 0 ≤ selectionScale := h_sel_pos.le

  have h_source_rhs_ne_top : (16 : ENNReal) * ENNReal.ofReal selectionScale * affine.normalizedG₁.enncard ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top <;> simp
    · simp [DiscreteSet.enncard]
  have h_source_toReal : ENNReal.toReal (ENNReal.ofReal (Real.rpow delta (3 * eta))) ≤
      ENNReal.toReal ((16 : ENNReal) * ENNReal.ofReal selectionScale * affine.normalizedG₁.enncard) :=
    ENNReal.toReal_mono h_source_rhs_ne_top h_source_enn2

  have h_rpow3eta_nonneg : 0 ≤ Real.rpow delta (3 * eta) := Real.rpow_nonneg hdelta.le _
  rw [ENNReal.toReal_ofReal h_rpow3eta_nonneg] at h_source_toReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at h_source_toReal
  have h_toReal16 : ENNReal.toReal (16 : ENNReal) = (16 : ℝ) := by simp
  have h_toReal_sel : ENNReal.toReal (ENNReal.ofReal selectionScale) = selectionScale := by
    rw [ENNReal.toReal_ofReal h_sel_nonneg]
  rw [h_toReal16, h_toReal_sel, h_toReal_G1] at h_source_toReal

  have h_source_real : Real.rpow delta (3 * eta) ≤
      16 * selectionScale * (affine.normalizedG₁.card : ℝ) := h_source_toReal

  have hG1_lower : (affine.normalizedG₁.card : ℝ) ≥
      Real.rpow delta (3 * eta) / (16 * selectionScale) := by
    have h_pos : 0 < 16 * selectionScale := by positivity
    calc
      (affine.normalizedG₁.card : ℝ)
        = (16 * selectionScale * (affine.normalizedG₁.card : ℝ)) / (16 * selectionScale) := by
          field_simp [h_pos.ne'] <;> ring
      _ ≥ Real.rpow delta (3 * eta) / (16 * selectionScale) := by
          apply div_le_div_of_nonneg_right h_source_real h_pos.le

  -- Combine
  have h_rpow_add1 : Real.rpow delta eta * Real.rpow delta (3 * eta) = Real.rpow delta (4 * eta) := by
    have h := Real.rpow_add hdelta eta (3 * eta)
    have h' : eta + 3 * eta = 4 * eta := by ring
    rw [h'] at h
    exact h.symm

  have h_combined : (finalG₁.card : ℝ) ≥
      Real.rpow delta (4 * eta) / (4096 * selectionScale) := by
    calc
      (finalG₁.card : ℝ)
        ≥ c_real * (affine.normalizedG₁.card : ℝ) := h_finalG1_real
      _ ≥ c_real * (Real.rpow delta (3 * eta) / (16 * selectionScale)) := by
          gcongr <;> exact hG1_lower
      _ = (Real.rpow delta eta / 256) * (Real.rpow delta (3 * eta) / (16 * selectionScale)) := by rfl
      _ = Real.rpow delta eta * Real.rpow delta (3 * eta) / (256 * 16 * selectionScale) := by
          field_simp [h_sel_pos.ne'] <;> ring
      _ = Real.rpow delta (4 * eta) / (4096 * selectionScale) := by
          rw [h_rpow_add1] <;> ring

  -- Selection scale bound
  have h_selection_le : selectionScale ≤
      384 * Real.rpow delta (-2 * epsilon1) * angularScale :=
    wz1Lemma8_13_selectionScale_le_angular input hdelta affine.aspect_upper

  have h_angular_pos : 0 < angularScale := affine.angularScale_pos
  have h_epsilon1_power_pos : 0 < Real.rpow delta (-2 * epsilon1) := Real.rpow_pos_of_pos hdelta _
  have h_rpow4eta_pos : 0 < Real.rpow delta (4 * eta) := Real.rpow_pos_of_pos hdelta _

  have h_rpow_sub : Real.rpow delta (4 * eta) / Real.rpow delta (-2 * epsilon1) =
      Real.rpow delta (4 * eta + 2 * epsilon1) := by
    have h_pos : 0 < Real.rpow delta (-2 * epsilon1) := h_epsilon1_power_pos
    have h_eq : Real.rpow delta (4 * eta + 2 * epsilon1) * Real.rpow delta (-2 * epsilon1) =
        Real.rpow delta (4 * eta) := by
      have h_add : Real.rpow delta ((4 * eta + 2 * epsilon1) + (-2 * epsilon1)) =
          Real.rpow delta (4 * eta + 2 * epsilon1) * Real.rpow delta (-2 * epsilon1) :=
        Real.rpow_add hdelta (4 * eta + 2 * epsilon1) (-2 * epsilon1)
      have h_sum : (4 * eta + 2 * epsilon1) + (-2 * epsilon1) = 4 * eta := by ring
      rw [h_sum] at h_add
      exact h_add.symm
    have h_cancel : Real.rpow delta (4 * eta + 2 * epsilon1) * Real.rpow delta (-2 * epsilon1) / Real.rpow delta (-2 * epsilon1) =
        Real.rpow delta (4 * eta + 2 * epsilon1) := by
      rw [mul_div_cancel_right₀ _ h_pos.ne']
    rw [h_eq] at h_cancel
    exact h_cancel

  have h_directionKappa_eq : directionKappa =
      Real.rpow delta (4 * eta + 2 * epsilon1) / 1572864 := by
    simp [directionKappa, wz1Lemma8_13FaithfulDirectionKappa, eta, epsilon1] <;> ring

  set denom2 : ℝ := 384 * Real.rpow delta (-2 * epsilon1) * angularScale with hdenom2_def
  have h_denom2_pos : 0 < denom2 := by positivity

  have h_bound : Real.rpow delta (4 * eta) / (4096 * selectionScale) ≥
      directionKappa / angularScale := by
    have h3 : 4096 * selectionScale ≤ 4096 * denom2 := by gcongr <;> linarith
    have h4 : Real.rpow delta (4 * eta) / (4096 * denom2) ≤
        Real.rpow delta (4 * eta) / (4096 * selectionScale) :=
      div_le_div_of_nonneg_left h_rpow4eta_pos.le (by positivity) h3
    have h5 : Real.rpow delta (4 * eta) / (4096 * denom2) =
        Real.rpow delta (4 * eta + 2 * epsilon1) / (1572864 * angularScale) := by
      simp only [hdenom2_def]
      have h6 : Real.rpow delta (4 * eta) / (4096 * (384 * Real.rpow delta (-2 * epsilon1) * angularScale)) =
          (Real.rpow delta (4 * eta) / Real.rpow delta (-2 * epsilon1)) / (4096 * 384 * angularScale) := by
        field_simp [h_epsilon1_power_pos.ne', h_angular_pos.ne'] <;> ring
      rw [h6, h_rpow_sub] <;> norm_num <;> ring
    have h7 : Real.rpow delta (4 * eta + 2 * epsilon1) / (1572864 * angularScale) =
        (Real.rpow delta (4 * eta + 2 * epsilon1) / 1572864) / angularScale := by
      field_simp [h_angular_pos.ne'] <;> ring
    have h8 : Real.rpow delta (4 * eta) / (4096 * selectionScale) ≥
        Real.rpow delta (4 * eta) / (4096 * denom2) := h4
    calc
      Real.rpow delta (4 * eta) / (4096 * selectionScale)
        ≥ Real.rpow delta (4 * eta) / (4096 * denom2) := h8
      _ = Real.rpow delta (4 * eta + 2 * epsilon1) / (1572864 * angularScale) := h5
      _ = (Real.rpow delta (4 * eta + 2 * epsilon1) / 1572864) / angularScale := h7
      _ = directionKappa / angularScale := by rw [h_directionKappa_eq]

  exact h_bound.trans h_combined

end

end Kakeya.Assouad
