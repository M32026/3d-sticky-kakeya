import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellSelectionSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationRestrict
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellScaleHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionDichotomyFromLeaves
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedHeavyCell
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedRefinedActive

/-!
PDF Proposition 8.9 wide branch: retain one fixed absolute-size cell triple
with the quantitative margins needed for common affine normalization.
-/

namespace Kakeya.Assouad

open scoped ENNReal
open Classical

theorem wz1_wide_fixed_cell_selection :
    WZ1Proposition8_9WideFixedCellSelectionStatement := by
  intro _hCoarsePrep
  intro epsilon parameters hepsilon_pos hepsilon_lt_one
  let lambda := parameters.projectionLambda
  let zeta := parameters.zeta
  let alpha := parameters.alpha
  have hlambda_pos : 0 < lambda := parameters.projectionLambda_pos
  have hzeta_pos : 0 < zeta := parameters.zeta_pos
  have halpha_pos : 0 < alpha := parameters.alpha_pos
  have hzeta_lt_one : zeta < 1 := parameters.zeta_lt_one
  have halpha_le : alpha ≤ zeta * lambda / 16 := parameters.alpha_le_zeta_projectionLambda

  let L : ENNReal := wz1WideFixedCellCountLoss
  let K_abs : ENNReal := (2 ^ 27 : ENNReal) * 16 * L

  have hK_ne_top : K_abs ≠ ⊤ := by
    simp [K_abs, L, wz1WideFixedCellCountLoss] <;> norm_num
  have hK_ne_zero : K_abs ≠ 0 := by
    simp [K_abs, L, wz1WideFixedCellCountLoss] <;> norm_num

  rcases wide_fixed_cell_absorption halpha_pos hlambda_pos hzeta_pos
      hepsilon_pos hepsilon_lt_one halpha_le (hK_ne_top := hK_ne_top) with
    ⟨etaCap, hetaCap_pos, h_abs_main⟩

  refine ⟨etaCap, hetaCap_pos, fun eta heta_pos heta_le => ?_⟩

  rcases h_abs_main eta heta_pos heta_le with
    ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, h_abs_delta⟩

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta F G₁ G₂ H hdelta hdelta_le data hwidth coarse

  let scale := coarse.scale
  have hscale_pos : 0 < scale := coarse.scale_pos
  have hscale_le_one : scale ≤ 1 :=
    le_trans coarse.scale_le_projectionDelta₀ parameters.projectionDelta₀_le_one

  have hscale_lt_rpow : scale < Real.rpow delta (epsilon / 10) :=
    wide_coarse_scale_lt_rpow hdelta hepsilon_pos data.width_pos coarse.scale_eq hwidth

  have h_abs := h_abs_delta delta hdelta hdelta_le scale hscale_pos hscale_lt_rpow
  have h_abs1 : K_abs * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN scale (-(lambda / 4)) := h_abs.1
  have h_abs2 : K_abs * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN scale (-(lambda * zeta / 4)) := h_abs.2.1
  have h_abs3 : Kakeya.realRpowENN scale alpha ≤
      Kakeya.realRpowENN delta eta / K_abs := h_abs.2.2.1
  have h_abs4 : scale ≤ 1 / 20 := h_abs.2.2.2

  let c : ENNReal := Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)
  let density : ENNReal := c / (16 * L)

  have h27_ne_zero : (2 ^ 27 : ENNReal) ≠ 0 := by norm_num
  have h27_ne_top : (2 ^ 27 : ENNReal) ≠ ⊤ := by norm_num
  have h16L_ne_zero : (16 * L : ENNReal) ≠ 0 := by
    simp [L, wz1WideFixedCellCountLoss] <;> norm_num
  have h16L_ne_top : (16 * L : ENNReal) ≠ ⊤ := by
    simp [L, wz1WideFixedCellCountLoss] <;> norm_num

  have h_density_eq : density = Kakeya.realRpowENN delta eta / K_abs := by
    dsimp only [density, c, K_abs]
    calc
      (Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)) / (16 * L)
        = (Kakeya.realRpowENN delta eta * (2 ^ 27 : ENNReal)⁻¹) * (16 * L)⁻¹ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
      _ = Kakeya.realRpowENN delta eta * ((2 ^ 27 : ENNReal)⁻¹ * (16 * L)⁻¹) := by
          rw [mul_assoc]
      _ = Kakeya.realRpowENN delta eta * (((2 ^ 27 : ENNReal) * (16 * L))⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl h27_ne_zero) (Or.inl h27_ne_top)]
      _ = Kakeya.realRpowENN delta eta / (((2 ^ 27 : ENNReal) * (16 * L))) := by
          rw [div_eq_mul_inv]
      _ = Kakeya.realRpowENN delta eta / K_abs := by
          have h : ((2 ^ 27 : ENNReal) * (16 * L)) = K_abs := by
            dsimp only [K_abs]
            rw [mul_assoc]
          rw [h]

  have h_rpow_ne_zero : Kakeya.realRpowENN delta eta ≠ 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  have h_rpow_ne_top : Kakeya.realRpowENN delta eta ≠ ⊤ :=
    ENNReal.ofReal_ne_top

  have h_density_ne_zero : density ≠ 0 := by
    rw [h_density_eq]
    exact (ENNReal.div_ne_zero).mpr ⟨h_rpow_ne_zero, hK_ne_top⟩

  have h_density_ne_top : density ≠ ⊤ := by
    rw [h_density_eq]
    exact ENNReal.div_ne_top h_rpow_ne_top hK_ne_zero

  rcases wz1_wide_fixed_refined_active
      wz1_wide_fixed_heavy_cell
      wz1_tripartite_hypergraph_refinement
      (coarse := coarse) h_abs4 with
    ⟨ra⟩

  let cellH := ra.cellH
  let cellF := ra.cellF
  let cellG₁ := ra.cellG₁
  let cellG₂ := ra.cellG₂
  let heavy := ra.heavy

  have h_density_le : Kakeya.realRpowENN scale alpha ≤ density := by
    rw [h_density_eq]
    exact h_abs3
  have hUniform : WZ1UniformTripleDensity (Kakeya.realRpowENN scale alpha)
      cellF cellG₁ cellG₂ cellH :=
    uniform_triple_density_mono ra.uniform_margin h_density_le

  let factor : ENNReal := K_abs * Kakeya.realRpowENN delta (-eta)

  have h_rpow_neg_mul : Kakeya.realRpowENN delta (-eta) * Kakeya.realRpowENN delta eta = 1 := by
    rw [← realRpowENN_add hdelta (-eta) eta]
    have h4 : -eta + eta = 0 := by ring
    rw [h4]
    simp [Kakeya.realRpowENN]

  have h_K_div : K_abs / K_abs = 1 := by
    rw [div_eq_mul_inv, ENNReal.mul_inv_cancel hK_ne_zero hK_ne_top] <;> simp

  have h_factor_density : factor * density = 1 := by
    have h_eq : factor * density =
        (K_abs * Kakeya.realRpowENN delta (-eta)) * (Kakeya.realRpowENN delta eta / K_abs) := by
      rw [h_density_eq] <;> rfl
    rw [h_eq]
    have h_div : Kakeya.realRpowENN delta eta / K_abs =
        Kakeya.realRpowENN delta eta * K_abs⁻¹ := by
      rw [div_eq_mul_inv]
    rw [h_div]
    have h5 : (K_abs * Kakeya.realRpowENN delta (-eta)) * (Kakeya.realRpowENN delta eta * K_abs⁻¹) =
        (Kakeya.realRpowENN delta (-eta) * Kakeya.realRpowENN delta eta) * (K_abs * K_abs⁻¹) := by
      ac_rfl
    rw [h5, h_rpow_neg_mul]
    have h6 : K_abs * K_abs⁻¹ = 1 := ENNReal.mul_inv_cancel hK_ne_zero hK_ne_top
    rw [h6] <;> simp

  have h_factorF : coarse.coarseF.enncard ≤ factor * cellF.enncard := by
    have h_ret : density * coarse.coarseF.enncard ≤ cellF.enncard := ra.cellF_retention
    calc
      coarse.coarseF.enncard
        = 1 * coarse.coarseF.enncard := by rw [one_mul]
      _ = (factor * density) * coarse.coarseF.enncard := by rw [h_factor_density]
      _ = factor * (density * coarse.coarseF.enncard) := by rw [mul_assoc]
      _ ≤ factor * cellF.enncard := by gcongr

  have h_factorG1 : coarse.coarseG₁.enncard ≤ factor * cellG₁.enncard := by
    have h_ret : density * coarse.coarseG₁.enncard ≤ cellG₁.enncard := ra.cellG₁_retention
    calc
      coarse.coarseG₁.enncard
        = 1 * coarse.coarseG₁.enncard := by rw [one_mul]
      _ = (factor * density) * coarse.coarseG₁.enncard := by rw [h_factor_density]
      _ = factor * (density * coarse.coarseG₁.enncard) := by rw [mul_assoc]
      _ ≤ factor * cellG₁.enncard := by gcongr

  have h_factorG2 : coarse.coarseG₂.enncard ≤ factor * cellG₂.enncard := by
    have h_ret : density * coarse.coarseG₂.enncard ≤ cellG₂.enncard := ra.cellG₂_retention
    calc
      coarse.coarseG₂.enncard
        = 1 * coarse.coarseG₂.enncard := by rw [one_mul]
      _ = (factor * density) * coarse.coarseG₂.enncard := by rw [h_factor_density]
      _ = factor * (density * coarse.coarseG₂.enncard) := by rw [mul_assoc]
      _ ≤ factor * cellG₂.enncard := by gcongr

  have hcellF_subset_coarse : cellF ⊆ coarse.coarseF :=
    subset_trans ra.cellF_subset heavy.ambientCellF_subset
  have hcellG1_subset_coarse : cellG₁ ⊆ coarse.coarseG₁ :=
    subset_trans ra.cellG₁_subset heavy.ambientCellG₁_subset
  have hcellG2_subset_coarse : cellG₂ ⊆ coarse.coarseG₂ :=
    subset_trans ra.cellG₂_subset heavy.ambientCellG₂_subset

  have h_frostman_const_le :
      Kakeya.realRpowENN scale (-(lambda / 2)) * factor ≤
      Kakeya.realRpowENN scale (-(3 * lambda / 4)) := by
    have h_exp : (-(lambda / 2)) + (-(lambda / 4)) = -(3 * lambda / 4) := by ring
    have h_mul : Kakeya.realRpowENN scale (-(lambda / 2)) * factor ≤
        Kakeya.realRpowENN scale (-(lambda / 2)) *
        Kakeya.realRpowENN scale (-(lambda / 4)) := by gcongr
    have h_add : Kakeya.realRpowENN scale (-(lambda / 2)) *
        Kakeya.realRpowENN scale (-(lambda / 4)) =
        Kakeya.realRpowENN scale ((-(lambda / 2)) + (-(lambda / 4))) :=
      (realRpowENN_add hscale_pos _ _).symm
    rw [h_add, h_exp] at h_mul
    exact h_mul

  have hcellF_frostman_margin : cellF.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-(3 * lambda / 4))) := by
    have h_transfer : cellF.IsFrostman scale 1
        (Kakeya.realRpowENN scale (-(lambda / 2)) * factor) :=
      coarse.coarseF_frostman_margin.subset_with_factor hcellF_subset_coarse h_factorF
    exact h_transfer.mono_const h_frostman_const_le

  have hcellG1_frostman_margin : cellG₁.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-(3 * lambda / 4))) := by
    have h_transfer : cellG₁.IsFrostman scale 1
        (Kakeya.realRpowENN scale (-(lambda / 2)) * factor) :=
      coarse.coarseG₁_frostman_margin.subset_with_factor hcellG1_subset_coarse h_factorG1
    exact h_transfer.mono_const h_frostman_const_le

  have hcellG2_frostman_margin : cellG₂.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-(3 * lambda / 4))) := by
    have h_transfer : cellG₂.IsFrostman scale 1
        (Kakeya.realRpowENN scale (-(lambda / 2)) * factor) :=
      coarse.coarseG₂_frostman_margin.subset_with_factor hcellG2_subset_coarse h_factorG2
    exact h_transfer.mono_const h_frostman_const_le

  have hmargin_le_full : Kakeya.realRpowENN scale (-(3 * lambda / 4)) ≤
      Kakeya.realRpowENN scale (-lambda) := by
    have h : -lambda ≤ -(3 * lambda / 4) := by linarith
    simp only [Kakeya.realRpowENN]
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hscale_pos hscale_le_one h

  have hcellF_frostman : cellF.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) :=
    hcellF_frostman_margin.mono_const hmargin_le_full
  have hcellG1_frostman : cellG₁.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) :=
    hcellG1_frostman_margin.mono_const hmargin_le_full
  have hcellG2_frostman : cellG₂.IsFrostman scale 1
      (Kakeya.realRpowENN scale (-lambda)) :=
    hcellG2_frostman_margin.mono_const hmargin_le_full

  have h_line_absorb :
      Kakeya.realRpowENN scale (-(lambda / 2) * zeta) * factor ≤
      Kakeya.realRpowENN scale (-(3 * lambda / 4) * zeta) := by
    have h_exp : (-(lambda / 2) * zeta) + (-(lambda * zeta / 4)) = -((3 * lambda / 4) * zeta) := by ring
    have h_mul : Kakeya.realRpowENN scale (-(lambda / 2) * zeta) * factor ≤
        Kakeya.realRpowENN scale (-(lambda / 2) * zeta) *
        Kakeya.realRpowENN scale (-(lambda * zeta / 4)) := by gcongr
    have h_add : Kakeya.realRpowENN scale (-(lambda / 2) * zeta) *
        Kakeya.realRpowENN scale (-(lambda * zeta / 4)) =
        Kakeya.realRpowENN scale ((-(lambda / 2) * zeta) + (-(lambda * zeta / 4))) :=
      (realRpowENN_add hscale_pos _ _).symm
    rw [h_add, h_exp] at h_mul
    have h_eq3 : -((3 * lambda / 4) * zeta) = (-(3 * lambda / 4)) * zeta := by ring
    rw [h_eq3] at h_mul
    exact h_mul

  have hline1_margin : WZ1LineNonConcentration scale (3 * lambda / 4) zeta cellG₁ :=
    coarse.first_line_nonconcentration_margin.transfer_subset
      hcellG1_subset_coarse h_factorG1 h_line_absorb hscale_pos hscale_le_one (by linarith)

  have hline2_margin : WZ1LineNonConcentration scale (3 * lambda / 4) zeta cellG₂ :=
    coarse.second_line_nonconcentration_margin.transfer_subset
      hcellG2_subset_coarse h_factorG2 h_line_absorb hscale_pos hscale_le_one (by linarith)

  have hline1 : WZ1LineNonConcentration scale lambda zeta cellG₁ :=
    hline1_margin.mono_lambda hscale_pos hscale_le_one (by linarith) (by linarith)
  have hline2 : WZ1LineNonConcentration scale lambda zeta cellG₂ :=
    hline2_margin.mono_lambda hscale_pos hscale_le_one (by linarith) (by linarith)

  have hcellF_ball : ∀ p ∈ cellF, dist p heavy.centerF ≤ 1 / 100 := by
    intro p hp
    have h_in_amb : p ∈ heavy.ambientCellF := ra.cellF_subset hp
    have h_filter : p ∈ (coarse.coarseF.filter (fun point => gridCenter (1 / 100) point = heavy.centerF)) := by
      rw [←heavy.ambientCellF_eq] <;> exact h_in_amb
    have h_eq : gridCenter (1 / 100) p = heavy.centerF :=
      (Finset.mem_filter.mp h_filter).2
    have h_close : dist p (gridCenter (1 / 100) p) ≤ 1 / 100 :=
      gridCenter_rho_close (1 / 100) (by norm_num) p
    rw [h_eq] at h_close
    exact h_close

  have hcellG1_ball : ∀ p ∈ cellG₁, dist p heavy.centerG₁ ≤ 1 / 100 := by
    intro p hp
    have h_in_amb : p ∈ heavy.ambientCellG₁ := ra.cellG₁_subset hp
    have h_filter : p ∈ (coarse.coarseG₁.filter (fun point => gridCenter (1 / 100) point = heavy.centerG₁)) := by
      rw [←heavy.ambientCellG₁_eq] <;> exact h_in_amb
    have h_eq : gridCenter (1 / 100) p = heavy.centerG₁ :=
      (Finset.mem_filter.mp h_filter).2
    have h_close : dist p (gridCenter (1 / 100) p) ≤ 1 / 100 :=
      gridCenter_rho_close (1 / 100) (by norm_num) p
    rw [h_eq] at h_close
    exact h_close

  have hcellG2_ball : ∀ p ∈ cellG₂, dist p heavy.centerG₂ ≤ 1 / 100 := by
    intro p hp
    have h_in_amb : p ∈ heavy.ambientCellG₂ := ra.cellG₂_subset hp
    have h_filter : p ∈ (coarse.coarseG₂.filter (fun point => gridCenter (1 / 100) point = heavy.centerG₂)) := by
      rw [←heavy.ambientCellG₂_eq] <;> exact h_in_amb
    have h_eq : gridCenter (1 / 100) p = heavy.centerG₂ :=
      (Finset.mem_filter.mp h_filter).2
    have h_close : dist p (gridCenter (1 / 100) p) ≤ 1 / 100 :=
      gridCenter_rho_close (1 / 100) (by norm_num) p
    rw [h_eq] at h_close
    exact h_close

  exact ⟨{
    ambientCellF := heavy.ambientCellF
    ambientCellG₁ := heavy.ambientCellG₁
    ambientCellG₂ := heavy.ambientCellG₂
    inducedH := heavy.inducedH
    cellH := cellH
    cellF := cellF
    cellG₁ := cellG₁
    cellG₂ := cellG₂
    centerF := heavy.centerF
    centerG₁ := heavy.centerG₁
    centerG₂ := heavy.centerG₂
    ambientCellF_eq := heavy.ambientCellF_eq
    ambientCellG₁_eq := heavy.ambientCellG₁_eq
    ambientCellG₂_eq := heavy.ambientCellG₂_eq
    inducedH_eq := heavy.inducedH_eq
    cellH_subset := ra.cellH_subset
    cellF_eq := ra.cellF_eq
    cellG₁_eq := ra.cellG₁_eq
    cellG₂_eq := ra.cellG₂_eq
    cellF_subset := ra.cellF_subset
    cellG₁_subset := ra.cellG₁_subset
    cellG₂_subset := ra.cellG₂_subset
    cellF_nonempty := ra.cellF_nonempty
    cellG₁_nonempty := ra.cellG₁_nonempty
    cellG₂_nonempty := ra.cellG₂_nonempty
    cellH_nonempty := ra.cellH_nonempty
    cellF_ball := hcellF_ball
    cellG₁_ball := hcellG1_ball
    cellG₂_ball := hcellG2_ball
    cellH_support := ra.cellH_support
    cellF_separated := ra.cellF_separated
    cellG₁_separated := ra.cellG₁_separated
    cellG₂_separated := ra.cellG₂_separated
    cellF_frostman := hcellF_frostman
    cellF_frostman_margin := hcellF_frostman_margin
    cellG₁_frostman := hcellG1_frostman
    cellG₁_frostman_margin := hcellG1_frostman_margin
    cellG₂_frostman := hcellG2_frostman
    cellG₂_frostman_margin := hcellG2_frostman_margin
    first_line_nonconcentration := hline1
    first_line_nonconcentration_margin := hline1_margin
    second_line_nonconcentration := hline2
    second_line_nonconcentration_margin := hline2_margin
    uniform := hUniform
    quantitative_separation := ra.quantitative_separation
  }⟩

end Kakeya.Assouad
