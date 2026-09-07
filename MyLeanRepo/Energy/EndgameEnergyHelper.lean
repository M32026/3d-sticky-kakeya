module

/-
Helper lemma for Endgame v3 energy integration.

Encapsulates the relative and absolute projected energy bounds in a single
lemma with all arguments explicit, so the large endgame theorem can call it
without triggering context-induced type-inference timeouts.
-/

public import MyLeanRepo.Energy.RieszEnergyMonotonicity
public import MyLeanRepo.Energy.RelativeEnergyBound
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Finset

namespace ProductLikeIncidence.ProductReduction

/-- Specialized wrapper for Endgame v3: given uniform measures μE on E and
    μE3 on E3fin ⊆ E with retention bound, return relative and absolute
    projected energy bounds for three directions θ1, θ2, θ3. -/
lemma endgame_projected_energy_bounds
    (δ κ0 rho_sel q_bad : ℝ)
    (hδ_pos : 0 < δ)
    (hκ0_pos : 0 < κ0)
    (hrho_sel_pos : 0 < rho_sel)
    (hq_bad_pos : 0 < q_bad)
    (E E3fin : Finset (EuclideanSpace ℝ (Fin 2)))
    (hE3_sub : E3fin ⊆ E)
    (hE3_nonempty : E3fin.Nonempty)
    (μE μE3 : Measure (EuclideanSpace ℝ (Fin 2)))
    (hμE : μE = uniformMeasureOn E)
    (hμE3 : μE3 = uniformMeasureOn E3fin)
    (h_retention : (E3fin.card : ENNReal) ≥ ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal))
    (θ1 θ2 θ3 : ℝ)
    (h_energy_dirs : ∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE) ≤
        ENNReal.ofReal (δ ^ (-q_bad))) :
    (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-6 * rho_sel)) *
          robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
            (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE)) ∧
    (∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
        ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) := by
  have h_pos3 : 0 ≤ δ ^ (3 * rho_sel) := Real.rpow_nonneg hδ_pos.le (3 * rho_sel)
  have hE_coe : (E.card : ENNReal) = ENNReal.ofReal (E.card : ℝ) := by simp
  have h_mul : ENNReal.ofReal (δ ^ (3 * rho_sel)) * (E.card : ENNReal) =
      ENNReal.ofReal (δ ^ (3 * rho_sel) * (E.card : ℝ)) := by
    rw [hE_coe, ENNReal.ofReal_mul h_pos3]
  have h_retention_real : (E3fin.card : ℝ) ≥ δ ^ (3 * rho_sel) * (E.card : ℝ) := by
    rw [h_mul] at h_retention
    exact_mod_cast h_retention
  have hc0 : Continuous (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0) := by exact PiLp.continuous_apply 2 (fun x => ℝ) 0
  have hc1 : Continuous (fun (p : EuclideanSpace ℝ (Fin 2)) => p 1) := by exact PiLp.continuous_apply 2 (fun x => ℝ) 1
  have h_cont : ∀ (θ : ℝ), Continuous (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) := by
    intro θ
    have hcθ : Continuous (fun (_ : EuclideanSpace ℝ (Fin 2)) => θ) := continuous_const
    exact hc0.mul hcθ |>.add hc1
  have h_meas : ∀ (θ : ℝ), Measurable (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) := by
    intro θ
    exact (h_cont θ).measurable
  have h_rel : ∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-6 * rho_sel)) *
        robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE) := by
    intro θ hθ
    have h_main := rieszEnergy_subset_uniform_delta_bound
      (α := EuclideanSpace ℝ (Fin 2)) (β := ℝ)
      (δ := δ) (ε := rho_sel) (α_exp := 2 * κ0)
      hδ_pos E E3fin hE3_sub hE3_nonempty
      (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) (h_meas θ) hrho_sel_pos h_retention_real
    rw [← hμE3, ← hμE] at h_main
    simpa using h_main
  have h_abs : ∀ θ ∈ ({θ1, θ2, θ3} : Set ℝ),
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))) := by
    intro θ hθ
    have h_abs_E : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) (uniformMeasureOn E)) ≤
        ENNReal.ofReal (δ ^ (-q_bad)) := by
      have h := h_energy_dirs θ hθ
      rw [hμE] at h
      exact h
    have h_main := absolute_subset_energy_bound (κ0 := κ0) hδ_pos hκ0_pos hrho_sel_pos hq_bad_pos
      (E := E) (E3fin := E3fin) hE3_sub hE3_nonempty
      (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ + p 1) (h_meas θ) h_retention h_abs_E
    rw [← hμE3] at h_main
    simpa using h_main
  exact ⟨h_rel, h_abs⟩

/-- Coordinate energy bounds for Endgame v3: given absolute projected energy
    bounds at θ1 and θ2, and separated directions, return bounds for the
    projective coordinates b3·π_θ2 and a3·π_θ1. -/
lemma endgame_coordinate_energy_bounds
    (δ κ0 rho_sel rho_sep q_bad : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hκ0_pos : 0 < κ0)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    (hrho_sep_le_one : rho_sep ≤ 1)
    (hq_bad_pos : 0 < q_bad)
    (μE3 : Measure (EuclideanSpace ℝ (Fin 2)))
    [SFinite μE3]
    (θ1 θ2 θ3 : ℝ)
    (hθ1_in : θ1 ∈ Set.Icc (0 : ℝ) 1)
    (hθ2_in : θ2 ∈ Set.Icc (0 : ℝ) 1)
    (hθ3_in : θ3 ∈ Set.Icc (0 : ℝ) 1)
    (h_ord13 : θ1 < θ3)
    (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ δ ^ rho_sep)
    (h_sep23 : |θ2 - θ3| ≥ δ ^ rho_sep)
    (h_abs_E2 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ2 + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel))))
    (h_abs_E1 : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) => p 0 * θ1 + p 1) μE3) ≤
      ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel)))) :
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1)) μE3) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) ∧
    robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun (p : EuclideanSpace ℝ (Fin 2)) =>
        ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1)) μE3) ≤
    ENNReal.ofReal (δ ^ (-(q_bad + 6 * rho_sel + 2 * κ0 * rho_sep))) := by
  have h_b3 := coordinate_energy_b3_bound hδ_pos hδ_lt_one hκ0_pos
    hrho_sel_pos hrho_sep_pos hrho_sep_le_one hq_bad_pos
    (hθ1_in := hθ1_in) (hθ2_in := hθ2_in) (hθ3_in := hθ3_in)
    h_ord13 h_ord32 h_sep13 h_sep23 h_abs_E2 h_abs_E1
  have h_a3 := coordinate_energy_a3_bound hδ_pos hδ_lt_one hκ0_pos
    hrho_sel_pos hrho_sep_pos hrho_sep_le_one hq_bad_pos
    (hθ1_in := hθ1_in) (hθ2_in := hθ2_in) (hθ3_in := hθ3_in)
    h_ord13 h_ord32 h_sep13 h_sep23 h_abs_E2 h_abs_E1
  exact ⟨h_b3, h_a3⟩

end ProductLikeIncidence.ProductReduction
