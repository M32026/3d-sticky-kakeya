import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjection

/-!
# Fiber-output form of the Kaufman projection theorem

This module keeps the projection lower bound on the selected incidence fiber.
That form is needed before transporting the projection to the WZ1
dot-difference set.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Metric

private def fiber (H : Finset (Point2 × Point2)) (θ : Point2) : Finset Point2 :=
  (H.filter (fun h => h.1 = θ)).image (fun h => h.2)

/-- Kaufman projection theorem with the covering bound on the selected incidence fiber. -/
theorem kaufman_projection_fiber
    {F Λ : DiscreteSet 2} {δ C d α β γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ_lt_alpha : γ < α) (hγ_lt_beta : γ < β)
    (hC : 0 ≤ C) (hd_pos : 0 < d)
    (hF_frost : F.IsFrostman δ α (ENNReal.ofReal C))
    (hΛ_frost : Λ.IsFrostman δ β (ENNReal.ofReal C))
    (hF_sep : F.IsDeltaSeparated δ)
    (hΛ_sep : Λ.IsDeltaSeparated δ)
    (hF_ball : F.IsInUnitBall)
    (hunit : ∀ θ ∈ Λ, ‖θ‖ = 1)
    (H : Finset (Point2 × Point2))
    (hH_sub : ∀ h ∈ H, h.1 ∈ Λ ∧ h.2 ∈ F)
    (h_dense : ∀ θ ∈ Λ, (fiber H θ).card ≥ d * F.card)
    (hneF : F.Nonempty) (hΛ_nonempty : Λ.Nonempty) :
    ∃ (θ : Point2), θ ∈ Λ ∧
      Metric.externalCoveringNumber (Real.toNNReal δ)
        (inner ℝ θ '' (fiber H θ : Set Point2)) ≥
      ENNReal.ofReal
          (d ^ 2 /
            (2 * kaufman_total_const (max 1 C) α β γ * (2 : ℝ) ^ γ)) *
        Kakeya.realRpowENN δ (-γ) := by
  classical
  have hC_pos : 0 < C := by
    by_contra h
    have hC0 : C = 0 := by linarith
    obtain ⟨θ, hθ⟩ := hΛ_nonempty
    have h1 : ((Λ.filter (fun y => dist y θ ≤ δ)).card : ℝ) ≤ C * δ^β * (Λ.card : ℝ) :=
      frostman_real_bound hδ hC hΛ_frost (by linarith) hδ_le_one
    have h2 : θ ∈ Λ.filter (fun y => dist y θ ≤ δ) := by
      simp only [Finset.mem_filter]
      exact ⟨hθ, by simp [hδ.le]⟩
    have h3 : 0 < (Λ.filter (fun y => dist y θ ≤ δ)).card :=
      Finset.card_pos.mpr ⟨θ, h2⟩
    rw [hC0] at h1
    have h4 : ((Λ.filter (fun y => dist y θ ≤ δ)).card : ℝ) ≤ 0 := by
      simpa using h1
    have h5 : 0 < ((Λ.filter (fun y => dist y θ ≤ δ)).card : ℝ) := by
      exact_mod_cast h3
    linarith

  let C' : ℝ := max 1 C
  have hC'_ge_one : 1 ≤ C' := le_max_left _ _
  have hC'_pos : 0 < C' := by linarith
  have hC_le_C' : C ≤ C' := le_max_right _ _
  have h_ofReal_mono : ENNReal.ofReal C ≤ ENNReal.ofReal C' :=
    ENNReal.ofReal_le_ofReal hC_le_C'
  have hF_frost' : F.IsFrostman δ α (ENNReal.ofReal C') := by
    intro x r hδr hr1
    have h_orig := hF_frost x r hδr hr1
    have h_mono : ENNReal.ofReal C * Kakeya.realRpowENN r α * F.enncard ≤
        ENNReal.ofReal C' * Kakeya.realRpowENN r α * F.enncard := by
      gcongr
    exact h_orig.trans h_mono
  have hΛ_frost' : Λ.IsFrostman δ β (ENNReal.ofReal C') := by
    intro x r hδr hr1
    have h_orig := hΛ_frost x r hδr hr1
    have h_mono : ENNReal.ofReal C * Kakeya.realRpowENN r β * Λ.enncard ≤
        ENNReal.ofReal C' * Kakeya.realRpowENN r β * Λ.enncard := by
      gcongr
    exact h_orig.trans h_mono

  let K_const : ℝ := kaufman_total_const C' α β γ
  have hK_const_pos : 0 < K_const := by
    dsimp only [K_const, kaufman_total_const]
    have hK_ang_pos : 0 < kaufman_K_ang β γ := by
      dsimp only [kaufman_K_ang]
      have h1 : 0 < (Real.sqrt 2)^β := by positivity
      have h2 : 0 < (2 : ℝ)^γ := by positivity
      have h3 : 0 < (1 : ℝ) - (2 : ℝ)^(-(β - γ)) := by
        have h4 : 0 < β - γ := by linarith
        have h5 : 1 < (2 : ℝ)^(β - γ) := Real.one_lt_rpow (by norm_num) h4
        have h6 : (2 : ℝ)^(-(β - γ)) = ((2 : ℝ)^(β - γ))⁻¹ := by
          rw [Real.rpow_neg (by norm_num)] <;> field_simp
        rw [h6]
        have h7 : 0 < (2 : ℝ)^(β - γ) := by positivity
        have h8 : ((2 : ℝ)^(β - γ))⁻¹ < 1 := by
          have h9 : 1 / ((2 : ℝ)^(β - γ)) < 1 := by
            apply (div_lt_one h7).mpr
            exact h5
          simpa [one_div] using h9
        linarith
      positivity
    have hK_frost0_pos : 0 < kaufman_K_frost0 α γ := by
      dsimp only [kaufman_K_frost0]
      have h1 : 0 < (2 : ℝ)^(α - γ) - 1 := by
        have h2 : 0 < α - γ := by linarith
        have h3 : 1 < (2 : ℝ)^(α - γ) := Real.one_lt_rpow (by norm_num) h2
        linarith
      positivity
    have h4 : 0 < C' + kaufman_K_ang β γ * kaufman_K_frost0 α γ * (1 + C') +
        kaufman_K_ang β γ := by
      positivity
    exact mul_pos h4 hC'_pos

  have h_total_energy :
      ∑ θ ∈ Λ, ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ,
          (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) ≤
      K_const * (F.card : ℝ)^2 * (Λ.card : ℝ) :=
    projection_energy_total hδ hδ_le_one hα hβ hγ hγ_lt_alpha hγ_lt_beta
      hC'_pos.le hC'_ge_one hF_frost' hΛ_frost' hF_sep hΛ_sep hF_ball hunit hneF
      hΛ_nonempty H hH_sub

  let E_total := K_const * (F.card : ℝ)^2 * (Λ.card : ℝ)
  let E (θ : Point2) : ℝ :=
    ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ,
      (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ)
  have hE_nonneg : ∀ θ ∈ Λ, 0 ≤ E θ := by
    intro θ _
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    positivity
  have h_sum : ∑ θ ∈ Λ, E θ ≤ E_total := h_total_energy
  rcases markov_good_directions E hE_nonneg h_sum hΛ_nonempty with
    ⟨Λ_good, hΛg_sub, hΛg_card, hΛg_energy⟩
  have hΛg_nonempty : Λ_good.Nonempty := by
    by_contra h
    have h_empty : Λ_good = ∅ := by simpa using h
    rw [h_empty] at hΛg_card
    have h_pos : (Λ.card : ℝ) > 0 := by
      exact_mod_cast hΛ_nonempty.card_pos
    have h_cont : (0 : ℝ) ≥ (Λ.card : ℝ) / 2 := by
      simpa using hΛg_card
    linarith
  let θ : Point2 := Classical.choose hΛg_nonempty
  have hθ_good : θ ∈ Λ_good := Classical.choose_spec hΛg_nonempty
  have hθ_in_Λ : θ ∈ Λ := hΛg_sub hθ_good
  have hE_θ : E θ ≤ 2 * E_total / (Λ.card : ℝ) := hΛg_energy θ hθ_good
  have h_dense_θ : (fiber H θ).card ≥ d * F.card := h_dense θ hθ_in_Λ
  have h_fiber_nonempty : (fiber H θ).Nonempty := by
    have h12 : ((fiber H θ).card : ℝ) ≥ d * (F.card : ℝ) := by
      exact_mod_cast h_dense_θ
    have h13 : 0 < d * (F.card : ℝ) :=
      mul_pos hd_pos (by exact_mod_cast hneF.card_pos)
    have h14 : 0 < ((fiber H θ).card : ℝ) := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast h14)

  have hEθ_pos : 0 < E θ := by
    rcases h_fiber_nonempty with ⟨x, hx⟩
    let g' : Point2 → Point2 → ℝ := fun x' y =>
      (max (dist (inner ℝ θ x') (inner ℝ θ y)) δ)^(-γ)
    have hg_nonneg : ∀ x' ∈ fiber H θ, 0 ≤ ∑ y ∈ fiber H θ, g' x' y := by
      intro x' _
      apply Finset.sum_nonneg
      intro y _
      positivity
    have h4 : 0 < g' x x := by
      dsimp only [g']
      have h5 : dist (inner ℝ θ x) (inner ℝ θ x) = 0 := by simp
      rw [h5]
      have h6 : max (0 : ℝ) δ = δ := by rw [max_eq_right] <;> linarith
      rw [h6]
      exact Real.rpow_pos_of_pos hδ _
    have h5 : g' x x ≤ ∑ y ∈ fiber H θ, g' x y :=
      Finset.single_le_sum (fun y _ => by positivity) hx
    have h6 : 0 < ∑ y ∈ fiber H θ, g' x y := h4.trans_le h5
    have h7 : (∑ y ∈ fiber H θ, g' x y) ≤ E θ :=
      Finset.single_le_sum hg_nonneg hx
    exact h6.trans_le h7
  have hE_θ_bound : E θ ≤ 2 * K_const * (F.card : ℝ)^2 := by
    have hΛ_pos : 0 < (Λ.card : ℝ) := by
      exact_mod_cast hΛ_nonempty.card_pos
    have h : 2 * E_total / (Λ.card : ℝ) = 2 * K_const * (F.card : ℝ)^2 := by
      dsimp only [E_total]
      field_simp [hΛ_pos.ne'] <;> ring
    rw [h] at hE_θ
    exact hE_θ

  have h_covering :
      Metric.externalCoveringNumber (Real.toNNReal δ)
          (inner ℝ θ '' (fiber H θ : Set Point2)) ≥
      ENNReal.ofReal (((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)) :=
    projected_energy_to_covering (fiber H θ) (inner ℝ θ) hδ hγ (by positivity)
      (le_refl (E θ))

  have h_main_real : ((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ) ≥
      d^2 / (2 * K_const * (2 : ℝ)^γ) * δ^(-γ) := by
    have h1 : (E θ) ≤ 2 * K_const * (F.card : ℝ)^2 := hE_θ_bound
    have h2 : ((fiber H θ).card : ℝ) ≥ d * (F.card : ℝ) := by
      exact_mod_cast h_dense_θ
    have h3 : 0 < (E θ) * (2 * δ)^γ := mul_pos hEθ_pos (by positivity)
    have h4 : 0 < d * (F.card : ℝ) :=
      mul_pos hd_pos (by exact_mod_cast hneF.card_pos)
    have h5 : 0 < (2 * K_const * (F.card : ℝ)^2) * (2 * δ)^γ := by
      positivity
    have h6 : (2 * δ)^γ = (2 : ℝ)^γ * δ^γ := by
      rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
    calc
      ((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)
          ≥ (d * (F.card : ℝ))^2 / ((E θ) * (2 * δ)^γ) := by
            gcongr
      _ ≥ (d * (F.card : ℝ))^2 /
          ((2 * K_const * (F.card : ℝ)^2) * (2 * δ)^γ) := by
            have h_denom_le : (E θ) * (2 * δ)^γ ≤
                (2 * K_const * (F.card : ℝ)^2) * (2 * δ)^γ := by
              gcongr
            have h_num_pos : 0 ≤ (d * (F.card : ℝ))^2 := by positivity
            exact div_le_div_of_nonneg_left h_num_pos h3 h_denom_le
      _ = d^2 / (2 * K_const * (2 : ℝ)^γ) * δ^(-γ) := by
        rw [h6]
        have hF2_ne : (F.card : ℝ)^2 ≠ 0 := by positivity
        have hδγ_ne : δ ^ γ ≠ 0 := by positivity
        have h2γ_ne : (2 : ℝ)^γ ≠ 0 := by positivity
        have hK_ne : K_const ≠ 0 := hK_const_pos.ne'
        have h9 : δ^(-γ) = (δ^γ)⁻¹ := by
          rw [Real.rpow_neg hδ.le] <;> field_simp
        have h_goal : (d * (F.card : ℝ))^2 /
              ((2 * K_const * (F.card : ℝ)^2) * ((2 : ℝ)^γ * δ^γ)) =
            d^2 / (2 * K_const * (2 : ℝ)^γ) * (δ^γ)⁻¹ := by
          calc
            (d * (F.card : ℝ))^2 /
                ((2 * K_const * (F.card : ℝ)^2) * ((2 : ℝ)^γ * δ^γ)) =
                d^2 * (F.card : ℝ)^2 /
                  (2 * K_const * (F.card : ℝ)^2 * (2 : ℝ)^γ * δ^γ) := by
                    ring
            _ = d^2 / (2 * K_const * (2 : ℝ)^γ * δ^γ) := by
              field_simp [hF2_ne, hK_ne, h2γ_ne, hδγ_ne] <;> ring
            _ = d^2 / (2 * K_const * (2 : ℝ)^γ) * (δ^γ)⁻¹ := by
              field_simp [hδγ_ne] <;> ring
        rw [h_goal, h9]

  let C_raw : ENNReal := ENNReal.ofReal (d^2 / (2 * K_const * (2 : ℝ)^γ))
  have h_raw_bound : Metric.externalCoveringNumber (Real.toNNReal δ)
      (inner ℝ θ '' (fiber H θ : Set Point2)) ≥
      C_raw * Kakeya.realRpowENN δ (-γ) := by
    have h1 : ENNReal.ofReal
          (((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)) ≥
        C_raw * Kakeya.realRpowENN δ (-γ) := by
      dsimp only [C_raw]
      have h2 : Kakeya.realRpowENN δ (-γ) = ENNReal.ofReal (δ^(-γ)) := by
        simp [Kakeya.realRpowENN] <;> rfl
      rw [h2]
      have h_pos1 : 0 ≤ d^2 / (2 * K_const * (2 : ℝ)^γ) := by positivity
      have h3 : ENNReal.ofReal (d^2 / (2 * K_const * (2 : ℝ)^γ)) *
            ENNReal.ofReal (δ^(-γ)) =
          ENNReal.ofReal ((d^2 / (2 * K_const * (2 : ℝ)^γ)) * δ^(-γ)) := by
        have h4 : ENNReal.ofReal
              ((d^2 / (2 * K_const * (2 : ℝ)^γ)) * δ^(-γ)) =
            ENNReal.ofReal (d^2 / (2 * K_const * (2 : ℝ)^γ)) *
              ENNReal.ofReal (δ^(-γ)) :=
          ENNReal.ofReal_mul
            (p := d^2 / (2 * K_const * (2 : ℝ)^γ)) (q := δ^(-γ)) h_pos1
        exact h4.symm
      rw [h3]
      exact ENNReal.ofReal_le_ofReal h_main_real
    exact h1.trans h_covering

  refine ⟨θ, hθ_in_Λ, ?_⟩
  simpa [C_raw, K_const, C'] using h_raw_bound

end Kakeya.Assouad
