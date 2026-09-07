module

/-
  Uniform RKP wrapper for all exponents u ∈ [t, 2].

  Key insight: `hP_upper` in `robust_kaufman_s_le_one` is unused. We provide
  `robust_kaufman_s_le_one_no_upper` (proof copied, hypothesis removed) and
  convert u-hypotheses to t-hypotheses for u ≥ t:
  - S-set: (δ,u,C)-set → (δ,t,C)-set when C ≥ 1 and P bounded
  - Lower bound: δ^(ρ-u) ≤ Ncover(P) → δ^(ρ-t) ≤ Ncover(P)
  - Upper bound: not needed

  Whiteprint node: uniform_rkp_wrapper
-/

public import MyLeanRepo.robust_kaufman_projection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace RobustKaufmanProjection.Dune

open RobustKaufmanProjection.EnergyAveraging
open RobustKaufmanProjection.RestrictionFrostman
open RobustKaufmanProjection.HausdorffContentToDeltaSet
open RobustKaufmanProjection.PerturbationGeneral
open RobustKaufmanProjection.GenericRefinement

open MeasureTheory Metric Set Finset Classical

abbrev Plane' := EuclideanSpace ℝ (Fin 2)

/-! ### S-set exponent weakening -/

/-- A (δ,u,C)-set with C ≥ 1, contained in a bounded set, is also a
    (δ,t,C)-set when u ≥ t. For r ≤ 1, r^u ≤ r^t; for r > 1, the bound
    is trivial since C * r^t ≥ 1. -/
lemma IsDeltaSSet.weaken_exponent {X : Type*} [PseudoMetricSpace X]
    {δ u t C : ℝ} {P : Set X}
    (h : IsDeltaSSet δ u C P)
    (htu : t ≤ u) (hC_one : 1 ≤ C) (ht_nonneg : 0 ≤ t) :
    IsDeltaSSet δ t C P := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, _, hcover⟩
  refine' ⟨hP_nonempty, hδ_pos, hC_pos, ht_nonneg, _⟩
  intro x r hr
  by_cases h_r_le_one : r ≤ 1
  · -- r ≤ 1: r^u ≤ r^t since u ≥ t and 0 ≤ r ≤ 1
    have h_r_nonneg : 0 ≤ r := by linarith [hδ_pos, hr]
    have h2 : ENNReal.ofReal r ≤ 1 := by exact_mod_cast h_r_le_one
    have h1 : (ENNReal.ofReal r) ^ u ≤ (ENNReal.ofReal r) ^ t :=
      ENNReal.rpow_le_rpow_of_exponent_ge h2 htu
    have h4 := hcover x r hr
    calc Ncover δ (P ∩ Metric.closedBall x r)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u * Ncover δ P := h4
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * Ncover δ P := by gcongr
  · -- r > 1: C * r^t ≥ 1, so RHS ≥ Ncover(P) ≥ Ncover(P ∩ B)
    have h_r_gt_one : 1 < r := by linarith
    have h6 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      have h61 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC_one
      simpa [ENNReal.ofReal_one] using h61
    have h8 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
      have h81 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (by linarith)
      simpa [ENNReal.ofReal_one] using h81
    have h9 : 0 ≤ t := ht_nonneg
    have h7 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ t := by
      have h10 : (1 : ENNReal) ^ t ≤ (ENNReal.ofReal r) ^ t := by gcongr
      have h11 : (1 : ENNReal) ^ t = (1 : ENNReal) := by simp
      rw [h11] at h10
      exact h10
    have h5 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t := by
      calc (1 : ENNReal)
        ≤ (1 : ENNReal) * (1 : ENNReal) := by simp
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t := by gcongr
    have h11 : (P ∩ Metric.closedBall x r) ⊆ P := by simp
    have h10 : Ncover δ (P ∩ Metric.closedBall x r) ≤ Ncover δ P := by
      dsimp only [Ncover]
      have h12 : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ.toNNReal P :=
        Metric.externalCoveringNumber_mono_set h11
      exact_mod_cast h12
    calc Ncover δ (P ∩ Metric.closedBall x r)
      ≤ Ncover δ P := h10
    _ ≤ (1 : ENNReal) * Ncover δ P := by simp
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * Ncover δ P := by
      gcongr <;> exact h5

/-! ### RKP without upper bound on P -/

/-- Version of `robust_kaufman_s_le_one` without the unused `hP_upper` hypothesis. -/
lemma robust_kaufman_s_le_one_no_upper
    (s t : ℝ)
    (hs : 0 < s) (hst : s < t) (ht : t ≤ 2) (h_s_le_one : s ≤ 1) :
    ∀ (ρ : ℝ), 0 < ρ → (12 : ℝ) * ρ < t - s →
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
        ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane) (directions : Set ℝ),
            InUnitSquare P →
            directions ⊆ Set.Icc (-1 : ℝ) 1 →
            IsDeltaSSet δ t (δ ^ (-ρ)) P →
            IsDeltaSSet δ s (δ ^ (-ρ)) directions →
            ENNReal.ofReal (δ ^ (ρ - t)) ≤ Ncover δ P →
            ENNReal.ofReal (δ ^ (ρ - s)) ≤ Ncover δ directions →
            Ncover δ directions ≤ ENNReal.ofReal (δ ^ (-s - ρ)) →
            ∃ goodDirections : Set ℝ,
              goodDirections ⊆ directions ∧
              Ncover δ directions ≤ 2 * Ncover δ goodDirections ∧
              ∀ σ ∈ goodDirections,
                ∀ P' : Set EuclideanPlane,
                  P' ⊆ P →
                  ENNReal.ofReal (δ ^ ρ) * Ncover δ P ≤ Ncover δ P' →
                  ∃ X : Set ℝ,
                    X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
                    IsDeltaSSet δ s (δ ^ (-12 * ρ)) X ∧
                    ENNReal.ofReal (δ ^ (12 * ρ - s)) ≤ Ncover δ X := by
  intro ρ hρ hAρ
  rcases e_ref_absorption s t ρ hs hst hρ with ⟨δ₀_abs, hδ₀_abs_pos, hδ₀_abs_le_one, h_abs⟩
  let C_sset_const : ℝ := (12 : ℝ) * (2 ^ s) * (2 ^ s + 1) * (3 : ℝ)^(s + 2) / 100
  have hC_sset_const_pos : 0 < C_sset_const := by positivity
  rcases RobustKaufmanProjection.Arithmetic.delta_pow_absorb_const C_sset_const (4 * ρ) hC_sset_const_pos (by positivity) with ⟨δ₀_sset, hδ₀_sset_pos, hδ₀_sset_le_one, h_sset_abs⟩
  let C_card : ℝ := 9
  let C_abs1 : ℝ := 49 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s) / 50
  let C_abs2 : ℝ := 882 * (2 : ℝ)^(2*s+4) * (3 : ℝ)^(2*s)
  have hC_card_pos : 0 < C_card := by norm_num
  have hC_abs1_pos : 0 < C_abs1 := by positivity
  have hC_abs2_pos : 0 < C_abs2 := by positivity
  have h_exp_card_pos : 0 < t - s + 10 * ρ := by linarith
  have h_exp4_pos : 0 < 4 * ρ := by positivity
  have h_exp22_pos : 0 < 22 * ρ := by positivity
  rcases RobustKaufmanProjection.Arithmetic.delta_pow_absorb_const C_card (t - s + 10 * ρ) hC_card_pos h_exp_card_pos with ⟨δ₁, hδ₁_pos, hδ₁_le_one, h_abs1⟩
  rcases RobustKaufmanProjection.Arithmetic.delta_pow_absorb_const C_abs1 (4 * ρ) hC_abs1_pos h_exp4_pos with ⟨δ₂, hδ₂_pos, hδ₂_le_one, h_abs2⟩
  rcases RobustKaufmanProjection.Arithmetic.delta_pow_absorb_const C_abs2 (22 * ρ) hC_abs2_pos h_exp22_pos with ⟨δ₃, hδ₃_pos, hδ₃_le_one, h_abs3⟩
  let δ₀ : ℝ := min (min (min (min (1 / 2) δ₀_abs) δ₀_sset) δ₁) δ₂
  let δ₀' : ℝ := min δ₀ δ₃
  have hδ₀'_pos : 0 < δ₀' := by positivity
  have hδ₀'_le_half : δ₀' ≤ 1 / 2 := by
    have h1 : δ₀' ≤ δ₀ := min_le_left _ _
    have h2a : δ₀ ≤ min (min (min (1 / 2) δ₀_abs) δ₀_sset) δ₁ := min_le_left _ _
    have h2 : δ₀ ≤ min (min (1 / 2) δ₀_abs) δ₀_sset := le_trans h2a (min_le_left _ _)
    have h3 : min (min (1 / 2) δ₀_abs) δ₀_sset ≤ min (1 / 2) δ₀_abs := min_le_left _ _
    have h4 : min (1 / 2) δ₀_abs ≤ 1 / 2 := min_le_left _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 h4))
  have hδ₀'_le_one : δ₀' ≤ 1 := by
    calc δ₀' ≤ (1 / 2 : ℝ) := hδ₀'_le_half
         _ ≤ 1 := by norm_num
  refine' ⟨δ₀', hδ₀'_pos, hδ₀'_le_one, _⟩
  intro δ hδ hδ_le₀ P directions hP_unit hdir_bounds hP_sset hdir_sset
        hP_lower hdir_lower hdir_upper
  have hδ_le_half : δ ≤ 1 / 2 := le_trans hδ_le₀ hδ₀'_le_half
  have hδ_le_abs : δ ≤ δ₀_abs := by
    have h1 : δ₀' ≤ δ₀ := min_le_left _ _
    have h2a : δ₀ ≤ min (min (min (1 / 2) δ₀_abs) δ₀_sset) δ₁ := min_le_left _ _
    have h2 : δ₀ ≤ min (min (1 / 2) δ₀_abs) δ₀_sset := le_trans h2a (min_le_left _ _)
    have h3 : min (min (1 / 2) δ₀_abs) δ₀_sset ≤ min (1 / 2) δ₀_abs := min_le_left _ _
    have h4 : min (1 / 2) δ₀_abs ≤ δ₀_abs := min_le_right _ _
    exact le_trans hδ_le₀ (le_trans h1 (le_trans h2 (le_trans h3 h4)))
  have hδ_le_sset : δ ≤ δ₀_sset := by
    have h1 : δ₀' ≤ δ₀ := min_le_left _ _
    have h2a : δ₀ ≤ min (min (min (1 / 2) δ₀_abs) δ₀_sset) δ₁ := min_le_left _ _
    have h2 : δ₀ ≤ min (min (1 / 2) δ₀_abs) δ₀_sset := le_trans h2a (min_le_left _ _)
    have h3 : min (min (1 / 2) δ₀_abs) δ₀_sset ≤ δ₀_sset := min_le_right _ _
    exact le_trans hδ_le₀ (le_trans h1 (le_trans h2 h3))
  have hδ_le1 : δ ≤ δ₁ := by
    have h1 : δ₀' ≤ δ₀ := min_le_left _ _
    have h2 : δ₀ ≤ δ₁ := by
      have h3 : δ₀ ≤ min (min (min (1 / 2) δ₀_abs) δ₀_sset) δ₁ := min_le_left _ _
      exact le_trans h3 (min_le_right _ _)
    exact le_trans hδ_le₀ (le_trans h1 h2)
  have hδ_le2 : δ ≤ δ₂ := by
    have h1 : δ₀' ≤ δ₀ := min_le_left _ _
    have h2 : δ₀ ≤ δ₂ := min_le_right _ _
    exact le_trans hδ_le₀ (le_trans h1 h2)
  have hδ_le3 : δ ≤ δ₃ := by
    have h1 : δ₀' ≤ δ₃ := min_le_right _ _
    exact le_trans hδ_le₀ h1
  set C_P : ℝ := δ ^ (-ρ) with hC_P_def
  set C_dir : ℝ := δ ^ (-ρ) with hC_dir_def
  have hC_P_pos : 0 < C_P := by positivity
  have hC_dir_pos : 0 < C_dir := by positivity
  have hP_bounded : Bornology.IsBounded P := InUnitSquare.bounded hP_unit
  have hdir_bounded : Bornology.IsBounded directions := by
    have h1 : directions ⊆ Set.Icc (-1 : ℝ) 1 := hdir_bounds
    have h2 : Bornology.IsBounded (Set.Icc (-1 : ℝ) 1) := by exact isBounded_Icc (-1) 1
    exact h2.subset h1
  have h_step2 := IsDeltaSSet.extract_plane hP_sset hP_bounded
  rcases h_step2 with ⟨S_P, hS_P_sub, hS_P_nonempty, hS_P_strict_sep, hS_P_sep, hS_P_cover, hS_P_ncover, hS_P_ball⟩
  have hdir_nonempty : directions.Nonempty := hdir_sset.1
  rcases ncover_witness_subset hδ hdir_bounded hdir_nonempty with ⟨R, hR_sub, hR_sep, hR_card⟩
  have hR_ball := direction_ball_growth_transfer hδ (by linarith) hC_dir_pos hdir_sset hR_sub hR_sep hR_card
  let μ : Measure Plane := uniformMeasure S_P
  letI : SFinite (Measure.count.restrict (S_P : Set Plane)) := sfinite_count_restrict_finset' S_P
  letI : SFinite μ := by
    dsimp only [μ, uniformMeasure]
    exact instSFiniteHSMulENNRealMeasure (↑(#S_P))⁻¹
  have h_denom_pos : 0 < 1 - (2 : ℝ)^(s-t) := by
    have h1 : (2 : ℝ)^(s-t) < (2 : ℝ)^(0 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      linarith
    have h2 : (2 : ℝ)^(s-t) < 1 := by simpa using h1
    linarith
  let M_plane : ℝ := 1 + (9 * C_P) * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t))
  have hM_plane_pos : 0 < M_plane := by
    dsimp only [M_plane]
    have h2 : 0 < (9 * C_P) * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)) := by positivity
    linarith
  have h_plane_energy : _root_.planeEnergy μ s ≤ ENNReal.ofReal M_plane :=
    finite_set_energy_bound_explicit hs hst hδ (show 0 < 9 * C_P by positivity) hS_P_nonempty hS_P_sep hS_P_ball
  have hS_subset_R : ∀ σ ∈ R, -1 ≤ σ ∧ σ ≤ 1 := by
    intro σ hσ
    have hσ_in_dir : σ ∈ directions := hR_sub hσ
    have h : σ ∈ Set.Icc (-1 : ℝ) 1 := hdir_bounds hσ_in_dir
    exact ⟨h.1, h.2⟩
  have hR_nonempty : R.Nonempty := by
    have h1 : 0 < Metric.externalCoveringNumber δ.toNNReal directions :=
      Metric.externalCoveringNumber_pos_iff.mpr hdir_nonempty
    have h1' : 0 < Ncover δ directions := by
      have h_pos : (0 : ENNReal) < (Metric.externalCoveringNumber δ.toNNReal directions : ENNReal) := by
        exact_mod_cast h1
      simpa [Ncover] using h_pos
    have h2 : 0 < (R.card : ENNReal) := by rw [hR_card]; exact h1'
    have h3 : 0 < R.card := by exact_mod_cast h2
    exact Finset.card_pos.mp h3
  let C_total : ℝ := C_dir * (4 : ℝ)^s * 3 / Real.log 2 + (4 : ℝ)^s
  have hμ_unit : ∀ᵐ (x : Plane) ∂μ, x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1 := by
    have hS_P_in_unit : ∀ x ∈ (S_P : Set Plane), x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      exact hP_unit (hS_P_sub hx)
    have h_ae : ∀ᵐ (x : Plane) ∂(Measure.count.restrict (S_P : Set Plane)), x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1 := by
      rw [MeasureTheory.ae_restrict_iff' (Finset.measurableSet S_P)]
      exact Filter.Eventually.of_forall hS_P_in_unit
    have h_def : μ = (S_P.card : ENNReal)⁻¹ • Measure.count.restrict (S_P : Set Plane) := by
      simp [μ, uniformMeasure] <;> rfl
    rw [h_def]
    exact Measure.ae_smul_measure h_ae ((S_P.card : ENNReal)⁻¹)
  have hμ_prob : μ Set.univ = 1 := by
    have h2 : μ Set.univ = (S_P.card : ENNReal)⁻¹ * (S_P.card : ENNReal) := by
      simp [μ, uniformMeasure] <;> rfl
    rw [h2]
    have h3 : (S_P.card : ENNReal) ≠ 0 := by exact_mod_cast hS_P_nonempty.card_pos.ne'
    exact ENNReal.inv_mul_cancel h3 ENNReal.coe_ne_top
  letI : IsProbabilityMeasure μ := ⟨hμ_prob⟩
  have h_avg_reg : (∑ σ ∈ R, projectedEnergyReg μ s δ σ) ≤
      ENNReal.ofReal (C_total * (R.card : ℝ) * Real.log (4 / δ)) * RobustKaufmanProjection.EnergyAveraging.planeEnergy μ s + ENNReal.ofReal (δ ^ (-s)) :=
    projected_energy_average_reg hδ (by linarith [hδ_le_half]) hs hS_subset_R hR_nonempty hR_ball hμ_unit
  let M : ℝ := C_total * Real.log (4 / δ) * M_plane
  have h_log_pos : 0 < Real.log (4 / δ) := by
    have h1 : 4 / δ > 1 := by
      have h2 : δ ≤ 1 / 2 := hδ_le_half
      have h3 : 4 / δ ≥ 8 := by
        calc 4 / δ ≥ 4 / (1 / 2 : ℝ) := by gcongr
             _ = 8 := by norm_num
      linarith
    exact Real.log_pos h1
  have hM_pos : 0 < M := by
    dsimp only [M]
    have hC_total_pos : 0 < C_total := by positivity
    positivity
  have hR_card_lower : (R.card : ℝ) ≥ δ ^ (ρ - s) := by
    have h1 : ENNReal.ofReal (δ ^ (ρ - s)) ≤ ENNReal.ofReal (R.card : ℝ) := by
      have h2 : ENNReal.ofReal (δ ^ (ρ - s)) ≤ (R.card : ENNReal) := by
        rw [hR_card] <;> exact hdir_lower
      simpa using h2
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h1
  have hM_lower : M ≥ δ ^ (-ρ) * (4 : ℝ)^s * 9 := by
    dsimp only [M, C_total, C_dir, M_plane]
    have h1 : C_total ≥ δ ^ (-ρ) * (4 : ℝ)^s * 3 / Real.log 2 := by
      dsimp only [C_total, C_dir]
      have h_pos : 0 ≤ (4 : ℝ)^s := by positivity
      linarith
    have h3 : Real.log (4 / δ) ≥ 3 * Real.log 2 := by
      have h4 : 4 / δ ≥ 8 := by
        calc 4 / δ ≥ 4 / (1 / 2 : ℝ) := by gcongr
             _ = 8 := by norm_num
      have h5 : Real.log (4 / δ) ≥ Real.log 8 := Real.log_le_log (by linarith) h4
      have h6 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow] <;> ring
      linarith
    have h7 : M_plane ≥ 1 := by
      dsimp only [M_plane]
      have h8 : 0 ≤ (9 * C_P) * (2 : ℝ)^s / (1 - (2 : ℝ)^(s-t)) := by positivity
      linarith
    calc C_total * Real.log (4 / δ) * M_plane
      ≥ (δ ^ (-ρ) * (4 : ℝ)^s * 3 / Real.log 2) * (3 * Real.log 2) * 1 := by gcongr
    _ = δ ^ (-ρ) * (4 : ℝ)^s * 9 := by
      have h8 : Real.log 2 ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
      field_simp [h8] <;> ring
  have h_extra_bound : δ ^ (-s) ≤ M * (R.card : ℝ) := by
    have h4 : (4 : ℝ)^s ≥ 1 := by
      have h5 : (1 : ℝ) ≤ (4 : ℝ) := by norm_num
      exact Real.one_le_rpow h5 hs.le
    have h6 : 0 ≤ δ ^ (-s) := by positivity
    have h7 : (1 : ℝ) ≤ (4 : ℝ)^s * 9 := by linarith
    have h8 : (1 : ℝ) * δ ^ (-s) ≤ ((4 : ℝ)^s * 9) * δ ^ (-s) := mul_le_mul_of_nonneg_right h7 h6
    have h9 : δ ^ (-s) ≤ (4 : ℝ)^s * 9 * δ ^ (-s) := by simpa using h8
    have h10 : (4 : ℝ)^s * 9 * δ ^ (-s) = (δ ^ (-ρ) * (4 : ℝ)^s * 9) * δ ^ (ρ - s) := by
      have h_rpow : δ ^ (-ρ) * δ ^ (ρ - s) = δ ^ (-s) := by
        rw [← Real.rpow_add hδ] <;> ring_nf
      calc (4 : ℝ)^s * 9 * δ ^ (-s)
        = (4 : ℝ)^s * 9 * (δ ^ (-ρ) * δ ^ (ρ - s)) := by rw [h_rpow]
      _ = (δ ^ (-ρ) * (4 : ℝ)^s * 9) * δ ^ (ρ - s) := by ring
    have h11 : δ ^ (-s) ≤ (δ ^ (-ρ) * (4 : ℝ)^s * 9) * δ ^ (ρ - s) := by
      rw [h10] at h9
      exact h9
    have h12 : (δ ^ (-ρ) * (4 : ℝ)^s * 9) * δ ^ (ρ - s) ≤ M * (R.card : ℝ) := by gcongr
    exact le_trans h11 h12
  have h_extra_ennreal : ENNReal.ofReal (δ ^ (-s)) ≤ ENNReal.ofReal M * (R.card : ENNReal) := by
    have h_posM : 0 ≤ M := by linarith [hM_pos]
    have h_posR : 0 ≤ (R.card : ℝ) := by positivity
    have h_eq : ENNReal.ofReal M * (R.card : ENNReal) = ENNReal.ofReal (M * (R.card : ℝ)) := by
      have h_card : (R.card : ENNReal) = ENNReal.ofReal (R.card : ℝ) := by simp
      rw [h_card]
      rw [← ENNReal.ofReal_mul h_posM]
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_extra_bound
  let M2 : ℝ := 2 * M
  have hM2_pos : 0 < M2 := by positivity
  have h_sum_reg : (∑ σ ∈ R, projectedEnergyReg μ s δ σ) ≤ ENNReal.ofReal M2 * (R.card : ENNReal) := by
    have h_plane_le : RobustKaufmanProjection.EnergyAveraging.planeEnergy μ s ≤ ENNReal.ofReal M_plane := by
      have h_eq : RobustKaufmanProjection.EnergyAveraging.planeEnergy μ s = _root_.planeEnergy μ s := by rfl
      rw [h_eq]
      exact h_plane_energy
    have h_first : ENNReal.ofReal (C_total * (R.card : ℝ) * Real.log (4 / δ)) * RobustKaufmanProjection.EnergyAveraging.planeEnergy μ s ≤ ENNReal.ofReal M * (R.card : ENNReal) := by
      have h_pos1 : 0 ≤ C_total * (R.card : ℝ) * Real.log (4 / δ) := by positivity
      have h_pos2 : 0 ≤ M_plane := by linarith [hM_plane_pos]
      have h_step1 : ENNReal.ofReal (C_total * (R.card : ℝ) * Real.log (4 / δ)) * RobustKaufmanProjection.EnergyAveraging.planeEnergy μ s ≤
          ENNReal.ofReal (C_total * (R.card : ℝ) * Real.log (4 / δ)) * ENNReal.ofReal M_plane :=
        mul_le_mul_of_nonneg_left h_plane_le (by positivity)
      have h_step2 : ENNReal.ofReal (C_total * (R.card : ℝ) * Real.log (4 / δ)) * ENNReal.ofReal M_plane =
          ENNReal.ofReal ((C_total * (R.card : ℝ) * Real.log (4 / δ)) * M_plane) := by
        rw [← ENNReal.ofReal_mul h_pos1]
      have h_mul : (C_total * (R.card : ℝ) * Real.log (4 / δ)) * M_plane = M * (R.card : ℝ) := by ring
      have h_step3 : ENNReal.ofReal ((C_total * (R.card : ℝ) * Real.log (4 / δ)) * M_plane) = ENNReal.ofReal (M * (R.card : ℝ)) := by
        rw [h_mul]
      have h_pos3 : 0 ≤ M := by linarith [hM_pos]
      have h_card : (R.card : ENNReal) = ENNReal.ofReal (R.card : ℝ) := by simp
      have h_step4 : ENNReal.ofReal (M * (R.card : ℝ)) = ENNReal.ofReal M * (R.card : ENNReal) := by
        have h_card2 : (R.card : ENNReal) = ENNReal.ofReal (R.card : ℝ) := by simp
        have h_posR : 0 ≤ (R.card : ℝ) := by positivity
        have h_eq1 : ENNReal.ofReal (M * (R.card : ℝ)) = ENNReal.ofReal M * ENNReal.ofReal (R.card : ℝ) := by
          rw [← ENNReal.ofReal_mul h_pos3]
        have h_eq2 : ENNReal.ofReal M * ENNReal.ofReal (R.card : ℝ) = ENNReal.ofReal M * (R.card : ENNReal) := by
          rw [← h_card2]
        exact Eq.trans h_eq1 h_eq2
      rw [h_step2, h_step3, h_step4] at h_step1
      exact h_step1
    calc (∑ σ ∈ R, projectedEnergyReg μ s δ σ)
      ≤ ENNReal.ofReal (C_total * (R.card : ℝ) * Real.log (4 / δ)) * RobustKaufmanProjection.EnergyAveraging.planeEnergy μ s + ENNReal.ofReal (δ ^ (-s)) := h_avg_reg
    _ ≤ ENNReal.ofReal M * (R.card : ENNReal) + ENNReal.ofReal M * (R.card : ENNReal) := by gcongr
    _ = 2 * (ENNReal.ofReal M * (R.card : ENNReal)) := by ring
    _ = ENNReal.ofReal M2 * (R.card : ENNReal) := by
      have h_pos4 : 0 ≤ M := by linarith [hM_pos]
      simp [M2, ENNReal.ofReal_mul h_pos4] <;> ring
  let E : ℝ → ENNReal := fun σ => projectedEnergyReg μ s δ σ
  have h_step7 := good_directions_factor2 hδ hM2_pos R hR_sub hR_sep hR_card.symm h_sum_reg
  rcases h_step7 with ⟨goodDirections, hgood_sub, hgood_cover, hgood_energy⟩
  refine' ⟨goodDirections, hgood_sub, hgood_cover, _⟩
  intro σ hσ_good P' hP'_sub hP'_density
  have h_step8a := refinement_cover_density
    hS_P_nonempty hS_P_sub hS_P_strict_sep hS_P_cover hP'_sub hP'_density hδ hρ
  rcases h_step8a with ⟨S_P', hS_P'_sub_SP, hS_P'_nonempty, hS_P'_near, hS_P'_density⟩
  let μ' : Measure Plane := uniformMeasure S_P'
  letI : SFinite (Measure.count.restrict (S_P' : Set Plane)) := sfinite_count_restrict_finset' S_P'
  have h_ratio : (S_P.card : ENNReal) / (S_P'.card : ENNReal) ≤ ENNReal.ofReal (9 * δ ^ (-ρ)) :=
    refinement_ratio_bound hS_P'_nonempty hS_P'_density hδ hρ
  have h_ref_reg : projectedEnergyReg μ' s δ σ ≤
      ((S_P.card : ENNReal) / (S_P'.card : ENNReal)) ^ 2 * projectedEnergyReg μ s δ σ := by
    have hK_meas : Measurable (fun p : Plane × Plane => projectedKernelReg s δ σ p.1 p.2) := by
      simp only [projectedKernelReg]
      have h_cont : Continuous (fun p : Plane × Plane => p.1 - p.2) := continuous_fst.sub continuous_snd
      have h_diag : MeasurableSet {p : Plane × Plane | p.1 = p.2} := by
        have h : {p : Plane × Plane | p.1 = p.2} = {p : Plane × Plane | p.1 - p.2 = 0} := by
          ext ⟨x, y⟩; simp [sub_eq_zero]
        rw [h]
        exact (isClosed_eq h_cont continuous_const).measurableSet
      exact Measurable.ite h_diag measurable_const (by fun_prop)
    exact RobustKaufmanProjection.GenericRefinement.finset_refinement_bound hS_P'_sub_SP hS_P'_nonempty hK_meas
  let E_ref : ℝ := 81 * δ ^ (-2 * ρ) * (4 * M)
  have hE_ref_pos : 0 < E_ref := by positivity
  have h_ref_reg2 : projectedEnergyReg μ' s δ σ ≤ ENNReal.ofReal E_ref := by
    have h1 : projectedEnergyReg μ' s δ σ ≤ ((S_P.card : ENNReal) / (S_P'.card : ENNReal)) ^ 2 * projectedEnergyReg μ s δ σ := h_ref_reg
    have h2 : ((S_P.card : ENNReal) / (S_P'.card : ENNReal)) ^ 2 * projectedEnergyReg μ s δ σ ≤ (ENNReal.ofReal (9 * δ ^ (-ρ))) ^ 2 * projectedEnergyReg μ s δ σ := by gcongr
    have h3 : (ENNReal.ofReal (9 * δ ^ (-ρ))) ^ 2 * projectedEnergyReg μ s δ σ = ENNReal.ofReal ((9 * δ ^ (-ρ)) ^ 2) * projectedEnergyReg μ s δ σ := by
      rw [← ENNReal.ofReal_pow (by positivity)] <;> ring
    have h4 : ENNReal.ofReal ((9 * δ ^ (-ρ)) ^ 2) * projectedEnergyReg μ s δ σ ≤ ENNReal.ofReal ((9 * δ ^ (-ρ)) ^ 2) * ENNReal.ofReal (2 * M2) := by
      apply mul_le_mul_of_nonneg_left
      · exact hgood_energy σ hσ_good
      · positivity
    have h5 : ENNReal.ofReal ((9 * δ ^ (-ρ)) ^ 2) * ENNReal.ofReal (2 * M2) = ENNReal.ofReal E_ref := by
      have h_M2_eq : (2 * M2) = 4 * M := by
        dsimp only [M2] <;> ring
      have h_real_eq : (9 * δ ^ (-ρ)) ^ 2 * (2 * M2) = E_ref := by
        dsimp only [E_ref]
        rw [h_M2_eq]
        have h : (9 * δ ^ (-ρ)) ^ 2 = 81 * δ ^ (-2 * ρ) := by
          have h1 : (9 * δ ^ (-ρ)) ^ 2 = 81 * ((δ ^ (-ρ)) * (δ ^ (-ρ))) := by
            rw [mul_pow, pow_two] <;> ring
          rw [h1]
          have h2 : (δ ^ (-ρ)) * (δ ^ (-ρ)) = δ ^ (-2 * ρ) := by
            have h3 : δ ^ ((-ρ) + (-ρ)) = δ ^ (-ρ) * δ ^ (-ρ) := Real.rpow_add hδ (-ρ) (-ρ)
            have h4 : (-ρ) + (-ρ) = -2 * ρ := by ring
            rw [h4] at h3
            exact h3.symm
          rw [h2] <;> ring
        rw [h] <;> ring
      rw [← ENNReal.ofReal_mul (by positivity), h_real_eq]
    calc
      projectedEnergyReg μ' s δ σ
        ≤ ((S_P.card : ENNReal) / (S_P'.card : ENNReal)) ^ 2 * projectedEnergyReg μ s δ σ := h1
      _ ≤ (ENNReal.ofReal (9 * δ ^ (-ρ))) ^ 2 * projectedEnergyReg μ s δ σ := h2
      _ = ENNReal.ofReal ((9 * δ ^ (-ρ)) ^ 2) * projectedEnergyReg μ s δ σ := h3
      _ ≤ ENNReal.ofReal ((9 * δ ^ (-ρ)) ^ 2) * ENNReal.ofReal (2 * M2) := h4
      _ = ENNReal.ofReal E_ref := h5
  have hσ_bounds : -1 ≤ σ ∧ σ ≤ 1 := by
    have hσ_in_dir : σ ∈ directions := hgood_sub hσ_good
    have h : σ ∈ Set.Icc (-1 : ℝ) 1 := hdir_bounds hσ_in_dir
    exact ⟨h.1, h.2⟩
  have hP'_unit' : P' ⊆ {p | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1} := by
    intro p hp; exact hP_unit (hP'_sub hp)
  have hE_poly : E_ref ≤ δ ^ (-8 * ρ) / 100 := by
    have h_abs' := h_abs δ hδ hδ_le_abs
    dsimp only [E_ref, M, C_total, M_plane, C_dir, C_P] at h_abs' ⊢
    exact h_abs'
  have hB_pos : (0 : ℝ) < 8 := by norm_num
  have hB_lt_A : (8 : ℝ) < 12 := by norm_num
  have h_sset_bound1 : C_sset_const ≤ δ ^ (-4 * ρ) := by
    have h := h_sset_abs δ hδ hδ_le_sset
    have h_eq : δ ^ (-(4 * ρ)) = δ ^ (-4 * ρ) := by ring_nf
    rw [h_eq] at h
    exact h
  have h_absorb_sset : (12 : ℝ) * (2 ^ s) * (2 ^ s + 1) * (3 : ℝ)^(s + 2) * E_ref ≤ δ ^ (-12 * ρ) := by
    have h1 : E_ref ≤ δ ^ (-8 * ρ) / 100 := hE_poly
    have h2 : (12 : ℝ) * (2 ^ s) * (2 ^ s + 1) * (3 : ℝ)^(s + 2) * E_ref ≤
        (12 : ℝ) * (2 ^ s) * (2 ^ s + 1) * (3 : ℝ)^(s + 2) * (δ ^ (-8 * ρ) / 100) := by gcongr
    have h3 : (12 : ℝ) * (2 ^ s) * (2 ^ s + 1) * (3 : ℝ)^(s + 2) * (δ ^ (-8 * ρ) / 100) =
        C_sset_const * δ ^ (-8 * ρ) := by
      dsimp only [C_sset_const] <;> ring
    rw [h3] at h2
    have h4 : C_sset_const * δ ^ (-8 * ρ) ≤ δ ^ (-4 * ρ) * δ ^ (-8 * ρ) := by gcongr
    have h5 : δ ^ (-4 * ρ) * δ ^ (-8 * ρ) = δ ^ (-12 * ρ) := by
      rw [← Real.rpow_add hδ, show (-4 * ρ) + (-8 * ρ) = -12 * ρ by ring]
    rw [h5] at h4
    linarith
  have h_absorb_ncover : δ ^ ((12 - 8) * ρ) ≤ (100 : ℝ) / 36 * (2 : ℝ)^(-s) := by
    have hδ_lt_one : δ < 1 := by linarith [hδ_le_half]
    have h1 : δ ^ (4 * ρ) < 1 := by
      have h2 : 0 < 4 * ρ := by positivity
      have h3 : δ ^ (4 * ρ) < 1 := Real.rpow_lt_one (by linarith) hδ_lt_one h2
      exact h3
    have h4 : (1 : ℝ) ≤ (100 : ℝ) / 36 * (2 : ℝ)^(-s) := by
      have h5 : s ≤ 1 := h_s_le_one
      have h6 : (2 : ℝ)^s ≤ 2 := by
        have h7 : (2 : ℝ)^s ≤ (2 : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
        simpa using h7
      have h8 : (2 : ℝ)^(-s) ≥ 1 / 2 := by
        have h9 : (2 : ℝ)^s ≤ 2 := h6
        have h10 : 0 < (2 : ℝ)^s := by positivity
        have h11 : (2 : ℝ)^(-s) = 1 / (2 : ℝ)^s := by
          rw [Real.rpow_neg (by positivity)] <;> simp
        rw [h11]
        gcongr
      linarith
    have h12 : (12 - 8) * ρ = 4 * ρ := by ring
    rw [h12]
    linarith
  have h_abs1' : (9 : ℝ) ≤ δ ^ (-(t - s + 10 * ρ)) := h_abs1 δ hδ hδ_le1
  have h_abs2' : C_abs1 ≤ δ ^ (-4 * ρ) := by
    have h_exp4 : δ ^ (-(4 * ρ)) = δ ^ (-4 * ρ) := by ring_nf
    have h := h_abs2 δ hδ hδ_le2
    rw [h_exp4] at h
    exact h
  have h_abs3' : C_abs2 ≤ δ ^ (-22 * ρ) := by
    have h_exp22 : δ ^ (-(22 * ρ)) = δ ^ (-22 * ρ) := by ring_nf
    have h := h_abs3 δ hδ hδ_le3
    rw [h_exp22] at h
    exact h
  rcases cardinality_and_absorption_bounds hs hst hρ hAρ h_s_le_one hδ hδ_le_half
      h_abs1' h_abs2' h_abs3' hS_P_ncover hP_lower hS_P'_density E_ref hE_poly hS_P'_nonempty
    with ⟨hS_card, h_absorb_sset, h_absorb_ncover⟩
  exact extract_delta_set_from_projected_energy hδ (by linarith) hs (by norm_num) hρ
    hS_P'_near hP'_unit' hσ_bounds hE_ref_pos h_ref_reg2
    hS_card h_absorb_sset h_absorb_ncover

end RobustKaufmanProjection.Dune

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open RobustKaufmanProjection.Dune

/-- The RKP conclusion at exponent u with threshold δ0.
    Matches rkp_bridge output type but with u instead of t. -/
abbrev RKPAtExponent (s u ε δ0 : ℝ) : Prop :=
  0 < δ0 ∧ δ0 ≤ 1 ∧
    ∀ (Δ : ℝ), 0 < Δ → Δ < 1 → Δ ≤ δ0 →
      ∀ (P : Set EuclideanPlane) (directions : Set ℝ),
        InUnitSquare P →
        directions ⊆ Set.Icc (-1 : ℝ) 1 →
        IsDeltaSSet Δ u (Real.rpow Δ (-48 * ε)) P →
        IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) directions →
        ENNReal.ofReal (Real.rpow Δ (48 * ε - u)) ≤ Ncover Δ P →
        Ncover Δ P ≤ ENNReal.ofReal (Real.rpow Δ (-u - 48 * ε)) →
        ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤ Ncover Δ directions →
        Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) →
        ∃ goodDirections : Set ℝ,
          goodDirections ⊆ directions ∧
          Ncover Δ directions ≤ 2 * Ncover Δ goodDirections ∧
          ∀ σ ∈ goodDirections,
            ∀ P' : Set EuclideanPlane, P' ⊆ P →
              ENNReal.ofReal (Real.rpow Δ (48 * ε)) * Ncover Δ P ≤ Ncover Δ P' →
              ∃ X : Set ℝ,
                X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
                IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
                ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ Ncover Δ X

/-- Uniform RKP wrapper: a single threshold δ0 works for all u ∈ [t, 2].

    Proof: call the no-upper-bound RKP theorem at t (worst case).
    For u ≥ t:
    - S-set exponent weakens: (δ,u,C)-set → (δ,t,C)-set when C ≥ 1
    - Lower bound improves: δ^(ρ-u) ≥ δ^(ρ-t)
    - Upper bound on P is not needed by the theorem
    - Directions hypotheses are at exponent s (unchanged)
-/
lemma uniform_rkp_wrapper
    (s t ε : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht : t ≤ 2)
    (hε_pos : 0 < ε) (hRKP_cond : 576 * ε < t - s) :
    ∃ (δ0_RKP : ℝ), 0 < δ0_RKP ∧
      ∀ (u : ℝ), t ≤ u → u ≤ 2 → RKPAtExponent s u ε δ0_RKP := by
  have h_s_le_one : s ≤ 1 := by linarith
  set ρ : ℝ := 48 * ε with hρ_def
  have hρ_pos : 0 < ρ := by positivity
  have h12ρ : (12 : ℝ) * ρ < t - s := by
    have h_eq : (12 : ℝ) * ρ = 576 * ε := by
      simp [hρ_def] <;> ring
    rw [h_eq]
    exact hRKP_cond
  have h_main := robust_kaufman_s_le_one_no_upper s t hs hst ht h_s_le_one
  rcases h_main ρ hρ_pos h12ρ with ⟨δ₀, hδ₀_pos, hδ₀_le_one, h_rkp_inner⟩
  have h_forall_u : ∀ (u : ℝ), t ≤ u → u ≤ 2 → RKPAtExponent s u ε δ₀ := by
    intro u htu hu2
    have h_body : ∀ (Δ : ℝ), 0 < Δ → Δ < 1 → Δ ≤ δ₀ →
        ∀ (P : Set EuclideanPlane) (directions : Set ℝ),
          InUnitSquare P →
          directions ⊆ Set.Icc (-1 : ℝ) 1 →
          IsDeltaSSet Δ u (Real.rpow Δ (-48 * ε)) P →
          IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) directions →
          ENNReal.ofReal (Real.rpow Δ (48 * ε - u)) ≤ Ncover Δ P →
          Ncover Δ P ≤ ENNReal.ofReal (Real.rpow Δ (-u - 48 * ε)) →
          ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤ Ncover Δ directions →
          Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) →
          ∃ goodDirections : Set ℝ,
            goodDirections ⊆ directions ∧
            Ncover Δ directions ≤ 2 * Ncover Δ goodDirections ∧
            ∀ σ ∈ goodDirections,
              ∀ P' : Set EuclideanPlane, P' ⊆ P →
                ENNReal.ofReal (Real.rpow Δ (48 * ε)) * Ncover Δ P ≤ Ncover Δ P' →
                ∃ X : Set ℝ,
                  X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
                  IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
                  ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ Ncover Δ X := by
      intro Δ hΔ_pos hΔ_lt_one hΔ_le
      intro P directions hP_unit hdir_bounds hP_sset_u hdir_sset
            hP_lower_u hP_upper_u hdir_lower hdir_upper_strong
      -- Convert S-set: u → t
      have hC_one : 1 ≤ Real.rpow Δ (-48 * ε) := by
        have h1 : -48 * ε ≤ 0 := by linarith
        have h2 : Real.rpow Δ (-48 * ε) ≥ Real.rpow Δ 0 :=
          Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h1
        have h3 : Real.rpow Δ 0 = 1 := by simp
        rw [h3] at h2
        exact h2
      have hP_sset_t : IsDeltaSSet Δ t (Real.rpow Δ (-48 * ε)) P :=
        RobustKaufmanProjection.Dune.IsDeltaSSet.weaken_exponent
          hP_sset_u htu hC_one (by linarith)
      -- Convert lower bound: δ^(ρ-u) ≤ Ncover(P) → δ^(ρ-t) ≤ Ncover(P)
      have h_exp_lower : (48 * ε - u) ≤ (48 * ε - t) := by linarith
      have h_rpow_lower : Real.rpow Δ (48 * ε - t) ≤ Real.rpow Δ (48 * ε - u) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h_exp_lower
      have hP_lower_t : ENNReal.ofReal (Real.rpow Δ (48 * ε - t)) ≤ Ncover Δ P :=
        calc ENNReal.ofReal (Real.rpow Δ (48 * ε - t))
          ≤ ENNReal.ofReal (Real.rpow Δ (48 * ε - u)) := by gcongr
        _ ≤ Ncover Δ P := hP_lower_u
      -- Convert directions upper bound: Δ^{-s-29ε} ≤ Δ^{-s-48ε}
      have h_exp_ineq : -s - 48 * ε ≤ -s - 29 * ε := by linarith
      have h_rpow_ineq : Real.rpow Δ (-s - 29 * ε) ≤ Real.rpow Δ (-s - 48 * ε) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h_exp_ineq
      have hdir_upper : Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 48 * ε)) := by
        calc Ncover Δ directions
          ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) := hdir_upper_strong
        _ ≤ ENNReal.ofReal (Real.rpow Δ (-s - 48 * ε)) := by gcongr
      -- Convert Real.rpow to ^ for the inner theorem
      have h_e1 : Real.rpow Δ (-48 * ε) = Δ ^ (-(48 * ε)) := by
        have h1 : (-48 * ε) = (-(48 * ε)) := by ring
        have h2 : Real.rpow Δ (-48 * ε) = Real.rpow Δ (-(48 * ε)) := by rw [h1]
        have h3 : Real.rpow Δ (-(48 * ε)) = Δ ^ (-(48 * ε)) := by rfl
        rw [h2, h3]
      have h_e2 : Real.rpow Δ (48 * ε - t) = Δ ^ (48 * ε - t) := by rfl
      have h_e4 : Real.rpow Δ (48 * ε - s) = Δ ^ (48 * ε - s) := by rfl
      have h_e5 : Real.rpow Δ (-s - 48 * ε) = Δ ^ (-s - 48 * ε) := by rfl
      have h_e7 : Δ ^ (-12 * (48 * ε)) = Real.rpow Δ (-576 * ε) := by
        have h1 : Δ ^ (-12 * (48 * ε)) = Real.rpow Δ (-12 * (48 * ε)) := by rfl
        have h2 : (-12 * (48 * ε)) = (-576 * ε) := by ring
        rw [h1, h2]
      have h_e8 : Δ ^ (12 * (48 * ε) - s) = Real.rpow Δ (576 * ε - s) := by
        have h1 : Δ ^ (12 * (48 * ε) - s) = Real.rpow Δ (12 * (48 * ε) - s) := by rfl
        have h2 : (12 * (48 * ε) - s) = (576 * ε - s) := by ring
        rw [h1, h2]
      -- Apply no-upper-bound theorem at t
      have h_result := h_rkp_inner (δ := Δ) hΔ_pos hΔ_le P directions hP_unit hdir_bounds
        (h_e1 ▸ hP_sset_t) (h_e1 ▸ hdir_sset)
        (by exact (congr_arg ENNReal.ofReal h_e2).symm ▸ hP_lower_t)
        (by exact (congr_arg ENNReal.ofReal h_e4).symm ▸ hdir_lower)
        (by exact (congr_arg ENNReal.ofReal h_e5).symm ▸ hdir_upper)
      rcases h_result with ⟨goodDirections, hgd_sub, hgd_cover, hgd_proj⟩
      refine' ⟨goodDirections, hgd_sub, hgd_cover, _⟩
      intro σ hσ P' hP'_sub hcover
      have h1 := hgd_proj σ hσ P' hP'_sub hcover
      rcases h1 with ⟨X, hX_sub, hX_sset, hX_lower⟩
      have hX_sset' : IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X := h_e7 ▸ hX_sset
      have hX_lower' : ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ Ncover Δ X :=
        (congr_arg ENNReal.ofReal h_e8) ▸ hX_lower
      exact ⟨X, hX_sub, hX_sset', hX_lower'⟩
    exact ⟨hδ₀_pos, hδ₀_le_one, h_body⟩
  exact ⟨δ₀, hδ₀_pos, h_forall_u⟩

end DirecretisedFurstenbergEstimate.AppendixA
