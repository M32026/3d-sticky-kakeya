module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.CoarsePhaseData
public import MyLeanRepo.InductionOnScales.CoarsePhaseHelpers
public import MyLeanRepo.InductionOnScales.MinimalCover
public import MyLeanRepo.InductionOnScales.UniformFibers
public import MyLeanRepo.InductionOnScales.FiberBounds
public import MyLeanRepo.InductionOnScales.TQLocal
public import MyLeanRepo.InductionOnScales.TrimFamilies
public import MyLeanRepo.InductionOnScales.NiceConfigHelpers
public import MyLeanRepo.InductionOnScales.FinePhaseAssembly
public import MyLeanRepo.InductionOnScales.CardinalityPhase
public import MyLeanRepo.InductionOnScales.PointSelection
public import MyLeanRepo.InductionOnScales.PerQUniformizeFine
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.MinimalCover
public import MyLeanRepo.InductionOnScales.FiberUniformizationBridge
public import MyLeanRepo.InductionOnScales.CardinalityFinal
public import MyLeanRepo.InductionOnScales.GeometricBounds
public import MyLeanRepo.InductionOnScales.KPolyBound
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Estimate3Bridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Induction Step v3 — Per-Q Coarse Phase Restructuring

Runs the coarse phase independently per coarse square Q, resolving the SSet gap.

## Proof order
1. Per-Q coarse phase → coarseTubes_Q, C₂_Q, H_Q, retained_Q
2. Size-band pigeonhole on |coarseTubes_Q| → QSet', MΔ
3. Trim each coarseTubes_Q to MΔ tubes → trimmedFamily Q
4. Build coarseConfig from trimmedFamily
5. Define candRet p = retained_Q p filtered to coarseAnc ∈ trimmedFamily Q
6. Containment (5.3) is automatic
7-14. SORRY: retention, point selection, uniformization, fine/cardinality phases
-/

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 500000

noncomputable section

namespace InductionOnScales

/-- Structure to hold per-Q coarse phase data, used internally in v3. -/
structure PerQCoarseData (n m : ℕ) (s C₁ : ℝ) (M : ℕ)
    (config : NiceConfiguration n s C₁ M) (hnm : m ≤ n)
    (Q : DyadicSquare m) where
  K_Q : ℝ
  coarseTubes_Q : Finset (DyadicTube m)
  C₂_Q : ℝ
  H_Q : ℝ
  hH_Q : 1 ≤ H_Q
  retained_Q : DyadicSquare n → Finset (DyadicTube n)
  h_sset : IsFiniteTubeSSet s C₂_Q coarseTubes_Q
  h_C₂_le : C₂_Q ≤ K_Q * C₁
  h_C₁_le : C₁ ≤ K_Q * C₂_Q
  h_card_upper : H_Q * (coarseTubes_Q.card : ℝ) ≤ K_Q * (M : ℝ) *
    ((config.points.filter (fun p => squareContained hnm p Q)).card : ℝ)
  h_card_lower : (M : ℝ) *
    ((config.points.filter (fun p => squareContained hnm p Q)).card : ℝ) ≤
    K_Q * H_Q * (coarseTubes_Q.card : ℝ)
  h_popularity : ∀ U ∈ coarseTubes_Q,
    H_Q ≤ ∑ p ∈ (config.points.filter (fun p => squareContained hnm p Q)),
      (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ)
  h_preimage : ∀ U ∈ coarseTubes_Q,
    ∃ (p : DyadicSquare n) (hp : p ∈ config.points) (hsc : squareContained hnm p Q)
      (T : DyadicTube n), T ∈ config.tubeFamily p hp ∧ coarseAnc hnm T = U
  h_retained_sub : ∀ (p : DyadicSquare n) (hp : p ∈ config.points.filter (fun p => squareContained hnm p Q)),
    retained_Q p ⊆ config.tubeFamily p ((Finset.mem_filter.mp hp).1)
  h_retained_contain : ∀ p ∈ config.points.filter (fun p => squareContained hnm p Q),
    ∀ T ∈ retained_Q p, T.toSet ⊆ (coarseAnc hnm T).toSet
  h_K_eq : K_Q = 32 * ((Nat.log 2 M : ℝ) + 2) *
    ((Nat.log 2 ((config.points.filter (fun p => squareContained hnm p Q)).card * M) : ℝ) + 2)
  h_C₂_eq : C₂_Q = K_Q * C₁

/-- Numeric inequalities for the induction step's K factors, extracted to keep
the main theorem's context small and avoid elaborator timeouts. -/
lemma induction_step_K_factors
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (M : ℕ) (hM : 0 < M)
    (K_Qmax : ℝ) (hK_Qmax_pos : 0 < K_Qmax) (hK_Qmax_one : 1 ≤ K_Qmax)
    (L_size : ℕ) (hL_size_pos : 0 < L_size) (hL_size_two : 2 ≤ (L_size : ℝ))
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (K_fiber_loss : ℝ) (hK_fiber_loss_one : 1 ≤ K_fiber_loss)
    (CΔ : ℝ) (hCΔ_def : CΔ = 2 * K_fiber_loss * K_Qmax * C₁)
    (K_ret K_loss K_fine K : ℝ)
    (hK_ret_def : K_ret = 4 * K_Qmax * K_fiber_loss)
    (hK_loss_def : K_loss = 16 * (numDyadicLevels M : ℝ)^2)
    (hK_fine_def : K_fine = K_loss * K_ret * Real.rpow 16 s)
    (hK_def : K = 24 * (L_size : ℝ) * K_fine) :
    (1 ≤ K_ret) ∧ (1 ≤ K_loss) ∧ (1 ≤ K_fine) ∧ (1 ≤ K) ∧
    (K_ret * K_loss ≤ K) ∧ (CΔ ≤ K * C₁) ∧ (C₁ ≤ K * CΔ) ∧
    (2 * (L_size : ℝ) * K_fiber_loss ≤ K) ∧
    (36 * K_ret * K_loss ≤ K) := by
  have h_pos_Q : 0 ≤ K_Qmax := by linarith [hK_Qmax_pos]
  have hL_pos : 0 < (L_size : ℝ) := by exact_mod_cast hL_size_pos
  have hL_nonneg : 0 ≤ (L_size : ℝ) := by linarith [hL_pos]
  have h_rpow_one : 1 ≤ Real.rpow 16 s := by
    apply Real.one_le_rpow <;> norm_num <;> linarith
  have h_rpow_nonneg : 0 ≤ Real.rpow 16 s := Real.rpow_nonneg (by norm_num) s
  have h_dyad_pos : 0 < numDyadicLevels M := by simp [numDyadicLevels] <;> omega
  have h_dyad_one : 1 ≤ (numDyadicLevels M : ℝ) := by exact_mod_cast h_dyad_pos
  have h_fiber_nonneg : 0 ≤ K_fiber_loss := by linarith [hK_fiber_loss_one]
  have h1 : 1 ≤ K_ret := by
    rw [hK_ret_def]
    have h9 : 1 ≤ 4 * K_Qmax * K_fiber_loss := by
      have h10 : 1 ≤ K_Qmax := hK_Qmax_one
      have h11 : 1 ≤ K_fiber_loss := hK_fiber_loss_one
      nlinarith
    exact h9
  have h2 : 1 ≤ K_loss := by
    rw [hK_loss_def]
    have h5 : 1 ≤ 16 * (numDyadicLevels M : ℝ)^2 := by
      have h6 : 1 ≤ (numDyadicLevels M : ℝ) := h_dyad_one
      nlinarith
    exact h5
  have h_loss_nonneg : 0 ≤ K_loss := by linarith [h2]
  have h_ret_nonneg : 0 ≤ K_ret := by linarith [h1]
  have h3 : 1 ≤ K_fine := by
    rw [hK_fine_def]
    have h4 : 1 ≤ K_loss * K_ret := by nlinarith [h1, h2]
    have h8 : 1 ≤ (K_loss * K_ret) * Real.rpow 16 s := by
      nlinarith [h_rpow_one, h4]
    exact h8
  have hK_fine_ge_ret : K_fine ≥ K_ret := by
    rw [hK_fine_def]
    have h : 1 ≤ K_loss * Real.rpow 16 s := by nlinarith [h2, h_rpow_one]
    nlinarith
  have h4 : 1 ≤ K := by
    rw [hK_def]
    have h9 : 1 ≤ 24 * (L_size : ℝ) * K_fine := by
      nlinarith [hL_size_two, h3]
    exact h9
  have h5 : K_ret * K_loss ≤ K := by
    rw [hK_def, hK_fine_def]
    have h9 : 1 ≤ 24 * (L_size : ℝ) * Real.rpow 16 s := by
      have h10 : 2 ≤ (L_size : ℝ) := hL_size_two
      have h11 : 1 ≤ Real.rpow 16 s := h_rpow_one
      nlinarith
    have h10 : 0 ≤ K_ret * K_loss := mul_nonneg h_ret_nonneg h_loss_nonneg
    have h11 : 1 * (K_ret * K_loss) ≤ (24 * (L_size : ℝ) * Real.rpow 16 s) * (K_ret * K_loss) :=
      mul_le_mul_of_nonneg_right h9 h10
    have h11' : K_ret * K_loss ≤ (24 * (L_size : ℝ) * Real.rpow 16 s) * (K_ret * K_loss) := by
      simpa [one_mul] using h11
    have h12 : (24 * (L_size : ℝ) * Real.rpow 16 s) * (K_ret * K_loss) =
        24 * (L_size : ℝ) * (K_loss * K_ret * Real.rpow 16 s) := by ring
    rw [h12] at h11'
    exact h11'
  have h6 : CΔ ≤ K * C₁ := by
    rw [hCΔ_def, hK_def]
    have h7 : 0 ≤ C₁ := by linarith [hC₁]
    have h81 : 2 * K_fiber_loss * K_Qmax ≤ 24 * (L_size : ℝ) * K_fine := by
      have h82 : K_fine ≥ K_ret := hK_fine_ge_ret
      rw [hK_ret_def] at h82
      nlinarith [hL_size_two]
    exact mul_le_mul_of_nonneg_right h81 h7
  have h7 : C₁ ≤ K * CΔ := by
    rw [hCΔ_def]
    have h8 : 0 ≤ C₁ := by linarith [hC₁]
    have h9 : 1 ≤ K := h4
    have h10 : 0 ≤ K := by linarith [h9]
    have h11 : 1 ≤ 2 * K_fiber_loss * K_Qmax := by
      nlinarith [hK_Qmax_one, hK_fiber_loss_one]
    have h13 : C₁ ≤ 2 * K_fiber_loss * K_Qmax * C₁ := by
      calc C₁ = 1 * C₁ := by ring
      _ ≤ 2 * K_fiber_loss * K_Qmax * C₁ := mul_le_mul_of_nonneg_right h11 h8
    have h14 : K * C₁ ≤ K * (2 * K_fiber_loss * K_Qmax * C₁) :=
      mul_le_mul_of_nonneg_left h13 h10
    have h15 : C₁ ≤ K * C₁ := by
      calc C₁ = 1 * C₁ := by ring
      _ ≤ K * C₁ := mul_le_mul_of_nonneg_right h9 h8
    calc C₁ ≤ K * C₁ := h15
         _ ≤ K * (2 * K_fiber_loss * K_Qmax * C₁) := h14
  have h8 : 2 * (L_size : ℝ) * K_fiber_loss ≤ K := by
    rw [hK_def]
    have h9 : 2 * (L_size : ℝ) * K_fiber_loss ≤ 24 * (L_size : ℝ) * K_fine := by
      have h10 : K_fine ≥ K_ret := hK_fine_ge_ret
      rw [hK_ret_def] at h10
      nlinarith [hL_nonneg, h_fiber_nonneg]
    exact h9
  have h9 : 36 * K_ret * K_loss ≤ K := by
    rw [hK_def, hK_fine_def]
    have h10 : 0 ≤ K_ret * K_loss := mul_nonneg h_ret_nonneg h_loss_nonneg
    have h11 : 36 ≤ 24 * (L_size : ℝ) * Real.rpow 16 s := by
      have h12 : 2 ≤ (L_size : ℝ) := hL_size_two
      have h13 : 1 ≤ Real.rpow 16 s := h_rpow_one
      nlinarith
    have h14 : 36 * K_ret * K_loss ≤ (24 * (L_size : ℝ) * Real.rpow 16 s) * (K_ret * K_loss) := by
      have h15 : 36 * K_ret * K_loss = 36 * (K_ret * K_loss) := by ring
      rw [h15]
      exact mul_le_mul_of_nonneg_right h11 h10
    have h16 : (24 * (L_size : ℝ) * Real.rpow 16 s) * (K_ret * K_loss) =
        24 * (L_size : ℝ) * (K_loss * K_ret * Real.rpow 16 s) := by ring
    rw [h16] at h14
    exact h14
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem induction_step_v3
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (hP_nonempty : config.points.Nonempty)
    (h_tubes_bounded : config.tubes.card ≤ 36 * 16^n) :
    ∃ (K : ℝ), 1 ≤ K ∧
      K ≤ 3145728 * (4 * (n : ℝ) + 7)^7 ∧
      ∃ (max_size : ℕ),
      K = 98304 * (numDyadicLevels max_size : ℝ) *
          (numDyadicLevels M : ℝ)^3 *
          (numDyadicLevels (config.points.card * M) : ℝ) *
          (numDyadicLevels config.tubes.card : ℝ)^2 *
          Real.rpow 16 s ∧
      ∃ (P : Finset (DyadicSquare n))
      (hP_sub : P ⊆ config.points)
      (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
      (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
      (coarseConfig : NiceConfiguration m s CΔ MΔ)
      (CQ : DyadicSquare m → ℝ)
      (MQ : DyadicSquare m → ℕ)
      (hMQ : ∀ Q ∈ coarseConfig.points, 0 < MQ Q)
      (fineConfig : (Q : DyadicSquare m) → Q ∈ coarseConfig.points →
        NiceConfiguration (n - m) s (CQ Q) (MQ Q)),
      P.Nonempty ∧
      coarseConfig.points = P.image (containingSquare hnm) ∧
      ((config.points.image (containingSquare hnm)).card : ℝ) ≤
        K * (coarseConfig.points.card : ℝ) ∧
      (∀ Q ∈ coarseConfig.points,
        ((config.points.filter fun p => squareContained hnm p Q).card : ℝ) ≤
          K * ((P.filter fun p => squareContained hnm p Q).card : ℝ)) ∧
      (∀ p, ∀ hp : p ∈ P,
        tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp) ∧
        (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ) ∧
        IsFiniteTubeSSet s (K * C₁) (tubeFamily p hp) ∧
        ∀ T ∈ tubeFamily p hp, (T.toSet ∩ p.toSet).Nonempty) ∧
      CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ ∧
      (∀ Q ∈ coarseConfig.points, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q) ∧
      (∀ p, ∀ hp : p ∈ P, ∀ T ∈ tubeFamily p hp,
        ∃ (hQ : containingSquare hnm p ∈ coarseConfig.points)
          (U : DyadicTube m),
          U ∈ coarseConfig.tubeFamily (containingSquare hnm p) hQ ∧
          T.toSet ⊆ U.toSet) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
        (fineConfig Q hQ).points =
          (P.filter fun p => squareContained hnm p Q).image
            (squareHomothety hnm Q)) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
        ∀ p, ∀ hp : p ∈ P, squareContained hnm p Q →
          ∃ hq : squareHomothety hnm Q p ∈ (fineConfig Q hQ).points,
            ((fineConfig Q hQ).tubeFamily
                (squareHomothety hnm Q p) hq).image (fun U => U.a) =
              (tubeFamily p hp).image
                (fun T => localSlopeCellIndex m T.a)) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
        K * (config.tubes.card : ℝ) * MΔ * MQ Q ≥
          (coarseConfig.tubes.card : ℝ) *
            ((fineConfig Q hQ).tubes.card : ℝ) * M) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.points,
        (fineConfig Q hQ).tubes =
          (fineConfig Q hQ).points.biUnion (fun q =>
            if hq : q ∈ (fineConfig Q hQ).points then
              (fineConfig Q hQ).tubeFamily q hq else ∅)) := by
  -- ========================================================================
  -- Step 1: Per-Q coarse phase
  -- ========================================================================
  let QSet : Finset (DyadicSquare m) :=
    config.points.image (containingSquare hnm)
  have hQSet_nonempty : QSet.Nonempty := hP_nonempty.image _

  let P_Q (Q : DyadicSquare m) : Finset (DyadicSquare n) :=
    config.points.filter (fun p => squareContained hnm p Q)

  let tubeFamily_Q (Q : DyadicSquare m) (p : DyadicSquare n)
      (hp : p ∈ P_Q Q) : Finset (DyadicTube n) :=
    config.tubeFamily p ((Finset.mem_filter.mp hp).1)

  have hP_Q_nonempty : ∀ Q ∈ QSet, (P_Q Q).Nonempty := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
    have h_cont : squareContained hnm p (containingSquare hnm p) :=
      (squareContained_iff_containingSquare hnm p (containingSquare hnm p)).mpr rfl
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h_cont⟩⟩

  have h_per_q_main : ∀ (Q : DyadicSquare m), Q ∈ QSet →
      ∃ (d : PerQCoarseData n m s C₁ M config hnm Q), True := by
    intro Q hQ
    rcases coarse_phase_data hnm s hs hs_one C₁ hC₁ M hM
        (P_Q Q) (tubeFamily_Q Q)
        (fun p hp => config.h_sset p ((Finset.mem_filter.mp hp).1))
        (fun p hp => config.h_size p ((Finset.mem_filter.mp hp).1))
        (fun p hp T hT => config.h_incidence p ((Finset.mem_filter.mp hp).1) T hT)
        (fun p hp T hT => config.h_tube_parameters T
          (config.h_subset p ((Finset.mem_filter.mp hp).1) hT))
        (fun p hp => config.h_bounded p ((Finset.mem_filter.mp hp).1))
        (hP_Q_nonempty Q hQ)
      with ⟨K_Q, hK_Q, coarseTubes_Q, C₂_Q, hC₂_Q, H_Q, hH_Q,
        bandTubes_Q, m₁_Q, coarseFamily_Q, retained_Q, h_main⟩
    dsimp only at h_main
    rcases h_main with ⟨_, _, h_coarse_sset, hC₂_le, hC₁_le,
      h_card_upper, h_card_lower, h_popularity_sum,
      h_band_sub, _, _, _,
      _, h_retained_eq, h_containment, hK_eq, hC₂_eq⟩

    -- Convert popularity sum to use config.tubeFamilyOpt
    have h_popularity' : ∀ U ∈ coarseTubes_Q,
        H_Q ≤ ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
      intro U hU
      have h_eq_sum : ∑ p ∈ P_Q Q,
          (countInCoarse hnm
            (if hp : p ∈ P_Q Q then tubeFamily_Q Q p hp else ∅) U : ℝ) =
          ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have h1 : (if hp' : p ∈ P_Q Q then tubeFamily_Q Q p hp' else ∅) =
            config.tubeFamilyOpt p := by
          have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
          simp [tubeFamily_Q, NiceConfiguration.tubeFamilyOpt, hp, hpin]
          <;> rfl
        rw [h1]
      have h_orig := h_popularity_sum U hU
      rw [h_eq_sum] at h_orig
      exact h_orig

    -- Preimage property from popularity sum
    let preimage : ∀ (U : DyadicTube m), U ∈ coarseTubes_Q →
        ∃ (p : DyadicSquare n) (hp : p ∈ config.points) (hsc : squareContained hnm p Q)
          (T : DyadicTube n), T ∈ config.tubeFamily p hp ∧ coarseAnc hnm T = U := by
      intro U hU
      have h_sum_pos : 0 < ∑ p ∈ P_Q Q,
          (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
        have hH : (1 : ℝ) ≤ H_Q := hH_Q
        have h := h_popularity' U hU
        linarith
      have h_exists : ∃ (p : DyadicSquare n), p ∈ P_Q Q ∧
          0 < countInCoarse hnm (config.tubeFamilyOpt p) U := by
        by_contra h
        push Not at h
        have h_all_zero : ∀ p ∈ P_Q Q,
            countInCoarse hnm (config.tubeFamilyOpt p) U = 0 := by
          intro p hp
          have h4 : countInCoarse hnm (config.tubeFamilyOpt p) U ≤ 0 := h p hp
          omega
        have h_sum_zero : ∑ p ∈ P_Q Q,
            (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) = 0 := by
          rw [Finset.sum_congr rfl (fun p hp => by
            rw [h_all_zero p hp] <;> norm_cast)] <;> simp
        rw [h_sum_zero] at h_sum_pos
        linarith
      rcases h_exists with ⟨p, hp, hpos⟩
      have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
      have hsc : squareContained hnm p Q := (Finset.mem_filter.mp hp).2
      have hF_eq : config.tubeFamilyOpt p = config.tubeFamily p hpin := by
        simp [NiceConfiguration.tubeFamilyOpt, hpin]
      have h_filter_pos : 0 < ((config.tubeFamily p hpin).filter (fun T => coarseAnc hnm T = U)).card := by
        have h_count_eq : countInCoarse hnm (config.tubeFamilyOpt p) U =
            ((config.tubeFamilyOpt p).filter (fun T => coarseAnc hnm T = U)).card := by rfl
        rw [h_count_eq, hF_eq] at hpos
        exact hpos
      have h_filter_nonempty : ((config.tubeFamily p hpin).filter (fun T => coarseAnc hnm T = U)).Nonempty :=
        Finset.card_pos.mp h_filter_pos
      rcases h_filter_nonempty with ⟨T, hT_in⟩
      have hT_in_F : T ∈ config.tubeFamily p hpin := (Finset.mem_filter.mp hT_in).1
      have hT_eq : coarseAnc hnm T = U := (Finset.mem_filter.mp hT_in).2
      exact ⟨p, hpin, hsc, T, hT_in_F, hT_eq⟩

    let d : PerQCoarseData n m s C₁ M config hnm Q :=
      { K_Q := K_Q
        coarseTubes_Q := coarseTubes_Q
        C₂_Q := C₂_Q
        H_Q := H_Q
        hH_Q := hH_Q
        retained_Q := retained_Q
        h_sset := h_coarse_sset
        h_C₂_le := hC₂_le
        h_C₁_le := hC₁_le
        h_card_upper := h_card_upper
        h_card_lower := h_card_lower
        h_popularity := h_popularity'
        h_preimage := preimage
        h_retained_sub := fun p hp => by
          have h1 : retained_Q p ⊆ bandTubes_Q p := by
            rw [h_retained_eq p hp] <;> exact Finset.filter_subset _ _
          exact Finset.Subset.trans h1 (h_band_sub p hp)
        h_retained_contain := h_containment
        h_K_eq := hK_eq
        h_C₂_eq := hC₂_eq }
    exact ⟨d, trivial⟩

  classical
  choose perQData _ using h_per_q_main

  -- Total accessor functions (return dummy values outside QSet)
  let K_Q (Q : DyadicSquare m) : ℝ :=
    if hQ : Q ∈ QSet then (perQData Q hQ).K_Q else 1
  let coarseTubes_Q (Q : DyadicSquare m) : Finset (DyadicTube m) :=
    if hQ : Q ∈ QSet then (perQData Q hQ).coarseTubes_Q else ∅
  let C₂_Q (Q : DyadicSquare m) : ℝ :=
    if hQ : Q ∈ QSet then (perQData Q hQ).C₂_Q else C₁
  let H_Q (Q : DyadicSquare m) : ℝ :=
    if hQ : Q ∈ QSet then (perQData Q hQ).H_Q else 1
  let retained_Q (Q : DyadicSquare m) : DyadicSquare n → Finset (DyadicTube n) :=
    if hQ : Q ∈ QSet then (perQData Q hQ).retained_Q else fun _ => ∅

  -- Uniform upper bound on K_Q
  let K_Qmax : ℝ :=
    32 * ((Nat.log 2 M : ℝ) + 2) *
      ((Nat.log 2 (config.points.card * M) : ℝ) + 2)

  have hK_Qmax_pos : 0 < K_Qmax := by
    have h1 : 0 < (Nat.log 2 M : ℝ) + 2 := by positivity
    have h2 : 0 < (Nat.log 2 (config.points.card * M) : ℝ) + 2 := by positivity
    positivity

  have hK_Qmax_one : 1 ≤ K_Qmax := by
    dsimp only [K_Qmax]
    have h1 : 2 ≤ (Nat.log 2 M : ℝ) + 2 := by
      have h11 : 0 ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : 2 ≤ (Nat.log 2 (config.points.card * M) : ℝ) + 2 := by
      have h21 : 0 ≤ (Nat.log 2 (config.points.card * M) : ℝ) := Nat.cast_nonneg _
      linarith
    have h4 : (128 : ℝ) ≤ 32 * ((Nat.log 2 M : ℝ) + 2) * ((Nat.log 2 (config.points.card * M) : ℝ) + 2) := by
      calc (128 : ℝ)
        = 32 * (2 : ℝ) * (2 : ℝ) := by norm_num
      _ ≤ 32 * ((Nat.log 2 M : ℝ) + 2) * (2 : ℝ) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by norm_num) (by norm_num) (by positivity)
      _ ≤ 32 * ((Nat.log 2 M : ℝ) + 2) * ((Nat.log 2 (config.points.card * M) : ℝ) + 2) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : (1 : ℝ) ≤ 128 := by norm_num
    exact le_trans h5 h4

  have hK_Q_le_max : ∀ Q ∈ QSet, K_Q Q ≤ K_Qmax := by
    intro Q hQ
    have h_eq : K_Q Q = (perQData Q hQ).K_Q := by
      simp [K_Q, hQ]
    rw [h_eq]
    have h3 : (P_Q Q).card ≤ config.points.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h4 : (perQData Q hQ).K_Q = 32 * ((Nat.log 2 M : ℝ) + 2) *
        ((Nat.log 2 ((P_Q Q).card * M) : ℝ) + 2) := (perQData Q hQ).h_K_eq
    rw [h4]
    have h5 : Nat.log 2 ((P_Q Q).card * M) ≤ Nat.log 2 (config.points.card * M) := by
      have h6 : (P_Q Q).card * M ≤ config.points.card * M := by
        have h7 : (P_Q Q).card ≤ config.points.card := Finset.card_le_card (Finset.filter_subset _ _)
        exact Nat.mul_le_mul_right M h7
      exact Nat.log_monotone h6
    simp only [K_Qmax]
    gcongr
    <;> linarith

  have hC₂_Q_le : ∀ Q ∈ QSet, C₂_Q Q ≤ K_Qmax * C₁ := by
    intro Q hQ
    have h1 : C₂_Q Q = (perQData Q hQ).C₂_Q := by simp [C₂_Q, hQ]
    rw [h1]
    have h2 : (perQData Q hQ).C₂_Q ≤ (perQData Q hQ).K_Q * C₁ :=
      (perQData Q hQ).h_C₂_le
    have hKQ_eq : K_Q Q = (perQData Q hQ).K_Q := by simp [K_Q, hQ]
    have h3 : (perQData Q hQ).K_Q ≤ K_Qmax := by
      rw [←hKQ_eq]
      exact hK_Q_le_max Q hQ
    calc (perQData Q hQ).C₂_Q
      ≤ (perQData Q hQ).K_Q * C₁ := h2
    _ ≤ K_Qmax * C₁ := by
      gcongr
      <;> linarith [hC₁]

  -- ========================================================================
  -- Step 2: Size-band pigeonhole on |coarseTubes_Q|
  -- ========================================================================
  let familySize (Q : DyadicSquare m) : ℕ := (coarseTubes_Q Q).card

  have h_coarseTubes_Q_nonempty : ∀ Q ∈ QSet, (coarseTubes_Q Q).Nonempty := by
    intro Q hQ
    have h_eq : coarseTubes_Q Q = (perQData Q hQ).coarseTubes_Q := by
      simp [coarseTubes_Q, hQ]
    rw [h_eq]
    have h1 : (M : ℝ) * (P_Q Q).card ≤
        (perQData Q hQ).K_Q * (perQData Q hQ).H_Q * ((perQData Q hQ).coarseTubes_Q.card : ℝ) :=
      (perQData Q hQ).h_card_lower
    have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hP_pos : (0 : ℝ) < (P_Q Q).card := by
      exact_mod_cast (hP_Q_nonempty Q hQ).card_pos
    have h3 : (0 : ℝ) < (M : ℝ) * (P_Q Q).card := by positivity
    have h4 : (0 : ℝ) < ((perQData Q hQ).coarseTubes_Q.card : ℝ) := by
      have h5 : 0 < (perQData Q hQ).K_Q := by
        have h6 : (perQData Q hQ).K_Q = 32 * ((Nat.log 2 M : ℝ) + 2) * ((Nat.log 2 ((P_Q Q).card * M) : ℝ) + 2) := (perQData Q hQ).h_K_eq
        rw [h6] <;> positivity
      have h7 : 0 < (perQData Q hQ).H_Q := by
        have h8 : 1 ≤ (perQData Q hQ).H_Q := (perQData Q hQ).hH_Q
        linarith
      have h_pos : 0 < (perQData Q hQ).K_Q * (perQData Q hQ).H_Q := mul_pos h5 h7
      have h9 : 0 < (perQData Q hQ).K_Q * (perQData Q hQ).H_Q * ((perQData Q hQ).coarseTubes_Q.card : ℝ) :=
        calc 0
          < (M : ℝ) * (P_Q Q).card := h3
        _ ≤ _ := h1
      exact (mul_pos_iff_of_pos_left h_pos).mp h9
    exact Finset.card_pos.mp (by exact_mod_cast h4)

  have h_familySize_pos : ∀ Q ∈ QSet, 0 < familySize Q := by
    intro Q hQ
    exact (h_coarseTubes_Q_nonempty Q hQ).card_pos

  let max_size : ℕ := QSet.sup familySize
  have hmax_pos : 0 < max_size := by
    rcases hQSet_nonempty with ⟨Q, hQ⟩
    have h1 : 0 < familySize Q := h_familySize_pos Q hQ
    have h2 : familySize Q ≤ max_size := Finset.le_sup hQ
    exact lt_of_lt_of_le h1 h2

  have h_bound : ∀ Q ∈ QSet, familySize Q ≤ max_size := by
    intro Q hQ
    exact Finset.le_sup hQ

  -- Size-band pigeonhole (inline version with real retention bound)
  rcases exists_dyadic_size_subfamily QSet familySize hmax_pos h_bound h_familySize_pos
    with ⟨MΔ0, QSet0, hQSet0_sub, h_band0, h_card0⟩

  -- Handle empty QSet0 by falling back to singleton
  rcases hQSet_nonempty with ⟨Q0, hQ0⟩
  let QSet' : Finset (DyadicSquare m) :=
    if h : QSet0.Nonempty then QSet0 else {Q0}
  let MΔ : ℕ :=
    if h : QSet0.Nonempty then MΔ0 else familySize Q0

  have hQSet'_sub : QSet' ⊆ QSet := by
    dsimp only [QSet']
    split_ifs <;> simp [hQSet0_sub, hQ0] <;> tauto

  have h_band : ∀ Q ∈ QSet', MΔ ≤ familySize Q ∧ familySize Q < 2 * MΔ := by
    intro Q hQ
    by_cases h : QSet0.Nonempty
    · have hQSet'_eq : QSet' = QSet0 := by dsimp only [QSet']; rw [dif_pos h]
      have hMΔ_eq : MΔ = MΔ0 := by dsimp only [MΔ]; rw [dif_pos h]
      have hQ0 : Q ∈ QSet0 := by rw [hQSet'_eq] at hQ; exact hQ
      rw [hMΔ_eq]
      exact h_band0 Q hQ0
    · have hQSet'_eq : QSet' = {Q0} := by dsimp only [QSet']; rw [dif_neg h]
      have hMΔ_eq : MΔ = familySize Q0 := by dsimp only [MΔ]; rw [dif_neg h]
      have hQ_eq : Q = Q0 := by rw [hQSet'_eq] at hQ; exact Finset.mem_singleton.mp hQ
      rw [hMΔ_eq, hQ_eq]
      have hpos : 0 < familySize Q0 := h_familySize_pos Q0 hQ0
      exact ⟨by rfl, by linarith⟩

  have hQSet'_nonempty : QSet'.Nonempty := by
    dsimp only [QSet']
    split_ifs with h
    · exact h
    · exact Finset.singleton_nonempty Q0

  have hMΔ_pos : 0 < MΔ := by
    by_cases h : QSet0.Nonempty
    · have hMΔ_eq : MΔ = MΔ0 := by dsimp only [MΔ]; rw [dif_pos h]
      rw [hMΔ_eq]
      rcases h with ⟨Q, hQ⟩
      have h2 : MΔ0 ≤ familySize Q := (h_band0 Q hQ).1
      have h2' : familySize Q < 2 * MΔ0 := (h_band0 Q hQ).2
      have h3 : 0 < familySize Q := h_familySize_pos Q (hQSet0_sub hQ)
      have h4 : 0 < MΔ0 := by
        by_contra h5
        have h6 : MΔ0 = 0 := by omega
        rw [h6] at h2'
        have h7 : familySize Q < 0 := h2'
        have h8 : 0 ≤ familySize Q := Nat.zero_le (familySize Q)
        exact False.elim (by linarith)
      exact h4
    · have hMΔ_eq : MΔ = familySize Q0 := by dsimp only [MΔ]; rw [dif_neg h]
      rw [hMΔ_eq]
      exact h_familySize_pos Q0 hQ0

  -- Real retention bound for QSet'
  let L := numDyadicLevels max_size
  have hL_pos : 0 < L := by simp [L, numDyadicLevels] <;> omega

  have h_retention_QSet : (QSet.card : ℝ) ≤ (2 * (L : ℝ)) * (QSet'.card : ℝ) := by
    dsimp only [QSet']
    split_ifs with h
    · -- QSet0 nonempty
      have h1 : QSet.card / L ≤ QSet0.card := h_card0
      have h2 : QSet.card = (QSet.card / L) * L + QSet.card % L := by exact Eq.symm (Nat.div_add_mod' QSet.card L)
      have h3 : QSet.card % L < L := Nat.mod_lt _ hL_pos
      have h4 : 0 < QSet0.card := h.card_pos
      have h5 : L ≤ L * QSet0.card := by
        exact Nat.le_mul_of_pos_right L h4
      have h6 : QSet.card % L ≤ L - 1 := by omega
      have h7 : L - 1 ≤ L * QSet0.card := by omega
      have h8 : QSet.card ≤ 2 * L * QSet0.card := by
        calc QSet.card
          = (QSet.card / L) * L + QSet.card % L := h2
        _ ≤ QSet0.card * L + (L - 1) := by gcongr <;> omega
        _ ≤ QSet0.card * L + L * QSet0.card := by gcongr
        _ = 2 * L * QSet0.card := by ring
      exact_mod_cast h8
    · -- QSet0 empty: QSet.card < L, QSet' = {Q0}
      have h_empty : QSet0 = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
      have h1 : QSet.card / L ≤ QSet0.card := h_card0
      rw [h_empty] at h1
      have h2 : QSet.card / L = 0 := Nat.eq_zero_of_le_zero h1
      have h3 : QSet.card < L := by
        exact (Nat.div_eq_zero_iff).mp h2 |>.resolve_left hL_pos.ne'
      have h4 : (QSet.card : ℝ) ≤ (2 * (L : ℝ)) := by
        exact_mod_cast (by omega)
      have h5 : ({Q0} : Finset (DyadicSquare m)).card = 1 := by simp
      rw [h5]
      <;> simpa using h4

  -- ========================================================================
  -- Step 3: Prove bridge inputs and call fiber-aware coarse phase
  -- ========================================================================

  -- Preimage: every coarse tube comes from a fine tube via coarseAnc.
  have h_coarse_preimage : ∀ (Q : DyadicSquare m) (hQ : Q ∈ QSet') (U : DyadicTube m),
      U ∈ coarseTubes_Q Q →
      ∃ (p : DyadicSquare n) (hp : p ∈ config.points)
        (hsc : squareContained hnm p Q) (T : DyadicTube n),
        T ∈ config.tubeFamily p hp ∧ coarseAnc hnm T = U := by
    intro Q hQ U hU
    have hQ_in : Q ∈ QSet := hQSet'_sub hQ
    let d := perQData Q hQ_in
    have h_eq1 : coarseTubes_Q Q = d.coarseTubes_Q := by
      dsimp only [coarseTubes_Q]
      rw [dif_pos hQ_in] <;> rfl
    have hU' : U ∈ d.coarseTubes_Q := by
      rw [h_eq1] at hU
      exact hU
    have h_sum : (d.H_Q : ℝ) ≤ ∑ p ∈ P_Q Q,
        (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) :=
      d.h_popularity U hU'
    have h_sum_pos : 0 < ∑ p ∈ P_Q Q,
        (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
      have hH : (1 : ℝ) ≤ d.H_Q := d.hH_Q
      linarith
    have h_exists : ∃ (p : DyadicSquare n), p ∈ P_Q Q ∧
        0 < countInCoarse hnm (config.tubeFamilyOpt p) U := by
      by_contra h
      push Not at h
      have h_all_zero : ∀ p ∈ P_Q Q, countInCoarse hnm (config.tubeFamilyOpt p) U = 0 := by
        intro p hp
        have h4 : _ ≤ 0 := h p hp
        omega
      have h_sum_zero : ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) = 0 := by
        rw [Finset.sum_congr rfl (fun p hp => by rw [h_all_zero p hp] <;> norm_cast)] <;> simp
      rw [h_sum_zero] at h_sum_pos
      linarith
    rcases h_exists with ⟨p, hpQ, hpos⟩
    have h_filter_nonempty : ((config.tubeFamilyOpt p).filter (fun T => coarseAnc hnm T = U)).Nonempty :=
      Finset.card_pos.mp (by simpa [countInCoarse] using hpos)
    rcases h_filter_nonempty with ⟨T, hT_in⟩
    have hT_in_F : T ∈ config.tubeFamilyOpt p := (Finset.mem_filter.mp hT_in).1
    have hT_eq : coarseAnc hnm T = U := (Finset.mem_filter.mp hT_in).2
    have hp' : p ∈ config.points := (Finset.mem_filter.mp hpQ).1
    have hsc : squareContained hnm p Q := (Finset.mem_filter.mp hpQ).2
    have hT_in_family : T ∈ config.tubeFamily p hp' := by
      have h_opt : config.tubeFamilyOpt p = config.tubeFamily p hp' := by
        simp [NiceConfiguration.tubeFamilyOpt, hp']
      rw [h_opt] at hT_in_F
      exact hT_in_F
    exact ⟨p, hp', hsc, T, hT_in_family, hT_eq⟩

  -- Fiber positivity for bridge input
  have h_fiber_pos_all : ∀ Q ∈ QSet', ∀ U ∈ coarseTubes_Q Q,
      0 < fiberSize hnm config.tubes U := by
    intro Q hQ U hU
    rcases h_coarse_preimage Q hQ U hU with ⟨p, hp', hsc, T, hT_in_F, hT_eq⟩
    have hT_in_tubes : T ∈ config.tubes := config.h_subset p hp' hT_in_F
    have h_contain : T.toSet ⊆ U.toSet := by
      have h : T.toSet ⊆ (coarseAnc hnm T).toSet := coarseAnc_contains hnm T
      rw [hT_eq] at h
      exact h
    have h_in_fiber : T ∈ config.tubes.filter (fun T => T.toSet ⊆ U.toSet) :=
      Finset.mem_filter.mpr ⟨hT_in_tubes, h_contain⟩
    exact Finset.card_pos.mpr ⟨T, h_in_fiber⟩

  -- Incidence for all coarse tubes (bridge input)
  have h_incidence_all : ∀ Q ∈ QSet', ∀ U ∈ coarseTubes_Q Q,
      (U.toSet ∩ Q.toSet).Nonempty := by
    intro Q hQ U hU
    rcases h_coarse_preimage Q hQ U hU with ⟨p, hp', hsc, T, hT_in_F, hT_eq⟩
    have h_inc_T : (T.toSet ∩ p.toSet).Nonempty := config.h_incidence p hp' T hT_in_F
    have hT_sub_U : T.toSet ⊆ U.toSet := by
      have h : T.toSet ⊆ (coarseAnc hnm T).toSet := coarseAnc_contains hnm T
      rw [hT_eq] at h
      exact h
    have hp_sub_Q : p.toSet ⊆ Q.toSet := squareContained_toSet_subset hsc
    rcases h_inc_T with ⟨x, hxT, hxp⟩
    exact ⟨x, hT_sub_U hxT, hp_sub_Q hxp⟩

  -- Parameter strip for all coarse tubes (bridge input)
  have h_strip_all : ∀ Q ∈ QSet', ∀ U ∈ coarseTubes_Q Q,
      U.IsInAllowedParameterStrip := by
    intro Q hQ U hU
    rcases h_coarse_preimage Q hQ U hU with ⟨p, hp', hsc, T, hT_in_F, hT_eq⟩
    have hT_in_config : T ∈ config.tubes := config.h_subset p hp' hT_in_F
    have hT_strip : T.IsInAllowedParameterStrip := config.h_tube_parameters T hT_in_config
    have hU_strip : (coarseAnc hnm T).IsInAllowedParameterStrip :=
      coarseAnc_in_allowed_strip hnm T hT_strip
    rw [hT_eq] at hU_strip
    exact hU_strip

  -- Boundedness for all Q in QSet' (bridge input)
  have h_bounded_all : ∀ Q ∈ QSet', Q.toSet ⊆ unitSquare := by
    intro Q hQ
    have hQ_in : Q ∈ QSet := hQSet'_sub hQ
    rcases Finset.mem_image.mp hQ_in with ⟨p, hp, rfl⟩
    have h_bounded : p.toSet ⊆ unitSquare := config.h_bounded p hp
    exact CoarsePhaseHelpers.coarse_square_bounded hnm p h_bounded

  -- C₂_max for bridge
  let C₂_max : ℝ := K_Qmax * C₁
  have hC₂_max : ∀ Q ∈ QSet', C₂_Q Q ≤ C₂_max := by
    intro Q hQ
    have hQ_in : Q ∈ QSet := hQSet'_sub hQ
    exact hC₂_Q_le Q hQ_in
  have hC₂_max_one : 1 ≤ C₂_max := by
    dsimp only [C₂_max]
    have h1 : 1 ≤ K_Qmax := hK_Qmax_one
    have h2 : 1 ≤ C₁ := hC₁
    nlinarith

  -- SSet for each Q (bridge input)
  have h_sset_all : ∀ Q ∈ QSet', IsFiniteTubeSSet s (C₂_Q Q) (coarseTubes_Q Q) := by
    intro Q hQ
    have hQ_in : Q ∈ QSet := hQSet'_sub hQ
    have h_eq : C₂_Q Q = (perQData Q hQ_in).C₂_Q := by simp [C₂_Q, hQ_in]
    have h_eq2 : coarseTubes_Q Q = (perQData Q hQ_in).coarseTubes_Q := by
      simpa [coarseTubes_Q, hQ_in] using rfl
    rw [h_eq, h_eq2]
    exact (perQData Q hQ_in).h_sset

  -- Call fiber-aware coarse phase bridge
  rcases (fiber_aware_coarse_phase hnm config QSet' coarseTubes_Q hMΔ_pos
      (fun Q hQ => (h_band Q hQ).1)
      (fun Q hQ => (h_band Q hQ).2)
      C₂_Q h_sset_all C₂_max hC₂_max hC₂_max_one
      h_fiber_pos_all h_incidence_all h_strip_all h_bounded_all
      hQSet'_nonempty)
    with ⟨QSet'', MΔ_new, trimmedFamily_new, CΔ_new, coarseConfig_new, NΔ, K_loss_fiber,
      hK_loss_one, hQSet''_sub, hQSet''_cover, hMΔ_new_pos, hMΔ_retention,
      hCΔ_eq, h_trimmed_card_new, h_trimmed_sub_new, h_fiber_band,
      h_points_new, h_tubes_new, h_tubeFamily_new, h_incidence_new, h_strip_new, h_bounded_new,
      hK_fiber_loss_eq⟩

  -- Save old values before shadowing
  let QSet_band := QSet'
  let MΔ_band := MΔ
  have hQSet_band_nonempty : QSet_band.Nonempty := hQSet'_nonempty
  have hQSet_band_sub : QSet_band ⊆ QSet := hQSet'_sub
  have h_band_band : ∀ Q ∈ QSet_band, MΔ_band ≤ (coarseTubes_Q Q).card ∧ (coarseTubes_Q Q).card < 2 * MΔ_band := h_band

  -- ========================================================================
  -- Step 4: Adopt bridge outputs (shadow previous definitions)
  -- ========================================================================
  let QSet' : Finset (DyadicSquare m) := QSet''
  let MΔ : ℕ := MΔ_new
  let trimmedFamily (Q : DyadicSquare m) (hQ : Q ∈ QSet') : Finset (DyadicTube m) :=
    trimmedFamily_new Q
  let CΔ : ℝ := CΔ_new
  let coarseConfig : NiceConfiguration m s CΔ MΔ := coarseConfig_new
  let K_fiber_loss : ℝ := K_loss_fiber

  have hMΔ_pos : 0 < MΔ := hMΔ_new_pos
  have hQSet'_sub' : QSet' ⊆ QSet := Finset.Subset.trans hQSet''_sub hQSet_band_sub
  have h_trimmed_card : ∀ Q hQ, (trimmedFamily Q hQ).card = MΔ := by
    intro Q hQ
    exact h_trimmed_card_new Q hQ
  have h_trimmed_sub : ∀ Q hQ, trimmedFamily Q hQ ⊆ coarseTubes_Q Q := by
    intro Q hQ
    exact h_trimmed_sub_new Q hQ
  have hQSet'_nonempty : QSet'.Nonempty := by
    by_contra h
    have h_empty : QSet' = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_cont : (QSet_band.card : ℝ) ≤ 0 := by
      have h_cov : (QSet_band.card : ℝ) ≤ K_fiber_loss * (QSet'.card : ℝ) := hQSet''_cover
      rw [h_empty] at h_cov
      simpa using h_cov
    have h_old_pos : 0 < (QSet_band.card : ℝ) := by
      exact_mod_cast hQSet_band_nonempty.card_pos
    linarith
  have hMΔ_retention_bound : (MΔ_band : ℝ) ≤ K_fiber_loss * (MΔ : ℝ) := hMΔ_retention

  -- Fiber bounds for all coarse tubes
  have h_fiber_lower : ∀ U ∈ coarseConfig.tubes, NΔ ≤ fiberSize hnm config.tubes U := by
    intro U hU
    have hU' : U ∈ QSet'.biUnion trimmedFamily_new := by
      have h : coarseConfig.tubes = QSet'.biUnion trimmedFamily_new := h_tubes_new
      rw [h] at hU <;> exact hU
    rcases Finset.mem_biUnion.mp hU' with ⟨Q, hQ, hU'⟩
    exact (h_fiber_band Q hQ U hU').1
  have h_fiber_upper : ∀ U ∈ coarseConfig.tubes, fiberSize hnm config.tubes U < 4 * NΔ := by
    intro U hU
    have hU' : U ∈ QSet'.biUnion trimmedFamily_new := by
      have h : coarseConfig.tubes = QSet'.biUnion trimmedFamily_new := h_tubes_new
      rw [h] at hU <;> exact hU
    rcases Finset.mem_biUnion.mp hU' with ⟨Q, hQ, hU'⟩
    exact (h_fiber_band Q hQ U hU').2

  -- Updated QSet coverage: old QSet (band) ≤ K_fiber_loss * new QSet'
  have hQSet'_cover_updated : (QSet_band.card : ℝ) ≤ K_fiber_loss * (QSet'.card : ℝ) := hQSet''_cover

  -- ========================================================================
  -- Step 5: Define candRet
  -- ========================================================================
  let P0 : Finset (DyadicSquare n) :=
    config.points.filter (fun p => containingSquare hnm p ∈ QSet')

  have hP0_nonempty : P0.Nonempty := by
    rcases hQSet'_nonempty with ⟨Q, hQ⟩
    have hQ_in_QSet : Q ∈ QSet := hQSet'_sub' hQ
    rcases Finset.mem_image.mp hQ_in_QSet with ⟨p, hp, rfl⟩
    have h1 : containingSquare hnm p ∈ QSet' := hQ
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h1⟩⟩

  -- Per-Q candidate retained family (full family filtered to trimmed coarse ancestors)
  let candRet_Q (Q : DyadicSquare m) (hQ : Q ∈ QSet') (p : DyadicSquare n) :
      Finset (DyadicTube n) :=
    (config.tubeFamilyOpt p).filter (fun T => coarseAnc hnm T ∈ trimmedFamily Q hQ)

  let candRet (p : DyadicSquare n) (hp : p ∈ P0) : Finset (DyadicTube n) :=
    let Q_p := containingSquare hnm p
    let hQ_p : Q_p ∈ QSet' := (Finset.mem_filter.mp hp).2
    let hp' : p ∈ config.points := (Finset.mem_filter.mp hp).1
    (config.tubeFamily p hp').filter (fun T => coarseAnc hnm T ∈ trimmedFamily Q_p hQ_p)

  have h_candRet_eq : ∀ (p : DyadicSquare n) (hp : p ∈ P0),
      candRet p hp = candRet_Q (containingSquare hnm p)
        ((Finset.mem_filter.mp hp).2) p := by
    intro p hp
    dsimp only [candRet, candRet_Q]
    have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
    simp [NiceConfiguration.tubeFamilyOpt, hpin]
    <;> congr <;> rfl

  -- Containment (5.3): T ∈ candRet p means coarseAnc T ∈ trimmedFamily,
  -- and T.toSet ⊆ (coarseAnc T).toSet by coarseAnc_contains.
  have h_candRet_containment : ∀ (p : DyadicSquare n) (hp : p ∈ P0)
      (T : DyadicTube n), T ∈ candRet p hp →
        ∃ (hQ : containingSquare hnm p ∈ coarseConfig.points)
          (U : DyadicTube m),
          U ∈ coarseConfig.tubeFamily (containingSquare hnm p) hQ ∧
          T.toSet ⊆ U.toSet := by
    intro p hp T hT
    let Q_p := containingSquare hnm p
    let hQ_p : Q_p ∈ QSet' := (Finset.mem_filter.mp hp).2
    have h_anc_in_trimmed : coarseAnc hnm T ∈ trimmedFamily Q_p hQ_p :=
      (Finset.mem_filter.mp hT).2
    have h_coarseConfig_points : Q_p ∈ coarseConfig.points := by
      have hpts : coarseConfig.points = QSet' := h_points_new
      rw [hpts]
      exact hQ_p
    have h_trimmed_eq : coarseConfig.tubeFamily Q_p h_coarseConfig_points = trimmedFamily_new Q_p :=
      h_tubeFamily_new Q_p h_coarseConfig_points
    have h_anc_in_coarseFamily : coarseAnc hnm T ∈ coarseConfig.tubeFamily Q_p h_coarseConfig_points := by
      rw [h_trimmed_eq]
      exact h_anc_in_trimmed
    have h_containment : T.toSet ⊆ (coarseAnc hnm T).toSet :=
      coarseAnc_contains hnm T
    exact ⟨h_coarseConfig_points, coarseAnc hnm T, h_anc_in_coarseFamily, h_containment⟩

  -- ========================================================================
  -- Step 7: Per-Q retention bound
  -- ========================================================================
  have h_partition : ∀ (F : Finset (DyadicTube n)) (S : Finset (DyadicTube m)),
      (F.filter (fun T => coarseAnc hnm T ∈ S)).card =
        ∑ U ∈ S, (countInCoarse hnm F U) := by
    intro F S
    let fiber := fun U : DyadicTube m => F.filter (fun T => coarseAnc hnm T = U)
    have h_disj : Set.PairwiseDisjoint (S : Set (DyadicTube m)) fiber := by
      intro U1 _ U2 _ hne
      simp only [Finset.disjoint_left]
      intro T hT1 hT2
      have h1 : coarseAnc hnm T = U1 := (Finset.mem_filter.mp hT1).2
      have h2 : coarseAnc hnm T = U2 := (Finset.mem_filter.mp hT2).2
      have h3 : U1 = U2 := by rw [←h1, h2]
      exact hne h3
    have h_union : S.biUnion fiber = F.filter (fun T => coarseAnc hnm T ∈ S) := by
      apply Finset.ext; intro T
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨U, hU, hT⟩
        have h4 : T ∈ F := (Finset.mem_filter.mp hT).1
        have h5 : coarseAnc hnm T = U := (Finset.mem_filter.mp hT).2
        have h6 : coarseAnc hnm T ∈ S := h5.symm.subst hU
        exact ⟨h4, h6⟩
      · rintro ⟨hT, hU⟩
        refine ⟨coarseAnc hnm T, hU, Finset.mem_filter.mpr ⟨hT, rfl⟩⟩
    have h_sum : ∑ U ∈ S, (fiber U).card = (S.biUnion fiber).card := by
      rw [Finset.card_biUnion h_disj]
    have h_eq1 : ∑ U ∈ S, (countInCoarse hnm F U) = ∑ U ∈ S, (fiber U).card := by
      apply Finset.sum_congr rfl; intro U _; rfl
    rw [h_eq1, h_sum, h_union]

  have h_retention_per_Q : ∀ (Q : DyadicSquare m) (hQ : Q ∈ QSet'),
      (∑ p ∈ P_Q Q, (candRet_Q Q hQ p).card : ℝ) ≥
        (M : ℝ) * ((P_Q Q).card : ℝ) / (2 * K_Qmax * K_fiber_loss) := by
    intro Q hQ
    have hQ_in : Q ∈ QSet := hQSet'_sub' hQ
    have hQ_in_band : Q ∈ QSet_band := hQSet''_sub hQ
    set d := perQData Q hQ_in with hd
    have h_coarseTubes_eq : coarseTubes_Q Q = d.coarseTubes_Q := by
      simp [coarseTubes_Q, hQ_in, hd]
    have h_card_lower : (M : ℝ) * ((P_Q Q).card : ℝ) ≤
        d.K_Q * d.H_Q * ((coarseTubes_Q Q).card : ℝ) := by
      simpa [coarseTubes_Q, hQ_in, hd] using d.h_card_lower
    have h_size_band : (coarseTubes_Q Q).card < 2 * MΔ_band := (h_band_band Q hQ_in_band).2
    have h_trimmed_card' : (trimmedFamily Q hQ).card = MΔ := h_trimmed_card Q hQ

    have h_main_eq : ∀ p ∈ P_Q Q, candRet_Q Q hQ p =
        (config.tubeFamilyOpt p).filter (fun T => coarseAnc hnm T ∈ trimmedFamily Q hQ) := by
      intro p hp
      rfl

    have h_sum_ret : (∑ p ∈ P_Q Q, (candRet_Q Q hQ p).card : ℝ) =
        ∑ U ∈ trimmedFamily Q hQ, ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
      have h1 : ∀ p ∈ P_Q Q, ((candRet_Q Q hQ p).card : ℝ) =
          ∑ U ∈ trimmedFamily Q hQ, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
        intro p hp
        have h_eq1 : (candRet_Q Q hQ p).card =
            ∑ U ∈ trimmedFamily Q hQ, (countInCoarse hnm (config.tubeFamilyOpt p) U) := by
          rw [h_main_eq p hp]
          exact h_partition (config.tubeFamilyOpt p) (trimmedFamily Q hQ)
        exact_mod_cast h_eq1
      have h : (∑ p ∈ P_Q Q, (candRet_Q Q hQ p).card : ℝ) =
          ∑ p ∈ P_Q Q, ((candRet_Q Q hQ p).card : ℝ) := by rfl
      rw [h]
      have h2 : ∑ p ∈ P_Q Q, ((candRet_Q Q hQ p).card : ℝ) =
          ∑ p ∈ P_Q Q, (∑ U ∈ trimmedFamily Q hQ, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ)) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact h1 p hp
      rw [h2, Finset.sum_comm]
    rw [h_sum_ret]
    have h2 : ∑ U ∈ trimmedFamily Q hQ, ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) ≥
        ∑ U ∈ trimmedFamily Q hQ, d.H_Q := by
      apply Finset.sum_le_sum
      intro U hU
      have hU_in_coarse : U ∈ coarseTubes_Q Q := h_trimmed_sub Q hQ hU
      have hU' : U ∈ d.coarseTubes_Q := by
        rw [h_coarseTubes_eq] at hU_in_coarse; exact hU_in_coarse
      exact d.h_popularity U hU'
    have h3 : ∑ U ∈ trimmedFamily Q hQ, d.H_Q = (d.H_Q : ℝ) * (MΔ : ℝ) := by
      rw [Finset.sum_const, h_trimmed_card'] <;> ring
    rw [h3] at h2
    have hKQ_eq : K_Q Q = d.K_Q := by
      simp [K_Q, hQ_in, hd]
    have hKQ_le : d.K_Q ≤ K_Qmax := by
      rw [←hKQ_eq] <;> exact hK_Q_le_max Q hQ_in
    have h7 : 0 < d.K_Q := by
      have h8 : d.K_Q = 32 * ((Nat.log 2 M : ℝ) + 2) *
          ((Nat.log 2 ((P_Q Q).card * M) : ℝ) + 2) := d.h_K_eq
      rw [h8] <;> positivity
    have hH_pos : 0 < d.H_Q := by linarith [d.hH_Q]
    have h9 : (M : ℝ) * ((P_Q Q).card : ℝ) ≤ 2 * K_Qmax * (d.H_Q * (MΔ_band : ℝ)) := by
      calc (M : ℝ) * ((P_Q Q).card : ℝ)
        ≤ d.K_Q * d.H_Q * ((coarseTubes_Q Q).card : ℝ) := h_card_lower
      _ ≤ d.K_Q * d.H_Q * (2 * (MΔ_band : ℝ)) := by
        have h5' : ((coarseTubes_Q Q).card : ℝ) ≤ 2 * (MΔ_band : ℝ) := by exact_mod_cast h_size_band.le
        have h_nonneg : 0 ≤ d.K_Q * d.H_Q := by positivity
        exact mul_le_mul_of_nonneg_left h5' h_nonneg
      _ = 2 * d.K_Q * (d.H_Q * (MΔ_band : ℝ)) := by ring
      _ ≤ 2 * K_Qmax * (d.H_Q * (MΔ_band : ℝ)) := by
        have h_double : 2 * d.K_Q ≤ 2 * K_Qmax := by linarith [hKQ_le]
        have h_nonneg2 : 0 ≤ d.H_Q * (MΔ_band : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right h_double h_nonneg2
    have h10 : (MΔ_band : ℝ) ≤ K_fiber_loss * (MΔ : ℝ) := hMΔ_retention_bound
    have h11 : (M : ℝ) * ((P_Q Q).card : ℝ) ≤ 2 * K_Qmax * K_fiber_loss * (d.H_Q * (MΔ : ℝ)) := by
      have h12 : d.H_Q * (MΔ_band : ℝ) ≤ d.H_Q * (K_fiber_loss * (MΔ : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h10 (by positivity)
      have h13 : 2 * K_Qmax * (d.H_Q * (MΔ_band : ℝ)) ≤
          2 * K_Qmax * (d.H_Q * (K_fiber_loss * (MΔ : ℝ))) := by
        exact mul_le_mul_of_nonneg_left h12 (by positivity)
      have h14 : 2 * K_Qmax * (d.H_Q * (K_fiber_loss * (MΔ : ℝ))) =
          2 * K_Qmax * K_fiber_loss * (d.H_Q * (MΔ : ℝ)) := by ring
      linarith
    have h15 : 0 < 2 * K_Qmax * K_fiber_loss := by positivity
    have h16 : (M : ℝ) * ((P_Q Q).card : ℝ) / (2 * K_Qmax * K_fiber_loss) ≤ d.H_Q * (MΔ : ℝ) := by
      calc (M : ℝ) * ((P_Q Q).card : ℝ) / (2 * K_Qmax * K_fiber_loss)
        = ((M : ℝ) * ((P_Q Q).card : ℝ)) / (2 * K_Qmax * K_fiber_loss) := by rfl
      _ ≤ (2 * K_Qmax * K_fiber_loss * (d.H_Q * (MΔ : ℝ))) / (2 * K_Qmax * K_fiber_loss) := by gcongr
      _ = d.H_Q * (MΔ : ℝ) := by
        have hK_fiber_ne : K_fiber_loss ≠ 0 := by linarith [hK_loss_one]
        have h_ne : (2 * K_Qmax * K_fiber_loss : ℝ) ≠ 0 := h15.ne'
        field_simp [hK_fiber_ne, h_ne] <;> ring
    exact le_trans h16 h2


  -- ========================================================================
  -- Steps 8-10: Per-Q point selection, uniformization, fine phase
  -- ========================================================================
  let K_cpd : ℝ := 2 * K_Qmax * K_fiber_loss
  have hK_cpd_one : 1 ≤ K_cpd := by
    dsimp only [K_cpd, K_Qmax]
    have h1 : 0 ≤ (Nat.log 2 M : ℝ) := by positivity
    have h2 : 0 ≤ (Nat.log 2 (config.points.card * M) : ℝ) := by positivity
    have h3 : 1 ≤ K_fiber_loss := by linarith [hK_loss_one]
    nlinarith

  let originalFamily (p : DyadicSquare n) : Finset (DyadicTube n) :=
    config.tubeFamilyOpt p

  have h_step8_10 : ∀ (Q : DyadicSquare m) (hQ : Q ∈ QSet'),
      ∃ (P_Q' : Finset (DyadicSquare n))
        (hP_Q'_sub : P_Q' ⊆ P_Q Q)
        (hP_Q'_nonempty : P_Q'.Nonempty)
        (uniformFamily : (p : DyadicSquare n) → p ∈ P_Q' → Finset (DyadicTube n))
        (m_Q MQ : ℕ) (hmQ_pos : 0 < m_Q) (hMQ_pos : 0 < MQ)
        (K_ret K_loss K_fine : ℝ) (hK_ret : 1 ≤ K_ret) (hK_ret_eq : K_ret = 2 * K_cpd)
        (hK_loss : 1 ≤ K_loss) (hK_loss_eq : K_loss = 16 * (numDyadicLevels M : ℝ)^2)
        (hK_fine : 1 ≤ K_fine) (hK_fine_eq : K_fine = K_loss * K_ret * Real.rpow 16 s),
        (∀ p hp, uniformFamily p hp ⊆ candRet_Q Q hQ p) ∧
        (∀ p hp, (M : ℝ) ≤ K_ret * K_loss * ((uniformFamily p hp).card : ℝ)) ∧
        ((P_Q Q).card : ℝ) ≤ K_ret * K_loss * (P_Q'.card : ℝ) ∧
        (∀ p hp, IsFiniteTubeSSet s (K_loss * K_ret * C₁) (uniformFamily p hp)) ∧
        (∀ p hp (a : ℤ), ((uniformFamily p hp).filter
            (fun T => localSlopeCellIndex m T.a = a)).card =
          if a ∈ (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a)
          then m_Q else 0) ∧
        (∀ p hp, ((uniformFamily p hp).image
            (fun T => localSlopeCellIndex m T.a)).card = MQ) ∧
        (∀ p hp T, T ∈ uniformFamily p hp → (T.toSet ∩ p.toSet).Nonempty) ∧
        (∀ p hp T, T ∈ uniformFamily p hp → T.IsInAllowedParameterStrip) ∧
        (∃ (fineConfig : NiceConfiguration (n - m) s (K_fine * C₁) MQ),
          fineConfig.points = P_Q'.image (squareHomothety hnm Q) ∧
          fineConfig.tubes = fineConfig.points.biUnion (fun q =>
            if hq : q ∈ fineConfig.points then fineConfig.tubeFamily q hq else ∅) ∧
          (∀ p (hp : p ∈ P_Q'),
            ∃ hq : squareHomothety hnm Q p ∈ fineConfig.points,
              (fineConfig.tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
                (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a))) := by
    intro Q hQ
    let hQ_in : Q ∈ QSet := hQSet'_sub' hQ
    let candRet_Q_p (p : DyadicSquare n) : Finset (DyadicTube n) := candRet_Q Q hQ p
    have hP_Q_contained : ∀ p ∈ P_Q Q, squareContained hnm p Q := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h_orig_sset : ∀ p ∈ P_Q Q, IsFiniteTubeSSet s C₁ (originalFamily p) := by
      intro p hp
      have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
      simpa [originalFamily, NiceConfiguration.tubeFamilyOpt, hpin] using config.h_sset p hpin
    have h_orig_size : ∀ p ∈ P_Q Q, (originalFamily p).card = M := by
      intro p hp
      have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
      simpa [originalFamily, NiceConfiguration.tubeFamilyOpt, hpin] using config.h_size p hpin
    have h_candRet_sub : ∀ p ∈ P_Q Q, candRet_Q_p p ⊆ originalFamily p := by
      intro p hp
      intro T hT
      simp only [candRet_Q_p, candRet_Q] at hT
      exact (Finset.mem_filter.mp hT).1
    have h_candRet_incidence : ∀ p ∈ P_Q Q, ∀ T ∈ candRet_Q_p p,
        (T.toSet ∩ p.toSet).Nonempty := by
      intro p hp T hT
      have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
      have h4 : T ∈ config.tubeFamilyOpt p := by
        simp only [candRet_Q_p, candRet_Q] at hT
        exact (Finset.mem_filter.mp hT).1
      have hT_in : T ∈ config.tubeFamily p hpin := by
        simpa [NiceConfiguration.tubeFamilyOpt, hpin] using h4
      exact config.h_incidence p hpin T hT_in
    have h_candRet_params : ∀ p ∈ P_Q Q, ∀ T ∈ candRet_Q_p p,
        T.IsInAllowedParameterStrip := by
      intro p hp T hT
      have hpin : p ∈ config.points := (Finset.mem_filter.mp hp).1
      have h4 : T ∈ config.tubeFamilyOpt p := by
        simp only [candRet_Q_p, candRet_Q] at hT
        exact (Finset.mem_filter.mp hT).1
      have hT_in : T ∈ config.tubeFamily p hpin := by
        simpa [NiceConfiguration.tubeFamilyOpt, hpin] using h4
      have hT_in_tubes : T ∈ config.tubes := config.h_subset p hpin hT_in
      exact config.h_tube_parameters T hT_in_tubes
    have h_retention_sum : (∑ p ∈ P_Q Q, (candRet_Q_p p).card : ℝ) ≥
        ((P_Q Q).card : ℝ) * (M : ℝ) / K_cpd := by
      have h1 := h_retention_per_Q Q hQ
      have h2 : K_cpd = 2 * K_Qmax * K_fiber_loss := by rfl
      rw [h2]
      have h3 : (M : ℝ) * ((P_Q Q).card : ℝ) / (2 * K_Qmax * K_fiber_loss) =
          ((P_Q Q).card : ℝ) * (M : ℝ) / (2 * K_Qmax * K_fiber_loss) := by ring
      rw [h3] at h1
      exact h1
    exact per_q_steps_8_10_with_sset hnm s hs hs_one C₁ hC₁ M hM config Q
      (P_Q Q) (hP_Q_nonempty Q hQ_in)
      (fun p hp => (Finset.mem_filter.mp hp).1)
      hP_Q_contained originalFamily h_orig_sset h_orig_size
      candRet_Q_p h_candRet_sub h_candRet_incidence h_candRet_params
      K_cpd hK_cpd_one h_retention_sum

  classical
  choose P_Q' hP_Q'_sub hP_Q'_nonempty uniformFamily_Q m_Q_fn MQ_fn hmQ_pos_fn hMQ_pos_fn
    K_ret_fn K_loss_fn K_fine_fn hK_ret_fn hK_ret_eq_fn hK_loss_fn hK_loss_eq_fn hK_fine_fn hK_fine_eq_fn
    h_unif_sub h_unif_ret h_unif_coverage h_unif_sset h_unif_packets h_unif_cells
    h_unif_inc h_unif_strip h_fine_data
    using h_step8_10

  -- Total wrappers for choose results (biUnion needs total functions)
  let P_Q'_total (Q : DyadicSquare m) : Finset (DyadicSquare n) :=
    if hQ : Q ∈ QSet' then P_Q' Q hQ else ∅

  -- Combine per-Q results
  let P' : Finset (DyadicSquare n) := QSet'.biUnion P_Q'_total

  have hP'_elim : ∀ p ∈ P', ∃ (Q : DyadicSquare m) (hQ : Q ∈ QSet'),
      p ∈ P_Q' Q hQ ∧ containingSquare hnm p = Q := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨Q, hQ, hpQ'⟩
    have hpQ'_real : p ∈ P_Q' Q hQ := by
      simpa [P_Q'_total, dif_pos hQ] using hpQ'
    have h_cont : squareContained hnm p Q := by
      have h1 : p ∈ P_Q Q := hP_Q'_sub Q hQ hpQ'_real
      exact (Finset.mem_filter.mp h1).2
    have h_eq : containingSquare hnm p = Q :=
      (squareContained_iff_containingSquare hnm p Q).mp h_cont
    exact ⟨Q, hQ, hpQ'_real, h_eq⟩

  have hP'_nonempty : P'.Nonempty := by
    rcases hQSet'_nonempty with ⟨Q, hQ⟩
    have h1 : (P_Q' Q hQ).Nonempty := hP_Q'_nonempty Q hQ
    rcases h1 with ⟨p, hp⟩
    have h2 : p ∈ P' := by
      apply Finset.mem_biUnion.mpr
      exact ⟨Q, hQ, by simpa [P_Q'_total, dif_pos hQ] using hp⟩
    exact ⟨p, h2⟩

  have hP'_sub : P' ⊆ config.points := by
    intro p hp
    rcases hP'_elim p hp with ⟨Q, hQ, hpQ', _⟩
    have h1 : p ∈ P_Q Q := hP_Q'_sub Q hQ hpQ'
    exact (Finset.mem_filter.mp h1).1

  have hP'_image : P'.image (containingSquare hnm) = QSet' := by
    apply Finset.ext
    intro Q
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hP'_elim p hp with ⟨Q0, hQ0, _, h_eq⟩
      rw [h_eq] <;> exact hQ0
    · intro hQ
      have h1 : (P_Q' Q hQ).Nonempty := hP_Q'_nonempty Q hQ
      rcases h1 with ⟨p, hp⟩
      have h2 : p ∈ P' := by
        apply Finset.mem_biUnion.mpr
        exact ⟨Q, hQ, by simpa [P_Q'_total, dif_pos hQ] using hp⟩
      have h3 : squareContained hnm p Q := by
        have h4 : p ∈ P_Q Q := hP_Q'_sub Q hQ hp
        exact (Finset.mem_filter.mp h4).2
      have h5 : containingSquare hnm p = Q :=
        (squareContained_iff_containingSquare hnm p Q).mp h3
      exact ⟨p, h2, h5⟩

  -- Global uniformFamily
  let Q_p (p : DyadicSquare n) : DyadicSquare m := containingSquare hnm p

  have hQ_p_of_P' : ∀ (p : DyadicSquare n), p ∈ P' → Q_p p ∈ QSet' := by
    intro p hp
    rcases hP'_elim p hp with ⟨Q, hQ, _, h_eq⟩
    have h : Q_p p = Q := h_eq
    rw [h]
    exact hQ

  have hpQ'_of_P' : ∀ (p : DyadicSquare n) (hp : p ∈ P'),
      p ∈ P_Q' (Q_p p) (hQ_p_of_P' p hp) := by
    intro p hp
    rcases hP'_elim p hp with ⟨Q, hQ, hpQ', h_eq⟩
    have hQ_eq : Q = Q_p p := h_eq.symm
    subst hQ_eq
    exact hpQ'

  let uniformFamily (p : DyadicSquare n) (hp : p ∈ P') : Finset (DyadicTube n) :=
    uniformFamily_Q (Q_p p) (hQ_p_of_P' p hp) p (hpQ'_of_P' p hp)

  -- Global MQ
  let MQ (Q : DyadicSquare m) : ℕ :=
    if hQ : Q ∈ QSet' then MQ_fn Q hQ else 1

  have hMQ_pos : ∀ Q ∈ coarseConfig.points, 0 < MQ Q := by
    intro Q hQ
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    simp [MQ, hQ'] <;> exact hMQ_pos_fn Q hQ'

  -- K factors
  let K_ret : ℝ := 4 * K_Qmax * K_fiber_loss
  let K_loss : ℝ := 16 * (numDyadicLevels M : ℝ)^2
  let K_fine : ℝ := K_loss * K_ret * Real.rpow 16 s

  have hK_ret_eq : ∀ Q hQ, K_ret_fn Q hQ = K_ret := by
    intro Q hQ
    have h1 : K_ret_fn Q hQ = 2 * K_cpd := hK_ret_eq_fn Q hQ
    have h2 : K_cpd = 2 * K_Qmax * K_fiber_loss := by rfl
    rw [h1, h2] <;> ring
  have hK_loss_eq : ∀ Q hQ, K_loss_fn Q hQ = K_loss := by
    intro Q hQ
    exact hK_loss_eq_fn Q hQ
  have hK_fine_eq : ∀ Q hQ, K_fine_fn Q hQ = K_fine := by
    intro Q hQ
    have h1 : K_fine_fn Q hQ = K_loss_fn Q hQ * K_ret_fn Q hQ * Real.rpow 16 s := hK_fine_eq_fn Q hQ
    have h2 : K_loss_fn Q hQ * K_ret_fn Q hQ * Real.rpow 16 s = K_fine := by
      rw [hK_loss_eq Q hQ, hK_ret_eq Q hQ] <;> rfl
    rw [h1, h2]

  let K_base : ℝ := K_fine
  let L_size : ℕ := numDyadicLevels max_size
  let K : ℝ := 24 * (L_size : ℝ) * K_base
  have hL_size_pos : 0 < L_size := by
    simp [L_size, numDyadicLevels, max_size] <;> omega
  have hL_size_two : 2 ≤ (L_size : ℝ) := by
    simp [L_size, numDyadicLevels, max_size] <;> omega
  have hK_fiber_loss_one : 1 ≤ K_fiber_loss := hK_loss_one

  have hCΔ_def' : CΔ = 2 * K_fiber_loss * K_Qmax * C₁ := by
    have h1 : CΔ = CΔ_new := by rfl
    rw [h1]
    have h2 : CΔ_new = 2 * K_loss_fiber * C₂_max := hCΔ_eq
    rw [h2]
    have h3 : C₂_max = K_Qmax * C₁ := by rfl
    rw [h3] <;> ring

  have hK_factors := induction_step_K_factors
    s hs hs_one M hM K_Qmax hK_Qmax_pos hK_Qmax_one L_size hL_size_pos hL_size_two
    C₁ hC₁ K_fiber_loss hK_fiber_loss_one CΔ hCΔ_def'
    K_ret K_loss K_fine K rfl rfl rfl rfl
  rcases hK_factors with ⟨hK_ret_one, hK_loss_one2, hK_fine_one, hK_one, hK_ret_loss_le, h_CΔ_le, h_C₁_le, h_K_cover, h_K_36⟩

  have hK_Qmax_eq : K_Qmax = 32 * (numDyadicLevels M : ℝ) * (numDyadicLevels (config.points.card * M) : ℝ) := by
    simp [K_Qmax, numDyadicLevels] <;> ring
  have hK_fiber_loss_eq' : K_fiber_loss = 2 * (numDyadicLevels config.tubes.card : ℝ)^2 := hK_fiber_loss_eq
  have hK_eq : K = 98304 * (numDyadicLevels max_size : ℝ) *
      (numDyadicLevels M : ℝ)^3 *
      (numDyadicLevels (config.points.card * M) : ℝ) *
      (numDyadicLevels config.tubes.card : ℝ)^2 *
      Real.rpow 16 s := by
    dsimp only [K, K_base, K_fine, K_loss, K_ret, L_size]
    rw [hK_Qmax_eq, hK_fiber_loss_eq'] <;> ring

  -- Polynomial bound on K
  have h_points_bound : config.points.card ≤ 4 ^ n := by
    have h : (config.points.card : ℝ) ≤ 1 / (dyadicDelta n)^2 := point_count_bound config
    have h9 : (1 : ℝ) / (dyadicDelta n)^2 = (4 ^ n : ℝ) := by
      have h10 : dyadicDelta n = 1 / (2 ^ n : ℝ) := by
        simp [dyadicDelta_eq_inv] <;> field_simp
      rw [h10]
      have h11 : (1 : ℝ) / (1 / (2 ^ n : ℝ)) ^ 2 = ((2 ^ n : ℝ) ^ 2) := by
        have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
        field_simp [h_pos.ne'] <;> ring
      rw [h11]
      have h12 : (2 ^ n : ℝ) ^ 2 = (4 ^ n : ℝ) := by
        have h13 : (2 ^ n : ℕ) ^ 2 = 4 ^ n := by
          have h14 : (2 ^ n : ℕ) ^ 2 = 2 ^ (n * 2) := by rw [pow_mul]
          rw [h14]
          have h15 : n * 2 = 2 * n := by ring
          rw [h15]
          have h16 : 2 ^ (2 * n) = (2 ^ 2) ^ n := by
            rw [← pow_mul] <;> ring
          rw [h16] <;> norm_num
        exact_mod_cast h13
      exact h12
    rw [h9] at h
    exact_mod_cast h

  have hM_le : M ≤ config.tubes.card := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h1 : config.tubeFamily p hp ⊆ config.tubes := config.h_subset p hp
    have h2 : (config.tubeFamily p hp).card = M := config.h_size p hp
    have h3 : (config.tubeFamily p hp).card ≤ config.tubes.card := Finset.card_le_card h1
    rw [h2] at h3
    exact h3

  have h_tubes_pos : 0 < config.tubes.card := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h1 : (config.tubeFamily p hp).card = M := config.h_size p hp
    have h2 : 0 < (config.tubeFamily p hp).card := by
      rw [h1] <;> exact hM
    have h3 : config.tubeFamily p hp ⊆ config.tubes := config.h_subset p hp
    have h4 : (config.tubeFamily p hp).card ≤ config.tubes.card := Finset.card_le_card h3
    exact lt_of_lt_of_le h2 h4

  have h_fiber_pos_general : ∀ (Q : DyadicSquare m), Q ∈ QSet → ∀ U ∈ coarseTubes_Q Q,
      0 < fiberSize hnm config.tubes U := by
    intro Q hQ U hU
    have hQ_in : Q ∈ QSet := hQ
    let d := perQData Q hQ_in
    have h_eq1 : coarseTubes_Q Q = d.coarseTubes_Q := by
      dsimp only [coarseTubes_Q]
      rw [dif_pos hQ_in] <;> rfl
    have hU' : U ∈ d.coarseTubes_Q := by rw [h_eq1] at hU <;> exact hU
    have h_sum : (d.H_Q : ℝ) ≤ ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) :=
      d.h_popularity U hU'
    have h_sum_pos : 0 < ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) := by
      have hH : (1 : ℝ) ≤ d.H_Q := d.hH_Q
      linarith
    have h_exists : ∃ (p : DyadicSquare n), p ∈ P_Q Q ∧ 0 < countInCoarse hnm (config.tubeFamilyOpt p) U := by
      by_contra h
      push Not at h
      have h_all_zero : ∀ p ∈ P_Q Q, countInCoarse hnm (config.tubeFamilyOpt p) U = 0 := by
        intro p hp
        have h4 : _ ≤ 0 := h p hp
        omega
      have h_sum_zero : ∑ p ∈ P_Q Q, (countInCoarse hnm (config.tubeFamilyOpt p) U : ℝ) = 0 := by
        rw [Finset.sum_congr rfl (fun p hp => by rw [h_all_zero p hp] <;> norm_cast)] <;> simp
      rw [h_sum_zero] at h_sum_pos
      linarith
    rcases h_exists with ⟨p, hpQ, hpos⟩
    have h_filter_nonempty : ((config.tubeFamilyOpt p).filter (fun T => coarseAnc hnm T = U)).Nonempty :=
      Finset.card_pos.mp (by simpa [countInCoarse] using hpos)
    rcases h_filter_nonempty with ⟨T, hT_in⟩
    have hT_in_F : T ∈ config.tubeFamilyOpt p := (Finset.mem_filter.mp hT_in).1
    have hT_eq : coarseAnc hnm T = U := (Finset.mem_filter.mp hT_in).2
    have hp' : p ∈ config.points := (Finset.mem_filter.mp hpQ).1
    have hT_in_family : T ∈ config.tubeFamily p hp' := by
      have h_opt : config.tubeFamilyOpt p = config.tubeFamily p hp' := by
        simp [NiceConfiguration.tubeFamilyOpt, hp']
      rw [h_opt] at hT_in_F <;> exact hT_in_F
    have hT_in_tubes : T ∈ config.tubes := config.h_subset p hp' hT_in_family
    have h_contain : T.toSet ⊆ U.toSet := by
      have h : T.toSet ⊆ (coarseAnc hnm T).toSet := coarseAnc_contains hnm T
      rw [hT_eq] at h <;> exact h
    have h_in_fiber : T ∈ config.tubes.filter (fun T => T.toSet ⊆ U.toSet) :=
      Finset.mem_filter.mpr ⟨hT_in_tubes, h_contain⟩
    exact Finset.card_pos.mpr ⟨T, h_in_fiber⟩

  have h_max_size_le : max_size ≤ config.tubes.card := by
    apply Finset.sup_le
    intro Q hQ
    have h1 : ∀ U ∈ coarseTubes_Q Q, 0 < fiberSize hnm config.tubes U :=
      h_fiber_pos_general Q hQ
    have h2 : (coarseTubes_Q Q).card ≤ ∑ U ∈ coarseTubes_Q Q, fiberSize hnm config.tubes U := by
      have h21 : ∑ U ∈ coarseTubes_Q Q, (1 : ℕ) = (coarseTubes_Q Q).card := by simp
      have h22 : ∑ U ∈ coarseTubes_Q Q, (1 : ℕ) ≤ ∑ U ∈ coarseTubes_Q Q, fiberSize hnm config.tubes U := by
        apply Finset.sum_le_sum
        intro U hU
        exact h1 U hU
      rw [h21] at h22
      exact h22
    have h3 : ∑ U ∈ coarseTubes_Q Q, fiberSize hnm config.tubes U ≤ config.tubes.card :=
      fiber_sum_le_total hnm config.tubes (coarseTubes_Q Q)
    exact le_trans h2 h3

  have hK_poly : K ≤ 3145728 * (4 * (n : ℝ) + 7)^7 :=
    prove_K_poly_bound_36 h_tubes_bounded K max_size hK_eq h_max_size_le hM_le hP_nonempty hM hs_one hs

  have hK_eq' : K = 98304 * (numDyadicLevels max_size : ℝ) *
      (numDyadicLevels M : ℝ)^3 *
      (numDyadicLevels (config.points.card * M) : ℝ) *
      (numDyadicLevels config.tubes.card : ℝ)^2 *
      Real.rpow 16 s := hK_eq

  have hK_fine_le : ∀ Q hQ, K_fine_fn Q hQ ≤ K := by
    intro Q hQ
    have h1 : K_fine_fn Q hQ = K_fine := hK_fine_eq Q hQ
    rw [h1]
    dsimp only [K, K_base]
    have hL_one : 1 ≤ (L_size : ℝ) := by exact_mod_cast hL_size_pos
    have h7 : 0 ≤ K_fine := le_trans zero_le_one hK_fine_one
    have h9 : 1 ≤ 24 * (L_size : ℝ) := by
      have h10 : 2 ≤ (L_size : ℝ) := hL_size_two
      nlinarith
    calc K_fine
      = 1 * K_fine := by ring
    _ ≤ 24 * (L_size : ℝ) * K_fine := mul_le_mul_of_nonneg_right h9 h7

  -- Per-Q fine configs
  classical
  choose fineConfig_Q hfine_points hfine_tubes_eq hfine_slope using h_fine_data

  let CQ (Q : DyadicSquare m) : ℝ :=
    if hQ : Q ∈ QSet' then K_fine_fn Q hQ * C₁ else C₁

  let fineConfig (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points) :
      NiceConfiguration (n - m) s (CQ Q) (MQ Q) :=
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    let fc := fineConfig_Q Q hQ'
    have hCQ : CQ Q = K_fine_fn Q hQ' * C₁ := by simp [CQ, hQ']
    have hMQ : MQ Q = MQ_fn Q hQ' := by simp [MQ, hQ']
    let tubes' := fc.points.biUnion (fun q => if hq : q ∈ fc.points then fc.tubeFamily q hq else ∅)
    have h_subset' : ∀ (p : DyadicSquare (n - m)) (hp : p ∈ fc.points), fc.tubeFamily p hp ⊆ tubes' := by
      intro p hp
      intro U hU
      exact Finset.mem_biUnion.mpr ⟨p, hp, by simp [hp, hU]⟩
    have h_tube_params' : ∀ (U : DyadicTube (n - m)), U ∈ tubes' → U.IsInAllowedParameterStrip := by
      intro U hU
      rcases Finset.mem_biUnion.mp hU with ⟨q, hq, hU'⟩
      have hU_in_fc : U ∈ fc.tubes := fc.h_subset q hq (by simpa [hq] using hU')
      exact fc.h_tube_parameters U hU_in_fc
    { points := fc.points,
      tubes := tubes',
      tubeFamily := fun p hp => fc.tubeFamily p hp,
      h_subset := h_subset',
      h_size := fun p hp =>
        have h : (fc.tubeFamily p hp).card = MQ_fn Q hQ' := fc.h_size p hp
        Eq.trans h hMQ.symm,
      h_sset := fun p hp =>
        have h : IsFiniteTubeSSet s (K_fine_fn Q hQ' * C₁) (fc.tubeFamily p hp) := fc.h_sset p hp
        have h' : IsFiniteTubeSSet s (CQ Q) (fc.tubeFamily p hp) := by
          rw [show CQ Q = K_fine_fn Q hQ' * C₁ from hCQ]
          exact h
        h',
      h_incidence := fc.h_incidence,
      h_bounded := fc.h_bounded,
      h_tube_parameters := h_tube_params' }

  -- Output properties
  have h_final_sub : ∀ p (hp : p ∈ P'),
      uniformFamily p hp ⊆ config.tubeFamily p (hP'_sub hp) := by
    intro p hp
    let Q_p := Q_p p
    have hQ_p : Q_p ∈ QSet' := hQ_p_of_P' p hp
    have hpQ' : p ∈ P_Q' Q_p hQ_p := hpQ'_of_P' p hp
    have h1 : uniformFamily p hp ⊆ candRet_Q Q_p hQ_p p :=
      h_unif_sub Q_p hQ_p p hpQ'
    have hpin : p ∈ config.points := hP'_sub hp
    have hpinPQ : p ∈ P_Q Q_p := hP_Q'_sub Q_p hQ_p hpQ'
    have h2 : candRet_Q Q_p hQ_p p ⊆ config.tubeFamily p hpin := by
      intro T hT
      simp only [candRet_Q] at hT
      have h4 : T ∈ config.tubeFamilyOpt p := (Finset.mem_filter.mp hT).1
      simpa [NiceConfiguration.tubeFamilyOpt, hpin] using h4
    exact Finset.Subset.trans h1 h2

  have h_final_retention : ∀ p (hp : p ∈ P'),
      (M : ℝ) ≤ K * ((uniformFamily p hp).card : ℝ) := by
    intro p hp
    let Q_p := Q_p p
    have hQ_p : Q_p ∈ QSet' := hQ_p_of_P' p hp
    have hpQ' : p ∈ P_Q' Q_p hQ_p := hpQ'_of_P' p hp
    have hK1 : K_ret_fn Q_p hQ_p = K_ret := hK_ret_eq Q_p hQ_p
    have hK2 : K_loss_fn Q_p hQ_p = K_loss := hK_loss_eq Q_p hQ_p
    have h1 : (M : ℝ) ≤ K_ret_fn Q_p hQ_p * K_loss_fn Q_p hQ_p * ((uniformFamily p hp).card : ℝ) :=
      h_unif_ret Q_p hQ_p p hpQ'
    rw [hK1, hK2] at h1
    have h2 : K_ret * K_loss ≤ K := hK_ret_loss_le
    let c : ℝ := ↑(uniformFamily p hp).card
    have hc_nonneg : 0 ≤ c := by
      dsimp only [c]
      exact Nat.cast_nonneg _
    have h3 : K_ret * K_loss * c ≤ K * c :=
      mul_le_mul_of_nonneg_right h2 hc_nonneg
    exact le_trans h1 h3

  have h_final_sset : ∀ p (hp : p ∈ P'),
      IsFiniteTubeSSet s (K * C₁) (uniformFamily p hp) := by
    intro p hp
    let Q_p := Q_p p
    have hQ_p : Q_p ∈ QSet' := hQ_p_of_P' p hp
    have hpQ' : p ∈ P_Q' Q_p hQ_p := hpQ'_of_P' p hp
    have hK1 : K_ret_fn Q_p hQ_p = K_ret := hK_ret_eq Q_p hQ_p
    have hK2 : K_loss_fn Q_p hQ_p = K_loss := hK_loss_eq Q_p hQ_p
    have h1 : IsFiniteTubeSSet s (K_loss_fn Q_p hQ_p * K_ret_fn Q_p hQ_p * C₁) (uniformFamily p hp) :=
      h_unif_sset Q_p hQ_p p hpQ'
    rw [hK2, hK1] at h1
    have h2 : K_loss * K_ret * C₁ ≤ K * C₁ := by
      have h3 : K_loss * K_ret ≤ K := by
        have h4 : K_ret * K_loss ≤ K := hK_ret_loss_le
        rwa [mul_comm K_ret K_loss] at h4
      have h4 : 0 ≤ C₁ := by linarith [hC₁]
      gcongr
    exact IsFiniteTubeSSet.monotone_const h2 h1

  have h_final_incidence : ∀ p (hp : p ∈ P') T,
      T ∈ uniformFamily p hp → (T.toSet ∩ p.toSet).Nonempty := by
    intro p hp T hT
    let Q_p := Q_p p
    have hQ_p : Q_p ∈ QSet' := hQ_p_of_P' p hp
    have hpQ' : p ∈ P_Q' Q_p hQ_p := hpQ'_of_P' p hp
    exact h_unif_inc Q_p hQ_p p hpQ' T hT

  have h_final_containment : ∀ p (hp : p ∈ P') T,
      T ∈ uniformFamily p hp →
        ∃ (hQ : containingSquare hnm p ∈ coarseConfig.points)
          (U : DyadicTube m),
          U ∈ coarseConfig.tubeFamily (containingSquare hnm p) hQ ∧
          T.toSet ⊆ U.toSet := by
    intro p hp T hT
    let Q_p := Q_p p
    have hQ_p : Q_p ∈ QSet' := hQ_p_of_P' p hp
    have hpQ' : p ∈ P_Q' Q_p hQ_p := hpQ'_of_P' p hp
    have h1 : T ∈ candRet_Q Q_p hQ_p p := h_unif_sub Q_p hQ_p p hpQ' hT
    have hpin : p ∈ config.points := hP'_sub hp
    have h2 : coarseAnc hnm T ∈ trimmedFamily Q_p hQ_p := by
      have h3 : candRet_Q Q_p hQ_p p = (config.tubeFamily p hpin).filter (fun T => coarseAnc hnm T ∈ trimmedFamily Q_p hQ_p) := by
        simp [candRet_Q, NiceConfiguration.tubeFamilyOpt, hpin] <;> rfl
      rw [h3] at h1
      exact (Finset.mem_filter.mp h1).2
    have h4 : Q_p ∈ coarseConfig.points := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] <;> exact hQ_p
    have h2' : coarseAnc hnm T ∈ coarseConfig.tubeFamily Q_p h4 := by
      have h_fam : coarseConfig.tubeFamily Q_p h4 = trimmedFamily_new Q_p := h_tubeFamily_new Q_p h4
      rw [h_fam]
      exact h2
    have h5 : T.toSet ⊆ (coarseAnc hnm T).toSet := coarseAnc_contains hnm T
    exact ⟨h4, coarseAnc hnm T, h2', h5⟩

  have h_global_coverage : ((config.points.image (containingSquare hnm)).card : ℝ) ≤
      K * (coarseConfig.points.card : ℝ) := by
    have h1 : (QSet.card : ℝ) ≤ (2 * (L : ℝ)) * (QSet_band.card : ℝ) := by
      convert h_retention_QSet using 1 <;> rfl
    have h2 : (QSet_band.card : ℝ) ≤ K_fiber_loss * (QSet'.card : ℝ) := hQSet'_cover_updated
    have h3 : (2 * (L_size : ℝ) * K_fiber_loss) ≤ K := h_K_cover
    have h4 : coarseConfig.points = QSet' := h_points_new
    have h5 : (L : ℝ) = (L_size : ℝ) := by rfl
    rw [h4]
    rw [h5] at h1
    have h6 : 0 ≤ (QSet'.card : ℝ) := Nat.cast_nonneg _
    have h7 : 0 ≤ (QSet_band.card : ℝ) := Nat.cast_nonneg _
    have h8 : (QSet.card : ℝ) ≤ (2 * (L_size : ℝ) * K_fiber_loss) * (QSet'.card : ℝ) := by
      calc (QSet.card : ℝ)
        ≤ (2 * (L_size : ℝ)) * (QSet_band.card : ℝ) := h1
      _ ≤ (2 * (L_size : ℝ)) * (K_fiber_loss * (QSet'.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * (L_size : ℝ) * K_fiber_loss) * (QSet'.card : ℝ) := by ring
    have h9 : (2 * (L_size : ℝ) * K_fiber_loss) * (QSet'.card : ℝ) ≤ K * (QSet'.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right h3 h6
    exact le_trans h8 h9

  have h_per_Q_coverage : ∀ Q ∈ coarseConfig.points,
      ((config.points.filter fun p => squareContained hnm p Q).card : ℝ) ≤
        K * ((P'.filter fun p => squareContained hnm p Q).card : ℝ) := by
    intro Q hQ
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    have hK1 : K_ret_fn Q hQ' = K_ret := hK_ret_eq Q hQ'
    have hK2 : K_loss_fn Q hQ' = K_loss := hK_loss_eq Q hQ'
    have h1 : ((P_Q Q).card : ℝ) ≤
        K_ret * K_loss * ((P_Q' Q hQ').card : ℝ) := by
      have h1_raw := h_unif_coverage Q hQ'
      rw [hK1, hK2] at h1_raw
      exact h1_raw
    have h2 : P_Q' Q hQ' = P'.filter (fun p => squareContained hnm p Q) := by
      apply Finset.ext
      intro p
      simp only [P', Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · intro hp
        have h3 : squareContained hnm p Q := by
          have h4 : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
          exact (Finset.mem_filter.mp h4).2
        have hp_total : p ∈ P_Q'_total Q := by
          simpa [P_Q'_total, dif_pos hQ'] using hp
        exact ⟨⟨Q, hQ', hp_total⟩, h3⟩
      · rintro ⟨⟨Q0, hQ0, hp0⟩, hsc⟩
        have hp0' : p ∈ P_Q' Q0 hQ0 := by
          simpa [P_Q'_total, dif_pos hQ0] using hp0
        have h_eq : Q0 = Q := by
          have h4 : squareContained hnm p Q0 := by
            have h5 : p ∈ P_Q Q0 := hP_Q'_sub Q0 hQ0 hp0'
            exact (Finset.mem_filter.mp h5).2
          have h5 : containingSquare hnm p = Q0 :=
            (squareContained_iff_containingSquare hnm p Q0).mp h4
          have h6 : containingSquare hnm p = Q :=
            (squareContained_iff_containingSquare hnm p Q).mp hsc
          rw [h5] at h6; exact h6
        subst h_eq
        exact hp0'
    rw [h2] at h1
    have h3 : K_ret * K_loss ≤ K := hK_ret_loss_le
    have h4 : 0 ≤ ((P'.filter (fun p => squareContained hnm p Q)).card : ℝ) := Nat.cast_nonneg _
    calc ((P_Q Q).card : ℝ)
      ≤ K_ret * K_loss * ((P'.filter (fun p => squareContained hnm p Q)).card : ℝ) := h1
    _ ≤ K * ((P'.filter (fun p => squareContained hnm p Q)).card : ℝ) :=
      mul_le_mul_of_nonneg_right h3 h4

  have h_CQ_bounds : ∀ Q ∈ coarseConfig.points,
      CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q := by
    intro Q hQ
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    have hCQ_eq : CQ Q = K_fine_fn Q hQ' * C₁ := by
      simp [CQ, hQ']
    constructor
    · rw [hCQ_eq]
      have h1 : K_fine_fn Q hQ' ≤ K := hK_fine_le Q hQ'
      have h2 : 0 ≤ C₁ := le_trans zero_le_one hC₁
      exact mul_le_mul_of_nonneg_right h1 h2
    · rw [hCQ_eq]
      have h1 : 1 ≤ K_fine_fn Q hQ' := hK_fine_fn Q hQ'
      have h2 : 0 ≤ C₁ := by linarith [hC₁]
      have h3 : C₁ ≤ K_fine_fn Q hQ' * C₁ := by
        calc C₁ = 1 * C₁ := by ring
        _ ≤ K_fine_fn Q hQ' * C₁ := mul_le_mul_of_nonneg_right h1 h2
      have h4 : 0 ≤ K_fine_fn Q hQ' * C₁ := mul_nonneg (le_trans zero_le_one h1) h2
      have h6 : 1 ≤ K := hK_one
      have h5 : K_fine_fn Q hQ' * C₁ ≤ K * (K_fine_fn Q hQ' * C₁) :=
        le_mul_of_one_le_left h4 h6
      exact le_trans h3 h5

  have h_fine_points : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points),
      (fineConfig Q hQ).points =
        (P'.filter fun p => squareContained hnm p Q).image (squareHomothety hnm Q) := by
    intro Q hQ
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    have h_eq : P_Q' Q hQ' = P'.filter (fun p => squareContained hnm p Q) := by
      apply Finset.ext
      intro p
      simp only [P', Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · intro hp
        have h3 : squareContained hnm p Q := by
          have h4 : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
          exact (Finset.mem_filter.mp h4).2
        have hp_total : p ∈ P_Q'_total Q := by
          simpa [P_Q'_total, dif_pos hQ'] using hp
        exact ⟨⟨Q, hQ', hp_total⟩, h3⟩
      · rintro ⟨⟨Q0, hQ0, hp0⟩, hsc⟩
        have hp0' : p ∈ P_Q' Q0 hQ0 := by
          simpa [P_Q'_total, dif_pos hQ0] using hp0
        have h_eq2 : Q0 = Q := by
          have h4 : squareContained hnm p Q0 := by
            have h5 : p ∈ P_Q Q0 := hP_Q'_sub Q0 hQ0 hp0'
            exact (Finset.mem_filter.mp h5).2
          have h5 : containingSquare hnm p = Q0 :=
            (squareContained_iff_containingSquare hnm p Q0).mp h4
          have h6 : containingSquare hnm p = Q :=
            (squareContained_iff_containingSquare hnm p Q).mp hsc
          rw [h5] at h6; exact h6
        subst h_eq2
        exact hp0'
    have hpts : (fineConfig_Q Q hQ').points = (P_Q' Q hQ').image (squareHomothety hnm Q) :=
      hfine_points Q hQ'
    rw [h_eq] at hpts
    have h_goal : (fineConfig Q hQ).points = (P'.filter fun p => squareContained hnm p Q).image (squareHomothety hnm Q) := by
      have h_eq_config : (fineConfig Q hQ).points = (fineConfig_Q Q hQ').points := by
        dsimp only [fineConfig]
        <;> rfl
      rw [h_eq_config]
      exact hpts
    exact h_goal

  have h_fine_slope : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points),
      ∀ p, ∀ hp : p ∈ P', squareContained hnm p Q →
        ∃ hq : squareHomothety hnm Q p ∈ (fineConfig Q hQ).points,
          ((fineConfig Q hQ).tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
            (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) := by
    intro Q hQ p hp hsc
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    have hpQ' : p ∈ P_Q' Q hQ' := by
      rcases Finset.mem_biUnion.mp hp with ⟨Q0, hQ0, hp0⟩
      have hp0' : p ∈ P_Q' Q0 hQ0 := by
        simpa [P_Q'_total, dif_pos hQ0] using hp0
      have h_eq : Q0 = Q := by
        have h4 : squareContained hnm p Q0 := by
          have h5 : p ∈ P_Q Q0 := hP_Q'_sub Q0 hQ0 hp0'
          exact (Finset.mem_filter.mp h5).2
        have h5 : containingSquare hnm p = Q0 :=
          (squareContained_iff_containingSquare hnm p Q0).mp h4
        have h6 : containingSquare hnm p = Q :=
          (squareContained_iff_containingSquare hnm p Q).mp hsc
        rw [h5] at h6; exact h6
      subst h_eq
      exact hp0'
    let hq : squareHomothety hnm Q p ∈ (fineConfig_Q Q hQ').points :=
      Classical.choose (hfine_slope Q hQ' p hpQ')
    have h_eq : ((fineConfig_Q Q hQ').tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) =
        (uniformFamily_Q Q hQ' p hpQ').image (fun T => localSlopeCellIndex m T.a) :=
      Classical.choose_spec (hfine_slope Q hQ' p hpQ')
    have hq' : squareHomothety hnm Q p ∈ (fineConfig Q hQ).points := by
      dsimp only [fineConfig]
      exact hq
    have h_eq2 : ((fineConfig Q hQ).tubeFamily (squareHomothety hnm Q p) hq').image (fun U => U.a) =
        ((fineConfig_Q Q hQ').tubeFamily (squareHomothety hnm Q p) hq).image (fun U => U.a) := by
      dsimp only [fineConfig] <;> rfl
    have hQp_eq : Q_p p = Q := by
      have h_contained : squareContained hnm p Q := by
        have h5 : p ∈ P_Q Q := hP_Q'_sub Q hQ' hpQ'
        exact (Finset.mem_filter.mp h5).2
      have h6 : containingSquare hnm p = Q := (squareContained_iff_containingSquare hnm p Q).mp h_contained
      exact h6
    have h_eq3 : (uniformFamily_Q Q hQ' p hpQ').image (fun T => localSlopeCellIndex m T.a) =
        (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) := by
      dsimp only [uniformFamily]
      subst hQp_eq
      <;> rfl
    have h_main : ((fineConfig Q hQ).tubeFamily (squareHomothety hnm Q p) hq').image (fun U => U.a) =
        (uniformFamily p hp).image (fun T => localSlopeCellIndex m T.a) :=
      Eq.trans h_eq2 (Eq.trans h_eq h_eq3)
    exact ⟨hq', h_main⟩

  -- Cardinality (5.5)
  have h_cardinality : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points),
      K * (config.tubes.card : ℝ) * MΔ * MQ Q ≥
        (coarseConfig.tubes.card : ℝ) *
          ((fineConfig Q hQ).tubes.card : ℝ) * M := by
    intro Q hQ
    have hQ' : Q ∈ QSet' := by
      have h_eq : coarseConfig.points = QSet' := h_points_new
      rw [h_eq] at hQ <;> exact hQ
    let k := n - m
    have hδ_k_eq : dyadicDelta k = (2 ^ m : ℝ) * dyadicDelta n := by
      have h : ((2 ^ m : ℕ) : ℝ) * dyadicDelta (m + k) = dyadicDelta k :=
        two_pow_mul_dyadicDelta m k
      have h_add : m + k = n := by omega
      rw [h_add] at h
      exact_mod_cast h.symm
    let TQ_local : Finset (DyadicTube n) :=
      (coarseConfig.tubeFamily Q hQ).biUnion
        (fun U => config.tubes.filter (fun T => T.toSet ⊆ U.toSet))
    have hTQ_local_eq : TQ_local =
        (coarseConfig.tubeFamily Q hQ).biUnion
          (fun U => config.tubes.filter (fun T => T.toSet ⊆ U.toSet)) := by rfl
    have hNΔ_pos : 0 < NΔ := by
      rcases hQSet'_nonempty with ⟨Q0, hQ0⟩
      have hMΔ_pos' : 0 < (trimmedFamily Q0 hQ0).card := by
        rw [h_trimmed_card Q0 hQ0] <;> exact hMΔ_pos
      rcases Finset.card_pos.mp hMΔ_pos' with ⟨U0, hU0⟩
      have h5 : NΔ ≤ fiberSize hnm config.tubes U0 := (h_fiber_band Q0 hQ0 U0 hU0).1
      have h6 : fiberSize hnm config.tubes U0 < 4 * NΔ := (h_fiber_band Q0 hQ0 U0 hU0).2
      have hQ0_band : Q0 ∈ QSet_band := hQSet''_sub hQ0
      have hU0_coarse : U0 ∈ coarseTubes_Q Q0 := h_trimmed_sub Q0 hQ0 hU0
      have h7 : 0 < fiberSize hnm config.tubes U0 := h_fiber_pos_all Q0 hQ0_band U0 hU0_coarse
      omega
    -- h_subset_TQ
    have h_subset_TQ : ∀ (p : DyadicSquare n) (hp : p ∈ P_Q' Q hQ'),
        uniformFamily_Q Q hQ' p hp ⊆ TQ_local := by
      intro p hp T hT
      have h1 : T ∈ candRet_Q Q hQ' p := h_unif_sub Q hQ' p hp hT
      have hpQ : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
      have hpin : p ∈ config.points := (Finset.mem_filter.mp hpQ).1
      have hT_in_opt : T ∈ config.tubeFamilyOpt p := (Finset.mem_filter.mp h1).1
      have hT_in_fam : T ∈ config.tubeFamily p hpin := by
        simpa [NiceConfiguration.tubeFamilyOpt, hpin] using hT_in_opt
      have h2 : coarseAnc hnm T ∈ trimmedFamily Q hQ' := (Finset.mem_filter.mp h1).2
      have hT_in_tubes : T ∈ config.tubes := config.h_subset p hpin hT_in_fam
      have h3 : coarseAnc hnm T ∈ coarseConfig.tubeFamily Q hQ := by
        have h_fam : coarseConfig.tubeFamily Q hQ = trimmedFamily_new Q := h_tubeFamily_new Q hQ
        rw [h_fam]; exact h2
      have h4 : T.toSet ⊆ (coarseAnc hnm T).toSet := coarseAnc_contains hnm T
      exact Finset.mem_biUnion.mpr ⟨coarseAnc hnm T, h3, Finset.mem_filter.mpr ⟨hT_in_tubes, h4⟩⟩
    -- p_of_q
    let p_of_q (q : DyadicSquare k) : DyadicSquare n := fine_local_p_of_q hnm Q q
    have h_P_Q'_eq_filter : P_Q' Q hQ' = P'.filter (fun p => squareContained hnm p Q) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · intro hp
        have h2 : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
        have h3 : squareContained hnm p Q := (Finset.mem_filter.mp h2).2
        have hp_total : p ∈ P_Q'_total Q := by
          simpa [P_Q'_total, dif_pos hQ'] using hp
        have h1 : p ∈ P' := Finset.mem_biUnion.mpr ⟨Q, hQ', hp_total⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, hsc⟩
        have h1' : ∃ (Q' : DyadicSquare m), Q' ∈ QSet' ∧ p ∈ P_Q'_total Q' :=
          Finset.mem_biUnion.mp h1
        rcases h1' with ⟨Q', hQ'_in, hp'⟩
        have h4 : p ∈ P_Q' Q' hQ'_in := by
          simpa [P_Q'_total, dif_pos hQ'_in] using hp'
        have h5 : p ∈ P_Q Q' := hP_Q'_sub Q' hQ'_in h4
        have h6 : squareContained hnm p Q' := (Finset.mem_filter.mp h5).2
        have h7 : containingSquare hnm p = Q' := (squareContained_iff_containingSquare hnm p Q').mp h6
        have h8 : containingSquare hnm p = Q := (squareContained_iff_containingSquare hnm p Q).mp hsc
        have h9 : Q' = Q := by rw [←h7, h8]
        subst h9
        exact h4
    have h_fine_points_eq : (fineConfig Q hQ).points = (P_Q' Q hQ').image (squareHomothety hnm Q) := by
      dsimp only [fineConfig]
      exact hfine_points Q hQ'
    have h_filter_id : (P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q) = P_Q Q := by
      apply Finset.filter_true_of_mem
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h_sub_filter : P_Q' Q hQ' ⊆ (P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q) := by
      rw [h_filter_id]
      exact hP_Q'_sub Q hQ'
    have h_p_of_q_sub : ∀ (q : DyadicSquare k) (hq : q ∈ (fineConfig Q hQ).points),
        p_of_q q ∈ P_Q' Q hQ' := by
      intro q hq
      rw [h_fine_points_eq] at hq
      have hq' : q ∈ ((P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q)).image (squareHomothety hnm Q) := by
        have h_img_sub : (P_Q' Q hQ').image (squareHomothety hnm Q) ⊆ ((P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q)).image (squareHomothety hnm Q) :=
          Finset.image_subset_image h_sub_filter
        exact h_img_sub hq
      have h5_raw : fine_local_p_of_q hnm Q q ∈ (P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q) :=
        fine_local_p_of_q_in_PQ hnm (P_Q Q) Q q hq'
      have h5 : p_of_q q ∈ P_Q Q := by
        have h_eq : p_of_q q = fine_local_p_of_q hnm Q q := by rfl
        rw [h_eq]
        exact (Finset.mem_filter.mp h5_raw).1
      have h6 : p_of_q q ∈ P_Q' Q hQ' := by
        have hq_img : q ∈ (P_Q' Q hQ').image (squareHomothety hnm Q) := hq
        rcases Finset.mem_image.mp hq_img with ⟨p, hp, h_eq⟩
        have hpQ : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
        have h_inv : p_of_q (squareHomothety hnm Q p) = p :=
          fine_local_p_of_q_inverse hnm Q p (Finset.mem_filter.mp hpQ).2
        have h_goal : p_of_q q = p := by
          rw [←h_eq]; exact h_inv
        rw [h_goal]; exact hp
      exact h6
    have h_contained : ∀ (q : DyadicSquare k) (hq : q ∈ (fineConfig Q hQ).points),
        squareContained hnm (p_of_q q) Q := by
      intro q hq
      have h5 : p_of_q q ∈ P_Q Q := by
        rw [h_fine_points_eq] at hq
        have hq' : q ∈ ((P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q)).image (squareHomothety hnm Q) := by
          have h_img_sub : (P_Q' Q hQ').image (squareHomothety hnm Q) ⊆ ((P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q)).image (squareHomothety hnm Q) :=
            Finset.image_subset_image h_sub_filter
          exact h_img_sub hq
        have h5_raw : fine_local_p_of_q hnm Q q ∈ (P_Q Q).filter (fun p : DyadicSquare n => squareContained hnm p Q) :=
          fine_local_p_of_q_in_PQ hnm (P_Q Q) Q q hq'
        have h_eq : p_of_q q = fine_local_p_of_q hnm Q q := by rfl
        rw [h_eq]
        exact (Finset.mem_filter.mp h5_raw).1
      exact (Finset.mem_filter.mp h5).2
    have h_image : ∀ (q : DyadicSquare k) (hq : q ∈ (fineConfig Q hQ).points)
        (x : InductionPlane), x ∈ (p_of_q q).toSet → homothetyS_Q m Q x ∈ q.toSet := by
      intro q hq x hx
      have h7 : squareHomothety hnm Q (p_of_q q) = q := by
        rw [h_fine_points_eq] at hq
        rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        have hpQ : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
        have h_inv : p_of_q (squareHomothety hnm Q p) = p :=
          fine_local_p_of_q_inverse hnm Q p (Finset.mem_filter.mp hpQ).2
        exact congr_arg (squareHomothety hnm Q) h_inv
      have h8 : homothetyS_Q m Q '' (p_of_q q).toSet = (squareHomothety hnm Q (p_of_q q)).toSet :=
        squareHomothety_toSet_eq_image hnm (p_of_q q) Q
      have h9 : homothetyS_Q m Q x ∈ homothetyS_Q m Q '' (p_of_q q).toSet :=
        ⟨x, hx, rfl⟩
      rw [h8] at h9
      rw [h7] at h9
      exact h9
    have h_local_bounded : ∀ (q : DyadicSquare k) (hq : q ∈ (fineConfig Q hQ).points),
        q.toSet ⊆ unitSquare := fun q hq => (fineConfig Q hQ).h_bounded q hq
    have h_fineTubes_eq : (fineConfig Q hQ).tubes =
        (fineConfig Q hQ).points.biUnion (fun q =>
          if hq : q ∈ (fineConfig Q hQ).points then (fineConfig Q hQ).tubeFamily q hq else ∅) := by
      dsimp only [fineConfig] <;> rfl
    have h_slope_preservation : ∀ (q : DyadicSquare k) (hq : q ∈ (fineConfig Q hQ).points),
        ((fineConfig Q hQ).tubeFamily q hq).image (fun U : DyadicTube k => U.a) =
        (uniformFamily_Q Q hQ' (p_of_q q) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a) := by
      intro q hq
      have h10 : squareHomothety hnm Q (p_of_q q) = q := by
        rw [h_fine_points_eq] at hq
        rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
        have hpQ : p ∈ P_Q Q := hP_Q'_sub Q hQ' hp
        have h_inv : p_of_q (squareHomothety hnm Q p) = p :=
          fine_local_p_of_q_inverse hnm Q p (Finset.mem_filter.mp hpQ).2
        exact congr_arg (squareHomothety hnm Q) h_inv
      let hq'' : squareHomothety hnm Q (p_of_q q) ∈ (fineConfig_Q Q hQ').points :=
        Classical.choose (hfine_slope Q hQ' (p_of_q q) (h_p_of_q_sub q hq))
      have h_eq : ((fineConfig_Q Q hQ').tubeFamily (squareHomothety hnm Q (p_of_q q)) hq'').image (fun U => U.a) =
          (uniformFamily_Q Q hQ' (p_of_q q) (h_p_of_q_sub q hq)).image (fun T => localSlopeCellIndex m T.a) :=
        Classical.choose_spec (hfine_slope Q hQ' (p_of_q q) (h_p_of_q_sub q hq))
      have hq' : squareHomothety hnm Q (p_of_q q) ∈ (fineConfig Q hQ).points := by
        dsimp only [fineConfig] <;> exact hq''
      have h_eq' : ((fineConfig Q hQ).tubeFamily (squareHomothety hnm Q (p_of_q q)) hq').image (fun U => U.a) =
          (uniformFamily_Q Q hQ' (p_of_q q) (h_p_of_q_sub q hq)).image (fun T => localSlopeCellIndex m T.a) := by
        dsimp only [fineConfig] at * <;> exact h_eq
      have h12 : squareHomothety hnm Q (p_of_q q) = q := h10
      simpa [h12] using h_eq'
    have h_uniform_packets : ∀ (q : DyadicSquare k) (hq : q ∈ (fineConfig Q hQ).points) (a : ℤ),
        ((uniformFamily_Q Q hQ' (p_of_q q) (h_p_of_q_sub q hq)).filter
          (fun T : DyadicTube n => localSlopeCellIndex m T.a = a)).card =
        if a ∈ (uniformFamily_Q Q hQ' (p_of_q q) (h_p_of_q_sub q hq)).image
          (fun T : DyadicTube n => localSlopeCellIndex m T.a) then m_Q_fn Q hQ' else 0 := by
      intro q hq a
      exact h_unif_packets Q hQ' (p_of_q q) (h_p_of_q_sub q hq) a
    have hQ_bounded : Q.toSet ⊆ unitSquare := h_bounded_new Q hQ'
    have h_est3 : (TQ_local.card : ℝ) ≥
        ((fineConfig Q hQ).tubes.card : ℝ) * (m_Q_fn Q hQ' : ℝ) / 9 :=
      estimate3_bridge_geo hnm hδ_k_eq
        (fineConfig Q hQ).points
        (fineConfig Q hQ).tubeFamily
        (fineConfig Q hQ).tubes
        h_fineTubes_eq
        (P_Q' Q hQ')
        (uniformFamily_Q Q hQ')
        (fun q _ => p_of_q q)
        h_p_of_q_sub
        (m_Q_fn Q hQ') (hmQ_pos_fn Q hQ')
        h_slope_preservation
        h_uniform_packets
        TQ_local
        h_subset_TQ
        Q hQ_bounded
        h_contained
        h_image
        h_local_bounded
        (fun p hp T hT => h_unif_strip Q hQ' p hp T hT)
        (fun p hp T hT => h_unif_inc Q hQ' p hp T hT)
        (fun q hq U hU => (fineConfig Q hQ).h_tube_parameters U ((fineConfig Q hQ).h_subset q hq hU))
        (fun q hq U hU => (fineConfig Q hQ).h_incidence q hq U hU)
    -- h_M_bound
    have h_M_bound : (M : ℝ) ≤ K_ret * K_loss * (m_Q_fn Q hQ' : ℝ) * (MQ Q : ℝ) := by
      rcases hP_Q'_nonempty Q hQ' with ⟨p, hp⟩
      have h1 : (M : ℝ) ≤ K_ret_fn Q hQ' * K_loss_fn Q hQ' * ((uniformFamily_Q Q hQ' p hp).card : ℝ) :=
        h_unif_ret Q hQ' p hp
      have hK1 : K_ret_fn Q hQ' = K_ret := hK_ret_eq Q hQ'
      have hK2 : K_loss_fn Q hQ' = K_loss := hK_loss_eq Q hQ'
      rw [hK1, hK2] at h1
      have h_card : (uniformFamily_Q Q hQ' p hp).card = (m_Q_fn Q hQ') * (MQ Q) := by
        set F := uniformFamily_Q Q hQ' p hp with hF
        let cells := F.image (fun T => localSlopeCellIndex m T.a)
        have hMQ_eq : MQ Q = MQ_fn Q hQ' := by
          simp [MQ, hQ'] <;> rfl
        have h_cells_card : cells.card = MQ_fn Q hQ' := h_unif_cells Q hQ' p hp
        have h_partition : F = cells.biUnion (fun a => F.filter (fun T => localSlopeCellIndex m T.a = a)) := by
          ext T
          simp only [Finset.mem_biUnion, Finset.mem_filter]
          constructor
          · intro hT
            exact ⟨localSlopeCellIndex m T.a, Finset.mem_image.mpr ⟨T, hT, rfl⟩, hT, rfl⟩
          · rintro ⟨a, _, hT, rfl⟩
            exact hT
        have h_disj : ∀ a ∈ cells, ∀ b ∈ cells, a ≠ b →
            Disjoint (F.filter (fun T => localSlopeCellIndex m T.a = a))
              (F.filter (fun T => localSlopeCellIndex m T.a = b)) := by
          intro a _ b _ hne
          simp [Finset.disjoint_left] <;> omega
        have h_main : F.card = (cells.card) * (m_Q_fn Q hQ') := by
          rw [h_partition, Finset.card_biUnion h_disj]
          have h_sum : ∑ a ∈ cells, (F.filter (fun T => localSlopeCellIndex m T.a = a)).card =
              ∑ a ∈ cells, (m_Q_fn Q hQ') := by
            apply Finset.sum_congr rfl
            intro a ha
            have h2 := h_unif_packets Q hQ' p hp a
            rw [if_pos ha] at h2
            exact h2
          rw [h_sum, Finset.sum_const, h_cells_card] <;> ring
        have h_final : F.card = (m_Q_fn Q hQ') * (MQ Q) := by
          calc F.card
            = cells.card * m_Q_fn Q hQ' := h_main
          _ = MQ_fn Q hQ' * m_Q_fn Q hQ' := by rw [h_cells_card]
          _ = m_Q_fn Q hQ' * MQ_fn Q hQ' := by ring
          _ = m_Q_fn Q hQ' * MQ Q := by rw [hMQ_eq]
        simpa [hF] using h_final
      rw [h_card] at h1
      have h_cast : (( (m_Q_fn Q hQ') * (MQ Q) : ℕ) : ℝ) =
          (m_Q_fn Q hQ' : ℝ) * (MQ Q : ℝ) := by
        exact Nat.cast_mul (m_Q_fn Q hQ') (MQ Q)
      rw [h_cast] at h1
      have h_goal : (M : ℝ) ≤ K_ret * K_loss * (m_Q_fn Q hQ' : ℝ) * (MQ Q : ℝ) := by
        have h_eq2 : K_ret * K_loss * (m_Q_fn Q hQ' : ℝ) * (MQ Q : ℝ) =
            K_ret * K_loss * ((m_Q_fn Q hQ' : ℝ) * (MQ Q : ℝ)) := by ring
        rw [h_eq2]
        exact h1
      exact h_goal
    exact cardinality_final hnm s hs hs_one C₁ hC₁ M hM config
      CΔ MΔ hMΔ_pos coarseConfig Q hQ (CQ Q) (MQ Q) (hMQ_pos Q hQ)
      (fineConfig Q hQ) (m_Q_fn Q hQ') (hmQ_pos_fn Q hQ')
      K_ret K_loss K hK_ret_one hK_loss_one2 hK_one h_K_36
      NΔ hNΔ_pos h_fiber_lower h_fiber_upper
      TQ_local hTQ_local_eq h_est3 h_M_bound

  have h_fine_tubes_eq : ∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points),
      (fineConfig Q hQ).tubes =
        (fineConfig Q hQ).points.biUnion (fun q =>
          if hq : q ∈ (fineConfig Q hQ).points then
            (fineConfig Q hQ).tubeFamily q hq else ∅) := by
    intro Q hQ
    dsimp only [fineConfig]
    <;> rfl

  exact ⟨K, hK_one, hK_poly, max_size, hK_eq', P', hP'_sub, uniformFamily,
    CΔ, MΔ, hMΔ_pos, coarseConfig, CQ, MQ, hMQ_pos, fineConfig,
    hP'_nonempty,
    by rw [h_points_new, hP'_image],
    h_global_coverage,
    h_per_Q_coverage,
    (fun p hp => ⟨h_final_sub p hp, h_final_retention p hp,
      h_final_sset p hp, h_final_incidence p hp⟩),
    h_CΔ_le, h_C₁_le, h_CQ_bounds,
    h_final_containment,
    h_fine_points,
    h_fine_slope,
    h_cardinality,
    h_fine_tubes_eq⟩

end InductionOnScales
