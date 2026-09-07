import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockPositiveWindowAssemblyStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationFromFullBlock
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CWindowShading
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
WZ2 Section 7: combine the weighted parameter-cluster, full local-block,
translation-amplification, and copied-shading PYZ outputs into the bounded
no-distinct positive-window one-scale estimate.

Conditional assembly for the parameter-Frostman specialization on the
Proposition 7.1 → Proposition 6.8 → Theorem 5.2 path. Instantiates the
local-block, amplification, cinematic-pullback, and projection-uniformization
premises with a single coherent chain of dependent witnesses.
-/

namespace Kakeya.Assouad

theorem parameter_block_positive_window_assembly :
    ParameterBlockPositiveWindowAssemblyStatement := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 _holder _pyzinput
    epsilon rhoMax h_eps_pos h_eps_lt1 h_rho_pos h_rho_le1 h_rho_lower

  let epsilon' :=
    parameterBlockProjectionWorkingEpsilon epsilon
  have h_eps'_pos : 0 < epsilon' := by
    simpa [epsilon',
      parameterBlockProjectionWorkingEpsilon] using
      h_eps_pos
  have h_eps'_lt_tenth : epsilon' < 1 / 10 := by
    simpa [epsilon',
      parameterBlockProjectionWorkingEpsilon] using
      h_eps_lt1.trans (by norm_num : (1 / 100 : ℝ) < 1 / 10)

  -- Apply h4 (local block selection) to get etaMax_local and delta₀_local
  rcases h4 h1 epsilon' h_eps'_pos h_eps'_lt_tenth with
    ⟨etaMax_local, delta₀_local, h_etaMax_local_pos, h_etaMax_local_le,
      h_delta₀_local_pos, h_delta₀_local_lt1, h_local_block⟩

  -- Apply h10 (cinematic pullback) to get threshold_pullback
  have h_pyzLoss_pos :
      0 < parameterBlockProjectionPYZLoss epsilon := by
    unfold parameterBlockProjectionPYZLoss
    positivity
  rcases h10 h6 h7 h8 h9 epsilon'
      (parameterBlockProjectionPYZLoss epsilon)
      h_eps'_pos h_eps'_lt_tenth h_pyzLoss_pos with
    ⟨threshold_pullback, h_tp_pos, h_tp_lt1, h_pullback⟩

  -- Choose etaMax
  let etaMax :=
    min (etaMax_local / 7) (epsilon ^ 3 / 2000)
  have h_etaMax_pos : 0 < etaMax := by positivity
  have h_etaMax_le_eps : etaMax ≤ epsilon := by
    have h1 : etaMax_local ≤ epsilon' ^ 2 / 1000 := h_etaMax_local_le
    have h3 : etaMax ≤ epsilon ^ 2 / 7000 := by
      calc etaMax
          ≤ etaMax_local / 7 := min_le_left _ _
        _ ≤ (epsilon' ^ 2 / 1000) / 7 := by gcongr
        _ = epsilon' ^ 2 / 7000 := by ring
        _ = epsilon ^ 2 / 7000 := by
          simp [epsilon',
            parameterBlockProjectionWorkingEpsilon]
    have h4 : epsilon ^ 2 / 7000 ≤ epsilon := by
      have h5 : epsilon ^ 2 ≤ epsilon := by nlinarith
      nlinarith
    exact h3.trans h4

  refine' ⟨etaMax, h_etaMax_pos, h_etaMax_le_eps, _⟩
  intro eta h_eta_pos h_eta_le_etaMax

  let eta_local := 7 * eta
  have h_eta_local_pos : 0 < eta_local := by positivity
  have h_eta_local_le : eta_local ≤ etaMax_local := by
    calc eta_local
        = 7 * eta := by rfl
      _ ≤ 7 * etaMax := by gcongr
      _ ≤ 7 * (etaMax_local / 7) := by
        gcongr
        exact min_le_left _ _
      _ = etaMax_local := by ring

  -- Apply h11 (projection uniformization) to get delta₀_uniform
  have h_1000_eta : 1000 * eta < epsilon ^ 3 := by
    have h4 : 1000 * eta ≤ epsilon ^ 3 / 2 := by
      calc 1000 * eta
          ≤ 1000 * etaMax := by gcongr
        _ ≤ 1000 * (epsilon ^ 3 / 2000) := by
          gcongr
          exact min_le_right _ _
        _ = epsilon ^ 3 / 2 := by ring
    have hepsilon_cube : 0 < epsilon ^ 3 := by positivity
    nlinarith
  rcases h11 epsilon rhoMax eta h_eps_pos h_eps_lt1
      h_rho_pos h_rho_le1 h_rho_lower h_eta_pos h_1000_eta with
    ⟨delta₀_uniform, h_du_pos, h_du_lt1, h_uniform⟩

  -- Get delta₀_log for logarithmic absorption
  rcases exists_delta_log_absorbed (K := 1600) (by norm_num) (B := eta) h_eta_pos (n := 1) (by norm_num) with
    ⟨delta₀_log, h_dl_pos, h_dl_le1, h_log_absorb⟩
  rcases exists_delta_realRpowENN_bound
      (2 : ENNReal) (by norm_num) h_eta_pos with
    ⟨delta₀_half, h_dh_pos, h_dh_le1, h_half_absorb⟩

  -- Choose delta₀ as min of all constraints
  let m1 := min delta₀_local threshold_pullback
  let m2 := min m1 delta₀_uniform
  let m3 := min m2 (1 / 100)
  let m4 := min m3 delta₀_log
  let delta₀ := min m4 delta₀_half
  have h_m1_pos : 0 < m1 := lt_min h_delta₀_local_pos h_tp_pos
  have h_m2_pos : 0 < m2 := lt_min h_m1_pos h_du_pos
  have h_m3_pos : 0 < m3 := lt_min h_m2_pos (by norm_num)
  have h_m4_pos : 0 < m4 := lt_min h_m3_pos h_dl_pos
  have h_d0_pos : 0 < delta₀ := lt_min h_m4_pos h_dh_pos
  have h_d0_lt1 : delta₀ < 1 := by
    have h : delta₀ ≤ delta₀_uniform := by
      calc delta₀ ≤ m4 := min_le_left _ _
           _ ≤ m3 := min_le_left _ _
           _ ≤ m2 := min_le_left _ _
           _ ≤ delta₀_uniform := min_le_right _ _
    exact h.trans_lt h_du_lt1

  refine' ⟨delta₀, h_d0_pos, h_d0_lt1, _⟩
  intro delta h_delta_pos h_delta_le_d0

  -- Extract individual constraints
  have h_delta_le_m4 : delta ≤ m4 := h_delta_le_d0.trans (min_le_left _ _)
  have h_delta_le_m3 : delta ≤ m3 := h_delta_le_m4.trans (min_le_left _ _)
  have h_delta_le_m2 : delta ≤ m2 := h_delta_le_m3.trans (min_le_left _ _)
  have h_delta_le_m1 : delta ≤ m1 := h_delta_le_m2.trans (min_le_left _ _)
  have h_delta_le_local : delta ≤ delta₀_local := h_delta_le_m1.trans (min_le_left _ _)
  have h_delta_le_pullback : delta ≤ threshold_pullback := h_delta_le_m1.trans (min_le_right _ _)
  have h_delta_le_uniform : delta ≤ delta₀_uniform := h_delta_le_m2.trans (min_le_right _ _)
  have h_delta_le_1_100 : delta ≤ (1 / 100 : ℝ) := h_delta_le_m3.trans (min_le_right _ _)
  have h_100_delta_le : 100 * delta ≤ 1 := by linarith
  have h_delta_le_log : delta ≤ delta₀_log :=
    h_delta_le_m4.trans (min_le_right _ _)
  have h_delta_le_half : delta ≤ delta₀_half :=
    h_delta_le_d0.trans (min_le_right _ _)
  have h_delta_lt1 : delta < 1 := lt_of_le_of_lt h_delta_le_d0 h_d0_lt1

  intro F hF_nonempty hF_vertical hF_params C hC1 hC_top hC_le hFrostman Y hY_dense hY_slab f hf_nonsing hf0

  -- Apply h11 to get projection uniform data
  have h_data : Nonempty (ParameterBlockProjectionUniformData (epsilon := epsilon) (eta := eta) (rhoMax := rhoMax) C Y f) :=
    h_uniform delta h_delta_pos h_delta_le_uniform F hF_nonempty hF_vertical hF_params C hC1 hC_top hC_le hFrostman Y hY_dense hY_slab f hf_nonsing hf0
  rcases h_data with ⟨data⟩

  let Z := data.globalShading
  have hZ_sub_Y : IsSubshading Z Y := data.subshading
  have hZ_dense : Z.IsLambdaDense (Kakeya.realRpowENN delta (4 * eta)) := data.density
  have hZ_slab : Z.union ⊆ horizontalSlab 0 1 := data.slab
  let Zfull := data.fullShading
  have hZfull_slab : Zfull.union ⊆ horizontalSlab 0 1 := by
    have hsub : Zfull.union ⊆ Z.union := by
      intro p hp
      rcases hp with ⟨i, hi⟩
      exact ⟨i, data.full_subshading i hi⟩
    exact hsub.trans hZ_slab

  -- Select a whole-tube c-window from the per-tube-full refinement.
  have h_delta_le4 : delta ≤ 4 := by linarith
  rcases c_window_subshading_mass hF_vertical delta h_delta_pos h_delta_le4 with
    ⟨c0, windowedShading, h_win_sub, h_win_cwindow,
      h_win_whole, h_win_mass⟩

  let lambda : ENNReal :=
    ENNReal.ofReal (delta / 8) *
      Kakeya.realRpowENN delta (5 * eta)
  have h_d8_pos : 0 < delta / 8 := by positivity
  have h_rpow_pos : 0 < Real.rpow delta (5 * eta) :=
    Real.rpow_pos_of_pos h_delta_pos (5 * eta)
  have h_lambda_ne_zero : lambda ≠ 0 := by
    have h1 : (ENNReal.ofReal (delta / 8)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr h_d8_pos
    have h2 : (Kakeya.realRpowENN delta (5 * eta)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr h_rpow_pos
    exact mul_ne_zero h1 h2
  have h_lambda_ne_top : lambda ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

  have h_two_absorb :
      (2 : ENNReal) ≤ Kakeya.realRpowENN delta (-eta) :=
    h_half_absorb delta h_delta_pos h_delta_le_half
  have h_power :
      Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta (4 * eta) =
        Kakeya.realRpowENN delta (5 * eta) := by
    rw [← Kakeya.Assouad.realRpowENN_add h_delta_pos]
    congr 1
    ring
  have h_half_power :
      Kakeya.realRpowENN delta (5 * eta) ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta (4 * eta) := by
    have hmul :
        (2 : ENNReal) * Kakeya.realRpowENN delta eta ≤ 1 := by
      have hInv :
          Kakeya.realRpowENN delta (-eta) *
              Kakeya.realRpowENN delta eta = 1 := by
        rw [← Kakeya.Assouad.realRpowENN_add h_delta_pos]
        simp [Kakeya.realRpowENN]
      calc
        (2 : ENNReal) * Kakeya.realRpowENN delta eta ≤
            Kakeya.realRpowENN delta (-eta) *
              Kakeya.realRpowENN delta eta := by
          gcongr
        _ = 1 := hInv
    calc
      Kakeya.realRpowENN delta (5 * eta) =
          Kakeya.realRpowENN delta eta *
            Kakeya.realRpowENN delta (4 * eta) := h_power.symm
      _ ≤ (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (4 * eta) := by
        have hHalf :
            Kakeya.realRpowENN delta eta ≤ (1 / 2 : ENNReal) := by
          have h :
              (2 : ENNReal) *
                  Kakeya.realRpowENN delta eta ≤
                (2 : ENNReal) * (1 / 2 : ENNReal) := by
            have hTwoHalf :
                (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
              simpa [one_div] using
                ENNReal.mul_inv_cancel
                  (show (2 : ENNReal) ≠ 0 by norm_num)
                  (show (2 : ENNReal) ≠ ⊤ by norm_num)
            rwa [hTwoHalf]
          exact
            (ENNReal.mul_le_mul_iff_right
              (show (2 : ENNReal) ≠ 0 by norm_num)
              (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp h
        gcongr

  -- Prove the full and windowed shadings have the adjusted density.
  have hZfull_dense :
      Zfull.IsLambdaDense
        (Kakeya.realRpowENN delta (5 * eta)) := by
    calc
      Kakeya.realRpowENN delta (5 * eta) *
            F.toBodyFamily.mass ≤
          ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (4 * eta)) *
              F.toBodyFamily.mass := by
        gcongr
      _ = (1 / 2 : ENNReal) *
          (Kakeya.realRpowENN delta (4 * eta) *
            F.toBodyFamily.mass) := by ring
      _ ≤ (1 / 2 : ENNReal) * Z.mass := by
        exact mul_le_mul_left' hZ_dense (1 / 2 : ENNReal)
      _ ≤ Zfull.mass := data.full_mass
  have h_win_dense : windowedShading.IsLambdaDense lambda := by
    have h1 :
        Kakeya.realRpowENN delta (5 * eta) *
            F.toBodyFamily.mass ≤ Zfull.mass := hZfull_dense
    have h2 :
        ENNReal.ofReal (delta / 8) * Zfull.mass ≤
          windowedShading.mass := h_win_mass
    have h3 :
        lambda * F.toBodyFamily.mass ≤
          ENNReal.ofReal (delta / 8) * Zfull.mass := by
      calc lambda * F.toBodyFamily.mass
          = ENNReal.ofReal (delta / 8) *
              (Kakeya.realRpowENN delta (5 * eta) *
                F.toBodyFamily.mass) := by
            rw [show lambda =
              ENNReal.ofReal (delta / 8) *
                Kakeya.realRpowENN delta (5 * eta) from rfl]
            ; ring
        _ ≤ ENNReal.ofReal (delta / 8) * Zfull.mass := by
          gcongr
    exact le_trans h3 h2

  -- Apply h2 (clustering) to get clustered data
  have h_clustered : Nonempty (TubeParameterClusterFrostmanData F windowedShading C lambda delta) :=
    h2 F hF_nonempty hF_params C hC1 hC_top hFrostman delta h_delta_pos (by linarith) h_100_delta_le
      windowedShading c0 h_win_cwindow lambda h_lambda_ne_zero h_lambda_ne_top h_win_dense
  rcases h_clustered with ⟨clustered⟩

  -- Numerical conditions for h3
  have h_5eta_pos : 0 < 5 * eta := by positivity
  have h_6eta_lt1 : 6 * eta < 1 := by
    have h_eta_cube :
        eta ≤ epsilon ^ 3 / 2000 :=
      h_eta_le_etaMax.trans (min_le_right _ _)
    have h_cube_small : epsilon ^ 3 < 1 := by
      nlinarith [sq_nonneg epsilon,
        mul_pos h_eps_pos (sq_pos_of_pos h_eps_pos)]
    nlinarith
  have h_density_frostman_lt1 : 5 * eta + eta < 1 := by
    have h : 5 * eta + eta = 6 * eta := by ring
    rw [h]; exact h_6eta_lt1
  have h_gamma_pos : 0 < eta := h_eta_pos
  have h_gamma_eq : eta = eta_local - (5 * eta + eta) := by
    simp [eta_local]; ring

  -- Log absorption condition
  have h_log_condition : 1600 * (1 + Real.log delta⁻¹) ≤ Real.rpow delta (-eta) := by
    have h := h_log_absorb delta h_delta_pos h_delta_le_log
    simpa using h

  -- Apply h3 (cardinality) to get cardinality bound
  have h_card : Kakeya.realRpowENN delta (-1 + eta_local) ≤ 100000 * clustered.points.enncard :=
    h3 (delta := delta) (densityLoss := 5 * eta) (frostmanLoss := eta) (targetLoss := eta_local) (gamma := eta)
      h_delta_pos h_delta_lt1 h_5eta_pos h_eta_pos h_density_frostman_lt1 h_gamma_eq h_gamma_pos
      (clustered := clustered) hC_le rfl h_log_condition

  -- c-window condition for clustered.shading
  have h_clustered_cwindow : ∀ i, clustered.shading.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ delta / 2 := by
    intro i hne
    have h_sub_i : clustered.shading.carrier i ⊆ windowedShading.carrier i := clustered.subshading i
    have h_win_nonempty : windowedShading.carrier i ≠ ∅ := by
      by_contra h
      have h5 : clustered.shading.carrier i = ∅ := by
        rw [h] at h_sub_i
        simpa using h_sub_i
      exact hne h5
    exact h_win_cwindow i h_win_nonempty

  -- Apply h4 to get local block
  have h_localBlock : Nonempty (ParameterLocalFullBlockData clustered epsilon') :=
    h_local_block eta_local h_eta_local_pos h_eta_local_le delta h_delta_pos h_delta_le_local
      F windowedShading C lambda clustered c0 h_clustered_cwindow h_card
  rcases h_localBlock with ⟨localBlock⟩

  rcases parameter_local_representative_block localBlock with
    ⟨representatives⟩

  -- Apply h5 (amplification)
  let s := 1 - 20 * epsilon' ^ 2
  have h_amp : Nonempty (ParameterBlockAmplificationData delta localBlock.blockScale s localBlock.centeredPoints) :=
    parameterBlockAmplification_from_fullBlock
      h5 localBlock h_delta_pos h_eps'_pos h_eps'_lt_tenth
  rcases h_amp with ⟨amplification⟩

  -- Prove clustered.shading.union ⊆ horizontalSlab 0 1
  have h_clustered_slab : clustered.shading.union ⊆ horizontalSlab 0 1 := by
    have h1 : clustered.shading.union ⊆ windowedShading.union := by
      intro p hp
      rcases hp with ⟨i, hi⟩
      exact ⟨i, clustered.subshading i hi⟩
    have h2 : windowedShading.union ⊆ Zfull.union := by
      intro p hp
      rcases hp with ⟨i, hi⟩
      exact ⟨i, h_win_sub i hi⟩
    exact h1.trans (h2.trans hZfull_slab)

  have h_window_per_tube :
      HasPerTubeMass windowedShading
        (parameterBlockProjectionPerTubeThreshold delta eta) :=
    data.full_per_tube.mono_whole h_win_whole
  have h_clustered_per_tube :
      HasPerTubeMass clustered.shading
        (parameterBlockProjectionPerTubeThreshold delta eta) :=
    h_window_per_tube.mono_whole clustered.whole_tube

  -- Apply h10 to get pullback
  have h_threshold_nonzero :
      parameterBlockProjectionPerTubeThreshold delta eta ≠ 0 := by
    have hHalf : (1 / 2 : ENNReal) ≠ 0 := by
      norm_num
    have hPower :
        Kakeya.realRpowENN delta (4 * eta) ≠ 0 := by
      rw [Kakeya.realRpowENN]
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (Real.rpow_pos_of_pos h_delta_pos _)
    have hVolume :
        Kakeya.deltaTubeVolume delta ≠ 0 :=
      (tube_volume_scaling.2.1 delta h_delta_pos
        (by linarith)).1.ne'
    exact mul_ne_zero (mul_ne_zero hHalf hPower) hVolume
  have h_threshold_ne_top :
      parameterBlockProjectionPerTubeThreshold delta eta ≠ ⊤ := by
    unfold parameterBlockProjectionPerTubeThreshold
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · simp
      · exact ENNReal.ofReal_ne_top
    · exact (tube_volume_scaling.2.1 delta h_delta_pos
        (by linarith)).2
  have h_pullback_data :
      Nonempty
        (ParameterBlockRepresentativeCinematicPullbackData
          localBlock representatives amplification f
            (parameterBlockProjectionPYZLoss epsilon)
            (parameterBlockProjectionPerTubeThreshold delta eta)) :=
    h_pullback delta h_delta_pos h_delta_le_pullback F hF_vertical
      windowedShading C lambda clustered h_clustered_slab
      localBlock representatives amplification
      (parameterBlockProjectionPerTubeThreshold delta eta)
      h_threshold_nonzero h_threshold_ne_top h_clustered_per_tube
      f hf_nonsing hf0
  rcases h_pullback_data with ⟨pullback⟩

  -- Apply data.globalize to get final rho and volume bound
  have h_final :=
    data.globalize c0 windowedShading h_win_sub h_win_mass
      h_win_whole h_win_cwindow clustered localBlock
      representatives amplification pullback

  rcases h_final with ⟨rho, h_rho_lower, h_rho_upper, h_volume⟩

  exact ⟨rho, h_rho_lower, h_rho_upper, Z, hZ_sub_Y, hZ_dense, h_volume⟩

end Kakeya.Assouad
