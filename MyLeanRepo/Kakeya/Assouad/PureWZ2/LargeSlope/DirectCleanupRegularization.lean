import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectRegularizedRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperCleanupSourceRegularization

/-!
# Nearby CWA after direct triangular centered cleanup

The second source regularization is supported exactly on the source indices
whose triangular targets survive centered cleanup.  Its dyadic level retains
an explicit floor in terms of the original `J₀`-box normalization.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The first direct dyadic level retains one quarter of the literal source
normalization. -/
theorem PureWZ2ExternalWeightRegularizationData.direct_selectedWeightLevel_lower
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount) :
    pureWZ2DirectPopularSourceNormalization assembly.horizontalSource / 4 ≤
      regularized.selectedWeightLevel := by
  apply regularized.normalization_div_four_le_selectedWeightLevel
  change pureWZ2DirectPopularSourceNormalization assembly.horizontalSource *
      assembly.cfg.family.enncard ≤
    ∑ index : Fin assembly.cfg.family.card,
      pureWZ2DirectPopularSourceWeight retubing.popular index
  change pureWZ2DirectPopularSourceNormalization assembly.horizontalSource *
      assembly.cfg.family.enncard ≤
    retubing.popular.popular.restricted.mass
  exact retubing.popular.normalization_mul_card_le_mass

/-- Run the source-side nearby-CWA regularization after centered cleanup. -/
theorem PureWZ2AnisotropicPaperCenteredCleanupData.reregularizeDirectSource
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    (outputConstant : ENNReal)
    (houtputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (outputLevelCount : ℕ)
    (hambientTwo : 2 < regularized.outputConstant)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      regularized.outputConstant ^ outputLevelCount)
    (houtput : regularized.outputConstant * regularized.outputConstant ≤
      outputConstant) :
    Nonempty (PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) := by
  apply pureWZ2_anisotropic_cleanup_source_regularization cleanup
    regularized.cwa_nearby regularized.selected_nonempty
    assembly.cfg.extremal.delta_le_one
    regularized.directSelectedWeightLevel_mul_card_le_sourceMass
    regularized.selectedWeightLevel_pos.ne'
    regularized.selectedWeightLevel_ne_top
  · unfold pureWZ2DirectRegularizedSourceTopConstant
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr
          (pureWZ2DirectPopularSourceNormalization_pos
            assembly.horizontalSource).ne')
        (by
          rw [regularized.retentionConstant_eq]
          exact ENNReal.mul_ne_top
            (by
              rw [regularized.regularizationLoss_eq]
              exact ENNReal.mul_ne_top (by norm_num)
                (ENNReal.pow_ne_top <| by simp))
            (by
              unfold pureWZ2DirectPopularSourceWeightUpper
              exact ENNReal.mul_ne_top
                (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
                (by simp [Kakeya.realRpowENN]))))
      (by simp [Kakeya.realRpowENN])
  · have hrawPos : 0 < anisotropicPaperRawScale delta
        assembly.horizontalSource.c assembly.horizontalSource.d := by
      unfold anisotropicPaperRawScale
      exact div_pos
        (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
        (sub_pos.mpr assembly.horizontalSource.ordered)
    have hrawHalf : anisotropicPaperRawScale delta
        assembly.horizontalSource.c assembly.horizontalSource.d ≤ 1 / 2 := by
      have hlength : assembly.horizontalSource.d -
          assembly.horizontalSource.c = assembly.rho.1 / 100 := by
        rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
      rw [show anisotropicPaperRawScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d =
            1600 * delta / assembly.rho.1 by
        unfold anisotropicPaperRawScale
        rw [hlength]
        field_simp [show assembly.rho.1 ≠ 0 by
          exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
            assembly.rho.2.1)]
        ring, div_le_iff₀
          (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
      have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
        linarith [assembly.rho_tiny]
      nlinarith [assembly.delta_le_rho_sq,
        mul_nonneg
          (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
          hfactor]
    exact anisotropicPaperAlignedScale_pos hrawPos hrawHalf
  · have htargetUpper : anisotropicPaperAlignedScale delta
        assembly.horizontalSource.c assembly.horizontalSource.d <
      32 * delta /
        (assembly.horizontalSource.d - assembly.horizontalSource.c) := by
      have hrawPos : 0 < anisotropicPaperRawScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d := by
        unfold anisotropicPaperRawScale
        exact div_pos
          (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
          (sub_pos.mpr assembly.horizontalSource.ordered)
      have hrawHalf : anisotropicPaperRawScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d ≤ 1 / 2 := by
        have hlength : assembly.horizontalSource.d -
            assembly.horizontalSource.c = assembly.rho.1 / 100 := by
          rw [assembly.horizontalSource.length_eq,
            assembly.horizontalSource_scale]
        rw [show anisotropicPaperRawScale delta
            assembly.horizontalSource.c assembly.horizontalSource.d =
              1600 * delta / assembly.rho.1 by
          unfold anisotropicPaperRawScale
          rw [hlength]
          field_simp [show assembly.rho.1 ≠ 0 by
            exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
              assembly.rho.2.1)]
          ring, div_le_iff₀
            (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
        have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
          linarith [assembly.rho_tiny]
        nlinarith [assembly.delta_le_rho_sq,
          mul_nonneg
            (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
            hfactor]
      exact (anisotropicPaperAlignedScale_lt_two_mul_raw
        hrawPos hrawHalf).trans_eq <| by
          unfold anisotropicPaperRawScale
          ring
    have hlength : assembly.horizontalSource.d -
        assembly.horizontalSource.c = assembly.rho.1 / 100 := by
      rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    have hrhoPos : 0 < assembly.rho.1 :=
      assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1
    have hdeltaRhoSeven : delta / assembly.rho.1 ≤ assembly.rho.1 ^ 7 := by
      rw [div_le_iff₀ hrhoPos]
      simpa [pow_succ] using assembly.delta_le_rho_eight
    have htargetRho : anisotropicPaperAlignedScale delta
        assembly.horizontalSource.c assembly.horizontalSource.d <
      3200 * assembly.rho.1 ^ 7 := by
      calc
        _ < 32 * delta /
            (assembly.horizontalSource.d - assembly.horizontalSource.c) :=
          htargetUpper
        _ = 3200 * (delta / assembly.rho.1) := by rw [hlength]; ring
        _ ≤ 3200 * assembly.rho.1 ^ 7 := by gcongr
    have hrhoSeven : assembly.rho.1 ^ 7 ≤ (1 / 6400 : ℝ) ^ 7 :=
      pow_le_pow_left₀ hrhoPos.le assembly.rho_tiny 7
    exact htargetRho.le.trans <|
      (mul_le_mul_of_nonneg_left hrhoSeven (by norm_num)).trans <| by
        norm_num
  · exact houtputFinite
  · exact hambientTwo
  · exact hlevels
  · exact houtput

/-- The second direct dyadic level is bounded below by the triangular
Jacobian times the first selected level. -/
theorem PureWZ2ExternalWeightRegularizationData.direct_cleanup_selectedWeightLevel_lower
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    (ENNReal.ofReal assembly.horizontalSource.m *
        pureWZ2DirectPopularSourceNormalization assembly.horizontalSource) /
        4 / 4 ≤ data.selectedWeightLevel := by
  have hfirst := regularized.direct_selectedWeightLevel_lower
  have hscaled :
      ENNReal.ofReal assembly.horizontalSource.m *
          (pureWZ2DirectPopularSourceNormalization
            assembly.horizontalSource / 4) ≤
        ENNReal.ofReal assembly.horizontalSource.m *
          regularized.selectedWeightLevel :=
    mul_le_mul_left' hfirst _
  calc
    (ENNReal.ofReal assembly.horizontalSource.m *
        pureWZ2DirectPopularSourceNormalization assembly.horizontalSource) /
          4 / 4 =
        (ENNReal.ofReal assembly.horizontalSource.m *
          (pureWZ2DirectPopularSourceNormalization
            assembly.horizontalSource / 4)) / 4 := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (ENNReal.ofReal assembly.horizontalSource.m *
          regularized.selectedWeightLevel) / 4 := by gcongr
    _ = anisotropicPaperCleanupNormalization assembly.horizontalSource.m
          regularized.selectedWeightLevel / 4 := by rfl
    _ ≤ data.selectedWeightLevel := by
      apply data.normalization_div_four_le_selectedWeightLevel
      exact cleanup.indicator_mass
        regularized.directSelectedWeightLevel_mul_card_le_sourceMass

/-- Source tubes retained by the second regularization inherit the bounded
base of the actual Node-5 configuration. -/
theorem PureWZ2ExternalWeightRegularizationData.direct_selected_source_base_le_five
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    ∀ source, ‖(data.selected.family.tube source).base‖ ≤ 5 := by
  intro source
  rw [data.selected.tube_eq,
    (regularized.toDirectNonemptySubfamily retubing).tube_eq,
    (wz2PaperNonemptyCarrierSubfamily
      retubing.popular.popular.restricted).tube_eq]
  exact (assembly.cfg.bounded_base _).trans (by norm_num)

end Kakeya.Assouad

end
