import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingAverageProfile

/-!
# Absorb the spacing-tree cardinality loss

The OS retention loss is at most one small power of the terminal mesh.  The
remaining fixed base-dependent constants are absorbed by choosing `delta`
sufficiently small after the base is fixed.
-/

noncomputable section

namespace Kakeya.Assouad

lemma parameterSpacing_retention_power_bound
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon) :
    (2 *
        (Nat.log 2 ((tree.base + 1) ^ 3) + 1) :
      ℝ) ^ tree.levels ≤
      Real.rpow (tree.base ^ tree.levels : ℝ)
        (epsilon ^ 2 / 1000) := by
  have hnonneg :
      0 ≤
        (2 *
            (Nat.log 2 ((tree.base + 1) ^ 3) + 1) :
          ℝ) := by positivity
  have hpow :=
    pow_le_pow_left₀
      hnonneg tree.local_loss tree.levels
  calc
    (2 *
        (Nat.log 2 ((tree.base + 1) ^ 3) + 1) :
      ℝ) ^ tree.levels
        ≤
          (Real.rpow (tree.base : ℝ)
            (epsilon ^ 2 / 1000)) ^
              tree.levels := hpow
    _ =
        Real.rpow (tree.base ^ tree.levels : ℝ)
          (epsilon ^ 2 / 1000) := by
      have hbase_pos : (0 : ℝ) < tree.base := by
        exact_mod_cast
          (show 0 < tree.base from
            lt_of_lt_of_le (by norm_num)
              tree.base_ge_three)
      rw [rpow_nat_pow hbase_pos]
      have hleft :
          Real.rpow (tree.base : ℝ)
              ((tree.levels : ℝ) *
                (epsilon ^ 2 / 1000)) =
            Real.rpow
              (Real.rpow (tree.base : ℝ)
                tree.levels)
              (epsilon ^ 2 / 1000) := by
        exact Real.rpow_mul hbase_pos.le
          tree.levels (epsilon ^ 2 / 1000)
      rw [hleft]
      exact congrArg
        (fun value : ℝ =>
          Real.rpow value (epsilon ^ 2 / 1000))
        (Real.rpow_natCast (tree.base : ℝ)
          tree.levels)

lemma parameterSpacing_refined_card_lower
    {delta epsilon eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (tree :
      ParameterSpacingUniformTreeData
        clustered epsilon)
    (hdelta : 0 < delta)
    (hglobal :
      Kakeya.realRpowENN delta (-1 + eta) ≤
        100000 * clustered.points.enncard) :
    Real.rpow delta (-1 + eta) ≤
      100000 *
        ((2 *
              (Nat.log 2 ((tree.base + 1) ^ 3) + 1) :
            ℝ) ^ tree.levels *
          (tree.refinedPoints.card : ℝ)) := by
  have hpoints_top :
      clustered.points.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  have hrefined_top :
      tree.refinedPoints.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  have hretention_real :
      (clustered.points.card : ℝ) ≤
        (2 *
            (Nat.log 2 ((tree.base + 1) ^ 3) + 1) :
          ℝ) ^ tree.levels *
          (tree.refinedPoints.card : ℝ) :=
    tree.retention
  have hglobal_real :
      Real.rpow delta (-1 + eta) ≤
        100000 * (clustered.points.card : ℝ) := by
    have hrpow_nonneg :
        0 ≤ Real.rpow delta (-1 + eta) :=
      Real.rpow_nonneg hdelta.le _
    have htoReal :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by norm_num) hpoints_top)
        hglobal
    rw [Kakeya.realRpowENN,
      ENNReal.toReal_ofReal hrpow_nonneg] at htoReal
    simpa [DiscreteSet.enncard] using htoReal
  calc
    Real.rpow delta (-1 + eta)
        ≤ 100000 *
            (clustered.points.card : ℝ) := hglobal_real
    _ ≤
        100000 *
          ((2 *
              (Nat.log 2
                ((tree.base + 1) ^ 3) + 1) :
            ℝ) ^ tree.levels *
            (tree.refinedPoints.card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        hretention_real (by norm_num)

theorem exists_parameterSpacing_average_cardinality_bound
    (base : ℕ)
    (hbase : 3 ≤ base)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ eta : ℝ,
        0 < eta →
        eta ≤ epsilon ^ 2 / 1000 →
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ C lambda : ENNReal,
                ∀ clustered :
                    TubeParameterClusterFrostmanData
                      F Y C lambda delta,
                  ∀ tree :
                      ParameterSpacingUniformTreeData
                        clustered epsilon,
                    tree.base = base →
                    Kakeya.realRpowENN
                        delta (-1 + eta) ≤
                      100000 *
                        clustered.points.enncard →
                    (cellCount tree.base
                        tree.refinedPoints 0 : ℝ) *
                        Real.rpow (tree.base : ℝ)
                          ((tree.levels : ℝ) *
                            parameterSpacingAverageThreshold
                              epsilon) ≤
                      (tree.refinedPoints.card : ℝ) := by
  let lossExponent : ℝ := epsilon ^ 2 / 1000
  let average : ℝ :=
    parameterSpacingAverageThreshold epsilon
  let combinedExponent : ℝ :=
    average + lossExponent
  let rootBound : ℝ := ((2 * base + 1) ^ 3 : ℕ)
  let distortion : ℝ := 3 * (base : ℝ)
  let constant : ℝ :=
    100000 * rootBound *
      Real.rpow distortion combinedExponent
  have hdistortion_pos : 0 < distortion := by
    dsimp only [distortion]
    positivity
  have hloss_pos : 0 < lossExponent := by
    dsimp only [lossExponent]
    positivity
  have hcombined_pos : 0 < combinedExponent := by
    dsimp only [combinedExponent, average,
      lossExponent,
      parameterSpacingAverageThreshold]
    nlinarith [sq_pos_of_pos hepsilon]
  have hconstant_nonneg : 0 ≤ constant := by
    dsimp only [constant]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (by
          dsimp only [rootBound]
          positivity))
      (Real.rpow_nonneg hdistortion_pos.le _)
  have hgap :
      (-1 + lossExponent) <
        -combinedExponent := by
    dsimp only [lossExponent, combinedExponent,
      average, parameterSpacingAverageThreshold]
    nlinarith [sq_pos_of_pos hepsilon]
  rcases exists_delta_mul_rpow_le_rpow
      constant hconstant_nonneg hgap with
    ⟨deltaAbsorb, hdeltaAbsorb,
      hdeltaAbsorbOne, habsorb⟩
  let delta₀ : ℝ :=
    min deltaAbsorb (1 / 1000)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaAbsorbOne
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro eta heta heta_le delta hdelta hdelta_le
    F Y C lambda clustered tree htree_base hglobal
  subst base
  have hdelta_absorb :
      delta ≤ deltaAbsorb :=
    hdelta_le.trans (min_le_left _ _)
  have hdelta_small :
      delta < 1 := by
    exact hdelta_le.trans_lt
      ((min_le_right _ _).trans_lt (by norm_num))
  have hdelta_one : delta ≤ 1 := hdelta_small.le
  have hbase_real : (0 : ℝ) < tree.base := by
    exact_mod_cast
      (show 0 < tree.base from
        lt_of_lt_of_le (by norm_num) hbase)
  have hloss :
      (2 *
          (Nat.log 2
            ((tree.base + 1) ^ 3) + 1) :
        ℝ) ^ tree.levels ≤
        Real.rpow
          (tree.base ^ tree.levels : ℝ)
          lossExponent := by
    simpa [lossExponent] using
      parameterSpacing_retention_power_bound tree
  have hrefined :
      Real.rpow delta (-1 + eta) ≤
        100000 *
          ((2 *
              (Nat.log 2
                ((tree.base + 1) ^ 3) + 1) :
            ℝ) ^ tree.levels *
            (tree.refinedPoints.card : ℝ)) :=
    parameterSpacing_refined_card_lower
      tree hdelta hglobal
  have hroot :
      (cellCount tree.base
          tree.refinedPoints 0 : ℝ) ≤
        rootBound := by
    dsimp only [rootBound]
    exact_mod_cast
      (parameterSpacing_root_cellCount_le tree)
  let terminalPower : ℝ :=
    (tree.base ^ tree.levels : ℝ)
  have hterminal_pos : 0 < terminalPower := by
    dsimp only [terminalPower]
    exact pow_pos hbase_real _
  have hterminal_upper :
      terminalPower ≤ distortion / delta := by
    have hmesh_lower := tree.terminal_mesh_lower
    have hdenom_pos : 0 < distortion := by
      exact hdistortion_pos
    have hdelta_div :
        delta / distortion ≤
          terminalPower⁻¹ := by
      simpa [terminalPower] using hmesh_lower
    have hinv :
        terminalPower ≤
          (delta / distortion)⁻¹ := by
      have hinv' :
          terminalPower⁻¹⁻¹ ≤
            (delta / distortion)⁻¹ :=
        (inv_le_inv₀
          (inv_pos.mpr hterminal_pos)
          (div_pos hdelta hdenom_pos)).2
          hdelta_div
      simpa [inv_inv] using hinv'
    calc
      terminalPower
          ≤ (delta / distortion)⁻¹ := hinv
      _ = distortion / delta := by
        field_simp [hdelta.ne', hdenom_pos.ne']
  have hterminal_rpow :
      Real.rpow terminalPower combinedExponent ≤
        Real.rpow (distortion / delta)
          combinedExponent :=
    Real.rpow_le_rpow hterminal_pos.le
      hterminal_upper hcombined_pos.le
  have hterminal_delta :
      Real.rpow terminalPower combinedExponent ≤
        Real.rpow distortion combinedExponent *
          Real.rpow delta (-combinedExponent) := by
    calc
      Real.rpow terminalPower combinedExponent
          ≤ Real.rpow (distortion / delta)
              combinedExponent := hterminal_rpow
      _ =
          Real.rpow distortion combinedExponent /
            Real.rpow delta combinedExponent := by
        exact Real.div_rpow
          hdistortion_pos.le hdelta.le _
      _ =
          Real.rpow distortion combinedExponent *
            Real.rpow delta (-combinedExponent) := by
        have hneg :
            Real.rpow delta (-combinedExponent) =
              (Real.rpow delta combinedExponent)⁻¹ :=
          Real.rpow_neg hdelta.le combinedExponent
        rw [hneg]
        ring
  have hpower_product :
      Real.rpow terminalPower lossExponent *
          Real.rpow terminalPower average =
        Real.rpow terminalPower combinedExponent := by
    exact
      (Real.rpow_add hterminal_pos
        lossExponent average).symm.trans
        (by
          congr 1
          dsimp only [combinedExponent]
          ring)
  have hfixed :
      constant *
          Real.rpow delta (-combinedExponent) ≤
        Real.rpow delta (-1 + lossExponent) :=
    habsorb delta hdelta hdelta_absorb
  have heta_mono :
      Real.rpow delta (-1 + lossExponent) ≤
        Real.rpow delta (-1 + eta) := by
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta hdelta_one (by
        dsimp only [lossExponent]
        linarith)
  let coefficient : ℝ :=
    100000 *
      (2 *
          (Nat.log 2
            ((tree.base + 1) ^ 3) + 1) :
        ℝ) ^ tree.levels
  have hcoefficient_pos : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  have htarget_scaled :
      coefficient *
          ((cellCount tree.base
              tree.refinedPoints 0 : ℝ) *
            Real.rpow (tree.base : ℝ)
              ((tree.levels : ℝ) * average)) ≤
        Real.rpow delta (-1 + eta) := by
    have hbase_power :
        Real.rpow (tree.base : ℝ)
            ((tree.levels : ℝ) * average) =
          Real.rpow terminalPower average := by
      have htree_base_pos : (0 : ℝ) < tree.base := by
        exact hbase_real
      calc
        Real.rpow (tree.base : ℝ)
              ((tree.levels : ℝ) * average) =
            Real.rpow
              (Real.rpow (tree.base : ℝ)
                tree.levels) average :=
          Real.rpow_mul htree_base_pos.le
            tree.levels average
        _ =
            Real.rpow terminalPower average := by
          congr 1
          dsimp only [terminalPower]
          exact Real.rpow_natCast _ _
    rw [hbase_power]
    have hroot_nonneg :
        0 ≤
          (cellCount tree.base
            tree.refinedPoints 0 : ℝ) := by positivity
    have hrootBound_nonneg : 0 ≤ rootBound := by
      dsimp only [rootBound]
      positivity
    have hlossPow_nonneg :
        0 ≤
          (2 *
            (Nat.log 2
              ((tree.base + 1) ^ 3) + 1) : ℝ) ^
              tree.levels := by positivity
    have hterminalLoss_nonneg :
        0 ≤ Real.rpow terminalPower lossExponent :=
      Real.rpow_nonneg hterminal_pos.le _
    have hterminalAverage_nonneg :
        0 ≤ Real.rpow terminalPower average :=
      Real.rpow_nonneg hterminal_pos.le _
    calc
      coefficient *
            ((cellCount tree.base
                tree.refinedPoints 0 : ℝ) *
              Real.rpow terminalPower average)
          =
            100000 *
              ((2 *
                (Nat.log 2
                  ((tree.base + 1) ^ 3) + 1) : ℝ) ^
                  tree.levels) *
              (cellCount tree.base
                tree.refinedPoints 0 : ℝ) *
              Real.rpow terminalPower average := by
        dsimp only [coefficient]
        ring
      _ ≤
            100000 *
              (Real.rpow terminalPower lossExponent) *
              (cellCount tree.base
                tree.refinedPoints 0 : ℝ) *
              Real.rpow terminalPower average := by
        gcongr
      _ ≤
            100000 *
              (Real.rpow terminalPower lossExponent) *
              rootBound *
              Real.rpow terminalPower average := by
        gcongr
      _ =
          100000 * rootBound *
            (Real.rpow terminalPower lossExponent *
              Real.rpow terminalPower average) := by ring
      _ =
          100000 * rootBound *
            Real.rpow terminalPower
              combinedExponent := by
        rw [hpower_product]
      _ ≤
          constant *
            Real.rpow delta
              (-combinedExponent) := by
        rw [show constant =
            100000 * rootBound *
              Real.rpow distortion
                combinedExponent by rfl]
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left
            hterminal_delta
            (mul_nonneg
              (show (0 : ℝ) ≤ 100000 by norm_num)
              hrootBound_nonneg)
      _ ≤
          Real.rpow delta
            (-1 + lossExponent) := hfixed
      _ ≤ Real.rpow delta (-1 + eta) :=
        heta_mono
  have hrefined_scaled :
      coefficient *
          (tree.refinedPoints.card : ℝ) ≥
        Real.rpow delta (-1 + eta) := by
    simpa [coefficient, mul_assoc] using hrefined
  have hcancel :
      (cellCount tree.base
          tree.refinedPoints 0 : ℝ) *
          Real.rpow (tree.base : ℝ)
            ((tree.levels : ℝ) * average) ≤
        (tree.refinedPoints.card : ℝ) := by
    apply le_of_mul_le_mul_left
      (htarget_scaled.trans hrefined_scaled)
      hcoefficient_pos
  simpa [average] using hcancel

end Kakeya.Assouad
