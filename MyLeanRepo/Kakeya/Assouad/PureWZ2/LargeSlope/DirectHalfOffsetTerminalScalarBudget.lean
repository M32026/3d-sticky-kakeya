import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationWeakening

/-!
# Scalar budgets for the actual direct half-offset terminal

This file combines the pre-runtime source-to-terminal scale bridge with the
standard fixed-constant absorption lemma.  The density and local-grain
wrappers below keep the remaining scalar receipts explicit and attach them to
the literal terminal family and shading.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly

/-- A fixed finite coefficient times a negative source power is absorbed by a
negative power of the actual terminal radius.  The strict exponent gap is the
only loss hypothesis. -/
theorem exists_delta_for_halfOffsetLineClass_constant_source_negative_le_target_negative
    (epsilon sourceLoss outputLoss : ℝ)
    (constant : ENNReal) (hconstant : constant ≠ ⊤)
    (hepsilon : 0 < epsilon)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : sourceLoss < (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        constant * Kakeya.realRpowENN delta (-sourceLoss) ≤
          Kakeya.realRpowENN commonSource.halfOffsetLineClassTargetDelta
            (-outputLoss) := by
  rcases exists_delta_constant_mul_power_le_power constant hconstant
      (-((1 - 2 * epsilon) * outputLoss)) (-sourceLoss)
      (by linarith) with
    ⟨constantScale, hconstantScale, hconstantScaleOne, habsorb⟩
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
      epsilon hepsilon with
    ⟨targetScale, htargetScale, htargetScaleOne, htarget⟩
  refine ⟨min constantScale targetScale,
    lt_min hconstantScale htargetScale,
    (min_le_left _ _).trans hconstantScaleOne, ?_⟩
  intro logExponent sigma delta commonSource hdelta hdeltaBound
  have hdeltaConstant : delta ≤ constantScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaTarget : delta ≤ targetScale :=
    hdeltaBound.trans (min_le_right _ _)
  exact (habsorb hdelta hdeltaConstant).trans <|
    pure_wz2_target_negative_power_lower
      commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
      commonSource.halfOffsetLineClassTargetDelta_pos
      (htarget commonSource hdelta hdeltaTarget) houtputLoss

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- Density on the literal actual terminal, specialized to the requested
`targetDelta ^ outputLoss`.  All geometric mass transport is discharged by
the existing terminal receipt; the displayed source inequality is the exact
remaining scalar/cardinality budget. -/
theorem cubicalShading_dense_at_outputLoss_of_source_receipt
    (terminal : commonSource.TerminalGeometry)
    (outputLoss : ℝ)
    (hsource :
      Kakeya.realRpowENN terminal.targetDelta outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              terminal.family.enncard) ≤
        ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal
              (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal
                commonSource.halfOffsetAssembly.horizontalSource.m *
              terminal.retubing.popular.sourceShading.mass))) :
    terminal.cubicalShading.IsLambdaDense
      (Kakeya.realRpowENN terminal.targetDelta outputLoss) := by
  apply pureWZ2_affineDiagonal_dense_of_mass_budget terminal.cubicalShading
    commonSource.halfOffsetLineClassTargetDelta_pos
    (le_trans (le_of_lt commonSource.halfOffsetLineClassTargetDelta_small)
      (by norm_num)) terminal.line_class
  exact terminal.composite_mass_card_receipt_of_source_receipt commonSource
    (Kakeya.realRpowENN terminal.targetDelta outputLoss) hsource

end TerminalGeometry

namespace TerminalPlaneData

/-- Fixed coefficient dominating the occupied-cover cardinality, its cubical
cover, and the outer factor in the public local-grain constructor. -/
def halfOffsetTerminalLocalGrainAbsorptionConstant : ENNReal :=
  15 * (9 * 500000 * 1728)

private theorem source_half_interval_slope_product_lower
    :
    Kakeya.realRpowENN delta (2 * epsilon) / 500000 ≤
      ENNReal.ofReal
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2) := by
  have hrhoPos : 0 < commonSource.halfOffsetAssembly.rho.1 :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.trans_le
      commonSource.halfOffsetAssembly.rho.2.1
  have hm : commonSource.halfOffsetAssembly.rho.1 ≤
      commonSource.halfOffsetAssembly.horizontalSource.m := by
    rw [← commonSource.halfOffsetAssembly.horizontalSource_scale]
    exact commonSource.halfOffsetAssembly.horizontalSource.slopeScale_lower
  have hlength :
      commonSource.halfOffsetAssembly.horizontalSource.d -
          commonSource.halfOffsetAssembly.horizontalSource.c =
        commonSource.halfOffsetAssembly.rho.1 / 100 := by
    rw [commonSource.halfOffsetAssembly.horizontalSource.length_eq,
      commonSource.halfOffsetAssembly.horizontalSource_scale]
  have hreal : Real.rpow delta (2 * epsilon) / 500000 ≤
      commonSource.halfOffsetAssembly.horizontalSource.m *
        (commonSource.halfOffsetAssembly.horizontalSource.d -
          commonSource.halfOffsetAssembly.horizontalSource.c) / 2 := by
    rw [hlength, commonSource.halfOffsetAssembly_rho_eq_power_div]
    have hpow : Real.rpow delta (2 * epsilon) =
        Real.rpow delta epsilon * Real.rpow delta epsilon := by
      calc
        Real.rpow delta (2 * epsilon) =
            Real.rpow delta (epsilon + epsilon) := by congr 1 <;> ring
        _ = Real.rpow delta epsilon * Real.rpow delta epsilon :=
          Real.rpow_add
            commonSource.halfOffsetAssembly.cfg.extremal.delta_pos _ _
    rw [hpow]
    have hp : 0 < Real.rpow delta epsilon :=
      Real.rpow_pos_of_pos
        commonSource.halfOffsetAssembly.cfg.extremal.delta_pos _
    have hmul := mul_le_mul_of_nonneg_right hm hp.le
    rw [commonSource.halfOffsetAssembly_rho_eq_power_div] at hmul
    nlinarith
  calc
    Kakeya.realRpowENN delta (2 * epsilon) / 500000 =
        ENNReal.ofReal (Real.rpow delta (2 * epsilon) / 500000) := by
      rw [Kakeya.realRpowENN]
      norm_num [ENNReal.ofReal_div_of_pos]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

private def toLocalGrainDataAtOutputLoss
    (data : commonSource.TerminalPlaneData)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (outputLoss : ℝ)
    {Csource : ENNReal}
    (hCsourceOne : 1 ≤ Csource) (hCsourceTop : Csource ≠ ⊤)
    (hlarge : (338 : ENNReal) ≤ Csource)
    (hsmall : ∀ (rho : ℝ) (n : ℕ),
      0 < rho → rho ≤ 1 / 6400 →
      (n : ℝ) ≤ 9 *
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹ →
      (n : ENNReal) *
          ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ≤ Csource)
    (hfinal : 15 * Csource ≤
      Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss))
    (houtputOne : 1 ≤
      Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss)) :
    PureWZ2LocalGrainData data.shading sigma
      (Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss)) := by
  have hsource := data.toLocalGrainData commonSource hsigma hsigmaOne
    hCsourceOne hCsourceTop hlarge hsmall
  exact hsource.weaken_constant hfinal (by
    simp [Kakeya.realRpowENN])

/-- For a strict source-to-terminal exponent gap, one pre-runtime threshold
absorbs every occupied-cover constant and returns the actual terminal local
grains with exactly the public constant `targetDelta ^ (-outputLoss)`. -/
theorem exists_delta_for_localGrainData_at_outputLoss
    (epsilon technicalLoss outputLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (htechnicalLoss : 0 ≤ technicalLoss)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : technicalLoss + 2 * epsilon <
      (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        commonSource.halfOffsetAssembly.technicalLoss ≤ technicalLoss →
        0 < sigma → sigma < 1 →
        0 < delta → delta ≤ delta₀ →
        ∀ data : commonSource.TerminalPlaneData,
          Nonempty <| PureWZ2LocalGrainData data.shading sigma
            (Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss)) := by
  rcases
      exists_delta_for_halfOffsetLineClass_constant_source_negative_le_target_negative
        epsilon (technicalLoss + 2 * epsilon) outputLoss
        halfOffsetTerminalLocalGrainAbsorptionConstant (by
          norm_num [halfOffsetTerminalLocalGrainAbsorptionConstant])
        hepsilon houtputLoss hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource htechnical hsigma hsigmaOne
    hdelta hdeltaBound data
  let sourceProduct : ENNReal :=
    ENNReal.ofReal
      (commonSource.halfOffsetAssembly.horizontalSource.m *
        (commonSource.halfOffsetAssembly.horizontalSource.d -
          commonSource.halfOffsetAssembly.horizontalSource.c) / 2)
  let Csource : ENNReal :=
    (9 * 500000 * 1728) *
      Kakeya.realRpowENN delta (-(technicalLoss + 2 * epsilon))
  have hproductLower := source_half_interval_slope_product_lower
    commonSource
  have hinv : sourceProduct⁻¹ ≤
      500000 * Kakeya.realRpowENN delta (-(2 * epsilon)) := by
    have hinvRaw : sourceProduct⁻¹ ≤
        (Kakeya.realRpowENN delta (2 * epsilon) / 500000)⁻¹ :=
      (ENNReal.inv_le_inv).2 hproductLower
    have hpowerInv :
        (Kakeya.realRpowENN delta (2 * epsilon))⁻¹ =
          Kakeya.realRpowENN delta (-(2 * epsilon)) :=
      pure_wz2_realRpowENN_inv
        commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
    calc
      sourceProduct⁻¹ ≤
          (Kakeya.realRpowENN delta (2 * epsilon) / 500000)⁻¹ := hinvRaw
      _ = (500000 : ENNReal) *
          (Kakeya.realRpowENN delta (2 * epsilon))⁻¹ := by
        rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        rw [div_eq_mul_inv]
      _ = 500000 * Kakeya.realRpowENN delta (-(2 * epsilon)) := by
        rw [hpowerInv]
  have hCsourceOne : 1 ≤ Csource := by
    have hdeltaOne : delta ≤ 1 :=
      hdeltaBound.trans hdelta₀One
    have hpowerOne : 1 ≤
        Kakeya.realRpowENN delta (-(technicalLoss + 2 * epsilon)) := by
      simpa [Kakeya.realRpowENN] using
        (pure_wz2_rpowENN_antitone hdelta hdeltaOne
          (by linarith : -(technicalLoss + 2 * epsilon) ≤ 0))
    dsimp only [Csource]
    calc
      1 ≤ (9 * 500000 * 1728 : ENNReal) := by norm_num
      _ ≤ (9 * 500000 * 1728) *
          Kakeya.realRpowENN delta (-(technicalLoss + 2 * epsilon)) := by
        simpa using mul_le_mul_left' hpowerOne (9 * 500000 * 1728 : ENNReal)
  have hCsourceTop : Csource ≠ ⊤ := by
    dsimp only [Csource]
    exact ENNReal.mul_ne_top (by norm_num) (by
      simp [Kakeya.realRpowENN])
  have hlarge : (338 : ENNReal) ≤ Csource := by
    calc
      (338 : ENNReal) ≤ 9 * 500000 * 1728 := by norm_num
      _ ≤ Csource := by
        dsimp only [Csource]
        have hdeltaOne : delta ≤ 1 := hdeltaBound.trans hdelta₀One
        have hpowerOne : 1 ≤
            Kakeya.realRpowENN delta (-(technicalLoss + 2 * epsilon)) :=
          by
            simpa [Kakeya.realRpowENN] using
              (pure_wz2_rpowENN_antitone hdelta hdeltaOne (by
                linarith : -(technicalLoss + 2 * epsilon) ≤ 0))
        simpa using mul_le_mul_left' hpowerOne (9 * 500000 * 1728 : ENNReal)
  have hsmall : ∀ (rho : ℝ) (n : ℕ),
      0 < rho → rho ≤ 1 / 6400 →
      (n : ℝ) ≤ 9 *
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹ →
      (n : ENNReal) *
          ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ≤ Csource := by
    intro rho n hrho _ hn
    have hratio : (5 * rho) / rho = 5 := by field_simp [hrho.ne']
    have hnENN : (n : ENNReal) ≤ 9 * sourceProduct⁻¹ := by
      rw [← ENNReal.ofReal_natCast]
      apply (ENNReal.ofReal_le_ofReal hn).trans_eq
      dsimp only [sourceProduct]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
        ENNReal.ofReal_inv_of_pos]
      · norm_num
      · have hm :=
          commonSource.halfOffsetAssembly.horizontalSource.slopeScale_pos
        have hlength :=
          commonSource.halfOffsetAssembly.horizontalSource.ordered
        positivity
    rw [hratio]
    have hcover :
        ((2 : ENNReal) * ((Nat.ceil (5 : ℝ) : ENNReal) + 1)) ^ 3 = 1728 := by
      norm_num
    have hnPower : (n : ENNReal) ≤
        9 * (500000 * Kakeya.realRpowENN delta (-(2 * epsilon))) :=
      hnENN.trans (mul_le_mul_left' hinv 9)
    rw [hcover]
    have htechnicalPower :
        Kakeya.realRpowENN delta
            (-commonSource.halfOffsetAssembly.technicalLoss) ≤
          Kakeya.realRpowENN delta (-technicalLoss) := by
      rw [Kakeya.realRpowENN, Kakeya.realRpowENN]
      exact ENNReal.ofReal_le_ofReal <|
        Real.rpow_le_rpow_of_exponent_ge hdelta
          (hdeltaBound.trans hdelta₀One) (by linarith)
    calc
      (n : ENNReal) *
          (1728 * Kakeya.realRpowENN delta
            (-commonSource.halfOffsetAssembly.technicalLoss)) ≤
        (9 * (500000 * Kakeya.realRpowENN delta (-(2 * epsilon)))) *
          (1728 * Kakeya.realRpowENN delta (-technicalLoss)) := by
            calc
              _ ≤ (9 * (500000 * Kakeya.realRpowENN delta
                    (-(2 * epsilon)))) *
                  (1728 * Kakeya.realRpowENN delta
                    (-commonSource.halfOffsetAssembly.technicalLoss)) := by
                      exact mul_le_mul_right' hnPower _
              _ ≤ _ := by gcongr
      _ = Csource := by
        dsimp only [Csource]
        have hpow :
            Kakeya.realRpowENN delta (-(2 * epsilon)) *
                Kakeya.realRpowENN delta (-technicalLoss) =
              Kakeya.realRpowENN delta
                (-(technicalLoss + 2 * epsilon)) := by
          rw [← realRpowENN_add
            commonSource.halfOffsetAssembly.cfg.extremal.delta_pos]
          congr 1 <;> ring
        calc
          _ = (9 * 500000 * 1728) *
              (Kakeya.realRpowENN delta (-(2 * epsilon)) *
                Kakeya.realRpowENN delta (-technicalLoss)) := by ac_rfl
          _ = _ := by rw [hpow]
  have hfinal : 15 * Csource ≤
      Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss) := by
    simpa [Csource, halfOffsetTerminalLocalGrainAbsorptionConstant, mul_assoc]
      using habsorb commonSource hdelta hdeltaBound
  have houtputOne : 1 ≤
      Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss) := by
    simpa [Kakeya.realRpowENN] using
      (pure_wz2_rpowENN_antitone
        commonSource.halfOffsetLineClassTargetDelta_pos
        (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
        (by linarith : -outputLoss ≤ 0))
  exact ⟨data.toLocalGrainDataAtOutputLoss commonSource hsigma hsigmaOne
    outputLoss hCsourceOne hCsourceTop hlarge hsmall hfinal houtputOne⟩

/-- Uniform pre-runtime version of the terminal local-grain budget.  The
threshold is chosen with the worst allowed technical loss `2 * epsilon`; the
runtime assembly then supplies that bound internally. -/
theorem exists_delta_for_localGrainData_at_outputLoss_uniform
    (epsilon outputLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (houtputLoss : 0 ≤ outputLoss)
    (hgap : 4 * epsilon < (1 - 2 * epsilon) * outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ}
        {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < sigma → sigma < 1 →
        0 < delta → delta ≤ delta₀ →
        ∀ data : commonSource.TerminalPlaneData,
          Nonempty <| PureWZ2LocalGrainData data.shading sigma
            (Kakeya.realRpowENN data.geometry.targetDelta (-outputLoss)) := by
  rcases exists_delta_for_localGrainData_at_outputLoss
      epsilon (2 * epsilon) outputLoss hepsilon
      (by linarith) houtputLoss (by nlinarith [hgap]) with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hlocalGrains⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource hsigma hsigmaOne
    hdelta hdeltaBound data
  exact hlocalGrains commonSource
    commonSource.halfOffsetAssembly.technicalLoss_le_two_epsilon
    hsigma hsigmaOne hdelta hdeltaBound data

end TerminalPlaneData

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
