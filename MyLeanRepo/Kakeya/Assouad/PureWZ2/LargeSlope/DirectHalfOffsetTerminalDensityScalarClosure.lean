import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# Scalar closure for density of the actual direct half-offset terminal

The retained-mass chain is the literal paper route: the Section-6 source
cardinality floor, the fixed `1/8` popular box, exact triangular Jacobian,
the two-coordinate terminal box, and terminal cubical saturation.  Only the
final source-to-target scalar comparison is left to a pre-runtime budget.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- Literal source-scale provenance for the direct half-offset construction.
The interval has length `rho / 100`, the slope scale dominates `rho`, and
`rho = delta^epsilon / 50`; hence the two source factors supply two copies
of the epsilon power before any terminal-scale comparison is made. -/
theorem source_interval_slope_product_lower
    :
    Kakeya.realRpowENN delta (2 * epsilon) / 250000 ≤
      ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
        ENNReal.ofReal
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) := by
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
  have hreal : Real.rpow delta (2 * epsilon) / 250000 ≤
      commonSource.halfOffsetAssembly.horizontalSource.m *
        (commonSource.halfOffsetAssembly.horizontalSource.d -
          commonSource.halfOffsetAssembly.horizontalSource.c) := by
    rw [hlength, commonSource.halfOffsetAssembly_rho_eq_power_div]
    have hpow : Real.rpow delta (2 * epsilon) =
        Real.rpow delta epsilon * Real.rpow delta epsilon := by
      calc
        Real.rpow delta (2 * epsilon) = Real.rpow delta (epsilon + epsilon) := by
          congr 1
          ring
        _ = Real.rpow delta epsilon * Real.rpow delta epsilon :=
          Real.rpow_add commonSource.halfOffsetAssembly.cfg.extremal.delta_pos _ _
    rw [hpow]
    have hp : 0 < Real.rpow delta epsilon :=
      Real.rpow_pos_of_pos commonSource.halfOffsetAssembly.cfg.extremal.delta_pos _
    have hmul := mul_le_mul_of_nonneg_right hm hp.le
    rw [commonSource.halfOffsetAssembly_rho_eq_power_div] at hmul
    nlinarith
  calc
    Kakeya.realRpowENN delta (2 * epsilon) / 250000 =
        ENNReal.ofReal (Real.rpow delta (2 * epsilon) / 250000) := by
          rw [Kakeya.realRpowENN]
          norm_num [ENNReal.ofReal_div_of_pos]
    _ ≤ ENNReal.ofReal
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
        ENNReal.ofReal
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) := by
      rw [ENNReal.ofReal_mul
        commonSource.halfOffsetAssembly.horizontalSource.slopeScale_pos.le]

/-- Pre-runtime power absorption for the literal direct terminal.  The two
source factors from `source_interval_slope_product_lower` contribute
`2 * epsilon`; the reciprocal-grid terminal costs `1 - 2 * epsilon`.  Thus
the displayed strict gap is exactly the remaining scalar condition. -/
theorem exists_delta_for_terminal_source_power_absorption
    (technicalLoss outputLoss : ℝ)
    (constant : ENNReal) (hconstant : constant ≠ ⊤)
    (hepsilon : 0 < epsilon)
    (hgap : technicalLoss + 2 + 2 * epsilon <
      (1 - 2 * epsilon) * (outputLoss + 2)) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        0 < delta → delta ≤ delta₀ →
        constant * Kakeya.realRpowENN delta
          ((1 - 2 * epsilon) * (outputLoss + 2)) ≤
          Kakeya.realRpowENN delta (technicalLoss + 2 + 2 * epsilon) := by
  rcases exists_delta_constant_mul_power_le_power constant hconstant
      (technicalLoss + 2 + 2 * epsilon)
      ((1 - 2 * epsilon) * (outputLoss + 2)) hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource hdelta hdeltaBound
  exact habsorb hdelta hdeltaBound

/-- The terminal indices embed into the original C2 configuration indices. -/
theorem family_enncard_le_cfg_enncard
    (terminal : commonSource.TerminalGeometry) :
    terminal.family.enncard ≤ commonSource.halfOffsetAssembly.cfg.family.enncard := by
  have hinj : Function.Injective (fun index : Fin terminal.family.card =>
      (wz2PaperNonemptyCarrierSubfamily
        terminal.retubing.popular.popular.restricted).embedding
        ((wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding
          index)) := by
    intro first second heq
    apply (wz2PaperNonemptyCarrierSubfamily terminal.box.restricted).embedding.injective
    apply (wz2PaperNonemptyCarrierSubfamily
      terminal.retubing.popular.popular.restricted).embedding.injective
    exact heq
  change (terminal.family.card : ENNReal) ≤
    (commonSource.halfOffsetAssembly.cfg.family.card : ENNReal)
  simpa using Fintype.card_le_of_injective _ hinj

/-- The full retained-mass chain, conditional on the displayed numerical
budget.  The public theorem below derives this budget uniformly from a
pre-runtime threshold. -/
private theorem cubicalShading_dense_at_outputLoss_of_budget
    (terminal : commonSource.TerminalGeometry)
    (outputLoss : ℝ)
    (hbudget :
    Kakeya.realRpowENN terminal.targetDelta outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              commonSource.halfOffsetAssembly.cfg.family.enncard) ≤
        ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal
              (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
              (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
                (ENNReal.ofReal (Real.pi / 4) *
                  Kakeya.realRpowENN delta
                    (commonSource.halfOffsetAssembly.technicalLoss + 2) *
                    commonSource.halfOffsetAssembly.cfg.family.enncard *
                    ENNReal.ofReal
                      (commonSource.halfOffsetAssembly.horizontalSource.d -
                        commonSource.halfOffsetAssembly.horizontalSource.c)))))) :
    terminal.cubicalShading.IsLambdaDense
      (Kakeya.realRpowENN terminal.targetDelta outputLoss) := by
  apply pureWZ2_affineDiagonal_dense_of_mass_budget terminal.cubicalShading
    commonSource.halfOffsetLineClassTargetDelta_pos
    (le_trans (le_of_lt commonSource.halfOffsetLineClassTargetDelta_small)
      (by norm_num)) terminal.line_class
  apply terminal.composite_mass_card_receipt_of_source_receipt commonSource
  have hcard := terminal.family_enncard_le_cfg_enncard commonSource
  have hsource := terminal.retubing.popular.source_mass_card
  calc
    Kakeya.realRpowENN terminal.targetDelta outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              terminal.family.enncard) ≤
        Kakeya.realRpowENN terminal.targetDelta outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              commonSource.halfOffsetAssembly.cfg.family.enncard) := by gcongr
    _ ≤ ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
              (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
                (ENNReal.ofReal (Real.pi / 4) *
                  Kakeya.realRpowENN delta
                    (commonSource.halfOffsetAssembly.technicalLoss + 2) *
                    commonSource.halfOffsetAssembly.cfg.family.enncard *
                    ENNReal.ofReal
                      (commonSource.halfOffsetAssembly.horizontalSource.d -
                        commonSource.halfOffsetAssembly.horizontalSource.c))))) := hbudget
    _ ≤ ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
              terminal.retubing.popular.sourceShading.mass)) := by
      have hscaled := mul_le_mul_left' hsource
        (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m)
      calc
        _ ≤ ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
            (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
              (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
                ((ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
                  (ENNReal.ofReal (Real.pi / 4) *
                    Kakeya.realRpowENN delta
                      (commonSource.halfOffsetAssembly.technicalLoss + 2) *
                    commonSource.halfOffsetAssembly.cfg.family.enncard *
                    ENNReal.ofReal
                      (commonSource.halfOffsetAssembly.horizontalSource.d -
                        commonSource.halfOffsetAssembly.horizontalSource.c)))))) := by
              gcongr
        _ ≤ _ := by
              simpa only [mul_assoc] using
                (mul_le_mul_left' hscaled
                  (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
                    ENNReal.ofReal
                      (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9)))

/-- Uniform density for the literal direct half-offset terminal.  The fixed
coefficient is absorbed before the runtime source is chosen; no scalar mass
receipt is retained in the public interface. -/
theorem exists_delta_for_cubicalShading_dense_at_outputLoss
    (technicalLoss outputLoss : ℝ)
    (hepsilon : 0 < epsilon)
    (houtput : 0 ≤ outputLoss + 2)
    (hgap : technicalLoss + 2 + 2 * epsilon <
      (1 - 2 * epsilon) * (outputLoss + 2)) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta),
        commonSource.halfOffsetAssembly.technicalLoss = technicalLoss →
        0 < delta → delta ≤ delta₀ →
        ∀ terminal : commonSource.TerminalGeometry,
          terminal.cubicalShading.IsLambdaDense
            (Kakeya.realRpowENN terminal.targetDelta outputLoss) := by
  let C : ENNReal :=
    ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
      (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
        (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
          ENNReal.ofReal (Real.pi / 4)))
  let S : ENNReal := C / 250000
  let K : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  have hCzero : C ≠ 0 := by
    dsimp [C]
    apply mul_ne_zero
    · exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos
        pureWZ2DirectHalfOffsetTerminalLambda_pos) |>.ne'
    apply mul_ne_zero
    · exact ENNReal.ofReal_pos.mpr (div_pos
        (sq_pos_of_pos pureWZ2DirectHalfOffsetTerminalWidth_pos)
        (by norm_num)) |>.ne'
    apply mul_ne_zero
    · norm_num
    exact ENNReal.ofReal_pos.mpr (by positivity) |>.ne'
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    repeat' apply ENNReal.mul_ne_top
    all_goals first | exact ENNReal.ofReal_ne_top | norm_num
  have hSzero : S ≠ 0 := by
    dsimp [S]
    exact (ENNReal.div_ne_zero).2 ⟨hCzero, by norm_num⟩
  have hStop : S ≠ ⊤ := by
    dsimp [S]
    exact ENNReal.div_ne_top hCtop (by norm_num)
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  rcases exists_delta_for_terminal_source_power_absorption
      (epsilon := epsilon) technicalLoss outputLoss (K / S)
      (ENNReal.div_ne_top hKtop hSzero) hepsilon hgap with
    ⟨absorbScale, habsorbScalePos, habsorbScaleOne, habsorb⟩
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_power_upper
      epsilon hepsilon with
    ⟨targetScale, htargetScalePos, htargetScaleOne, htarget⟩
  refine ⟨min absorbScale targetScale, lt_min habsorbScalePos htargetScalePos,
    (min_le_left _ _).trans habsorbScaleOne, ?_⟩
  intro logExponent sigma delta commonSource htechnical hdelta hdeltaBound terminal
  subst technicalLoss
  have hdeltaAbsorb : delta ≤ absorbScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaTarget : delta ≤ targetScale :=
    hdeltaBound.trans (min_le_right _ _)
  have htargetPower := pure_wz2_target_power_upper
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
    commonSource.halfOffsetLineClassTargetDelta_pos.le
    (htarget commonSource hdelta hdeltaTarget) houtput
  change Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) ≤ _ at htargetPower
  have habsorb' := habsorb commonSource hdelta hdeltaAbsorb
  have hKS : K = (K / S) * S :=
    (ENNReal.div_mul_cancel hSzero hStop).symm
  have hmain :
      K * Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) ≤
        S * Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) := by
    calc
      K * Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) ≤
          K * Kakeya.realRpowENN delta
            ((1 - 2 * epsilon) * (outputLoss + 2)) := by gcongr
      _ = ((K / S) * Kakeya.realRpowENN delta
            ((1 - 2 * epsilon) * (outputLoss + 2))) * S := by
          conv_lhs => rw [hKS]
          ac_rfl
      _ ≤ Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) * S := by
          gcongr
      _ = S * Kakeya.realRpowENN delta
            (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) := by
          ac_rfl
  have htargetAdd :
      Kakeya.realRpowENN terminal.targetDelta outputLoss *
        Kakeya.realRpowENN terminal.targetDelta 2 =
      Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2) := by
    rw [← realRpowENN_add commonSource.halfOffsetLineClassTargetDelta_pos]
  have hsourceAdd :
      Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2 + 2 * epsilon) =
        Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2) *
          Kakeya.realRpowENN delta (2 * epsilon) := by
    rw [← realRpowENN_add
      commonSource.halfOffsetAssembly.cfg.extremal.delta_pos]
  rw [hsourceAdd] at hmain
  have hsource := source_interval_slope_product_lower commonSource
  have hscaled := mul_le_mul_left' hsource
    (C * (Kakeya.realRpowENN delta
      (commonSource.halfOffsetAssembly.technicalLoss + 2) *
        commonSource.halfOffsetAssembly.cfg.family.enncard))
  refine cubicalShading_dense_at_outputLoss_of_budget commonSource terminal
    outputLoss ?_
  calc
    Kakeya.realRpowENN terminal.targetDelta outputLoss *
          (K * Kakeya.realRpowENN terminal.targetDelta 2 *
            commonSource.halfOffsetAssembly.cfg.family.enncard) =
        (K * Kakeya.realRpowENN terminal.targetDelta (outputLoss + 2)) *
          commonSource.halfOffsetAssembly.cfg.family.enncard := by
      rw [← htargetAdd]
      ac_rfl
    _ ≤ (S * (Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2) *
            Kakeya.realRpowENN delta (2 * epsilon))) *
          commonSource.halfOffsetAssembly.cfg.family.enncard := by
      gcongr
    _ = (C * (Kakeya.realRpowENN delta
          (commonSource.halfOffsetAssembly.technicalLoss + 2) *
            commonSource.halfOffsetAssembly.cfg.family.enncard)) *
          (Kakeya.realRpowENN delta (2 * epsilon) / 250000) := by
      dsimp [S]
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ac_rfl
    _ ≤ ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
              (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
                (ENNReal.ofReal (Real.pi / 4) *
                  Kakeya.realRpowENN delta
                    (commonSource.halfOffsetAssembly.technicalLoss + 2) *
                  commonSource.halfOffsetAssembly.cfg.family.enncard *
                  ENNReal.ofReal
                    (commonSource.halfOffsetAssembly.horizontalSource.d -
                      commonSource.halfOffsetAssembly.horizontalSource.c))))) := by
      dsimp [C] at hscaled
      convert hscaled using 1 <;> ac_rfl

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
