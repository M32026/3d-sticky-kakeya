import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalExtremalBudgets

/-!
# Density receipt for the actual direct half-offset terminal

This wrapper keeps the final density call tied to the literal cubical
terminal shading.  The geometric construction supplies the mass retention;
the remaining power absorption is deliberately an explicit input.
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

/-- The full mass/card receipt factors through the actual retubing, the
two-coordinate popular box, and the terminal cubical saturation.  The
caller supplies only the final scalar absorption against the source mass. -/
theorem composite_mass_card_receipt_of_source_receipt
    (terminal : commonSource.TerminalGeometry)
    (density : ENNReal)
    (hsource :
      density *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              terminal.family.enncard) ≤
        ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          (ENNReal.ofReal
              (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
            (ENNReal.ofReal
                commonSource.halfOffsetAssembly.horizontalSource.m *
              terminal.retubing.popular.sourceShading.mass))) :
    density *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN terminal.targetDelta 2 *
            terminal.family.enncard) ≤
      terminal.cubicalShading.mass := by
  apply hsource.trans
  have hretubing :
      ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
          terminal.retubing.popular.sourceShading.mass =
        terminal.retubing.raw.exactShading.mass := by
    rw [terminal.retubing.raw.exactShading_mass]
    rw [terminal.retubing.popular.openSourceShading_mass]
  have hbox :
      ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalWidth ^ 2 / 9) *
          (ENNReal.ofReal commonSource.halfOffsetAssembly.horizontalSource.m *
            terminal.retubing.popular.sourceShading.mass) ≤
        terminal.box.restricted.mass :=
    by
      rw [hretubing]
      exact terminal.box.mass_lower
  exact (mul_le_mul_left' hbox
    (ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2))).trans
      terminal.mass_lower

/-- A scalar receipt against the selected `(x,z)` box transfers through the
literal cubical saturation of the actual terminal. -/
theorem mass_receipt_of_box_receipt
    (terminal : commonSource.TerminalGeometry)
    (density : ENNReal)
    (hbox :
      density *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              terminal.family.enncard) ≤
        ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          terminal.box.restricted.mass) :
    density *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN terminal.targetDelta 2 *
            terminal.family.enncard) ≤
      terminal.cubicalShading.mass :=
  hbox.trans terminal.mass_lower

/-- The actual terminal cubical shading is dense as soon as its explicit
source/box power absorption has supplied the displayed box receipt. -/
theorem cubicalShading_dense_of_box_receipt
    (terminal : commonSource.TerminalGeometry)
    (density : ENNReal)
    (hbox :
      density *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN terminal.targetDelta 2 *
              terminal.family.enncard) ≤
        ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
          terminal.box.restricted.mass) :
    terminal.cubicalShading.IsLambdaDense density := by
  apply pureWZ2_affineDiagonal_dense_of_mass_budget terminal.cubicalShading
    commonSource.halfOffsetLineClassTargetDelta_pos
    (le_trans (le_of_lt commonSource.halfOffsetLineClassTargetDelta_small)
      (by norm_num))
    terminal.line_class density
  exact mass_receipt_of_box_receipt commonSource terminal density hbox

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
