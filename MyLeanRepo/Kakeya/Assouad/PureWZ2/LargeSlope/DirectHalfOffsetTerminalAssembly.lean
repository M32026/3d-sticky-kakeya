import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalGeometry

/-!
# Actual direct half-offset terminal assembly

This module packages the literal exact and cubical outputs after the actual
target radius, carrier containment, and crop have been discharged.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

abbrev halfOffsetLineClassActualExactShading
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :=
  commonSource.halfOffsetLineClassTerminalExactShading retubing box
    commonSource.halfOffsetLineClassTargetDelta
    (commonSource.halfOffsetLineClass_exact_carrier retubing box)

abbrev halfOffsetLineClassActualCubicalShading
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :=
  commonSource.halfOffsetLineClassTerminalCubicalShading retubing box
    commonSource.halfOffsetLineClassTargetDelta
    commonSource.halfOffsetLineClassSourceDelta_pos
    commonSource.halfOffsetLineClassTargetDelta_pos
    commonSource.halfOffsetLineClass_radius_budget
    (commonSource.halfOffsetLineClass_cubical_crop retubing box)

theorem halfOffsetLineClassActualExactShading_union
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    (commonSource.halfOffsetLineClassActualExactShading retubing box).union =
      commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := pureWZ2DirectHalfOffsetTerminalLambda) := by
  exact commonSource.halfOffsetLineClassTerminalExactShading_union retubing box
    commonSource.halfOffsetLineClassTargetDelta
    (commonSource.halfOffsetLineClass_exact_carrier retubing box)

theorem halfOffsetLineClassActualExactShading_mass
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    (commonSource.halfOffsetLineClassActualExactShading retubing box).mass =
      ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
        box.restricted.mass := by
  exact commonSource.halfOffsetLineClassTerminalExactShading_mass retubing box
    commonSource.halfOffsetLineClassTargetDelta
    (commonSource.halfOffsetLineClass_exact_carrier retubing box)

theorem halfOffsetLineClassActualCubicalShading_cubical
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    WZ1PaperIsCubicalShading
      (commonSource.halfOffsetLineClassActualCubicalShading retubing box) := by
  exact commonSource.halfOffsetLineClassTerminalCubicalShading_cubical
    retubing box commonSource.halfOffsetLineClassTargetDelta
    commonSource.halfOffsetLineClassSourceDelta_pos
    commonSource.halfOffsetLineClassTargetDelta_pos
    commonSource.halfOffsetLineClass_radius_budget
    (commonSource.halfOffsetLineClass_cubical_crop retubing box)

theorem halfOffsetLineClassActualCubicalShading_targetWitness
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    ∀ point : {point : Point3 // point ∈
      (commonSource.halfOffsetLineClassActualCubicalShading retubing box).union},
      ∃ source : {point : Point3 // point ∈
        commonSource.halfOffsetTerminalExactSet retubing box
          (lambda := pureWZ2DirectHalfOffsetTerminalLambda)},
        dist (point : Point3) (source : Point3) ≤
          commonSource.halfOffsetLineClassTargetDelta * Real.sqrt 3 := by
  exact commonSource.halfOffsetLineClassTerminalCubicalShading_targetWitness
    retubing box commonSource.halfOffsetLineClassTargetDelta
    commonSource.halfOffsetLineClassSourceDelta_pos
    commonSource.halfOffsetLineClassTargetDelta_pos
    commonSource.halfOffsetLineClass_radius_budget
    (commonSource.halfOffsetLineClass_cubical_crop retubing box)

theorem halfOffsetLineClassActualCubicalShading_mass_lower
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
        box.restricted.mass ≤
      (commonSource.halfOffsetLineClassActualCubicalShading retubing box).mass := by
  exact commonSource.halfOffsetLineClassTerminalCubicalShading_mass_lower
    retubing box commonSource.halfOffsetLineClassTargetDelta
    commonSource.halfOffsetLineClassSourceDelta_pos
    commonSource.halfOffsetLineClassTargetDelta_pos
    commonSource.halfOffsetLineClass_radius_budget
    (commonSource.halfOffsetLineClass_cubical_crop retubing box)

structure TerminalGeometry where
  retubing : PureWZ2DirectAnisotropicRetubingData
    commonSource.halfOffsetAssembly
  box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
    pureWZ2DirectHalfOffsetTerminalWidth

theorem toTerminalGeometry : Nonempty commonSource.TerminalGeometry := by
  rcases commonSource.halfOffsetAssembly.toDirectAnisotropicRetubing with
    ⟨retubing⟩
  rcases commonSource.toHalfOffsetLineClassTerminalPopularBox retubing with
    ⟨box⟩
  exact ⟨⟨retubing, box⟩⟩

namespace TerminalGeometry

abbrev targetDelta (_terminal : commonSource.TerminalGeometry) : ℝ :=
  commonSource.halfOffsetLineClassTargetDelta

abbrev family (terminal : commonSource.TerminalGeometry) :=
  commonSource.halfOffsetLineClassTerminalFamily terminal.retubing terminal.box
    terminal.targetDelta

abbrev exactShading (terminal : commonSource.TerminalGeometry) :=
  commonSource.halfOffsetLineClassActualExactShading terminal.retubing
    terminal.box

abbrev cubicalShading (terminal : commonSource.TerminalGeometry) :=
  commonSource.halfOffsetLineClassActualCubicalShading terminal.retubing
    terminal.box

theorem line_class (terminal : commonSource.TerminalGeometry) :
    WZ1PaperIsLineClass terminal.family :=
  commonSource.halfOffsetLineClassTerminalFamily_line_class terminal.retubing
    terminal.box

theorem cubical (terminal : commonSource.TerminalGeometry) :
    WZ1PaperIsCubicalShading terminal.cubicalShading :=
  commonSource.halfOffsetLineClassActualCubicalShading_cubical
    terminal.retubing terminal.box

theorem exact_union (terminal : commonSource.TerminalGeometry) :
    terminal.exactShading.union =
      commonSource.halfOffsetTerminalExactSet terminal.retubing terminal.box
        (lambda := pureWZ2DirectHalfOffsetTerminalLambda) :=
  commonSource.halfOffsetLineClassActualExactShading_union terminal.retubing
    terminal.box

theorem mass_lower (terminal : commonSource.TerminalGeometry) :
    ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
        terminal.box.restricted.mass ≤ terminal.cubicalShading.mass :=
  commonSource.halfOffsetLineClassActualCubicalShading_mass_lower
    terminal.retubing terminal.box

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
