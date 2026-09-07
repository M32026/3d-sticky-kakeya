import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements

/-!
# Legal literal-paper cubical image shading

Define each target carrier as the union of `delta / rho` grid cubes meeting
the literal affine image of the corresponding source carrier.  The supplied
one-tube image-carrier theorem proves the shading lies in its target tube.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_unit_rescaled_shading :
    WZ2PaperLiteralUnitRescaledShadingStatement := by
  intro hcarrier delta rho hdelta hrho hrhoOne hdeltaRho
    sourceFamily hsourceLine anchor hanchorLine hcovered
    familyData sourceShading
  let targetCarrier :
      Fin familyData.targetFamily.card → Set Point3 :=
    fun target =>
      wz1PaperCubicalSaturation (delta / rho)
        (wz2PaperLiteralUnitRescalingMap anchor hrho ''
          sourceShading.carrier (familyData.sourceIndex target))
  have hmeasurable :
      ∀ target, MeasurableSet (targetCarrier target) := by
    intro target
    exact
      wz1PaperCubicalSaturation_measurable
        (delta / rho) _
  have hsubset :
      ∀ target,
        targetCarrier target ⊆
          wz1PaperTubeCarrier
            (familyData.targetFamily.tube target) := by
    intro target
    exact
      hcarrier hdelta hrho hrhoOne hdeltaRho
        (sourceFamily.tube (familyData.sourceIndex target))
        anchor
        (familyData.targetFamily.tube target)
        (hsourceLine (familyData.sourceIndex target))
        hanchorLine
        (familyData.target_line_class target)
        (hcovered (familyData.sourceIndex target))
        (familyData.target_axis target)
        (sourceShading.carrier (familyData.sourceIndex target))
        (sourceShading.subset_body
          (familyData.sourceIndex target))
  let targetShading :
      WZ1PaperTubeShading familyData.targetFamily :=
    { carrier := targetCarrier
      measurable_carrier := hmeasurable
      subset_body := hsubset }
  have hcubical :
      WZ1PaperIsCubicalShading targetShading := by
    intro index point hpoint
    exact
      wz1PaperCubicalSaturation_isCubical
        (delta / rho) _ point hpoint
  exact
    ⟨{
      targetShading := targetShading
      target_carrier_eq := by
        intro target
        rfl
      target_cubical := hcubical }⟩

end Kakeya.Assouad

end
