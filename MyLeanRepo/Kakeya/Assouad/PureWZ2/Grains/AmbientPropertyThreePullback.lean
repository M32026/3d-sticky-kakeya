import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SubfamilyShadingExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackAD

/-!
# Ambient lift of one sticky Property-P pullback

One Node-3 sticky witness first selects a fine tube subfamily.  The genuine
Property-P pullback therefore initially lives on that selected family.  This
file zero-extends the pullback to the original source family and proves that
the lift preserves exactly the union and mass, remains cubical, and is a
subshading of the original source shading.

This removes the dependent-family mismatch between witnesses at different
scales.  It does not assert that independently selected witnesses have a
large intersection; that separate quantitative issue must not be hidden by
the reindexing step.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The whole-cell Property-P pullback, zero-extended from the selected fine
family to the ambient source family. -/
noncomputable def ambientPropertyThreePullback
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    WZ1PaperTubeShading source :=
  extendShading sticky.selected
    (propertyThreeFinePullbackShading
      sticky.cover sticky.refined propertyThree)

/-- On a selected ambient tube, the lifted carrier is definitionally the
fine Property-P pullback carrier. -/
lemma ambientPropertyThreePullback_carrier_selected
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (index : Fin sticky.selected.family.card) :
    (ambientPropertyThreePullback sticky propertyThree).carrier
        (sticky.selected.embedding index) =
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree).carrier index := by
  exact extendShading_carrier_mem

/-- The ambient lift is a genuine subshading of the source shading. -/
lemma ambientPropertyThreePullback_subshading
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    PaperIsSubshading
      (ambientPropertyThreePullback sticky propertyThree) sourceShading := by
  intro ambientIndex point hpoint
  by_cases himage : ∃ selectedIndex,
      sticky.selected.embedding selectedIndex = ambientIndex
  · rcases himage with ⟨selectedIndex, rfl⟩
    rw [ambientPropertyThreePullback_carrier_selected sticky propertyThree
      selectedIndex] at hpoint
    exact sticky.subshading selectedIndex hpoint.1
  · have hempty :
        (ambientPropertyThreePullback sticky propertyThree).carrier
            ambientIndex = ∅ :=
      extendShading_carrier_empty himage
    rw [hempty] at hpoint
    exact False.elim hpoint

/-- Zero-extension preserves the selected fine pullback union exactly. -/
lemma ambientPropertyThreePullback_union
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    (ambientPropertyThreePullback sticky propertyThree).union =
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree).union := by
  exact extendShading_union _ _

/-- Zero-extension preserves shaded mass exactly. -/
lemma ambientPropertyThreePullback_mass
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    (ambientPropertyThreePullback sticky propertyThree).mass =
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree).mass := by
  exact extendShading_mass _ _

/-- Cubicality on the selected fine family survives zero-extension to the
ambient family. -/
lemma ambientPropertyThreePullback_cubical
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hpullbackCubical : WZ1PaperIsCubicalShading
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree)) :
    WZ1PaperIsCubicalShading
      (ambientPropertyThreePullback sticky propertyThree) := by
  intro ambientIndex point hpoint other hother
  by_cases himage : ∃ selectedIndex,
      sticky.selected.embedding selectedIndex = ambientIndex
  · rcases himage with ⟨selectedIndex, rfl⟩
    rw [ambientPropertyThreePullback_carrier_selected sticky propertyThree
      selectedIndex] at hpoint ⊢
    exact hpullbackCubical selectedIndex point hpoint hother
  · have hempty :
        (ambientPropertyThreePullback sticky propertyThree).carrier
            ambientIndex = ∅ :=
      extendShading_carrier_empty himage
    rw [hempty] at hpoint
    exact False.elim hpoint

/-- The explicit sticky multiplicity loss gives the same mass lower bound
after lifting back to the ambient source family. -/
lemma ambientPropertyThreePullback_mass_lower_of_sticky
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hdelta : 0 < delta)
    (hsub : PaperIsSubshading
      propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf :
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
        propertyThree.mass) :
    ((2 * stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky : ENNReal)⁻¹) *
        sticky.refined.mass ≤
      (ambientPropertyThreePullback sticky propertyThree).mass := by
  rw [ambientPropertyThreePullback_mass]
  exact propertyThreeFinePullback_mass_lower_of_sticky
    sticky propertyThree hdelta hsub hcubical hhalf

/-- Combine Node 3's selected-family retention with the Property-P pullback
loss.  This is the honest one-scale mass bound relative to the original
source shading; it is polynomial/polylogarithmic rather than near-full. -/
lemma ambientPropertyThreePullback_source_mass_lower
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hdelta : 0 < delta)
    (hsub : PaperIsSubshading
      propertyThree sticky.croppedCoarseShading)
    (hcubical : WZ1PaperIsCubicalShading propertyThree)
    (hhalf :
      (1 / 2 : ENNReal) * sticky.croppedCoarseShading.mass ≤
        propertyThree.mass) :
    ((2 * stickyCoarseMultiplicityCap sticky *
        stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky : ENNReal)⁻¹) *
        (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) ≤
      (ambientPropertyThreePullback sticky propertyThree).mass := by
  let factor : ENNReal :=
    (2 * stickyCoarseMultiplicityCap sticky *
      stickyCoarseMultiplicityCap sticky *
      stickyFiberMultiplicityCap sticky)⁻¹
  calc
    factor * (wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass) ≤
      factor * sticky.refined.mass := by
        gcongr
        exact sticky.retained_mass
    _ ≤ (ambientPropertyThreePullback sticky propertyThree).mass := by
      exact ambientPropertyThreePullback_mass_lower_of_sticky
        sticky propertyThree hdelta hsub hcubical hhalf

/-- Any paper-AD estimate on the selected fine pullback transports unchanged
to its ambient zero-extension because the underlying union is identical. -/
lemma ambientPropertyThreePullback_ad
    {delta sigma outputLoss queryScale alpha : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (v q : Point3) (C : ENNReal)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection v
        ((propertyThreeFinePullbackShading
            sticky.cover sticky.refined propertyThree).union ∩
          Metric.closedBall q (Real.sqrt queryScale)))
      queryScale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection v
        ((ambientPropertyThreePullback sticky propertyThree).union ∩
          Metric.closedBall q (Real.sqrt queryScale)))
      queryScale alpha C := by
  rw [ambientPropertyThreePullback_union]
  exact hAD

end Kakeya.Assouad.PureWZ2

end
