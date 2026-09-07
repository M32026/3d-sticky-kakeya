import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialHull
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmbientPropertyThreePullback

/-!
# Common-spatial form of a Property-P fine pullback

The raw Property-P pullback depends on the tube index.  First zero-extend it
to the ambient source family, then replace it by its common spatial hull in
the source shading.  The resulting shading has exactly the same union and AD
information, loses no additional mass, and preserves every source tube
membership at retained points.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The ambient Property-P pullback in common-spatial form. -/
def ambientPropertyThreeCommonHull
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
  paperCommonSpatialHull sourceShading
    (ambientPropertyThreePullback sticky propertyThree)

lemma ambientPropertyThreeCommonHull_subshading
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
      (ambientPropertyThreeCommonHull sticky propertyThree) sourceShading :=
  paperCommonSpatialHull_subshading _ _

/-- The common-spatial lift has exactly the genuine selected fine pullback
union. -/
lemma ambientPropertyThreeCommonHull_union
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    (ambientPropertyThreeCommonHull sticky propertyThree).union =
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree).union := by
  rw [ambientPropertyThreeCommonHull,
    paperCommonSpatialHull_union
      (ambientPropertyThreePullback_subshading sticky propertyThree),
    ambientPropertyThreePullback_union]

/-- Coarse Property-Three refinement is monotone after fine pullback. -/
lemma propertyThreeFinePullbackShading_mono
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    {first second : WZ1PaperTubeShading coarse}
    (hsub : PaperIsSubshading second first) :
    PaperIsSubshading
      (propertyThreeFinePullbackShading cover fineShading second)
      (propertyThreeFinePullbackShading cover fineShading first) := by
  intro source point hpoint
  refine ⟨hpoint.1, ?_⟩
  rcases hpoint.2 with ⟨witness, ⟨parent, hwitness⟩, hgrid⟩
  exact ⟨witness, ⟨parent, hsub parent hwitness⟩, hgrid⟩

/-- The ambient common-spatial lift is monotone in the selected coarse
Property-Three shading. -/
lemma ambientPropertyThreeCommonHull_mono
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    {first second : WZ1PaperTubeShading sticky.coarse}
    (hsub : PaperIsSubshading second first) :
    PaperIsSubshading
      (ambientPropertyThreeCommonHull sticky second)
      (ambientPropertyThreeCommonHull sticky first) := by
  intro sourceIndex point hpoint
  refine ⟨hpoint.1, ?_⟩
  have hsecond : point ∈
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined second).union := by
    rw [← ambientPropertyThreePullback_union sticky second]
    exact hpoint.2
  rcases hsecond with ⟨selectedIndex, hselected⟩
  rw [ambientPropertyThreePullback_union sticky first]
  exact ⟨selectedIndex,
    propertyThreeFinePullbackShading_mono
      sticky.cover sticky.refined hsub selectedIndex hselected⟩

/-- All source memberships are restored at every retained point. -/
lemma ambientPropertyThreeCommonHull_pointMultiplicity_eq
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse) :
    ∀ point ∈ (ambientPropertyThreeCommonHull sticky propertyThree).union,
      (ambientPropertyThreeCommonHull sticky propertyThree).pointMultiplicity
          point =
        sourceShading.pointMultiplicity point :=
  paperCommonSpatialHull_pointMultiplicity_eq _ _

/-- Whole-cell cubicality of the raw pullback passes to the common-spatial
ambient lift. -/
lemma ambientPropertyThreeCommonHull_cubical
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (hsourceCubical : WZ1PaperIsCubicalShading sourceShading)
    (hpullbackCubical : WZ1PaperIsCubicalShading
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propertyThree)) :
    WZ1PaperIsCubicalShading
      (ambientPropertyThreeCommonHull sticky propertyThree) := by
  exact paperCommonSpatialHull_cubical hsourceCubical
    (ambientPropertyThreePullback_cubical
      sticky propertyThree hpullbackCubical)

/-- The honest one-scale mass lower bound survives the common-spatial hull. -/
lemma ambientPropertyThreeCommonHull_source_mass_lower
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
      (ambientPropertyThreeCommonHull sticky propertyThree).mass := by
  exact (ambientPropertyThreePullback_source_mass_lower
    sticky propertyThree hdelta hsub hcubical hhalf).trans
      (paperCommonSpatialHull_mass_lower
        (ambientPropertyThreePullback_subshading sticky propertyThree))

/-- Paper AD on the genuine fine pullback transports unchanged to the
common-spatial ambient lift. -/
lemma ambientPropertyThreeCommonHull_ad
    {delta sigma outputLoss queryScale alpha : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (propertyThree : WZ1PaperTubeShading sticky.coarse)
    (plane center : Point3) (C : ENNReal)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection plane
        ((propertyThreeFinePullbackShading
            sticky.cover sticky.refined propertyThree).union ∩
          Metric.closedBall center (Real.sqrt queryScale)))
      queryScale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection plane
        ((ambientPropertyThreeCommonHull sticky propertyThree).union ∩
          Metric.closedBall center (Real.sqrt queryScale)))
      queryScale alpha C := by
  rw [ambientPropertyThreeCommonHull_union sticky propertyThree]
  exact hAD

end Kakeya.Assouad.PureWZ2

end
