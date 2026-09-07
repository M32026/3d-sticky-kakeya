import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FiniteUniformCellGlobalization
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicCellSelectionStatement

/-!
# Globalize one local cinematic certificate

The prepared projected set is a finite union of comparable occupied cells.
A local set contained in one cinematic corridor is supported on only
linearly many of those cells.  The cancellation-free finite-cell theorem
therefore converts its area lower bound into a quantitative comparison
between the global projected set and its `rho`-thickening.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Explicit linear cell bound supplied by the cinematic corridor theorem. -/
def projectedFiberOSCinematicCellBound
    (base level slopeBlocks radiusBlocks : ℕ) : ℕ :=
  (base ^ level + 2 * radiusBlocks + 3) *
    (2 *
        (2 * radiusBlocks +
          slopeBlocks * (1 + 2 * radiusBlocks) + 2) +
      3)

/-- Common `rho`-thickening area bound for one occupied prepared cell. -/
def projectedFiberOSPreparedCellThickeningBound
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {f : SlopeFunction}
    (prepared : ProjectedFiberOSPreparationData (eta := eta) Y f)
    (rho : ℝ) : ENNReal :=
  ENNReal.ofReal
    (((((2 * prepared.base + 3 : ℕ) : ℝ) * rho) ^ 2) *
      Real.pi)

/--
Exact local-to-global inequality for one cinematic certificate.

The factor four is the planar cell-area comparability.  The remaining factors
are the explicit number of corridor cells and the single-cell thickening
area.  No total global cell count appears.
-/
def ProjectedFiberOSCinematicGlobalizationStatement : Prop :=
  PlanarGridCinematicCorridorCountStatement →
    ProjectedFiberOSCinematicCellSelectionStatement →
      ∀ {delta eta rho : ℝ},
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ f : SlopeFunction,
              ∀ prepared :
                  ProjectedFiberOSPreparationData (eta := eta) Y f,
                ∀ level : ℕ,
                  ∀ cellSystem :
                      ProjectedFiberOSLevelCellSystemData
                        (rho := rho) prepared level,
                    ∀ g : Kakeya.Cinematic.C2Function,
                      ∀ slopeBlocks radiusBlocks : ℕ,
                        LipschitzOnWith
                            (slopeBlocks : NNReal)
                            g.extension
                            (Set.Icc (0 : ℝ) 1) →
                        ∀ r : ℝ,
                          0 ≤ r →
                          projectedFiberOSCinematicExpandedRadius
                              prepared r ≤
                            (radiusBlocks : ℝ) *
                              ((prepared.base ^ level : ℝ)⁻¹) →
                          ∀ localSet : Set Point2,
                            localSet ⊆
                                twistedUnion
                                  prepared.density.globalShading f →
                            localSet ⊆
                                Metric.cthickening r
                                  (cinematicExtensionGraph g) →
                              ∀ L : ENNReal,
                                L ≤ volume localSet →
                                  L *
                                      volume
                                        (Metric.cthickening rho
                                          (twistedUnion
                                            prepared.density.globalShading
                                            f)) ≤
                                    4 *
                                      (projectedFiberOSCinematicCellBound
                                        prepared.base level
                                        slopeBlocks radiusBlocks :
                                        ENNReal) *
                                      projectedFiberOSPreparedCellThickeningBound
                                        prepared rho *
                                      volume
                                        (twistedUnion
                                          prepared.density.globalShading f)

end Kakeya.Assouad
