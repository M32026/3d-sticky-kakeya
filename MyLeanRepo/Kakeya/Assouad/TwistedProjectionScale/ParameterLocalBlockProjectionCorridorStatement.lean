import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicShearCorridorTransferStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockCinematicStatements

/-!
# One cinematic corridor containing a local parameter block

All collapsed parameter centers in a selected local block lie near one
`localCenter`.  Every active tube parameter is close to its assigned center.
Thus all local tube curves are close to one central cinematic curve.  After
undoing the common `c`-window shear, the entire local twisted projection lies
in one bounded-slope corridor at the local block scale.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Central unsheared cinematic curve attached to one local parameter block. -/
def parameterLocalBlockCentralCurve
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {epsilon : ℝ}
    (localBlock : ParameterLocalFullBlockData clustered epsilon)
    (f : SlopeFunction) :
    Kakeya.Cinematic.C2Function :=
  unshearedCinematicCurve
    (halfParameterSlopeCurve f localBlock.localCenter)
    localBlock.windowCenter

/--
Every subshading of one selected local parameter block has its full twisted
projection inside one explicit bounded-slope corridor.

The constants are deliberately rounded:

* `300 * blockScale` covers the `C²` distance from every active raw tube curve
  to the central sheared curve;
* the assigned-curve containment has radius at most
  `6020 * blockScale`;
* undoing a shear with `|windowCenter| ≤ 3` gives corridor radius
  `30100 * blockScale`;
* the central curve has first-derivative bound `128` before the shear and
  `131` afterwards.
-/
def ParameterLocalBlockProjectionCorridorStatement : Prop :=
  AssignedCurveProjectionContainmentFromVerticalChartStatement →
    CinematicShearCorridorTransferStatement →
      ∀ {delta : ℝ},
        0 < delta →
        delta ≤ 1 →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          IsInVerticalChart F →
          (∀ i : Fin F.card, |(tubeParams i).c| ≤ 2) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.union ⊆ horizontalSlab 0 1 →
            ∀ C lambda : ENNReal,
              ∀ clustered :
                  TubeParameterClusterFrostmanData
                    F Y C lambda delta,
                ∀ epsilon : ℝ,
                  ∀ localBlock :
                      ParameterLocalFullBlockData
                        clustered epsilon,
                    ∀ f : SlopeFunction,
                      f.IsNonsingular →
                      f 0 = 0 →
                        ∀ Z :
                            Kakeya.Streamlined.TubeShading
                              (parameterLocalBlockFamily
                                clustered localBlock.sourcePoints),
                          IsSubshading Z
                            (parameterLocalBlockShading
                              clustered localBlock.sourcePoints) →
                            twistedUnion Z f ⊆
                                Metric.cthickening
                                  (30100 * localBlock.blockScale)
                                  (cinematicExtensionGraph
                                    (parameterLocalBlockCentralCurve
                                      localBlock f)) ∧
                              LipschitzOnWith (131 : NNReal)
                                (parameterLocalBlockCentralCurve
                                  localBlock f).extension
                                (Set.Icc (0 : ℝ) 1)

end Kakeya.Assouad
