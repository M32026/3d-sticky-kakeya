import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.MultiplicityFiberCap

/-!
# Conditional Section 7 cinematic Hölder assembly

This statement exposes the exact completed leaves needed to turn a compact
positive-window shading and a cinematic multiplicity estimate into a lower
bound for the twisted union.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

def CompactAssignedCinematicHolderStatement : Prop :=
  CompactSubshadingSelectionStatement →
    CompactTubeTwistedProjectionAreaStatement →
      TubeParameterClusterFiberCapStatement →
        SelectedCurveAssignmentClusterStatement →
          SelectedCurveAssignmentFiberCapStatement →
            AssignedCurveProjectionContainmentStatement →
              ∀ (delta w : ℝ),
                0 < delta → delta ≤ 1 →
                0 < w → delta ≤ 500 * w → 500 * w ≤ 1 →
                ∀ F : Kakeya.Streamlined.TubeFamily delta,
                  HasBoundedBase F 4 →
                  IsInVerticalChart F →
                  ∀ C : ENNReal,
                    TubeParameterFrostmanBound F C →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      Y.union ⊆ horizontalSlab 0 1 →
                      ∀ f : SlopeFunction,
                        f.IsNonsingular → f 0 = 0 →
                        ∀ c0 : ℝ,
                          (∀ i, Y.carrier i ≠ ∅ →
                            |(tubeParams i).c - c0| ≤ w / 2) →
                          ∀ G : Kakeya.Cinematic.FiniteFunctionFamily,
                            (∀ i, Y.carrier i ≠ ∅ →
                              ∃ g ∈ G.carrier,
                                Kakeya.Cinematic.c2Distance
                                  (slopeCurve f (tubeParams i).a
                                    (tubeParams i).b (tubeParams i).d)
                                  g ≤ w) →
                            ∀ P : ENNReal,
                              eLpNorm
                                  (cinematicMultiplicityENN G
                                    (20 * (delta + w)))
                                  (3 / 2 : ENNReal) volume ≤ P →
                              ∃ Z : Kakeya.Streamlined.TubeShading F,
                                IsSubshading Z Y ∧
                                (1 / 2 : ENNReal) * Y.mass ≤ Z.mass ∧
                                volume (twistedUnion Z f) ≥
                                  ((Z.mass /
                                      ENNReal.ofReal (20 * delta)) /
                                    ((C *
                                        Kakeya.realRpowENN (500 * w) 2 *
                                        F.enncard) * P)) ^ 3

/--
Basepoint-free Hölder assembly for an already supplied finite cinematic
family.

All quantitative inputs after the curve family has been chosen use only the
vertical chart, the indexed parameter Frostman bound, and the active
`c`-window.  This is the form that can be reused by selected-scale families
whose supporting-line parameters remain bounded but whose stored segment
basepoints have changed.
-/
def CompactAssignedCinematicHolderFromVerticalChartStatement : Prop :=
  CompactSubshadingSelectionStatement →
    CompactTubeTwistedProjectionAreaStatement →
      TubeParameterClusterFiberCapStatement →
        SelectedCurveAssignmentClusterStatement →
          SelectedCurveAssignmentFiberCapStatement →
            AssignedCurveProjectionContainmentFromVerticalChartStatement →
              ∀ (delta w : ℝ),
                0 < delta → delta ≤ 1 →
                0 < w → delta ≤ 500 * w → 500 * w ≤ 1 →
                ∀ F : Kakeya.Streamlined.TubeFamily delta,
                  IsInVerticalChart F →
                  ∀ C : ENNReal,
                    TubeParameterFrostmanBound F C →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      Y.union ⊆ horizontalSlab 0 1 →
                      ∀ f : SlopeFunction,
                        f.IsNonsingular → f 0 = 0 →
                        ∀ c0 : ℝ,
                          (∀ i, Y.carrier i ≠ ∅ →
                            |(tubeParams i).c - c0| ≤ w / 2) →
                          ∀ G : Kakeya.Cinematic.FiniteFunctionFamily,
                            (∀ i, Y.carrier i ≠ ∅ →
                              ∃ g ∈ G.carrier,
                                Kakeya.Cinematic.c2Distance
                                  (slopeCurve f (tubeParams i).a
                                    (tubeParams i).b (tubeParams i).d)
                                  g ≤ w) →
                            ∀ P : ENNReal,
                              eLpNorm
                                  (cinematicMultiplicityENN G
                                    (20 * (delta + w)))
                                  (3 / 2 : ENNReal) volume ≤ P →
                              ∃ Z : Kakeya.Streamlined.TubeShading F,
                                IsSubshading Z Y ∧
                                (1 / 2 : ENNReal) * Y.mass ≤ Z.mass ∧
                                volume (twistedUnion Z f) ≥
                                  ((Z.mass /
                                      ENNReal.ofReal (20 * delta)) /
                                    ((C *
                                        Kakeya.realRpowENN (500 * w) 2 *
                                        F.enncard) * P)) ^ 3

end Kakeya.Assouad
