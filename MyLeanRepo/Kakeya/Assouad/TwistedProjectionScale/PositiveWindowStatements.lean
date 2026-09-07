import MyLeanRepo.Kakeya.Assouad.Inputs
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.AssemblyStatements

/-!
# Positive-window Section 7 statement

The indexed four-parameter Frostman condition is an explicit input.  No
carrier-model implication from `TubeWolffBound` is asserted.
-/

namespace Kakeya.Assouad

/--
Paper-faithful positive-window one-scale projection estimate with indexed
four-parameter Frostman non-concentration supplied explicitly.
-/
def PositiveWindowParameterFrostmanScaleStatement : Prop :=
  CompactAssignedCinematicHolderStatement →
    PYZInput →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∃ eta delta₀ : ℝ,
          0 < eta ∧ eta ≤ epsilon ∧
          0 < delta₀ ∧ delta₀ < 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              F.Nonempty →
              HasBoundedBase F 4 →
              F.IsEssentiallyDistinct →
              IsInVerticalChart F →
              ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                C ≤ Kakeya.realRpowENN delta (-eta) →
                TubeParameterFrostmanBound F C →
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  Y.IsLambdaDense
                      (Kakeya.realRpowENN delta eta) →
                  Y.union ⊆ horizontalSlab 0 1 →
                  ∀ f : SlopeFunction,
                    f.IsNonsingular → f 0 = 0 →
                      ∃ rho : ℝ,
                        Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                        rho < 1 ∧
                        ∃ Z : Kakeya.Streamlined.TubeShading F,
                          IsSubshading Z Y ∧
                          Z.IsLambdaDense
                            (Kakeya.realRpowENN delta (4 * eta)) ∧
                          MeasureTheory.volume (twistedUnion Z f) ≥
                            Kakeya.realRpowENN
                                (delta / rho) epsilon *
                              MeasureTheory.volume
                                (Metric.cthickening rho
                                  (twistedUnion Z f))

/--
Positive-window one-scale estimate with an adjustable loss parameter.

The paper chooses the structural loss sufficiently small relative to
`epsilon`; every still smaller positive loss is also admissible after
shrinking the scale threshold again.  The threshold is therefore quantified
after the concrete `eta`.  Requiring one threshold uniformly for all
`eta → 0` would be stronger than the fixed-constant absorption used in the
proof.

This is the adjustable-loss input needed by the iterable Section 7 boundary.
It avoids the previous obstruction where an existentially chosen loss could
not be matched to the effective losses of a later selected-scale coarse state.
The construction of that coarse state remains a separate geometric target.
-/
def PositiveWindowParameterFrostmanScaleAdjustableEtaStatement : Prop :=
  CompactAssignedCinematicHolderStatement →
    PYZInput →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ epsilon ∧
          ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
            ∃ delta₀ : ℝ,
              0 < delta₀ ∧ delta₀ < 1 ∧
              ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                ∀ F : Kakeya.Streamlined.TubeFamily delta,
                  F.Nonempty →
                  HasBoundedBase F 4 →
                  F.IsEssentiallyDistinct →
                  IsInVerticalChart F →
                  ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                    C ≤ Kakeya.realRpowENN delta (-eta) →
                    TubeParameterFrostmanBound F C →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      Y.IsLambdaDense
                          (Kakeya.realRpowENN delta eta) →
                      Y.union ⊆ horizontalSlab 0 1 →
                      ∀ f : SlopeFunction,
                        f.IsNonsingular → f 0 = 0 →
                          ∃ rho : ℝ,
                            Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                            rho < 1 ∧
                            ∃ Z : Kakeya.Streamlined.TubeShading F,
                              IsSubshading Z Y ∧
                              Z.IsLambdaDense
                                (Kakeya.realRpowENN delta (4 * eta)) ∧
                              MeasureTheory.volume (twistedUnion Z f) ≥
                                Kakeya.realRpowENN
                                    (delta / rho) epsilon *
                                  MeasureTheory.volume
                                    (Metric.cthickening rho
                                      (twistedUnion Z f))

/--
Iterable positive-window one-scale estimate from an explicit line-parameter
certificate.

After selected-scale rediscretization the modeled unit segments need not keep
the original radius-four basepoints, but their supporting lines retain the
same bounded `(a,b,c,d)` parameters.  Every use of the old basepoint
hypothesis in the one-scale route is replaced here by that certificate and by
the basepoint-free cinematic Holder assembly.  The adjustable-loss quantifier
order is unchanged: each concrete `eta` may shrink its own scale threshold.
-/
def PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersStatement :
    Prop :=
  CompactAssignedCinematicHolderFromVerticalChartStatement →
    PYZInput →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ epsilon ∧
          ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
            ∃ delta₀ : ℝ,
              0 < delta₀ ∧ delta₀ < 1 ∧
              ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                ∀ F : Kakeya.Streamlined.TubeFamily delta,
                  F.Nonempty →
                  IsInVerticalChart F →
                  (∀ i : Fin F.card,
                    |(tubeParams i).a| ≤ 12 ∧
                      |(tubeParams i).b| ≤ 12 ∧
                      |(tubeParams i).c| ≤ 2 ∧
                      |(tubeParams i).d| ≤ 2) →
                  F.IsEssentiallyDistinct →
                  ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                    C ≤ Kakeya.realRpowENN delta (-eta) →
                    TubeParameterFrostmanBound F C →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      Y.IsLambdaDense
                          (Kakeya.realRpowENN delta eta) →
                      Y.union ⊆ horizontalSlab 0 1 →
                      ∀ f : SlopeFunction,
                        f.IsNonsingular → f 0 = 0 →
                          ∃ rho : ℝ,
                            Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                            rho < 1 ∧
                            ∃ Z : Kakeya.Streamlined.TubeShading F,
                              IsSubshading Z Y ∧
                              Z.IsLambdaDense
                                (Kakeya.realRpowENN delta (4 * eta)) ∧
                              MeasureTheory.volume (twistedUnion Z f) ≥
                                Kakeya.realRpowENN
                                    (delta / rho) epsilon *
                                  MeasureTheory.volume
                                    (Metric.cthickening rho
                                      (twistedUnion Z f))

/--
Bounded-scale version of the iterable parameter-certificate theorem.

The caller chooses `rhoMax` before the structural loss.  The proof may then
shrink its scale threshold so the fixed test radius `rhoMax / 2` lies above
`delta^(1-epsilon^2)`.  This is the form needed before selected-scale
rediscretization, whose four-block geometry requires `rho ≤ 1/8`.
-/
def
    PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersBoundedStatement :
    Prop :=
  CompactAssignedCinematicHolderFromVerticalChartStatement →
    PYZInput →
      ∀ epsilon rhoMax : ℝ,
        0 < epsilon → epsilon < 1 →
        0 < rhoMax → rhoMax ≤ 1 →
          ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ epsilon ∧
            ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
              ∃ delta₀ : ℝ,
                0 < delta₀ ∧ delta₀ < 1 ∧
                ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                  ∀ F : Kakeya.Streamlined.TubeFamily delta,
                    F.Nonempty →
                    IsInVerticalChart F →
                    (∀ i : Fin F.card,
                      |(tubeParams i).a| ≤ 12 ∧
                        |(tubeParams i).b| ≤ 12 ∧
                        |(tubeParams i).c| ≤ 2 ∧
                        |(tubeParams i).d| ≤ 2) →
                    F.IsEssentiallyDistinct →
                    ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                      C ≤ Kakeya.realRpowENN delta (-eta) →
                      TubeParameterFrostmanBound F C →
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        Y.IsLambdaDense
                            (Kakeya.realRpowENN delta eta) →
                        Y.union ⊆ horizontalSlab 0 1 →
                        ∀ f : SlopeFunction,
                          f.IsNonsingular → f 0 = 0 →
                            ∃ rho : ℝ,
                              Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                              rho ≤ rhoMax ∧
                              ∃ Z : Kakeya.Streamlined.TubeShading F,
                                IsSubshading Z Y ∧
                                Z.IsLambdaDense
                                  (Kakeya.realRpowENN delta (4 * eta)) ∧
                                MeasureTheory.volume (twistedUnion Z f) ≥
                                  Kakeya.realRpowENN
                                      (delta / rho) epsilon *
                                    MeasureTheory.volume
                                      (Metric.cthickening rho
                                        (twistedUnion Z f))

/--
Bounded-scale positive-window estimate without an essential-distinctness
premise.

The analytic proof uses only indexed parameter Frostman control: it constructs
a finite set of active parameter points, applies the no-separation
Frostman-to-Katz--Tao extraction, and bounds assignment fibers directly by the
indexed four-parameter Frostman hypothesis.  Pairwise volume-half
essential-distinctness of the tube carriers is not consumed by those steps.

This is the iterable boundary needed by the full selected four-block family
before any cross-block conflict coloring.
-/
def
    PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersBoundedNoDistinctStatement :
    Prop :=
  CompactAssignedCinematicHolderFromVerticalChartStatement →
    PYZInput →
      ∀ epsilon rhoMax : ℝ,
        0 < epsilon → epsilon < 1 / 100 →
        0 < rhoMax → rhoMax ≤ 1 →
        1 / 100 ≤ rhoMax →
          ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ epsilon ∧
            ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
              ∃ delta₀ : ℝ,
                0 < delta₀ ∧ delta₀ < 1 ∧
                ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                  ∀ F : Kakeya.Streamlined.TubeFamily delta,
                    F.Nonempty →
                    IsInVerticalChart F →
                    (∀ i : Fin F.card,
                      |(tubeParams i).a| ≤ 12 ∧
                        |(tubeParams i).b| ≤ 12 ∧
                        |(tubeParams i).c| ≤ 2 ∧
                        |(tubeParams i).d| ≤ 2) →
                    ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                      C ≤ Kakeya.realRpowENN delta (-eta) →
                      TubeParameterFrostmanBound F C →
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        Y.IsLambdaDense
                            (Kakeya.realRpowENN delta eta) →
                        Y.union ⊆ horizontalSlab 0 1 →
                        ∀ f : SlopeFunction,
                          f.IsNonsingular → f 0 = 0 →
                            ∃ rho : ℝ,
                              Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                              rho ≤ rhoMax ∧
                              ∃ Z : Kakeya.Streamlined.TubeShading F,
                                IsSubshading Z Y ∧
                                Z.IsLambdaDense
                                  (Kakeya.realRpowENN delta (4 * eta)) ∧
                                MeasureTheory.volume (twistedUnion Z f) ≥
                                  Kakeya.realRpowENN
                                      (delta / rho) epsilon *
                                    MeasureTheory.volume
                                      (Metric.cthickening rho
                                        (twistedUnion Z f))

/--
Full-window one-scale estimate obtained by selecting one vertical half-window.

The input density exponent is `eta / 2`, leaving a positive power gap to
absorb the fixed one-half mass loss before applying the positive-window
theorem at exponent `eta`.  The negative half is transported by the exact
vertical reflection package and returned as a subshading of the original
family.
-/
def SignedWindowParameterFrostmanScaleStatement : Prop :=
  HalfWindowMassSelectionStatement →
    ReflectedSlopeCinematicStatement →
      Section7VerticalReflectionStatement →
        PositiveWindowParameterFrostmanScaleStatement →
          CompactAssignedCinematicHolderStatement →
            PYZInput →
              ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
                ∃ eta delta₀ : ℝ,
                  0 < eta ∧ eta ≤ epsilon ∧
                  0 < delta₀ ∧ delta₀ < 1 ∧
                  ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                    ∀ F : Kakeya.Streamlined.TubeFamily delta,
                      F.Nonempty →
                      HasBoundedBase F 4 →
                      F.IsEssentiallyDistinct →
                      IsInVerticalChart F →
                      ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                        C ≤ Kakeya.realRpowENN delta (-eta) →
                        TubeParameterFrostmanBound F C →
                        ∀ Y : Kakeya.Streamlined.TubeShading F,
                          Y.IsLambdaDense
                            (Kakeya.realRpowENN delta (eta / 2)) →
                          IsInSlopeWindow Y →
                          ∀ f : SlopeFunction,
                            f.IsNonsingular → f 0 = 0 →
                              ∃ rho : ℝ,
                                Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                                rho < 1 ∧
                                ∃ Z : Kakeya.Streamlined.TubeShading F,
                                  IsSubshading Z Y ∧
                                  Z.IsLambdaDense
                                    (Kakeya.realRpowENN delta (4 * eta)) ∧
                                  MeasureTheory.volume (twistedUnion Z f) ≥
                                    Kakeya.realRpowENN
                                        (delta / rho) epsilon *
                                      MeasureTheory.volume
                                        (Metric.cthickening rho
                                          (twistedUnion Z f))

/--
Full-window bounded-scale assembly for the parameter-certificate interface.

Half-window selection and exact vertical reflection are explicit
predecessors.  Reflection preserves the parameter box, so both signs call
the same bounded positive-window theorem.  The output is pulled back to the
original indexed family and is ready for selected-scale four-block
rediscretization.
-/
def SignedWindowParameterFrostmanScaleFromParametersBoundedStatement : Prop :=
  HalfWindowMassSelectionStatement →
    ReflectedSlopeCinematicStatement →
      Section7VerticalReflectionStatement →
        PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersBoundedStatement →
          CompactAssignedCinematicHolderFromVerticalChartStatement →
            PYZInput →
              ∀ epsilon rhoMax : ℝ,
                0 < epsilon → epsilon < 1 →
                0 < rhoMax → rhoMax ≤ 1 →
                  ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ epsilon ∧
                    ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
                      ∃ delta₀ : ℝ,
                        0 < delta₀ ∧ delta₀ < 1 ∧
                        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                          ∀ F : Kakeya.Streamlined.TubeFamily delta,
                            F.Nonempty →
                            IsInVerticalChart F →
                            (∀ i : Fin F.card,
                              |(tubeParams i).a| ≤ 12 ∧
                                |(tubeParams i).b| ≤ 12 ∧
                                |(tubeParams i).c| ≤ 2 ∧
                                |(tubeParams i).d| ≤ 2) →
                            F.IsEssentiallyDistinct →
                            ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                              C ≤ Kakeya.realRpowENN delta (-eta) →
                              TubeParameterFrostmanBound F C →
                              ∀ Y : Kakeya.Streamlined.TubeShading F,
                                Y.IsLambdaDense
                                  (Kakeya.realRpowENN delta (eta / 2)) →
                                IsInSlopeWindow Y →
                                ∀ f : SlopeFunction,
                                  f.IsNonsingular → f 0 = 0 →
                                    ∃ rho : ℝ,
                                      Real.rpow delta
                                          (1 - epsilon ^ 2) < rho ∧
                                      rho ≤ rhoMax ∧
                                      ∃ Z :
                                          Kakeya.Streamlined.TubeShading F,
                                        IsSubshading Z Y ∧
                                        Z.IsLambdaDense
                                          (Kakeya.realRpowENN
                                            delta (4 * eta)) ∧
                                        MeasureTheory.volume
                                            (twistedUnion Z f) ≥
                                          Kakeya.realRpowENN
                                              (delta / rho) epsilon *
                                            MeasureTheory.volume
                                              (Metric.cthickening rho
                                                (twistedUnion Z f))

/--
Full-window bounded-scale assembly without an essential-distinctness premise.

This is the iterable signed-window boundary for the OS-uniform four-block
states.  Half-window selection and reflection preserve indexed parameter
Frostman control, while the positive theorem used in each branch is the
no-distinct variant.
-/
def
    SignedWindowParameterFrostmanScaleFromParametersBoundedNoDistinctStatement :
    Prop :=
  HalfWindowMassSelectionStatement →
    ReflectedSlopeCinematicStatement →
      Section7VerticalReflectionStatement →
        PositiveWindowParameterFrostmanScaleAdjustableEtaFromParametersBoundedNoDistinctStatement →
          CompactAssignedCinematicHolderFromVerticalChartStatement →
            PYZInput →
              ∀ epsilon rhoMax : ℝ,
                0 < epsilon → epsilon < 1 / 100 →
                0 < rhoMax → rhoMax ≤ 1 →
                1 / 100 ≤ rhoMax →
                  ∃ etaMax : ℝ, 0 < etaMax ∧ etaMax ≤ epsilon ∧
                    ∀ eta : ℝ, 0 < eta → eta ≤ etaMax →
                      ∃ delta₀ : ℝ,
                        0 < delta₀ ∧ delta₀ < 1 ∧
                        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                          ∀ F : Kakeya.Streamlined.TubeFamily delta,
                            F.Nonempty →
                            IsInVerticalChart F →
                            (∀ i : Fin F.card,
                              |(tubeParams i).a| ≤ 12 ∧
                                |(tubeParams i).b| ≤ 12 ∧
                                |(tubeParams i).c| ≤ 2 ∧
                                |(tubeParams i).d| ≤ 2) →
                            ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                              C ≤ Kakeya.realRpowENN delta (-eta) →
                              TubeParameterFrostmanBound F C →
                              ∀ Y : Kakeya.Streamlined.TubeShading F,
                                Y.IsLambdaDense
                                  (Kakeya.realRpowENN delta (eta / 2)) →
                                IsInSlopeWindow Y →
                                ∀ f : SlopeFunction,
                                  f.IsNonsingular → f 0 = 0 →
                                    ∃ rho : ℝ,
                                      Real.rpow delta
                                          (1 - epsilon ^ 2) < rho ∧
                                      rho ≤ rhoMax ∧
                                      ∃ Z :
                                          Kakeya.Streamlined.TubeShading F,
                                        IsSubshading Z Y ∧
                                        Z.IsLambdaDense
                                          (Kakeya.realRpowENN
                                            delta (4 * eta)) ∧
                                        MeasureTheory.volume
                                            (twistedUnion Z f) ≥
                                          Kakeya.realRpowENN
                                              (delta / rho) epsilon *
                                            MeasureTheory.volume
                                              (Metric.cthickening rho
                                                (twistedUnion Z f))

end Kakeya.Assouad
