import MyLeanRepo.Kakeya.Assouad.WZ1.C2GrainNormalizationStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.CubicalPlaneMapStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalPlaninessTransportStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.RescaledFiberStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ScaleChangedLipschitzStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.SuppliedWeakPlaneMapStatements

/-!
# Lightweight WZ1 main-chain statements

These proposition-only interfaces do not depend on the implementation of the
completed CV broad-set theorem.  Keeping them outside `CVStatements` prevents
independent WZ1 proof targets from rebuilding the full CV and Borsuk--Ulam
dependency chain during Seed startup.
-/

namespace Kakeya.Assouad

/--
WZ1 Proposition 9 global-planiness producer on one extremal configuration.

The Lemma 12 scale change and Lemma 15 Lipschitz map are explicit predecessors.
This broad producer applies the first every-scale local-grain refinement and
performs the anisotropic rescaling that creates the global Lipschitz slope and
the rescaled plane map on one configuration.  These scale-changing steps must
stay dependent; the predecessor conclusions alone do not assemble by
propositional glue.
-/
def WZ1GlobalPlaninessConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasExtremalCounterexampleSequence sigma →
    HasCriticalVolumeFloor sigma →
      ∀ outputLoss delta₀ : ℝ,
        0 < outputLoss → 0 < delta₀ →
          ∃ delta inputLoss : ℝ,
            0 < delta ∧ delta ≤ delta₀ ∧
            0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
              Nonempty
                (WZ1GlobalPlaninessData
                  sigma inputLoss delta)

/--
Construct the same-configuration global slope and plane map through the
paper's two scale changes.

The additional inputs record the dependencies that an ordinary
balanced cover forgets:

* Proposition 5 item (ii), with extremality only after unit rescaling of each
  retained fine fiber;
* the later Property-(P) refinement and distinguished-tube selection on the
  supplied rescaled fiber;
* the second planiness application on that supplied rescaled configuration at
  the prescribed global-grain scale;
* the geometric transport from source local grains to the final global slab
  AD certificate.

In particular, this statement does not assert the false same-scale
extremality of a single coarse fiber, and it does not apply the point
rescaling map directly to plane normals.
-/
def WZ1GlobalPlaninessStatement : Prop :=
  WZ1BalancedCoverStatement →
    WZ1BalancedCoverRescaledFiberConclusion →
      WZ1PropertyPSelectionStatement →
        WZ1SuppliedWeakPlaneMapStatement →
          WZ1ScaleChangedLipschitzPlaneMapStatement →
            WZ1AnchoredGlobalGrainTransportConclusion →
              WZ1HorizontalChartNormalizationStatement →
                WZ1CubicalPlaneMapConclusion →
                  WZ1LipschitzPlaneMapConclusion →
                    WZ1EveryScaleLocalGrainConclusion →
                      WZ1GlobalPlaninessConclusion

/--
Assemble the global and local grain certificates before the final mild
rescaling in WZ1 Proposition 9.
-/
def WZ1PreNormalizedPlaninessGraininessConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
          HasExtremalCounterexampleSequence sigma →
          HasCriticalVolumeFloor sigma →
            ∀ epsilon delta₀ : ℝ,
              0 < epsilon → 0 < delta₀ →
                ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
                  Nonempty
                    (WZ1PreNormalizedPlaninessGraininessData
                      sigma epsilon delta)

/--
The dependent pre-normalized Proposition 9 assembly.
-/
def WZ1PreNormalizedPlaninessGraininessStatement : Prop :=
  WZ1GlobalPlaninessConclusion →
    WZ1EveryScaleLocalGrainConclusion →
      WZ1PreNormalizedPlaninessGraininessConclusion

/--
WZ1 Proposition 9 after the final Lemma 8 mild rescaling.

The resulting global slope and local plane map are both `1`-Lipschitz on the
same rescaled extremal configuration.
-/
def WZ1PlaninessGraininessConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
          HasExtremalCounterexampleSequence sigma →
          HasCriticalVolumeFloor sigma →
            ∀ epsilon delta₀ : ℝ,
              0 < epsilon → 0 < delta₀ →
                ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
                  Nonempty
                    (WZ1PlaninessGraininessPackage
                      sigma epsilon delta)

/--
Proposition 9 assembled from the pre-normalized dependent configuration and
the paper's final mild-rescaling lemma.
-/
def WZ1PlaninessGraininessStatement : Prop :=
  WZ1PreNormalizedPlaninessGraininessConclusion →
    WZ1Proposition9MildRescalingStatement →
      WZ1PlaninessGraininessConclusion

/--
WZ1 Corollary 26: apply the proved projection dichotomy on the same
Proposition 9 configuration at finitely many scales and convert the nested
trapezoids into finite correction data consumed by Proposition 27.

The output keeps the scale levels and the raw power loss explicit.  It does
not assert normalized `C²` bounds: Proposition 27 constructs a raw `C²`
function from this hierarchy, and Proposition 21 normalizes it only after a
final vertical rescaling.
-/
def WZ1NestedSlopeCorrectionsStatement : Prop :=
  WZ1ProjectionDichotomyConclusion →
    WZ1PlaninessGraininessConclusion →
      ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
        HasExtremalCounterexampleSequence sigma →
        HasCriticalVolumeFloor sigma →
          ∀ outputLoss delta₀ : ℝ,
            0 < outputLoss → 0 < delta₀ →
              ∃ delta inputLoss : ℝ,
                0 < delta ∧ delta ≤ delta₀ ∧
                0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
                ∃ source :
                    WZ1PlaninessGraininessPackage
                      sigma inputLoss delta,
                  Nonempty
                    (WZ1MultiscaleSlopeCorrectionPackage
                      source outputLoss)

/--
Proposition 21 assembled after the finite projection dichotomy has already
been proved.  All substantial inputs remain explicit; the theorem performs
only the dependent selection and final normalization chain.
-/
def WZ1C2GrainPackageFromProjectionStatement : Prop :=
  WZ1SmoothSegmentExtensionStatement →
    WZ1PlaninessGraininessConclusion →
      WZ1NestedSlopeCorrectionsStatement →
        WZ1RawGlobalGrainsFromMultiscaleCorrectionsStatement →
          WZ1C2GrainNormalizationStatement →
            WZ1ProjectionDichotomyConclusion →
              ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
                HasExtremalCounterexampleSequence sigma →
                HasCriticalVolumeFloor sigma →
                  ∀ epsilon delta₀ : ℝ,
                    0 < epsilon → 0 < delta₀ →
                      ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
                        Nonempty
                          (WZ1C2GrainPackage
                            sigma epsilon delta)

/--
Supply the single external OSW hypothesis to the proved projection dichotomy
and obtain the legacy complete WZ1 package producer.
-/
def WZ1C2GrainPackageAssemblyStatement : Prop :=
  WZ1ProjectionDichotomyStatement →
    WZ1SmoothSegmentExtensionStatement →
      WZ1PlaninessGraininessConclusion →
        WZ1NestedSlopeCorrectionsStatement →
          WZ1RawGlobalGrainsFromMultiscaleCorrectionsStatement →
            WZ1C2GrainNormalizationStatement →
              WZ1C2GrainPackageFromProjectionStatement →
                WZ1C2GrainPackageStatement

end Kakeya.Assouad
