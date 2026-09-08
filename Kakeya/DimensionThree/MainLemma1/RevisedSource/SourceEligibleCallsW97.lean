module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceAssignedNormalizationW97

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

def actualSecondAmbientW97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    {p : Params} {BF loss : NNReal} {block : ActualSourceDividingBlockW95 U p BF}
    (selections : ActualSameMassSelectionsW95 block loss) :
    iota -> ShadedTube (Tube.gridScale delta M block.b.val) E :=
  zeroExtend selections.secondFamily (U.cover.tube block.b.val) selections.secondShading

def actualEligibleThetaParentsW97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    {p : Params} {BF loss : NNReal} {block : ActualSourceDividingBlockW95 U p BF}
    (selections : ActualSameMassSelectionsW95 block loss) (Cext : NNReal) (etaLambda : Real) : Finset iota :=
  (U.cover.indexSet block.a.val).filter (fun R =>
    (Cext : ENNReal) *
      ((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : ENNReal) ^ etaLambda *
        (∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
          volume (U.cover.tube block.b.val Q).carrier) <=
      ∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
        volume (actualSecondAmbientW97 selections Q).shade)

/-- Genuine per-fibre input and output on the SAME full ambient labels. -/
structure ActualEligibleTrialCallsW97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    {U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan}
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    {p : Params} {BF loss : NNReal} (block : ActualSourceDividingBlockW95 U p BF)
    (selections : ActualSameMassSelectionsW95 block loss)
    (xi : Fin (p.N + 1) -> Real) (gamma : Real)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M) where
  eligible_nonempty : (actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)).Nonempty
  mass_retention : (1 / 2 : ENNReal) *
      (∑ Q ∈ U.cover.indexSet block.b.val, volume (actualSecondAmbientW97 selections Q).shade) <=
    ∑ R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
      ∑ Q ∈ actualDescendantsW95 A U.cover.assign block.a.val block.b.val R,
        volume (actualSecondAmbientW97 selections Q).shade
  normalization : ∀ R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
    ActualAssignedUnitNormalizationW97 U Uext block.a.val block.b.val R
      (actualSecondAmbientW97 selections) Rnorm Cext Cnorm CtwNorm CcellNorm
  input : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
    DetailedTrialInputW94 (normalization R hR).cells p.ε (xi block.label)
      (p.η (block.label.val + 1) / 2) (aux.inner block.label)
  outcome : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
    detailedInnerGoodW94 (actualDescendantsW95 A U.cover.assign block.a.val block.b.val R)
      (normalization R hR).normalized gamma p.ε (xi block.label) ∨
    Nonempty (DetailedTrialDropW94 (normalization R hR).cells p.ε
      (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))


end

end Kakeya.ml1Boot.TrialRestartW94
