module

public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseProductBridgeW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedExactCoarseActualProducer

noncomputable section

universe u v z

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 12000000 in
/--
The leaf-ED producer followed by the honest product factorization, with a first-pass
analytic estimate carried along on the *same* returned witness.  The continuation
`hfirst` is deliberately polymorphic in the factor family and all product indices;
the existential producer therefore cannot be satisfied by a different coarse family.
-/
theorem exists_honestProduct_after_leafED_two_refinements_with_first_pass_w50
    (hdim : Module.finrank Real E = 3)
    {sigma tau rho : NNReal} (hsigma0 : 0 < sigma) (htau0 : 0 < tau)
    (hrho0 : 0 < rho) (hrho1 : rho <= 1)
    (hsigmaRho : sigma <= rho) (htauRho : tau <= rho)
    {iota : Type u} [DecidableEq iota]
    {leaves source0 parents0 : Finset iota}
    (Vleaf : iota -> ShadedTube sigma E)
    (T : iota -> ShadedTube tau E) (Trho : iota -> Tube rho E)
    (pLeaf pSource : iota -> iota) {Co : NNReal} (hCo : 1 <= Co)
    (hleafBall : forall i, i ∈ leaves ->
      (Vleaf i).carrier ⊆ Metric.closedBall 0 1)
    (hleafED : (leaves : Set iota).Pairwise fun i j =>
      IsEssentiallyDistinct (Vleaf i).carrier (Vleaf j).carrier)
    (hleafParent : IsParentFamily leaves (fun i => (Vleaf i).toTube)
      parents0 Trho pLeaf)
    (hoverlap : Tube.HasBoundedOverlap leaves (fun i => (Vleaf i).toTube)
      parents0 Trho Co)
    (hsourceParent : IsParentFamilyDilate (2 : Real) source0
      (fun i => (T i).toTube) parents0 Trho pSource)
    (hsourceActive : forall i, i ∈ source0 ->
      (fibre leaves pLeaf (pSource i)).Nonempty)
    (hsourceBall : forall i, i ∈ source0 ->
      (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmass0 : 0 < ∑ i ∈ source0, volume (T i).shade)
    {alpha : Type z} [DecidableEq alpha]
    {S : Finset alpha} {VS : alpha -> ShadedBody E}
    {A : NNReal}
    (hfirst : ∀ {F : ShadedBody.FactorFamily E iota iota}
      {fineSet coarseSet : Finset iota}
      {fineShade : iota -> ShadedTube tau E}
      {coarseShade : iota -> ShadedTube rho E}
      {parent : iota -> iota} {productConstant : NNReal},
      Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
        (c := (2 : NNReal)) F T Trho fineSet coarseSet
          fineShade coarseShade parent productConstant ->
      ∀ j ∈ coarseSet,
        ShadedBody.multiplicity S VS ≤
          (A : ENNReal) * ShadedBody.multiplicity F.innerSet F.innerBody) :
    let M1 := Kakeya.ml1Boot.parentConflictCover.degreeM E Co rho
    let M2 := Tube.undilateAtZeroConflict.M
      (Module.finrank Real E) (2 : Real)
    exists source, source ⊆ source0 /\
      exists parents, parents ⊆ parents0 /\
        (∑ i ∈ source0, volume (T i).shade) <=
          (((M1 : ENNReal) + 1) * ((M2 : ENNReal) + 1)) *
            ∑ i ∈ source, volume (T i).shade /\
        source.Nonempty /\ parents.Nonempty /\
        (forall q, q ∈ parents ->
          fibre source pSource q = fibre source0 pSource q) /\
        exists hparent : IsParentFamilyDilate (2 : Real) source
            (fun i => (T i).toTube) parents Trho pSource,
          let F := Kakeya.ml1CoarseHonestW45.factorFamilyOfParentDilate
            (c := (2 : NNReal)) T Trho pSource hparent.mapsTo
              hparent.le_parent_dilate
          let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank Real E) source.card tau (2 : NNReal)
          exists fineSet coarseSet : Finset iota,
            exists fineShade : iota -> ShadedTube tau E,
            exists coarseShade : iota -> ShadedTube rho E,
            exists parent : iota -> iota,
              Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
                (c := (2 : NNReal)) F T Trho fineSet coarseSet
                  fineShade coarseShade parent cprod /\
              (coarseSet : Set iota).Pairwise (fun q q' =>
                IsEssentiallyDistinct (coarseShade q).carrier
                  (coarseShade q').carrier) /\
              (∀ j ∈ coarseSet,
                ShadedBody.multiplicity S VS <=
                  (A : ENNReal) * (cprod : ENNReal) *
                    ShadedBody.multiplicity coarseSet
                      (fun k => (coarseShade k).toShadedBody) *
                    ShadedBody.multiplicity
                      (Kakeya.ml1CoarseHonestW45.activeFibre
                        fineSet parent j)
                      (fun i => (fineShade i).toShadedBody)) := by
  classical
  let M1 := Kakeya.ml1Boot.parentConflictCover.degreeM E Co rho
  let M2 := Tube.undilateAtZeroConflict.M
    (Module.finrank Real E) (2 : Real)
  obtain ⟨source, hsourceSub, parents, hparentsSub, hshare,
      hsourceNe, hparentsNe, hcomplete, hparent, fineSet, coarseSet,
      fineShade, coarseShade, parent, hOut, hcoarseED⟩ :=
    Kakeya.ml1Boot.W50CountedExactCoarse.exists_honestProduct_after_leafED_two_refinements_w50
      hdim hsigma0 htau0 hrho0 hrho1 hsigmaRho htauRho
      Vleaf T Trho pLeaf pSource hCo hleafBall hleafED hleafParent
      hoverlap hsourceParent hsourceActive hsourceBall hmass0
  have hbound : ∀ j ∈ coarseSet,
      ShadedBody.multiplicity S VS <=
        (A : ENNReal) *
          (shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank Real E) source.card tau (2 : NNReal) : ENNReal) *
          ShadedBody.multiplicity coarseSet
            (fun k => (coarseShade k).toShadedBody) *
          ShadedBody.multiplicity
            (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent j)
            (fun i => (fineShade i).toShadedBody) := by
    exact _root_.Kakeya.ml1Boot.W50CountedExactCoarseProductBridge.honestProduct_compose_first_pass_w50 hOut
      (hfirst hOut)
  refine ⟨source, hsourceSub, parents, hparentsSub, hshare,
    hsourceNe, hparentsNe, hcomplete, ?_⟩
  dsimp only
  exact ⟨hparent, fineSet, coarseSet, fineShade, coarseShade, parent,
    hOut, hcoarseED, hbound⟩

end
end Kakeya.ml1Boot.W50CountedExactCoarseActualProducer

#print axioms Kakeya.ml1Boot.W50CountedExactCoarseActualProducer.exists_honestProduct_after_leafED_two_refinements_with_first_pass_w50
