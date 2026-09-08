module

public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W48EndpointCoarseDirect

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- The generic endpoint parent family has the crude leaf-cardinality overlap bound.
This is only used by the pre-factorization conflict selection. -/
theorem endpoint_parentFamily_hasBoundedOverlap_card_w50
    {delta theta : NNReal} {iota : Type u} [DecidableEq iota]
    {s tTheta : Finset iota} {T : iota -> ShadedTube delta E}
    {TTheta : iota -> Tube theta E}
    (htTheta : tTheta ⊆ s) :
    Tube.HasBoundedOverlap s (fun i => (T i).toTube)
      tTheta TTheta (s.card : NNReal) := by
  classical
  intro W
  exact_mod_cast Finset.card_le_card
    ((Finset.filter_subset _ tTheta).trans htTheta)

/-- Restrict the geometric endpoint parent family to the terminal retained family and
upgrade its containment to the `c = 2` dilated form required by the counted honest-product
producer.  This is the exact same `tTheta/TTheta/pTheta`; no post-product ED selection is
performed here. -/
theorem endpoint_geometry_sourceParentDilate_w50
    {delta theta : NNReal} {iota : Type u} [DecidableEq iota]
    {s tm tTheta : Finset iota}
    {T : iota → ShadedTube delta E}
    {Ztau : iota → ShadedTube delta E}
    {TTheta : iota → Tube theta E} {pTheta : iota → iota}
    (htm : tm ⊆ s)
    (hZtau : ∀ i, i ∈ tm → (Ztau i).toTube = (T i).toTube)
    (hparent : IsParentFamily s (fun i => (T i).toTube)
      tTheta TTheta pTheta) :
    IsParentFamilyDilate (2 : Real) tm
      (fun i => (Ztau i).toTube) tTheta TTheta pTheta := by
  refine
    { one_le := by norm_num
      mapsTo := ?_
      injOn := hparent.injOn
      le_parent_dilate := ?_ }
  · intro i hi
    exact hparent.mapsTo i (htm hi)
  · intro i hi
    rw [hZtau i hi]
    exact (hparent.le_parent i (htm hi)).trans
      (Tube.subset_dilate (TTheta (pTheta i)) (by norm_num))

set_option maxHeartbeats 16000000 in
/-- Concrete endpoint bridge: the retained geometric endpoint family feeds the verified
counted two-refinement producer.  The returned honest product has a literal pairwise-ED
coarse family, while all parent/coarse objects are generated before factorization. -/
theorem exists_endpoint_geometry_honestProduct_coarseED_w50
    (hdim : Module.finrank Real E = 3)
    {delta theta : NNReal} (hdelta0 : 0 < delta)
    (hdeltaTheta : delta <= theta) (htheta1 : theta <= 1)
    {iota : Type u} [DecidableEq iota]
    {s tm tTheta : Finset iota}
    (T : iota → ShadedTube delta E)
    (Ztau : iota → ShadedTube delta E)
    (TTheta : iota → Tube theta E) (pTheta : iota → iota)
    (htm : tm ⊆ s) (htTheta : tTheta ⊆ s)
    (hball : ∀ i, i ∈ s →
      (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set iota).Pairwise fun i j =>
      IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (hparent : IsParentFamily s (fun i => (T i).toTube)
      tTheta TTheta pTheta)
    (hZtau : ∀ i, i ∈ tm → (Ztau i).toTube = (T i).toTube)
    (htmne : tm.Nonempty)
    (hmass : 0 < ∑ i ∈ tm, volume (Ztau i).shade) :
    let Co : NNReal := (s.card : NNReal)
    exists source, source ⊆ tm /\
      exists parents, parents ⊆ tTheta /\
        exists hparent' : IsParentFamilyDilate (2 : Real) source
            (fun i => (Ztau i).toTube) parents TTheta pTheta,
          let F := Kakeya.ml1CoarseHonestW45.factorFamilyOfParentDilate
            (c := (2 : NNReal)) Ztau TTheta pTheta hparent'.mapsTo
              hparent'.le_parent_dilate
          let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank Real E) source.card delta (2 : NNReal)
          exists fineSet coarseSet : Finset iota,
            exists fineShade : iota → ShadedTube delta E,
            exists coarseShade : iota → ShadedTube theta E,
            exists parent : iota → iota,
              Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
                (c := (2 : NNReal)) F Ztau TTheta fineSet coarseSet
                  fineShade coarseShade parent cprod /\
              (coarseSet : Set iota).Pairwise (fun q q' =>
                IsEssentiallyDistinct (coarseShade q).carrier
                  (coarseShade q').carrier) := by
  classical
  let Co : NNReal := (s.card : NNReal)
  have hsne : s.Nonempty := htmne.mono htm
  have hCo : (1 : NNReal) <= Co := by
    have hcard : (1 : NNReal) <= (s.card : NNReal) := by
      exact_mod_cast Finset.one_le_card.mpr hsne
    simpa [Co] using hcard
  have hparentDilate : IsParentFamilyDilate (2 : Real) tm
      (fun i => (Ztau i).toTube) tTheta TTheta pTheta :=
    endpoint_geometry_sourceParentDilate_w50 htm hZtau hparent
  have hoverlap : Tube.HasBoundedOverlap s (fun i => (T i).toTube)
      tTheta TTheta Co := by
    simpa [Co] using
      (endpoint_parentFamily_hasBoundedOverlap_card_w50 (E := E)
        (T := T) (TTheta := TTheta) htTheta)
  have hsourceActive : ∀ i, i ∈ tm ->
      (fibre s pTheta (pTheta i)).Nonempty := by
    intro i hi
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨htm hi, rfl⟩
  have hsourceBall : ∀ i, i ∈ tm →
      (Ztau i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    rw [hZtau i hi]
    exact hball i (htm hi)
  obtain ⟨source, hsource, parents, hparents, _hshare,
      _hsourcene, _hparentsne, _hcomplete, hparent', fineSet, coarseSet,
      fineShade, coarseShade, parent, hOut, hcoarseED⟩ :=
    Kakeya.ml1Boot.W50CountedExactCoarse.exists_honestProduct_after_leafED_two_refinements_w50
      (E := E) hdim hdelta0 hdelta0
      (lt_of_lt_of_le hdelta0 hdeltaTheta) htheta1
      hdeltaTheta hdeltaTheta T Ztau TTheta pTheta pTheta hCo
      (fun i hi => hball i hi) hED hparent hoverlap hparentDilate
      hsourceActive hsourceBall hmass
  refine ⟨source, hsource, parents, hparents, hparent', ?_⟩
  dsimp only
  exact ⟨fineSet, coarseSet, fineShade, coarseShade, parent, hOut, hcoarseED⟩

end
end Kakeya.ml1Boot.W48EndpointCoarseDirect

#print axioms Kakeya.ml1Boot.W48EndpointCoarseDirect.endpoint_geometry_sourceParentDilate_w50
#print axioms Kakeya.ml1Boot.W48EndpointCoarseDirect.endpoint_parentFamily_hasBoundedOverlap_card_w50
#print axioms Kakeya.ml1Boot.W48EndpointCoarseDirect.exists_endpoint_geometry_honestProduct_coarseED_w50
