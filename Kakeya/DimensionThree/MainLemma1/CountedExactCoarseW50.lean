module

public import Kakeya.Factoring.DilatedTubePresentation
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma1.ParentConflictCover

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedExactCoarse

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 8000000 in
/-- Select complete parent fibres before forming the honest product.  The second weighted
selection is made after the common undilation has been accounted for, so the literal coarse
family of the returned product is pairwise essentially distinct. -/
theorem exists_honestProduct_after_undilateED_refinement_upstream_w50
    {sigma rho : NNReal} (hsigma0 : 0 < sigma)
    (hsigmaRho : sigma <= rho) (hrho1 : rho <= 1)
    {iota : Type u} [DecidableEq iota]
    {source0 parents0 : Finset iota}
    (T : iota -> ShadedTube sigma E) (Trho : iota -> Tube rho E)
    (p : iota -> iota)
    (hparent0 : IsParentFamilyDilate (2 : Real) source0
      (fun i => (T i).toTube) parents0 Trho p)
    (hball0 : forall i, i ∈ source0 ->
      (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmass0 : 0 < ∑ i ∈ source0, volume (T i).shade)
    (hrawED : (parents0 : Set iota).Pairwise fun q q' =>
      IsEssentiallyDistinct (Trho q).carrier (Trho q').carrier) :
    let M := Tube.undilateAtZeroConflict.M
      (Module.finrank Real E) (2 : Real)
    exists source, source ⊆ source0 /\
      exists parents, parents ⊆ parents0 /\
        (∑ i ∈ source0, volume (T i).shade) <=
          (((M : ENNReal) + 1) * ∑ i ∈ source, volume (T i).shade) /\
        source.Nonempty /\ parents.Nonempty /\
        (forall q, q ∈ parents -> fibre source p q = fibre source0 p q) /\
        exists hparent : IsParentFamilyDilate (2 : Real) source
            (fun i => (T i).toTube) parents Trho p,
          let F := Kakeya.ml1CoarseHonestW45.factorFamilyOfParentDilate
            (c := (2 : NNReal)) T Trho p hparent.mapsTo
              hparent.le_parent_dilate
          let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
            (Module.finrank Real E) source.card sigma (2 : NNReal)
          exists fineSet coarseSet : Finset iota,
            exists fineShade : iota -> ShadedTube sigma E,
            exists coarseShade : iota -> ShadedTube rho E,
            exists parent : iota -> iota,
              Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
                (c := (2 : NNReal)) F T Trho fineSet coarseSet
                  fineShade coarseShade parent cprod /\
              (coarseSet : Set iota).Pairwise (fun q q' =>
                IsEssentiallyDistinct (coarseShade q).carrier
                  (coarseShade q').carrier) := by
  classical
  let M := Tube.undilateAtZeroConflict.M
    (Module.finrank Real E) (2 : Real)
  have hrho0 : 0 < rho := hsigma0.trans_le hsigmaRho
  have hundilate : IsEDUpToMult parents0
      (fun q => (Tube.undilateAtZero (2 : Real) (Trho q)).carrier) M := by
    simpa [M] using Tube.isEDUpToMult_undilateAtZero
      hrho0 hrho1 parents0 Trho (c := (2 : Real)) (by norm_num) hrawED
  let w : iota -> ENNReal := fun q =>
    ∑ i ∈ fibre source0 p q, volume (T i).shade
  have hwfin : forall q, q ∈ parents0 -> w q ≠ ⊤ := by
    intro q hq
    exact ENNReal.sum_ne_top.mpr fun i hi =>
      ne_top_of_le_ne_top (T i).isCompact'.measure_ne_top
        (measure_mono (T i).shade_subset)
  obtain ⟨parents, hparentsSub, hparentsED, hweight, _hcard⟩ :=
    hundilate.exists_pairwise_subset_with_measure_and_card w hwfin
  let source : Finset iota := source0.filter fun i => p i ∈ parents
  have hsourceSub : source ⊆ source0 := Finset.filter_subset _ _
  have hmaps : forall i, i ∈ source -> p i ∈ parents := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsum0 : (∑ q ∈ parents0, w q) =
      ∑ i ∈ source0, volume (T i).shade := by
    exact Finset.sum_fiberwise_of_maps_to hparent0.mapsTo
      (fun i => volume (T i).shade)
  have hfibre : forall q, q ∈ parents ->
      fibre source p q = fibre source0 p q := by
    intro q hq
    simpa [source] using fibre_filter_mem source0 p parents hq
  have hsum : (∑ q ∈ parents, w q) =
      ∑ i ∈ source, volume (T i).shade := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => volume (T i).shade)]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [w]
    change (∑ i ∈ fibre source0 p q, volume (T i).shade) =
      ∑ i ∈ fibre source p q, volume (T i).shade
    rw [hfibre q hq]
  have hmassShare : (∑ i ∈ source0, volume (T i).shade) <=
      ((M : ENNReal) + 1) * ∑ i ∈ source, volume (T i).shade := by
    simpa [hsum0, hsum] using hweight
  have hsourceMass : 0 < ∑ i ∈ source, volume (T i).shade := by
    by_contra hnot
    have hzero : ∑ i ∈ source, volume (T i).shade = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hzero, mul_zero] at hmassShare
    exact (not_le_of_gt hmass0) hmassShare
  have hsourceNe : source.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    simp [hnot] at hsourceMass
  have hparentsNe : parents.Nonempty := by
    obtain ⟨i, hi⟩ := hsourceNe
    exact ⟨p i, hmaps i hi⟩
  have hparent : IsParentFamilyDilate (2 : Real) source
      (fun i => (T i).toTube) parents Trho p :=
    { one_le := hparent0.one_le
      mapsTo := hmaps
      injOn := hparent0.injOn.mono (Finset.coe_subset.mpr hparentsSub)
      le_parent_dilate := fun i hi => hparent0.le_parent_dilate i (hsourceSub hi) }
  have hball : forall i, i ∈ source ->
      (T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => hball0 i (hsourceSub hi)
  let F := Kakeya.ml1CoarseHonestW45.factorFamilyOfParentDilate
    (c := (2 : NNReal)) T Trho p hparent.mapsTo hparent.le_parent_dilate
  let cprod := shadingMultiplicityEstimateForRhoTubesDilate.C
    (Module.finrank Real E) source.card sigma (2 : NNReal)
  obtain ⟨fineSet, coarseSet, fineShade, coarseShade, parent, hOut⟩ :=
    Kakeya.ml1CoarseHonestW45.exists_honestProduct_after_parentRefinement
      hsigma0 hsigmaRho hrho1 (by norm_num : (1 : NNReal) <= 2)
      T Trho p hparent.mapsTo hparent.le_parent_dilate hball hsourceMass
  have hcoarseED : (coarseSet : Set iota).Pairwise (fun q q' =>
      IsEssentiallyDistinct (coarseShade q).carrier
        (coarseShade q').carrier) := by
    intro q hq q' hq' hne
    have hqq' := hparentsED (hOut.coarse_subset hq)
      (hOut.coarse_subset hq') hne
    have hqTube := hOut.coarse_tube q
    have hq'Tube := hOut.coarse_tube q'
    have hqCarrier := congrArg (fun S : Tube rho E => S.carrier) hqTube
    have hq'Carrier := congrArg (fun S : Tube rho E => S.carrier) hq'Tube
    simpa [hqCarrier, hq'Carrier] using hqq'
  refine ⟨source, hsourceSub, parents, hparentsSub, hmassShare,
    hsourceNe, hparentsNe, hfibre, hparent, ?_⟩
  dsimp only
  refine ⟨fineSet, coarseSet, fineShade, coarseShade, parent, ?_, hcoarseED⟩
  simpa [F, cprod] using hOut

set_option maxHeartbeats 8000000 in
/-- Use the original leaf ED and its genuine bounded-overlap parent system to select complete
source fibres before factorization.  The selection weight is the whole shade mass in each source
fibre, so the returned source remains a union of complete fibres and retains the weighted share
needed by the later scalar bridge. -/
theorem exists_rawED_completeFibre_refinement_from_leafED_w50
    (hdim : Module.finrank Real E = 3)
    {sigma tau rho : NNReal} (hsigma0 : 0 < sigma) (hrho0 : 0 < rho)
    (hrho1 : rho <= 1) (hsigmaRho : sigma <= rho)
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
    (hmass0 : 0 < ∑ i ∈ source0, volume (T i).shade) :
    let M := Kakeya.ml1Boot.parentConflictCover.degreeM E Co rho
    exists source, source ⊆ source0 /\
      exists parents, parents ⊆ parents0 /\
        (∑ i ∈ source0, volume (T i).shade) <=
          (((M : ENNReal) + 1) * ∑ i ∈ source, volume (T i).shade) /\
        source.Nonempty /\ parents.Nonempty /\
        (forall q, q ∈ parents ->
          fibre source pSource q = fibre source0 pSource q) /\
        IsParentFamilyDilate (2 : Real) source
          (fun i => (T i).toTube) parents Trho pSource /\
        (parents : Set iota).Pairwise fun q q' =>
          IsEssentiallyDistinct (Trho q).carrier (Trho q').carrier := by
  classical
  let active : Finset iota :=
    parents0.filter fun q => (fibre leaves pLeaf q).Nonempty
  let M := Kakeya.ml1Boot.parentConflictCover.degreeM E Co rho
  have hactiveUpTo : IsEDUpToMult active (fun q => (Trho q).carrier) M := by
    simpa [active, M] using
      (Kakeya.ml1Boot.parentConflictCover.activeParents_isEDUpToMult
        hdim hsigma0 hrho0 hrho1 hsigmaRho
        (fun i => (Vleaf i).toTube) Trho pLeaf hCo hleafBall hleafED
        hleafParent hoverlap)
  have hsourceMapsActive : forall i, i ∈ source0 -> pSource i ∈ active := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨hsourceParent.mapsTo i hi, hsourceActive i hi⟩
  let w : iota -> ENNReal := fun q =>
    ∑ i ∈ fibre source0 pSource q, volume (T i).shade
  have hwfin : forall q, q ∈ active -> w q ≠ ⊤ := by
    intro q hq
    exact ENNReal.sum_ne_top.mpr fun i hi =>
      ne_top_of_le_ne_top (T i).isCompact'.measure_ne_top
        (measure_mono (T i).shade_subset)
  obtain ⟨parents, hparentsActive, hparentsED, hweight, _hcard⟩ :=
    hactiveUpTo.exists_pairwise_subset_with_measure_and_card w hwfin
  have hparentsSub : parents ⊆ parents0 := by
    exact hparentsActive.trans (Finset.filter_subset _ _)
  let source : Finset iota := source0.filter fun i => pSource i ∈ parents
  have hsourceSub : source ⊆ source0 := Finset.filter_subset _ _
  have hmaps : forall i, i ∈ source -> pSource i ∈ parents := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsum0 : (∑ q ∈ active, w q) =
      ∑ i ∈ source0, volume (T i).shade := by
    exact Finset.sum_fiberwise_of_maps_to hsourceMapsActive
      (fun i => volume (T i).shade)
  have hfibre : forall q, q ∈ parents ->
      fibre source pSource q = fibre source0 pSource q := by
    intro q hq
    simpa [source] using fibre_filter_mem source0 pSource parents hq
  have hsum : (∑ q ∈ parents, w q) =
      ∑ i ∈ source, volume (T i).shade := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => volume (T i).shade)]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [w]
    change (∑ i ∈ fibre source0 pSource q, volume (T i).shade) =
      ∑ i ∈ fibre source pSource q, volume (T i).shade
    rw [hfibre q hq]
  have hmassShare : (∑ i ∈ source0, volume (T i).shade) <=
      ((M : ENNReal) + 1) * ∑ i ∈ source, volume (T i).shade := by
    simpa [hsum0, hsum] using hweight
  have hsourceMass : 0 < ∑ i ∈ source, volume (T i).shade := by
    by_contra hnot
    have hzero : ∑ i ∈ source, volume (T i).shade = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hzero, mul_zero] at hmassShare
    exact (not_le_of_gt hmass0) hmassShare
  have hsourceNe : source.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    simp [hnot] at hsourceMass
  have hparentsNe : parents.Nonempty := by
    obtain ⟨i, hi⟩ := hsourceNe
    exact ⟨pSource i, hmaps i hi⟩
  have hparent : IsParentFamilyDilate (2 : Real) source
      (fun i => (T i).toTube) parents Trho pSource :=
    { one_le := hsourceParent.one_le
      mapsTo := hmaps
      injOn := hsourceParent.injOn.mono (Finset.coe_subset.mpr hparentsSub)
      le_parent_dilate := fun i hi =>
        hsourceParent.le_parent_dilate i (hsourceSub hi) }
  exact ⟨source, hsourceSub, parents, hparentsSub, hmassShare,
    hsourceNe, hparentsNe, hfibre, hparent, hparentsED⟩

set_option maxHeartbeats 12000000 in
/-- Compose the leaf-mediated raw-parent selection with the honest-undilation selection.  Both
selections precede factorization; consequently the returned `HonestDilateProductOutput` and its
literal `coarseSet` are the final witness, and its coarse family is already pairwise ED. -/
theorem exists_honestProduct_after_leafED_two_refinements_w50
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
    (hmass0 : 0 < ∑ i ∈ source0, volume (T i).shade) :
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
                  (coarseShade q').carrier) := by
  classical
  let M1 := Kakeya.ml1Boot.parentConflictCover.degreeM E Co rho
  let M2 := Tube.undilateAtZeroConflict.M
    (Module.finrank Real E) (2 : Real)
  obtain ⟨source1, hsource1Sub, parents1, hparents1Sub, hshare1,
      hsource1Ne, hparents1Ne, hcomplete1, hparent1, hrawED⟩ :=
    exists_rawED_completeFibre_refinement_from_leafED_w50
      hdim hsigma0 hrho0 hrho1 hsigmaRho Vleaf T Trho pLeaf pSource hCo
      hleafBall hleafED hleafParent hoverlap hsourceParent hsourceActive hmass0
  have hmass1 : 0 < ∑ i ∈ source1, volume (T i).shade := by
    by_contra hnot
    have hzero : ∑ i ∈ source1, volume (T i).shade = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hzero, mul_zero] at hshare1
    exact (not_le_of_gt hmass0) hshare1
  have hball1 : forall i, i ∈ source1 ->
      (T i).carrier ⊆ Metric.closedBall 0 1 :=
    fun i hi => hsourceBall i (hsource1Sub hi)
  obtain ⟨source, hsourceSub1, parents, hparentsSub1, hshare2,
      hsourceNe, hparentsNe, hcomplete2, hparent, fineSet, coarseSet, fineShade,
      coarseShade, parent, hOut, hcoarseED⟩ :=
    exists_honestProduct_after_undilateED_refinement_upstream_w50
      htau0 htauRho hrho1 T Trho pSource hparent1 hball1 hmass1 hrawED
  have hshare : (∑ i ∈ source0, volume (T i).shade) <=
      (((M1 : ENNReal) + 1) * ((M2 : ENNReal) + 1)) *
        ∑ i ∈ source, volume (T i).shade := by
    calc
      (∑ i ∈ source0, volume (T i).shade) <=
          ((M1 : ENNReal) + 1) *
            ∑ i ∈ source1, volume (T i).shade := by
              simpa [M1] using hshare1
      _ <= ((M1 : ENNReal) + 1) *
          (((M2 : ENNReal) + 1) *
            ∑ i ∈ source, volume (T i).shade) := by
              gcongr
      _ = (((M1 : ENNReal) + 1) * ((M2 : ENNReal) + 1)) *
          ∑ i ∈ source, volume (T i).shade := by ring
  have hcomplete : forall q, q ∈ parents ->
      fibre source pSource q = fibre source0 pSource q := by
    intro q hq
    rw [hcomplete2 q hq]
    exact hcomplete1 q (hparentsSub1 hq)
  refine ⟨source, hsourceSub1.trans hsource1Sub, parents,
    hparentsSub1.trans hparents1Sub, hshare, hsourceNe, hparentsNe,
    hcomplete, hparent, ?_⟩
  dsimp only
  exact ⟨fineSet, coarseSet, fineShade, coarseShade, parent, hOut, hcoarseED⟩

end

end Kakeya.ml1Boot.W50CountedExactCoarse

#print axioms Kakeya.ml1Boot.W50CountedExactCoarse.exists_honestProduct_after_undilateED_refinement_upstream_w50
#print axioms Kakeya.ml1Boot.W50CountedExactCoarse.exists_rawED_completeFibre_refinement_from_leafED_w50
#print axioms Kakeya.ml1Boot.W50CountedExactCoarse.exists_honestProduct_after_leafED_two_refinements_w50
