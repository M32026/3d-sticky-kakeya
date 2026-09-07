import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicStatements

/-!
# Representative local shading remains inside the source local block

Paper Lemma 7.12 applies the cinematic estimate to one representative tube
for each selected collapsed parameter.  This reindexing does not change the
underlying source carriers: every representative carrier is one of the
carriers in the full selected local block.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Every subshading of the representative local family has its union contained
in the full selected local-block shading.
-/
theorem parameterLocalRepresentative_union_subset_local
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    (representatives :
      ParameterLocalRepresentativeBlockData localBlock)
    (Z :
      Kakeya.Streamlined.TubeShading
        (parameterLocalRepresentativeFamily representatives))
    (hZ :
      IsSubshading Z
        (parameterLocalRepresentativeShading representatives)) :
    Z.union ⊆
      (parameterLocalBlockShading
        clustered localBlock.sourcePoints).union := by
  intro point hpoint
  rcases hpoint with ⟨representativeIndex, hpoint⟩
  let sourceIndex : Fin F.card :=
    representatives.sourceIndex representativeIndex
  have hsource_nonempty :
      clustered.shading.carrier sourceIndex ≠ ∅ :=
    representatives.source_nonempty representativeIndex
  have hsource_assign :
      clustered.assign sourceIndex ∈ localBlock.sourcePoints := by
    rw [representatives.source_assign representativeIndex]
    exact (localBlock.sourcePoints.equivFin.symm representativeIndex).2
  have hsource_mem :
      sourceIndex ∈
        parameterLocalBlockIndices
          clustered localBlock.sourcePoints := by
    simpa [parameterLocalBlockIndices, sourceIndex,
      Finset.mem_filter] using hsource_assign
  let localIndex :
      Fin (parameterLocalBlockFamily
        clustered localBlock.sourcePoints).card :=
    (parameterLocalBlockIndices
      clustered localBlock.sourcePoints).equivFin
        ⟨sourceIndex, hsource_mem⟩
  refine ⟨localIndex, ?_⟩
  have hrepresentative :
      point ∈
        (parameterLocalRepresentativeShading
          representatives).carrier representativeIndex :=
    hZ representativeIndex hpoint
  simpa [parameterLocalBlockShading, selectedTubeShading,
    parameterLocalRepresentativeShading, localIndex, sourceIndex] using
      hrepresentative

/--
The representative twisted projection is contained in the twisted projection
of the full selected local block.
-/
theorem parameterLocalRepresentative_twisted_subset_local
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    (representatives :
      ParameterLocalRepresentativeBlockData localBlock)
    (Z :
      Kakeya.Streamlined.TubeShading
        (parameterLocalRepresentativeFamily representatives))
    (hZ :
      IsSubshading Z
        (parameterLocalRepresentativeShading representatives))
    (f : SlopeFunction) :
    twistedUnion Z f ⊆
      twistedUnion
        (parameterLocalBlockShading
          clustered localBlock.sourcePoints) f := by
  intro point hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  exact ⟨sourcePoint,
    parameterLocalRepresentative_union_subset_local
      representatives Z hZ hsourcePoint,
    rfl⟩

end Kakeya.Assouad
