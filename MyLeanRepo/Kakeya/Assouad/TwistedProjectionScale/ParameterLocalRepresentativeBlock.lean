import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockStatements

/-!
# One source tube for every selected local parameter

Paper Lemma 7.12 applies the cinematic estimate to the collapsed parameter
set.  After the common `c`-window and per-tube fullness pruning, it therefore
uses one actual source tube for every selected `(a,b,d)` parameter.  Indexed
duplicates over the same collapsed parameter are not copied into the
cinematic family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The selected local parameter indexed by `j`. -/
def parameterLocalBlockPoint
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock : ParameterLocalFullBlockData clustered epsilon)
    (j : Fin localBlock.sourcePoints.card) : Point 3 :=
  (localBlock.sourcePoints.equivFin.symm j).1

/-- One genuine source tube for each selected local parameter point. -/
structure ParameterLocalRepresentativeBlockData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock : ParameterLocalFullBlockData clustered epsilon) where
  sourceIndex : Fin localBlock.sourcePoints.card → Fin F.card
  source_nonempty :
    ∀ j, clustered.shading.carrier (sourceIndex j) ≠ ∅
  source_assign :
    ∀ j,
      clustered.assign (sourceIndex j) =
        parameterLocalBlockPoint localBlock j
  source_point :
    ∀ j,
      tubeParameterPoint3 (sourceIndex j) =
        parameterLocalBlockPoint localBlock j
  sourceIndex_injective : Function.Injective sourceIndex

/-- The representative tube family, with exactly one index per local point. -/
def parameterLocalRepresentativeFamily
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    (representatives : ParameterLocalRepresentativeBlockData localBlock) :
    Kakeya.Streamlined.TubeFamily delta where
  card := localBlock.sourcePoints.card
  tube j := F.tube (representatives.sourceIndex j)

/-- The unchanged source shading on the representative tube family. -/
def parameterLocalRepresentativeShading
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    (representatives : ParameterLocalRepresentativeBlockData localBlock) :
    Kakeya.Streamlined.TubeShading
      (parameterLocalRepresentativeFamily representatives) where
  carrier j := clustered.shading.carrier (representatives.sourceIndex j)
  measurable_carrier j :=
    clustered.shading.measurable_carrier (representatives.sourceIndex j)
  subset_body j := by
    exact clustered.shading.subset_body (representatives.sourceIndex j)

/--
Select one genuine nonempty source tube for each selected local parameter.
-/
theorem parameter_local_representative_block
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock : ParameterLocalFullBlockData clustered epsilon) :
    Nonempty (ParameterLocalRepresentativeBlockData localBlock) := by
  let sourcePoint :
      Fin localBlock.sourcePoints.card → Point 3 :=
    parameterLocalBlockPoint localBlock
  have hSourcePointMem :
      ∀ j, sourcePoint j ∈ clustered.points := by
    intro j
    exact localBlock.sourcePoints_subset
      (localBlock.sourcePoints.equivFin.symm j).2
  have hSource :
      ∀ j,
        ∃ i : Fin F.card,
          clustered.shading.carrier i ≠ ∅ ∧
            clustered.assign i = sourcePoint j ∧
            tubeParameterPoint3 i = sourcePoint j := by
    intro j
    exact clustered.point_source (sourcePoint j) (hSourcePointMem j)
  let sourceIndex : Fin localBlock.sourcePoints.card → Fin F.card :=
    fun j => Classical.choose (hSource j)
  have hSourceNonempty :
      ∀ j, clustered.shading.carrier (sourceIndex j) ≠ ∅ := by
    intro j
    exact (Classical.choose_spec (hSource j)).1
  have hSourceEq :
      ∀ j, tubeParameterPoint3 (sourceIndex j) = sourcePoint j := by
    intro j
    exact (Classical.choose_spec (hSource j)).2.2
  have hSourceAssign :
      ∀ j, clustered.assign (sourceIndex j) = sourcePoint j := by
    intro j
    exact (Classical.choose_spec (hSource j)).2.1
  have hInjective : Function.Injective sourceIndex := by
    intro first second h
    have hPoint :
        sourcePoint first = sourcePoint second := by
      rw [← hSourceEq first, ← hSourceEq second, h]
    have hSubtype :
        localBlock.sourcePoints.equivFin.symm first =
          localBlock.sourcePoints.equivFin.symm second := by
      apply Subtype.ext
      exact hPoint
    exact localBlock.sourcePoints.equivFin.symm.injective hSubtype
  exact
    ⟨{
      sourceIndex := sourceIndex
      source_nonempty := hSourceNonempty
      source_assign := hSourceAssign
      source_point := hSourceEq
      sourceIndex_injective := hInjective
    }⟩

/-- Every representative tube inherits a supplied per-tube mass floor. -/
theorem parameterLocalRepresentativeShading_hasPerTubeMass
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda threshold : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    (representatives : ParameterLocalRepresentativeBlockData localBlock)
    (hMass : HasPerTubeMass clustered.shading threshold) :
    HasPerTubeMass
      (parameterLocalRepresentativeShading representatives) threshold := by
  intro j
  rcases hMass (representatives.sourceIndex j) with hEmpty | hLower
  · exact False.elim (representatives.source_nonempty j hEmpty)
  · exact Or.inr hLower

/-- Total representative mass is at least one mass floor per local point. -/
theorem parameterLocalRepresentativeShading_mass_lower
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda threshold : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    (representatives : ParameterLocalRepresentativeBlockData localBlock)
    (hMass : HasPerTubeMass clustered.shading threshold) :
    threshold * localBlock.sourcePoints.enncard ≤
      (parameterLocalRepresentativeShading representatives).mass := by
  have hEach :
      ∀ j : Fin localBlock.sourcePoints.card,
        threshold ≤
          volume
            ((parameterLocalRepresentativeShading representatives).carrier j) := by
    intro j
    rcases
        parameterLocalRepresentativeShading_hasPerTubeMass
          representatives hMass j with hEmpty | hLower
    · exact False.elim (representatives.source_nonempty j hEmpty)
    · exact hLower
  calc
    threshold * localBlock.sourcePoints.enncard =
        ∑ _j : Fin localBlock.sourcePoints.card, threshold := by
      simp [DiscreteSet.enncard, mul_comm]
    _ ≤
        ∑ j : Fin localBlock.sourcePoints.card,
          volume
            ((parameterLocalRepresentativeShading representatives).carrier j) := by
      exact Finset.sum_le_sum fun j _ => hEach j
    _ = (parameterLocalRepresentativeShading representatives).mass := rfl

end Kakeya.Assouad
