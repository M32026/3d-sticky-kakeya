import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedCoarseSetupInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignmentInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.JointFiberCardinalityRegularizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberCardinalityRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRefinement

/-!
# Finite refinement of one large fixed ambient bin

Starting from ambient-restricted fine and coarse setup data, assign the bin
measurably to the enlarged fine carriers, choose one polynomially controlled
dyadic piece-volume layer, jointly regularize the paper's metric and retained
fiber cardinalities, and then regularize the number of selected fine
rectangles below each coarse parent.
-/

open MeasureTheory

namespace Kakeya.Cinematic

structure AmbientRestrictedLargeBinRefinementData
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    (massExponent : ℝ) where
  piece : Fin fineSetup.fine.card → Set (ℝ × ℝ)
  piece_measurable : ∀ i, MeasurableSet (piece i)
  piece_disjoint :
    Set.PairwiseDisjoint
      (Set.univ : Set (Fin fineSetup.fine.card)) piece
  piece_subset : ∀ i,
    piece i ⊆
      ambientRestrictedSet data center ∩
        (fineSetup.enlarged i).realCarrier
  bin_eq_union :
    ambientRestrictedSet data center = ⋃ i, piece i
  volume_sum :
    volume (ambientRestrictedSet data center) =
      ∑ i, volume (piece i)
  piece_volume : ∀ i,
    volume (piece i) ≤
      ENNReal.ofReal
        (2 * (C_shading * delta) *
          (fineSetup.enlarged i).interval.length)
  cutoff : ENNReal
  cutoff_pos : 0 < cutoff
  cutoff_ne_top : cutoff ≠ ⊤
  cutoff_eq :
    2 * ((fineSetup.fine.card : ENNReal) * cutoff) =
      volume (ambientRestrictedSet data center)
  layerCount : ℕ
  layerCount_pos : 0 < layerCount
  layerCount_bound :
    (layerCount : ℝ) ≤
      (C_count + massExponent + 2) *
        (Real.logb 2 (1 / delta) + 1)
  layer : Fin layerCount
  volumeSelected : Finset (Fin fineSetup.fine.card)
  volumeSelected_nonempty : volumeSelected.Nonempty
  volumeSelected_layer : ∀ i ∈ volumeSelected,
    (2 : ENNReal) ^ layer.val * cutoff ≤ volume (piece i) ∧
      volume (piece i) <
        (2 : ENNReal) ^ (layer.val + 1) * cutoff
  volumeSelected_mass :
    volume (ambientRestrictedSet data center) ≤
      ((2 * layerCount : ℕ) : ENNReal) *
        ∑ i ∈ volumeSelected, volume (piece i)
  metricLevel : ℕ
  retainedLevel : ℕ
  metricLevel_bound :
    metricLevel ≤ Nat.log2 data.ambientSource.card
  retainedLevel_bound :
    retainedLevel ≤ Nat.log2 data.ambientSource.card
  fiberLoss : ℕ
  fiberLoss_eq :
    fiberLoss = (Nat.log2 data.ambientSource.card + 1) ^ 2
  selected : Finset (Fin fineSetup.fine.card)
  selected_nonempty : selected.Nonempty
  selected_eq :
    selected =
      volumeSelected.filter (fun i =>
        2 ^ metricLevel ≤
            ((ambientRestrictedData data center hE).metricFiber
              (fineSetup.source i)).card ∧
          ((ambientRestrictedData data center hE).metricFiber
              (fineSetup.source i)).card <
            2 ^ (metricLevel + 1) ∧
          2 ^ retainedLevel ≤
            (fineSetup.pointData.fiber (fineSetup.source i)).card ∧
          (fineSetup.pointData.fiber (fineSetup.source i)).card <
            2 ^ (retainedLevel + 1))
  selected_subset : selected ⊆ volumeSelected
  fiber_retention :
    volumeSelected.card ≤ fiberLoss * selected.card
  selected_layer : ∀ i ∈ selected,
    (2 : ENNReal) ^ layer.val * cutoff ≤ volume (piece i) ∧
      volume (piece i) <
        (2 : ENNReal) ^ (layer.val + 1) * cutoff
  metric_range : ∀ i ∈ selected,
    2 ^ metricLevel ≤
        ((ambientRestrictedData data center hE).metricFiber
          (fineSetup.source i)).card ∧
      ((ambientRestrictedData data center hE).metricFiber
          (fineSetup.source i)).card <
        2 ^ (metricLevel + 1)
  retained_range : ∀ i ∈ selected,
    2 ^ retainedLevel ≤
        (fineSetup.pointData.fiber (fineSetup.source i)).card ∧
      (fineSetup.pointData.fiber (fineSetup.source i)).card <
        2 ^ (retainedLevel + 1)
  massFactor : ℕ
  massFactor_eq :
    massFactor = 4 * layerCount * fiberLoss
  selected_mass :
    volume (ambientRestrictedSet data center) ≤
      (massFactor : ENNReal) *
        ∑ i ∈ selected, volume (piece i)
  parentLevel : ℕ
  selectedParents :
    Finset (Fin coarseSetup.coarseData.coarse.card)
  parentLevel_bound :
    parentLevel ≤ Nat.log2 selected.card
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_eq :
    selectedParents =
      (parentSupport selected coarseSetup.coarseData.parent).filter
        (fun coarse =>
          2 ^ parentLevel ≤
              (parentFiber selected
                coarseSetup.coarseData.parent coarse).card ∧
            (parentFiber selected
              coarseSetup.coarseData.parent coarse).card <
                2 ^ (parentLevel + 1))
  parent_retention :
    selected.card ≤
      (Nat.log2 selected.card + 1) *
        (rectanglesOverParents selected
          coarseSetup.coarseData.parent selectedParents).card
  parent_partition :
    (rectanglesOverParents selected
      coarseSetup.coarseData.parent selectedParents).card =
        ∑ coarse ∈ selectedParents,
          (parentFiber selected
            coarseSetup.coarseData.parent coarse).card
  parent_range : ∀ coarse ∈ selectedParents,
    2 ^ parentLevel ≤
        (parentFiber selected
          coarseSetup.coarseData.parent coarse).card ∧
      (parentFiber selected
        coarseSetup.coarseData.parent coarse).card <
          2 ^ (parentLevel + 1)

namespace AmbientRestrictedLargeBinRefinementData

variable
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent)

def metricScale : ℕ := 2 ^ refinement.metricLevel

def retainedScale : ℕ := 2 ^ refinement.retainedLevel

lemma metricScale_pos : 0 < refinement.metricScale := by
  simp [metricScale]

lemma retainedScale_pos : 0 < refinement.retainedScale := by
  simp [retainedScale]

lemma metric_scale_range (i : Fin fineSetup.fine.card)
    (hi : i ∈ refinement.selected) :
    refinement.metricScale ≤
        ((ambientRestrictedData data center hE).metricFiber
          (fineSetup.source i)).card ∧
      ((ambientRestrictedData data center hE).metricFiber
          (fineSetup.source i)).card <
        2 * refinement.metricScale := by
  have h := refinement.metric_range i hi
  simpa [metricScale, pow_succ, mul_comm] using h

lemma retained_scale_range (i : Fin fineSetup.fine.card)
    (hi : i ∈ refinement.selected) :
    refinement.retainedScale ≤
        (fineSetup.pointData.fiber (fineSetup.source i)).card ∧
      (fineSetup.pointData.fiber (fineSetup.source i)).card <
        2 * refinement.retainedScale := by
  have h := refinement.retained_range i hi
  simpa [retainedScale, pow_succ, mul_comm] using h

end AmbientRestrictedLargeBinRefinementData

def AmbientRestrictedLargeBinRefinementStatement : Prop :=
  FineCarrierMeasurableAssignmentStatement →
    DyadicPieceVolumeRefinementStatement →
    PolynomialDyadicPieceRangeStatement →
    JointFiberCardinalityRegularizationStatement.{0} →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ},
      ∀ (data : DyadicFineAssignmentData
          family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
        (center : C2Function)
        (hE : MeasurableSet E)
        {C_R C_count C_shading C_volume : ℝ}
        (fineSetup : AmbientRestrictedFSVSetupData
          data center hE C_R C_count C_shading C_volume)
        (coarseSetup : AmbientRestrictedCoarseSetupData
          data center hE fineSetup)
        (massExponent : ℝ),
        0 < delta →
        delta ≤ 1 / 2 →
        0 ≤ C_count →
        0 ≤ C_shading →
        0 ≤ massExponent →
        ENNReal.ofReal (Real.rpow delta massExponent) <
          volume (ambientRestrictedSet data center) →
        volume (ambientRestrictedSet data center) ≤ 1 →
        Nonempty
          (AmbientRestrictedLargeBinRefinementData
            data center hE fineSetup coarseSetup massExponent)

end Kakeya.Cinematic
