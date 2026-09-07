import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinementInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignment
import MyLeanRepo.Kakeya.Cinematic.Section5.JointFiberCardinalityMass
import MyLeanRepo.Kakeya.Cinematic.Section5.JointFiberCardinalityRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.JointFiberCardinalityRatio
import MyLeanRepo.Kakeya.Cinematic.Section5.MeasurableDisjointification
import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberCardinalityRegularization
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRefinement

/-!
# Finite refinement of one large fixed ambient bin
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem ambient_restricted_large_bin_refinement :
    AmbientRestrictedLargeBinRefinementStatement := by
  intro hFine hRefine hRange hJoint
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
  intro data center hE C_R C_count C_shading C_volume
  intro fineSetup coarseSetup massExponent
  intro hdelta hdelta_half hcountExponent hshading hmassExponent
  intro hmass_large hbin_le_one
  let N := fineSetup.fine.card
  have hN_pos : 0 < N := fineSetup.fine_nonempty
  have hshading_delta_nonneg :
      0 ≤ C_shading * delta := by
    positivity
  have hE_meas :
      MeasurableSet (ambientRestrictedSet data center) :=
    measurableSet_ambientRestrictedSet data center hE
  rcases hFine finite_measurable_disjointification
      (E := ambientRestrictedSet data center)
      (carrier := fineSetup.enlarged)
      hshading_delta_nonneg hE_meas fineSetup.bin_cover with
    ⟨piece, piece_measurable, piece_disjoint, piece_subset,
      bin_eq_union, hmeasure, piece_volume⟩
  have volume_sum :
      volume (ambientRestrictedSet data center) =
        ∑ i, volume (piece i) :=
    hmeasure volume
  let total : ENNReal :=
    volume (ambientRestrictedSet data center)
  have htotal_pos : 0 < total := by
    exact lt_of_le_of_lt bot_le hmass_large
  have htotal_ne_top : total ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hbin_le_one
  rcases exists_positive_finite_half_mass_cutoff
      hN_pos htotal_pos htotal_ne_top with
    ⟨cutoff, cutoff_pos, cutoff_ne_top, cutoff_eq⟩
  let weight : Fin N → ENNReal := fun i => volume (piece i)
  have hweight_le_one :
      ∀ i, weight i ≤ (1 : ENNReal) := by
    intro i
    have hsubset :
        piece i ⊆ ambientRestrictedSet data center :=
      (piece_subset i).trans Set.inter_subset_left
    exact (measure_mono hsubset).trans hbin_le_one
  rcases polynomial_dyadic_piece_refinement_from_cutoff
      hRange hRefine
      (delta := delta) (countExponent := C_count)
      (massExponent := massExponent)
      (N := N) weight
      (total := total) (lower := cutoff) (upper := (1 : ENNReal))
      hdelta hdelta_half hcountExponent hmassExponent
      hN_pos fineSetup.fine_card hmass_large cutoff_eq
      (by norm_num) volume_sum.symm cutoff_pos cutoff_ne_top
      hweight_le_one with
    ⟨layerCount, layerCount_pos, layerCount_bound, layer,
      volumeSelected, volumeSelected_nonempty, volumeSelected_layer,
      volumeSelected_mass_raw⟩
  have volumeSelected_mass :
      volume (ambientRestrictedSet data center) ≤
        ((2 * layerCount : ℕ) : ENNReal) *
          ∑ i ∈ volumeSelected, volume (piece i) := by
    have h :
        (∑ i, weight i) =
          volume (ambientRestrictedSet data center) :=
      volume_sum.symm
    rw [h] at volumeSelected_mass_raw
    exact volumeSelected_mass_raw
  let metricCard : Fin fineSetup.fine.card → ℕ := fun i =>
    ((ambientRestrictedData data center hE).metricFiber
      (fineSetup.source i)).card
  let retainedCard : Fin fineSetup.fine.card → ℕ := fun i =>
    (fineSetup.pointData.fiber (fineSetup.source i)).card
  let upper := data.ambientSource.card
  have hcardBounds :
      ∀ i ∈ volumeSelected,
        0 < metricCard i ∧
          metricCard i ≤ upper ∧
          0 < retainedCard i ∧
          retainedCard i ≤ upper := by
    intro i _
    let p := fineSetup.source i
    let restricted := ambientRestrictedData data center hE
    have hretainedNonempty :
        (fineSetup.pointData.fiber p).carrier.Nonempty := by
      rw [fineSetup.pointData_fiber p]
      exact restricted.fiber_nonempty hdelta p
    have hretainedPos : 0 < retainedCard i := by
      exact (Set.ncard_pos
        (fineSetup.pointData.fiber p).finite).2 hretainedNonempty
    have hmetricNonempty :
        (restricted.metricFiber p).carrier.Nonempty := by
      have hcenter := restricted.center_mem_fiber hdelta p
      exact
        ⟨restricted.assignment.center p,
          restricted.fiber_subset_metric p hcenter⟩
    have hmetricPos : 0 < metricCard i := by
      exact (Set.ncard_pos
        (restricted.metricFiber p).finite).2 hmetricNonempty
    have hmetricSubset :
        (restricted.metricFiber p).carrier ⊆
          data.ambientSource.carrier := by
      intro function hfunction
      have hsource :
          function ∈ (restricted.source p).carrier :=
        ((restricted.certificate p).metric_subset hfunction).1
      exact restricted.source_subset_ambient p hsource
    have hmetricUpper : metricCard i ≤ upper := by
      exact Set.ncard_le_ncard hmetricSubset data.ambientSource.finite
    have hretainedSubset :
        (fineSetup.pointData.fiber p).carrier ⊆
          data.ambientSource.carrier := by
      rw [fineSetup.pointData_fiber p]
      exact restricted.fiber_subset_ambient p
    have hretainedUpper : retainedCard i ≤ upper := by
      exact Set.ncard_le_ncard hretainedSubset data.ambientSource.finite
    exact
      ⟨hmetricPos, hmetricUpper, hretainedPos, hretainedUpper⟩
  rcases hJoint volumeSelected metricCard retainedCard upper
      volumeSelected_nonempty hcardBounds with
    ⟨metricLevel, retainedLevel, selected,
      metricLevel_bound, retainedLevel_bound, selected_nonempty,
      selected_eq, fiber_retention_raw, ranges⟩
  let fiberLoss := (Nat.log2 data.ambientSource.card + 1) ^ 2
  have fiberLoss_eq :
      fiberLoss = (Nat.log2 data.ambientSource.card + 1) ^ 2 := rfl
  have selected_subset : selected ⊆ volumeSelected := by
    rw [selected_eq]
    exact Finset.filter_subset _ _
  have selected_layer : ∀ i ∈ selected,
      (2 : ENNReal) ^ layer.val * cutoff ≤ volume (piece i) ∧
        volume (piece i) <
          (2 : ENNReal) ^ (layer.val + 1) * cutoff := by
    intro i hi
    exact volumeSelected_layer i (selected_subset hi)
  have metric_range : ∀ i ∈ selected,
      2 ^ metricLevel ≤
          ((ambientRestrictedData data center hE).metricFiber
            (fineSetup.source i)).card ∧
        ((ambientRestrictedData data center hE).metricFiber
            (fineSetup.source i)).card <
          2 ^ (metricLevel + 1) := by
    intro i hi
    exact ⟨(ranges i hi).1, (ranges i hi).2.1⟩
  have retained_range : ∀ i ∈ selected,
      2 ^ retainedLevel ≤
          (fineSetup.pointData.fiber (fineSetup.source i)).card ∧
        (fineSetup.pointData.fiber (fineSetup.source i)).card <
          2 ^ (retainedLevel + 1) := by
    intro i hi
    exact (ranges i hi).2.2
  have fiber_retention :
      volumeSelected.card ≤ fiberLoss * selected.card := by
    simpa [fiberLoss] using fiber_retention_raw
  let massFactor := 4 * layerCount * fiberLoss
  have massFactor_eq : massFactor = 4 * layerCount * fiberLoss := rfl
  have selected_mass :
      volume (ambientRestrictedSet data center) ≤
        (massFactor : ENNReal) *
          ∑ i ∈ selected, volume (piece i) := by
    have hmass :=
      dyadic_selected_mass_le_joint_regularized_sum
        (weight := fun i => volume (piece i))
        volumeSelected selected
        ((2 : ENNReal) ^ layer.val * cutoff)
        (volume (ambientRestrictedSet data center))
        (fun i hi => by
          have h := (volumeSelected_layer i hi).2
          simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h)
        (fun i hi => (selected_layer i hi).1)
        volumeSelected_mass fiber_retention
    simpa [massFactor] using hmass
  rcases parent_fiber_cardinality_regularization
      (rectangles := selected)
      (parent := coarseSetup.coarseData.parent)
      selected_nonempty with
    ⟨parentLevel, selectedParents, parentLevel_bound,
      selectedParents_nonempty, selectedParents_eq,
      parent_retention, parent_partition, parent_range⟩
  exact
    ⟨⟨piece, piece_measurable, piece_disjoint, piece_subset,
      bin_eq_union, volume_sum, piece_volume,
      cutoff, cutoff_pos, cutoff_ne_top, cutoff_eq,
      layerCount, layerCount_pos, layerCount_bound, layer,
      volumeSelected, volumeSelected_nonempty,
      volumeSelected_layer, volumeSelected_mass,
      metricLevel, retainedLevel,
      metricLevel_bound, retainedLevel_bound,
      fiberLoss, fiberLoss_eq,
      selected, selected_nonempty, selected_eq, selected_subset,
      fiber_retention, selected_layer, metric_range, retained_range,
      massFactor, massFactor_eq, selected_mass,
      parentLevel, selectedParents, parentLevel_bound,
      selectedParents_nonempty, selectedParents_eq,
      parent_retention, parent_partition, parent_range⟩⟩

lemma AmbientRestrictedLargeBinRefinementData.metric_card_bound
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
    (hdelta : 0 < delta)
    (i : Fin fineSetup.fine.card)
    (hi : i ∈ refinement.selected) :
    (((ambientRestrictedData data center hE).metricFiber
        (fineSetup.source i)).card : ℝ) ≤
      (4 * Real.rpow (2 * tRep / DeltaRep) eta) *
        (refinement.retainedScale : ℝ) := by
  let restricted := ambientRestrictedData data center hE
  let p := fineSetup.source i
  have hretainedEq :
      (fineSetup.pointData.fiber p).card =
        (restricted.assignment.fiber p).card := by
    rw [fineSetup.pointData_fiber p]
  have hretainedUpper :
      (restricted.assignment.fiber p).card <
        2 * refinement.retainedScale := by
    rw [← hretainedEq]
    exact (refinement.retained_scale_range i hi).2
  have hretention :
      Real.rpow (DeltaRep / (2 * tRep)) eta *
            ((restricted.metricFiber p).card : ℝ) ≤
        2 * ((restricted.assignment.fiber p).card : ℝ) :=
    representative_metric_to_retained_fiber restricted hdelta p
  exact representative_metric_card_le_retained_scale
    data.tRep_pos (hdelta.trans_le data.delta_le_DeltaRep)
    data.eta_pos hretainedUpper hretention

end Kakeya.Cinematic
