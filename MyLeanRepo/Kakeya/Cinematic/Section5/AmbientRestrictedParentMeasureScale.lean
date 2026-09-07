import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentMeasureScaleInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberAssignedMass

/-!
# Measure scale for the selected parent multiplicity
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem ambient_restricted_parent_measure_scale :
    AmbientRestrictedParentMeasureScaleStatement := by
  intro hContain hCommon hComparable K D C_shading hK hD hC_shading
  rcases coarse_fiber_assigned_piece_card
      hContain hCommon hComparable hK hD hC_shading with
    ⟨C_out, hC_out, hfiber⟩
  refine ⟨C_out, hC_out, ?_⟩
  intro family E delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_volume fineSetup coarseSetup
    massExponent refinement
  intro hfamily hdelta hC_R
  let Lambda : ENNReal :=
    (2 : ENNReal) ^ refinement.layer.val * refinement.cutoff
  have htwo_ne_zero :
      (2 : ENNReal) ^ refinement.layer.val ≠ 0 := by
    simp
  have hLambda_pos : 0 < Lambda :=
    ENNReal.mul_pos htwo_ne_zero refinement.cutoff_pos.ne'
  have hLambda_ne_top : Lambda ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · exact refinement.cutoff_ne_top
  rcases refinement.selectedParents_nonempty with ⟨j, hj⟩
  have hI :
      (ambientRestrictedData data center hE).interval.IsControlled K := by
    have h : data.assignment.interval.IsControlled K :=
      data.assignment.intervalControlled
    have h1 :
        (ambientRestrictedData data center hE).interval =
          data.assignment.interval := by
      simp [ambientRestrictedData, data.assignment_interval]
    rw [h1]
    exact h
  have hpiece_sub :
      ∀ i, refinement.piece i ⊆ (fineSetup.enlarged i).realCarrier := by
    intro i
    exact (refinement.piece_subset i).trans Set.inter_subset_right
  have hpiece_lower :
      ∀ i ∈ refinement.selected,
        Lambda ≤ volume (refinement.piece i) := by
    intro i hi
    exact (refinement.selected_layer i hi).1
  have hbound := hfiber
    (data := coarseSetup.coarseData)
    hfamily hI hdelta data.delta_le_DeltaRep data.DeltaRep_le_tRep
    hC_R
    (U := fineSetup.enlarged)
    fineSetup.enlarged_function fineSetup.enlarged_midpoint
    refinement.piece refinement.piece_measurable
    refinement.piece_disjoint hpiece_sub
    refinement.selected Lambda hLambda_pos hLambda_ne_top
    hpiece_lower j
  have hfiber_eq :
      refinement.selected.filter
          (fun i => coarseSetup.coarseData.parent i = j) =
        parentFiber refinement.selected
          coarseSetup.coarseData.parent j := by
    rfl
  rw [hfiber_eq] at hbound
  have hparent_lower :
      (2 ^ refinement.parentLevel : ℕ) ≤
        (parentFiber refinement.selected
          coarseSetup.coarseData.parent j).card :=
    (refinement.parent_range j hj).1
  have hmain :
      ((2 ^ refinement.parentLevel : ℕ) : ℝ) ≤
        ((parentFiber refinement.selected
          coarseSetup.coarseData.parent j).card : ℝ) := by
    exact_mod_cast hparent_lower
  exact hmain.trans hbound

end Kakeya.Cinematic
