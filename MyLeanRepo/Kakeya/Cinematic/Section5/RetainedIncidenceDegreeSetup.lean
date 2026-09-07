import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedIncidenceDegreeSetupInputs

/-!
# Degree regularization on retained fine rectangles
-/

noncomputable section

namespace Kakeya.Cinematic

local instance retainedIncidenceDegreeSetupDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem retained_incidence_degree_setup :
    RetainedIncidenceDegreeSetupStatement := by
  intro hreg
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
  intro data center hE C_R C_count C_shading C_volume
  intro fineSetup coarseSetup massExponent refinement
  intro hfibers
  let retained := rectanglesOverParents refinement.selected
    coarseSetup.coarseData.parent refinement.selectedParents
  let fiber : Fin fineSetup.fine.card → FiniteFunctionFamily :=
    fun i => fineSetup.pointData.fiber (fineSetup.source i)
  let rawEdges := fineFiberIncidenceEdgesOn retained fiber
  have hretained_nonempty : retained.Nonempty := by
    rcases refinement.selectedParents_nonempty with ⟨coarse, hcoarse⟩
    have hrange := refinement.parent_range coarse hcoarse
    have hpow_pos : 0 < 2 ^ refinement.parentLevel :=
      pow_pos (by norm_num) refinement.parentLevel
    have h1 : 1 ≤ (parentFiber refinement.selected
        coarseSetup.coarseData.parent coarse).card := by
      have h2 : 1 ≤ 2 ^ refinement.parentLevel := by
        exact Nat.succ_le_iff.mpr hpow_pos
      linarith [hrange.1]
    have hfiber_nonempty : (parentFiber refinement.selected
        coarseSetup.coarseData.parent coarse).Nonempty :=
      Finset.card_pos.mp (by omega)
    rcases hfiber_nonempty with ⟨i, hi⟩
    have hi_selected : i ∈ refinement.selected :=
      (Finset.mem_filter.mp hi).1
    have hparent_eq : coarseSetup.coarseData.parent i = coarse :=
      (Finset.mem_filter.mp hi).2
    have hparent_in : coarseSetup.coarseData.parent i ∈
        refinement.selectedParents := by
      rw [hparent_eq]
      exact hcoarse
    have hi_retained : i ∈ retained := by
      simp only [retained, rectanglesOverParents, Finset.mem_filter]
      exact ⟨hi_selected, hparent_in⟩
    exact ⟨i, hi_retained⟩
  have hrawEdges_nonempty : rawEdges.Nonempty := by
    rcases hretained_nonempty with ⟨i, hi⟩
    have hfiber_nonempty : (fiber i).carrier.Nonempty := hfibers i hi
    rcases hfiber_nonempty with ⟨function, hfunction⟩
    have hedge : (function, i) ∈ rawEdges := by
      rw [mem_fineFiberIncidenceEdgesOn]
      exact ⟨hi, hfunction⟩
    exact ⟨(function, i), hedge⟩
  rcases hreg (edges := rawEdges)
      (parent := coarseSetup.coarseData.parent) hrawEdges_nonempty with
    ⟨level, selected, hlevel_bound, hselected_eq, hretention, hrange⟩
  refine' ⟨retained, fiber, rawEdges, rfl, rfl, rfl,
    hrawEdges_nonempty, level, selected,
    hlevel_bound, hselected_eq, hretention, hrange, _, _⟩
  · rw [hselected_eq]
    exact Finset.filter_subset _ _
  · have hpos : 0 < rawEdges.card := hrawEdges_nonempty.card_pos
    have h : 0 < selected.card := by
      by_contra h'
      have h'' : selected.card = 0 := by omega
      rw [h''] at hretention
      omega
    exact Finset.card_pos.mp h

end Kakeya.Cinematic

end section
