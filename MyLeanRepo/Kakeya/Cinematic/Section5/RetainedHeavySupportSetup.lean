import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberRetainedEq
import MyLeanRepo.Kakeya.Cinematic.Section5.RetainedHeavySupportSetupInputs

/-!
# Heavy-parent and support regularization on retained incidences
-/

namespace Kakeya.Cinematic

attribute [local instance] Classical.decEq

theorem retained_heavy_support_setup :
    RetainedHeavySupportSetupStatement := by
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement degreeSetup
    q_fiber fiberBound hq_fiber_pos hfiberBound_pos
    hfiber_lower hfiber_upper
  set parent := coarseSetup.coarseData.parent with hparent_def
  set retained := degreeSetup.retained with hretained_def
  set fiber := degreeSetup.fiber with hfiber_def
  set selectedEdges := degreeSetup.selectedEdges with hselectedEdges_def
  set M_parent : ℕ := 2 ^ refinement.parentLevel with hM_parent_def
  set degreeLoss : ℕ :=
    Nat.log2 (Fintype.card (Fin fineSetup.fine.card)) + 1
      with hdegreeLoss_def
  set rectangleBound : ℝ := 2 * M_parent with hrectangleBound_def
  set heavyLogLoss : ℝ := 4 * degreeLoss with hheavyLogLoss_def
  set heavyThreshold : ℝ :=
    rectangleBound * (q_fiber : ℝ) / heavyLogLoss
      with hheavyThreshold_def
  set active := incidenceParentSupport selectedEdges parent
    with hactive_def
  set heavy := active.filter fun coarse =>
    heavyThreshold ≤
      ((incidenceParentEdges selectedEdges parent coarse).card : ℝ)
    with hheavy_def
  set ambientFamily :=
    data.ambientSource.cluster center (3 * tRep)
      with hambientFamily_def
  set ambient : Finset C2Function := ambientFamily.toFinset
    with hambient_def
  have hselected' :
      selectedEdges ⊆ fineFiberIncidenceEdgesOn retained fiber := by
    rw [hselectedEdges_def, hretained_def, hfiber_def]
    rw [← degreeSetup.rawEdges_eq]
    exact degreeSetup.selectedEdges_subset
  have hretention :
      (fineFiberIncidenceEdgesOn retained fiber).card ≤
        degreeLoss * selectedEdges.card := by
    have h1 :
        (fineFiberIncidenceEdgesOn retained fiber).card =
          degreeSetup.rawEdges.card := by
      rw [hretained_def, hfiber_def, degreeSetup.rawEdges_eq]
    rw [h1]
    exact degreeSetup.degree_retention
  have hM_parent_pos : 0 < M_parent := by
    rw [hM_parent_def]
    positivity
  have hdegreeLoss_pos : 0 < degreeLoss := by
    rw [hdegreeLoss_def]
    omega
  have hactive_subset : active ⊆ refinement.selectedParents := by
    rw [hactive_def]
    intro coarse hcoarse
    rcases Finset.mem_image.mp hcoarse with
      ⟨edge, hedge, hparent_eq⟩
    have hedge_raw : edge ∈ degreeSetup.rawEdges :=
      degreeSetup.selectedEdges_subset hedge
    have hedge_full :
        edge ∈ fineFiberIncidenceEdgesOn
          degreeSetup.retained degreeSetup.fiber := by
      rw [degreeSetup.rawEdges_eq] at hedge_raw
      exact hedge_raw
    have hrectangle : edge.2 ∈ degreeSetup.retained :=
      (mem_fineFiberIncidenceEdgesOn
        degreeSetup.retained degreeSetup.fiber
        edge.1 edge.2).mp hedge_full |>.1
    have hparent_in :
        parent edge.2 ∈ refinement.selectedParents := by
      rw [degreeSetup.retained_eq] at hrectangle
      exact (Finset.mem_filter.mp hrectangle).2
    rw [hparent_eq] at hparent_in
    exact hparent_in
  have hparentFiber_eq :
      ∀ coarse ∈ refinement.selectedParents,
        parentFiber retained parent coarse =
          parentFiber refinement.selected parent coarse := by
    intro coarse hcoarse
    have h :
        retained =
          rectanglesOverParents refinement.selected
            parent refinement.selectedParents := by
      rw [hretained_def, degreeSetup.retained_eq]
    rw [h]
    exact parentFiber_retained_eq
      refinement.selected parent refinement.selectedParents
      coarse hcoarse
  have hparentRange :
      ∀ coarse ∈ active,
        M_parent ≤ (parentFiber retained parent coarse).card ∧
          (parentFiber retained parent coarse).card <
            2 * M_parent := by
    intro coarse hcoarse
    have hcoarse' : coarse ∈ refinement.selectedParents :=
      hactive_subset hcoarse
    have hrange := refinement.parent_range coarse hcoarse'
    have heq :
        parentFiber retained parent coarse =
          parentFiber refinement.selected parent coarse :=
      hparentFiber_eq coarse hcoarse'
    rw [heq]
    have h2 : M_parent = 2 ^ refinement.parentLevel := by
      rw [hM_parent_def]
    rw [h2]
    have h3 : parent = coarseSetup.coarseData.parent :=
      hparent_def
    rw [h3] at *
    have h4 :
        2 ^ (refinement.parentLevel + 1) =
          2 * 2 ^ refinement.parentLevel := by
      rw [pow_succ]
      ring
    rw [h4] at hrange
    exact hrange
  rcases incidence_quantitative_heavy_parent_selection
      retained fiber selectedEdges hselected' parent
      M_parent q_fiber degreeLoss fiberBound
      hM_parent_pos hq_fiber_pos hdegreeLoss_pos hfiberBound_pos
      hparentRange hfiber_lower hfiber_upper
      hretention degreeSetup.selectedEdges_nonempty with
    ⟨hheavy_lower, hheavy_nonempty, hheavy_aggregate⟩
  have hfiber_ambient :
      ∀ rectangle ∈ retained,
        (fiber rectangle).carrier ⊆ ambientFamily.carrier := by
    intro rectangle _
    rw [hfiber_def, degreeSetup.fiber_eq]
    exact fineSetup.point_fiber_ambient
      (fineSetup.source rectangle)
  have hsupportAmbient_set :
      ∀ coarse,
        (incidenceFunctionSupport selectedEdges parent coarse :
            Set C2Function) ⊆ ambientFamily.carrier := by
    intro coarse
    exact incidenceFunctionSupport_subset_ambient_on
      retained fiber selectedEdges hselected'
      ambientFamily hfiber_ambient parent coarse
  have hsupportAmbient :
      ∀ coarse ∈ heavy,
        incidenceFunctionSupport selectedEdges parent coarse ⊆
          ambient := by
    intro coarse _ function hfunction
    have h6 : function ∈ ambientFamily.carrier :=
      hsupportAmbient_set coarse hfunction
    simpa [ambient, FiniteFunctionFamily.toFinset,
      Set.Finite.mem_toFinset] using h6
  rcases regularize_heavy_incidence_supports
      ambient selectedEdges parent heavy
      hheavy_nonempty
      (show heavy ⊆ active from Finset.filter_subset _ _)
      hsupportAmbient with
    ⟨supportLevel, selectedCoarse, hsupportLevel_bound,
      hselectedCoarse_nonempty, hselectedCoarse_eq,
      hsupport_retention, hselectedCoarse_subset,
      hsupport_range⟩
  exact
    ⟨M_parent, degreeLoss, active, rectangleBound,
      heavyLogLoss, heavyThreshold, heavy,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      hheavy_lower, hheavy_nonempty, hheavy_aggregate,
      ambient, rfl,
      supportLevel, selectedCoarse,
      hsupportLevel_bound, hselectedCoarse_nonempty,
      hselectedCoarse_eq, hsupport_retention,
      hselectedCoarse_subset, hsupport_range,
      hsupportAmbient⟩

end Kakeya.Cinematic
