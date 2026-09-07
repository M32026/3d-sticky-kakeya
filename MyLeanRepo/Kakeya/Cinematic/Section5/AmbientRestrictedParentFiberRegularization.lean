import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentFiberRegularizationInputs

/-!
# Selected incidence fibers below each fixed-bin parent
-/

namespace Kakeya.Cinematic

noncomputable local instance
    ambientRestrictedParentFiberRegularizationProofDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem ambient_restricted_parent_fiber_regularization :
    AmbientRestrictedParentFiberRegularizationStatement := by
  dsimp only [AmbientRestrictedParentFiberRegularizationStatement]
  intro hreg
  refine' fun {family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    data center hE {C_R C_count C_shading C_volume}
    fineSetup coarseSetup {massExponent} refinement degreeSetup
    q_fiber fiberBound heavySetup hq_fiber hlogLoss
    hfiberBoundPos hfiberBound => _
  let selectedCoarse := heavySetup.selectedCoarse
  let subfamily :=
    selectedCoarseSubfamily coarseSetup.coarseData selectedCoarse
  have hselectedEdges_subset :
      degreeSetup.selectedEdges ⊆
        fineFiberIncidenceEdgesOn
          degreeSetup.retained degreeSetup.fiber := by
    rw [← degreeSetup.rawEdges_eq]
    exact degreeSetup.selectedEdges_subset
  choose pairLower_parent selectedRectangles_parent
      h1 h2 h3 h4 h5 h6 h7 using
    fun (index : Fin subfamily.card) =>
      let coarse := subfamily.embedding index
      have hcoarse_selected : coarse ∈ selectedCoarse :=
        selectedCoarseSubfamily_parent_mem
          coarseSetup.coarseData selectedCoarse index
      have hcoarse_heavy : coarse ∈ heavySetup.heavy :=
        heavySetup.selectedCoarse_subset hcoarse_selected
      have hheavyThreshold_pos :
          0 < heavySetup.heavyThreshold := by
        rw [heavySetup.heavyThreshold_eq]
        have hrectBound_pos :
            0 < heavySetup.rectangleBound := by
          rw [heavySetup.rectangleBound_eq,
            heavySetup.M_parent_eq]
          positivity
        positivity
      have hthresh :
          heavySetup.heavyThreshold ≤
            ((incidenceParentEdges degreeSetup.selectedEdges
              coarseSetup.coarseData.parent coarse).card : ℝ) := by
        rw [heavySetup.heavy_eq] at hcoarse_heavy
        exact (Finset.mem_filter.mp hcoarse_heavy).2
      have hparentEdges_pos :
          0 < (incidenceParentEdges degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).card := by
        have hpos :
            (0 : ℝ) <
              ((incidenceParentEdges degreeSetup.selectedEdges
                coarseSetup.coarseData.parent coarse).card : ℝ) :=
          hheavyThreshold_pos.trans_le hthresh
        exact_mod_cast hpos
      have hparentNonempty :
          (incidenceParentEdges degreeSetup.selectedEdges
            coarseSetup.coarseData.parent coarse).Nonempty :=
        Finset.card_pos.mp hparentEdges_pos
      have haggregate :
          ((incidenceRectangleSupport degreeSetup.selectedEdges
              coarseSetup.coarseData.parent coarse).card : ℝ) *
                (q_fiber : ℝ) ≤
            heavySetup.heavyLogLoss *
              ((incidenceParentEdges degreeSetup.selectedEdges
                coarseSetup.coarseData.parent coarse).card : ℝ) := by
        have h := heavySetup.heavy_aggregate coarse hcoarse_heavy
        rw [incidenceCountOverParent_support_eq_parentEdges_card
          degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse] at h
        exact h
      have hfiberBound' :
          ∀ rectangle ∈
              incidenceRectangleSupport degreeSetup.selectedEdges
                coarseSetup.coarseData.parent coarse,
            ((incidenceRectangleFiber
              degreeSetup.selectedEdges rectangle).card : ℝ) ≤
              fiberBound := by
        intro rectangle hrectangle
        have hrect_retained : rectangle ∈ degreeSetup.retained :=
          incidenceRectangleSupport_subset_selected
            degreeSetup.retained degreeSetup.fiber
            degreeSetup.selectedEdges hselectedEdges_subset
            coarseSetup.coarseData.parent coarse hrectangle
        have hsubset :
            incidenceRectangleFiber degreeSetup.selectedEdges rectangle ⊆
              (degreeSetup.fiber rectangle).toFinset :=
          incidenceRectangleFiber_subset_fiber_on
            degreeSetup.retained degreeSetup.fiber
            degreeSetup.selectedEdges hselectedEdges_subset rectangle
        have hcard :
            (incidenceRectangleFiber
              degreeSetup.selectedEdges rectangle).card ≤
              (degreeSetup.fiber rectangle).toFinset.card :=
          Finset.card_le_card hsubset
        have hcard_eq :
            (degreeSetup.fiber rectangle).toFinset.card =
              (degreeSetup.fiber rectangle).card :=
          (Set.ncard_eq_toFinset_card
            (degreeSetup.fiber rectangle).carrier
            (degreeSetup.fiber rectangle).finite).symm
        have hcard' :
            ((incidenceRectangleFiber
              degreeSetup.selectedEdges rectangle).card : ℝ) ≤
              ((degreeSetup.fiber rectangle).card : ℝ) := by
          rw [← hcard_eq]
          exact_mod_cast hcard
        exact hcard'.trans
          (hfiberBound rectangle hrect_retained)
      hreg (α := C2Function)
        (β := Fin fineSetup.fine.card)
        (γ := Fin coarseSetup.coarseData.coarse.card)
        degreeSetup.selectedEdges coarseSetup.coarseData.parent
        coarse q_fiber heavySetup.heavyLogLoss fiberBound
        hq_fiber hlogLoss hfiberBoundPos
        hparentNonempty haggregate hfiberBound'
  let pairLower : Fin subfamily.card → ℕ :=
    pairLower_parent
  let selectedRectangles :
      Fin subfamily.card → Finset (Fin fineSetup.fine.card) :=
    selectedRectangles_parent
  have h8 :
      ∀ index,
        selectedRectangles index ⊆ degreeSetup.retained := by
    intro index
    have hsub :
        selectedRectangles index ⊆
          incidenceRectangleSupport degreeSetup.selectedEdges
            coarseSetup.coarseData.parent
            (subfamily.embedding index) := by
      dsimp only [selectedRectangles]
      rw [h3 index]
      exact Finset.filter_subset _ _
    have hsup :
        incidenceRectangleSupport degreeSetup.selectedEdges
            coarseSetup.coarseData.parent
            (subfamily.embedding index) ⊆
          degreeSetup.retained :=
      incidenceRectangleSupport_subset_selected
        degreeSetup.retained degreeSetup.fiber
        degreeSetup.selectedEdges hselectedEdges_subset
        coarseSetup.coarseData.parent (subfamily.embedding index)
    exact hsub.trans hsup
  have h9 :
      ∀ rectangle,
        incidenceRectangleFiber degreeSetup.selectedEdges rectangle ⊆
          (degreeSetup.fiber rectangle).toFinset := by
    intro rectangle
    exact incidenceRectangleFiber_subset_fiber_on
      degreeSetup.retained degreeSetup.fiber
      degreeSetup.selectedEdges hselectedEdges_subset rectangle
  exact
    ⟨{ pairLower := pairLower
       selectedRectangles := selectedRectangles
       pairLower_eq := h1
       pairLower_pos := h2
       selectedRectangles_eq := h3
       selectedRectangles_nonempty := h4
       selected_card_lower := h5
       q_fiber_le_pairLower := h6
       selected_fiber_lower := h7
       selectedRectangles_subset_retained := h8
       selected_fiber_subset_original := h9 }⟩

end Kakeya.Cinematic
