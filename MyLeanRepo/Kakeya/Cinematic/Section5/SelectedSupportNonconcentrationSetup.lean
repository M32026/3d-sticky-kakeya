import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportNonconcentrationSetupInputs

/-!
# Nonconcentration of selected fixed-bin supports
-/

namespace Kakeya.Cinematic

theorem selected_support_nonconcentration_setup :
    SelectedSupportNonconcentrationSetupStatement := by
  refine' fun hCoarseAt => _
  refine' fun {family E K delta diameter epsilon eta tRep DeltaRep C_R₀} => _
  refine' fun data center hE {C_R C_count C_shading C_volume} => _
  refine' fun fineSetup coarseSetup {massExponent} => _
  refine' fun refinement degreeSetup q_fiber fiberBound heavySetup
    mu₁ coefficient radius => _
  refine' fun hq_fiber_pos hcoefficient_nonneg hmu₁_le
    hfiberBound => _
  classical
  let edges := degreeSetup.selectedEdges
  let parent := coarseSetup.coarseData.parent
  let level := degreeSetup.degreeLevel
  let mu₂ : ℝ := q_fiber
  have hMu2Pos : 0 < mu₂ := by
    simp only [mu₂]
    exact_mod_cast hq_fiber_pos
  have hDegreeLossOne : 1 ≤ heavySetup.degreeLoss := by
    rw [heavySetup.degreeLoss_eq]
    omega
  have hLogLossOne : 1 ≤ heavySetup.heavyLogLoss := by
    rw [heavySetup.heavyLogLoss_eq]
    have h : (1 : ℝ) ≤ 4 * (heavySetup.degreeLoss : ℝ) := by
      have h' : (1 : ℝ) ≤ (heavySetup.degreeLoss : ℝ) := by
        exact_mod_cast hDegreeLossOne
      linarith
    exact h
  have hparents :
      heavySetup.selectedCoarse ⊆
        incidenceParentSupport edges parent := by
    have h1 : heavySetup.selectedCoarse ⊆ heavySetup.heavy :=
      heavySetup.selectedCoarse_subset
    have h2 : heavySetup.heavy ⊆ heavySetup.active := by
      rw [heavySetup.heavy_eq]
      exact Finset.filter_subset _ _
    have h3 :
        heavySetup.active = incidenceParentSupport edges parent :=
      heavySetup.active_eq
    simpa [h3] using h1.trans h2
  have hAggregate' :
      ∀ coarse ∈ heavySetup.selectedCoarse,
        ((incidenceRectangleSupport edges parent coarse).card : ℝ) *
              mu₂ ≤
          heavySetup.heavyLogLoss *
            (incidenceCountOverParent edges parent coarse
              (incidenceFunctionSupport edges parent coarse) : ℝ) := by
    intro coarse hcoarse
    exact heavySetup.heavy_aggregate coarse
      (heavySetup.selectedCoarse_subset hcoarse)
  have hBallUpper' :
      ∀ coarse ∈ heavySetup.selectedCoarse,
        ∀ rectangle ∈ incidenceRectangleSupport edges parent coarse,
          ∀ testCenter,
            (((incidenceRectangleFiber edges rectangle :
                Set C2Function) ∩
              c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
              mu₁ := by
    intro coarse hcoarse
    exact hfiberBound coarse
      (heavySetup.selectedCoarse_subset hcoarse)
  have hSupportNonconcentration :
      ∀ coarse ∈ heavySetup.selectedCoarse, ∀ testCenter,
        (((incidenceSupportFamily edges parent coarse).carrier ∩
            c2Ball testCenter (11 * radius)).ncard : ℝ) ≤
          (2 * heavySetup.heavyLogLoss) * coefficient *
            ((incidenceSupportFamily edges parent coarse).card : ℝ) := by
    intro coarse hcoarse testCenter
    exact hCoarseAt incidence_support_double_count
      edges parent level degreeSetup.degree_range coarse
      (incidenceRectangleSupport_nonempty_of_mem_parentSupport
        edges parent coarse (hparents hcoarse))
      testCenter (11 * radius)
      (mu₁ := mu₁) (mu₂ := mu₂)
      (coefficient := coefficient)
      (logLoss := heavySetup.heavyLogLoss)
      hMu2Pos hcoefficient_nonneg hLogLossOne hmu₁_le
      (hAggregate' coarse hcoarse)
      (fun rectangle hrectangle =>
        hBallUpper' coarse hcoarse
          rectangle hrectangle testCenter)
  have hCoarseTangent' :
      ∀ coarse, ∀ function ∈
        (coarseTangentFamily coarseSetup.coarseData
          degreeSetup.fiber coarse).carrier,
        (coarseSetup.coarseData.coarse.rectangle coarse).IsLambdaTangent
          function coarseSetup.tangency := by
    have hfiber_eq :
        degreeSetup.fiber =
          fun i : Fin fineSetup.fine.card =>
            fineSetup.pointData.fiber (fineSetup.source i) :=
      degreeSetup.fiber_eq
    intro coarse function hfunction
    rw [hfiber_eq] at hfunction
    exact coarseSetup.coarse_tangent coarse function hfunction
  have hClusterTangentHalf :
      2 * ((2 * heavySetup.heavyLogLoss) * coefficient) ≤ 1 →
        ∀ index :
            Fin (selectedCoarseSubfamily coarseSetup.coarseData
              heavySetup.selectedCoarse).card,
          ∀ testCenter,
            2 * RectangleFamily.tangentCount
                  ((selectedCoarseSubfamily coarseSetup.coarseData
                    heavySetup.selectedCoarse).family.rectangle index)
                  ((selectedCoarseIncidenceSupport
                    coarseSetup.coarseData edges
                      heavySetup.selectedCoarse index).cluster
                        testCenter (11 * radius))
                  coarseSetup.tangency ≤
              RectangleFamily.tangentCount
                ((selectedCoarseSubfamily coarseSetup.coarseData
                  heavySetup.selectedCoarse).family.rectangle index)
                (selectedCoarseIncidenceSupport
                  coarseSetup.coarseData edges
                    heavySetup.selectedCoarse index)
                coarseSetup.tangency := by
    intro hsmall index testCenter
    have hsmall' :
        4 * heavySetup.heavyLogLoss * coefficient ≤ 1 := by
      have h' :
          2 * ((2 * heavySetup.heavyLogLoss) * coefficient) =
            4 * heavySetup.heavyLogLoss * coefficient := by
        ring
      rw [h'] at hsmall
      exact hsmall
    have hselected :
        edges ⊆ fineFiberIncidenceEdgesOn
          degreeSetup.retained degreeSetup.fiber := by
      calc
        edges ⊆ degreeSetup.rawEdges :=
          degreeSetup.selectedEdges_subset
        _ = fineFiberIncidenceEdgesOn
            degreeSetup.retained degreeSetup.fiber :=
          degreeSetup.rawEdges_eq
    exact selectedCoarseIncidenceSupport_cluster_tangentCount_half
      coarseSetup.coarseData
      degreeSetup.retained degreeSetup.fiber
      edges hselected heavySetup.selectedCoarse
      hCoarseTangent'
      (hsmall := hsmall')
      (hNonconcentration := fun coarse hcoarse center =>
        hSupportNonconcentration coarse hcoarse center)
      index testCenter
  exact ⟨hSupportNonconcentration, hClusterTangentHalf⟩

end Kakeya.Cinematic
