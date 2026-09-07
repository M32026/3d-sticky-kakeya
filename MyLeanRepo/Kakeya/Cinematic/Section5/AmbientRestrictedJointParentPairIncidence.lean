import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedJointParentPairIncidenceInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.Counting
import MyLeanRepo.Kakeya.Cinematic.Section5.FinePairIncidenceBound
import MyLeanRepo.Kakeya.Cinematic.Section5.ProductScaleFixedPairIncidence
import MyLeanRepo.Kakeya.Cinematic.TangencyGeometryCompletion
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceGoodPairBudgetAlgebra

/-!
# Parent pair incidence from the joint fiber scales
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_joint_parent_pair_incidence :
    AmbientRestrictedJointParentPairIncidenceStatement := by
  intro hCutoffs hGoodPairs hPairIncidence K D hK hD
  have hMain :=
    hPairIncidence product_scale_fixed_pair_incidence
      tangency_geometry_completion fine_pair_incidence_bound
      pair_incidence_counting
  rcases hMain K D hK hD with ⟨C_inc, hC_inc_pos, hC_inc⟩
  refine' ⟨C_inc, hC_inc_pos, ?h_goal⟩
  · exact fun {family E delta diameter epsilon eta tRep DeltaRep C_R₀}
      (data : _) (center : _) (hE : _)
      {C_R C_count C_shading C_volume}
      (fineSetup : _) (coarseSetup : _)
      {massExponent}
      (refinement : _) (incidence : _)
      (hFamily : _) (hdelta : _) (hC_R : _) (hq_fiber : _)
      (hmetricScale : _) (htangencyScale : _)
      (hsmall : _) (hCc_delta : _) (index : _) => by
        classical
        let fiberRatio : ℝ :=
          4 * Real.rpow (2 * tRep / DeltaRep) eta
        let heavyLogLoss : ℝ := incidence.heavySetup.heavyLogLoss
        let metricCut : ℝ :=
          selectedIncidenceMetricCut heavyLogLoss fiberRatio epsilon
        let tangencyCut : ℝ :=
          selectedIncidenceTangencyCut heavyLogLoss eta

        have hDeltaRep_pos : 0 < DeltaRep := by
          have h : delta ≤ DeltaRep := data.delta_le_DeltaRep
          linarith
        have htRep_pos : 0 < tRep := data.tRep_pos
        have hepsilon_pos : 0 < epsilon := data.epsilon_pos
        have heta_pos : 0 < eta := data.eta_pos

        have hdegreeLoss_pos : 0 < incidence.heavySetup.degreeLoss := by
          rw [incidence.heavySetup.degreeLoss_eq]
          omega
        have hheavyLogLoss_ge_one : 1 ≤ heavyLogLoss := by
          dsimp only [heavyLogLoss]
          rw [incidence.heavySetup.heavyLogLoss_eq]
          have h :
              (1 : ℝ) ≤
                (4 : ℝ) * (incidence.heavySetup.degreeLoss : ℝ) := by
            have h' : 0 < incidence.heavySetup.degreeLoss :=
              hdegreeLoss_pos
            have h'' : 1 ≤ incidence.heavySetup.degreeLoss := by
              omega
            exact_mod_cast (by linarith)
          exact h
        have hfiberRatio_ge_one : 1 ≤ fiberRatio := by
          dsimp only [fiberRatio]
          have h1 : DeltaRep ≤ tRep := data.DeltaRep_le_tRep
          have h2 : 1 ≤ 2 * tRep / DeltaRep := by
            have h3 : 0 < DeltaRep := hDeltaRep_pos
            have h4 : DeltaRep ≤ 2 * tRep := by linarith
            calc
              1 = DeltaRep / DeltaRep := by
                field_simp [h3.ne']
                <;> ring
              _ ≤ 2 * tRep / DeltaRep := by gcongr
          have h5 : 1 ≤ Real.rpow (2 * tRep / DeltaRep) eta := by
            have h6 : (1 : ℝ) ≤ (2 * tRep / DeltaRep) := h2
            have h7 :
                Real.rpow (2 * tRep / DeltaRep) eta ≥
                  Real.rpow 1 eta :=
              Real.rpow_le_rpow (by norm_num) h6 heta_pos.le
            simpa using h7
          linarith

        have hCutoffs' :=
          hCutoffs heavyLogLoss fiberRatio epsilon eta
            hheavyLogLoss_ge_one hfiberRatio_ge_one
            hepsilon_pos heta_pos
        rcases hCutoffs' with
          ⟨hmetricCut_pos, hmetricCut_lt,
            htangencyCut_pos, htangencyCut_lt,
            hmetricIdentity, htangencyIdentity⟩

        have hmetricSmall :
            24 * heavyLogLoss *
                Real.rpow (2 * metricCut) epsilon *
                fiberRatio ≤
              1 := by
          rw [hmetricIdentity]
        have htangencySmall :
            24 * heavyLogLoss *
                Real.rpow tangencyCut eta ≤
              1 := by
          rw [htangencyIdentity]

        let rects := incidence.parentSetup.selectedRectangles index
        let sub := RectangleSubfamily.ofFinset fineSetup.fine rects
        let R := sub.family
        let coarse :=
          (selectedCoarseSubfamily coarseSetup.coarseData
            incidence.heavySetup.selectedCoarse).embedding index
        let ambient :=
          selectedCoarseIncidenceSupport coarseSetup.coarseData
            incidence.degreeSetup.selectedEdges
            incidence.heavySetup.selectedCoarse index
        let selectedFiber : Fin R.card → Finset C2Function := fun i =>
          incidenceRectangleFiber incidence.degreeSetup.selectedEdges
            (sub.embedding i)
        let q := incidence.parentSetup.pairLower index
        let I := fineSetup.pointData.interval
        let metricLower := metricCut * tRep / 8
        let tangencyLower := tangencyCut * DeltaRep / 2
        let Cc := 100
        let t := C_R * tRep * DeltaRep / delta

        have hcoarse_in_heavy :
            coarse ∈ incidence.heavySetup.heavy := by
          have h1 : coarse ∈ incidence.heavySetup.selectedCoarse :=
            selectedCoarseSubfamily_parent_mem
              coarseSetup.coarseData
              incidence.heavySetup.selectedCoarse index
          exact incidence.heavySetup.selectedCoarse_subset h1

        have hambient_subset : ambient.carrier ⊆ family := by
          have h1 :
              ambient.carrier ⊆
                (incidence.heavySetup.ambient : Set C2Function) := by
            dsimp only [ambient]
            simpa [selectedCoarseIncidenceSupport,
              incidenceSupportFamily] using
              incidence.heavySetup.support_ambient
                ((selectedCoarseSubfamily coarseSetup.coarseData
                    incidence.heavySetup.selectedCoarse).embedding index)
                hcoarse_in_heavy
          have h2 :
              (incidence.heavySetup.ambient : Set C2Function) ⊆
                data.ambientSource.carrier := by
            rw [incidence.heavySetup.ambient_eq]
            simp [FiniteFunctionFamily.toFinset,
              FiniteFunctionFamily.cluster]
            <;> tauto
          have h3 : data.ambientSource.carrier ⊆ family :=
            data.ambientSource_subset
          exact h1.trans (h2.trans h3)

        have hrects_subset_support :
            rects ⊆
              incidenceRectangleSupport
                incidence.degreeSetup.selectedEdges
                coarseSetup.coarseData.parent coarse := by
          dsimp only [rects]
          rw [incidence.parentSetup.selectedRectangles_eq index]
          exact Finset.filter_subset _ _

        have hfiber_subset_ambient :
            ∀ (i : Fin R.card),
              (selectedFiber i : Set C2Function) ⊆ ambient.carrier := by
          intro i function hfunction
          let rectangle := sub.embedding i
          have hrect : rectangle ∈ rects :=
            RectangleSubfamily.ofFinset_embedding_mem
              fineSetup.fine rects i
          have hrect_support :
              rectangle ∈
                incidenceRectangleSupport
                  incidence.degreeSetup.selectedEdges
                  coarseSetup.coarseData.parent coarse :=
            hrects_subset_support hrect
          have hparent :
              coarseSetup.coarseData.parent rectangle = coarse := by
            rcases Finset.mem_image.mp hrect_support with
              ⟨edge, hedge, h_edge_snd⟩
            have h_parent_edge :
                coarseSetup.coarseData.parent edge.2 = coarse :=
              (Finset.mem_filter.mp hedge).2
            rw [← h_edge_snd]
            exact h_parent_edge
          rcases Finset.mem_image.mp hfunction with
            ⟨edge, hedge, h_edge_fst⟩
          have h_edge_selected :
              edge ∈ incidence.degreeSetup.selectedEdges :=
            (Finset.mem_filter.mp hedge).1
          have h_edge_snd : edge.2 = rectangle :=
            (Finset.mem_filter.mp hedge).2
          have h_goal :
              edge ∈ incidence.degreeSetup.selectedEdges.filter
                (fun e =>
                  coarseSetup.coarseData.parent e.2 = coarse) := by
            rw [Finset.mem_filter]
            exact ⟨h_edge_selected, by rw [h_edge_snd, hparent]⟩
          have h_final :
              function ∈
                incidenceFunctionSupport
                  incidence.degreeSetup.selectedEdges
                  coarseSetup.coarseData.parent coarse := by
            rw [← h_edge_fst]
            exact Finset.mem_image.mpr ⟨edge, h_goal, rfl⟩
          simpa [ambient, coarse,
            selectedCoarseIncidenceSupport,
            incidenceSupportFamily] using h_final

        have htangent :
            ∀ (i : Fin R.card), ∀ function ∈ selectedFiber i,
              (R.rectangle i).IsLambdaTangent function 5 := by
          intro i function hfunction
          let rectangle := sub.embedding i
          have h1 :
              function ∈
                (incidence.degreeSetup.fiber rectangle).toFinset :=
            have h_selected_on :
                incidence.degreeSetup.selectedEdges ⊆
                  fineFiberIncidenceEdgesOn
                    incidence.degreeSetup.retained
                    incidence.degreeSetup.fiber := by
              rw [← incidence.degreeSetup.rawEdges_eq]
              exact incidence.degreeSetup.selectedEdges_subset
            incidenceRectangleFiber_subset_fiber_on
              incidence.degreeSetup.retained
              incidence.degreeSetup.fiber
              incidence.degreeSetup.selectedEdges h_selected_on
              rectangle hfunction
          have h2 :
              function ∈
                (incidence.degreeSetup.fiber rectangle).carrier := by
            simpa [FiniteFunctionFamily.toFinset] using h1
          have h3 :
              function ∈
                (fineSetup.pointData.fiber
                  (fineSetup.source rectangle)).carrier := by
            rw [incidence.degreeSetup.fiber_eq] at h2
            exact h2
          have h4 :
              (fineSetup.pointData.rectangle
                (fineSetup.source rectangle)).IsLambdaTangent
                  function 5 :=
            fineSetup.pointData.fiber_tangent
              (fineSetup.source rectangle) function h3
          have h5 :
              fineSetup.fine.rectangle rectangle =
                fineSetup.pointData.rectangle
                  (fineSetup.source rectangle) :=
            fineSetup.fine_source rectangle
          have h6 :
              (fineSetup.fine.rectangle rectangle).IsLambdaTangent
                function 5 := by
            rw [h5]
            exact h4
          exact h6

        have hgood :
            ∀ (i : Fin R.card),
              (selectedFiber i).card ^ 2 ≤
                3 * (((selectedFiber i).product
                  (selectedFiber i)).filter fun pair =>
                    metricLower < c2Distance pair.2 pair.1 ∧
                    tangencyLower ≤
                      tangencyParameterOn I pair.2 pair.1 + delta).card := by
          intro i
          let p' := fineSetup.source (sub.embedding i)
          let p : E := ⟨p'.val, p'.property.1⟩
          have hselected_subset :
              (selectedFiber i : Set C2Function) ⊆
                (data.assignment.fiber p).carrier := by
            have h1 :
                (selectedFiber i : Set C2Function) ⊆
                  (incidence.degreeSetup.fiber
                    (sub.embedding i)).carrier := by
              have h2 :=
                incidence.parentSetup.selected_fiber_subset_original
                  (sub.embedding i)
              simpa [FiniteFunctionFamily.toFinset] using h2
            rw [incidence.degreeSetup.fiber_eq] at h1
            have h3 :
                (fineSetup.pointData.fiber
                    (fineSetup.source (sub.embedding i))).carrier =
                  (data.assignment.fiber p).carrier := by
              rw [fineSetup.pointData_fiber]
              <;> rfl
            rw [h3] at h1
            exact h1

          have hrect_in : sub.embedding i ∈ rects :=
            RectangleSubfamily.ofFinset_embedding_mem
              fineSetup.fine rects i
          have hrect_retained :
              sub.embedding i ∈ incidence.degreeSetup.retained :=
            incidence.parentSetup.selectedRectangles_subset_retained
              index hrect_in

          have hmetricFiber :
              ((data.metricFiber p).card : ℝ) ≤
                fiberRatio * (incidence.q_fiber : ℝ) := by
            have h :=
              incidence.retained_metric_bound
                (sub.embedding i) hrect_retained
            have h_eq :
                (ambientRestrictedData data center hE).metricFiber p' =
                  data.metricFiber p := by
              simp [ambientRestrictedData, p]
              <;> rfl
            rw [h_eq] at h
            rw [incidence.metricBound_eq] at h
            exact h

          have hassignmentFiber :
              ((data.assignment.fiber p).card : ℝ) ≤
                2 * (incidence.q_fiber : ℝ) := by
            have h_range :=
              incidence.retained_fiber_range
                (sub.embedding i) hrect_retained
            have h :
                ((incidence.degreeSetup.fiber
                  (sub.embedding i)).card : ℝ) ≤
                  incidence.fiberBound :=
              h_range.2
            have h_fiber_eq :
                (incidence.degreeSetup.fiber
                    (sub.embedding i)).carrier =
                  (data.assignment.fiber p).carrier := by
              have h1 :
                  incidence.degreeSetup.fiber (sub.embedding i) =
                    fineSetup.pointData.fiber
                      (fineSetup.source (sub.embedding i)) := by
                rw [incidence.degreeSetup.fiber_eq]
                <;> rfl
              rw [h1]
              have h2 :
                  fineSetup.pointData.fiber
                      (fineSetup.source (sub.embedding i)) =
                    (ambientRestrictedData data center hE).assignment.fiber
                      (fineSetup.source (sub.embedding i)) :=
                fineSetup.pointData_fiber
                  (fineSetup.source (sub.embedding i))
              rw [h2]
              <;> rfl
            have h_card :
                (incidence.degreeSetup.fiber
                    (sub.embedding i)).card =
                  (data.assignment.fiber p).card := by
              simp only [FiniteFunctionFamily.card, h_fiber_eq]
            rw [h_card] at h
            rw [incidence.fiberBound_eq] at h
            exact h

          have hmetricScale' :
              delta / data.exactT p < metricCut := by
            have h := hmetricScale p'
            have h_eq :
                (ambientRestrictedData data center hE).exactT p' =
                  data.exactT p := by
              simp [ambientRestrictedData, p]
              <;> rfl
            rw [h_eq] at h
            exact h

          have htangencyScale' :
              delta / data.exactDelta p < tangencyCut := by
            have h := htangencyScale p'
            have h_eq :
                (ambientRestrictedData data center hE).exactDelta p' =
                  data.exactDelta p := by
              simp [ambientRestrictedData, p]
              <;> rfl
            rw [h_eq] at h
            exact h

          have hI_eq : I = data.interval := by
            have h1 : I = fineSetup.pointData.interval := by rfl
            have h2 :
                fineSetup.pointData.interval =
                  (ambientRestrictedData data center hE).assignment.interval :=
              fineSetup.pointData_interval
            have h3 :
                (ambientRestrictedData data center hE).assignment.interval =
                  (ambientRestrictedData data center hE).interval :=
              (ambientRestrictedData data center hE).assignment_interval
            have h4 :
                (ambientRestrictedData data center hE).interval =
                  data.interval := by
              rfl
            rw [h1, h2, h3, h4]

          set qf := incidence.q_fiber with hqf_def
          set qval := (q : ℕ) with hqval_def
          set s := ((selectedFiber i).card : ℕ) with hs_def

          have hq_lower :
              (qf : ℝ) ≤ 2 * heavyLogLoss * (qval : ℝ) :=
            incidence.parentSetup.q_fiber_le_pairLower index

          have hq_le_s : qval ≤ s := by
            have h :
                incidence.parentSetup.pairLower index ≤
                  (selectedFiber i).card :=
              incidence.parentSetup.selected_fiber_lower index
                (sub.embedding i) hrect_in
            exact_mod_cast h

          have hmetricBadScale_nonneg :
              0 ≤ Real.rpow (2 * metricCut) epsilon :=
            Real.rpow_nonneg (by positivity) _
          have htangencyBadScale_nonneg :
              0 ≤ Real.rpow tangencyCut eta :=
            Real.rpow_nonneg (by positivity) _
          have hfiberRatio_nonneg : 0 ≤ fiberRatio := by
            linarith [hfiberRatio_ge_one]
          have hheavyLogLoss_nonneg : 0 ≤ heavyLogLoss := by
            linarith [hheavyLogLoss_ge_one]

          have hbudgets :=
            selected_incidence_fiber_good_pair_budgets_of_joint_scales
              qf qval s
              (data.metricFiber p).card
              (data.assignment.fiber p).card
              heavyLogLoss fiberRatio
              (Real.rpow (2 * metricCut) epsilon)
              (Real.rpow tangencyCut eta)
              hheavyLogLoss_nonneg hfiberRatio_nonneg
              hmetricBadScale_nonneg htangencyBadScale_nonneg
              hq_lower hq_le_s
              hmetricFiber hassignmentFiber
              hmetricSmall htangencySmall

          have h_metric_budget :
              12 * Real.rpow (2 * metricCut) epsilon *
                  ((data.metricFiber p).card : ℝ) ≤
                (s : ℝ) :=
            hbudgets.1
          have h_tangency_budget :
              6 * Real.rpow tangencyCut eta *
                  ((data.assignment.fiber p).card : ℝ) ≤
                (s : ℝ) :=
            hbudgets.2

          have hresult :=
            hGoodPairs good_pair_counting hdelta data p
              (selectedFiber i) hselected_subset
              metricCut tangencyCut
              hmetricCut_pos hmetricCut_lt hmetricScale'
              htangencyCut_pos htangencyCut_lt htangencyScale'
              h_metric_budget h_tangency_budget
          simpa [hI_eq.symm, metricLower, tangencyLower] using hresult

        have ht_pos : 0 < t := by
          dsimp only [t]
          exact
            div_pos
              (mul_pos (mul_pos hC_R data.tRep_pos) hDeltaRep_pos)
              hdelta
        have hmetricLower_pos : 0 < metricLower := by
          dsimp only [metricLower]
          exact
            div_pos (mul_pos hmetricCut_pos data.tRep_pos)
              (by norm_num)
        have htangencyLower_pos : 0 < tangencyLower := by
          dsimp only [tangencyLower]
          exact
            div_pos (mul_pos htangencyCut_pos hDeltaRep_pos)
              (by norm_num)

        have h_final :=
          hC_inc
            (delta := delta) (t := t)
            (metricLower := metricLower)
            (tangencyLower := tangencyLower)
            (Cc := Cc)
            hdelta ht_pos hmetricLower_pos htangencyLower_pos
            hsmall (by norm_num) hCc_delta
            hFamily
            fineSetup.pointData.intervalControlled
            R
            (RectangleSubfamily.overCentralQuarter_transfer
              sub fineSetup.fine_central)
            (RectangleSubfamily.ofFinset_incomparable
              fineSetup.fine_incomparable rects)
            ambient hambient_subset selectedFiber
            hfiber_subset_ambient htangent q
            (incidence.parentSetup.pairLower_pos index)
            (fun i => by
              have hrect : sub.embedding i ∈ rects :=
                RectangleSubfamily.ofFinset_embedding_mem
                  fineSetup.fine rects i
              exact
                incidence.parentSetup.selected_fiber_lower index
                  (sub.embedding i) hrect)
            hgood
        have hR_card : R.card = rects.card := by
          have h1 : R.card = sub.card := by rfl
          rw [h1]
          exact
            RectangleSubfamily.ofFinset_card fineSetup.fine rects
        have h_final' :
            (rects.card : ℝ) * (q : ℝ) ^ 2 ≤
              3 * (ambient.card : ℝ) ^ 2 *
                (C_inc *
                    Real.sqrt
                      (delta * t /
                        (metricLower * tangencyLower)) +
                  1) := by
          have h : (R.card : ℝ) = (rects.card : ℝ) := by
            exact_mod_cast hR_card
          rw [h] at h_final
          exact h_final
        exact h_final'

end Kakeya.Cinematic
