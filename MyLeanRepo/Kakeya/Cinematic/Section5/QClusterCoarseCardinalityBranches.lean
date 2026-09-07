import MyLeanRepo.Kakeya.Cinematic.Section5.QClusterCoarseCardinalityBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.DeltaPositivity
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseScaleBounds
import MyLeanRepo.Kakeya.Cinematic.Section5.FiberwiseSeparatedTangentBallPairAt
import MyLeanRepo.Kakeya.Cinematic.Section5.SharedTangentBallPairPigeonholeAt
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountFromPairs

/-!
# The two cluster-cardinality branches
-/

noncomputable section

namespace Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _

theorem q_cluster_coarse_cardinality_branches :
    QClusterCoarseCardinalityBranchesStatement := by
  intro hRobust hNormalCount hNormalFromPairs hSingletonPair hSingletonWitness K hK
  rcases hNormalCount fiberwise_separated_tangent_ball_pair_at
      shared_tangent_ball_pair_pigeonhole_at hRobust
      normal_coarse_rectangle_count K hK with
    ⟨C_positive, hC_positive, hMainPositive⟩
  rcases hNormalFromPairs shared_tangent_ball_pair_pigeonhole_at
      hRobust normal_coarse_rectangle_count_from_pairs K hK with
    ⟨C_singleton, hC_singleton, hMainSingleton⟩
  refine' ⟨C_positive, C_singleton, hC_positive, hC_singleton, _⟩
  intro family E D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement degreeSetup
    q_fiber fiberBound heavySetup ballCoefficient radius A
    nonconcentration cover hfamily hballCoefficient hradius hA hEq hdelta_le_A

  let R := (selectedCoarseSubfamily coarseSetup.coarseData heavySetup.selectedCoarse).family
  let H := data.ambientSource.cluster center (3 * tRep)
  let T := selectedCoarseIncidenceSupport coarseSetup.coarseData degreeSetup.selectedEdges heavySetup.selectedCoarse
  let centers := cover.centers
  let support := 2 ^ heavySetup.supportLevel
  let tangency := coarseSetup.tangency
  let t_coarse := C_R * tRep
  let I := (ambientRestrictedData data center hE).interval

  have hdelta_pos : 0 < delta := fine_delta_pos fineSetup
  have hDeltaRep_pos : 0 < DeltaRep := hdelta_pos.trans_le data.delta_le_DeltaRep

  have hCurv : HasCinematicCurvature family K :=
    ⟨hfamily.1, hfamily.2.2⟩
  have hIControlled : I.IsControlled K := by
    have h1 : fineSetup.pointData.interval = (ambientRestrictedData data center hE).assignment.interval :=
      fineSetup.pointData_interval
    have h2 : (ambientRestrictedData data center hE).assignment.interval = I :=
      (ambientRestrictedData data center hE).assignment_interval
    have h3 : fineSetup.pointData.interval.IsControlled K :=
      fineSetup.pointData.intervalControlled
    rw [h1, h2] at h3
    exact h3

  have hA_ne : A ≠ 0 := by linarith
  have ht_coarse_pos : 0 < t_coarse := by
    have h : C_R * tRep = 8 * radius * A := by
      field_simp [hA_ne] at hEq ⊢ <;> linarith
    have h' : 0 < 8 * radius * A := by positivity
    linarith
  have hC_R_pos : 0 < C_R := by
    by_contra h
    have h' : C_R ≤ 0 := by linarith
    have h'' : C_R * tRep ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg h' (by linarith [data.tRep_pos])
    linarith [ht_coarse_pos]
  have htangency : 5 ≤ tangency := coarseSetup.tangency_ge_five
  have hdelta_le_t : DeltaRep ≤ t_coarse :=
    coarse_DeltaRep_le_C_R_tRep coarseSetup ht_coarse_pos
  have hEq' : t_coarse / A = 8 * radius := hEq

  have hselected : degreeSetup.selectedEdges ⊆
      fineFiberIncidenceEdgesOn degreeSetup.retained degreeSetup.fiber := by
    have h := degreeSetup.selectedEdges_subset
    rw [degreeSetup.rawEdges_eq] at h
    exact h
  have hall : ∀ (coarse : Fin coarseSetup.coarseData.coarse.card),
      ∀ (function : C2Function), function ∈ (coarseTangentFamily coarseSetup.coarseData degreeSetup.fiber coarse).carrier →
        (coarseSetup.coarseData.coarse.rectangle coarse).IsLambdaTangent function tangency := by
    intro coarse function hfunction
    have hfunction' : function ∈
        (coarseTangentFamily coarseSetup.coarseData
          (fun i => fineSetup.pointData.fiber (fineSetup.source i)) coarse).carrier := by
      simpa [degreeSetup.fiber_eq] using hfunction
    exact coarseSetup.coarse_tangent coarse function hfunction'
  have hR_centers : R.CentersIn family :=
    selectedCoarseSubfamily_centers coarseSetup.coarseData heavySetup.selectedCoarse
  have hR_central : R.IsOverCentralQuarterOf I :=
    selectedCoarseSubfamily_central coarseSetup.coarseData heavySetup.selectedCoarse
  have hR_incomp : R.IsPairwiseIncomparable family 100 :=
    selectedCoarseSubfamily_incomparable coarseSetup.coarseData heavySetup.selectedCoarse
  have hR_nonempty : R.Nonempty :=
    selectedCoarseSubfamily_nonempty coarseSetup.coarseData heavySetup.selectedCoarse_nonempty
  have hR_card : R.card = heavySetup.selectedCoarse.card :=
    selectedCoarseSubfamily_card coarseSetup.coarseData heavySetup.selectedCoarse
  have htangentCount_eq : ∀ (i : Fin R.card),
      RectangleFamily.tangentCount (R.rectangle i) (T i) tangency = (T i).card := by
    intro i
    exact selectedCoarseIncidenceSupport_tangentCount
      coarseSetup.coarseData degreeSetup.retained degreeSetup.fiber
      degreeSetup.selectedEdges hselected heavySetup.selectedCoarse hall i
  have hsupport_card_lower : ∀ (i : Fin R.card), support ≤ (T i).card := by
    intro i
    have h := selectedCoarseIncidenceSupport_card_range
      coarseSetup.coarseData degreeSetup.selectedEdges heavySetup.selectedCoarse
      heavySetup.support_range i
    exact h.1

  have hambient_eq : (heavySetup.ambient : Set C2Function) = H.carrier := by
    rw [heavySetup.ambient_eq]
    exact H.finite.coe_toFinset
  have hambient_card_eq : heavySetup.ambient.card = H.card := by
    rw [heavySetup.ambient_eq]
    have h : (H.toFinset : Set C2Function) = H.carrier := H.finite.coe_toFinset
    have h' : H.toFinset.card = H.carrier.ncard := by
      have h_coe : (H.toFinset : Set C2Function) = H.carrier := H.finite.coe_toFinset
      have h_card : H.toFinset.card = (H.toFinset : Set C2Function).ncard := by
        simp
      rw [h_card, h_coe]
    simpa [FiniteFunctionFamily.card] using h'

  have hsupport_ambient_set : ∀ coarse ∈ heavySetup.selectedCoarse,
      (incidenceFunctionSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent coarse : Set C2Function) ⊆ H.carrier := by
    intro coarse hcoarse
    have h1 : incidenceFunctionSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent coarse ⊆ heavySetup.ambient :=
      heavySetup.support_ambient coarse (heavySetup.selectedCoarse_subset hcoarse)
    have h2 : (incidenceFunctionSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent coarse : Set C2Function) ⊆ (heavySetup.ambient : Set C2Function) :=
      Finset.coe_subset.mp h1
    rw [hambient_eq] at h2
    exact h2
  have hT_sub : ∀ (i : Fin R.card), (T i).carrier ⊆ H.carrier := by
    intro i
    exact selectedCoarseIncidenceSupport_subset
      coarseSetup.coarseData degreeSetup.selectedEdges
      heavySetup.selectedCoarse H hsupport_ambient_set i
  have hT_nonempty : ∀ (i : Fin R.card), (T i).carrier.Nonempty := by
    intro i
    have h : 0 < (T i).card := by
      have h' : support ≤ (T i).card := hsupport_card_lower i
      have h_sup_pos : 0 < support := by positivity
      exact h_sup_pos.trans_le h'
    by_contra h3
    have h4 : (T i).carrier = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h3
    have h5 : (T i).card = 0 := by
      simp only [FiniteFunctionFamily.card, h4, Set.ncard_empty]
    rw [h5] at h
    <;> linarith
  have hH_nonempty : H.carrier.Nonempty := by
    let i : Fin R.card := Classical.choice (Fin.pos_iff_nonempty.mp hR_nonempty)
    rcases hT_nonempty i with ⟨f, hf⟩
    have h2 : f ∈ H.carrier := hT_sub i hf
    exact ⟨f, h2⟩
  have hH_card_pos : 0 < H.card := by
    have h : H.carrier.Nonempty := hH_nonempty
    exact (Set.ncard_pos H.finite).mpr h
  have hsupport_le_ambient : support ≤ H.card := by
    have h1 : heavySetup.supportLevel ≤ Nat.log2 heavySetup.ambient.card :=
      heavySetup.supportLevel_bound
    rw [hambient_card_eq] at h1
    have h2 : 2 ^ heavySetup.supportLevel ≤ 2 ^ Nat.log2 H.card := by
      have h_pow : ∀ (a b : ℕ), a ≤ b → 2 ^ a ≤ 2 ^ b := by
        intro a b h
        induction' h with b h ih
        · simp
        · simp [pow_succ] at * <;> omega
      exact h_pow heavySetup.supportLevel (Nat.log2 H.card) h1
    have h3 : 2 ^ Nat.log2 H.card ≤ H.card := by
      by_cases hH : H.card = 0
      · rw [hH] at h1 <;> simp at h1 <;> omega
      · have h4 : 2 ^ Nat.log2 H.card ≤ H.card := (Nat.le_log2 hH).mp le_rfl
        exact h4
    exact h2.trans h3
  have hcover : ∀ (i : Fin R.card), (T i).carrier ⊆ ⋃ c ∈ centers, c2Ball c radius :=
    cover.selected_support_cover
  have hcenters_nonempty : centers.Nonempty := cover.centers_nonempty
  have hcenters_pos : 0 < centers.card :=
    Finset.card_pos.mpr hcenters_nonempty
  have hcluster_half : ∀ (i : Fin R.card), ∀ c ∈ centers,
      2 * RectangleFamily.tangentCount (R.rectangle i) ((T i).cluster c (11 * radius)) tangency ≤
        RectangleFamily.tangentCount (R.rectangle i) (T i) tangency := by
    intro i c _
    exact nonconcentration.cluster_tangent_half hballCoefficient i c
  have htangent_prop : ∀ (i : Fin R.card),
      ∀ function ∈ (T i).carrier, (R.rectangle i).IsLambdaTangent function tangency := by
    intro i
    exact selectedCoarseIncidenceSupport_tangent
      coarseSetup.coarseData degreeSetup.retained degreeSetup.fiber
      degreeSetup.selectedEdges hselected heavySetup.selectedCoarse hall i
  have hH_sub : H.carrier ⊆ family :=
    Set.inter_subset_left.trans data.ambientSource_subset
  have hH_diam : ∀ f ∈ H.carrier, ∀ g ∈ H.carrier, dist f g ≤ 6 * t_coarse :=
    fineSetup.fixed_ambient_diameter
  have hsupport_pos : 0 < support := by positivity
  have hDeltaRep_le_A : DeltaRep ≤ A * t_coarse := by
    calc
      DeltaRep ≤ t_coarse := hdelta_le_t
      _ ≤ A * t_coarse := by
        have h : 1 ≤ A := hA
        have h' : 0 ≤ t_coarse := by positivity
        nlinarith

  by_cases hpos : 2 * centers.card ≤ support
  · rcases exists_positive_cluster_lower centers.card support hcenters_pos hpos with
      ⟨q_cluster, hq_pos, hlower, hupper⟩
    have h_tangent_lower : ∀ (i : Fin R.card),
        2 * centers.card * q_cluster ≤
          RectangleFamily.tangentCount (R.rectangle i) (T i) tangency := by
      intro i
      have h1 : 2 * centers.card * q_cluster ≤ support := hlower
      have h2 : support ≤ (T i).card := hsupport_card_lower i
      have h3 : RectangleFamily.tangentCount (R.rectangle i) (T i) tangency = (T i).card :=
        htangentCount_eq i
      rw [h3] <;> omega
    rcases hMainPositive hCurv hIControlled hDeltaRep_pos ht_coarse_pos hdelta_le_t
        hradius htangency hA hEq' hDeltaRep_le_A
        H hH_sub hH_diam R hR_centers hR_central hR_incomp hR_nonempty
        T hT_sub centers hcenters_nonempty hcover
        q_cluster hq_pos h_tangent_lower hcluster_half with
      ⟨c, hc_in, d, hd_in, h_sep, S, hS_nonempty, hS_tangent, hS_card⟩
    have hnormalized : 2 ≤ RectangleFamily.bipartiteNormalizedCount
          (H.cluster c radius) (H.cluster d radius) q_cluster q_cluster :=
        RectangleFamily.two_le_bipartiteNormalizedCount_of_tangentCounts
      hS_nonempty hq_pos hq_pos hS_tangent
    let coefficient : ℝ := C_positive * Real.rpow tangency C_positive * Real.rpow A C_positive
    have hcoeff_nonneg : 0 ≤ coefficient := by
      dsimp only [coefficient]
      have h1 : 0 ≤ C_positive := by linarith
      have htang_pos : 0 < tangency := by linarith
      have hA_pos : 0 < A := by linarith
      have h2 : 0 ≤ Real.rpow tangency C_positive := Real.rpow_nonneg htang_pos.le _
      have h3 : 0 ≤ Real.rpow A C_positive := Real.rpow_nonneg hA_pos.le _
      positivity
    have hS_card' : (R.card : ℝ) ≤
        (centers.card : ℝ) ^ 2 * coefficient *
          Real.rpow (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) q_cluster q_cluster) (3 / 2 : ℝ) *
        Real.log (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) q_cluster q_cluster) := by
      have h_coeff : C_positive * Real.rpow tangency C_positive * Real.rpow A C_positive = coefficient := by
        simp [coefficient] <;> ring
      rw [h_coeff] at hS_card
      simpa [mul_assoc] using hS_card
    have h_final' : (R.card : ℝ) ≤
        (centers.card : ℝ) ^ 2 * coefficient *
          Real.rpow (8 * (centers.card : ℝ) * (H.card : ℝ)) (3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          Real.log (8 * (centers.card : ℝ) * (H.card : ℝ) / (support : ℝ)) :=
      normal_coarse_card_bound_with_support_decay
        H c d radius q_cluster centers.card support R.card
        coefficient hq_pos hcenters_pos hsupport_pos hupper hnormalized hS_card' hcoeff_nonneg
    have h_main : (heavySetup.selectedCoarse.card : ℝ) ≤
        (centers.card : ℝ) ^ 2 * coefficient *
          Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          (Real.rpow (8 * (centers.card : ℝ) * (H.card : ℝ)) (3 / 2 : ℝ) *
            Real.log (8 * (centers.card : ℝ) * (H.card : ℝ) / (support : ℝ))) := by
      have hRcard : (R.card : ℝ) = (heavySetup.selectedCoarse.card : ℝ) := by
        exact_mod_cast hR_card
      rw [hRcard] at h_final'
      have h_eq : (centers.card : ℝ) ^ 2 * coefficient *
          Real.rpow (8 * (centers.card : ℝ) * (H.card : ℝ)) (3 / 2 : ℝ) *
          Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          Real.log (8 * (centers.card : ℝ) * (H.card : ℝ) / (support : ℝ)) =
        (centers.card : ℝ) ^ 2 * coefficient *
          Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
          (Real.rpow (8 * (centers.card : ℝ) * (H.card : ℝ)) (3 / 2 : ℝ) *
            Real.log (8 * (centers.card : ℝ) * (H.card : ℝ) / (support : ℝ))) := by ring
      rw [h_eq] at h_final'
      exact h_final'
    exact QClusterCoarseCardinalityResult.positive h_main

  · have hsmall : support < 2 * centers.card := by omega
    have hPairs : ∀ (i : Fin R.card),
        ∃ c ∈ centers, ∃ d ∈ centers,
          10 * radius ≤ c2Distance c d ∧
          1 ≤ RectangleFamily.tangentCount (R.rectangle i) (H.cluster c radius) tangency ∧
          1 ≤ RectangleFamily.tangentCount (R.rectangle i) (H.cluster d radius) tangency ∧
          (H.cluster c radius).AreSeparated (H.cluster d radius) (8 * radius) :=
      hSingletonPair (r := radius) hradius H R T hT_sub centers hcenters_nonempty
        hcover hT_nonempty htangent_prop hcluster_half
    rcases hMainSingleton hCurv hIControlled hDeltaRep_pos ht_coarse_pos hdelta_le_t
        hradius htangency hA hEq' hDeltaRep_le_A
        H hH_sub hH_diam R hR_centers hR_central hR_incomp hR_nonempty
        centers hcenters_nonempty 1 (by norm_num) hPairs with
      ⟨c, hc_in, d, hd_in, h_sep, S, hS_nonempty, hS_tangent, hS_card⟩
    let coefficient : ℝ :=
      (centers.card : ℝ) ^ 2 *
        (C_singleton * Real.rpow tangency C_singleton * Real.rpow A C_singleton)
    have hcoeff_nonneg : 0 ≤ coefficient := by
      dsimp only [coefficient]
      have h1 : 0 ≤ (centers.card : ℝ) ^ 2 := by positivity
      have h2 : 0 ≤ C_singleton := by linarith
      have h3 : 0 ≤ Real.rpow tangency C_singleton := Real.rpow_nonneg (by linarith) _
      have h4 : 0 ≤ Real.rpow A C_singleton := Real.rpow_nonneg (by linarith) _
      positivity
    have hS_card' : (R.card : ℝ) ≤
        coefficient * (Real.rpow (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) 1 1) (3 / 2 : ℝ) *
          Real.log (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) 1 1)) := by
      have h_eq : (centers.card : ℝ) ^ 2 *
          (C_singleton * Real.rpow tangency C_singleton * Real.rpow A C_singleton *
            Real.rpow (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) 1 1) (3 / 2 : ℝ) *
            Real.log (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) 1 1)) =
        coefficient * (Real.rpow (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) 1 1) (3 / 2 : ℝ) *
          Real.log (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c radius) (H.cluster d radius) 1 1)) := by
        simp [coefficient] <;> ring
      rw [h_eq] at hS_card
      exact hS_card
    have h_final' : (R.card : ℝ) ≤
        coefficient * (Real.rpow (2 * (H.card : ℝ)) (3 / 2 : ℝ) * Real.log (2 * (H.card : ℝ))) :=
      hSingletonWitness (delta := DeltaRep) (t := t_coarse) S.family R.card H c d radius
        tangency coefficient hS_nonempty hS_tangent hcoeff_nonneg hS_card'
    have h_final : (heavySetup.selectedCoarse.card : ℝ) ≤
        coefficient * (Real.rpow (2 * (H.card : ℝ)) (3 / 2 : ℝ) * Real.log (2 * (H.card : ℝ))) := by
      have hRcard : (R.card : ℝ) = (heavySetup.selectedCoarse.card : ℝ) := by
        exact_mod_cast hR_card
      rw [hRcard] at h_final'
      exact h_final'
    exact QClusterCoarseCardinalityResult.singleton hsmall h_final

end Kakeya.Cinematic
