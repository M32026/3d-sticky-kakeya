import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedCardinalityBranchesInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalSelectedTotalCardinality
import MyLeanRepo.Kakeya.Cinematic.Section5.SmallSupportTotalCardinality

/-!
# Selected fine-cardinality branches inside one ambient bin
-/

noncomputable section

namespace Kakeya.Cinematic

local instance ambientRestrictedSelectedCardinalityBranchesProofDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem ambient_restricted_selected_cardinality_branches :
    AmbientRestrictedSelectedCardinalityBranchesStatement := by
  intro hInterpolate hNormal hSmall
  intro family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
  intro data center hE C_R C_count C_shading C_volume
  intro fineSetup coarseSetup massExponent refinement degreeSetup
    q_fiber fiberBound heavySetup radius A cover
  intro C_positive C_singleton retention measureScale tangencyScale
  intro hq hA hCpos hCsing hfiberBound hretention hmeasureScale
    htangencyScale
  intro hfiberScale hqRetention hfiberLower hMmeasure hMtangency hQ
  set M : ℕ := heavySetup.M_parent with hM_def
  set support : ℕ := 2 ^ heavySetup.supportLevel with hsupport_def
  set centers : ℕ := cover.centers.card with hcenters_def
  set ambientCard : ℕ :=
    (data.ambientSource.cluster center (3 * tRep)).card
      with hambientCard_def
  set parentLoss : ℝ :=
    ↑(Nat.log2 refinement.selected.card + 1)
      with hparentLoss_def
  set degreeLoss : ℝ :=
    ↑heavySetup.degreeLoss with hdegreeLoss_def
  set supportLoss : ℝ :=
    ↑(Nat.log2 heavySetup.ambient.card + 1)
      with hsupportLoss_def
  have hM_pos : 0 < M := by
    rw [hM_def, heavySetup.M_parent_eq]
    positivity
  have hmu_pos : 0 < data.mu := data.mu_pos
  have hsupport_pos : 0 < support := by
    rw [hsupport_def]
    positivity
  have hcenters_pos : 0 < centers := by
    rw [hcenters_def]
    exact Finset.card_pos.mpr cover.centers_nonempty
  have hparentLoss_nonneg : 0 ≤ parentLoss := by
    rw [hparentLoss_def]
    positivity
  have hdegreeLoss_nonneg : 0 ≤ degreeLoss := by
    rw [hdegreeLoss_def]
    positivity
  have hsupportLoss_nonneg : 0 ≤ supportLoss := by
    rw [hsupportLoss_def]
    positivity
  have hambientCard_pos : 0 < ambientCard := by
    rcases heavySetup.selectedCoarse_nonempty with
      ⟨coarse, hcoarse⟩
    have hcoarse_heavy : coarse ∈ heavySetup.heavy :=
      heavySetup.selectedCoarse_subset hcoarse
    have hrange := heavySetup.support_range coarse hcoarse
    have hsupport_card_pos :
        0 < (incidenceFunctionSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).card := by
      omega
    have hsupport_nonempty :
        (incidenceFunctionSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).Nonempty :=
      Finset.card_pos.mp hsupport_card_pos
    rcases hsupport_nonempty with ⟨function, hfunction⟩
    have hfunction_ambient :
        function ∈ heavySetup.ambient :=
      heavySetup.support_ambient
        coarse hcoarse_heavy hfunction
    have hambient_nonempty : heavySetup.ambient.Nonempty :=
      ⟨function, hfunction_ambient⟩
    have h : 0 < heavySetup.ambient.card :=
      Finset.card_pos.mpr hambient_nonempty
    have h2 : heavySetup.ambient.card = ambientCard := by
      rw [heavySetup.ambient_eq, hambientCard_def]
      exact
        (Set.ncard_eq_toFinset_card _
          (data.ambientSource.cluster
            center (3 * tRep)).finite).symm
    rw [h2] at h
    exact h
  have horiginal :
      (refinement.selected.card : ℝ) ≤
        parentLoss * (degreeSetup.retained.card : ℝ) := by
    have h :
        refinement.selected.card ≤
          (Nat.log2 refinement.selected.card + 1) *
            degreeSetup.retained.card := by
      rw [degreeSetup.retained_eq]
      exact refinement.parent_retention
    have h' :
        (refinement.selected.card : ℝ) ≤
          ((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ) *
            (degreeSetup.retained.card : ℝ) := by
      exact_mod_cast h
    simpa [hparentLoss_def] using h'
  have hrawLower :
      (degreeSetup.retained.card : ℝ) * (q_fiber : ℝ) ≤
        (degreeSetup.rawEdges.card : ℝ) := by
    have h :
        degreeSetup.retained.card * q_fiber ≤
          (fineFiberIncidenceEdgesOn
            degreeSetup.retained degreeSetup.fiber).card :=
      card_mul_le_fineFiberIncidenceEdgesOn
        degreeSetup.retained degreeSetup.fiber
        q_fiber hfiberLower
    have h' :
        degreeSetup.retained.card * q_fiber ≤
          degreeSetup.rawEdges.card := by
      simpa [degreeSetup.rawEdges_eq] using h
    exact_mod_cast h'
  have hedgeRetention :
      (degreeSetup.rawEdges.card : ℝ) ≤
        degreeLoss * (degreeSetup.selectedEdges.card : ℝ) := by
    have h :
        degreeSetup.rawEdges.card ≤
          heavySetup.degreeLoss *
            degreeSetup.selectedEdges.card := by
      rw [heavySetup.degreeLoss_eq]
      exact degreeSetup.degree_retention
    have h' :
        (degreeSetup.rawEdges.card : ℝ) ≤
          (heavySetup.degreeLoss : ℝ) *
            (degreeSetup.selectedEdges.card : ℝ) := by
      exact_mod_cast h
    simpa [hdegreeLoss_def] using h'
  have hheavyLower :
      ((degreeSetup.selectedEdges.card : ℝ) / 2) /
          ((2 * (M : ℝ)) * fiberBound) ≤
        (heavySetup.heavy.card : ℝ) := by
    have h := heavySetup.heavy_lower
    rw [heavySetup.rectangleBound_eq] at h
    simpa [hM_def, heavySetup.M_parent_eq] using h
  have hsupportRetention :
      (heavySetup.heavy.card : ℝ) ≤
        supportLoss *
          (heavySetup.selectedCoarse.card : ℝ) := by
    have h :
        heavySetup.heavy.card ≤
          (Nat.log2 heavySetup.ambient.card + 1) *
            heavySetup.selectedCoarse.card :=
      heavySetup.support_retention
    have h' :
        (heavySetup.heavy.card : ℝ) ≤
          ((Nat.log2 heavySetup.ambient.card + 1 : ℕ) : ℝ) *
            (heavySetup.selectedCoarse.card : ℝ) := by
      exact_mod_cast h
    simpa [hsupportLoss_def] using h'
  cases hQ with
  | positive hcoarseBound =>
      set coefficient : ℝ :=
        (centers : ℝ) ^ 2 *
          (C_positive *
            Real.rpow coarseSetup.tangency C_positive *
            Real.rpow A C_positive)
          with hcoefficient_def
      set tail : ℝ :=
        Real.rpow
            (8 * (centers : ℝ) * (ambientCard : ℝ))
            (3 / 2 : ℝ) *
          Real.log
            (8 * (centers : ℝ) * (ambientCard : ℝ) /
              (support : ℝ))
          with htail_def
      have htangency_pos : 0 < coarseSetup.tangency := by
        linarith [coarseSetup.tangency_ge_five]
      have hcoefficient_pos : 0 < coefficient := by
        rw [hcoefficient_def]
        have h1 : 0 < (centers : ℝ) := by
          exact_mod_cast hcenters_pos
        have h2 : 0 < C_positive := by
          linarith
        have h3 :
            0 < Real.rpow coarseSetup.tangency C_positive :=
          Real.rpow_pos_of_pos htangency_pos C_positive
        have h4 : 0 < Real.rpow A C_positive :=
          Real.rpow_pos_of_pos (by linarith) C_positive
        positivity
      have hrpow_support_pos :
          0 < Real.rpow (support : ℝ) (-3 / 2 : ℝ) :=
        Real.rpow_pos_of_pos
          (by exact_mod_cast hsupport_pos) _
      have htail_nonneg : 0 ≤ tail := by
        have hselected_pos :
            0 < (heavySetup.selectedCoarse.card : ℝ) :=
          Nat.cast_pos.mpr
            (Finset.card_pos.mpr
              heavySetup.selectedCoarse_nonempty)
        have hprod_pos :
            0 <
              coefficient *
                Real.rpow (support : ℝ) (-3 / 2 : ℝ) :=
          mul_pos hcoefficient_pos hrpow_support_pos
        have h :
            (heavySetup.selectedCoarse.card : ℝ) ≤
              coefficient *
                Real.rpow (support : ℝ) (-3 / 2 : ℝ) *
                tail :=
          hcoarseBound
        nlinarith
      have hmain :
          (refinement.selected.card : ℝ) ≤
            (48 * parentLoss * degreeLoss * supportLoss *
              Real.rpow retention (-1)) *
            ((Real.rpow measureScale (1 / 4 : ℝ) *
              Real.rpow tangencyScale (3 / 4 : ℝ)) *
              coefficient * tail *
              Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ)) :=
        hNormal hInterpolate
          refinement.selected.card degreeSetup.retained.card
          degreeSetup.rawEdges.card degreeSetup.selectedEdges.card
          heavySetup.heavy.card heavySetup.selectedCoarse.card
          M q_fiber data.mu support
          parentLoss degreeLoss supportLoss fiberBound retention
          measureScale tangencyScale coefficient tail
          hM_pos hq hmu_pos hsupport_pos
          hparentLoss_nonneg hdegreeLoss_nonneg
          hsupportLoss_nonneg hfiberBound hretention
          hmeasureScale htangencyScale
          (by linarith) htail_nonneg
          horiginal hrawLower hedgeRetention
          hheavyLower hsupportRetention
          hfiberScale hqRetention hMmeasure hMtangency
          hcoarseBound
      simpa [hcoefficient_def, htail_def,
        hparentLoss_def, hdegreeLoss_def,
        hsupportLoss_def, hM_def, hsupport_def,
        hcenters_def, hambientCard_def] using
        AmbientRestrictedSelectedCardinalityResult.positive hmain
  | singleton hsmall hcoarseBound =>
      set coefficient : ℝ :=
        (centers : ℝ) ^ 2 *
          (C_singleton *
            Real.rpow coarseSetup.tangency C_singleton *
            Real.rpow A C_singleton)
          with hcoefficient_def
      set tail : ℝ :=
        Real.rpow (2 * (ambientCard : ℝ)) (3 / 2 : ℝ) *
          Real.log (2 * (ambientCard : ℝ))
          with htail_def
      have htangency_pos : 0 < coarseSetup.tangency := by
        linarith [coarseSetup.tangency_ge_five]
      have hcoefficient_pos : 0 < coefficient := by
        rw [hcoefficient_def]
        have h1 : 0 < (centers : ℝ) := by
          exact_mod_cast hcenters_pos
        have h2 : 0 < C_singleton := by
          linarith
        have h3 :
            0 < Real.rpow coarseSetup.tangency C_singleton :=
          Real.rpow_pos_of_pos htangency_pos C_singleton
        have h4 : 0 < Real.rpow A C_singleton :=
          Real.rpow_pos_of_pos (by linarith) C_singleton
        positivity
      have htail_nonneg : 0 ≤ tail := by
        have hselected_pos :
            0 < (heavySetup.selectedCoarse.card : ℝ) :=
          Nat.cast_pos.mpr
            (Finset.card_pos.mpr
              heavySetup.selectedCoarse_nonempty)
        have h :
            (heavySetup.selectedCoarse.card : ℝ) ≤
              coefficient * tail :=
          hcoarseBound
        nlinarith
      have hmain :
          (refinement.selected.card : ℝ) ≤
            (48 * parentLoss * degreeLoss * supportLoss *
              Real.rpow retention (-1)) *
            ((Real.rpow measureScale (1 / 4 : ℝ) *
              Real.rpow tangencyScale (3 / 4 : ℝ)) *
              coefficient * tail *
              Real.rpow (2 * (centers : ℝ)) (3 / 2 : ℝ) *
              Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ)) :=
        hSmall hInterpolate
          refinement.selected.card degreeSetup.retained.card
          degreeSetup.rawEdges.card degreeSetup.selectedEdges.card
          heavySetup.heavy.card heavySetup.selectedCoarse.card
          M q_fiber data.mu support centers
          parentLoss degreeLoss supportLoss fiberBound retention
          measureScale tangencyScale coefficient tail
          hM_pos hq hmu_pos hsupport_pos hsmall
          hparentLoss_nonneg hdegreeLoss_nonneg
          hsupportLoss_nonneg hfiberBound hretention
          hmeasureScale htangencyScale
          (by linarith) htail_nonneg
          horiginal hrawLower hedgeRetention
          hheavyLower hsupportRetention
          hfiberScale hqRetention hMmeasure hMtangency
          hcoarseBound
      simpa [hcoefficient_def, htail_def,
        hparentLoss_def, hdegreeLoss_def,
        hsupportLoss_def, hM_def, hsupport_def,
        hcenters_def, hambientCard_def] using
        AmbientRestrictedSelectedCardinalityResult.singleton hmain

theorem ambient_restricted_selected_cardinality_branches_of_fiber :
    AmbientRestrictedSelectedCardinalityBranchesOfFiberStatement := by
  intro hInterpolate
  intro family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
  intro data center hE C_R C_count C_shading C_volume
  intro fineSetup coarseSetup massExponent refinement degreeSetup
    q_fiber fiberBound fiberCoefficient heavySetup radius A cover
  intro C_positive C_singleton retention measureScale tangencyScale
  intro hq hA hCpos hCsing hfiberBound hretention
    hfiberCoefficient hmeasureScale htangencyScale
  intro hfiberScale hqRetention hfiberLower hMmeasure hMtangency hQ
  set M : ℕ := heavySetup.M_parent with hM_def
  set support : ℕ := 2 ^ heavySetup.supportLevel with hsupport_def
  set centers : ℕ := cover.centers.card with hcenters_def
  set ambientCard : ℕ :=
    (data.ambientSource.cluster center (3 * tRep)).card
      with hambientCard_def
  set parentLoss : ℝ :=
    ↑(Nat.log2 refinement.selected.card + 1)
      with hparentLoss_def
  set degreeLoss : ℝ :=
    ↑heavySetup.degreeLoss with hdegreeLoss_def
  set supportLoss : ℝ :=
    ↑(Nat.log2 heavySetup.ambient.card + 1)
      with hsupportLoss_def
  have hM_pos : 0 < M := by
    rw [hM_def, heavySetup.M_parent_eq]
    positivity
  have hsupport_pos : 0 < support := by
    rw [hsupport_def]
    positivity
  have hcenters_pos : 0 < centers := by
    rw [hcenters_def]
    exact Finset.card_pos.mpr cover.centers_nonempty
  have hparentLoss_nonneg : 0 ≤ parentLoss := by
    rw [hparentLoss_def]
    positivity
  have hdegreeLoss_nonneg : 0 ≤ degreeLoss := by
    rw [hdegreeLoss_def]
    positivity
  have hsupportLoss_nonneg : 0 ≤ supportLoss := by
    rw [hsupportLoss_def]
    positivity
  have hambientCard_pos : 0 < ambientCard := by
    rcases heavySetup.selectedCoarse_nonempty with ⟨coarse, hcoarse⟩
    have hcoarse_heavy : coarse ∈ heavySetup.heavy :=
      heavySetup.selectedCoarse_subset hcoarse
    have hrange := heavySetup.support_range coarse hcoarse
    have hsupport_card_pos :
        0 < (incidenceFunctionSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse).card := by
      omega
    rcases Finset.card_pos.mp hsupport_card_pos with ⟨function, hfunction⟩
    have hfunction_ambient :
        function ∈ heavySetup.ambient :=
      heavySetup.support_ambient coarse hcoarse_heavy hfunction
    have h : 0 < heavySetup.ambient.card :=
      Finset.card_pos.mpr ⟨function, hfunction_ambient⟩
    have h2 : heavySetup.ambient.card = ambientCard := by
      rw [heavySetup.ambient_eq, hambientCard_def]
      exact
        (Set.ncard_eq_toFinset_card _
          (data.ambientSource.cluster
            center (3 * tRep)).finite).symm
    rw [h2] at h
    exact h
  have horiginal :
      (refinement.selected.card : ℝ) ≤
        parentLoss * (degreeSetup.retained.card : ℝ) := by
    have h :
        refinement.selected.card ≤
          (Nat.log2 refinement.selected.card + 1) *
            degreeSetup.retained.card := by
      rw [degreeSetup.retained_eq]
      exact refinement.parent_retention
    have h' :
        (refinement.selected.card : ℝ) ≤
          ((Nat.log2 refinement.selected.card + 1 : ℕ) : ℝ) *
            (degreeSetup.retained.card : ℝ) := by
      exact_mod_cast h
    simpa [hparentLoss_def] using h'
  have hrawLower :
      (degreeSetup.retained.card : ℝ) * (q_fiber : ℝ) ≤
        (degreeSetup.rawEdges.card : ℝ) := by
    have h :
        degreeSetup.retained.card * q_fiber ≤
          (fineFiberIncidenceEdgesOn
            degreeSetup.retained degreeSetup.fiber).card :=
      card_mul_le_fineFiberIncidenceEdgesOn
        degreeSetup.retained degreeSetup.fiber q_fiber hfiberLower
    rw [← degreeSetup.rawEdges_eq] at h
    exact_mod_cast h
  have hedgeRetention :
      (degreeSetup.rawEdges.card : ℝ) ≤
        degreeLoss * (degreeSetup.selectedEdges.card : ℝ) := by
    have h :
        degreeSetup.rawEdges.card ≤
          heavySetup.degreeLoss * degreeSetup.selectedEdges.card := by
      rw [heavySetup.degreeLoss_eq]
      exact degreeSetup.degree_retention
    have h' :
        (degreeSetup.rawEdges.card : ℝ) ≤
          (heavySetup.degreeLoss : ℝ) *
            (degreeSetup.selectedEdges.card : ℝ) := by
      exact_mod_cast h
    simpa [hdegreeLoss_def] using h'
  have hheavyLower :
      ((degreeSetup.selectedEdges.card : ℝ) / 2) /
          ((2 * (M : ℝ)) * fiberBound) ≤
        (heavySetup.heavy.card : ℝ) := by
    have h := heavySetup.heavy_lower
    rw [heavySetup.rectangleBound_eq] at h
    simpa [hM_def, heavySetup.M_parent_eq] using h
  have hsupportRetention :
      (heavySetup.heavy.card : ℝ) ≤
        supportLoss * (heavySetup.selectedCoarse.card : ℝ) := by
    have h :
        heavySetup.heavy.card ≤
          (Nat.log2 heavySetup.ambient.card + 1) *
            heavySetup.selectedCoarse.card :=
      heavySetup.support_retention
    have h' :
        (heavySetup.heavy.card : ℝ) ≤
          ((Nat.log2 heavySetup.ambient.card + 1 : ℕ) : ℝ) *
            (heavySetup.selectedCoarse.card : ℝ) := by
      exact_mod_cast h
    simpa [hsupportLoss_def] using h'
  cases hQ with
  | positive hcoarseBound =>
      set coefficient : ℝ :=
        (centers : ℝ) ^ 2 *
          (C_positive *
            Real.rpow coarseSetup.tangency C_positive *
            Real.rpow A C_positive)
          with hcoefficient_def
      set tail : ℝ :=
        Real.rpow
            (8 * (centers : ℝ) * (ambientCard : ℝ))
            (3 / 2 : ℝ) *
          Real.log
            (8 * (centers : ℝ) * (ambientCard : ℝ) /
              (support : ℝ))
          with htail_def
      have hcoefficient_nonneg : 0 ≤ coefficient := by
        rw [hcoefficient_def]
        have htangency_nonneg : 0 ≤ coarseSetup.tangency := by
          linarith [coarseSetup.tangency_ge_five]
        exact mul_nonneg (sq_nonneg _)
          (mul_nonneg
            (mul_nonneg (by linarith) <|
              Real.rpow_nonneg htangency_nonneg _)
            (Real.rpow_nonneg (by linarith) _))
      have htail_nonneg : 0 ≤ tail := by
        have hselected_pos :
            0 < (heavySetup.selectedCoarse.card : ℝ) := by
          exact_mod_cast
            (Finset.card_pos.mpr heavySetup.selectedCoarse_nonempty)
        have hsupportRpow :
            0 < Real.rpow (support : ℝ) (-3 / 2 : ℝ) := by
          exact Real.rpow_pos_of_pos
            (by exact_mod_cast hsupport_pos) _
        have hcoeff_pos : 0 < coefficient := by
          rw [hcoefficient_def]
          have hcenters_real : 0 < (centers : ℝ) := by
            exact_mod_cast hcenters_pos
          have htangency_pos : 0 < coarseSetup.tangency := by
            linarith [coarseSetup.tangency_ge_five]
          have hC_positive_pos : 0 < C_positive := by linarith
          have hA_pos : 0 < A := by linarith
          exact mul_pos (sq_pos_of_pos hcenters_real) <|
            mul_pos
              (mul_pos hC_positive_pos <|
                Real.rpow_pos_of_pos htangency_pos _)
              (Real.rpow_pos_of_pos hA_pos _)
        have hprod :
            0 < coefficient * Real.rpow (support : ℝ) (-3 / 2 : ℝ) :=
          mul_pos hcoeff_pos hsupportRpow
        nlinarith [hcoarseBound]
      have hmain :=
        normal_selected_total_cardinality_of_fiber_coefficient
          hInterpolate
          refinement.selected.card degreeSetup.retained.card
          degreeSetup.rawEdges.card degreeSetup.selectedEdges.card
          heavySetup.heavy.card heavySetup.selectedCoarse.card
          M q_fiber data.mu support
          parentLoss degreeLoss supportLoss fiberBound retention
          fiberCoefficient measureScale tangencyScale coefficient tail
          hM_pos hq data.mu_pos hsupport_pos
          hparentLoss_nonneg hdegreeLoss_nonneg hsupportLoss_nonneg
          hfiberBound hretention hfiberCoefficient
          hmeasureScale htangencyScale hcoefficient_nonneg htail_nonneg
          horiginal hrawLower hedgeRetention hheavyLower hsupportRetention
          hfiberScale hqRetention hMmeasure hMtangency hcoarseBound
      simpa [hcoefficient_def, htail_def,
        hparentLoss_def, hdegreeLoss_def, hsupportLoss_def,
        hM_def, hsupport_def, hcenters_def, hambientCard_def] using
        AmbientRestrictedSelectedCardinalityResultOfFiber.positive hmain
  | singleton hsmall hcoarseBound =>
      set coefficient : ℝ :=
        (centers : ℝ) ^ 2 *
          (C_singleton *
            Real.rpow coarseSetup.tangency C_singleton *
            Real.rpow A C_singleton)
          with hcoefficient_def
      set tail : ℝ :=
        Real.rpow (2 * (ambientCard : ℝ)) (3 / 2 : ℝ) *
          Real.log (2 * (ambientCard : ℝ))
          with htail_def
      have hcoefficient_nonneg : 0 ≤ coefficient := by
        rw [hcoefficient_def]
        have htangency_nonneg : 0 ≤ coarseSetup.tangency := by
          linarith [coarseSetup.tangency_ge_five]
        exact mul_nonneg (sq_nonneg _)
          (mul_nonneg
            (mul_nonneg (by linarith) <|
              Real.rpow_nonneg htangency_nonneg _)
            (Real.rpow_nonneg (by linarith) _))
      have htail_nonneg : 0 ≤ tail := by
        have hselected_pos :
            0 < (heavySetup.selectedCoarse.card : ℝ) := by
          exact_mod_cast
            (Finset.card_pos.mpr heavySetup.selectedCoarse_nonempty)
        have hcoeff_pos : 0 < coefficient := by
          rw [hcoefficient_def]
          have hcenters_real : 0 < (centers : ℝ) := by
            exact_mod_cast hcenters_pos
          have htangency_pos : 0 < coarseSetup.tangency := by
            linarith [coarseSetup.tangency_ge_five]
          have hC_singleton_pos : 0 < C_singleton := by linarith
          have hA_pos : 0 < A := by linarith
          exact mul_pos (sq_pos_of_pos hcenters_real) <|
            mul_pos
              (mul_pos hC_singleton_pos <|
                Real.rpow_pos_of_pos htangency_pos _)
              (Real.rpow_pos_of_pos hA_pos _)
        nlinarith [hcoarseBound]
      have hmain :=
        small_support_total_cardinality_of_fiber_coefficient
          hInterpolate
          refinement.selected.card degreeSetup.retained.card
          degreeSetup.rawEdges.card degreeSetup.selectedEdges.card
          heavySetup.heavy.card heavySetup.selectedCoarse.card
          M q_fiber data.mu support centers
          parentLoss degreeLoss supportLoss fiberBound retention
          fiberCoefficient measureScale tangencyScale coefficient tail
          hM_pos hq data.mu_pos hsupport_pos hsmall
          hparentLoss_nonneg hdegreeLoss_nonneg hsupportLoss_nonneg
          hfiberBound hretention hfiberCoefficient
          hmeasureScale htangencyScale hcoefficient_nonneg htail_nonneg
          horiginal hrawLower hedgeRetention hheavyLower hsupportRetention
          hfiberScale hqRetention hMmeasure hMtangency hcoarseBound
      simpa [hcoefficient_def, htail_def,
        hparentLoss_def, hdegreeLoss_def, hsupportLoss_def,
        hM_def, hsupport_def, hcenters_def, hambientCard_def] using
        AmbientRestrictedSelectedCardinalityResultOfFiber.singleton hmain

end Kakeya.Cinematic
