import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverRefinementStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostBalancingRefinementStatements

/-!
# Logarithmic loss absorption for final geometric balancing

This module contains only the cardinality estimates and logarithmic
absorptions needed by the post-balancing and final balanced-cover numerical
certificates.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_final_geometric_coarse_log_bound
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hrhoOne : rho ≤ 1)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (hLine : WZ1PaperIsLineClass coarse)
    (hDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
  have hCard :
      coarse.card ≤
        (2 * Nat.ceil (80 / rho) + 1) ^ 5 :=
    paper_essentially_distinct_card_bound_nat
      hDistinct hLine hrho hrhoOne
  have hRaw :
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
        (5 / Real.log 2) * Real.log (1 / rho) +
          (5 * Real.log 163 / Real.log 2 + 2) :=
    explicit_card_log_bound hrho hrhoOne hCard
  have hDeltaOne : delta ≤ 1 := hdeltaRho.trans hrhoOne
  have hLogDelta : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    calc
      (1 : ℝ) = 1⁻¹ := by norm_num
      _ ≤ delta⁻¹ := by gcongr
  have hInverse :
      1 / rho ≤ 1 / delta :=
    one_div_le_one_div_of_le hdelta hdeltaRho
  have hLogRhoDelta :
      Real.log (1 / rho) ≤ Real.log (1 / delta) :=
    Real.log_le_log (by positivity) hInverse
  have hLogOne :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [hdelta.ne']
  rw [hLogOne] at hLogRhoDelta
  have hCoefficientA :
      5 / Real.log 2 ≤ wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    exact le_max_right _ _
  have hCoefficientB :
      5 * Real.log 163 / Real.log 2 + 2 ≤
        wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    exact le_max_left _ _
  have hReal :
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
        wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹) := by
    calc
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
          (5 / Real.log 2) * Real.log (1 / rho) +
            (5 * Real.log 163 / Real.log 2 + 2) :=
        hRaw
      _ ≤
          (5 / Real.log 2) * Real.log delta⁻¹ +
            (5 * Real.log 163 / Real.log 2 + 2) := by
        gcongr
      _ ≤
          wz2PaperBoundaryLogCoefficient * Real.log delta⁻¹ +
            wz2PaperBoundaryLogCoefficient := by
        gcongr
      _ =
          wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹) := by ring
  have hCast :
      (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) =
        ENNReal.ofReal
          (Nat.log 2 (2 * coarse.card) + 1 : ℝ) := by
    norm_cast
  rw [hCast]
  exact ENNReal.ofReal_mono hReal

lemma wz2_paper_final_geometric_nat_log_two_twice_mul_add_one_le
    (first second : ℕ) :
    Nat.log 2 (2 * (first * second)) + 1 ≤
      (Nat.log 2 first + 1) +
        (Nat.log 2 (2 * second) + 1) := by
  by_cases hfirst : first = 0
  · simp [hfirst]
  by_cases hsecond : second = 0
  · simp [hsecond]
  let firstExponent := Nat.log 2 first + 1
  let secondExponent := Nat.log 2 (2 * second) + 1
  have hFirst :
      first < 2 ^ firstExponent := by
    dsimp only [firstExponent]
    exact Nat.lt_pow_succ_log_self (by norm_num) first
  have hSecond :
      2 * second < 2 ^ secondExponent := by
    dsimp only [secondExponent]
    exact Nat.lt_pow_succ_log_self (by norm_num) (2 * second)
  have hProduct :
      2 * (first * second) <
        2 ^ (firstExponent + secondExponent) := by
    calc
      2 * (first * second) = first * (2 * second) := by ring
      _ < 2 ^ firstExponent * (2 * second) :=
        Nat.mul_lt_mul_of_pos_right hFirst (by positivity)
      _ < 2 ^ firstExponent * 2 ^ secondExponent :=
        Nat.mul_lt_mul_of_pos_left hSecond (by positivity)
      _ = 2 ^ (firstExponent + secondExponent) := by
        exact (Nat.pow_add 2 firstExponent secondExponent).symm
  have hLog :
      Nat.log 2 (2 * (first * second)) <
        firstExponent + secondExponent :=
    Nat.log_lt_of_lt_pow (by positivity) hProduct
  dsimp only [firstExponent, secondExponent] at hLog
  omega

theorem wz2_paper_final_geometric_pair_card_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho)
    (fiberShading : WZ1PaperTubeShading fine) :
    (wz2PaperPositiveParentCellPairs active fiberShading).card ≤
      balancing.retainedCoarseCells.card * coarse.card := by
  calc
    (wz2PaperPositiveParentCellPairs active fiberShading).card ≤
        (wz2PaperParentCellPairs active).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤
        ∑ cell ∈ balancing.retainedCoarseCells,
          ((active.activeParents cell).image
            fun parent => (cell, parent)).card :=
      Finset.card_biUnion_le
    _ ≤
        ∑ _cell ∈ balancing.retainedCoarseCells,
          coarse.card := by
      apply Finset.sum_le_sum
      intro cell _
      exact
        Finset.card_image_le.trans <|
          (show (active.activeParents cell).card ≤ coarse.card by
            simpa using
              (Finset.card_le_univ
                (active.activeParents cell :
                  Finset (Fin coarse.card))))
    _ = balancing.retainedCoarseCells.card * coarse.card := by
      simp [Finset.sum_const]

theorem wz2_paper_final_geometric_retained_coarse_cells_subset_active_cells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    (coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing)
    (hrho : 0 < rho) :
    balancing.retainedCoarseCells ⊆
      wz1PaperActiveCells coarseData.coarseShading hrho := by
  intro cell hcell
  rcases coarseData.retained_cell_owned cell hcell with
    ⟨parent, hparent⟩
  let point : Point3 := cellCorner rho cell
  have hpointCell :
      point ∈ wz1PaperGridCube rho cell :=
    cellCorner_mem_gridCube hrho cell
  have hpointCarrier :
      point ∈ coarseData.coarseShading.carrier parent := by
    rw [coarseData.coarseShading_carrier_eq parent]
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hparent, hpointCell⟩
  have hpointBody :
      point ∈ wz1PaperTubeCarrier (coarse.tube parent) :=
    coarseData.coarseShading.subset_body parent hpointCarrier
  have hwindow :
      wz1PaperGridIndex rho point ∈
        wz1PaperGridIndicesInWindow rho hrho :=
    paper_point_gridIndex_in_window hrho hpointBody.2
  have hindex :
      wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  rw [hindex] at hwindow
  rw [mem_wz1PaperActiveCells]
  exact
    ⟨hwindow,
      ⟨point, ⟨parent, hpointCarrier⟩, hpointCell⟩⟩

theorem wz2_paper_final_geometric_available_cell_count_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {fiberBand :
      WZ2PaperFiberMultiplicityBandData cover balancing.refined}
    {pairBand :
      WZ2PaperParentCellMassBandData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand}
    {restriction :
      WZ2PaperParentCellRestrictionData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand}
    (finalFine :
      WZ2PaperFinalFineExactBalancingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction) :
    (∑ cell ∈ finalFine.finalCoarseCells,
        (finalFine.availableFinalFineCells cell).card) =
      finalFine.activeFineCells.card := by
  simp_rw [finalFine.availableFinalFineCells_eq]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  apply congrArg Finset.card
  apply Finset.filter_true_of_mem
  intro fineCell hfineCell
  rw [finalFine.finalCoarseCells_eq]
  exact Finset.mem_image.mpr
    ⟨fineCell, hfineCell, rfl⟩

theorem wz2_paper_final_geometric_post_balancing_loss_absorption :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta rho : ℝ},
        ∀ (hdelta : 0 < delta),
        delta ≤ delta₀ →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {shading : WZ1PaperTubeShading fine},
            ∀ {multiplicityCap : ENNReal},
              ∀ (pruning :
                  WZ2PaperBoundaryCellPruningData
                    (rho := rho) shading hdelta multiplicityCap),
                wz1PaperRefinementFraction delta 2 *
                    wz2PaperPostBalancingLoss pruning ≤
                  1 := by
  have hCoefficient :
      0 ≤ 8 * wz2PaperBoundaryLogCoefficient := by
    exact mul_nonneg (by norm_num) <| by
      dsimp only [wz2PaperBoundaryLogCoefficient]
      positivity
  rcases
      exists_delta_boundary_log_square
        (8 * wz2PaperBoundaryLogCoefficient) hCoefficient
    with ⟨delta₀, hdelta₀Pos, hdelta₀One, hLogData⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro delta rho hdelta hdeltaBound fine shading multiplicityCap pruning
  let logScale : ENNReal :=
    ENNReal.ofReal (Real.log delta⁻¹)
  let availableLog : ENNReal :=
    ((Nat.log 2
        (∑ coarseCell ∈ pruning.coarseCells,
          (pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
      ENNReal)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans hdelta₀One
  have hLogRealPos : 0 < Real.log delta⁻¹ := by
    linarith [(hLogData delta hdelta hdeltaBound).1]
  have hLogScaleZero : logScale ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogScaleTop : logScale ≠ ⊤ := by
    dsimp only [logScale]
    exact ENNReal.ofReal_ne_top
  have hAvailable :
      availableLog ≤
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹)) := by
    dsimp only [availableLog]
    exact
      wz2_paper_available_cell_log_bound_ennreal
        hdelta hdeltaOne pruning
  have hEnvelope :
      ENNReal.ofReal
          (8 * wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹)) ≤
        logScale ^ 2 := by
    calc
      ENNReal.ofReal
            (8 * wz2PaperBoundaryLogCoefficient *
              (1 + Real.log delta⁻¹)) ≤
          ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono
          (hLogData delta hdelta hdeltaBound).2
      _ = logScale ^ 2 := by
        dsimp only [logScale]
        rw [← ENNReal.ofReal_pow hLogRealPos.le]
  have hLoss :
      wz2PaperPostBalancingLoss pruning ≤ logScale ^ 2 := by
    calc
      wz2PaperPostBalancingLoss pruning =
          8 * availableLog := by
        simp [wz2PaperPostBalancingLoss, availableLog]
      _ ≤
          8 *
            ENNReal.ofReal
              (wz2PaperBoundaryLogCoefficient *
                (1 + Real.log delta⁻¹)) := by
        gcongr
      _ =
          ENNReal.ofReal
            (8 * wz2PaperBoundaryLogCoefficient *
              (1 + Real.log delta⁻¹)) := by
        calc
          (8 : ENNReal) *
                ENNReal.ofReal
                  (wz2PaperBoundaryLogCoefficient *
                    (1 + Real.log delta⁻¹)) =
              ENNReal.ofReal (8 : ℝ) *
                ENNReal.ofReal
                  (wz2PaperBoundaryLogCoefficient *
                    (1 + Real.log delta⁻¹)) := by
            norm_num
          _ =
              ENNReal.ofReal
                ((8 : ℝ) *
                  (wz2PaperBoundaryLogCoefficient *
                    (1 + Real.log delta⁻¹))) := by
            exact
              (ENNReal.ofReal_mul
                (p := (8 : ℝ))
                (q := wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹))
                (by norm_num)).symm
          _ =
              ENNReal.ofReal
                (8 * wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) := by
            congr 1
            ring
      _ ≤ logScale ^ 2 := hEnvelope
  have hFraction :
      wz1PaperRefinementFraction delta 2 =
        logScale⁻¹ ^ 2 := by
    dsimp only [wz1PaperRefinementFraction, logScale]
    congr 2
    congr 1
    field_simp [hdelta.ne']
  rw [hFraction]
  calc
    logScale⁻¹ ^ 2 * wz2PaperPostBalancingLoss pruning ≤
        logScale⁻¹ ^ 2 * logScale ^ 2 := by
      gcongr
    _ = 1 := by
      rw [← mul_pow,
        ENNReal.inv_mul_cancel hLogScaleZero hLogScaleTop]
      norm_num

theorem wz2_paper_final_geometric_balanced_cover_loss_bound_of_logs
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData)
    (envelope : ENNReal)
    (hFineLog :
      ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤ envelope)
    (hPairLog :
      (Nat.log 2
          (2 *
            (wz2PaperPositiveParentCellPairs
              producer.active producer.fiberBand.refined).card) :
        ENNReal) + 1 ≤
        2 * envelope)
    (hFinalCellLog :
      ((Nat.log 2
          (∑ cell ∈ producer.finalFine.finalCoarseCells,
            (producer.finalFine.availableFinalFineCells cell).card) + 1 :
        ℕ) : ENNReal) ≤
        envelope)
    (hCoarseLog :
      ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤ envelope) :
    wz2PaperFinalBalancedCoverLoss producer ≤
      16 * envelope ^ 5 := by
  dsimp only [wz2PaperFinalBalancedCoverLoss]
  calc
    ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) *
          (2 *
            ((Nat.log 2
                (2 *
                  (wz2PaperPositiveParentCellPairs
                    producer.active
                    producer.fiberBand.refined).card) :
              ENNReal) + 1)) *
          ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) *
          (4 *
            ((Nat.log 2
                (∑ cell ∈ producer.finalFine.finalCoarseCells,
                  (producer.finalFine.availableFinalFineCells cell).card) +
                  1 : ℕ) : ENNReal)) *
          ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤
        envelope * (2 * (2 * envelope)) * envelope *
          (4 * envelope) * envelope := by
      gcongr
    _ = 16 * envelope ^ 5 := by ring

theorem wz2_paper_final_geometric_balanced_cover_loss_absorption :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta rho : ℝ},
        ∀ (hdelta : 0 < delta),
          delta ≤ delta₀ →
          ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
            ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
              ∀ {cover : WZ2PaperPartitioningCover fine coarse},
                ∀ {sourceShading : WZ1PaperTubeShading fine},
                  ∀ {coarseCells : Finset WZ2PaperCellIndex},
                    ∀ {availableFineCells :
                        WZ2PaperCellIndex → Finset WZ2PaperCellIndex},
                      ∀ {balancing :
                          WZ2PaperExactCellBalancingData
                            (rho := rho) sourceShading coarseCells
                            availableFineCells},
                        ∀ {coarseData :
                            WZ2PaperCoarseShadingData
                              cover sourceShading coarseCells
                              availableFineCells balancing},
                          ∀ {hrho : 0 < rho},
                            ∀ (producer :
                                WZ2PaperFinalBalancedCoverProducerData
                                  (hdelta := hdelta) (hrho := hrho)
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData),
                              ∀ (envelope : ENNReal),
                                ((Nat.log 2 fine.card + 1 : ℕ) :
                                    ENNReal) ≤ envelope →
                                (Nat.log 2
                                    (2 *
                                      (wz2PaperPositiveParentCellPairs
                                        producer.active
                                        producer.fiberBand.refined).card) :
                                  ENNReal) + 1 ≤
                                  2 * envelope →
                                ((Nat.log 2
                                    (∑ cell ∈
                                      producer.finalFine.finalCoarseCells,
                                      (producer.finalFine
                                        |>.availableFinalFineCells cell).card) +
                                      1 : ℕ) : ENNReal) ≤
                                  envelope →
                                ((Nat.log 2 coarse.card + 1 : ℕ) :
                                    ENNReal) ≤ envelope →
                                envelope ≤
                                  ENNReal.ofReal
                                    (wz2PaperBoundaryLogCoefficient *
                                      (1 + Real.log delta⁻¹)) →
                                wz1PaperRefinementFraction delta 14 *
                                    wz2PaperFinalBalancedCoverLoss producer ≤
                                  1 := by
  have hCoefficient :
      0 ≤ wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    positivity
  rcases
      exists_delta_boundary_log_square
        wz2PaperBoundaryLogCoefficient hCoefficient
    with ⟨delta₀, hdelta₀Pos, hdelta₀One, hLogData⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro delta rho hdelta hdeltaBound fine coarse cover sourceShading
    coarseCells availableFineCells balancing coarseData hrho producer
    envelope hFineLog hPairLog hFinalCellLog hCoarseLog hEnvelope
  let logScale : ENNReal :=
    ENNReal.ofReal (Real.log delta⁻¹)
  let physicalEnvelope : ENNReal :=
    ENNReal.ofReal
      (wz2PaperBoundaryLogCoefficient *
        (1 + Real.log delta⁻¹))
  have hLogThree :
      3 ≤ Real.log delta⁻¹ :=
    (hLogData delta hdelta hdeltaBound).1
  have hLogRealPos : 0 < Real.log delta⁻¹ := by
    linarith
  have hLogScaleZero : logScale ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogScaleTop : logScale ≠ ⊤ := by
    dsimp only [logScale]
    exact ENNReal.ofReal_ne_top
  have hPhysicalEnvelope :
      physicalEnvelope ≤ logScale ^ 2 := by
    calc
      physicalEnvelope ≤
          ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) := by
        dsimp only [physicalEnvelope]
        exact ENNReal.ofReal_mono
          (hLogData delta hdelta hdeltaBound).2
      _ = logScale ^ 2 := by
        dsimp only [logScale]
        rw [← ENNReal.ofReal_pow hLogRealPos.le]
  have hEnvelopeLog : envelope ≤ logScale ^ 2 :=
    hEnvelope.trans hPhysicalEnvelope
  have hLogScaleThree : (3 : ENNReal) ≤ logScale := by
    dsimp only [logScale]
    simpa using
      (ENNReal.ofReal_le_ofReal_iff hLogRealPos.le).mpr hLogThree
  have hSixteen :
      (16 : ENNReal) ≤ logScale ^ 4 := by
    calc
      (16 : ENNReal) ≤ 3 ^ 4 := by norm_num
      _ ≤ logScale ^ 4 := by gcongr
  have hLoss :
      wz2PaperFinalBalancedCoverLoss producer ≤
        16 * envelope ^ 5 :=
    wz2_paper_final_geometric_balanced_cover_loss_bound_of_logs
      producer envelope hFineLog hPairLog hFinalCellLog hCoarseLog
  have hLossLog :
      wz2PaperFinalBalancedCoverLoss producer ≤ logScale ^ 14 := by
    calc
      wz2PaperFinalBalancedCoverLoss producer ≤
          16 * envelope ^ 5 := hLoss
      _ ≤ 16 * (logScale ^ 2) ^ 5 := by
        gcongr
      _ ≤ logScale ^ 4 * (logScale ^ 2) ^ 5 := by
        gcongr
      _ = logScale ^ 14 := by
        rw [← pow_mul]
        ring_nf
  have hFraction :
      wz1PaperRefinementFraction delta 14 =
        logScale⁻¹ ^ 14 := by
    dsimp only [wz1PaperRefinementFraction, logScale]
    congr 2
    congr 1
    field_simp [hdelta.ne']
  rw [hFraction]
  calc
    logScale⁻¹ ^ 14 *
          wz2PaperFinalBalancedCoverLoss producer ≤
        logScale⁻¹ ^ 14 * logScale ^ 14 := by
      gcongr
    _ = 1 := by
      rw [← mul_pow,
        ENNReal.inv_mul_cancel hLogScaleZero hLogScaleTop]
      norm_num

theorem wz2_paper_final_geometric_balanced_cover_loss_absorption_from_lines :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta rho : ℝ},
        ∀ (hdelta : 0 < delta),
          delta ≤ delta₀ →
          ∀ (hrho : 0 < rho),
            delta ≤ rho →
            rho ≤ 1 →
            ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
              ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
                fine.Nonempty →
                coarse.Nonempty →
                WZ1PaperIsLineClass fine →
                WZ1PaperIsEssentiallyDistinct fine →
                WZ1PaperIsLineClass coarse →
                WZ1PaperIsEssentiallyDistinct coarse →
                ∀ {cover : WZ2PaperPartitioningCover fine coarse},
                  ∀ {sourceShading : WZ1PaperTubeShading fine},
                    ∀ {coarseCells : Finset WZ2PaperCellIndex},
                      ∀ {availableFineCells :
                          WZ2PaperCellIndex → Finset WZ2PaperCellIndex},
                        ∀ {balancing :
                            WZ2PaperExactCellBalancingData
                              (rho := rho) sourceShading coarseCells
                              availableFineCells},
                          ∀ {coarseData :
                              WZ2PaperCoarseShadingData
                                cover sourceShading coarseCells
                                availableFineCells balancing},
                            ∀ (producer :
                                WZ2PaperFinalBalancedCoverProducerData
                                  (hdelta := hdelta) (hrho := hrho)
                                  cover sourceShading coarseCells
                                  availableFineCells balancing coarseData),
                              wz1PaperRefinementFraction delta 14 *
                                  wz2PaperFinalBalancedCoverLoss producer ≤
                                1 := by
  rcases wz2_paper_final_geometric_balanced_cover_loss_absorption with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hAbsorb⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro delta rho hdelta hdeltaBound hrho hdeltaRho hrhoOne
    fine coarse fineNonempty coarseNonempty fineLine fineDistinct
    coarseLine coarseDistinct cover sourceShading coarseCells
    availableFineCells balancing coarseData producer
  let envelope : ENNReal :=
    ENNReal.ofReal
      (wz2PaperBoundaryLogCoefficient *
        (1 + Real.log delta⁻¹))
  have hdeltaOne : delta ≤ 1 := hdeltaRho.trans hrhoOne
  have hFineDouble :
      (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ≤ envelope := by
    dsimp only [envelope]
    exact
      wz2_paper_final_geometric_coarse_log_bound
        hdelta hdelta le_rfl hdeltaOne fineLine fineDistinct
  have hFineLog :
      ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤ envelope := by
    calc
      ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) := by
        exact_mod_cast
          Nat.add_le_add_right
            (Nat.log_mono_right <| by omega) 1
      _ ≤ envelope := hFineDouble
  have hCoarseDouble :
      (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ≤ envelope := by
    dsimp only [envelope]
    exact
      wz2_paper_final_geometric_coarse_log_bound
        hdelta hrho hdeltaRho hrhoOne coarseLine coarseDistinct
  have hCoarseLog :
      ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤ envelope := by
    calc
      ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal) ≤
          (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) := by
        exact_mod_cast
          Nat.add_le_add_right
            (Nat.log_mono_right <| by omega) 1
      _ ≤ envelope := hCoarseDouble
  have hCoarseCells :
      balancing.retainedCoarseCells ⊆
        wz1PaperActiveCells coarseData.coarseShading hrho :=
    wz2_paper_final_geometric_retained_coarse_cells_subset_active_cells
      coarseData hrho
  have hCoarseCellLog :
      ((Nat.log 2 balancing.retainedCoarseCells.card + 1 : ℕ) :
          ENNReal) ≤ envelope := by
    calc
      ((Nat.log 2 balancing.retainedCoarseCells.card + 1 : ℕ) :
          ENNReal) ≤
          ((Nat.log 2
              (wz1PaperActiveCells
                coarseData.coarseShading hrho).card + 1 : ℕ) :
            ENNReal) := by
        exact_mod_cast
          Nat.add_le_add_right
            (Nat.log_mono_right <| Finset.card_le_card hCoarseCells) 1
      _ ≤
          ENNReal.ofReal
            (wz2PaperBoundaryLogCoefficient *
              (1 + Real.log rho⁻¹)) :=
        wz2_paper_active_cell_log_bound_ennreal
          hrho hrhoOne coarseData.coarseShading
      _ ≤ envelope := by
        dsimp only [envelope]
        apply ENNReal.ofReal_mono
        have hLog :
            Real.log rho⁻¹ ≤ Real.log delta⁻¹ := by
          apply Real.log_le_log
          · exact inv_pos.mpr hrho
          · exact (inv_le_inv₀ hrho hdelta).mpr hdeltaRho
        have hCoefficient :
            0 ≤ wz2PaperBoundaryLogCoefficient := by
          dsimp only [wz2PaperBoundaryLogCoefficient]
          positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hCoefficient
  have hPairCard :
      (wz2PaperPositiveParentCellPairs
          producer.active producer.fiberBand.refined).card ≤
        balancing.retainedCoarseCells.card * coarse.card :=
    wz2_paper_final_geometric_pair_card_le
      producer.active producer.fiberBand.refined
  have hPairLog :
      (Nat.log 2
          (2 *
            (wz2PaperPositiveParentCellPairs
              producer.active producer.fiberBand.refined).card) :
        ENNReal) + 1 ≤
        2 * envelope := by
    have hNat :
        Nat.log 2
              (2 *
                (wz2PaperPositiveParentCellPairs
                  producer.active producer.fiberBand.refined).card) + 1 ≤
          (Nat.log 2 balancing.retainedCoarseCells.card + 1) +
            (Nat.log 2 (2 * coarse.card) + 1) := by
      calc
        _ ≤
            Nat.log 2
                (2 *
                  (balancing.retainedCoarseCells.card * coarse.card)) + 1 := by
          exact Nat.add_le_add_right
            (Nat.log_mono_right <| Nat.mul_le_mul_left 2 hPairCard) 1
        _ ≤ _ :=
          wz2_paper_final_geometric_nat_log_two_twice_mul_add_one_le _ _
    calc
      (Nat.log 2
            (2 *
              (wz2PaperPositiveParentCellPairs
                producer.active producer.fiberBand.refined).card) :
          ENNReal) + 1 ≤
          ((Nat.log 2 balancing.retainedCoarseCells.card + 1 : ℕ) :
              ENNReal) +
            ((Nat.log 2 (2 * coarse.card) + 1 : ℕ) : ENNReal) := by
        exact_mod_cast hNat
      _ ≤ envelope + envelope :=
        add_le_add hCoarseCellLog <| by
          simpa only [Nat.cast_add, Nat.cast_one] using hCoarseDouble
      _ = 2 * envelope := by ring
  have hFinalCount :
      (∑ cell ∈ producer.finalFine.finalCoarseCells,
          (producer.finalFine.availableFinalFineCells cell).card) =
        producer.finalFine.activeFineCells.card :=
    wz2_paper_final_geometric_available_cell_count_eq producer.finalFine
  have hFinalCellLog :
      ((Nat.log 2
          (∑ cell ∈ producer.finalFine.finalCoarseCells,
            (producer.finalFine.availableFinalFineCells cell).card) + 1 :
        ℕ) : ENNReal) ≤
        envelope := by
    rw [hFinalCount, producer.finalFine.activeFineCells_eq]
    exact
      wz2_paper_active_cell_log_bound_ennreal
        hdelta hdeltaOne producer.finalFine.fineBand
  exact
    hAbsorb hdelta hdeltaBound producer envelope
      hFineLog hPairLog hFinalCellLog hCoarseLog le_rfl

end Kakeya.Assouad

end
