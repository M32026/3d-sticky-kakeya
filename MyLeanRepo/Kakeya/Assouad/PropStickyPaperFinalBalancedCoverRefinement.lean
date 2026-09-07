import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverRefinementStatements

/-! # Total refinement loss for the ghost-free final balanced cover -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_balanced_cover_refinement :
    WZ2PaperFinalBalancedCoverRefinementStatement := by
  intro delta rho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData hdelta hrho producer
    logExponent hAbsorb
  let fiberLoss : ENNReal :=
    ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal)
  let pairLoss : ENNReal :=
    2 *
      ((Nat.log 2
          (2 *
            (wz2PaperPositiveParentCellPairs
              producer.active producer.fiberBand.refined).card) :
        ENNReal) + 1)
  let fineLoss : ENNReal :=
    ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal)
  let exactLoss : ENNReal :=
    4 *
      ((Nat.log 2
          (∑ cell ∈ producer.finalFine.finalCoarseCells,
            (producer.finalFine.availableFinalFineCells cell).card) + 1 :
        ℕ) : ENNReal)
  let coarseLoss : ENNReal :=
    ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal)
  have hFiberLossZero : fiberLoss ≠ 0 := by
    dsimp only [fiberLoss]
    positivity
  have hFiberLossTop : fiberLoss ≠ ⊤ := by
    dsimp only [fiberLoss]
    simp
  have hFiber :
      balancing.refined.mass ≤
        fiberLoss * producer.fiberBand.refined.mass := by
    have h := producer.fiberBand.retained_mass
    rw [ENNReal.div_le_iff hFiberLossZero hFiberLossTop] at h
    simpa [fiberLoss, mul_comm] using h
  have hPairLossZero : pairLoss ≠ 0 := by
    dsimp only [pairLoss]
    positivity
  have hPairLossTop : pairLoss ≠ ⊤ := by
    dsimp only [pairLoss]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have hPair :
      producer.fiberBand.refined.mass ≤
        pairLoss * producer.restriction.refined.mass := by
    have h := producer.restriction.retained_mass
    rw [ENNReal.div_le_iff hPairLossZero hPairLossTop] at h
    simpa [pairLoss, mul_comm] using h
  have hFineLossZero : fineLoss ≠ 0 := by
    dsimp only [fineLoss]
    positivity
  have hFineLossTop : fineLoss ≠ ⊤ := by
    dsimp only [fineLoss]
    simp
  have hFine :
      producer.restriction.refined.mass ≤
        fineLoss * producer.finalFine.fineBand.mass := by
    have h := producer.finalFine.fineBand_mass_retention
    rw [ENNReal.div_le_iff hFineLossZero hFineLossTop] at h
    simpa [fineLoss, mul_comm] using h
  have hExact :
      producer.finalFine.fineBand.mass ≤
        exactLoss * producer.finalFine.exact.refined.mass := by
    simpa [exactLoss] using producer.finalFine.exact_mass_retention
  have hCoarseLossZero : coarseLoss ≠ 0 := by
    dsimp only [coarseLoss]
    positivity
  have hCoarseLossTop : coarseLoss ≠ ⊤ := by
    dsimp only [coarseLoss]
    simp
  have hCoarse :
      producer.finalFine.exact.refined.mass ≤
        coarseLoss * producer.coarseBand.selectedFineShading.mass := by
    have h := producer.coarseBand.selectedFine_mass_retention
    rw [ENNReal.div_le_iff hCoarseLossZero hCoarseLossTop] at h
    simpa [coarseLoss, mul_comm] using h
  have hSource :
      balancing.refined.mass ≤
        wz2PaperFinalBalancedCoverLoss producer *
          producer.coarseBand.selectedFineShading.mass := by
    calc
      balancing.refined.mass ≤
          fiberLoss * producer.fiberBand.refined.mass := hFiber
      _ ≤ fiberLoss *
          (pairLoss * producer.restriction.refined.mass) := by
        gcongr
      _ ≤ fiberLoss *
          (pairLoss *
            (fineLoss * producer.finalFine.fineBand.mass)) := by
        gcongr
      _ ≤ fiberLoss *
          (pairLoss *
            (fineLoss *
              (exactLoss *
                producer.finalFine.exact.refined.mass))) := by
        gcongr
      _ ≤ fiberLoss *
          (pairLoss *
            (fineLoss *
              (exactLoss *
                (coarseLoss *
                  producer.coarseBand.selectedFineShading.mass)))) := by
        gcongr
      _ =
          wz2PaperFinalBalancedCoverLoss producer *
            producer.coarseBand.selectedFineShading.mass := by
        simp only [wz2PaperFinalBalancedCoverLoss, fiberLoss,
          pairLoss, fineLoss, exactLoss, coarseLoss]
        ring
  have hSubshading :
      ∀ index,
        producer.coarseBand.selectedFineShading.carrier index ⊆
          balancing.refined.carrier index := by
    intro index
    have h1 :
        producer.coarseBand.selectedFineShading.carrier index ⊆
          producer.finalFine.exact.refined.carrier index :=
      producer.coarseBand.selectedFine_subshading index
    have h2 :
        producer.finalFine.exact.refined.carrier index ⊆
          producer.finalFine.fineBand.carrier index :=
      producer.finalFine.exact.refined_subshading index
    have h3 :
        producer.finalFine.fineBand.carrier index ⊆
          producer.restriction.refined.carrier index := by
      rw [producer.finalFine.fineBand_carrier_eq index]
      exact Set.inter_subset_left
    have h4 :
        producer.restriction.refined.carrier index ⊆
          producer.fiberBand.refined.carrier index :=
      producer.restriction.refined_subshading index
    have h5 :
        producer.fiberBand.refined.carrier index ⊆
          balancing.refined.carrier index :=
      producer.fiberBand.refined_subshading index
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hRetained :
      wz1PaperRefinementFraction delta logExponent *
          balancing.refined.mass ≤
        producer.coarseBand.selectedFineShading.mass := by
    calc
      wz1PaperRefinementFraction delta logExponent *
            balancing.refined.mass ≤
          wz1PaperRefinementFraction delta logExponent *
            (wz2PaperFinalBalancedCoverLoss producer *
              producer.coarseBand.selectedFineShading.mass) := by
        gcongr
      _ =
          (wz1PaperRefinementFraction delta logExponent *
            wz2PaperFinalBalancedCoverLoss producer) *
              producer.coarseBand.selectedFineShading.mass := by
        rw [mul_assoc]
      _ ≤ 1 * producer.coarseBand.selectedFineShading.mass := by
        gcongr
      _ = producer.coarseBand.selectedFineShading.mass := by
        simp
  exact ⟨{
    source_mass_le := hSource
    subshading := hSubshading
    retained_mass := hRetained
  }⟩

end Kakeya.Assouad

end
