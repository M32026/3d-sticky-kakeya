import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseSharpGeometry

/-!
# Dependent genuine-coarse Lemma-23 pipeline

Every field below is constructed from the same paper-order carrier data.
This prevents a second choice of the balanced-cover witnesses from breaking
the graph-cell, owner-cell, parent, and original-normal identities.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceFixedBinCoarsePipelineData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained) where
  original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
    carrier fineWitnesses.coarseWitnesses
  prep : PureWZ2SourceFixedBinCoarsePreparationData original
  prep_shadow_union : prep.shadow.union = carrier.shading.union
  graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep
  normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
    (eta := normalEta) fineWitnesses
  preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
    graphParents normalFirst
  sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph

/-- Backwards-compatible maximal-bin view of the genuine-coarse pipeline. -/
abbrev PureWZ2SourceFixedLineCoarsePipelineData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale) : Type :=
  PureWZ2SourceFixedBinCoarsePipelineData
    (normalEta := normalEta) carriers.coarseCarrier carriers.fineWitnesses

/-- The graph-side continuation indexed by an already selected fixed-bin
preparation.  Keeping `prep` as an index (rather than an internal field) is
what preserves the ready-volume certificate chosen by the all-bin argument. -/
structure PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedBinCoarsePreparationData original) where
  graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep
  normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
    (eta := normalEta) fineWitnesses
  preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
    graphParents normalFirst
  sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph

/-- Continue the genuine-coarse graph construction from one already selected
fixed-bin preparation, without reselecting the preparation. -/
theorem PureWZ2SourceFixedBinCoarsePreparationData.coarseGraphPipelineAtPreparationFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedBinCoarsePreparationData original)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hvolumePos : 0 < MeasureTheory.volume prep.shadow.union) :
    Nonempty (PureWZ2SourceFixedBinCoarsePipelineAtPreparationData
      (normalEta := normalEta) prep) := by
  rcases prep.graphParentsFixedBin with ⟨graphParents⟩
  rcases prep.normalFirstFixedBin hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
      hlocalPower hglobalPower hPlanarSmall hrootSmall20
      hlocalizationAbsorb with ⟨normalFirst⟩
  rcases graphParents.prepareGraphFixedBin normalFirst hbridge hlocalConstant
      hvolumePos with
    ⟨preparedGraph⟩
  rcases preparedGraph.toSharpGeometryFixedBin with ⟨sharp⟩
  exact ⟨{
    graphParents := graphParents
    normalFirst := normalFirst
    preparedGraph := preparedGraph
    sharp := sharp
  }⟩

/-- Construct the complete graph-side prefix on one fixed-bin genuine coarse
carrier while preserving its exact fine-witness provenance. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.coarseGraphPipelineFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedBinCoarsePipelineData
      (normalEta := normalEta) carrier fineWitnesses) := by
  rcases carrier.withEndpointBudgetFixedBin
      fineWitnesses.coarseWitnesses hsigma hsigmaOne
      hCge hendpoint hbridge with ⟨original⟩
  rcases original.prepareFixedBin hgraphOne hheightAbsorb with
    ⟨prep, hshadow⟩
  have hvolumePos : 0 < MeasureTheory.volume prep.shadow.union := by
    rw [hshadow, carrier.volume_eq]
    have hselectedPos : 0 < (residue.selected.card : ENNReal) := by
      exact_mod_cast residue.selected_nonempty.card_pos
    exact ENNReal.mul_pos hselectedPos.ne'
      twoScale.fine.balanced.cellMass_pos.ne'
  rcases prep.coarseGraphPipelineAtPreparationFixedBin hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
      hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb
      hlocalConstant hvolumePos with ⟨pipeline⟩
  exact ⟨{
    original := original
    prep := prep
    prep_shadow_union := hshadow
    graphParents := pipeline.graphParents
    normalFirst := pipeline.normalFirst
    preparedGraph := pipeline.preparedGraph
    sharp := pipeline.sharp
  }⟩

/-- Production genuine-coarse graph prefix.  Its original-slope AD input is
the exact global AD certificate of `twoScale.coarseGrains`, restricted along
the genuine coarse carrier and transported by `coarse_slope_eq`. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.coarseGraphPipelineFromCoarseGlobalGrainsFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedBinCoarsePipelineData
      (normalEta := normalEta) carrier fineWitnesses) := by
  rcases carrier.withCoarseGlobalGrainsFixedBin
      fineWitnesses.coarseWitnesses hbridge with ⟨original⟩
  rcases original.prepareFixedBin hgraphOne hheightAbsorb with
    ⟨prep, hshadow⟩
  have hvolumePos : 0 < MeasureTheory.volume prep.shadow.union := by
    rw [hshadow, carrier.volume_eq]
    have hselectedPos : 0 < (residue.selected.card : ENNReal) := by
      exact_mod_cast residue.selected_nonempty.card_pos
    exact ENNReal.mul_pos hselectedPos.ne'
      twoScale.fine.balanced.cellMass_pos.ne'
  rcases prep.coarseGraphPipelineAtPreparationFixedBin hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
      hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb
      hlocalConstant hvolumePos with ⟨pipeline⟩
  exact ⟨{
    original := original
    prep := prep
    prep_shadow_union := hshadow
    graphParents := pipeline.graphParents
    normalFirst := pipeline.normalFirst
    preparedGraph := pipeline.preparedGraph
    sharp := pipeline.sharp
  }⟩

/-- Construct the complete fixed-bin genuine-coarse graph prefix from an
explicit original-source `rho`-slab AD receipt.  Unlike
`coarseGraphPipelineFixedBin`, this route has no bounded-diameter endpoint
hypothesis. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.coarseGraphPipelineOfSourceRhoSlabADFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (carrier : PureWZ2SourceFixedBinCoarseCarrierData residue)
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedBinCoarsePipelineData
      (normalEta := normalEta) carrier fineWitnesses) := by
  rcases carrier.withSourceRhoSlabADFixedBin fineWitnesses.coarseWitnesses
      hsourceRhoSlabAD hconstant with ⟨original⟩
  rcases original.prepareFixedBin hgraphOne hheightAbsorb with
    ⟨prep, hshadow⟩
  have hvolumePos : 0 < MeasureTheory.volume prep.shadow.union := by
    rw [hshadow, carrier.volume_eq]
    have hselectedPos : 0 < (residue.selected.card : ENNReal) := by
      exact_mod_cast residue.selected_nonempty.card_pos
    exact ENNReal.mul_pos hselectedPos.ne'
      twoScale.fine.balanced.cellMass_pos.ne'
  rcases prep.coarseGraphPipelineAtPreparationFixedBin hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
      hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb
      hlocalConstant hvolumePos with ⟨pipeline⟩
  exact ⟨{
    original := original
    prep := prep
    prep_shadow_union := hshadow
    graphParents := pipeline.graphParents
    normalFirst := pipeline.normalFirst
    preparedGraph := pipeline.preparedGraph
    sharp := pipeline.sharp
  }⟩

/-- Construct the complete graph-side prefix of Lemma 24 on the genuine
first-sticky coarse carrier. -/
theorem PureWZ2OrdinaryPaperOrderCarrierData.coarseGraphPipeline
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarsePipelineData
      (normalEta := normalEta) carriers) := by
  exact carriers.coarseCarrier.coarseGraphPipelineFixedBin
    carriers.fineWitnesses hbridge hsigma hsigmaOne hnormalEta
    hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower hglobalPower
    hPlanarSmall hrootSmall20 hlocalizationAbsorb hgraphOne hheightAbsorb
    hCge hendpoint hlocalConstant

/-- Maximal-bin production view of
`coarseGraphPipelineFromCoarseGlobalGrainsFixedBin`. -/
theorem PureWZ2OrdinaryPaperOrderCarrierData.coarseGraphPipelineFromCoarseGlobalGrains
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarsePipelineData
      (normalEta := normalEta) carriers) :=
  carriers.coarseCarrier.coarseGraphPipelineFromCoarseGlobalGrainsFixedBin
    carriers.fineWitnesses hbridge hsigma hsigmaOne hnormalEta
    hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower hglobalPower
    hPlanarSmall hrootSmall20 hlocalizationAbsorb hgraphOne hheightAbsorb
    hlocalConstant

/-- Maximal-bin compatibility view of the source-slab genuine-coarse graph
constructor. -/
theorem PureWZ2OrdinaryPaperOrderCarrierData.coarseGraphPipelineOfSourceRhoSlabAD
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale)
    {C : ENNReal}
    (hsourceRhoSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection source.globalGrains.slope
          (globalGrainSlab source.shading.union z rho))
        rho (1 - sigma) C)
    (hconstant :
      144 * C ≤ 10 * Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta)
    (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hlocalConstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty (PureWZ2SourceFixedLineCoarsePipelineData
      (normalEta := normalEta) carriers) :=
  carriers.coarseCarrier.coarseGraphPipelineOfSourceRhoSlabADFixedBin
    carriers.fineWitnesses hsourceRhoSlabAD hconstant hbridge hsigma hsigmaOne
    hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor hlocalPower
    hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb hgraphOne
    hheightAbsorb hlocalConstant

end Kakeya.Assouad

end
