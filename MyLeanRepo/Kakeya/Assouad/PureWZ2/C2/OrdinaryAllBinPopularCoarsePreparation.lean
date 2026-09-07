import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderGlobalBinCoarseFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePopularPreparation

/-!
# Outer-popular genuine-coarse preparations over all global bins

For every fixed global bin, restrict the genuine first-sticky coarse carrier
to the outer source-popular height region before running Lemma 23.  The full
coarse preparation remains available only as the source of its original-slope
certificate; graph data downstream is indexed by the synchronized restricted
preparation.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarsePreparationFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family) where
  popularCarrier : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinPopularCoarseCarrierData
      carriers.outerPopular (family.graphRetained bin)
        (family.coarseCarrier bin)
  popularPreparation : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinPopularCoarsePreparationData (popularCarrier bin)
  prep : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinCoarsePreparationData (coarse.original bin) :=
      fun bin =>
        PureWZ2SourceFixedBinPopularCoarsePreparationData.toCoarsePreparation
          (popularCoarse := popularCarrier bin)
          (fineWitnesses := family.fineWitnesses bin)
          (coarse.original bin) (popularPreparation bin)
  prep_eq : ∀ bin, prep bin =
    PureWZ2SourceFixedBinPopularCoarsePreparationData.toCoarsePreparation
      (popularCoarse := popularCarrier bin)
      (coarse.original bin) (popularPreparation bin)
  prep_shadow_union : ∀ bin, (prep bin).shadow.union =
    (family.coarseCarrier bin).shading.union ∩
      carriers.outerPopular.popular.heightRegion
  prep_height_region : ∀ bin, (prep bin).shadow.union ⊆
    carriers.outerPopular.popular.heightRegion
  source_popular_volume_le : ∀ bin,
    volume ((family.sourceRetained bin).shading.union ∩
        carriers.outerPopular.popular.shading.union) ≤
      volume (prep bin).shadow.union

/-- Construct the synchronized graph preparations without choosing a good
bin.  No per-bin positivity or volume threshold is claimed here. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData.prepareAllPopularCoarseGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarsePreparationFamilyData
        coarse) := by
  have hcarrier : ∀ bin : {bin // bin ∈ family.line.globalBins},
      Nonempty (PureWZ2SourceFixedBinPopularCoarseCarrierData
        carriers.outerPopular (family.graphRetained bin)
          (family.coarseCarrier bin)) := fun bin =>
    (family.coarseCarrier bin).restrictToOuterPopular
      carriers.outerPopular (family.graphRetained bin)
  let popularCarrier : ∀ bin : {bin // bin ∈ family.line.globalBins},
      PureWZ2SourceFixedBinPopularCoarseCarrierData
        carriers.outerPopular (family.graphRetained bin)
          (family.coarseCarrier bin) := fun bin =>
    Classical.choice (hcarrier bin)
  have hpreparation : ∀ bin : {bin // bin ∈ family.line.globalBins},
      Nonempty (PureWZ2SourceFixedBinPopularCoarsePreparationData
        (popularCarrier bin)) := fun bin =>
    PureWZ2SourceFixedBinPopularCoarseCarrierData.prepareFixedBin
      (fineWitnesses := family.fineWitnesses bin)
      (popularCarrier bin) (coarse.original bin) hgraphOne hheightAbsorb
  let popularPreparation : ∀ bin : {bin // bin ∈ family.line.globalBins},
      PureWZ2SourceFixedBinPopularCoarsePreparationData
        (popularCarrier bin) := fun bin =>
    Classical.choice (hpreparation bin)
  let prep : ∀ bin : {bin // bin ∈ family.line.globalBins},
      PureWZ2SourceFixedBinCoarsePreparationData (coarse.original bin) :=
    fun bin =>
      PureWZ2SourceFixedBinPopularCoarsePreparationData.toCoarsePreparation
        (popularCoarse := popularCarrier bin)
        (fineWitnesses := family.fineWitnesses bin)
        (coarse.original bin) (popularPreparation bin)
  exact ⟨{
    popularCarrier := popularCarrier
    popularPreparation := popularPreparation
    prep := prep
    prep_eq := fun _ => rfl
    prep_shadow_union := fun bin =>
      (popularPreparation bin).shadow_union
    prep_height_region := fun bin =>
      (popularPreparation bin).shadow_height_region
    source_popular_volume_le := fun bin => by
      have h := (popularCarrier bin).source_volume_lower
      have hshading : (family.graphRetained bin).shading =
          (family.sourceRetained bin).shading := by
        rw [family.graphRetained_eq bin]
        simp only [
          PureWZ2SourceHorizontalFixedBinResidueShadingData.withPopularGraphFixedBin]
      have hshadow : (prep bin).shadow =
          (popularCarrier bin).shading := by
        exact (popularPreparation bin).shadow_eq
      calc
        volume ((family.sourceRetained bin).shading.union ∩
            carriers.outerPopular.popular.shading.union) =
            volume ((family.graphRetained bin).shading.union ∩
              carriers.outerPopular.popular.shading.union) := by
          rw [hshading]
        _ ≤ volume (popularCarrier bin).shading.union := h
        _ = volume (prep bin).shadow.union := by
          rw [hshadow]
  }⟩

/-- The synchronized coarse graph dominates, bin by bin, the corresponding
outer-popular source carrier. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarsePreparationFamilyData.aggregate_source_popular_volume_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (popularCoarse :
      PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarsePreparationFamilyData
        coarse) :
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume ((family.sourceRetained bin).shading.union ∩
          carriers.outerPopular.popular.shading.union)) ≤
      ∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (popularCoarse.prep bin).shadow.union := by
  exact Finset.sum_le_sum fun bin _ =>
    popularCoarse.source_popular_volume_le bin

/-- Whole-cell synchronized preparations over every global bin.  The coarse
cells are selected by meeting the complete source-cell envelope, rather than
by an exact pointwise height cut. -/
structure PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family) where
  envelope : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
      carriers.outerPopular (family.graphRetained bin)
        (family.coarseCarrier bin)
  prep : ∀ bin : {bin // bin ∈ family.line.globalBins},
    PureWZ2SourceFixedBinCoarsePreparationData (coarse.original bin)
  prep_shadow : ∀ bin, (prep bin).shadow = (envelope bin).shading
  point_near_height_region : ∀ bin point, point ∈ (prep bin).shadow.union →
    ∃ anchor ∈ carriers.outerPopular.popular.heightRegion,
      dist point anchor < 2 * rho + 2 * delta
  parent_cells_volume_lower : ∀ bin,
    (((family.residue bin).selected.card : ENNReal) *
        volume (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0))) ≤
      volume (prep bin).shadow.union

/-- Construct the all-bin whole-cell envelope and prepare each resulting
graph on the original source slope. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData.prepareAllPopularCoarseCellEnvelopes
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    (coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
        coarse) := by
  have hwindowOuter : carriers.outerPopular.windowed.shading.union ⊆
      carriers.outerPopular.shading.union := by
    rw [carriers.outerPopular.windowed_shading]
  have henvelope : ∀ bin : {bin // bin ∈ family.line.globalBins},
      Nonempty (PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
        carriers.outerPopular (family.graphRetained bin)
          (family.coarseCarrier bin)) := fun bin =>
    (family.coarseCarrier bin).envelopeOuterPopularCells
      carriers.outerPopular (family.graphRetained bin) hwindowOuter
  let envelope : ∀ bin : {bin // bin ∈ family.line.globalBins},
      PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData
        carriers.outerPopular (family.graphRetained bin)
          (family.coarseCarrier bin) := fun bin =>
    Classical.choice (henvelope bin)
  have hprep : ∀ bin : {bin // bin ∈ family.line.globalBins},
      ∃ prep : PureWZ2SourceFixedBinCoarsePreparationData
          (coarse.original bin),
        prep.shadow = (envelope bin).shading := fun bin =>
    PureWZ2SourceFixedBinPopularCoarseCellEnvelopeData.prepareFixedBin
      (envelope := envelope bin) (fineWitnesses := family.fineWitnesses bin)
      (coarse.original bin)
      hgraphOne hheightAbsorb
  let prep : ∀ bin : {bin // bin ∈ family.line.globalBins},
      PureWZ2SourceFixedBinCoarsePreparationData (coarse.original bin) :=
    fun bin => (hprep bin).choose
  have hshadow : ∀ bin, (prep bin).shadow = (envelope bin).shading :=
    fun bin => (hprep bin).choose_spec
  exact ⟨{
    envelope := envelope
    prep := prep
    prep_shadow := hshadow
    point_near_height_region := by
      intro bin point hpoint
      apply (envelope bin).point_near_height_region point
      rw [← hshadow bin]
      exact hpoint
    parent_cells_volume_lower := by
      intro bin
      calc
        _ ≤ volume (envelope bin).shading.union :=
          (envelope bin).parent_cells_volume_lower
        _ = volume (prep bin).shadow.union := by rw [hshadow bin]
  }⟩

/-- The fixed-slice count controls the synchronized whole-cell envelopes.
The right scale is one literal `rho`-cube per retained parent; no claim that
the full second balanced cell mass survives the height synchronization is
made here. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData.aggregate_graph_volume_supply_le
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (envelopes :
      PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
        coarse) :
    carriers.outerPopular.popularWindow.volumeSupply *
        volume (wz1PaperGridCube rho (0, 0, 0)) ≤
      pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (envelopes.prep bin).shadow.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let parentBound : ENNReal :=
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal)
  let thinning : ENNReal := 23040
  let window := carriers.outerPopular.windowed
  have hwindowSupply : carriers.outerPopular.popularWindow.volumeSupply ≤
      volume window.shading.union := by
    calc
      carriers.outerPopular.popularWindow.volumeSupply ≤
          window.volumeSupply := by
        dsimp only [window]
        rw [carriers.outerPopular.popularWindow_supply,
          carriers.outerPopular.windowed_supply]
        exact carriers.outerPopular.volume_lower
      _ ≤ volume window.shading.union := window.volume_lower
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      window.subshading.union_subset hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hsliceArea :
      volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) ≤
        (family.line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      window.shading source.extremal.delta_pos hball family.line.lineHeight
    simpa [family.line.sliceCells_eq, sliceDisk] using hraw
  have hthicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr family.line.rho_pos
    nlinarith [family.line.rho_pos]
  have hwindowToSlice : volume window.shading.union ≤
      volume (wz1Lemma23PlanarSlice window.shading.union
        family.line.lineHeight) * sliceThickness := by
    apply (ENNReal.div_le_iff hthicknessPos.ne' ENNReal.ofReal_ne_top).mp
    simpa [sliceThickness] using family.line.slice_area_lower
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  have hbin : ∀ bin : {bin // bin ∈ family.line.globalBins},
      ((family.core bin).heavyCells.card : ENNReal) * cubeVolume ≤
        parentBound * thinning *
          volume (envelopes.prep bin).shadow.union := by
    intro bin
    have hheavy : ((family.core bin).heavyCells.card : ENNReal) ≤
        parentBound * ((family.parents bin).parents.card : ENNReal) := by
      dsimp only [parentBound]
      exact_mod_cast (family.parents bin).heavy_card
    have hparentNat : (family.parents bin).parents.card ≤
        23040 * (family.residue bin).selected.card := by
      calc
        (family.parents bin).parents.card ≤
            45 * (family.selection bin).selected.card :=
          (family.selection bin).parent_card
        _ ≤ 45 * (512 * (family.residue bin).selected.card) := by
          gcongr
          exact (family.residue bin).card_fraction
        _ = 23040 * (family.residue bin).selected.card := by ring
    have hparent : ((family.parents bin).parents.card : ENNReal) ≤
        thinning * ((family.residue bin).selected.card : ENNReal) := by
      dsimp only [thinning]
      exact_mod_cast hparentNat
    calc
      ((family.core bin).heavyCells.card : ENNReal) * cubeVolume ≤
          (parentBound * ((family.parents bin).parents.card : ENNReal)) *
            cubeVolume := by gcongr
      _ ≤ (parentBound *
          (thinning * ((family.residue bin).selected.card : ENNReal))) *
            cubeVolume := by gcongr
      _ = parentBound * thinning *
          (((family.residue bin).selected.card : ENNReal) *
            volume (wz1PaperGridCube twoScale.rhoRequested.1 (0, 0, 0))) := by
        rw [twoScale.rhoRequested_eq]
        dsimp only [cubeVolume]
        ring
      _ ≤ parentBound * thinning *
          volume (envelopes.prep bin).shadow.union := by
        gcongr
        exact envelopes.parent_cells_volume_lower bin
  have hslice : (family.line.sliceCells.card : ENNReal) * cubeVolume ≤
      parentBound * thinning *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (envelopes.prep bin).shadow.union := by
    rw [show (family.line.sliceCells.card : ENNReal) =
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          ((family.core bin).heavyCells.card : ENNReal) by
      exact_mod_cast family.slice_card]
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ bin : {bin // bin ∈ family.line.globalBins},
          parentBound * thinning *
            volume (envelopes.prep bin).shadow.union :=
        Finset.sum_le_sum fun bin _ => hbin bin
      _ = parentBound * thinning *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            volume (envelopes.prep bin).shadow.union := by
        rw [Finset.mul_sum]
  calc
    carriers.outerPopular.popularWindow.volumeSupply * cubeVolume ≤
        volume window.shading.union * cubeVolume := by gcongr
    _ ≤ (volume (wz1Lemma23PlanarSlice window.shading.union
          family.line.lineHeight) * sliceThickness) * cubeVolume := by gcongr
    _ ≤ (((family.line.sliceCells.card : ENNReal) * sliceDisk) *
          sliceThickness) * cubeVolume := by gcongr
    _ = sliceThickness * sliceDisk *
        ((family.line.sliceCells.card : ENNReal) * cubeVolume) := by ring
    _ ≤ sliceThickness * sliceDisk *
        (parentBound * thinning *
          ∑ bin : {bin // bin ∈ family.line.globalBins},
            volume (envelopes.prep bin).shadow.union) := by gcongr
    _ = pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta *
        ∑ bin : {bin // bin ∈ family.line.globalBins},
          volume (envelopes.prep bin).shadow.union := by
      simp [pureWZ2OrdinaryAllBinCoarseVolumeCost, sliceThickness,
        sliceDisk, parentBound, thinning]
      ring

/-- Cancel the finite all-bin cost from the synchronized whole-cell budget. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData.graph_budget_of_scaled
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (envelopes :
      PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
        coarse)
    (hscaled :
      (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
        carriers.outerPopular.popularWindow.volumeSupply *
          volume (wz1PaperGridCube rho (0, 0, 0))) :
    2 * ((family.line.globalBins.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss)) ≤
      ∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (envelopes.prep bin).shadow.union := by
  let cost := pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta
  have hcostPos : 0 < cost := by
    dsimp only [cost, pureWZ2OrdinaryAllBinCoarseVolumeCost]
    have hrho : 0 < rho := family.line.rho_pos
    have hdelta : 0 < delta := source.extremal.delta_pos
    have hparent :
        0 < (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) := by
      simp [pureWZ2SourceFixedLineParentFiberBound,
        pureWZ2SourceFixedLineParentYBound]
    positivity
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost, pureWZ2OrdinaryAllBinCoarseVolumeCost]
    repeat' apply ENNReal.mul_ne_top
    all_goals simp [Kakeya.realRpowENN]
  apply (ENNReal.mul_le_mul_iff_right hcostPos.ne' hcostTop).mp
  calc
    cost * (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) =
        (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) * cost := by ring
    _ ≤ carriers.outerPopular.popularWindow.volumeSupply *
          volume (wz1PaperGridCube rho (0, 0, 0)) := hscaled
    _ ≤ cost * ∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (envelopes.prep bin).shadow.union :=
      envelopes.aggregate_graph_volume_supply_le

def pureWZ2OrdinaryPaperOrderGoodPopularCoarseCellEnvelopeGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (envelopes :
      PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
        coarse)
    (volumeLoss : ℝ) :
    Finset {bin // bin ∈ family.line.globalBins} :=
  Finset.univ.filter fun bin =>
    Kakeya.realRpowENN (envelopes.prep bin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (envelopes.prep bin).shadow.union

structure PureWZ2OrdinaryPaperOrderGoodPopularCoarseCellEnvelopeGlobalBinFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (envelopes :
      PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
        coarse)
    (volumeLoss : ℝ) where
  selected : Finset {bin // bin ∈ family.line.globalBins} :=
    pureWZ2OrdinaryPaperOrderGoodPopularCoarseCellEnvelopeGlobalBins
      envelopes volumeLoss
  selected_eq : selected =
    pureWZ2OrdinaryPaperOrderGoodPopularCoarseCellEnvelopeGlobalBins
      envelopes volumeLoss
  selected_nonempty : selected.Nonempty
  volume_lower : ∀ bin ∈ selected,
    Kakeya.realRpowENN (envelopes.prep bin).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume (envelopes.prep bin).shadow.union
  total_volume_le :
    (∑ bin : {bin // bin ∈ family.line.globalBins},
        volume (envelopes.prep bin).shadow.union) ≤
      2 * ∑ bin ∈ selected, volume (envelopes.prep bin).shadow.union

/-- Select a nonempty family of ready whole-cell-envelope graphs from the
honest aggregate budget. -/
theorem PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData.selectGoodGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierAtWindowData sourceWindow}
    {family :
      PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData carriers}
    {coarse :
      PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData family}
    (envelopes :
      PureWZ2OrdinaryPaperOrderGlobalBinPopularCoarseCellEnvelopeFamilyData
        coarse)
    (hscaled :
      (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
        carriers.outerPopular.popularWindow.volumeSupply *
          volume (wz1PaperGridCube rho (0, 0, 0))) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderGoodPopularCoarseCellEnvelopeGlobalBinFamilyData
        envelopes volumeLoss) := by
  let bins := (Finset.univ : Finset {bin // bin ∈ family.line.globalBins})
  let supply : {bin // bin ∈ family.line.globalBins} → ENNReal := fun bin =>
    volume (envelopes.prep bin).shadow.union
  let threshold := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  have hbad : 2 * ((bins.card : ENNReal) * threshold) ≤
      ∑ bin ∈ bins, supply bin * 1 := by
    have h := envelopes.graph_budget_of_scaled hscaled
    simpa [bins, supply, threshold] using h
  have hthresholdTop : threshold ≠ ⊤ := by
    simp [threshold, Kakeya.realRpowENN]
  have hhalf := finset_good_weighted_supply_retains_half
    bins supply 1 threshold hthresholdTop hbad
  let selected := bins.filter fun bin => threshold ≤ supply bin
  have htotalPos : 0 < ∑ bin ∈ bins, supply bin := by
    have hthresholdPos : 0 < threshold := by
      apply ENNReal.ofReal_pos.mpr
      apply Real.rpow_pos_of_pos
      have hrho : 0 < rho := family.line.rho_pos
      positivity
    have hbinsPos : 0 < (bins.card : ENNReal) := by
      have hbinsNonempty : bins.Nonempty := by
        refine ⟨⟨family.line.lineBin, family.line.lineBin_mem⟩, ?_⟩
        simp [bins]
      exact_mod_cast hbinsNonempty.card_pos
    have hleftPos : 0 < 2 * ((bins.card : ENNReal) * threshold) := by
      positivity
    exact hleftPos.trans_le (by simpa using hbad)
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hleZero : (∑ bin ∈ bins, supply bin) ≤ 0 := by
      simpa [selected, hselectedEmpty] using hhalf
    exact (not_le_of_gt htotalPos) hleZero
  exact ⟨{
    selected := selected
    selected_eq := by
      ext bin
      simp [selected, bins, supply, threshold,
        pureWZ2OrdinaryPaperOrderGoodPopularCoarseCellEnvelopeGlobalBins,
        (envelopes.prep bin).graphScale_eq]
    selected_nonempty := hselectedNonempty
    volume_lower := by
      intro bin hbin
      have hgood := (Finset.mem_filter.mp hbin).2
      simpa [threshold, supply,
        (envelopes.prep bin).graphScale_eq] using hgood
    total_volume_le := by
      simpa [selected, bins, supply, threshold,
        (envelopes.prep _).graphScale_eq] using hhalf
  }⟩

end Kakeya.Assouad

end
