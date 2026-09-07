import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseGraphParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseNormalFirst
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HeterogeneousLocalBins
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalGraphExtension
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalBinPackage

/-!
# Heterogeneous local bins on the genuine coarse carrier

Graph-cell representatives come from the first-sticky coarse shading.  Every
snapped y-layer uses the original fine witness attached to its selected
side-`sqrt rho` parent.  Individual graph cells retain their side-`rho` owner
cell only for the coarse-to-fine projection perturbation.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma coarseLocalBins_nat_le_ceil_add_one
    {n : ℕ} {X : ENNReal} (hX : X ≠ ⊤)
    (hn : (n : ENNReal) ≤ X) :
    n ≤ Nat.ceil X.toReal + 1 := by
  have hreal : (n : ℝ) ≤ X.toReal := by
    rw [← ENNReal.toReal_natCast n]
    exact (ENNReal.toReal_le_toReal
      (ENNReal.natCast_ne_top n) hX).mpr hn
  have hceil : n ≤ Nat.ceil X.toReal := by
    exact_mod_cast hreal.trans (Nat.le_ceil X.toReal)
  omega

theorem PureWZ2SourceFixedBinCoarseGraphParentData.localBinsFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
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
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep)
    (normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hconstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty
      (WZ1Lemma23LocalBinPackage
        (rho := prep.graphScale) (sigma := sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))
        prep.windowed.global.cells) := by
  let cells := prep.windowed.global.cells
  let sample : Finset ℝ := cells.image fun cell =>
    wz1Lemma23SnappedYValue prep.graphScale cell.2.1
  have hcellExists :
      ∀ y (hy : y ∈ sample),
        ∃ cell ∈ cells,
          wz1Lemma23SnappedYValue prep.graphScale cell.2.1 = y := by
    intro y hy
    simpa [sample] using Finset.mem_image.mp hy
  let cellFor : ∀ y, y ∈ sample → ℤ × ℤ × ℤ := fun y hy =>
    Classical.choose (hcellExists y hy)
  have hcellForMem :
      ∀ y (hy : y ∈ sample), cellFor y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).1
  have hcellForValue :
      ∀ y (hy : y ∈ sample),
        wz1Lemma23SnappedYValue prep.graphScale (cellFor y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).2
  have hySample :
      ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
        wz1Lemma23SnappedYValue prep.graphScale y ∈ sample := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨cell, hcell, hcellY⟩
    exact Finset.mem_image.mpr
      ⟨cell, hcell, congrArg
        (wz1Lemma23SnappedYValue prep.graphScale) hcellY⟩
  let anchor : ℝ → Point3 := fun y =>
    if hy : y ∈ sample then
      fineWitnesses.witness
        (graphParents.parentOf (cellFor y hy))
    else 0
  let extension : Point3 → Point3 :=
    Classical.choose source.localGrains.exists_ambient_extension
  have hextensionEq :
      ∀ point : {point : Point3 // point ∈ source.shading.union},
        extension point = source.localGrains.planeMap point :=
    (Classical.choose_spec source.localGrains.exists_ambient_extension).2
  have hanchorEq :
      ∀ y (hy : y ∈ sample),
        anchor y = fineWitnesses.witness
          (graphParents.parentOf (cellFor y hy)) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hparentFor :
      ∀ y (hy : y ∈ sample),
        graphParents.parentOf (cellFor y hy) ∈
          residue.selected := by
    intro y hy
    exact graphParents.parent_mem _ (hcellForMem y hy)
  have hnormalAt :
      ∀ y (hy : y ∈ sample),
        extension (anchor y) = fineWitnesses.normal
          (graphParents.parentOf (cellFor y hy)) := by
    intro y hy
    rw [hanchorEq y hy]
    exact (hextensionEq
      ⟨fineWitnesses.witness
          (graphParents.parentOf (cellFor y hy)),
        fineWitnesses.witness_mem_source _
          (hparentFor y hy)⟩).trans
      (fineWitnesses.normal_eq
        (graphParents.parentOf (cellFor y hy))
        (hparentFor y hy)).symm
  have hnormalDist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (extension (anchor y₁)) (extension (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂) := by
    intro y₁ hy₁ y₂ hy₂
    rw [hnormalAt y₁ hy₁, hnormalAt y₂ hy₂,
      hanchorEq y₁ hy₁, hanchorEq y₂ hy₂]
    exact fineWitnesses.normal_dist
      _ (hparentFor y₁ hy₁) _ (hparentFor y₂ hy₂)
  have hanchorDist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (anchor y₁) (anchor y₂) ≤ 4 * |y₁ - y₂| := by
    intro y₁ hy₁ y₂ hy₂
    rw [hanchorEq y₁ hy₁, hanchorEq y₂ hy₂]
    simpa only
        [PureWZ2SourceFixedBinCoarseGraphParentData.anchorFor,
          hcellForValue y₁ hy₁, hcellForValue y₂ hy₂] using
      graphParents.anchorFor_dist
        (cellFor y₁ hy₁) (hcellForMem y₁ hy₁)
        (cellFor y₂ hy₂) (hcellForMem y₂ hy₂)
  rcases wz1_lemma23_local_graph_extension_of_distortion
      sample anchor extension
      (by
        intro y hy
        rw [hnormalAt y hy]
        exact fineWitnesses.normal_vertical _ (hparentFor y hy))
      (by
        intro y hy
        rw [hnormalAt y hy]
        exact normalFirst.normal_first _ (hparentFor y hy))
      hnormalDist hanchorDist with
    ⟨g, hgLipschitz, hgBounded, hgSample⟩
  let anchorCell : ℤ → (ℤ × ℤ × ℤ) := fun y =>
    if hy : y ∈ wz1Lemma23SnappedYLayers cells then
      graphParents.parentOf
        (cellFor (wz1Lemma23SnappedYValue prep.graphScale y)
          (hySample y hy))
    else (0, 0, 0)
  have hanchorCellEq :
      ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
        anchorCell y = graphParents.parentOf
          (cellFor (wz1Lemma23SnappedYValue prep.graphScale y)
            (hySample y hy)) := by
    intro y hy
    simp only [anchorCell, dif_pos hy]
  have hcoarseNormalEq :
      ∀ parent (hparent : parent ∈ residue.selected),
        fineWitnesses.coarseWitnesses.normal
            (retained.cellFor parent) =
          fineWitnesses.normal parent := by
    intro parent hparent
    rw [fineWitnesses.coarseWitnesses.normal_eq
        (retained.cellFor parent)
        (fineWitnesses.cell_active parent hparent),
      fineWitnesses.normal_eq parent hparent]
    apply congrArg source.localGrains.planeMap
    apply Subtype.ext
    exact (fineWitnesses.witness_eq parent hparent).symm
  let coarseFine : PureWZ2Lemma23CoarseFineLocalBinData
      fineWitnesses.coarseWitnesses prep.graphScale cells g := {
    coarseRepresentative := graphParents.representative
    coarse_representative_mem := by
      intro cell hcell
      have hshadow := graphParents.representative_mem cell hcell
      have hcarrier := prep.shadow_union_subset hshadow
      rw [carrier.union_eq] at hcarrier
      exact hcarrier.1
    coarse_representative_index := graphParents.representative_index
    ownerCell := graphParents.ownerCell
    owner_active := graphParents.owner_active
    representative_mem_owner := graphParents.representative_mem_owner
    anchorCell := fun y => retained.cellFor (anchorCell y)
    anchor_active := by
      intro y hy
      exact fineWitnesses.cell_active _ (by
        rw [hanchorCellEq y hy]
        exact graphParents.parent_mem _ (hcellForMem _ (hySample y hy)))
    layer_fine_ball := by
      intro y hy cell hcell hcellY
      let sampleY := wz1Lemma23SnappedYValue prep.graphScale y
      have hs := hySample y hy
      have hchosenY : (cellFor sampleY hs).2.1 = y :=
        wz1Lemma23SnappedYValue_injective prep.graphScale_pos
          (by simpa [sampleY] using hcellForValue sampleY hs)
      have hparentEq := graphParents.same_y_parent
        (cellFor sampleY hs) (hcellForMem sampleY hs) cell hcell
        (hchosenY.trans hcellY.symm)
      have hfirst := graphParents.owner_witness_mem_parent cell hcell
      have hsecond := fineWitnesses.witness_mem_parent
        (graphParents.parentOf (cellFor sampleY hs))
        (hparentFor sampleY hs)
      have hanchorEqParent : anchorCell y = graphParents.parentOf cell := by
        rw [hanchorCellEq y hy, hparentEq]
      have hanchorWitness :
          fineWitnesses.coarseWitnesses.witness
              (retained.cellFor (anchorCell y)) =
            fineWitnesses.witness (anchorCell y) := by
        rw [fineWitnesses.witness_eq (anchorCell y) (by
          rw [hanchorEqParent]
          exact graphParents.parent_mem cell hcell)]
      rw [hanchorWitness]
      have hsecond' : fineWitnesses.witness (anchorCell y) ∈
          wz1PaperGridCube twoScale.sqrtRequested.1
            (graphParents.parentOf cell) := by
        rw [hanchorEqParent]
        exact fineWitnesses.witness_mem_parent _
          (graphParents.parent_mem cell hcell)
      have hdist := wz1_paper_grid_cube_diameter_lt_two_rho
        twoScale.fine.coarse_extremal.delta_pos hfirst hsecond'
      exact (le_of_lt hdist).trans (by
        rw [prep.graphScale_sqrt]
        nlinarith [twoScale.fine.coarse_extremal.delta_pos])
    normal_first := by
      intro y hy
      have hparent : anchorCell y ∈ residue.selected := by
        rw [hanchorCellEq y hy]
        exact graphParents.parent_mem _ (hcellForMem _ (hySample y hy))
      rw [hcoarseNormalEq (anchorCell y) hparent]
      exact normalFirst.normal_first _ hparent
    graph_eq := by
      intro y hy
      let sampleY := wz1Lemma23SnappedYValue prep.graphScale y
      have hs := hySample y hy
      have hsample := hgSample sampleY hs
      rw [hnormalAt sampleY hs] at hsample
      have hparent : anchorCell y ∈ residue.selected := by
        rw [hanchorCellEq y hy]
        exact graphParents.parent_mem _ (hcellForMem _ hs)
      rw [hcoarseNormalEq (anchorCell y) hparent]
      rw [hanchorCellEq y hy]
      exact hsample
  }
  let X : ENNReal := 19 *
    (10 * Kakeya.realRpowENN rho (-middleLoss)) *
    Kakeya.realRpowENN
      (Real.sqrt prep.graphScale / prep.graphScale) (1 - sigma)
  have hXtop : X ≠ ⊤ := by
    dsimp only [X]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN])))
      (by simp [Kakeya.realRpowENN])
  let localBinBound := Nat.ceil X.toReal + 1
  refine ⟨{
    g := g
    g_lipschitz := hgLipschitz
    g_bounded := hgBounded
    localBinBound := localBinBound
    localBinBound_eq := rfl
    local_bins := ?_
  }⟩
  intro y hy
  have hbins := coarseFine.local_bins_at hbridge prep.rho_le_graphScale
    prep.graphScale_one y hy
  have hbound :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN
            (Real.sqrt prep.graphScale / prep.graphScale) (1 - sigma) ≤
        X := by
    dsimp only [X]
    gcongr
  have henn := hbins.trans hbound
  exact coarseLocalBins_nat_le_ceil_add_one hXtop henn

/-- Backwards-compatible maximal-bin constructor for local graph bins. -/
theorem PureWZ2SourceFixedLineCoarseGraphParentData.localBins
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep)
    (normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) carriers.fineWitnesses)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hconstant :
      35 * (10 * Kakeya.realRpowENN delta (-inputLoss)) ≤
        19 * (10 * Kakeya.realRpowENN rho (-middleLoss))) :
    Nonempty
      (WZ1Lemma23LocalBinPackage
        (rho := prep.graphScale) (sigma := sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss))
        prep.windowed.global.cells) :=
  PureWZ2SourceFixedBinCoarseGraphParentData.localBinsFixedBin
    graphParents normalFirst hbridge hconstant

end Kakeya.Assouad

end
