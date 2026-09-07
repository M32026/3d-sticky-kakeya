import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAnchorGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalNormalFirst
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalBinPackage

/-!
# Source-slope local-bin package

The local graph is built from the original source plane map on the final
residue shadow.  The strong second-stage sources are used only through the
already extracted first-component lower bound.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma sourceHorizontal_nat_le_ceil_add_one
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

theorem PureWZ2SourceHorizontalFixedBinGraphParentData.localBinsFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    (graphParents : PureWZ2SourceHorizontalFixedBinGraphParentData prep)
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    (normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
      (eta := eta) fineWitnesses) :
    Nonempty
      (WZ1Lemma23LocalBinPackage
        (rho := prep.graphScale) (sigma := sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))
        prep.windowed.global.cells) := by
  let cells := prep.windowed.global.cells
  let C : ENNReal := 10 * Kakeya.realRpowENN delta (-inputLoss)
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
  let anchor : ℝ → Point3 := fun y =>
    if hy : y ∈ sample then
      graphParents.anchorForFixedBin fineWitnesses (cellFor y hy)
        (hcellForMem y hy)
    else 0
  have hanchorEq :
      ∀ y (hy : y ∈ sample),
        anchor y = graphParents.anchorForFixedBin fineWitnesses (cellFor y hy)
          (hcellForMem y hy) := by
    intro y hy
    simp only [anchor, dif_pos hy]
  have hanchorMem : ∀ y (hy : y ∈ sample),
      anchor y ∈ prep.ambientShadow.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact graphParents.anchorFor_mem_ambientShadowFixedBin
      fineWitnesses (cellFor y hy) (hcellForMem y hy)
  have hnormalEq : ∀ y (hy : y ∈ sample),
      prep.ambientLocalGrains.planeMap (anchor y) =
        fineWitnesses.normal (graphParents.parentOf (cellFor y hy)) := by
    intro y hy
    let cell := cellFor y hy
    have hcell : cell ∈ cells := hcellForMem y hy
    let parent := graphParents.parentOf cell
    have hparent : parent ∈ residue.selected :=
      graphParents.parent_mem cell hcell
    have hpaper : anchor y ∈ retained.shading.union := by
      rw [← prep.ambientShadow_union]
      exact hanchorMem y hy
    rw [prep.ambientPlaneMap_eq_on_paper ⟨anchor y, hanchorMem y hy⟩]
    rw [prep.localPaper_planeMap_eq ⟨anchor y, hpaper⟩]
    rw [fineWitnesses.normal_eq parent hparent]
    apply congrArg source.localGrains.planeMap
    apply Subtype.ext
    exact hanchorEq y hy
  have hvertical : ∀ y ∈ sample,
      |prep.ambientLocalGrains.planeMap (anchor y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    exact prep.planeMap_vertical_bound (anchor y) (hanchorMem y hy)
  have hfirst : ∀ y ∈ sample,
      1 / 4 ≤ |prep.ambientLocalGrains.planeMap (anchor y) (0 : Fin 3)| := by
    intro y hy
    rw [hnormalEq y hy]
    exact normalFirst.normal_first
      (graphParents.parentOf (cellFor y hy))
      (graphParents.parent_mem _ (hcellForMem y hy))
  have hnormalDist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (prep.ambientLocalGrains.planeMap (anchor y₁))
            (prep.ambientLocalGrains.planeMap (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂) := by
    intro y₁ hy₁ y₂ hy₂
    have hpaper₁ : anchor y₁ ∈ retained.shading.union := by
      rw [← prep.ambientShadow_union]
      exact hanchorMem y₁ hy₁
    have hpaper₂ : anchor y₂ ∈ retained.shading.union := by
      rw [← prep.ambientShadow_union]
      exact hanchorMem y₂ hy₂
    rw [prep.ambientPlaneMap_eq_on_paper ⟨anchor y₁, hanchorMem y₁ hy₁⟩]
    rw [prep.ambientPlaneMap_eq_on_paper ⟨anchor y₂, hanchorMem y₂ hy₂⟩]
    have hlip := prep.localPaper.planeMap_lipschitz.dist_le_mul
      ⟨anchor y₁, hpaper₁⟩ ⟨anchor y₂, hpaper₂⟩
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hlip
  have hanchorDist :
      ∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
        dist (anchor y₁) (anchor y₂) ≤ 4 * |y₁ - y₂| := by
    intro y₁ hy₁ y₂ hy₂
    rw [hanchorEq y₁ hy₁, hanchorEq y₂ hy₂]
    have hdist := graphParents.anchorFor_distFixedBin fineWitnesses
      (cellFor y₁ hy₁) (hcellForMem y₁ hy₁)
      (cellFor y₂ hy₂) (hcellForMem y₂ hy₂)
    simpa [hcellForValue y₁ hy₁, hcellForValue y₂ hy₂] using hdist
  rcases wz1_lemma23_local_graph_extension_of_distortion
      sample anchor prep.ambientLocalGrains.planeMap
      hvertical hfirst hnormalDist hanchorDist with
    ⟨g, hgLipschitz, hgBounded, hgSample⟩
  have hySample :
      ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
        wz1Lemma23SnappedYValue prep.graphScale y ∈ sample := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨cell, hcell, hcellY⟩
    exact Finset.mem_image.mpr
      ⟨cell, hcell, congrArg
        (wz1Lemma23SnappedYValue prep.graphScale) hcellY⟩
  have hanchorLayer :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        anchor (wz1Lemma23SnappedYValue prep.graphScale y) ∈
          prep.ambientShadow.union := by
    intro y hy
    exact hanchorMem _ (hySample y hy)
  have hverticalLayer :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        |prep.ambientLocalGrains.planeMap
          (anchor (wz1Lemma23SnappedYValue prep.graphScale y))
            (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    exact hvertical _ (hySample y hy)
  have hfirstLayer :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        1 / 4 ≤ |prep.ambientLocalGrains.planeMap
          (anchor (wz1Lemma23SnappedYValue prep.graphScale y))
            (0 : Fin 3)| := by
    intro y hy
    exact hfirst _ (hySample y hy)
  have hgraphLayer :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        g (wz1Lemma23SnappedYValue prep.graphScale y) =
          prep.ambientLocalGrains.planeMap
              (anchor (wz1Lemma23SnappedYValue prep.graphScale y))
                (2 : Fin 3) /
            prep.ambientLocalGrains.planeMap
              (anchor (wz1Lemma23SnappedYValue prep.graphScale y))
                (0 : Fin 3) := by
    intro y hy
    exact hgSample _ (hySample y hy)
  have hlayerBall :
      ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
        ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
          dist
              (wz1Lemma23CellRepresentative prep.ambientShadow prep.graphScale_pos
                ⟨idx, prep.activeCells_subset_ambientFixedBin
                  (prep.windowed.global.cells_active hidx)⟩)
              (anchor (wz1Lemma23SnappedYValue prep.graphScale y)) ≤
            Real.sqrt prep.graphScale := by
    intro y hy idx hidx hidxY
    have hs := hySample y hy
    let value := wz1Lemma23SnappedYValue prep.graphScale y
    let chosen := cellFor value hs
    have hchosenMem : chosen ∈ cells := hcellForMem value hs
    have hchosenYValue :
        wz1Lemma23SnappedYValue prep.graphScale chosen.2.1 =
          wz1Lemma23SnappedYValue prep.graphScale y := by
      simpa [value] using hcellForValue value hs
    have hchosenY : chosen.2.1 = y :=
      wz1Lemma23SnappedYValue_injective prep.graphScale_pos hchosenYValue
    have hparent : graphParents.parentOf chosen = graphParents.parentOf idx :=
      graphParents.same_y_parent chosen hchosenMem idx hidx
        (hchosenY.trans hidxY.symm)
    have hanchorSame :
        graphParents.anchorForFixedBin fineWitnesses chosen hchosenMem =
          graphParents.anchorForFixedBin fineWitnesses idx hidx := by
      simp only [PureWZ2SourceHorizontalFixedBinGraphParentData.anchorForFixedBin, hparent]
    rw [hanchorEq value hs, hanchorSame]
    exact graphParents.canonical_rep_dist_anchorFixedBin fineWitnesses idx hidx
  let X : ENNReal := 19 * C *
    Kakeya.realRpowENN
      (Real.sqrt prep.graphScale / prep.graphScale) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num)
          (by simp [Kakeya.realRpowENN])))
      (by simp [Kakeya.realRpowENN])
  let localBinBound := Nat.ceil X.toReal + 1
  have hlocalBins :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        (wz1Lemma23SnappedLocalBinsAt
          prep.graphScale g cells y).card ≤ localBinBound := by
    intro y hy
    have hactiveAmbient :
        cells ⊆ wz1Lemma23ActiveCells prep.ambientShadow
          prep.graphScale prep.graphScale_pos := by
      intro idx hidx
      exact prep.activeCells_subset_ambientFixedBin
        (prep.windowed.global.cells_active hidx)
    have hbins := wz1_lemma23_actual_local_bins_at
      prep.ambientShadow C prep.ambientLocalGrains cells g
      (fun y => anchor (wz1Lemma23SnappedYValue prep.graphScale y))
      prep.graphScale_pos prep.sourceScale_le_graphScale prep.graphScale_one
      hactiveAmbient hanchorLayer
      hverticalLayer hfirstLayer hgraphLayer hlayerBall y hy
    exact sourceHorizontal_nat_le_ceil_add_one hX
      (by simpa [X] using hbins)
  exact ⟨{
    g := g
    g_lipschitz := hgLipschitz
    g_bounded := hgBounded
    localBinBound := localBinBound
    localBinBound_eq := rfl
    local_bins := hlocalBins
  }⟩


/-- Compatibility wrapper for the former maximal-bin local-bin API. -/
theorem PureWZ2SourceHorizontalGraphParentData.localBins
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    (graphParents : PureWZ2SourceHorizontalGraphParentData prep)
    (fineWitnesses : PureWZ2SourceHorizontalFineWitnessData retained)
    (normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) fineWitnesses) :
    Nonempty (WZ1Lemma23LocalBinPackage (rho := prep.graphScale) (sigma := sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) prep.windowed.global.cells) :=
  PureWZ2SourceHorizontalFixedBinGraphParentData.localBinsFixedBin
    graphParents fineWitnesses normalFirst

end Kakeya.Assouad
