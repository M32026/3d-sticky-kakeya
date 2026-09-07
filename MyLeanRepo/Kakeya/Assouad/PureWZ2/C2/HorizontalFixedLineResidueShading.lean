import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineYResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineRetainedShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity

/-!
# Whole-cell fixed-line shading on one separated y-residue
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalFixedLineResidueShadingData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    (residue : PureWZ2HorizontalFixedLineYResidueData selection) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.fine.selected twoScale.fine.refined
  selectedRegion : Set Point3 :=
    ⋃ parent ∈ residue.selected,
      wz1PaperGridCube twoScale.sqrtRequested.1 parent
  selectedRegion_eq :
    selectedRegion =
      ⋃ parent ∈ residue.selected,
        wz1PaperGridCube twoScale.sqrtRequested.1 parent
  shading : WZ1PaperTubeShading twoScale.coarse.coarse
  carrier_eq :
    ∀ index, shading.carrier index =
      zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading :
    PureWZ2PaperIsSubshading shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq :
    shading.union = twoScale.fine.refined.union ∩ selectedRegion
  volume_eq :
    MeasureTheory.volume shading.union =
      (residue.selected.card : ENNReal) * twoScale.fine.balanced.cellMass
  volume_fraction :
    MeasureTheory.volume
        (twoScale.fine.refined.union ∩
          ⋃ parent ∈ parents.parents,
            wz1PaperGridCube twoScale.sqrtRequested.1 parent) ≤
      23040 * MeasureTheory.volume shading.union
  commonParentHeight : ℤ
  parent_height_eq :
    ∀ parent ∈ residue.selected, parent.2.2 = commonParentHeight
  union_height :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈
        Set.Ico
          ((commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
          (((commonParentHeight : ℝ) + 1) * twoScale.sqrtRequested.1)

theorem PureWZ2HorizontalFixedLineYResidueData.retainShading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    (residue : PureWZ2HorizontalFixedLineYResidueData selection) :
    Nonempty (PureWZ2HorizontalFixedLineResidueShadingData residue) := by
  let root := twoScale.sqrtRequested.1
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  rcases wz2_paper_subfamily_zero_extension
      twoScale.fine.selected twoScale.fine.refined with
    ⟨zeroExtension⟩
  let selectedRegion : Set Point3 :=
    ⋃ parent ∈ residue.selected, wz1PaperGridCube root parent
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion residue.selected.finite_toSet.countable
      (fun parent _ => wz1PaperGridCube_measurable parent)
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter hregionMeas
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (zeroExtension.ambientShading.subset_body index) }
  have hunion :
      shading.union = twoScale.fine.refined.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hzero, hregion⟩
      have hzeroUnion : point ∈ zeroExtension.ambientShading.union :=
        ⟨index, hzero⟩
      rw [zeroExtension.union_eq] at hzeroUnion
      exact ⟨hzeroUnion, hregion⟩
    · rintro ⟨hfine, hregion⟩
      rw [← zeroExtension.union_eq] at hfine
      rcases hfine with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  have hsub : PureWZ2PaperIsSubshading shading
      twoScale.coarseGrains.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact twoScale.fine.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading := by
    have hzeroCubical := zeroExtension.cubical twoScale.fine.refined_cubical
    intro index point hpoint other hother
    have hzeroOther := hzeroCubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedParent, hselectedParent, hpointParent⟩
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hselectedFine⟩
    rcases twoScale.fine.balanced.fine_cell_nested
        selectedIndex point hselectedFine with
      ⟨nestedParent, _hnestedActive, hnested⟩
    have hpointNested : point ∈ wz1PaperGridCube root nestedParent := by
      apply hnested
      exact (mem_wz1PaperGridCube twoScale.rhoRequested.1 _ point).mpr rfl
    have hparentEq : nestedParent = selectedParent :=
      ((mem_wz1PaperGridCube root nestedParent point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube root selectedParent point).mp hpointParent)
    exact ⟨hzeroOther, Set.mem_iUnion₂.mpr
      ⟨selectedParent, hselectedParent, by
        rw [← hparentEq]
        exact hnested hother⟩⟩
  have hvolume :
      MeasureTheory.volume shading.union =
        (residue.selected.card : ENNReal) *
          twoScale.fine.balanced.cellMass := by
    rw [hunion]
    exact twoScale.fine.balanced.selected_cells_volume
      residue.selected
      (residue.selected_subset.trans
        (selection.selected_subset.trans parents.parents_subset))
  have hvolumeAll :
      MeasureTheory.volume
          (twoScale.fine.refined.union ∩
            ⋃ parent ∈ parents.parents, wz1PaperGridCube root parent) =
        (parents.parents.card : ENNReal) *
          twoScale.fine.balanced.cellMass :=
    twoScale.fine.balanced.selected_cells_volume
      parents.parents parents.parents_subset
  have hcardNat : parents.parents.card ≤ 23040 * residue.selected.card := by
    calc
      parents.parents.card ≤ 45 * selection.selected.card := selection.parent_card
      _ ≤ 45 * (512 * residue.selected.card) :=
        Nat.mul_le_mul_left 45 residue.card_fraction
      _ = 23040 * residue.selected.card := by ring
  have hcard :
      (parents.parents.card : ENNReal) ≤
        23040 * (residue.selected.card : ENNReal) := by
    exact_mod_cast hcardNat
  have hfraction :
      MeasureTheory.volume
          (twoScale.fine.refined.union ∩
            ⋃ parent ∈ parents.parents, wz1PaperGridCube root parent) ≤
        23040 * MeasureTheory.volume shading.union := by
    rw [hvolumeAll, hvolume]
    calc
      (parents.parents.card : ENNReal) * twoScale.fine.balanced.cellMass
          ≤ (23040 * (residue.selected.card : ENNReal)) *
              twoScale.fine.balanced.cellMass := by gcongr
      _ = 23040 * ((residue.selected.card : ENNReal) *
            twoScale.fine.balanced.cellMass) := by ring
  let firstParent := Classical.choose residue.selected_nonempty
  have hfirstParent : firstParent ∈ residue.selected :=
    Classical.choose_spec residue.selected_nonempty
  let commonParentHeight := firstParent.2.2
  have hparentHeight :
      ∀ parent ∈ residue.selected, parent.2.2 = commonParentHeight := by
    intro parent hparent
    have hparentAll : parent ∈ parents.parents :=
      selection.selected_subset (residue.selected_subset hparent)
    have hfirstAll : firstParent ∈ parents.parents :=
      selection.selected_subset (residue.selected_subset hfirstParent)
    rcases parents.parent_hit parent hparentAll with
      ⟨cell, hcell, hcellParent⟩
    rcases parents.parent_hit firstParent hfirstAll with
      ⟨firstCell, hfirstCell, hfirstCellParent⟩
    have hmem := parents.representative_mem_parent cell hcell
    have hfirstMem := parents.representative_mem_parent firstCell hfirstCell
    rw [hcellParent] at hmem
    rw [hfirstCellParent] at hfirstMem
    have hindex :
        wz1PaperGridIndex root (line.representative cell) = parent :=
      (mem_wz1PaperGridCube root parent _).mp hmem
    have hfirstIndex :
        wz1PaperGridIndex root (line.representative firstCell) = firstParent :=
      (mem_wz1PaperGridCube root firstParent _).mp hfirstMem
    have hheight := line.representative_height cell hcell
    have hfirstHeight := line.representative_height firstCell hfirstCell
    have hz := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hindex
    have hzFirst := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hfirstIndex
    simp [wz1PaperGridIndex, gridIndex, hheight, hfirstHeight] at hz hzFirst
    exact hz.symm.trans hzFirst
  have hunionHeight :
      ∀ point ∈ shading.union,
        point (2 : Fin 3) ∈
          Set.Ico ((commonParentHeight : ℝ) * root)
            (((commonParentHeight : ℝ) + 1) * root) := by
    intro point hpoint
    have hregion := (by rw [hunion] at hpoint; exact hpoint.2)
    rcases Set.mem_iUnion₂.mp hregion with
      ⟨parent, hparent, hpointParent⟩
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
    rw [← hparentHeight parent hparent]
    exact ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
  exact
    ⟨{ zeroExtension := zeroExtension
       selectedRegion := selectedRegion
       selectedRegion_eq := rfl
       shading := shading
       carrier_eq := fun _ => rfl
       subshading := hsub
       whole_cells := hwhole
       union_eq := hunion
       volume_eq := hvolume
       volume_fraction := hfraction
       commonParentHeight := commonParentHeight
       parent_height_eq := hparentHeight
       union_height := hunionHeight }⟩

/-- The residue is a full spatial restriction of the zero extension of the
second sticky refinement, so its final factor-two multiplicity band is
unchanged. -/
theorem PureWZ2HorizontalFixedLineResidueShadingData.constantMultiplicity
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    (data : PureWZ2HorizontalFixedLineResidueShadingData residue) :
    data.shading.HasConstantMultiplicity
      twoScale.fine.fineMultiplicity
      (2 * twoScale.fine.fineMultiplicity) := by
  have hambient := data.zeroExtension.constantMultiplicity
    twoScale.fine.refined_multiplicity_band
  intro point hpoint
  have hregion : point ∈ data.selectedRegion := by
    rcases hpoint with ⟨index, hindex⟩
    rw [data.carrier_eq index] at hindex
    exact hindex.2
  have hpointAmbient : point ∈ data.zeroExtension.ambientShading.union := by
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, (by rw [data.carrier_eq index] at hindex; exact hindex.1)⟩
  have hmultiplicity :
      data.shading.pointMultiplicity point =
        data.zeroExtension.ambientShading.pointMultiplicity point := by
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro index _
    rw [data.carrier_eq index]
    exact and_iff_left hregion
  rw [hmultiplicity]
  exact hambient point hpointAmbient

end Kakeya.Assouad
