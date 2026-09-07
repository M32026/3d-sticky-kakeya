import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalYResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseRegionSourcePullback

/-!
# First-sticky coarse carrier selected by the original source fixed line

This is the carrier bridge used in the paper proof of Lemma 24.  The horizontal
slice and the fixed line are selected using the original `delta`-scale source
slope.  The selected side-`sqrt rho` cells are then applied to the genuine
first-sticky `rho`-scale shading.  Thus the local Lemma-23 graph receives the
coarse volume supply, while the line still has the required original-source
provenance.

The construction deliberately does not identify the source slope with the
global slope produced by applying the grain theorem to the coarse family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceFixedBinCoarseCarrierData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (residue : PureWZ2SourceHorizontalFixedBinYResidueData selection) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.fine.selected twoScale.fine.refined
  selectedRegion : Set Point3 :=
    ⋃ parent ∈ residue.selected,
      wz1PaperGridCube twoScale.sqrtRequested.1 parent
  selectedRegion_eq : selectedRegion =
    ⋃ parent ∈ residue.selected,
      wz1PaperGridCube twoScale.sqrtRequested.1 parent
  shading : WZ1PaperTubeShading twoScale.coarse.coarse
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading :
    PureWZ2PaperIsSubshading shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = twoScale.fine.refined.union ∩ selectedRegion
  volume_eq :
    volume shading.union =
      (residue.selected.card : ENNReal) * twoScale.fine.balanced.cellMass
  volume_fraction :
    volume
        (twoScale.fine.refined.union ∩
          ⋃ parent ∈ parents.parents,
            wz1PaperGridCube twoScale.sqrtRequested.1 parent) ≤
      23040 * volume shading.union
  commonParentHeight : ℤ
  parent_height_eq :
    ∀ parent ∈ residue.selected, parent.2.2 = commonParentHeight
  union_height :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈
        Set.Ico
          ((commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
          (((commonParentHeight : ℝ) + 1) * twoScale.sqrtRequested.1)

abbrev PureWZ2SourceFixedLineCoarseCarrierData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    (residue : PureWZ2SourceHorizontalYResidueData selection) : Type :=
  PureWZ2SourceFixedBinCoarseCarrierData residue

/-- Restrict the genuine first-sticky carrier to the `sqrt rho` parents
selected by the original-source fixed line. -/
theorem PureWZ2SourceHorizontalFixedBinYResidueData.retainCoarseCarrierFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (residue : PureWZ2SourceHorizontalFixedBinYResidueData selection) :
    Nonempty (PureWZ2SourceFixedBinCoarseCarrierData residue) := by
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
      volume shading.union =
        (residue.selected.card : ENNReal) *
          twoScale.fine.balanced.cellMass := by
    rw [hunion]
    exact twoScale.fine.balanced.selected_cells_volume
      residue.selected
      (residue.selected_subset.trans
        (selection.selected_subset.trans parents.parents_subset))
  have hvolumeAll :
      volume
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
      volume
          (twoScale.fine.refined.union ∩
            ⋃ parent ∈ parents.parents, wz1PaperGridCube root parent) ≤
        23040 * volume shading.union := by
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

/-- The coarse graph carrier is localized near the fixed line selected from
the original source slice.  No coarse-grain slope is used. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.fixed_line_localizationFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue) :
    ∀ point ∈ data.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1 := by
  let root := twoScale.sqrtRequested.1
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hrho : 0 < rho := line.rho_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrhoRoot : rho ≤ root := by
    have hrootEq : root = Real.sqrt rho := by
      simpa [root] using twoScale.sqrtRequested_eq
    rw [hrootEq]
    have hrhoOne : rho ≤ 1 := by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.rhoRequested.property.2
    nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt hrho.le]
  intro point hpoint
  have hregion : point ∈ data.selectedRegion := by
    rw [data.union_eq] at hpoint
    exact hpoint.2
  rw [data.selectedRegion_eq] at hregion
  rcases Set.mem_iUnion₂.mp hregion with
    ⟨parent, hparent, hpointParent⟩
  have hparentAll : parent ∈ parents.parents :=
    selection.selected_subset (residue.selected_subset hparent)
  rcases parents.parent_hit parent hparentAll with
    ⟨cell, hcell, hcellParent⟩
  let representative := line.representative cell
  have hrepresentativeParent :
      representative ∈ wz1PaperGridCube root parent := by
    have hmem := parents.representative_mem_parent cell hcell
    rwa [hcellParent] at hmem
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hrepresentativeParent
  rcases hpointParent with
    ⟨hpoint0Lower, hpoint0Upper, hpoint1Lower, hpoint1Upper,
      hpoint2Lower, hpoint2Upper⟩
  rcases hrepresentativeParent with
    ⟨hrep0Lower, hrep0Upper, hrep1Lower, hrep1Upper,
      hrep2Lower, hrep2Upper⟩
  have hcoord0 : |point 0 - representative 0| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hcoord1 : |point 1 - representative 1| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hcoord2 : |point 2 - representative 2| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hpointCoarse : point ∈ twoScale.coarseGrains.shading.union :=
    data.subshading.union_subset hpoint
  have hpointBox := shading_union_subset_axisBox hpointCoarse
  have hpoint1 : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := hpointBox.2.2
    simpa [Kakeya.Streamlined.axisBox, abs_le] using h
  have hrepresentativeHeight :
      representative (2 : Fin 3) = line.lineHeight :=
    line.representative_height cell hcell
  have hslopeDifference :
      |source.globalGrains.slope (point (2 : Fin 3)) -
          source.globalGrains.slope line.lineHeight| ≤ root := by
    have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
      (point (2 : Fin 3)) hpointHeight
      line.lineHeight line.lineHeight_mem
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans (by
      rw [← hrepresentativeHeight]
      exact hcoord2)
  have hslopeLine :
      |source.globalGrains.slope line.lineHeight| ≤ 3 :=
    source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem
  have hprojectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight))| ≤
        5 * root := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) =
          (point 0 - representative 0) +
            source.globalGrains.slope line.lineHeight *
              (point 1 - representative 1) +
            (source.globalGrains.slope (point (2 : Fin 3)) -
              source.globalGrains.slope line.lineHeight) * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      |(point 0 - representative 0) +
          source.globalGrains.slope line.lineHeight *
            (point 1 - representative 1) +
          (source.globalGrains.slope (point (2 : Fin 3)) -
            source.globalGrains.slope line.lineHeight) * point 1|
          ≤ |point 0 - representative 0| +
              |source.globalGrains.slope line.lineHeight| *
                |point 1 - representative 1| +
              |source.globalGrains.slope (point (2 : Fin 3)) -
                source.globalGrains.slope line.lineHeight| * |point 1| := by
            calc
              _ ≤ |(point 0 - representative 0) +
                    source.globalGrains.slope line.lineHeight *
                      (point 1 - representative 1)| +
                    |(source.globalGrains.slope (point (2 : Fin 3)) -
                      source.globalGrains.slope line.lineHeight) * point 1| :=
                abs_add_le _ _
              _ ≤ (|point 0 - representative 0| +
                    |source.globalGrains.slope line.lineHeight *
                      (point 1 - representative 1)|) +
                    |(source.globalGrains.slope (point (2 : Fin 3)) -
                      source.globalGrains.slope line.lineHeight) * point 1| := by
                gcongr
                exact abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ root + 3 * root + root * 1 := by gcongr
      _ = 5 * root := by ring
  have hrepresentativeNear :=
    line.heavy_representative_near_line cell hcell
  calc
    |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel|
        ≤ |inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight))| +
          |inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            line.lineLevel| := by
              have := abs_add_le
                (inner ℝ point
                    (globalGrainDirection
                      (source.globalGrains.slope (point (2 : Fin 3)))) -
                  inner ℝ representative
                    (globalGrainDirection
                      (source.globalGrains.slope line.lineHeight)))
                (inner ℝ representative
                    (globalGrainDirection
                      (source.globalGrains.slope line.lineHeight)) -
                  line.lineLevel)
              simpa only [sub_add_sub_cancel] using this
    _ ≤ 5 * root + 9 * delta := by gcongr
    _ ≤ 5 * root + 9 * rho := by gcongr
    _ ≤ 14 * root := by linarith

theorem PureWZ2SourceHorizontalYResidueData.retainCoarseCarrier
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    (residue : PureWZ2SourceHorizontalYResidueData selection) :
    Nonempty (PureWZ2SourceFixedLineCoarseCarrierData residue) :=
  residue.retainCoarseCarrierFixedBin

theorem PureWZ2SourceFixedLineCoarseCarrierData.fixed_line_localization
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue) :
    ∀ point ∈ data.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1 :=
  data.fixed_line_localizationFixedBin

/-- Exact Fubini bookkeeping for the hybrid carrier.  The source fixed-line
selection costs only the second balanced cell mass; the first balanced cell
mass is not paid a second time. -/
theorem PureWZ2SourceFixedLineCoarseCarrierData.volume_supply_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue) :
    window.volumeSupply * twoScale.fine.balanced.cellMass ≤
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        volume data.shading.union := by
  let sliceThickness : ENNReal :=
    ENNReal.ofReal (Real.sqrt rho + 2 * rho)
  let sliceDisk : ENNReal :=
    ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi
  let globalBound : ENNReal :=
    132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
      Kakeya.realRpowENN (1 / delta) (1 - sigma)
  let parentBound : ENNReal :=
    (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal)
  have hwindowSupply :
      window.volumeSupply ≤ volume window.shading.union :=
    window.volume_lower
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, window.subshading index hindex⟩
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hsliceAreaUpper :
      volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) ≤
        (line.sliceCells.card : ENNReal) * sliceDisk := by
    have hraw := wz1_lemma23_exactSlice_area_le_two
      window.shading hdelta hball line.lineHeight
    simpa [line.sliceCells_eq, sliceDisk] using hraw
  have hsliceThicknessPos : 0 < sliceThickness := by
    apply ENNReal.ofReal_pos.mpr
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.mpr line.rho_pos
    exact add_pos hsqrt (mul_pos (by norm_num) line.rho_pos)
  have hwindowToSlice :
      volume window.shading.union ≤
        volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
          sliceThickness := by
    apply (ENNReal.div_le_iff
      hsliceThicknessPos.ne' ENNReal.ofReal_ne_top).mp
    simpa [sliceThickness] using line.slice_area_lower
  have hsliceCount :
      (line.sliceCells.card : ENNReal) ≤
        (line.globalBins.card : ENNReal) *
          (line.heavyCells.card : ENNReal) := by
    exact_mod_cast line.heavy_cell_count
  have hglobalCount :
      (line.globalBins.card : ENNReal) ≤ globalBound := by
    simpa [globalBound] using line.global_bin_count
  have hheavyCount :
      (line.heavyCells.card : ENNReal) ≤
        parentBound * (parents.parents.card : ENNReal) := by
    change (line.heavyCells.card : ENNReal) ≤
      (pureWZ2SourceFixedLineParentFiberBound delta rho : ENNReal) *
        (parents.parents.card : ENNReal)
    exact_mod_cast parents.heavy_card
  have hwindowCount :
      volume window.shading.union ≤
        sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal) := by
    calc
      volume window.shading.union ≤
          volume (wz1Lemma23PlanarSlice window.shading.union line.lineHeight) *
            sliceThickness := hwindowToSlice
      _ ≤ ((line.sliceCells.card : ENNReal) * sliceDisk) *
            sliceThickness := by gcongr
      _ ≤ (((line.globalBins.card : ENNReal) *
              (line.heavyCells.card : ENNReal)) * sliceDisk) *
            sliceThickness := by gcongr
      _ ≤ ((globalBound * (parentBound *
              (parents.parents.card : ENNReal))) * sliceDisk) *
            sliceThickness := by gcongr
      _ = sliceThickness * sliceDisk * globalBound * parentBound *
            (parents.parents.card : ENNReal) := by ring
  have hparentVolume :
      (parents.parents.card : ENNReal) *
          twoScale.fine.balanced.cellMass ≤
        23040 * volume data.shading.union := by
    have hvolumeAll :
        volume
            (twoScale.fine.refined.union ∩
              ⋃ parent ∈ parents.parents,
                wz1PaperGridCube twoScale.sqrtRequested.1 parent) =
          (parents.parents.card : ENNReal) *
            twoScale.fine.balanced.cellMass :=
      twoScale.fine.balanced.selected_cells_volume
        parents.parents parents.parents_subset
    rw [← hvolumeAll]
    exact data.volume_fraction
  calc
    window.volumeSupply * twoScale.fine.balanced.cellMass ≤
        volume window.shading.union *
          twoScale.fine.balanced.cellMass := by gcongr
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound *
          (parents.parents.card : ENNReal)) *
          twoScale.fine.balanced.cellMass := by gcongr
    _ = (sliceThickness * sliceDisk * globalBound * parentBound) *
          ((parents.parents.card : ENNReal) *
            twoScale.fine.balanced.cellMass) := by ring
    _ ≤ (sliceThickness * sliceDisk * globalBound * parentBound) *
          (23040 * volume data.shading.union) := by gcongr
    _ = pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          volume data.shading.union := by
      simp [pureWZ2SourceHorizontalVolumeCost, sliceThickness, sliceDisk,
        globalBound, parentBound]
      ring

/-- Apply the first balanced cover to the hybrid coarse region.  This is the
exact same-relative-density pullback back to the original source family. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.pullbackToSourceFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue) :
    Nonempty (PureWZ2SelectedCoarseRegionSourcePullbackData data.shading) :=
  pureWZ2_pullback_selected_coarse_region data.shading
    data.subshading data.whole_cells

/-- The genuine fixed-line coarse carrier is a full spatial restriction of
the zero extension of the second sticky refinement, so the final factor-two
point-multiplicity band is unchanged. -/
theorem PureWZ2SourceFixedBinCoarseCarrierData.constantMultiplicityFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (data : PureWZ2SourceFixedBinCoarseCarrierData residue) :
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

theorem PureWZ2SourceFixedLineCoarseCarrierData.pullbackToSource
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue) :
    Nonempty (PureWZ2SelectedCoarseRegionSourcePullbackData data.shading) :=
  data.pullbackToSourceFixedBin

theorem PureWZ2SourceFixedLineCoarseCarrierData.constantMultiplicity
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (data : PureWZ2SourceFixedLineCoarseCarrierData residue) :
    data.shading.HasConstantMultiplicity
      twoScale.fine.fineMultiplicity
      (2 * twoScale.fine.fineMultiplicity) :=
  data.constantMultiplicityFixedBin

/-- Exact parentwise same-relative-density identity across both balanced
covers.  The source and coarse carriers use the same selected second-stage
parents; the first-cover incidence mass and the physical side-`rho` cube are
therefore the two conversion factors. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.coarse_volume_mass_cross
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue) :
    volume coarseCarrier.shading.union *
          twoScale.coarse.balanced.incidenceMass =
      retained.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [coarseCarrier.volume_eq, retained.mass_mul_cube]

/-- The exact parentwise cross identity and first-stage multiplicity band give
the corresponding source-mass lower bound without replacing either balanced
cell mass by a scale power. -/
theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.coarse_volume_mul_source_unit_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
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
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (coarseCarrier : PureWZ2SourceFixedBinCoarseCarrierData residue) :
    volume coarseCarrier.shading.union *
          ((twoScale.coarse.fineMultiplicity : ENNReal) *
            twoScale.coarse.balanced.cellMass) ≤
      retained.shading.mass *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [← retained.coarse_volume_mass_cross coarseCarrier]
  gcongr
  exact twoScale.coarse.balanced_incidenceMass_band.1

end Kakeya.Assouad

end
