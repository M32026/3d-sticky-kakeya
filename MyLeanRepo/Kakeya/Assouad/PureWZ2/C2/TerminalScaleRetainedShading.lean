import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleParentResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension

/-!
# Original-family terminal shading on separated actual parents

The selected terminal refinement is extended by zero to the original source
family and then restricted to the actual mod-512 parent residue.  The output
therefore remains a whole-cell subshading of the frozen source configuration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalBinRetainedShadingData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    (residue : PureWZ2TerminalBinParentYResidueData selection) where
  zeroExtension : WZ2PaperSubfamilyZeroExtensionData
    terminal.sticky.selected terminal.sticky.refined
  selectedRegion : Set Point3 :=
    ⋃ parent ∈ residue.selected,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  selectedRegion_eq : selectedRegion =
    ⋃ parent ∈ residue.selected,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq : shading.union = terminal.sticky.refined.union ∩ selectedRegion
  volume_eq : volume shading.union =
    (residue.selected.card : ENNReal) * terminal.sticky.balanced.cellMass
  volume_fraction :
    volume (terminal.sticky.refined.union ∩
        ⋃ parent ∈ parents.parents,
          wz1PaperGridCube terminal.sqrtRequested.1 parent) ≤
      23040 * volume shading.union
  commonParentHeight : ℤ
  parent_height_eq :
    ∀ parent ∈ residue.selected, parent.2.2 = commonParentHeight
  union_height : ∀ point ∈ shading.union,
    point (2 : Fin 3) ∈ Set.Ico
      ((commonParentHeight : ℝ) * terminal.sqrtRequested.1)
      (((commonParentHeight : ℝ) + 1) * terminal.sqrtRequested.1)

/-- Backwards-compatible retained shading on the largest global bin. -/
abbrev PureWZ2TerminalRetainedShadingData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    (residue : PureWZ2TerminalParentYResidueData selection) :=
  PureWZ2TerminalBinRetainedShadingData residue

theorem PureWZ2TerminalBinParentYResidueData.retainSourceShadingBin
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    (residue : PureWZ2TerminalBinParentYResidueData selection) :
    Nonempty (PureWZ2TerminalBinRetainedShadingData residue) := by
  let root := terminal.sqrtRequested.1
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  rcases wz2_paper_subfamily_zero_extension
      terminal.sticky.selected terminal.sticky.refined with
    ⟨zeroExtension⟩
  let selectedRegion : Set Point3 :=
    ⋃ parent ∈ residue.selected, wz1PaperGridCube root parent
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion residue.selected.finite_toSet.countable
      (fun parent _ => wz1PaperGridCube_measurable parent)
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter hregionMeas
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (zeroExtension.ambientShading.subset_body index) }
  have hunion : shading.union =
      terminal.sticky.refined.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hzero, hregion⟩
      have hzeroUnion : point ∈ zeroExtension.ambientShading.union :=
        ⟨index, hzero⟩
      rw [zeroExtension.union_eq] at hzeroUnion
      exact ⟨hzeroUnion, hregion⟩
    · rintro ⟨hrefined, hregion⟩
      rw [← zeroExtension.union_eq] at hrefined
      rcases hrefined with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact terminal.sticky.subshading selectedIndex hselected
  have hwhole : WZ1PaperIsCubicalShading shading := by
    have hzeroCubical := zeroExtension.cubical terminal.sticky.refined_cubical
    intro index point hpoint other hother
    have hzeroOther := hzeroCubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedParent, hselectedParent, hpointParent⟩
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hselectedFine⟩
    rcases terminal.sticky.balanced.fine_cell_nested
        selectedIndex point hselectedFine with
      ⟨nestedParent, _hnestedActive, hnested⟩
    have hpointNested : point ∈ wz1PaperGridCube root nestedParent := by
      apply hnested
      exact (mem_wz1PaperGridCube delta _ point).mpr rfl
    have hparentEq : nestedParent = selectedParent :=
      ((mem_wz1PaperGridCube root nestedParent point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube root selectedParent point).mp hpointParent)
    exact ⟨hzeroOther, Set.mem_iUnion₂.mpr
      ⟨selectedParent, hselectedParent, by
        rw [← hparentEq]
        exact hnested hother⟩⟩
  have hvolume : volume shading.union =
      (residue.selected.card : ENNReal) *
        terminal.sticky.balanced.cellMass := by
    rw [hunion]
    exact terminal.sticky.balanced.selected_cells_volume
      residue.selected
      (residue.selected_subset.trans
        (selection.selected_subset.trans parents.parents_subset))
  have hvolumeAll :
      volume (terminal.sticky.refined.union ∩
          ⋃ parent ∈ parents.parents, wz1PaperGridCube root parent) =
        (parents.parents.card : ENNReal) *
          terminal.sticky.balanced.cellMass :=
    terminal.sticky.balanced.selected_cells_volume
      parents.parents parents.parents_subset
  have hparentCard : parents.parents.card ≤ 23040 * residue.selected.card := by
    calc
      parents.parents.card ≤ 45 * selection.selected.card := selection.parent_card
      _ ≤ 45 * (512 * residue.selected.card) :=
        Nat.mul_le_mul_left 45 residue.card_fraction
      _ = 23040 * residue.selected.card := by ring
  have hfraction :
      volume (terminal.sticky.refined.union ∩
          ⋃ parent ∈ parents.parents, wz1PaperGridCube root parent) ≤
        23040 * volume shading.union := by
    rw [hvolumeAll, hvolume]
    have hcard : (parents.parents.card : ENNReal) ≤
        23040 * (residue.selected.card : ENNReal) := by
      exact_mod_cast hparentCard
    calc
      (parents.parents.card : ENNReal) * terminal.sticky.balanced.cellMass
          ≤ (23040 * (residue.selected.card : ENNReal)) *
              terminal.sticky.balanced.cellMass := by gcongr
      _ = 23040 * ((residue.selected.card : ENNReal) *
            terminal.sticky.balanced.cellMass) := by ring
  let firstParent := Classical.choose residue.selected_nonempty
  have hfirstParent : firstParent ∈ residue.selected :=
    Classical.choose_spec residue.selected_nonempty
  let commonParentHeight := firstParent.2.2
  have hparentHeight :
      ∀ parent ∈ residue.selected, parent.2.2 = commonParentHeight := by
    intro parent hparent
    rcases selection.selected_hit parent (residue.selected_subset hparent) with
      ⟨cell, hcell, hcellParent⟩
    rcases selection.selected_hit firstParent
        (residue.selected_subset hfirstParent) with
      ⟨firstCell, hfirstCell, hfirstCellParent⟩
    have hmem := parents.representative_mem_parent cell hcell
    have hfirstMem := parents.representative_mem_parent firstCell hfirstCell
    rw [hcellParent] at hmem
    rw [hfirstCellParent] at hfirstMem
    have hindex : wz1PaperGridIndex root (line.representative cell) = parent :=
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
  have hunionHeight : ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        ((commonParentHeight : ℝ) * root)
        (((commonParentHeight : ℝ) + 1) * root) := by
    intro point hpoint
    have hregion := (by rw [hunion] at hpoint; exact hpoint.2)
    rcases Set.mem_iUnion₂.mp hregion with
      ⟨parent, hparent, hpointParent⟩
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
    rw [← hparentHeight parent hparent]
    exact ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
  exact ⟨{
    zeroExtension := zeroExtension
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    whole_cells := hwhole
    union_eq := hunion
    volume_eq := hvolume
    volume_fraction := hfraction
    commonParentHeight := commonParentHeight
    parent_height_eq := hparentHeight
    union_height := hunionHeight
  }⟩

/-- Compatibility wrapper for the former largest-bin terminal chain. -/
theorem PureWZ2TerminalParentYResidueData.retainSourceShading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    (residue : PureWZ2TerminalParentYResidueData selection) :
    Nonempty (PureWZ2TerminalRetainedShadingData residue) :=
  residue.retainSourceShadingBin

end Kakeya.Assouad
