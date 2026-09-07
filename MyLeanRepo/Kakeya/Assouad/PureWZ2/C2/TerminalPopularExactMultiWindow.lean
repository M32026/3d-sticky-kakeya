import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularExactTrapezoid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalSourceBlockMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension

/-!
# Multi-window aggregation for the terminal paper-order chain

This is the multi-window consumer for `TerminalPopularExactTrapezoid`.  It
keeps the heterogeneous outer-popular chain attached to each source block,
selects one mass-heavy block residue, and only then zero-extends the resulting
height restriction to the original source family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The paper-order exact output on every good terminal source block. -/
structure PureWZ2TerminalPopularGoodBlockFamilyData
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) where
  indexCount : ℕ
  indexCount_pos : 0 < indexCount
  block : Fin indexCount → ℤ
  block_injective : Function.Injective block
  sourceShading : Fin indexCount →
    WZ1PaperTubeShading terminal.sticky.selected.family
  sourceShading_subshading : ∀ index,
    PureWZ2PaperIsSubshading (sourceShading index) terminalSource.shading
  sourceShading_constant_multiplicity : ∀ index,
    (sourceShading index).HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity)
  sourceMassCost : ENNReal
  sourceMassCost_pos : 0 < sourceMassCost
  sourceMassCost_ne_top : sourceMassCost ≠ ⊤
  source_mass_control : terminalSource.shading.mass ≤
    sourceMassCost * ∑ index : Fin indexCount, (sourceShading index).mass
  window : ∀ index, PureWZ2TerminalWindow prepared
  window_left : ∀ index,
    (window index).left = pureWZ2SourceCarrierBlockLeft delta (block index)
  source_window_union : ∀ index,
    (sourceShading index).union = (window index).shading.union
  output : ∀ index, PureWZ2TerminalPopularExactWindowOutput
    (eta := eta) (theoremEta := theoremEta) (outputLoss := outputLoss)
    (window index)
  block_volume_retention : ∀ index,
    2 * Kakeya.realRpowENN delta localMassLoss *
        volume (sourceShading index).union ≤
      volume (output index).chain.outerHeightLift.shading.union

namespace PureWZ2TerminalPopularGoodBlockFamilyData

variable
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared)

/-- Enumerate every good source block and retain the certified output selected
for its literal window.  The refill inequality cannot be supplied using an
output chosen from another block or another dependent chain. -/
theorem build
    (outputFor : ∀ {block : ℤ}
      (windowData : PureWZ2TerminalBlockWindowData prepared block),
        Nonempty (PureWZ2TerminalPopularExactWindowOutput
          (eta := eta) (theoremEta := theoremEta)
          (outputLoss := outputLoss) windowData.window))
    (volumeFor : ∀ {block : ℤ}
      (windowData : PureWZ2TerminalBlockWindowData prepared block)
      (output : PureWZ2TerminalPopularExactWindowOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) windowData.window),
        2 * Kakeya.realRpowENN delta localMassLoss *
            volume (terminalSourceBlockShading prepared block).union ≤
          volume output.chain.outerHeightLift.shading.union)
    (hgood : (pureWZ2GoodTerminalBlocks prepared).Nonempty) :
    Nonempty (PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared) := by
  let goodBlocks := pureWZ2GoodTerminalBlocks prepared
  let goodEquiv := goodBlocks.equivFin
  let block : Fin goodBlocks.card → ℤ := fun index =>
    (goodEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ goodBlocks := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let windowData : ∀ index : Fin goodBlocks.card,
      PureWZ2TerminalBlockWindowData prepared (block index) := fun index =>
    Classical.choice (prepared.windowDataOfGoodBlock (hblockMem index))
  let output : ∀ index, PureWZ2TerminalPopularExactWindowOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (windowData index).window := fun index =>
    Classical.choice (outputFor (windowData index))
  exact ⟨{
    indexCount := goodBlocks.card
    indexCount_pos := Finset.card_pos.mpr hgood
    block := block
    block_injective := hblockInjective
    sourceShading := fun index =>
      terminalSourceBlockShading prepared (block index)
    sourceShading_subshading := fun index _ => Set.inter_subset_left
    sourceShading_constant_multiplicity := fun index =>
      terminalSourceBlockShading_constant_multiplicity prepared (block index)
    sourceMassCost := 4
    sourceMassCost_pos := by norm_num
    sourceMassCost_ne_top := by norm_num
    source_mass_control := by
      calc
        terminalSource.shading.mass ≤
            4 * ∑ target ∈ goodBlocks,
              (terminalSourceBlockShading prepared target).mass :=
          terminalSource_mass_le_four_mul_goodBlockMass prepared
        _ = 4 * ∑ index : Fin goodBlocks.card,
              (terminalSourceBlockShading prepared (block index)).mass := by
          congr 1
          symm
          apply Finset.sum_bij (fun index _ => block index)
          · intro index _
            exact hblockMem index
          · intro first _ second _ equality
            exact hblockInjective equality
          · intro target htarget
            let index := goodEquiv ⟨target, htarget⟩
            refine ⟨index, Finset.mem_univ index, ?_⟩
            change (goodEquiv.symm index).1 = target
            simp [index]
          · intro _ _
            rfl
    window := fun index => (windowData index).window
    window_left := fun index => (windowData index).left_eq
    source_window_union := fun index => by
      rw [(windowData index).shading_eq,
        terminalSourceBlockShading_union_eq prepared (block index)]
    output := output
    block_volume_retention := fun index =>
      volumeFor (windowData index) (output index) }⟩

/-- Build the same multi-window consumer from a caller-specified family of
source pieces.  This is used by the block--parent pair route, where each
piece is an honest intersection of one block with its selected parents. -/
theorem buildFromSourcePieces
    (blocks : Finset ℤ) (hblocks : blocks.Nonempty)
    (sourceFor : ℤ → WZ1PaperTubeShading terminal.sticky.selected.family)
    (sourceSubshading : ∀ {block : ℤ} (hblock : block ∈ blocks),
      PureWZ2PaperIsSubshading (sourceFor block) terminalSource.shading)
    (sourceConstant : ∀ {block : ℤ} (hblock : block ∈ blocks),
      (sourceFor block).HasConstantMultiplicity
        terminalSource.multiplicity (2 * terminalSource.multiplicity))
    (sourceMassCost : ENNReal) (hsourceMassCostPos : 0 < sourceMassCost)
    (hsourceMassCostTop : sourceMassCost ≠ ⊤)
    (sourceMassControl : terminalSource.shading.mass ≤
      sourceMassCost * ∑ block ∈ blocks, (sourceFor block).mass)
    (windowFor : ∀ {block : ℤ} (hblock : block ∈ blocks),
      PureWZ2TerminalWindow prepared)
    (windowLeft : ∀ {block : ℤ} (hblock : block ∈ blocks),
      (windowFor hblock).left = pureWZ2SourceCarrierBlockLeft delta block)
    (sourceWindowUnion : ∀ {block : ℤ} (hblock : block ∈ blocks),
      (sourceFor block).union = (windowFor hblock).shading.union)
    (outputFor : ∀ {block : ℤ} (hblock : block ∈ blocks),
      Nonempty (PureWZ2TerminalPopularExactWindowOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) (windowFor hblock)))
    (volumeFor : ∀ {block : ℤ} (hblock : block ∈ blocks)
      (output : PureWZ2TerminalPopularExactWindowOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) (windowFor hblock)),
      2 * Kakeya.realRpowENN delta localMassLoss *
          volume (sourceFor block).union ≤
        volume output.chain.outerHeightLift.shading.union) :
    Nonempty (PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared) := by
  let blockEquiv := blocks.equivFin
  let block : Fin blocks.card → ℤ := fun index => (blockEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ blocks := fun index =>
    (blockEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply blockEquiv.symm.injective
    exact Subtype.ext heq
  let sourceShading : Fin blocks.card →
      WZ1PaperTubeShading terminal.sticky.selected.family := fun index =>
    sourceFor (block index)
  let window : ∀ index : Fin blocks.card, PureWZ2TerminalWindow prepared :=
    fun index => windowFor (hblockMem index)
  let output : ∀ index, PureWZ2TerminalPopularExactWindowOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (window index) := fun index =>
    Classical.choice (outputFor (hblockMem index))
  have hmassReindex :
      (∑ target ∈ blocks, (sourceFor target).mass) =
        ∑ index : Fin blocks.card, (sourceShading index).mass := by
    symm
    apply Finset.sum_bij (fun index _ => block index)
    · intro index _
      exact hblockMem index
    · intro first _ second _ equality
      exact hblockInjective equality
    · intro target htarget
      let index := blockEquiv ⟨target, htarget⟩
      refine ⟨index, Finset.mem_univ index, ?_⟩
      have heq : block index = target := by
        change (blockEquiv.symm index).1 = target
        simp [index]
      rw [heq]
    · intro _ _
      rfl
  exact ⟨{
    indexCount := blocks.card
    indexCount_pos := Finset.card_pos.mpr hblocks
    block := block
    block_injective := hblockInjective
    sourceShading := sourceShading
    sourceShading_subshading := fun index =>
      sourceSubshading (hblockMem index)
    sourceShading_constant_multiplicity := fun index =>
      sourceConstant (hblockMem index)
    sourceMassCost := sourceMassCost
    sourceMassCost_pos := hsourceMassCostPos
    sourceMassCost_ne_top := hsourceMassCostTop
    source_mass_control := by
      rw [← hmassReindex]
      exact sourceMassControl
    window := window
    window_left := fun index => windowLeft (hblockMem index)
    source_window_union := fun index => sourceWindowUnion (hblockMem index)
    output := output
    block_volume_retention := fun index =>
      volumeFor (hblockMem index) (output index)
  }⟩

/-- Version of `buildFromSourcePieces` that records the caller-supplied mass
cost definitionally for downstream scalar bookkeeping. -/
theorem buildFromSourcePiecesWithCost
    (blocks : Finset ℤ) (hblocks : blocks.Nonempty)
    (sourceFor : ℤ → WZ1PaperTubeShading terminal.sticky.selected.family)
    (sourceSubshading : ∀ {block : ℤ} (hblock : block ∈ blocks),
      PureWZ2PaperIsSubshading (sourceFor block) terminalSource.shading)
    (sourceConstant : ∀ {block : ℤ} (hblock : block ∈ blocks),
      (sourceFor block).HasConstantMultiplicity
        terminalSource.multiplicity (2 * terminalSource.multiplicity))
    (sourceMassCost : ENNReal) (hsourceMassCostPos : 0 < sourceMassCost)
    (hsourceMassCostTop : sourceMassCost ≠ ⊤)
    (sourceMassControl : terminalSource.shading.mass ≤
      sourceMassCost * ∑ block ∈ blocks, (sourceFor block).mass)
    (windowFor : ∀ {block : ℤ} (hblock : block ∈ blocks),
      PureWZ2TerminalWindow prepared)
    (windowLeft : ∀ {block : ℤ} (hblock : block ∈ blocks),
      (windowFor hblock).left = pureWZ2SourceCarrierBlockLeft delta block)
    (sourceWindowUnion : ∀ {block : ℤ} (hblock : block ∈ blocks),
      (sourceFor block).union = (windowFor hblock).shading.union)
    (outputFor : ∀ {block : ℤ} (hblock : block ∈ blocks),
      Nonempty (PureWZ2TerminalPopularExactWindowOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) (windowFor hblock)))
    (volumeFor : ∀ {block : ℤ} (hblock : block ∈ blocks)
      (output : PureWZ2TerminalPopularExactWindowOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) (windowFor hblock)),
      2 * Kakeya.realRpowENN delta localMassLoss *
          volume (sourceFor block).union ≤
        volume output.chain.outerHeightLift.shading.union) :
    ∃ good : PureWZ2TerminalPopularGoodBlockFamilyData
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared,
      good.sourceMassCost = sourceMassCost := by
  let blockEquiv := blocks.equivFin
  let block : Fin blocks.card → ℤ := fun index => (blockEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ blocks := fun index =>
    (blockEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply blockEquiv.symm.injective
    exact Subtype.ext heq
  let sourceShading : Fin blocks.card →
      WZ1PaperTubeShading terminal.sticky.selected.family := fun index =>
    sourceFor (block index)
  let window : ∀ index : Fin blocks.card, PureWZ2TerminalWindow prepared :=
    fun index => windowFor (hblockMem index)
  let output : ∀ index, PureWZ2TerminalPopularExactWindowOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (window index) := fun index =>
    Classical.choice (outputFor (hblockMem index))
  have hmassReindex :
      (∑ target ∈ blocks, (sourceFor target).mass) =
        ∑ index : Fin blocks.card, (sourceShading index).mass := by
    symm
    apply Finset.sum_bij (fun index _ => block index)
    · intro index _
      exact hblockMem index
    · intro first _ second _ equality
      exact hblockInjective equality
    · intro target htarget
      let index := blockEquiv ⟨target, htarget⟩
      refine ⟨index, Finset.mem_univ index, ?_⟩
      change (blockEquiv.symm index).1 = target
      simp [index]
    · intro _ _
      rfl
  let good : PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared := {
    indexCount := blocks.card
    indexCount_pos := Finset.card_pos.mpr hblocks
    block := block
    block_injective := hblockInjective
    sourceShading := sourceShading
    sourceShading_subshading := fun index => sourceSubshading (hblockMem index)
    sourceShading_constant_multiplicity := fun index =>
      sourceConstant (hblockMem index)
    sourceMassCost := sourceMassCost
    sourceMassCost_pos := hsourceMassCostPos
    sourceMassCost_ne_top := hsourceMassCostTop
    source_mass_control := by rw [← hmassReindex]; exact sourceMassControl
    window := window
    window_left := fun index => windowLeft (hblockMem index)
    source_window_union := fun index => sourceWindowUnion (hblockMem index)
    output := output
    block_volume_retention := fun index =>
      volumeFor (hblockMem index) (output index)
  }
  exact ⟨good, rfl⟩

/-- The exact height-only source shading produced on one good block. -/
abbrev blockShading (index : Fin good.indexCount) :
    WZ1PaperTubeShading terminal.sticky.selected.family :=
  (good.output index).chain.outerHeightLift.shading

/-- Every block output is a restriction of the literal terminal source. -/
theorem blockShading_subshading (index : Fin good.indexCount) :
    PureWZ2PaperIsSubshading (good.blockShading index)
      terminalSource.shading :=
  (good.output index).chain.outerHeightLift.subshading

/-- Every block output keeps the terminal constant-multiplicity band. -/
theorem blockShading_constant_multiplicity (index : Fin good.indexCount) :
    (good.blockShading index).HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) :=
  (good.output index).chain.outerHeightLift.constant_multiplicity

/-- Every block output has positive indexed mass. -/
theorem blockShading_mass_pos (index : Fin good.indexCount) :
    0 < (good.blockShading index).mass := by
  have hsourceVolume : 0 < volume
      (good.sourceShading index).union := by
    rw [good.source_window_union index]
    exact (good.window index).volumeSupply_pos.trans_le
      (good.window index).volume_lower
  have hfactor : 0 < 2 * Kakeya.realRpowENN delta localMassLoss := by
    exact ENNReal.mul_pos (by norm_num) (by
      simp [Kakeya.realRpowENN,
        Real.rpow_pos_of_pos source.extremal.delta_pos])
  have hvolume : 0 < volume (good.blockShading index).union :=
    (ENNReal.mul_pos hfactor.ne' hsourceVolume.ne').trans_le
      (good.block_volume_retention index)
  let multiplicity : ENNReal := terminalSource.multiplicity
  have hmultiplicity : 0 < multiplicity := by
    change (0 : ENNReal) < (terminalSource.multiplicity : ENNReal)
    exact_mod_cast terminalSource.multiplicity_pos
  exact (ENNReal.mul_pos hmultiplicity.ne' hvolume.ne').trans_le
    (constant_multiplicity_mass_volume_generic
      (good.blockShading_constant_multiplicity index)).1

end PureWZ2TerminalPopularGoodBlockFamilyData

/-- A mass-heavy separated residue of paper-order block outputs. -/
structure PureWZ2TerminalPopularBlockResidueData
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared) where
  residue : Fin 16
  selected : Finset (Fin good.indexCount)
  selected_eq : selected = Finset.univ.filter fun index =>
    (good.block index % (16 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  total_mass_le :
    (∑ index : Fin good.indexCount, (good.blockShading index).mass) ≤
      16 * ∑ index ∈ selected, (good.blockShading index).mass
  separated_cores : ∀ first second : Fin good.indexCount,
    first ∈ selected → second ∈ selected → first ≠ second →
      ∀ z ∈ (good.output first).exactTrapezoid.trapezoid.core,
        ∀ w ∈ (good.output second).exactTrapezoid.trapezoid.core,
          Real.sqrt delta ≤ |z - w|

namespace PureWZ2TerminalPopularGoodBlockFamilyData

variable
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared)

private lemma block_residue_separated
    {first second : ℤ}
    (hne : first ≠ second)
    (hmod : first % (16 : ℤ) = second % (16 : ℤ)) :
    (16 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (16 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  have hdiv : (16 : ℤ) ∣ first - second := by
    rwa [Int.dvd_iff_emod_eq_zero]
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne) hdiv

/-- Select one mod-16 class by the actual indexed mass of the source-family
height lifts. -/
theorem selectResidue :
    Nonempty (PureWZ2TerminalPopularBlockResidueData good) := by
  let label : Fin good.indexCount → Fin 16 := fun index =>
    ⟨(good.block index % (16 : ℤ)).toNat, by
      have hnonneg : 0 ≤ good.block index % (16 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : good.block index % (16 : ℤ) < (16 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let weight : Fin good.indexCount → ENNReal := fun index =>
    (good.blockShading index).mass
  rcases finset_ennreal_weighted_pigeonhole (n := 16) (by norm_num)
      Finset.univ weight label with ⟨residue, hretained⟩
  let selected := Finset.univ.filter fun index => label index = residue
  have htotalPos : 0 < ∑ index : Fin good.indexCount, weight index := by
    let first : Fin good.indexCount := ⟨0, good.indexCount_pos⟩
    have hsingle : (good.blockShading first).mass ≤
        ∑ index : Fin good.indexCount, (good.blockShading index).mass :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun index : Fin good.indexCount =>
          (good.blockShading index).mass)
        (fun _ _ => bot_le) (Finset.mem_univ first)
    exact (good.blockShading_mass_pos first).trans_le (by
      simpa [weight] using hsingle)
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ index ∈ selected, weight index = 0 := by
      simp [hselectedEmpty]
    have hleZero : (∑ index : Fin good.indexCount, weight index) ≤ 0 := by
      simpa [selected, hzero] using hretained
    exact (not_le_of_gt htotalPos) hleZero
  refine ⟨{
    residue := residue
    selected := selected
    selected_eq := by
      apply Finset.ext
      intro index
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        exact Fin.ext (by simpa [label] using h)
    selected_nonempty := hselectedNonempty
    total_mass_le := by simpa [weight, selected] using hretained
    separated_cores := ?_
  }⟩
  intro first second hfirst hsecond hne z hz w hw
  have hfirstResidue : label first = residue := by
    simpa [selected] using hfirst
  have hsecondResidue : label second = residue := by
    simpa [selected] using hsecond
  have hfirstNonneg : 0 ≤ good.block first % (16 : ℤ) :=
    Int.emod_nonneg _ (by norm_num)
  have hsecondNonneg : 0 ≤ good.block second % (16 : ℤ) :=
    Int.emod_nonneg _ (by norm_num)
  have hfirstNat : (good.block first % (16 : ℤ)).toNat = residue.val := by
    simpa [label] using congrArg Fin.val hfirstResidue
  have hsecondNat : (good.block second % (16 : ℤ)).toNat = residue.val := by
    simpa [label] using congrArg Fin.val hsecondResidue
  have hmod : good.block first % (16 : ℤ) =
      good.block second % (16 : ℤ) := by
    have hfirstInt : good.block first % (16 : ℤ) = (residue : ℤ) := by
      rw [← Int.toNat_of_nonneg hfirstNonneg]
      exact_mod_cast hfirstNat
    have hsecondInt : good.block second % (16 : ℤ) = (residue : ℤ) := by
      rw [← Int.toNat_of_nonneg hsecondNonneg]
      exact_mod_cast hsecondNat
    exact hfirstInt.trans hsecondInt.symm
  have hblocks := block_residue_separated
    (fun heq => hne (good.block_injective heq)) hmod
  have hzWindow := (good.output first).exactTrapezoid.core_height_window hz
  have hwWindow := (good.output second).exactTrapezoid.core_height_window hw
  rw [good.window_left first] at hzWindow
  rw [good.window_left second] at hwWindow
  simp only [pureWZ2SourceCarrierBlockLeft] at hzWindow hwWindow
  have hroot : 0 < Real.sqrt delta :=
    Real.sqrt_pos.mpr source.extremal.delta_pos
  by_cases horder : good.block first < good.block second
  · have hdiffInt : (16 : ℤ) ≤ good.block second - good.block first := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks
      simpa using hblocks
    have hdiffReal : (16 : ℝ) ≤
        (good.block second : ℝ) - good.block first := by
      exact_mod_cast hdiffInt
    have hwz : 11 * Real.sqrt delta ≤ w - z := by
      nlinarith [hzWindow.2, hwWindow.1]
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith : 0 ≤ w - z)]
    nlinarith
  · have hreverse : good.block second < good.block first := by
      have hblockNe : good.block first ≠ good.block second := fun heq =>
        hne (good.block_injective heq)
      omega
    have hdiffInt : (16 : ℤ) ≤ good.block first - good.block second := by
      rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks
      exact hblocks
    have hdiffReal : (16 : ℝ) ≤
        (good.block first : ℝ) - good.block second := by
      exact_mod_cast hdiffInt
    have hzw : 11 * Real.sqrt delta ≤ z - w := by
      nlinarith [hzWindow.1, hwWindow.2]
    rw [abs_of_nonneg (by nlinarith : 0 ≤ z - w)]
    nlinarith

end PureWZ2TerminalPopularGoodBlockFamilyData

namespace PureWZ2TerminalPopularBlockResidueData

variable
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared}
    (data : PureWZ2TerminalPopularBlockResidueData good)

def selectedShading : WZ1PaperTubeShading terminal.sticky.selected.family where
  carrier selectedIndex := ⋃ index : {index // index ∈ data.selected},
    (good.blockShading index.1).carrier selectedIndex
  measurable_carrier selectedIndex := MeasurableSet.iUnion fun index =>
    (good.blockShading index.1).measurable_carrier selectedIndex
  subset_body selectedIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (good.blockShading index.1).subset_body selectedIndex hindex

@[simp] theorem mem_selectedShading_carrier_iff
    (selectedIndex : Fin terminal.sticky.selected.family.card) (point : Point3) :
    point ∈ data.selectedShading.carrier selectedIndex ↔
      ∃ index ∈ data.selected,
        point ∈ (good.blockShading index).carrier selectedIndex := by
  simp [selectedShading]

theorem selectedShading_subshading :
    PureWZ2PaperIsSubshading data.selectedShading terminalSource.shading := by
  intro selectedIndex point hpoint
  rcases (data.mem_selectedShading_carrier_iff selectedIndex point).mp hpoint with
    ⟨index, _hindex, hlocal⟩
  exact good.blockShading_subshading index selectedIndex hlocal

theorem mem_selectedShading_union_iff (point : Point3) :
    point ∈ data.selectedShading.union ↔
      ∃ index ∈ data.selected, point ∈ (good.blockShading index).union := by
  constructor
  · rintro ⟨selectedIndex, hpoint⟩
    rcases (data.mem_selectedShading_carrier_iff selectedIndex point).mp hpoint with
      ⟨index, hindex, hlocal⟩
    exact ⟨index, hindex, selectedIndex, hlocal⟩
  · rintro ⟨index, hindex, selectedIndex, hlocal⟩
    exact ⟨selectedIndex,
      (data.mem_selectedShading_carrier_iff selectedIndex point).mpr
        ⟨index, hindex, hlocal⟩⟩

theorem selected_union_pairwise_disjoint :
    (data.selected : Set (Fin good.indexCount)).PairwiseDisjoint fun index =>
      (good.blockShading index).union := by
  intro first hfirst second hsecond hne
  change Disjoint (good.blockShading first).union
    (good.blockShading second).union
  rw [Set.disjoint_left]
  intro point hpointFirst hpointSecond
  have hfirstSlice : horizontalSlice (good.blockShading first).union
      (point 2) ≠ ∅ := Set.nonempty_iff_ne_empty.mp
        ⟨point, hpointFirst, rfl⟩
  have hsecondSlice : horizontalSlice (good.blockShading second).union
      (point 2) ≠ ∅ := Set.nonempty_iff_ne_empty.mp
        ⟨point, hpointSecond, rfl⟩
  have hsep := data.separated_cores first second hfirst hsecond hne
    (point 2) ((good.output first).exactTrapezoid.active_height_coverage
      (point 2) hfirstSlice)
    (point 2) ((good.output second).exactTrapezoid.active_height_coverage
      (point 2) hsecondSlice)
  exact (not_le_of_gt (Real.sqrt_pos.mpr source.extremal.delta_pos))
    (by simpa using hsep)

theorem selected_carrier_pairwise_disjoint
    (selectedIndex : Fin terminal.sticky.selected.family.card) :
    Pairwise fun first second : {index // index ∈ data.selected} =>
      Disjoint ((good.blockShading first.1).carrier selectedIndex)
        ((good.blockShading second.1).carrier selectedIndex) := by
  intro first second hne
  exact (data.selected_union_pairwise_disjoint first.property second.property
    (Subtype.coe_injective.ne hne)).mono
      (fun point hpoint =>
        show point ∈ (good.blockShading first.1).union from
          ⟨selectedIndex, hpoint⟩)
      (fun point hpoint =>
        show point ∈ (good.blockShading second.1).union from
          ⟨selectedIndex, hpoint⟩)

theorem selectedShading_mass_eq_sum :
    data.selectedShading.mass =
      ∑ index ∈ data.selected, (good.blockShading index).mass := by
  calc
    data.selectedShading.mass =
        ∑ selectedIndex : Fin terminal.sticky.selected.family.card,
          volume (⋃ index : {index // index ∈ data.selected},
            (good.blockShading index.1).carrier selectedIndex) := rfl
    _ = ∑ selectedIndex : Fin terminal.sticky.selected.family.card,
          ∑ index : {index // index ∈ data.selected},
            volume ((good.blockShading index.1).carrier selectedIndex) := by
      apply Finset.sum_congr rfl
      intro selectedIndex _
      rw [MeasureTheory.measure_iUnion
        (data.selected_carrier_pairwise_disjoint selectedIndex)
        (fun index =>
          (good.blockShading index.1).measurable_carrier selectedIndex)]
      simp [tsum_fintype]
    _ = ∑ index : {index // index ∈ data.selected},
          ∑ selectedIndex : Fin terminal.sticky.selected.family.card,
            volume ((good.blockShading index.1).carrier selectedIndex) := by
      rw [Finset.sum_comm]
    _ = ∑ index : {index // index ∈ data.selected},
          (good.blockShading index.1).mass := rfl
    _ = ∑ index ∈ data.selected, (good.blockShading index).mass := by
      exact (Finset.sum_subtype data.selected (fun _ => Iff.rfl)
        (fun index : Fin good.indexCount =>
          (good.blockShading index).mass)).symm

theorem selectedShading_constant_multiplicity :
    data.selectedShading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
  intro point hpoint
  rcases (data.mem_selectedShading_union_iff point).mp hpoint with
    ⟨index, hindex, selectedIndex, hlocal⟩
  have hlocal' := hlocal
  rw [(good.output index).chain.outerHeightLift.carrier_eq] at hlocal'
  have hregion := hlocal'.2
  have hmultiplicity : data.selectedShading.pointMultiplicity point =
      terminalSource.shading.pointMultiplicity point := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    congr 1
    ext target
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases (data.mem_selectedShading_carrier_iff target point).mp h with
        ⟨_block, _hblock, htarget⟩
      have htarget' := htarget
      rw [(good.output _block).chain.outerHeightLift.carrier_eq] at htarget'
      exact htarget'.1
    · intro htarget
      exact (data.mem_selectedShading_carrier_iff target point).mpr
        ⟨index, hindex, by
          rw [(good.output index).chain.outerHeightLift.carrier_eq]
          exact ⟨htarget, hregion⟩⟩
  rw [hmultiplicity]
  exact terminalSource.constant_multiplicity point ⟨selectedIndex, hlocal'.1⟩

noncomputable def zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData terminal.sticky.selected
      data.selectedShading :=
  Classical.choice <| wz2_paper_subfamily_zero_extension
    terminal.sticky.selected data.selectedShading

noncomputable def finalShading : WZ1PaperTubeShading source.family :=
  data.zeroExtension.ambientShading

theorem finalShading_mass_eq_sum :
    data.finalShading.mass =
      ∑ index ∈ data.selected, (good.blockShading index).mass := by
  rw [show data.finalShading.mass = data.selectedShading.mass from
    data.zeroExtension.mass_eq, data.selectedShading_mass_eq_sum]

theorem finalShading_union_eq :
    data.finalShading.union = data.selectedShading.union :=
  data.zeroExtension.union_eq

theorem finalShading_subshading :
    PureWZ2PaperIsSubshading data.finalShading source.shading := by
  intro ambient point hpoint
  rcases data.zeroExtension.carrier_support ambient point hpoint with
    ⟨selectedIndex, heq, hselected⟩
  subst ambient
  apply terminal.sticky.subshading selectedIndex
  exact (congrArg (fun shading => point ∈ shading.carrier selectedIndex)
    terminalSource.shading_eq).mp
      (data.selectedShading_subshading selectedIndex hselected)

theorem finalShading_volume_lower
    (hscalar :
      32 * good.sourceMassCost *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta (sigma + stickyLoss)) :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume data.finalShading.union := by
  let multiplicity : ENNReal := terminalSource.multiplicity
  have hmultiplicityZero : multiplicity ≠ 0 := by
    dsimp only [multiplicity]
    exact_mod_cast terminalSource.multiplicity_pos.ne'
  have hmultiplicityTop : multiplicity ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsourceMassFloor : multiplicity *
      Kakeya.realRpowENN delta (sigma + stickyLoss) ≤
        terminalSource.shading.mass :=
    (mul_le_mul_right terminalSource.volume_lower multiplicity).trans
      (constant_multiplicity_mass_volume_generic
        terminalSource.constant_multiplicity).1
  have hterminalGood : terminalSource.shading.mass ≤
      good.sourceMassCost * ∑ index : Fin good.indexCount,
        (good.sourceShading index).mass := good.source_mass_control
  have hlocal : ∀ index : Fin good.indexCount,
      Kakeya.realRpowENN delta localMassLoss *
          (good.sourceShading index).mass ≤
        (good.blockShading index).mass := by
    intro index
    have hsourceUpper := (constant_multiplicity_mass_volume_generic
      (good.sourceShading_constant_multiplicity index)).2
    have htargetLower := (constant_multiplicity_mass_volume_generic
      (good.blockShading_constant_multiplicity index)).1
    calc
      Kakeya.realRpowENN delta localMassLoss *
          (good.sourceShading index).mass ≤
        Kakeya.realRpowENN delta localMassLoss *
          ((2 * multiplicity) *
            volume (good.sourceShading index).union) := by
          gcongr
      _ = multiplicity *
          (2 * Kakeya.realRpowENN delta localMassLoss *
            volume (good.sourceShading index).union) := by
          ring
      _ ≤ multiplicity * volume (good.blockShading index).union := by
          gcongr
          exact good.block_volume_retention index
      _ ≤ (good.blockShading index).mass := htargetLower
  have hlocalSum : Kakeya.realRpowENN delta localMassLoss *
      (∑ index : Fin good.indexCount,
        (good.sourceShading index).mass) ≤
      ∑ index : Fin good.indexCount, (good.blockShading index).mass := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun index _ => hlocal index
  have hmassChain : Kakeya.realRpowENN delta localMassLoss *
      (multiplicity * Kakeya.realRpowENN delta (sigma + stickyLoss)) ≤
      (32 * good.sourceMassCost) *
        (multiplicity * volume data.finalShading.union) := by
    calc
      _ ≤ Kakeya.realRpowENN delta localMassLoss *
          terminalSource.shading.mass := by gcongr
      _ ≤ Kakeya.realRpowENN delta localMassLoss *
          (good.sourceMassCost * ∑ index : Fin good.indexCount,
            (good.sourceShading index).mass) := by
          gcongr
      _ = good.sourceMassCost * (Kakeya.realRpowENN delta localMassLoss *
          ∑ index : Fin good.indexCount,
            (good.sourceShading index).mass) := by ring
      _ ≤ good.sourceMassCost * ∑ index : Fin good.indexCount,
          (good.blockShading index).mass := by gcongr
      _ ≤ good.sourceMassCost * (16 * ∑ index ∈ data.selected,
          (good.blockShading index).mass) :=
        mul_le_mul_right data.total_mass_le good.sourceMassCost
      _ = (16 * good.sourceMassCost) * data.selectedShading.mass := by
        rw [data.selectedShading_mass_eq_sum]
        ring
      _ ≤ (16 * good.sourceMassCost) * ((2 * multiplicity : ENNReal) *
          volume data.selectedShading.union) := by
        gcongr
        exact (constant_multiplicity_mass_volume_generic
          data.selectedShading_constant_multiplicity).2
      _ = (32 * good.sourceMassCost) *
          (multiplicity * volume data.finalShading.union) := by
        rw [data.finalShading_union_eq]
        dsimp only [multiplicity]
        ring
  have hscaled : multiplicity *
      ((32 * good.sourceMassCost) *
        Kakeya.realRpowENN delta (sigma + outputLoss)) ≤
      multiplicity * ((32 * good.sourceMassCost) *
        volume data.finalShading.union) := by
    calc
      multiplicity *
          ((32 * good.sourceMassCost) *
            Kakeya.realRpowENN delta (sigma + outputLoss)) ≤
        multiplicity *
          (Kakeya.realRpowENN delta localMassLoss *
            Kakeya.realRpowENN delta (sigma + stickyLoss)) := by gcongr
      _ = Kakeya.realRpowENN delta localMassLoss *
          (multiplicity * Kakeya.realRpowENN delta (sigma + stickyLoss)) := by ring
      _ ≤ (32 * good.sourceMassCost) *
          (multiplicity * volume data.finalShading.union) := hmassChain
      _ = multiplicity * ((32 * good.sourceMassCost) *
          volume data.finalShading.union) := by ring
  have hcancelMultiplicity :
      (32 * good.sourceMassCost) *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        (32 * good.sourceMassCost) * volume data.finalShading.union :=
    (ENNReal.mul_le_mul_iff_right hmultiplicityZero hmultiplicityTop).mp hscaled
  exact (ENNReal.mul_le_mul_iff_right
    (mul_ne_zero (by norm_num) good.sourceMassCost_pos.ne')
    (ENNReal.mul_ne_top (by norm_num) good.sourceMassCost_ne_top)).mp
      hcancelMultiplicity

theorem toExactTerminalLevel
    (data : PureWZ2TerminalPopularBlockResidueData good)
    (hinputOutput : inputLoss ≤ outputLoss)
    (hscalar :
      32 * good.sourceMassCost *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta (sigma + stickyLoss)) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  have hsub := PureWZ2TerminalPopularBlockResidueData.finalShading_subshading
    (data := data)
  have hvolume := PureWZ2TerminalPopularBlockResidueData.finalShading_volume_lower
    (data := data) hscalar
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputOutput
  have hconstantTop : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant hsub hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict hsub hconstant hconstantTop
  let trapezoids : Finset WZ1VerticalTrapezoid :=
    data.selected.image fun index =>
      (good.output index).exactTrapezoid.trapezoid
  exact ⟨{
    shading := data.finalShading
    subshading := hsub
    volume_lower := hvolume
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact source.planeMap_vertical_bound
        ⟨point, hsub.union_subset point.property⟩
    sourceGlobalGrains := globalGrains
    source_slope_eq := rfl
    trapezoids := trapezoids
    trapezoids_nonempty := data.selected_nonempty.image _
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      exact (good.output index).exactTrapezoid.height_eq
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      exact (good.output index).exactTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      exact (good.output index).exactTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with ⟨first, hfirst, rfl⟩
      rcases Finset.mem_image.mp hother with ⟨second, hsecond, rfl⟩
      have hindexNe : first ≠ second := by
        intro heq
        subst second
        exact hne rfl
      exact data.separated_cores first second hfirst hsecond hindexNe
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with ⟨target, htarget, rfl⟩
      rw [data.finalShading_union_eq] at hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (data.mem_selectedShading_union_iff point).mp hpoint.1 with
        ⟨sourceIndex, hsourceIndex, selectedIndex, hlocal⟩
      have hlocal' := hlocal
      rw [(good.output sourceIndex).chain.outerHeightLift.carrier_eq] at hlocal'
      rcases hlocal' with ⟨hsource, hregion⟩
      have hsourcePoint : point ∈
          (good.blockShading sourceIndex).carrier selectedIndex :=
        hlocal
      have hsourceSlice : horizontalSlice
          (good.blockShading sourceIndex).union z ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp ⟨point, ⟨selectedIndex, hsourcePoint⟩, hpoint.2⟩
      have hsourceCore :=
        (good.output sourceIndex).exactTrapezoid.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (good.output target).exactTrapezoid.trapezoid =
            (good.output sourceIndex).exactTrapezoid.trapezoid
      · rw [heq]
        change |source.globalGrains.slope z -
          (good.output sourceIndex).exactTrapezoid.trapezoid.affine z| ≤ delta
        exact (good.output sourceIndex).exactTrapezoid.slope_approximation
          z hsourceCore hsourceSlice
      · have hindexNe : target ≠ sourceIndex := by
          intro hindex
          subst sourceIndex
          exact heq rfl
        have hsep := data.separated_cores target sourceIndex
          htarget hsourceIndex hindexNe z hz z hsourceCore
        exact False.elim ((not_le_of_gt
          (Real.sqrt_pos.mpr source.extremal.delta_pos)) (by simpa using hsep))
    active_height_coverage := by
      intro z _hz hslice
      rw [data.finalShading_union_eq] at hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (data.mem_selectedShading_union_iff point).mp hpoint.1 with
        ⟨index, hindex, selectedIndex, hlocal⟩
      have hlocal' := hlocal
      rw [(good.output index).chain.outerHeightLift.carrier_eq] at hlocal'
      rcases hlocal' with ⟨hsource, hregion⟩
      have hsourcePoint : point ∈ (good.blockShading index).carrier
          selectedIndex := hlocal
      have hlocalSlice : horizontalSlice (good.blockShading index).union z ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp ⟨point, ⟨selectedIndex, hsourcePoint⟩, hpoint.2⟩
      exact ⟨(good.output index).exactTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩,
        (good.output index).exactTrapezoid.active_height_coverage
          z hlocalSlice⟩
  }⟩

end PureWZ2TerminalPopularBlockResidueData

end Kakeya.Assouad

end
