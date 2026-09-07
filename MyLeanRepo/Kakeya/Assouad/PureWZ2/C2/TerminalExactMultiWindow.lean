import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalWindowBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalChainAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactHeightLift

/-!
# Exact terminal multi-window assembly

The last level of the Corollary-5.6 iteration cannot be obtained from one
`sqrt delta` window: that would lose a fixed half power of `delta`.  As in
the paper, this file runs the local construction on every popular height
block, retains one separated residue class, and takes the finite union of
the resulting exact rich-set shadings.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Uniform Alternative-A height count at the twice-normalized exact terminal
graph scale. -/
def pureWZ2TerminalExactRichFloor
    (delta outputLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN
    (wz1Lemma23Theorem22Scale (delta / 625)) (outputLoss - 1)

/-- The two logarithmic popularity costs and the number of source-popular
height layers in a terminal window. -/
def pureWZ2TerminalExactHeightRetentionCost
    (delta extraLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (2 * Real.rpow delta (-extraLoss)) *
    ENNReal.ofReal (3 / Real.sqrt delta)

/-- Completed exact-rich outputs on every good terminal height block. -/
structure PureWZ2TerminalExactGoodBlockFamilyData
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) where
  indexCount : ℕ
  indexCount_pos : 0 < indexCount
  block : Fin indexCount → ℤ
  block_injective : Function.Injective block
  block_mem : ∀ index, block index ∈ pureWZ2GoodTerminalBlocks prepared
  block_surjective : ∀ target ∈ pureWZ2GoodTerminalBlocks prepared,
    ∃ index, block index = target
  windowData : ∀ index, PureWZ2TerminalBlockWindowData prepared (block index)
  chain : ∀ index, PureWZ2TerminalWindowChainOutput
    (eta := eta) (theoremEta := theoremEta) (outputLoss := outputLoss)
    (windowData index).window
  /-- The paper-faithful return from the auxiliary graph to the original
  source shading over its selected rich heights. -/
  heightLift : ∀ index, PureWZ2TerminalExactHeightLift
    (chain index).exactTrapezoid
  extraLoss : ℝ
  extraCost_power : ∀ index,
    ((chain index).preparedGraph.graph.residue.extraCost : ℝ) ≤
      Real.rpow delta (-extraLoss)

namespace PureWZ2TerminalExactGoodBlockFamilyData

/-- Popular height layers in one exact terminal graph lie in the same
`O(delta⁻¹/²)` window as the graph cells. -/
theorem popular_heights_le_cap
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (data : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared)
    (index : Fin data.indexCount) :
    ((data.chain index).preparedGraph.heightPopular.heightIndices.card :
        ENNReal) ≤ ENNReal.ofReal (3 / Real.sqrt delta) := by
  let chain := data.chain index
  have hsubset : chain.preparedGraph.heightPopular.heightIndices ⊆
      wz1Lemma23SnappedHeights chain.prep.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈
        chain.prep.windowed.global.heightIndices := by
      rw [chain.prep.windowed.global.heightIndices_eq]
      exact chain.preparedGraph.heightPopular.heightIndices_subset hheight
    have hlayerNonempty :
        (chain.prep.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < volume
          (chain.prep.shadow.union ∩
            wz1Lemma23HeightSlab delta heightIndex) :=
        chain.preparedGraph.heightPopular.layerMass_pos.trans_le
          (chain.preparedGraph.heightPopular.layer_volume_band
            heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := chain.prep.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two chain.prep.shadow
        source.extremal.delta_pos
        (by
          intro point hpoint
          have hpaper : point ∈ chain.retained.shading.union := by
            have hambient := chain.prep.subshading.union_subset hpoint
            rwa [chain.prep.ambient_union] at hambient
          have hsource : point ∈ source.shading.union :=
            chain.retained.subshading.union_subset hpaper
          have hnorm := norm_le_two_of_mem_paperShading hsource
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (chain.prep.windowed.global.selectedHeight heightIndex)
      have hemptyExact : wz1Lemma23ExactSliceCells chain.prep.shadow delta
          source.extremal.delta_pos
          (chain.prep.windowed.global.selectedHeight heightIndex) = ∅ := by
        rw [← chain.prep.windowed.global.layerCells_eq heightIndex]
        exact hlayerEmpty
      rw [hemptyExact] at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal
          (gridSide (delta / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        rw [gridSide]
        exact div_pos (by nlinarith [source.extremal.delta_pos])
          (Real.sqrt_pos.mpr (by norm_num))
      have hzero : volume
          (chain.prep.shadow.union ∩
            wz1Lemma23HeightSlab delta heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : volume
              (chain.prep.shadow.union ∩
                wz1Lemma23HeightSlab delta heightIndex) /
              ENNReal.ofReal (gridSide (delta / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈ chain.prep.windowed.global.cells := by
      rw [chain.prep.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr ⟨cell, hcellGlobal, by
      exact chain.prep.windowed.global.layer_height
        heightIndex hglobal cell hcell⟩
  have hreal := wz1Lemma23_height_layer_count
    source.extremal.delta_pos source.extremal.delta_le_one
    chain.prep.windowed.global_cells_window
  have hcardReal :
      (chain.preparedGraph.heightPopular.heightIndices.card : ℝ) ≤
        3 / Real.sqrt delta := by
    have hcast :
        (chain.preparedGraph.heightPopular.heightIndices.card : ℝ) ≤
          ((wz1Lemma23SnappedHeights
            chain.prep.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  exact (ENNReal.natCast_le_ofReal
    chain.preparedGraph.heightPopular.heightIndices_nonempty.card_ne_zero).mpr
      hcardReal

/-- One exact terminal block supply controls the indexed mass of its exact
rich-set output. -/
theorem block_mass_bound
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (data : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared)
    (index : Fin data.indexCount) :
    (data.windowData index).window.volumeSupply *
          terminal.sticky.balanced.cellMass *
          (terminalSource.multiplicity : ENNReal) *
          pureWZ2TerminalExactRichFloor delta outputLoss ≤
      pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
        pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
        (data.chain index).exactTrapezoid.shading.mass := by
  let chain := data.chain index
  let cost := pureWZ2TerminalExactVolumeCost delta sigma inputLoss
  let floor := pureWZ2TerminalExactRichFloor delta outputLoss
  have hsupply : (data.windowData index).window.volumeSupply *
        terminal.sticky.balanced.cellMass ≤
      cost * volume chain.prep.shadow.union := by
    simpa [chain, cost] using chain.prep.volume_supply_le
  have hpopular : volume chain.prep.shadow.union ≤
      2 * chain.preparedGraph.heightPopular.bins *
        volume chain.preparedGraph.heightPopular.shading.union := by
    have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      chain.preparedGraph.heightPopular.retained_volume
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hfloor : floor ≤ (chain.rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        chain.ready.ready.deltaGraph (outputLoss - 1) := by
      dsimp only [floor, pureWZ2TerminalExactRichFloor]
      rw [chain.ready.deltaGraph_eq, chain.first.ready.deltaGraph_eq]
      have hsqrt : Real.sqrt (delta / 625) = Real.sqrt delta / 25 := by
        rw [Real.sqrt_div source.extremal.delta_pos.le]
        norm_num
      simp only [wz1Lemma23Theorem22Scale]
      rw [hsqrt]
      ring
    rw [hfloorEq]
    simpa [chain.rich.heightIndices_card] using chain.rich.richF_card
  have hpopularLayer : volume
        chain.preparedGraph.heightPopular.shading.union ≤
      2 * (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
        chain.preparedGraph.heightPopular.layerMass := by
    rw [chain.preparedGraph.heightPopular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ chain.preparedGraph.heightPopular.heightIndices,
          volume (chain.prep.shadow.union ∩
            wz1Lemma23HeightSlab delta heightIndex)) ≤
        ∑ _heightIndex ∈ chain.preparedGraph.heightPopular.heightIndices,
          2 * chain.preparedGraph.heightPopular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (chain.preparedGraph.heightPopular.layer_volume_band
            heightIndex hheight).2
      _ = 2 *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
            chain.preparedGraph.heightPopular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hweightedMass :
      floor * volume chain.prep.shadow.union *
          (terminalSource.multiplicity : ENNReal) ≤
        4 * chain.preparedGraph.heightPopular.bins *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
            chain.exactTrapezoid.shading.mass := by
    calc
      floor * volume chain.prep.shadow.union *
            (terminalSource.multiplicity : ENNReal) ≤
        floor * (2 * chain.preparedGraph.heightPopular.bins *
          volume chain.preparedGraph.heightPopular.shading.union) *
            (terminalSource.multiplicity : ENNReal) := by gcongr
      _ ≤ floor * (2 * chain.preparedGraph.heightPopular.bins *
          (2 *
            (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
              chain.preparedGraph.heightPopular.layerMass)) *
            (terminalSource.multiplicity : ENNReal) := by gcongr
      _ ≤ (chain.rich.heightIndices.card : ENNReal) *
          (2 * chain.preparedGraph.heightPopular.bins *
            (2 *
              (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
                chain.preparedGraph.heightPopular.layerMass)) *
            (terminalSource.multiplicity : ENNReal) := by gcongr
      _ = 4 * chain.preparedGraph.heightPopular.bins *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
          ((terminalSource.multiplicity : ENNReal) *
            ((chain.rich.heightIndices.card : ENNReal) *
              chain.preparedGraph.heightPopular.layerMass)) := by ring
      _ ≤ 4 * chain.preparedGraph.heightPopular.bins *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
            chain.exactTrapezoid.shading.mass := by
        exact mul_le_mul_left'
          ((mul_le_mul_left' chain.exactTrapezoid.volume_lower
              (terminalSource.multiplicity : ENNReal)).trans
            chain.exactTrapezoid.multiplicity_mass_lower)
          (4 * chain.preparedGraph.heightPopular.bins *
            (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal))
  have hlogPos : 1 ≤ Nat.log 2 chain.preparedGraph.rawResidue.cells.card + 1 :=
    by omega
  have hbinsNat : 4 * chain.preparedGraph.heightPopular.bins ≤
      2 * chain.preparedGraph.graph.residue.extraCost := by
    rw [chain.preparedGraph.extraCost_eq]
    nlinarith
  have hbinsENN : (4 * chain.preparedGraph.heightPopular.bins : ENNReal) ≤
      2 * (chain.preparedGraph.graph.residue.extraCost : ENNReal) := by
    exact_mod_cast hbinsNat
  have hextraENN : (chain.preparedGraph.graph.residue.extraCost : ENNReal) ≤
      ENNReal.ofReal (Real.rpow delta (-data.extraLoss)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (data.extraCost_power index)
  have hheight := data.popular_heights_le_cap index
  have hretention :
      (4 * chain.preparedGraph.heightPopular.bins : ENNReal) *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) ≤
        pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss := by
    calc
      (4 * chain.preparedGraph.heightPopular.bins : ENNReal) *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) ≤
        (2 * (chain.preparedGraph.graph.residue.extraCost : ENNReal)) *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) := by
        gcongr
      _ ≤ (2 * ENNReal.ofReal (Real.rpow delta (-data.extraLoss))) *
          ENNReal.ofReal (3 / Real.sqrt delta) := by gcongr
      _ = pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss := by
        unfold pureWZ2TerminalExactHeightRetentionCost
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  calc
    (data.windowData index).window.volumeSupply *
          terminal.sticky.balanced.cellMass *
          (terminalSource.multiplicity : ENNReal) * floor ≤
      (cost * volume chain.prep.shadow.union) *
          (terminalSource.multiplicity : ENNReal) * floor := by gcongr
    _ = cost * (floor * volume chain.prep.shadow.union *
          (terminalSource.multiplicity : ENNReal)) := by ring
    _ ≤ cost *
        (4 * chain.preparedGraph.heightPopular.bins *
          (chain.preparedGraph.heightPopular.heightIndices.card : ENNReal) *
            chain.exactTrapezoid.shading.mass) := by
      exact mul_le_mul_left' hweightedMass cost
    _ ≤ cost *
        (pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
          chain.exactTrapezoid.shading.mass) := by gcongr
    _ = cost * pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
        chain.exactTrapezoid.shading.mass := by ring

/-- The same local calculation with the common multiplicity cancelled. -/
theorem block_volume_bound
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (data : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared)
    (index : Fin data.indexCount) :
    (data.windowData index).window.volumeSupply *
          terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss ≤
      2 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
        pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
        volume (data.chain index).exactTrapezoid.shading.union := by
  let multiplicity : ENNReal := terminalSource.multiplicity
  have hmultiplicityZero : multiplicity ≠ 0 := by
    dsimp only [multiplicity]
    exact_mod_cast terminalSource.multiplicity_pos.ne'
  have hmultiplicityTop : multiplicity ≠ ⊤ := ENNReal.natCast_ne_top _
  have hupper :=
    (constant_multiplicity_mass_volume_generic
      (data.chain index).exactTrapezoid.constant_multiplicity).2
  have hscaled :
      ((data.windowData index).window.volumeSupply *
          terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss) * multiplicity ≤
        (2 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
          volume (data.chain index).exactTrapezoid.shading.union) *
            multiplicity := by
    calc
      ((data.windowData index).window.volumeSupply *
          terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss) * multiplicity =
        (data.windowData index).window.volumeSupply *
          terminal.sticky.balanced.cellMass * multiplicity *
          pureWZ2TerminalExactRichFloor delta outputLoss := by ring
      _ ≤ pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
          (data.chain index).exactTrapezoid.shading.mass :=
        data.block_mass_bound index
      _ ≤ pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
          ((2 * terminalSource.multiplicity : ENNReal) *
            volume (data.chain index).exactTrapezoid.shading.union) := by gcongr
      _ = (2 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta data.extraLoss *
          volume (data.chain index).exactTrapezoid.shading.union) *
            multiplicity := by
        dsimp only [multiplicity]
        push_cast
        ring
  apply (ENNReal.mul_le_mul_iff_right hmultiplicityZero hmultiplicityTop).mp
  simpa [mul_comm] using hscaled

end PureWZ2TerminalExactGoodBlockFamilyData

/-- Completed local outputs before the final height-residue selection. -/
structure PureWZ2TerminalExactBlockFamilyData
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared) where
  /-- The selected block residue.  Modulo 16 is enough because every local
  terminal core stays within two blocks below and three blocks above its
  source block. -/
  residue : Fin 16
  selected : Finset (Fin good.indexCount)
  selected_eq : selected = Finset.univ.filter fun index =>
    (good.block index % (16 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  total_volume_le :
    (∑ index : Fin good.indexCount,
        volume (good.chain index).exactTrapezoid.shading.union) ≤
      16 * ∑ index ∈ selected,
        volume (good.chain index).exactTrapezoid.shading.union

namespace PureWZ2TerminalExactGoodBlockFamilyData

/-- Select one mass-heavy congruence class of completed terminal windows. -/
theorem selectResidue
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared) :
    Nonempty (PureWZ2TerminalExactBlockFamilyData good) := by
  let label : Fin good.indexCount → Fin 16 := fun index =>
    ⟨(good.block index % (16 : ℤ)).toNat, by
      have hnonneg : 0 ≤ good.block index % (16 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : good.block index % (16 : ℤ) < (16 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let weight : Fin good.indexCount → ENNReal := fun index =>
    volume (good.chain index).exactTrapezoid.shading.union
  rcases finset_ennreal_weighted_pigeonhole (n := 16) (by norm_num)
      Finset.univ weight label with ⟨residue, hretained⟩
  let selected := Finset.univ.filter fun index => label index = residue
  have hweightPos : ∀ index : Fin good.indexCount, 0 < weight index := by
    intro index
    dsimp only [weight]
    have hheight : 0 <
        ((good.chain index).rich.heightIndices.card : ENNReal) := by
      exact_mod_cast
        (good.chain index).rich.heightIndices_card.trans_gt
          (good.chain index).rich.richF_nonempty.card_pos
    have hlayer :=
      (good.chain index).preparedGraph.heightPopular.layerMass_pos
    have hproduct : 0 <
        ((good.chain index).rich.heightIndices.card : ENNReal) *
          (good.chain index).preparedGraph.heightPopular.layerMass :=
      ENNReal.mul_pos hheight.ne' hlayer.ne'
    exact hproduct.trans_le
      (good.chain index).exactTrapezoid.volume_lower
  have htotalPos : 0 < ∑ index : Fin good.indexCount, weight index := by
    let first : Fin good.indexCount := ⟨0, good.indexCount_pos⟩
    exact (hweightPos first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ index ∈ selected, weight index = 0 := by
      simp [hselectedEmpty]
    have hleZero : (∑ index : Fin good.indexCount, weight index) ≤ 0 := by
      simpa [selected, hzero] using hretained
    exact (not_le_of_gt htotalPos) hleZero
  exact ⟨{
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
    total_volume_le := by simpa [weight, selected] using hretained }⟩

end PureWZ2TerminalExactGoodBlockFamilyData

namespace PureWZ2TerminalExactBlockFamilyData

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

/-- Selected exact terminal cores are separated by `sqrt delta`. -/
theorem separated_cores
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good)
    {first second : Fin good.indexCount}
    (hfirst : first ∈ data.selected) (hsecond : second ∈ data.selected)
    (hne : first ≠ second) :
    ∀ z ∈ (good.chain first).exactTrapezoid.trapezoid.core,
      ∀ w ∈ (good.chain second).exactTrapezoid.trapezoid.core,
        Real.sqrt delta ≤ |z - w| := by
  rw [data.selected_eq] at hfirst hsecond
  have hfirstResidue := (Finset.mem_filter.mp hfirst).2
  have hsecondResidue := (Finset.mem_filter.mp hsecond).2
  have hmod : good.block first % (16 : ℤ) =
      good.block second % (16 : ℤ) := by
    have hfirstNonneg : 0 ≤ good.block first % (16 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hsecondNonneg : 0 ≤ good.block second % (16 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    have hfirstInt : good.block first % (16 : ℤ) =
        (data.residue : ℤ) := by
      rw [← Int.toNat_of_nonneg hfirstNonneg]
      exact_mod_cast hfirstResidue
    have hsecondInt : good.block second % (16 : ℤ) =
        (data.residue : ℤ) := by
      rw [← Int.toNat_of_nonneg hsecondNonneg]
      exact_mod_cast hsecondResidue
    exact hfirstInt.trans hsecondInt.symm
  have hblocks := block_residue_separated
    (fun heq => hne (good.block_injective heq)) hmod
  intro z hz w hw
  have hzWindow :=
    (good.chain first).exactTrapezoid.core_height_window hz
  have hwWindow :=
    (good.chain second).exactTrapezoid.core_height_window hw
  rw [(good.windowData first).left_eq] at hzWindow
  rw [(good.windowData second).left_eq] at hwWindow
  simp only [pureWZ2SourceCarrierBlockLeft] at hzWindow hwWindow
  have hroot : 0 < Real.sqrt delta :=
    Real.sqrt_pos.mpr source.extremal.delta_pos
  by_cases horder : good.block first < good.block second
  · have hdiffInt : (16 : ℤ) ≤ good.block second - good.block first := by
      rw [abs_of_nonpos (sub_nonpos.mpr horder.le)] at hblocks
      simpa using hblocks
    have hdiffReal : (16 : ℝ) ≤
        (good.block second : ℝ) - good.block first := by exact_mod_cast hdiffInt
    have hwz : 11 * Real.sqrt delta ≤ w - z := by
      nlinarith [hzWindow.2, hwWindow.1]
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith : 0 ≤ w - z)]
    exact (by nlinarith : Real.sqrt delta ≤ w - z)
  · have hreverse : good.block second < good.block first := by
      have hblockNe : good.block first ≠ good.block second := fun heq =>
        hne (good.block_injective heq)
      omega
    have hdiffInt : (16 : ℤ) ≤ good.block first - good.block second := by
      rw [abs_of_nonneg (sub_nonneg.mpr hreverse.le)] at hblocks
      exact hblocks
    have hdiffReal : (16 : ℝ) ≤
        (good.block first : ℝ) - good.block second := by exact_mod_cast hdiffInt
    have hzw : 11 * Real.sqrt delta ≤ z - w := by
      nlinarith [hzWindow.1, hwWindow.2]
    rw [abs_of_nonneg (by nlinarith : 0 ≤ z - w)]
    exact (by nlinarith : Real.sqrt delta ≤ z - w)

/-- The final non-cubical union of exact rich-set shadings. -/
def shading
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good) :
    WZ1PaperTubeShading source.family where
  carrier sourceIndex := ⋃ index : {index // index ∈ data.selected},
    (good.chain index.1).exactTrapezoid.shading.carrier sourceIndex
  measurable_carrier sourceIndex := MeasurableSet.iUnion fun index =>
    (good.chain index.1).exactTrapezoid.shading.measurable_carrier sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (good.chain index.1).exactTrapezoid.shading.subset_body
      sourceIndex hindex

@[simp] theorem mem_shading_carrier_iff
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good)
    (sourceIndex : Fin source.family.card) (point : Point3) :
    point ∈ data.shading.carrier sourceIndex ↔
      ∃ index ∈ data.selected,
        point ∈ (good.chain index).exactTrapezoid.shading.carrier sourceIndex := by
  simp [shading]

theorem subshading
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good) :
    PureWZ2PaperIsSubshading data.shading source.shading := by
  intro sourceIndex point hpoint
  rcases (data.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, _hindex, hlocal⟩
  exact (good.chain index).retained.subshading sourceIndex
    ((good.chain index).exactTrapezoid.subshading sourceIndex hlocal)

theorem mem_shading_union_iff
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good) (point : Point3) :
    point ∈ data.shading.union ↔
      ∃ index ∈ data.selected,
        point ∈ (good.chain index).exactTrapezoid.shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (data.mem_shading_carrier_iff sourceIndex point).mp hpoint with
      ⟨index, hindex, hlocal⟩
    exact ⟨index, hindex, sourceIndex, hlocal⟩
  · rintro ⟨index, hindex, sourceIndex, hlocal⟩
    exact ⟨sourceIndex,
      (data.mem_shading_carrier_iff sourceIndex point).mpr
        ⟨index, hindex, hlocal⟩⟩

/-- The exact-rich unions from distinct selected terminal blocks are
disjoint, since their active heights lie in separated trapezoid cores. -/
theorem union_pairwise_disjoint
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good) :
    (data.selected : Set (Fin good.indexCount)).PairwiseDisjoint fun index =>
      (good.chain index).exactTrapezoid.shading.union := by
  intro first hfirst second hsecond hne
  change Disjoint
    (good.chain first).exactTrapezoid.shading.union
    (good.chain second).exactTrapezoid.shading.union
  rw [Set.disjoint_left]
  intro point hpointFirst hpointSecond
  have hfirstSlice : horizontalSlice
      (good.chain first).exactTrapezoid.shading.union (point 2) ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hpointFirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (good.chain second).exactTrapezoid.shading.union (point 2) ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hpointSecond, rfl⟩
  have hsep := data.separated_cores hfirst hsecond hne
    (point 2)
    ((good.chain first).exactTrapezoid.active_height_coverage
      (point 2) hfirstSlice)
    (point 2)
    ((good.chain second).exactTrapezoid.active_height_coverage
      (point 2) hsecondSlice)
  have hroot : 0 < Real.sqrt delta :=
    Real.sqrt_pos.mpr source.extremal.delta_pos
  have hzero : ¬ Real.sqrt delta ≤ |point 2 - point 2| := by
    simpa using (not_le_of_gt hroot)
  exact hzero hsep

theorem shading_volume_eq_sum
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good) :
    volume data.shading.union = ∑ index ∈ data.selected,
      volume (good.chain index).exactTrapezoid.shading.union := by
  have hunion : data.shading.union =
      ⋃ index : {index // index ∈ data.selected},
        (good.chain index.1).exactTrapezoid.shading.union := by
    ext point
    constructor
    · intro hpoint
      rcases (data.mem_shading_union_iff point).mp hpoint with
        ⟨index, hindex, hlocal⟩
      exact Set.mem_iUnion.mpr ⟨⟨index, hindex⟩, hlocal⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨index, hlocal⟩
      exact (data.mem_shading_union_iff point).mpr
        ⟨index.1, index.2, hlocal⟩
  have hdisjoint : Pairwise (Function.onFun Disjoint
      (fun index : {index // index ∈ data.selected} =>
        (good.chain index.1).exactTrapezoid.shading.union)) := by
    intro first second hne
    exact data.union_pairwise_disjoint first.property second.property
      (Subtype.coe_injective.ne hne)
  rw [hunion, MeasureTheory.measure_iUnion hdisjoint]
  · rw [tsum_fintype]
    exact (Finset.sum_subtype data.selected (fun _ => Iff.rfl)
      (fun index : Fin good.indexCount =>
        volume (good.chain index).exactTrapezoid.shading.union)).symm
  · intro index
    exact measurableSet_shading_union
      (good.chain index.1).exactTrapezoid.shading

/-- Summing the local exact-rich bounds over all good windows and then
selecting one separated congruence class costs only the fixed factor `32`. -/
theorem aggregate_volume_bound
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good) :
    volume prepared.shadow.union * terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss ≤
      64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
        pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
        volume data.shading.union := by
  let localCost := pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
    pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss
  have hhalf := pureWZ2GoodTerminalBlocks_half prepared
  have hvolumeIndexed :
      (∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
          volume (pureWZ2TerminalBlockShading prepared block).union) =
        ∑ index : Fin good.indexCount,
          (good.windowData index).window.volumeSupply := by
    symm
    apply Finset.sum_bij (fun index _ => good.block index)
    · intro index _
      exact good.block_mem index
    · intro first _ second _ heq
      exact good.block_injective heq
    · intro block hblock
      rcases good.block_surjective block hblock with ⟨index, rfl⟩
      exact ⟨index, Finset.mem_univ index, rfl⟩
    · intro index _
      rw [(good.windowData index).supply_eq,
        (good.windowData index).shading_eq]
  have hlocal :
      (∑ index : Fin good.indexCount,
          (good.windowData index).window.volumeSupply) *
            terminal.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor delta outputLoss ≤
        2 * localCost * ∑ index : Fin good.indexCount,
          volume (good.chain index).exactTrapezoid.shading.union := by
    calc
      _ = ∑ index : Fin good.indexCount,
          ((good.windowData index).window.volumeSupply *
            terminal.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor delta outputLoss) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin good.indexCount,
          (2 * localCost *
            volume (good.chain index).exactTrapezoid.shading.union) := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [localCost, mul_assoc] using good.block_volume_bound index
      _ = 2 * localCost * ∑ index : Fin good.indexCount,
          volume (good.chain index).exactTrapezoid.shading.union := by
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union * terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss ≤
        (2 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
          volume (pureWZ2TerminalBlockShading prepared block).union) *
          terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss := by gcongr
    _ = 2 * ((∑ index : Fin good.indexCount,
          (good.windowData index).window.volumeSupply) *
            terminal.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor delta outputLoss) := by
      rw [hvolumeIndexed]
      ring
    _ ≤ 2 * (2 * localCost * ∑ index : Fin good.indexCount,
          volume (good.chain index).exactTrapezoid.shading.union) :=
      mul_le_mul_left' hlocal 2
    _ ≤ 4 * localCost *
        (16 * ∑ index ∈ data.selected,
          volume (good.chain index).exactTrapezoid.shading.union) :=
      by
        calc
          2 * (2 * localCost * ∑ index : Fin good.indexCount,
              volume (good.chain index).exactTrapezoid.shading.union) =
            4 * localCost * ∑ index : Fin good.indexCount,
              volume (good.chain index).exactTrapezoid.shading.union := by ring
          _ ≤ 4 * localCost *
              (16 * ∑ index ∈ data.selected,
                volume (good.chain index).exactTrapezoid.shading.union) :=
            mul_le_mul_left' data.total_volume_le (4 * localCost)
    _ = 64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
        pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
        volume data.shading.union := by
      rw [data.shading_volume_eq_sum]
      dsimp only [localCost]
      ring

/-- Package the selected multi-window exact-rich union as the terminal level. -/
theorem toExactTerminalLevel
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared}
    (data : PureWZ2TerminalExactBlockFamilyData good)
    (hinputOutput : inputLoss ≤ outputLoss)
    (hvolume : Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume data.shading.union) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  have hsub := data.subshading
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
      (good.chain index).exactTrapezoid.trapezoid
  exact ⟨{
    shading := data.shading
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
      exact (good.chain index).exactTrapezoid.height_eq
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      exact (good.chain index).exactTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with ⟨index, _hindex, rfl⟩
      exact (good.chain index).exactTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with
        ⟨first, hfirst, rfl⟩
      rcases Finset.mem_image.mp hother with
        ⟨second, hsecond, rfl⟩
      have hindexNe : first ≠ second := by
        intro heq
        subst second
        exact hne rfl
      exact data.separated_cores hfirst hsecond hindexNe
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨target, htarget, rfl⟩
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (data.mem_shading_union_iff point).mp hpoint.1 with
        ⟨sourceIndex, hsourceIndex, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (good.chain sourceIndex).exactTrapezoid.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore :=
        (good.chain sourceIndex).exactTrapezoid.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (good.chain target).exactTrapezoid.trapezoid =
            (good.chain sourceIndex).exactTrapezoid.trapezoid
      · rw [heq]
        exact (good.chain sourceIndex).exactTrapezoid.slope_approximation
          z hsourceCore hsourceSlice
      · have hindexNe : target ≠ sourceIndex := by
          intro hindex
          subst sourceIndex
          exact heq rfl
        have hsep := data.separated_cores htarget hsourceIndex hindexNe
          z hz z hsourceCore
        exact False.elim ((not_le_of_gt
          (Real.sqrt_pos.mpr source.extremal.delta_pos)) (by simpa using hsep))
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (data.mem_shading_union_iff point).mp hpoint.1 with
        ⟨index, hindex, hlocal⟩
      have hlocalSlice : horizontalSlice
          (good.chain index).exactTrapezoid.shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hlocal, hpoint.2⟩
      exact ⟨(good.chain index).exactTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩,
        (good.chain index).exactTrapezoid.active_height_coverage
          z hlocalSlice⟩ }⟩

end PureWZ2TerminalExactBlockFamilyData

/-- Build every good terminal block through the same exact dependent chain. -/
theorem PureWZ2TerminalLemma23Prepared.buildExactGoodBlockFamily
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss)
    (certificates : PureWZ2TerminalChainCertificates
      eta theoremEta outputLoss terminal)
    (hextra : ∀ {window : PureWZ2TerminalWindow prepared}
      (chain : PureWZ2TerminalWindowChainOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) window),
      (chain.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss))
    (hgood : (pureWZ2GoodTerminalBlocks prepared).Nonempty) :
    Nonempty (PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared) := by
  let good := pureWZ2GoodTerminalBlocks prepared
  let goodEquiv := good.equivFin
  let block : Fin good.card → ℤ := fun index => (goodEquiv.symm index).1
  have hblockMem : ∀ index, block index ∈ good := fun index =>
    (goodEquiv.symm index).2
  have hblockInjective : Function.Injective block := by
    intro first second heq
    apply goodEquiv.symm.injective
    exact Subtype.ext heq
  let windowData : ∀ index : Fin good.card,
      PureWZ2TerminalBlockWindowData prepared (block index) := fun index =>
    Classical.choice (prepared.windowDataOfGoodBlock (hblockMem index))
  have hchain : ∀ index, Nonempty (PureWZ2TerminalWindowChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (windowData index).window) := fun index =>
    pureWZ2_terminal_window_chain_of_certificates
      (windowData index).window hbridge budget certificates
  let chain : ∀ index, PureWZ2TerminalWindowChainOutput
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (windowData index).window := fun index =>
    Classical.choice (hchain index)
  let heightLift : ∀ index, PureWZ2TerminalExactHeightLift
      (chain index).exactTrapezoid := fun index =>
    Classical.choice (chain index).exactTrapezoid.toHeightLift
  exact ⟨{
    indexCount := good.card
    indexCount_pos := Finset.card_pos.mpr hgood
    block := block
    block_injective := hblockInjective
    block_mem := hblockMem
    block_surjective := by
      intro target htarget
      let index := goodEquiv ⟨target, htarget⟩
      refine ⟨index, ?_⟩
      change (goodEquiv.symm index).1 = target
      simp [index]
    windowData := windowData
    chain := chain
    heightLift := heightLift
    extraLoss := extraLoss
    extraCost_power := fun index => hextra (chain index) }⟩

end Kakeya.Assouad

end
