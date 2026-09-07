import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactMultiWindow

/-!
# Paper-faithful exact terminal multi-window lift

The auxiliary exact-rich graph in each terminal block selects heights only.
This module takes the union of the corresponding restrictions of the original
source shading.  The older exact-rich aggregate remains as a certified subset,
so all established volume estimates transfer, while the final carrier now has
the form used in WZ Corollary 5.6.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2TerminalExactBlockFamilyData

/-- Union of the height-only lifts in the selected separated block class. -/
def liftedShading
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
    (good.heightLift index.1).shading.carrier sourceIndex
  measurable_carrier sourceIndex := MeasurableSet.iUnion fun index =>
    (good.heightLift index.1).shading.measurable_carrier sourceIndex
  subset_body sourceIndex := by
    intro point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨index, hindex⟩
    exact (good.heightLift index.1).shading.subset_body sourceIndex hindex

@[simp] theorem mem_liftedShading_carrier_iff
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
    point ∈ data.liftedShading.carrier sourceIndex ↔
      ∃ index ∈ data.selected,
        point ∈ (good.heightLift index).shading.carrier sourceIndex := by
  simp [liftedShading]

/-- The lifted union is still an indexed subshading of the original source. -/
theorem liftedShading_subshading
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
    PureWZ2PaperIsSubshading data.liftedShading source.shading := by
  intro sourceIndex point hpoint
  rcases (data.mem_liftedShading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, _hindex, hlocal⟩
  exact (good.heightLift index).subshading sourceIndex hlocal

theorem mem_liftedShading_union_iff
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
    point ∈ data.liftedShading.union ↔
      ∃ index ∈ data.selected,
        point ∈ (good.heightLift index).shading.union := by
  constructor
  · rintro ⟨sourceIndex, hpoint⟩
    rcases (data.mem_liftedShading_carrier_iff sourceIndex point).mp hpoint with
      ⟨index, hindex, hlocal⟩
    exact ⟨index, hindex, sourceIndex, hlocal⟩
  · rintro ⟨index, hindex, sourceIndex, hlocal⟩
    exact ⟨sourceIndex,
      (data.mem_liftedShading_carrier_iff sourceIndex point).mpr
        ⟨index, hindex, hlocal⟩⟩

/-- The former auxiliary exact-rich aggregate is contained in the genuine
source-height aggregate. -/
theorem shading_sub_liftedShading
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
    PureWZ2PaperIsSubshading data.shading data.liftedShading := by
  intro sourceIndex point hpoint
  rcases (data.mem_shading_carrier_iff sourceIndex point).mp hpoint with
    ⟨index, hindex, hlocal⟩
  exact (data.mem_liftedShading_carrier_iff sourceIndex point).mpr
    ⟨index, hindex, (good.heightLift index).exact_subshading sourceIndex hlocal⟩

/-- Distinct selected lifts are disjoint because all their active heights lie
in the already-separated terminal cores. -/
theorem lifted_union_pairwise_disjoint
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
      (good.heightLift index).shading.union := by
  intro first hfirst second hsecond hne
  change Disjoint
    (good.heightLift first).shading.union
    (good.heightLift second).shading.union
  rw [Set.disjoint_left]
  intro point hpointFirst hpointSecond
  have hfirstSlice : horizontalSlice
      (good.heightLift first).shading.union (point 2) ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hpointFirst, rfl⟩
  have hsecondSlice : horizontalSlice
      (good.heightLift second).shading.union (point 2) ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨point, hpointSecond, rfl⟩
  have hsep := data.separated_cores hfirst hsecond hne
    (point 2) ((good.heightLift first).active_height_coverage _ hfirstSlice)
    (point 2) ((good.heightLift second).active_height_coverage _ hsecondSlice)
  exact (not_le_of_gt (Real.sqrt_pos.mpr source.extremal.delta_pos))
    (by simpa using hsep)

theorem liftedShading_volume_eq_sum
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
    volume data.liftedShading.union = ∑ index ∈ data.selected,
      volume (good.heightLift index).shading.union := by
  have hunion : data.liftedShading.union =
      ⋃ index : {index // index ∈ data.selected},
        (good.heightLift index.1).shading.union := by
    ext point
    constructor
    · intro hpoint
      rcases (data.mem_liftedShading_union_iff point).mp hpoint with
        ⟨index, hindex, hlocal⟩
      exact Set.mem_iUnion.mpr ⟨⟨index, hindex⟩, hlocal⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨index, hlocal⟩
      exact (data.mem_liftedShading_union_iff point).mpr
        ⟨index.1, index.2, hlocal⟩
  have hdisjoint : Pairwise (Function.onFun Disjoint
      (fun index : {index // index ∈ data.selected} =>
        (good.heightLift index.1).shading.union)) := by
    intro first second hne
    exact data.lifted_union_pairwise_disjoint first.property second.property
      (Subtype.coe_injective.ne hne)
  rw [hunion, MeasureTheory.measure_iUnion hdisjoint]
  · rw [tsum_fintype]
    exact (Finset.sum_subtype data.selected (fun _ => Iff.rfl)
      (fun index : Fin good.indexCount =>
        volume (good.heightLift index).shading.union)).symm
  · intro index
    exact measurableSet_shading_union (good.heightLift index.1).shading

/-- Every aggregate bound already proved for the auxiliary exact-rich carrier
passes to the larger source-height carrier. -/
theorem aggregate_lifted_volume_bound
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
        volume data.liftedShading.union := by
  have hvolumeMono : volume data.shading.union ≤
      volume data.liftedShading.union :=
    MeasureTheory.measure_mono data.shading_sub_liftedShading.union_subset
  calc
    _ ≤ 64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
          volume data.shading.union := data.aggregate_volume_bound
    _ ≤ 64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
          volume data.liftedShading.union := by
      exact mul_le_mul_left' hvolumeMono
        (64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss)

/-- Package the paper-faithful lifted terminal union as the exact final level. -/
theorem toLiftedExactTerminalLevel
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
      volume data.liftedShading.union) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  have hsub := data.liftedShading_subshading
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
    shading := data.liftedShading
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
      rcases Finset.mem_image.mp htrapezoid with ⟨first, hfirst, rfl⟩
      rcases Finset.mem_image.mp hother with ⟨second, hsecond, rfl⟩
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
      rcases (data.mem_liftedShading_union_iff point).mp hpoint.1 with
        ⟨sourceIndex, hsourceIndex, hsourcePoint⟩
      have hsourceSlice : horizontalSlice
          (good.heightLift sourceIndex).shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hsourcePoint, hpoint.2⟩
      have hsourceCore :=
        (good.heightLift sourceIndex).active_height_coverage z hsourceSlice
      by_cases heq :
          (good.chain target).exactTrapezoid.trapezoid =
            (good.chain sourceIndex).exactTrapezoid.trapezoid
      · rw [heq]
        change |source.globalGrains.slope z -
          (good.chain sourceIndex).exactTrapezoid.trapezoid.affine z| ≤ delta
        exact (good.heightLift sourceIndex).slope_approximation z hsourceSlice
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
      rcases (data.mem_liftedShading_union_iff point).mp hpoint.1 with
        ⟨index, hindex, hlocal⟩
      have hlocalSlice : horizontalSlice
          (good.heightLift index).shading.union z ≠ ∅ := by
        apply Set.nonempty_iff_ne_empty.mp
        exact ⟨point, hlocal, hpoint.2⟩
      exact ⟨(good.chain index).exactTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩,
        (good.heightLift index).active_height_coverage z hlocalSlice⟩
  }⟩

/-- The aggregate terminal estimate, followed by one explicit numerical
absorption, gives the exact terminal level used by Corollary 5.6.  Keeping
the absorption premise here separates the geometric construction from the
outer choice of losses and the sufficiently small source scale. -/
theorem toLiftedExactTerminalLevelOfBudget
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
    (hfinalAbsorb :
      64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
          pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        volume prepared.shadow.union * terminal.sticky.balanced.cellMass *
          pureWZ2TerminalExactRichFloor delta outputLoss) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  let cost : ENNReal :=
    64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
      pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss
  have hcostZero : cost ≠ 0 := by
    dsimp only [cost, pureWZ2TerminalExactVolumeCost,
      pureWZ2TerminalExactHeightRetentionCost,
      pureWZ2TerminalExactParentThinning, pureWZ2TerminalExactAnchorCost]
    have hdelta : 0 < delta := source.extremal.delta_pos
    have hthickness : 0 < ENNReal.ofReal
        (Real.sqrt delta + 2 * delta) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    have hdeltaENN : 0 < ENNReal.ofReal delta :=
      ENNReal.ofReal_pos.mpr hdelta
    have hpi : 0 < ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_pos.mpr Real.pi_pos
    have hinv : 0 < 1 / delta := one_div_pos.mpr hdelta
    have hglobal : 0 < Kakeya.realRpowENN (1 / delta) (1 - sigma) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hinv _)
    have hsource : 0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have hparent : 0 < (pureWZ2FixedLineParentFiberBound delta : ENNReal) := by
      simp [pureWZ2FixedLineParentFiberBound, pureWZ2FixedLineParentYBound]
    have hheight : 0 < ENNReal.ofReal
        (2 * Real.rpow delta (-good.extraLoss)) := by
      apply ENNReal.ofReal_pos.mpr
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hdelta _)
    have hcap : 0 < ENNReal.ofReal (3 / Real.sqrt delta) := by
      apply ENNReal.ofReal_pos.mpr
      exact div_pos (by norm_num) (Real.sqrt_pos.mpr hdelta)
    positivity
  have hcostTop : cost ≠ ⊤ := by
    have hvolumeCostTop :
        pureWZ2TerminalExactVolumeCost delta sigma inputLoss ≠ ⊤ := by
      dsimp only [pureWZ2TerminalExactVolumeCost,
        pureWZ2TerminalExactParentThinning, pureWZ2TerminalExactAnchorCost]
      repeat' apply ENNReal.mul_ne_top
      all_goals simp [Kakeya.realRpowENN]
    have hheightCostTop :
        pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss ≠ ⊤ := by
      unfold pureWZ2TerminalExactHeightRetentionCost
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    dsimp only [cost]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hvolumeCostTop) hheightCostTop
  have hscaled : cost *
        Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      cost * volume data.liftedShading.union := by
    calc
      cost * Kakeya.realRpowENN delta (sigma + outputLoss) ≤
          volume prepared.shadow.union *
            terminal.sticky.balanced.cellMass *
              pureWZ2TerminalExactRichFloor delta outputLoss := by
        simpa [cost, mul_comm, mul_left_comm, mul_assoc] using hfinalAbsorb
      _ ≤ cost * volume data.liftedShading.union := by
        simpa [cost, mul_comm, mul_left_comm, mul_assoc] using
          data.aggregate_lifted_volume_bound
  have hvolume : Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume data.liftedShading.union :=
    (ENNReal.mul_le_mul_iff_left hcostZero hcostTop).mp (by
      simpa [mul_comm] using hscaled)
  exact data.toLiftedExactTerminalLevel hinputOutput hvolume

end PureWZ2TerminalExactBlockFamilyData

/-- Run the exact terminal argument on every good `sqrt delta` height block,
select one separated block residue, and return to the original source family
by the height-only lift.  This is the geometric terminal step in the proof of
Corollary 5.6; the caller retains responsibility for the final power budget. -/
theorem PureWZ2TerminalScaleStickyData.toLiftedExactTerminalLevelOfBudgets
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (terminal : PureWZ2TerminalScaleStickyData
      source stickyLoss logExponent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (budget : PureWZ2TerminalChainBudget
      sigma inputLoss delta stickyLoss eta theoremEta outputLoss)
    (certificates : PureWZ2TerminalChainCertificates
      eta theoremEta outputLoss terminal)
    (hextra : ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      (chain : PureWZ2TerminalWindowChainOutput
        (eta := eta) (theoremEta := theoremEta)
        (outputLoss := outputLoss) window),
      (chain.preparedGraph.graph.residue.extraCost : ℝ) ≤
        Real.rpow delta (-extraLoss))
    (hinputOutput : inputLoss ≤ outputLoss)
    (hfinalAbsorb :
      ∀ {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
        {good : PureWZ2TerminalExactGoodBlockFamilyData
          (eta := eta) (theoremEta := theoremEta)
          (outputLoss := outputLoss) prepared}
        (data : PureWZ2TerminalExactBlockFamilyData good),
        64 * pureWZ2TerminalExactVolumeCost delta sigma inputLoss *
            pureWZ2TerminalExactHeightRetentionCost delta good.extraLoss *
            Kakeya.realRpowENN delta (sigma + outputLoss) ≤
          volume prepared.shadow.union * terminal.sticky.balanced.cellMass *
            pureWZ2TerminalExactRichFloor delta outputLoss) :
    Nonempty (PureWZ2ExactTerminalLevelData source outputLoss) := by
  rcases terminal.prepareSource with ⟨terminalSource⟩
  rcases terminalSource.toLemma23Prepared hbridge with ⟨prepared⟩
  have hgood := pureWZ2GoodTerminalBlocks_nonempty prepared
  rcases prepared.buildExactGoodBlockFamily hbridge budget certificates
      hextra hgood with ⟨good⟩
  rcases good.selectResidue with ⟨data⟩
  exact data.toLiftedExactTerminalLevelOfBudget hinputOutput
    (hfinalAbsorb prepared data)

end Kakeya.Assouad

end
