import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalExactMultiWindow

/-!
# Terminal source blocks with indexed mass

The active-cell terminal block decomposition is lifted back to the original
selected terminal-source family.  Restriction by one common block region
preserves the source multiplicity band, and the source indexed mass splits
exactly over all blocks.  These facts convert the existing good-block volume
retention into good-block indexed-mass retention without any CWA argument.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict the original selected terminal shading by one terminal block
region, without changing its tube family or indices. -/
def terminalSourceBlockShading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) : WZ1PaperTubeShading terminal.sticky.selected.family where
  carrier index := terminalSource.shading.carrier index ∩
    pureWZ2TerminalBlockRegion prepared block
  measurable_carrier index :=
    (terminalSource.shading.measurable_carrier index).inter
      (MeasurableSet.biUnion
        (pureWZ2TerminalBlockCells prepared block).finite_toSet.countable
        (fun cell _ => wz1Lemma23Cell_measurable
          terminalSource.delta_pos cell))
  subset_body index := Set.inter_subset_left.trans
    (terminalSource.shading.subset_body index)

theorem terminalSourceBlockShading_carrier
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) (index : Fin terminal.sticky.selected.family.card) :
    (terminalSourceBlockShading prepared block).carrier index =
      terminalSource.shading.carrier index ∩
        pureWZ2TerminalBlockRegion prepared block :=
  rfl

/-- The original-family block shading and the active-cell block shading have
the same geometric union. -/
theorem terminalSourceBlockShading_union_eq
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) :
    (terminalSourceBlockShading prepared block).union =
      (pureWZ2TerminalBlockShading prepared block).union := by
  ext point
  constructor
  · rintro ⟨index, hsource, hregion⟩
    have hshadowUnion : point ∈ prepared.shadow.union := by
      rw [prepared.shadow_union]
      exact ⟨index, hsource⟩
    rcases hshadowUnion with ⟨shadowIndex, hshadow⟩
    exact ⟨shadowIndex, hshadow, hregion⟩
  · rintro ⟨shadowIndex, hshadow, hregion⟩
    have hsourceUnion : point ∈ terminalSource.shading.union := by
      rw [← prepared.shadow_union]
      exact ⟨shadowIndex, hshadow⟩
    rcases hsourceUnion with ⟨index, hsource⟩
    exact ⟨index, hsource, hregion⟩

/-- Restricting every source tube by the same block region preserves the
pointwise multiplicity band on that block. -/
theorem terminalSourceBlockShading_constant_multiplicity
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (block : ℤ) :
    (terminalSourceBlockShading prepared block).HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
  intro point hpoint
  rcases hpoint with ⟨index, hsource, hregion⟩
  have hpointMultiplicity :
      (terminalSourceBlockShading prepared block).pointMultiplicity point =
        terminalSource.shading.pointMultiplicity point := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    congr 1
    ext target
    simp [terminalSourceBlockShading, hregion]
  rw [hpointMultiplicity]
  exact terminalSource.constant_multiplicity point ⟨index, hsource⟩

/-- The original carrier of each terminal-source tube is partitioned by all
terminal block regions. -/
theorem terminalSourceBlockShading_carrier_partition
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (index : Fin terminal.sticky.selected.family.card) :
    terminalSource.shading.carrier index =
      ⋃ block ∈ pureWZ2TerminalBlocks prepared,
        (terminalSourceBlockShading prepared block).carrier index := by
  ext point
  constructor
  · intro hsource
    have hshadowUnion : point ∈ prepared.shadow.union := by
      rw [prepared.shadow_union]
      exact ⟨index, hsource⟩
    rw [pureWZ2TerminalBlock_union_partition prepared] at hshadowUnion
    rcases Set.mem_iUnion₂.mp hshadowUnion with
      ⟨block, hblock, _shadowIndex, _hshadow, hregion⟩
    exact Set.mem_iUnion₂.mpr ⟨block, hblock, hsource, hregion⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨block, _hblock, hsource, _hregion⟩
    exact hsource

/-- Block carriers are pairwise disjoint tube by tube because the common block
regions are pairwise disjoint. -/
theorem terminalSourceBlockShading_carrier_pairwise_disjoint
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (index : Fin terminal.sticky.selected.family.card) :
    (pureWZ2TerminalBlocks prepared : Set ℤ).PairwiseDisjoint fun block =>
      (terminalSourceBlockShading prepared block).carrier index := by
  intro first hfirst second hsecond hne
  exact (pureWZ2TerminalBlockRegion_pairwise_disjoint prepared
    hfirst hsecond hne).mono Set.inter_subset_right Set.inter_subset_right

/-- The terminal-source indexed mass is exactly the sum of the indexed masses
of all original-family terminal blocks. -/
theorem terminalSourceBlockShading_mass_partition
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    terminalSource.shading.mass =
      ∑ block ∈ pureWZ2TerminalBlocks prepared,
        (terminalSourceBlockShading prepared block).mass := by
  calc
    terminalSource.shading.mass =
        ∑ index : Fin terminal.sticky.selected.family.card,
          volume (terminalSource.shading.carrier index) := rfl
    _ = ∑ index : Fin terminal.sticky.selected.family.card,
          volume (⋃ block ∈ pureWZ2TerminalBlocks prepared,
            (terminalSourceBlockShading prepared block).carrier index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [terminalSourceBlockShading_carrier_partition prepared index]
    _ = ∑ index : Fin terminal.sticky.selected.family.card,
          ∑ block ∈ pureWZ2TerminalBlocks prepared,
            volume ((terminalSourceBlockShading prepared block).carrier index) := by
      apply Finset.sum_congr rfl
      intro index _
      exact MeasureTheory.measure_biUnion_finset
        (terminalSourceBlockShading_carrier_pairwise_disjoint prepared index)
        (fun block _ =>
          (terminalSourceBlockShading prepared block).measurable_carrier index)
    _ = ∑ block ∈ pureWZ2TerminalBlocks prepared,
          ∑ index : Fin terminal.sticky.selected.family.card,
            volume ((terminalSourceBlockShading prepared block).carrier index) := by
      rw [Finset.sum_comm]
    _ = ∑ block ∈ pureWZ2TerminalBlocks prepared,
          (terminalSourceBlockShading prepared block).mass := rfl

/-- The existing good-block half-volume selection retains one quarter of the
terminal source's indexed mass after applying the common multiplicity band on
both the source and every block. -/
theorem terminalSource_mass_le_four_mul_goodBlockMass
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    terminalSource.shading.mass ≤
      4 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
        (terminalSourceBlockShading prepared block).mass := by
  have hsourceUpper :=
    (constant_multiplicity_mass_volume_generic
      terminalSource.constant_multiplicity).2
  have hgoodHalf := pureWZ2GoodTerminalBlocks_half prepared
  have hblockLower : ∀ block : ℤ,
      (terminalSource.multiplicity : ENNReal) *
          volume (pureWZ2TerminalBlockShading prepared block).union ≤
        (terminalSourceBlockShading prepared block).mass := by
    intro block
    rw [← terminalSourceBlockShading_union_eq prepared block]
    exact (constant_multiplicity_mass_volume_generic
      (terminalSourceBlockShading_constant_multiplicity prepared block)).1
  have hgoodMass :
      (∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
          (terminalSource.multiplicity : ENNReal) *
            volume (pureWZ2TerminalBlockShading prepared block).union) ≤
        ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
          (terminalSourceBlockShading prepared block).mass :=
    Finset.sum_le_sum fun block _ => hblockLower block
  calc
    terminalSource.shading.mass ≤
        (2 * terminalSource.multiplicity : ENNReal) *
          volume terminalSource.shading.union := hsourceUpper
    _ = (2 * terminalSource.multiplicity : ENNReal) *
          volume prepared.shadow.union := by rw [prepared.shadow_union]
    _ ≤ (2 * terminalSource.multiplicity : ENNReal) *
          (2 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
            volume (pureWZ2TerminalBlockShading prepared block).union) := by
      exact mul_le_mul_right hgoodHalf _
    _ = 4 * ((terminalSource.multiplicity : ENNReal) *
          ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
            volume (pureWZ2TerminalBlockShading prepared block).union) := by ring
    _ = 4 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
          ((terminalSource.multiplicity : ENNReal) *
            volume (pureWZ2TerminalBlockShading prepared block).union) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
          (terminalSourceBlockShading prepared block).mass := by
      exact mul_le_mul_right hgoodMass 4

/-- Reindex a sum over all good blocks by the exact `good.block` bijection. -/
theorem PureWZ2TerminalExactGoodBlockFamilyData.goodBlockMass_sum_eq
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared) :
    (∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
        (terminalSourceBlockShading prepared block).mass) =
      ∑ index : Fin good.indexCount,
        (terminalSourceBlockShading prepared (good.block index)).mass := by
  symm
  apply Finset.sum_bij (fun index _ => good.block index)
  · intro index _
    exact good.block_mem index
  · intro first _ second _ heq
    exact good.block_injective heq
  · intro block hblock
    rcases good.block_surjective block hblock with ⟨index, rfl⟩
    exact ⟨index, Finset.mem_univ index, rfl⟩
  · intro _ _
    rfl

/-- Generic same-family bridge from a local mass transfer on every good block
and one scalar absorption to the all-good-block lifted-mass lower bound.  The
source-relative conclusion is proved here rather than assumed. -/
theorem PureWZ2TerminalExactGoodBlockFamilyData.heightLift_mass_lower_of_blocks
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (good : PureWZ2TerminalExactGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) prepared)
    (localFactor desiredFactor : ENNReal)
    (hlocal : ∀ index : Fin good.indexCount,
      localFactor *
          (terminalSourceBlockShading prepared (good.block index)).mass ≤
        (good.heightLift index).shading.mass)
    (hscalar : 64 * desiredFactor ≤
      wz2PaperPureRefinementFraction delta logExponent * localFactor) :
    16 * desiredFactor * source.shading.mass ≤
      ∑ index : Fin good.indexCount,
        (good.heightLift index).shading.mass := by
  have hterminalGood : terminalSource.shading.mass ≤
      4 * ∑ index : Fin good.indexCount,
        (terminalSourceBlockShading prepared (good.block index)).mass := by
    calc
      terminalSource.shading.mass ≤
          4 * ∑ block ∈ pureWZ2GoodTerminalBlocks prepared,
            (terminalSourceBlockShading prepared block).mass :=
        terminalSource_mass_le_four_mul_goodBlockMass prepared
      _ = 4 * ∑ index : Fin good.indexCount,
            (terminalSourceBlockShading prepared (good.block index)).mass := by
        rw [good.goodBlockMass_sum_eq]
  have hlocalSum : localFactor *
      (∑ index : Fin good.indexCount,
        (terminalSourceBlockShading prepared (good.block index)).mass) ≤
      ∑ index : Fin good.indexCount,
        (good.heightLift index).shading.mass := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun index _ => hlocal index
  have hretained : wz2PaperPureRefinementFraction delta logExponent *
      source.shading.mass ≤ terminalSource.shading.mass := by
    calc
      wz2PaperPureRefinementFraction delta logExponent *
          source.shading.mass ≤ terminal.sticky.refined.mass :=
        terminal.sticky.retained_mass
      _ = terminalSource.shading.mass := by rw [terminalSource.shading_eq]
  have hscaled : 4 * (16 * desiredFactor * source.shading.mass) ≤
      4 * ∑ index : Fin good.indexCount,
        (good.heightLift index).shading.mass := by
    calc
      4 * (16 * desiredFactor * source.shading.mass) =
          (64 * desiredFactor) * source.shading.mass := by ring
      _ ≤ (wz2PaperPureRefinementFraction delta logExponent * localFactor) *
          source.shading.mass := by gcongr
      _ = localFactor *
          (wz2PaperPureRefinementFraction delta logExponent *
            source.shading.mass) := by ring
      _ ≤ localFactor * terminalSource.shading.mass := by gcongr
      _ ≤ localFactor * (4 * ∑ index : Fin good.indexCount,
          (terminalSourceBlockShading prepared (good.block index)).mass) := by
        gcongr
      _ = 4 * (localFactor * ∑ index : Fin good.indexCount,
          (terminalSourceBlockShading prepared (good.block index)).mass) := by ring
      _ ≤ 4 * ∑ index : Fin good.indexCount,
          (good.heightLift index).shading.mass := by gcongr
  apply (ENNReal.mul_le_mul_iff_right
    (show (4 : ENNReal) ≠ 0 by norm_num)
    (show (4 : ENNReal) ≠ ⊤ by norm_num)).mp
  simpa [mul_comm] using hscaled

end Kakeya.Assouad

end
