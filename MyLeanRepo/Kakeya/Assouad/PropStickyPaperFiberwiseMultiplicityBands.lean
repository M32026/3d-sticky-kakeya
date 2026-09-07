import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberMultiplicityBand
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancing

/-!
# Independent multiplicity bands in every complete coarse fiber

For each complete parent fiber, choose its own best dyadic point-multiplicity
band.  The resulting global shading uses the chosen local band of the unique
parent of each fine tube.  Every fiber separately retains its logarithmic
share of mass, so no positive-mass fiber is erased at this stage.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFiberwiseMultiplicityBandsData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine) where
  localBand :
    ∀ parent : Fin coarse.card,
      WZ2PaperGlobalMultiplicityBandData
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) shading)
  local_band_mass_pos :
    ∀ parent, 0 < (localBand parent).band.mass
  local_level_lt :
    ∀ parent,
      (localBand parent).level <
        Nat.log 2
          (cover.fullFiberSubfamily parent).family.card + 1
  refined : WZ1PaperTubeShading fine
  refined_carrier_eq :
    ∀ source,
      refined.carrier source =
        shading.carrier source ∩
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading
              (cover.fullFiberSubfamily (cover.parent source))
              shading)
            (localBand (cover.parent source)).level
  refined_subshading :
    ∀ source, refined.carrier source ⊆ shading.carrier source
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  local_carrier_eq :
    ∀ parent index,
      (restrictPaperShading
        (cover.fullFiberSubfamily parent) refined).carrier index =
          (localBand parent).band.carrier index
  local_mass_eq :
    ∀ parent,
      (restrictPaperShading
        (cover.fullFiberSubfamily parent) refined).mass =
          (localBand parent).band.mass
  fiber_mass_retention :
    ∀ parent,
      (restrictPaperShading
          (cover.fullFiberSubfamily parent) shading).mass /
            ((Nat.log 2
                (cover.fullFiberSubfamily parent).family.card +
              1 : ℕ) : ENNReal) ≤
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) refined).mass
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) refined).union →
        (2 ^ (localBand parent).level : ENNReal) ≤
            ((restrictPaperShading
                (cover.fullFiberSubfamily parent) refined
              ).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent) refined
            ).pointMultiplicity point : ENNReal) <
            (2 ^ ((localBand parent).level + 1) : ENNReal)

theorem wz2_paper_fiberwise_multiplicity_bands
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hCubical : WZ1PaperIsCubicalShading shading)
    (hFiberMassPos :
      ∀ parent,
        0 <
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading).mass) :
    Nonempty
      (WZ2PaperFiberwiseMultiplicityBandsData cover shading) := by
  let localBand :
      ∀ parent : Fin coarse.card,
        WZ2PaperGlobalMultiplicityBandData
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading) :=
    fun parent =>
      Classical.choice <|
        wz2_paper_global_multiplicity_band
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading)
          (restrictPaperShading_cubical
            (cover.fullFiberSubfamily parent) hCubical)
  let refined : WZ1PaperTubeShading fine :=
    { carrier := fun source =>
        shading.carrier source ∩
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading
              (cover.fullFiberSubfamily (cover.parent source))
              shading)
            (localBand (cover.parent source)).level
      measurable_carrier := fun source =>
        (shading.measurable_carrier source).inter
          (wz1PaperDyadicMultiplicityBand_measurable
            (restrictPaperShading
              (cover.fullFiberSubfamily (cover.parent source))
              shading)
            (localBand (cover.parent source)).level)
      subset_body := fun source =>
        Set.inter_subset_left.trans (shading.subset_body source) }
  have hLocalBandMassPos :
      ∀ parent, 0 < (localBand parent).band.mass := by
    intro parent
    let denominator : ENNReal :=
      ((Nat.log 2
          (cover.fullFiberSubfamily parent).family.card +
        1 : ℕ) : ENNReal)
    have hDenominatorTop : denominator ≠ ⊤ := by
      dsimp only [denominator]
      simp
    have hQuotientPos :
        0 <
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading).mass /
              denominator :=
      ENNReal.div_pos (hFiberMassPos parent).ne' hDenominatorTop
    exact
      hQuotientPos.trans_le
        (by
          simpa [denominator] using
            (localBand parent).band_mass_retention)
  have hLocalLevel :
      ∀ parent,
        (localBand parent).level <
          Nat.log 2
            (cover.fullFiberSubfamily parent).family.card + 1 := by
    intro parent
    by_contra hlevel
    have hgt :
        Nat.log 2
            (cover.fullFiberSubfamily parent).family.card <
          (localBand parent).level := by
      omega
    have hempty :
        wz1PaperDyadicMultiplicityBand
            (restrictPaperShading
              (cover.fullFiberSubfamily parent) shading)
            (localBand parent).level =
          ∅ :=
      paperDyadicBand_empty_of_level_gt_log hgt
    have hzero :
        (wz1PaperDyadicBandSubshading
          (restrictPaperShading
            (cover.fullFiberSubfamily parent) shading)
          (localBand parent).level).mass = 0 :=
      paperDyadicBandSubshading_mass_zero_of_empty hempty
    have hBandZero : (localBand parent).band.mass = 0 := by
      rw [(localBand parent).band_eq]
      exact hzero
    have hpos := hLocalBandMassPos parent
    rw [hBandZero] at hpos
    exact (lt_irrefl 0) hpos
  have hRefinedCubical :
      WZ1PaperIsCubicalShading refined := by
    intro source point hpoint second hsecond
    have hsame :
        wz1PaperGridIndex delta second =
          wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube _ _ _).mp hsecond
    have hsecondCarrier :
        second ∈ shading.carrier source :=
      (hCubical.carrier_mem_iff_of_same_cell
        source hsame.symm).mp hpoint.1
    let fiberShading :=
      restrictPaperShading
        (cover.fullFiberSubfamily (cover.parent source)) shading
    have hFiberCubical : WZ1PaperIsCubicalShading fiberShading :=
      restrictPaperShading_cubical
        (cover.fullFiberSubfamily (cover.parent source)) hCubical
    have hsecondBand :
        second ∈
          wz1PaperDyadicMultiplicityBand fiberShading
            (localBand (cover.parent source)).level :=
      (hFiberCubical.dyadicBand_mem_iff_of_same_cell
        (localBand (cover.parent source)).level hsame.symm).mp hpoint.2
    exact ⟨hsecondCarrier, hsecondBand⟩
  have hLocalCarrier :
      ∀ parent index,
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) refined).carrier index =
            (localBand parent).band.carrier index := by
    intro parent index
    let source :=
      (cover.fullFiberSubfamily parent).embedding index
    have hParent : cover.parent source = parent := by
      exact
        (cover.mem_fullFiber_iff_parent parent source).mp
          (cover.fullFiberSubfamily_mem parent index)
    rw [(localBand parent).band_eq]
    change
      shading.carrier source ∩
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading
              (cover.fullFiberSubfamily (cover.parent source))
              shading)
            (localBand (cover.parent source)).level =
        shading.carrier source ∩
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading
              (cover.fullFiberSubfamily parent) shading)
            (localBand parent).level
    rw [hParent]
  have hLocalMass :
      ∀ parent,
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) refined).mass =
            (localBand parent).band.mass := by
    intro parent
    change
      (∑ index :
          Fin (cover.fullFiberSubfamily parent).family.card,
        MeasureTheory.volume
          ((restrictPaperShading
            (cover.fullFiberSubfamily parent) refined).carrier index)) =
        ∑ index :
          Fin (cover.fullFiberSubfamily parent).family.card,
        MeasureTheory.volume ((localBand parent).band.carrier index)
    apply Finset.sum_congr rfl
    intro index _
    rw [hLocalCarrier parent index]
  exact
    ⟨{
      localBand := localBand
      local_band_mass_pos := hLocalBandMassPos
      local_level_lt := hLocalLevel
      refined := refined
      refined_carrier_eq := fun _ => rfl
      refined_subshading := fun _ => Set.inter_subset_left
      refined_cubical := hRefinedCubical
      local_carrier_eq := hLocalCarrier
      local_mass_eq := hLocalMass
      fiber_mass_retention := by
        intro parent
        rw [hLocalMass parent]
        exact (localBand parent).band_mass_retention
      fiber_multiplicity_band := by
        intro parent point hpoint
        have hPoint :
            point ∈ (localBand parent).band.union := by
          rcases hpoint with ⟨index, hindex⟩
          exact ⟨index, by
            rw [← hLocalCarrier parent index]
            exact hindex⟩
        have hMultiplicity :
            (restrictPaperShading
                (cover.fullFiberSubfamily parent) refined
              ).pointMultiplicity point =
              (localBand parent).band.pointMultiplicity point := by
          classical
          simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
          congr 1
          apply Finset.filter_congr
          intro index _
          rw [hLocalCarrier parent index]
        rw [hMultiplicity]
        exact (localBand parent).band_multiplicity point hPoint
    }⟩

end Kakeya.Assouad

end
