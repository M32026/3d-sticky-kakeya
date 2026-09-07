import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.MassPopularSubband
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoverRemoveEmptyStatements

/-!
# A fixed-width popular box inside the mass-popular derivative subband

The fixed width `1/8` leaves explicit room for the common horizontal
translation, the fixed rotation, affine retubing, and target cubical
saturation while losing only a universal fraction of the selected mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Popular source box on the mass-popular hundredth band, with empty source
tubes removed but no mass lost. -/
structure PureWZ2SubbandPopularBoxData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) where
  popular : PureWZ2PaperPopularBoxData subband.shading (1 / 8)
  restricted_mass_pos : 0 < popular.restricted.mass
  localGrains : PureWZ2LocalGrainData popular.restricted sigma
    band.sourceConstant
  sourceShading : WZ1PaperTubeShading
    (wz2PaperNonemptyCarrierSubfamily popular.restricted).family
  source_carrier_eq : ∀ index, sourceShading.carrier index =
    popular.restricted.carrier
      ((wz2PaperNonemptyCarrierSubfamily popular.restricted).embedding index)
  source_carrier_nonempty : ∀ index,
    (sourceShading.carrier index).Nonempty
  source_mass_eq : sourceShading.mass = popular.restricted.mass
  source_mass_lower :
    ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
        (subband.shading.mass) ≤ sourceShading.mass

theorem PureWZ2MassPopularSubbandData.toPopularBox
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    Nonempty (PureWZ2SubbandPopularBoxData subband) := by
  rcases pureWZ2_paper_popular_box subband.shading
      (show (0 : ℝ) < 1 / 8 by norm_num)
      (show (1 / 8 : ℝ) ≤ 1 by norm_num) with ⟨popular⟩
  have hsubbandMass : 0 < subband.shading.mass := by
    have hbandMass : 0 < band.literalBandShading.mass := by
      rw [band.literalBandShading_mass]
      have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
      have hrho : 0 < band.lemma31.data.rho.1 :=
        hdelta.trans_le band.lemma31.data.rho.2.1
      have hpower : 0 < Kakeya.realRpowENN delta
          (band.massLoss + 3) := by
        simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
          Real.rpow_pos_of_pos hdelta]
      have hrhoENN : 0 < ENNReal.ofReal band.lemma31.data.rho.1 :=
        ENNReal.ofReal_pos.mpr hrho
      have hcoefficient : 0 < Kakeya.realRpowENN delta
            (band.massLoss + 3) *
          ENNReal.ofReal band.lemma31.data.rho.1 / 50 := by
        exact ENNReal.div_pos
          (ENNReal.mul_pos hpower.ne' hrhoENN.ne').ne' (by norm_num)
      exact hcoefficient.trans_le band.shaded_mass
    have hhundredth : 0 < band.literalBandShading.mass / 100 :=
      ENNReal.div_pos hbandMass.ne' (by norm_num)
    exact hhundredth.trans_le subband.mass_lower
  have hfactor : 0 < ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) := by
    apply ENNReal.ofReal_pos.mpr
    norm_num
  have hpopularMass : 0 < popular.restricted.mass :=
    (ENNReal.mul_pos hfactor.ne' hsubbandMass.ne').trans_le
      popular.mass_lower
  let sourceShading := wz2PaperNonemptyCarrierShading popular.restricted
  have hcarrier : ∀ index, (sourceShading.carrier index).Nonempty := by
    intro index
    have hmem :
        (wz2PaperNonemptyCarrierSubfamily popular.restricted).embedding index ∈
        wz2PaperNonemptyCarrierIndices popular.restricted :=
      Finset.orderEmbOfFin_mem
        (wz2PaperNonemptyCarrierIndices popular.restricted) rfl index
    exact (Finset.mem_filter.mp hmem).2
  have hmassEq : sourceShading.mass = popular.restricted.mass := by
    dsimp only [sourceShading, wz2PaperNonemptyCarrierShading,
      wz2PaperNonemptyCarrierSubfamily]
    rw [restrictPaperShading_fromFinset_mass]
    change (∑ index ∈ wz2PaperNonemptyCarrierIndices popular.restricted,
        volume (popular.restricted.carrier index)) =
      ∑ index, volume (popular.restricted.carrier index)
    apply Finset.sum_subset (Finset.subset_univ _)
    intro index _ hnot
    have hempty : popular.restricted.carrier index = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonempty⟩)
    simp [hempty]
  exact ⟨{
    popular := popular
    restricted_mass_pos := hpopularMass
    localGrains := subband.localGrains.restrict popular.restricted_subshading
    sourceShading := sourceShading
    source_carrier_eq := fun _ => rfl
    source_carrier_nonempty := hcarrier
    source_mass_eq := hmassEq
    source_mass_lower := by rw [hmassEq]; exact popular.mass_lower
  }⟩

namespace PureWZ2SubbandPopularBoxData

end PureWZ2SubbandPopularBoxData

end Kakeya.Assouad

end
