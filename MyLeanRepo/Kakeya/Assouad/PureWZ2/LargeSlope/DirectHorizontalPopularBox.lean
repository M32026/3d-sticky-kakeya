import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoverRemoveEmptyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization

/-!
# Popular spatial box for the direct horizontal Node-6 route

After the mass-popular height interval has been selected, Proposition 6.5
localizes its literal slab shading to one fixed-width spatial box.  Empty
source tubes are then removed without changing mass.  This module keeps the
resulting family, shading, and both grain structures synchronized.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The direct interval-local source after spatial localization and removal
of empty tubes.  No cubicality is asserted at the source scale; target
cubicalization occurs only after the full affine map. -/
structure PureWZ2DirectHorizontalPopularBoxData
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) where
  popular : PureWZ2PaperPopularBoxData source.sourceShading (1 / 8)
  restricted_mass_pos : 0 < popular.restricted.mass
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
        source.sourceShading.mass ≤ sourceShading.mass
  source_mass_card :
    ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
        (ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (inputLoss + 2) *
          cfg.family.enncard * ENNReal.ofReal (source.d - source.c)) ≤
      sourceShading.mass
  source_subshading : ∀ index, sourceShading.carrier index ⊆
    source.sourceShading.carrier
      ((wz2PaperNonemptyCarrierSubfamily popular.restricted).embedding index)
  sourceGlobalGrains : PureWZ2C2GlobalGrainData sourceShading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  /-- Every later restriction retains the same ambient slope selected by the
  actual Node-5 configuration. -/
  source_global_slope_eq : sourceGlobalGrains.slope =
    cfg.globalGrains.slope
  sourceLocalGrains : PureWZ2LocalGrainData sourceShading sigma
    (Kakeya.realRpowENN delta (-inputLoss))

/-- Select the paper's fixed-width spatial box on the already selected
height interval, remove empty tubes, and restrict both grain structures to
the resulting literal source shading. -/
theorem PureWZ2HorizontalSourceData.toDirectPopularBox
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    Nonempty (PureWZ2DirectHorizontalPopularBoxData source) := by
  have hsourceMass : 0 < source.sourceShading.mass := by
    have hdeltaPower :
        0 < Kakeya.realRpowENN delta (inputLoss + 3) := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
        Real.rpow_pos_of_pos cfg.extremal.delta_pos]
    have hwidth : 0 < source.d - source.c := sub_pos.mpr source.ordered
    have hwidthENN : 0 < ENNReal.ofReal (source.d - source.c) :=
      ENNReal.ofReal_pos.mpr hwidth
    have hcoefficient :
        0 < Kakeya.realRpowENN delta (inputLoss + 3) *
          ENNReal.ofReal (source.d - source.c) :=
      ENNReal.mul_pos hdeltaPower.ne' hwidthENN.ne'
    exact hcoefficient.trans_le source.source_mass_lower
  rcases pureWZ2_paper_popular_box source.sourceShading
      (show (0 : ℝ) < 1 / 8 by norm_num)
      (show (1 / 8 : ℝ) ≤ 1 by norm_num) with
    ⟨popular⟩
  have hfactor : 0 < ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) := by
    apply ENNReal.ofReal_pos.mpr
    norm_num
  have hpopularMass : 0 < popular.restricted.mass :=
    (ENNReal.mul_pos hfactor.ne' hsourceMass.ne').trans_le
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
  have hsub : ∀ index, sourceShading.carrier index ⊆
      source.sourceShading.carrier
        ((wz2PaperNonemptyCarrierSubfamily popular.restricted).embedding
          index) := by
    intro index
    change popular.restricted.carrier
        ((wz2PaperNonemptyCarrierSubfamily popular.restricted).embedding
          index) ⊆ _
    exact popular.restricted_subshading _
  exact ⟨{
    popular := popular
    restricted_mass_pos := hpopularMass
    sourceShading := sourceShading
    source_carrier_eq := fun _ => rfl
    source_carrier_nonempty := hcarrier
    source_mass_eq := hmassEq
    source_mass_lower := by
      rw [hmassEq]
      exact popular.mass_lower
    source_mass_card := by
      rw [hmassEq]
      exact (mul_le_mul_left' source.source_mass_card
        (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27))).trans
          popular.mass_lower
    source_subshading := hsub
    sourceGlobalGrains :=
      (source.sourceGlobalGrains.restrict_same_constant
        popular.restricted_subshading)
        |>.subfamily (wz2PaperNonemptyCarrierSubfamily popular.restricted)
    source_global_slope_eq := source.source_global_slope_eq
    sourceLocalGrains :=
      (source.sourceLocalGrains.restrict popular.restricted_subshading)
        |>.subfamily (wz2PaperNonemptyCarrierSubfamily popular.restricted)
  }⟩

namespace PureWZ2DirectHorizontalPopularBoxData

/-- The source family after removing empty carriers. -/
abbrev family
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :=
  (wz2PaperNonemptyCarrierSubfamily data.popular.restricted).family

theorem nonempty
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :
    data.family.Nonempty := by
  change 0 < data.family.card
  by_contra hnot
  have hzero : data.family.card = 0 := Nat.eq_zero_of_not_pos hnot
  have hmassZero : data.sourceShading.mass = 0 := by
    rw [Kakeya.Streamlined.Shading.mass]
    apply Finset.sum_eq_zero
    intro index _
    have indexLt : index.val < data.family.card := index.isLt
    rw [hzero] at indexLt
    omega
  have hpositive : 0 < data.sourceShading.mass := by
    rw [data.source_mass_eq]
    exact data.restricted_mass_pos
  rw [hmassZero] at hpositive
  exact (lt_irrefl 0 hpositive)

theorem line_class
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (data : PureWZ2DirectHorizontalPopularBoxData source) :
    WZ1PaperIsLineClass data.family := by
  intro index
  exact cfg.line_class
    ((wz2PaperNonemptyCarrierSubfamily data.popular.restricted).embedding index)

end PureWZ2DirectHorizontalPopularBoxData

end Kakeya.Assouad

end
