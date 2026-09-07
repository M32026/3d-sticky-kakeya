import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularBoxOccupiedAnchor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6CommonYDerivativeBand

/-!
# A mass-popular hundredth of the Lemma-32 derivative band

Centering an arbitrary occupied height can send the opposite end of the
selected derivative band outside the target paper window.  Following
Proposition 6.5 literally, we split the band into one hundred equal pieces,
retain a piece with at least one hundredth of the shaded mass, and use its
midpoint as the common height anchor.  The derivative bracket and tight upper
bound are inherited from the original band.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- One mass-popular hundredth band and its literal source restriction. -/
structure PureWZ2MassPopularSubbandData
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) where
  left : ℝ
  right : ℝ
  left_mem : band.left ≤ left
  ordered : left < right
  right_mem : right ≤ band.right
  length_eq : right - left = (band.right - band.left) / 100
  anchor : ℝ
  anchor_eq : anchor = (left + right) / 2
  anchor_mem : anchor ∈ Set.Icc band.left band.right
  shading : WZ1PaperTubeShading
    band.lemma31.data.cfg.family
  carrier_eq : ∀ index, shading.carrier index =
    band.sourceShading.carrier index ∩ horizontalSlab left right
  mass_eq : shading.mass =
    shadedMassInSlab band.sourceShading left right
  mass_lower : band.literalBandShading.mass / 100 ≤ shading.mass
  localGrains : PureWZ2LocalGrainData shading sigma band.sourceConstant

/-- If the derivative band was selected from the paper's whole-label
common-y refinement `F2`, then its mass-popular hundredth retains a companion
on the very same common slice and in the same global-grain label.  The
companion stays in `J₀` because it is chosen at exactly the source point's
height. -/
theorem PureWZ2MassPopularSubbandData.exists_common_slice_companion
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (popular : PureWZ2WeightedPopularGlobalGrainData
      band.lemma31.data.cfg band.lemma31.data.rho
        band.lemma31.data.scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYCore
      band.lemma31.data.cfg band.lemma31.data.rho
        band.lemma31.data.scaleData popular frameSlope)
    (hsourceUnion : band.sourceShading.union = common.F2.union)
    {point : Point3} (hpoint : point ∈ subband.shading.union) :
    ∃ label, label ∈ common.selectedLabels ∧
      point ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
      ∃ companion, companion ∈ subband.shading.union ∧
        companion ∈ pureWZ2WeightedCroppedLabelRegion popular label ∧
        pureWZ2HorizontalRotation frameSlope companion 1 = common.y0 ∧
        companion 2 = point 2 := by
  rcases hpoint with ⟨index, hpointCarrier⟩
  rw [subband.carrier_eq] at hpointCarrier
  have hpointF2 : point ∈ common.F2.union := by
    rw [← hsourceUnion]
    exact ⟨index, hpointCarrier.1⟩
  rcases common.exists_common_slice_companion_same_height hpointF2 with
    ⟨label, hlabel, hpointRegion, companion, hcompanionRegion,
      hcompanionY, hsameHeight⟩
  have hcompanionF2 : companion ∈ common.F2.union := by
    rw [common.F2_union_eq, common.selectedCells_eq]
    rw [pureWZ2WeightedCroppedLabelRegion_eq] at hcompanionRegion
    rcases Set.mem_iUnion₂.mp hcompanionRegion with
      ⟨cell, hcellFiber, hcompanionCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, Finset.mem_biUnion.mpr ⟨label, hlabel, hcellFiber⟩,
        hcompanionCell⟩
  have hcompanionHeight : companion ∈ horizontalSlab subband.left subband.right := by
    have hpointHeight : point ∈ horizontalSlab subband.left subband.right :=
      hpointCarrier.2
    change companion 2 ∈ Set.Icc subband.left subband.right
    change point 2 ∈ Set.Icc subband.left subband.right at hpointHeight
    constructor
    · rw [hsameHeight]
      exact hpointHeight.1
    · rw [hsameHeight]
      exact hpointHeight.2
  have hcompanionSubband : companion ∈ subband.shading.union := by
    rw [← hsourceUnion] at hcompanionF2
    rcases hcompanionF2 with ⟨companionIndex, hcompanionCarrier⟩
    refine ⟨companionIndex, ?_⟩
    rw [subband.carrier_eq]
    exact ⟨hcompanionCarrier, hcompanionHeight⟩
  exact ⟨label, hlabel, hpointRegion, companion, hcompanionSubband,
    hcompanionRegion, hcompanionY, hsameHeight⟩

/-- Select one of one hundred equal bands carrying at least one hundredth of
the total selected-band mass. -/
theorem PureWZ2Lemma32DerivativeBandAssembly.massPopularSubband
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    Nonempty (PureWZ2MassPopularSubbandData band) := by
  let length : ℝ := band.right - band.left
  have hlength : 0 < length := by
    dsimp only [length]
    linarith [band.ordered]
  let subLeft (index : Fin 100) : ℝ :=
    band.left + (index : ℝ) * length / 100
  let subRight (index : Fin 100) : ℝ :=
    band.left + ((index : ℝ) + 1) * length / 100
  have hcover : horizontalSlab band.left band.right ⊆
      ⋃ index : Fin 100, horizontalSlab (subLeft index) (subRight index) := by
    intro point hpoint
    let coordinate : ℝ := (point 2 - band.left) / (length / 100)
    have hcoordinateZero : 0 ≤ coordinate := by
      dsimp only [coordinate]
      exact div_nonneg (by linarith [hpoint.1]) (by positivity)
    have hcoordinateHundred : coordinate ≤ 100 := by
      dsimp only [coordinate]
      apply (div_le_iff₀ (by positivity : 0 < length / 100)).2
      dsimp only [length]
      linarith [hpoint.2]
    have hindex : ∃ index : ℕ, index < 100 ∧
        (index : ℝ) ≤ coordinate ∧ coordinate ≤ (index : ℝ) + 1 := by
      by_cases htop : coordinate < 100
      · have hfloor : 0 ≤ ⌊coordinate⌋ :=
          Int.floor_nonneg.mpr hcoordinateZero
        let index : ℕ := ⌊coordinate⌋.toNat
        have hindexFloor : (index : ℤ) = ⌊coordinate⌋ := by
          simp [index, Int.toNat_of_nonneg hfloor]
        have hindexLt : index < 100 := by
          have : (index : ℤ) < 100 := by
            rw [hindexFloor]
            exact_mod_cast (Int.floor_le coordinate).trans_lt htop
          exact_mod_cast this
        have hindexLe : (index : ℝ) ≤ coordinate := by
          rw [show (index : ℝ) = (⌊coordinate⌋ : ℝ) by
            exact_mod_cast hindexFloor]
          exact Int.floor_le coordinate
        have hcoordinateLt : coordinate < (index : ℝ) + 1 := by
          rw [show (index : ℝ) = (⌊coordinate⌋ : ℝ) by
            exact_mod_cast hindexFloor]
          exact Int.lt_floor_add_one coordinate
        exact ⟨index, hindexLt, hindexLe, hcoordinateLt.le⟩
      · have htopEq : coordinate = 100 := by linarith
        exact ⟨99, by norm_num, by rw [htopEq]; norm_num, by rw [htopEq]; norm_num⟩
    rcases hindex with ⟨index, hindexLt, hindexLe, hcoordinateLe⟩
    let finiteIndex : Fin 100 := ⟨index, hindexLt⟩
    apply Set.mem_iUnion.mpr
    refine ⟨finiteIndex, ?_⟩
    have hpositive : 0 < length / 100 := by positivity
    have hleft : subLeft finiteIndex ≤ point 2 := by
      dsimp only [subLeft, finiteIndex]
      have := mul_le_mul_of_nonneg_right hindexLe hpositive.le
      dsimp only [coordinate] at this
      field_simp [hlength.ne'] at this
      linarith
    have hright : point 2 ≤ subRight finiteIndex := by
      dsimp only [subRight, finiteIndex]
      have := mul_le_mul_of_nonneg_right hcoordinateLe hpositive.le
      dsimp only [coordinate] at this
      field_simp [hlength.ne'] at this
      linarith
    exact ⟨hleft, hright⟩
  have hmassSum : shadedMassInSlab band.sourceShading
        band.left band.right ≤
      ∑ index : Fin 100, shadedMassInSlab band.sourceShading
        (subLeft index) (subRight index) := by
    simp only [shadedMassInSlab]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro source _
    have hsubset : band.sourceShading.carrier source ∩
          horizontalSlab band.left band.right ⊆
        ⋃ index : Fin 100, band.sourceShading.carrier source ∩
          horizontalSlab (subLeft index) (subRight index) := by
      intro point hpoint
      rcases Set.mem_iUnion.mp (hcover hpoint.2) with ⟨index, hindex⟩
      exact Set.mem_iUnion.mpr ⟨index, hpoint.1, hindex⟩
    calc
      volume (band.sourceShading.carrier source ∩
          horizontalSlab band.left band.right) ≤
        volume (⋃ index : Fin 100, band.sourceShading.carrier source ∩
          horizontalSlab (subLeft index) (subRight index)) :=
            measure_mono hsubset
      _ ≤ ∑ index : Fin 100, volume
          (band.sourceShading.carrier source ∩
            horizontalSlab (subLeft index) (subRight index)) :=
        measure_iUnion_fintype_le volume _
  let mass (index : Fin 100) : ENNReal :=
    shadedMassInSlab band.sourceShading (subLeft index) (subRight index)
  obtain ⟨selected, _hselected, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 100)) mass (by simp)
  have hsumLe : (∑ index : Fin 100, mass index) ≤ 100 * mass selected := by
    calc
      (∑ index : Fin 100, mass index) ≤ ∑ _index : Fin 100, mass selected := by
        apply Finset.sum_le_sum
        intro index _
        exact hmax index (Finset.mem_univ index)
      _ = 100 * mass selected := by simp [Finset.sum_const]
  have hmassSelected : band.literalBandShading.mass / 100 ≤ mass selected := by
    rw [band.literalBandShading_mass]
    apply (ENNReal.div_le_iff' (by norm_num) (by norm_num)).2
    exact hmassSum.trans <| by simpa [mass] using hsumLe
  let left := subLeft selected
  let right := subRight selected
  have hleft : band.left ≤ left := by
    dsimp only [left, subLeft]
    have hindex : 0 ≤ (selected : ℝ) := Nat.cast_nonneg selected
    have hlengthNonnegative : 0 ≤ length := hlength.le
    nlinarith
  have hright : right ≤ band.right := by
    dsimp only [right, subRight, length]
    have hindex : (selected : ℝ) + 1 ≤ 100 := by
      exact_mod_cast (show selected.val + 1 ≤ 100 by omega)
    have hnonnegative : 0 ≤ band.right - band.left := sub_nonneg.mpr band.ordered.le
    nlinarith
  have hordered : left < right := by
    have hdifference : right - left = length / 100 := by
      dsimp only [left, right, subLeft, subRight]
      ring
    linarith [div_pos hlength (by norm_num : (0 : ℝ) < 100)]
  have hlengthEq : right - left = (band.right - band.left) / 100 := by
    dsimp only [left, right, subLeft, subRight, length]
    ring
  let anchor := (left + right) / 2
  have hanchor : anchor ∈ Set.Icc band.left band.right := by
    dsimp only [anchor]
    constructor <;> linarith
  let shading := pureWZ2PaperRestrictToSet band.sourceShading
    (horizontalSlab left right) (measurableSet_horizontalSlab left right)
  have hsub : ∀ index, shading.carrier index ⊆
      band.lemma31.data.cfg.shading.carrier index := by
    intro index
    exact Set.inter_subset_left.trans
      (band.source_subshading index)
  let localGrains :=
    band.lemma31.data.cfg.localGrains.restrict hsub
  exact ⟨{
    left := left
    right := right
    left_mem := hleft
    ordered := hordered
    right_mem := hright
    length_eq := hlengthEq
    anchor := anchor
    anchor_eq := rfl
    anchor_mem := hanchor
    shading := shading
    carrier_eq := fun _ => rfl
    mass_eq := rfl
    mass_lower := by
      change band.literalBandShading.mass / 100 ≤
        shadedMassInSlab band.sourceShading left right
      simpa [mass, left, right] using hmassSelected
    localGrains := localGrains
  }⟩

end Kakeya.Assouad

end
