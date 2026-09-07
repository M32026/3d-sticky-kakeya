import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularBoxLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma32DerivativeBand

/-!
# A genuinely occupied affine center in the Lemma-32 band

Paper Lemma 8 is applied to `Y ∩ Q`, before target cubical saturation.  This
module therefore keeps the literal slab and box intersections.  Their positive
mass supplies an actual shaded point; its third coordinate is the height anchor
used by the fixed rotation and diagonal map.  No center of an auxiliary grid
cell is substituted for that occupied height.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The source local-grain constant before the final loss absorption. -/
abbrev PureWZ2Lemma32DerivativeBandAssembly.sourceConstant
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :=
  Kakeya.realRpowENN delta (-band.lemma31.data.targetLoss)

/-- Literal restriction of the source shading to the selected derivative
band.  This need not be cubical; cubicalization is performed after applying
the common affine map, exactly as in paper Lemma 8. -/
def PureWZ2Lemma32DerivativeBandAssembly.literalBandShading
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    WZ1PaperTubeShading band.lemma31.data.cfg.family :=
  pureWZ2PaperRestrictToSet band.sourceShading
    (horizontalSlab band.left band.right)
    (measurableSet_horizontalSlab band.left band.right)

@[simp] theorem PureWZ2Lemma32DerivativeBandAssembly.literalBandShading_mass
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    band.literalBandShading.mass =
      shadedMassInSlab band.sourceShading band.left band.right := rfl

/-- Positive paper-shading mass gives an actual point of its union. -/
theorem pureWZ2PaperShading_union_nonempty_of_mass_pos
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hmass : 0 < shading.mass) :
    shading.union.Nonempty := by
  by_contra hempty
  have hunion : shading.union = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
  have hcarrier : ∀ index, shading.carrier index = ∅ := by
    intro index
    ext point
    constructor
    · intro hpoint
      have : point ∈ shading.union := ⟨index, hpoint⟩
      rw [hunion] at this
      exact this
    · simp
  have hmassZero : shading.mass = 0 := by
    change (∑ index, volume (shading.carrier index)) = 0
    simp [hcarrier]
  rw [hmassZero] at hmass
  exact (lt_irrefl 0 hmass)

/-- A mass-popular literal box together with an actual shaded affine center. -/
structure PureWZ2PopularBoxOccupiedAnchorData
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (width : ℝ) where
  popular : PureWZ2PaperPopularBoxData band.literalBandShading width
  localGrains : PureWZ2LocalGrainData popular.restricted sigma
    band.sourceConstant
  restricted_mass_pos : 0 < popular.restricted.mass
  occupied : Point3
  occupied_mem : occupied ∈ popular.restricted.union
  anchor_mem : occupied 2 ∈ Set.Icc band.left band.right

/-- Select the literal Lemma-8 box and an occupied height in the derivative
band. -/
theorem PureWZ2Lemma32DerivativeBandAssembly.popularBoxOccupiedAnchor
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2PopularBoxOccupiedAnchorData band width) := by
  have hsourceMass : 0 < band.literalBandShading.mass := by
    rw [band.literalBandShading_mass]
    have hdelta : 0 < delta :=
      band.lemma31.data.cfg.extremal.delta_pos
    have hrho : 0 < band.lemma31.data.rho.1 :=
      hdelta.trans_le band.lemma31.data.rho.2.1
    have hpower :
        0 < Kakeya.realRpowENN delta
          (band.massLoss + 3) := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
        Real.rpow_pos_of_pos hdelta]
    have hrhoENN : 0 < ENNReal.ofReal band.lemma31.data.rho.1 :=
      ENNReal.ofReal_pos.mpr hrho
    have hcoefficient :
        0 < Kakeya.realRpowENN delta
              (band.massLoss + 3) *
            ENNReal.ofReal band.lemma31.data.rho.1 / 50 := by
      have hproduct :
          0 < Kakeya.realRpowENN delta
              (band.massLoss + 3) *
            ENNReal.ofReal band.lemma31.data.rho.1 :=
        ENNReal.mul_pos hpower.ne' hrhoENN.ne'
      exact ENNReal.div_pos hproduct.ne' (by norm_num)
    exact hcoefficient.trans_le band.shaded_mass
  rcases pureWZ2_paper_popular_box band.literalBandShading
      hwidth hwidthOne with ⟨popular⟩
  have hfactor : 0 < ENNReal.ofReal (width ^ 3 / 27) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hrestrictedMass : 0 < popular.restricted.mass := by
    exact (ENNReal.mul_pos hfactor.ne' hsourceMass.ne').trans_le
      popular.mass_lower
  have hunion :=
    pureWZ2PaperShading_union_nonempty_of_mass_pos hrestrictedMass
  let occupied : Point3 := Classical.choose hunion
  have hoccupied : occupied ∈ popular.restricted.union :=
    Classical.choose_spec hunion
  have hband : occupied 2 ∈ Set.Icc band.left band.right := by
    rw [popular.restricted_union] at hoccupied
    have hliteral := hoccupied.1
    rcases hliteral with ⟨index, _hsource, hslab⟩
    exact hslab
  have hsub : ∀ index, popular.restricted.carrier index ⊆
      band.lemma31.data.cfg.shading.carrier index := by
    intro index
    exact (popular.restricted_subshading index).trans <|
      Set.inter_subset_left.trans (band.source_subshading index)
  let localGrains :=
    band.lemma31.data.cfg.localGrains.restrict hsub
  exact ⟨{
    popular := popular
    localGrains := localGrains
    restricted_mass_pos := hrestrictedMass
    occupied := occupied
    occupied_mem := hoccupied
    anchor_mem := hband
  }⟩

end Kakeya.Assouad

end
