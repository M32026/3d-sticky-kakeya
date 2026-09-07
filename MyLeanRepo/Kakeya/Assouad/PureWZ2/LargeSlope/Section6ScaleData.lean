import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Stable Section-6 slab input

This is the pure internal output of the Proposition-5/Lemma-32 selection.
It records one whole-cell shading, on the same family as the C2 grains, for
which the mass and spatial-cover hypotheses of Lemma 31 hold simultaneously.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2Section6ScaleData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading family)
    (sigma loss : ℝ)
    (scale : WZ2PaperRequestedScale delta) where
  slabLeft : ℝ
  slabRight : ℝ
  slabLeft_mem : -1 ≤ slabLeft
  slab_ordered : slabLeft < slabRight
  slabRight_mem : slabRight ≤ 1
  slab_width : slabRight - slabLeft = scale.1
  slabShading : WZ1PaperTubeShading family
  slab_subshading : ∀ index,
    slabShading.carrier index ⊆ sourceShading.carrier index
  slab_cubical : WZ1PaperIsCubicalShading slabShading
  slab_in_slab : ∀ index, slabShading.carrier index ⊆
    horizontalSlab slabLeft slabRight
  slab_mass :
    ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (loss + 2) *
        family.enncard * ENNReal.ofReal scale.1 ≤
      slabShading.mass
  slab_cover :
    CanCoverByBalls slabShading.union scale.1
      (Kakeya.realRpowENN delta (-loss) *
        Kakeya.realRpowENN scale.1 (-2 + sigma))
  /-- Proposition 5's sharp fine multiplicity cap, weakened only to the
  declared slab loss. -/
  slab_pointMultiplicity_upper : ∀ point,
    (slabShading.pointMultiplicity point : ENNReal) ≤
      Kakeya.realRpowENN (delta / scale.1)
          (2 - sigma - loss) * family.enncard

/-- Re-anchor slab data on a smaller source shading when the selected slab
already lies in it.  All quantitative fields are unchanged. -/
def PureWZ2Section6ScaleData.restrictSource
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading smaller : WZ1PaperTubeShading family}
    {scale : WZ2PaperRequestedScale delta}
    (data : PureWZ2Section6ScaleData sourceShading sigma loss scale)
    (hsub : ∀ index, data.slabShading.carrier index ⊆
      smaller.carrier index) :
    PureWZ2Section6ScaleData smaller sigma loss scale :=
  { slabLeft := data.slabLeft
    slabRight := data.slabRight
    slabLeft_mem := data.slabLeft_mem
    slab_ordered := data.slab_ordered
    slabRight_mem := data.slabRight_mem
    slab_width := data.slab_width
    slabShading := data.slabShading
    slab_subshading := hsub
    slab_cubical := data.slab_cubical
    slab_in_slab := data.slab_in_slab
    slab_mass := data.slab_mass
    slab_cover := data.slab_cover
    slab_pointMultiplicity_upper := data.slab_pointMultiplicity_upper }

theorem PureWZ2Section6ScaleData.pointMultiplicity_le_source
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {scale : WZ2PaperRequestedScale delta}
    (data : PureWZ2Section6ScaleData sourceShading sigma loss scale)
    (point : Point3) :
    data.slabShading.pointMultiplicity point ≤
      sourceShading.pointMultiplicity point := by
  apply Finset.card_le_card
  intro index hindex
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, data.slab_subshading index
      (Finset.mem_filter.mp hindex).2⟩

end Kakeya.Assouad

end
