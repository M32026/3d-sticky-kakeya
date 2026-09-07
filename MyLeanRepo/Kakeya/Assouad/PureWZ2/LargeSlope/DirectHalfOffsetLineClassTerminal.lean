import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationRetubing

/-!
# Direct half-offset line-class terminal geometry

This module applies the generic line-class normalization directly to the
exact shading produced by the half-offset anisotropic retubing.  The final
normalization is fixed at `lambda = 60600`; its source localization therefore
uses width `1 / (100 * lambda)`.  The target radius and crop remain explicit
geometric inputs.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

/-- The terminal line-class stretch is the same fixed stretch used by the
projective-normal transport. -/
def pureWZ2DirectHalfOffsetTerminalLambda : ℝ :=
  pureWZ2FixedProjectiveNormalLambda

theorem pureWZ2DirectHalfOffsetTerminalLambda_eq :
    pureWZ2DirectHalfOffsetTerminalLambda = 60600 := by
  rfl

theorem pureWZ2DirectHalfOffsetTerminalLambda_pos :
    0 < pureWZ2DirectHalfOffsetTerminalLambda := by
  norm_num [pureWZ2DirectHalfOffsetTerminalLambda,
    pureWZ2FixedProjectiveNormalLambda]

theorem pureWZ2DirectHalfOffsetTerminalLambda_one_le :
    1 ≤ pureWZ2DirectHalfOffsetTerminalLambda := by
  simpa [pureWZ2DirectHalfOffsetTerminalLambda] using
    pureWZ2FixedProjectiveNormalLambda_one_le

/-- The reciprocal `(x,z)` localization width paid before the fixed terminal
stretch. -/
def pureWZ2DirectHalfOffsetTerminalWidth : ℝ :=
  1 / (100 * pureWZ2DirectHalfOffsetTerminalLambda)

theorem pureWZ2DirectHalfOffsetTerminalWidth_pos :
    0 < pureWZ2DirectHalfOffsetTerminalWidth := by
  unfold pureWZ2DirectHalfOffsetTerminalWidth
  positivity [pureWZ2DirectHalfOffsetTerminalLambda_pos]

theorem pureWZ2DirectHalfOffsetTerminalWidth_le_one :
    pureWZ2DirectHalfOffsetTerminalWidth ≤ 1 := by
  norm_num [pureWZ2DirectHalfOffsetTerminalWidth,
    pureWZ2DirectHalfOffsetTerminalLambda,
    pureWZ2FixedProjectiveNormalLambda]

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

/-- The exact family underlying the first, half-offset anisotropic retubing.
This name keeps the source of the terminal normalization visible without
introducing any second copy of the family. -/
abbrev halfOffsetLineClassTerminalSourceFamily
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly) :
    Kakeya.Streamlined.TubeFamily
      (anisotropicPaperAlignedScale delta
        commonSource.halfOffsetAssembly.horizontalSource.c
        commonSource.halfOffsetAssembly.horizontalSource.d) :=
  anisotropicPaperTargetFamily retubing.popular.family
    (pureWZ2DirectGeometrySlope
      commonSource.halfOffsetAssembly.horizontalSource)
    commonSource.halfOffsetAssembly.horizontalSource.c
    commonSource.halfOffsetAssembly.horizontalSource.d
    commonSource.halfOffsetAssembly.horizontalSource.m
    (pureWZ2DirectAnisotropicCenter retubing.popular)
    (anisotropicPaperAlignedScale delta
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d)
    commonSource.halfOffsetAssembly.horizontalSource.ordered
    commonSource.halfOffsetAssembly.horizontalSource.slopeScale_pos

/-- Select the literal two-coordinate source box for the fixed terminal
stretch. -/
theorem toHalfOffsetLineClassTerminalPopularBox
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly) :
    Nonempty (PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :=
  pureWZ2_lineClass_popular_box retubing.raw.exactShading
    pureWZ2DirectHalfOffsetTerminalWidth_pos
    pureWZ2DirectHalfOffsetTerminalWidth_le_one

/-- Discard the source tubes whose `(x,z)`-restricted carrier is empty before
forming the terminal family.  This is needed because the terminal line-class
base estimates use an actual retained point. -/
abbrev halfOffsetLineClassTerminalSourceSubfamily
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    Kakeya.Streamlined.TubeSubfamily
      (commonSource.halfOffsetLineClassTerminalSourceFamily retubing) :=
  wz2PaperNonemptyCarrierSubfamily box.restricted

/-- The literal `(x,z)` restriction reindexed along its nonempty carriers. -/
def halfOffsetLineClassTerminalSourceShading
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    WZ1PaperTubeShading
      (wz2PaperNonemptyCarrierSubfamily box.restricted).family :=
  wz2PaperNonemptyCarrierShading box.restricted

/-- Removing empty `(x,z)` carriers preserves their union. -/
theorem halfOffsetLineClassTerminalSourceShading_union
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).union =
      box.restricted.union := by
  apply Set.Subset.antisymm
  · exact restrictPaperShading_union_subset
      (wz2PaperNonemptyCarrierSubfamily box.restricted) box.restricted
  · rintro point ⟨index, hpoint⟩
    have hindex : index ∈ wz2PaperNonemptyCarrierIndices box.restricted :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ index, ⟨point, hpoint⟩⟩
    let selectedIndex : Fin
        (wz2PaperNonemptyCarrierSubfamily box.restricted).family.card :=
      (wz2PaperNonemptyCarrierIndices box.restricted).orderIsoOfFin rfl |>.symm
        ⟨index, hindex⟩
    refine ⟨selectedIndex, ?_⟩
    change point ∈ box.restricted.carrier
      ((wz2PaperNonemptyCarrierSubfamily box.restricted).embedding selectedIndex)
    have hembedding :
        (wz2PaperNonemptyCarrierSubfamily box.restricted).embedding selectedIndex =
          index := by
      exact congrArg Subtype.val
        ((wz2PaperNonemptyCarrierIndices box.restricted).orderIsoOfFin rfl
          |>.apply_symm_apply ⟨index, hindex⟩)
    rwa [hembedding]

/-- Removing empty `(x,z)` carriers preserves indexed shaded mass. -/
theorem halfOffsetLineClassTerminalSourceShading_mass
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth) :
    (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).mass =
      box.restricted.mass := by
  change (restrictPaperShading
      (wz2PaperNonemptyCarrierSubfamily box.restricted)
      box.restricted).mass = box.restricted.mass
  unfold wz2PaperNonemptyCarrierSubfamily
  rw [restrictPaperShading_fromFinset_mass]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro index _ hindex
  have hempty : box.restricted.carrier index = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp fun hnonempty =>
      hindex (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonempty⟩)
  simp [hempty]

/-- Every retained terminal source carrier is genuinely occupied. -/
theorem halfOffsetLineClassTerminalSourceShading_carrier_nonempty
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (index : Fin
      (wz2PaperNonemptyCarrierSubfamily box.restricted).family.card) :
    ((commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
      index).Nonempty := by
  change (box.restricted.carrier
    ((wz2PaperNonemptyCarrierSubfamily box.restricted).embedding index)).Nonempty
  have hmem :
      (wz2PaperNonemptyCarrierSubfamily box.restricted).embedding index ∈
        wz2PaperNonemptyCarrierIndices box.restricted :=
    Finset.orderEmbOfFin_mem
      (wz2PaperNonemptyCarrierIndices box.restricted) rfl index
  exact (Finset.mem_filter.mp hmem).2

/-- Generic terminal family at an explicit target radius. -/
abbrev halfOffsetLineClassTerminalFamily
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ) :
    Kakeya.Streamlined.TubeFamily targetDelta :=
  pureWZ2LineClassNormalizationFamily
    (wz2PaperNonemptyCarrierSubfamily box.restricted).family
    box.center pureWZ2DirectHalfOffsetTerminalLambda
    pureWZ2DirectHalfOffsetTerminalLambda_pos

/-- The unsaturated terminal shading is the literal image of the selected
half-offset exact shading. -/
def halfOffsetLineClassTerminalExactShading
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap box.center
          pureWZ2DirectHalfOffsetTerminalLambda ''
          (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
            index ⊆
        wz1PaperTubeCarrier
          ((commonSource.halfOffsetLineClassTerminalFamily retubing box
            targetDelta).tube index)) :
    WZ1PaperTubeShading
      (commonSource.halfOffsetLineClassTerminalFamily retubing box
        targetDelta) :=
  pureWZ2LineClassNormalizationExactShading
    (commonSource.halfOffsetLineClassTerminalSourceShading retubing box) box.center
    pureWZ2DirectHalfOffsetTerminalLambda
    pureWZ2DirectHalfOffsetTerminalLambda_pos hcarrier

/-- The terminal exact union is exactly the set consumed by the direct
half-offset terminal plane map. -/
theorem halfOffsetLineClassTerminalExactShading_union
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap box.center
          pureWZ2DirectHalfOffsetTerminalLambda ''
          (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
            index ⊆
        wz1PaperTubeCarrier
          ((commonSource.halfOffsetLineClassTerminalFamily retubing box
            targetDelta).tube index)) :
    (commonSource.halfOffsetLineClassTerminalExactShading retubing box
      targetDelta hcarrier).union =
      commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := pureWZ2DirectHalfOffsetTerminalLambda) := by
  unfold halfOffsetLineClassTerminalExactShading
  rw [pureWZ2LineClassNormalizationExactShading_union]
  rw [commonSource.halfOffsetLineClassTerminalSourceShading_union]
  rfl

/-- Exact `lambda^2` Jacobian receipt for the literal terminal image. -/
theorem halfOffsetLineClassTerminalExactShading_mass
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap box.center
          pureWZ2DirectHalfOffsetTerminalLambda ''
          (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
            index ⊆
        wz1PaperTubeCarrier
          ((commonSource.halfOffsetLineClassTerminalFamily retubing box
            targetDelta).tube index)) :
    (commonSource.halfOffsetLineClassTerminalExactShading retubing box
      targetDelta hcarrier).mass =
      ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
        box.restricted.mass := by
  unfold halfOffsetLineClassTerminalExactShading
  rw [pureWZ2LineClassNormalizationExactShading_mass]
  rw [commonSource.halfOffsetLineClassTerminalSourceShading_mass]

/-- Generic cubical terminal shading.  The target scale, radius budget, and
final crop are deliberately explicit. -/
def halfOffsetLineClassTerminalCubicalShading
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hsourceDelta : 0 < anisotropicPaperAlignedScale delta
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d)
    (htargetDelta : 0 < targetDelta)
    (hradius : pureWZ2DirectHalfOffsetTerminalLambda *
        (6 * anisotropicPaperAlignedScale delta
          commonSource.halfOffsetAssembly.horizontalSource.c
          commonSource.halfOffsetAssembly.horizontalSource.d) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
          (pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda ''
            (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
              index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperTubeShading
      (commonSource.halfOffsetLineClassTerminalFamily retubing box
        targetDelta) :=
  pureWZ2LineClassNormalizationCubicalShading
    (commonSource.halfOffsetLineClassTerminalSourceShading retubing box) box.center
    pureWZ2DirectHalfOffsetTerminalLambda_one_le hsourceDelta htargetDelta
    hradius hcrop

/-- The generic terminal construction is cubical at its explicit target
scale. -/
theorem halfOffsetLineClassTerminalCubicalShading_cubical
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hsourceDelta : 0 < anisotropicPaperAlignedScale delta
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d)
    (htargetDelta : 0 < targetDelta)
    (hradius : pureWZ2DirectHalfOffsetTerminalLambda *
        (6 * anisotropicPaperAlignedScale delta
          commonSource.halfOffsetAssembly.horizontalSource.c
          commonSource.halfOffsetAssembly.horizontalSource.d) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
          (pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda ''
            (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
              index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperIsCubicalShading
      (commonSource.halfOffsetLineClassTerminalCubicalShading retubing box
        targetDelta hsourceDelta htargetDelta hradius hcrop) :=
  pureWZ2LineClassNormalizationCubicalShading_cubical
    (commonSource.halfOffsetLineClassTerminalSourceShading retubing box)
    box.center pureWZ2DirectHalfOffsetTerminalLambda_one_le hsourceDelta
    htargetDelta hradius hcrop

/-- Every cubical terminal point has a same-cell witness in the literal
terminal exact set. -/
theorem halfOffsetLineClassTerminalCubicalShading_targetWitness
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hsourceDelta : 0 < anisotropicPaperAlignedScale delta
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d)
    (htargetDelta : 0 < targetDelta)
    (hradius : pureWZ2DirectHalfOffsetTerminalLambda *
        (6 * anisotropicPaperAlignedScale delta
          commonSource.halfOffsetAssembly.horizontalSource.c
          commonSource.halfOffsetAssembly.horizontalSource.d) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
          (pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda ''
            (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
              index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ∀ point : {point : Point3 // point ∈
      (commonSource.halfOffsetLineClassTerminalCubicalShading retubing box
        targetDelta hsourceDelta htargetDelta hradius hcrop).union},
      ∃ source : {point : Point3 // point ∈
        commonSource.halfOffsetTerminalExactSet retubing box
          (lambda := pureWZ2DirectHalfOffsetTerminalLambda)},
        dist (point : Point3) (source : Point3) ≤
          targetDelta * Real.sqrt 3 :=
  by
    intro point
    rcases pureWZ2LineClassNormalizationCubicalShading_targetWitness
        (commonSource.halfOffsetLineClassTerminalSourceShading retubing box)
        box.center pureWZ2DirectHalfOffsetTerminalLambda_one_le hsourceDelta
        htargetDelta hradius hcrop point with ⟨source, hdist⟩
    refine ⟨⟨source, ?_⟩, hdist⟩
    rcases source.property with ⟨raw, hraw, hsource⟩
    refine ⟨raw, ?_, hsource⟩
    rw [← commonSource.halfOffsetLineClassTerminalSourceShading_union
      retubing box]
    exact hraw

/-- Cubical saturation preserves the exact `lambda^2` mass receipt. -/
theorem halfOffsetLineClassTerminalCubicalShading_mass_lower
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (hsourceDelta : 0 < anisotropicPaperAlignedScale delta
      commonSource.halfOffsetAssembly.horizontalSource.c
      commonSource.halfOffsetAssembly.horizontalSource.d)
    (htargetDelta : 0 < targetDelta)
    (hradius : pureWZ2DirectHalfOffsetTerminalLambda *
        (6 * anisotropicPaperAlignedScale delta
          commonSource.halfOffsetAssembly.horizontalSource.c
          commonSource.halfOffsetAssembly.horizontalSource.d) +
        2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
          (pureWZ2LineClassNormalizationMap box.center
            pureWZ2DirectHalfOffsetTerminalLambda ''
            (commonSource.halfOffsetLineClassTerminalSourceShading retubing box).carrier
              index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    ENNReal.ofReal (pureWZ2DirectHalfOffsetTerminalLambda ^ 2) *
        box.restricted.mass ≤
      (commonSource.halfOffsetLineClassTerminalCubicalShading retubing box
        targetDelta hsourceDelta htargetDelta hradius hcrop).mass :=
  by
    rw [← commonSource.halfOffsetLineClassTerminalSourceShading_mass
      retubing box]
    exact pureWZ2LineClassNormalizationCubicalShading_mass_lower
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing box)
      box.center pureWZ2DirectHalfOffsetTerminalLambda_one_le hsourceDelta
      htargetDelta hradius hcrop

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
