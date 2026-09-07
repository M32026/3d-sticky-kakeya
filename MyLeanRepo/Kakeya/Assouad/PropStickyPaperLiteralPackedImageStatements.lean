import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSelectedImageStatements

/-!
# Packed source image inside one fixed literal family

The geometric tree constructs one fixed literal target family before the
final fine-tube packing refinement.  A packed source subfamily therefore has
to be represented as a genuine target subfamily of that already-fixed family,
not by independently choosing a second literal family.

This module defines the exact finite reindexing and freezes the non-recursive
image package on it.  Hereditary nearby-scale CWA is deliberately not asserted
for the packed target subfamily; it must be restored by the separate finite
parent-regularization route.
-/

noncomputable section

namespace Kakeya.Assouad

noncomputable def
    WZ2PaperLiteralUnitRescaledFamilyData.sourceEquiv
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (data :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho) :
    Fin data.targetFamily.card ≃ Fin sourceFamily.card :=
  Equiv.ofBijective data.sourceIndex data.sourceIndex_bijective

/-- Target tubes corresponding exactly to one supplied source subfamily. -/
noncomputable def
    WZ2PaperLiteralUnitRescaledFamilyData.targetSubfamilyForSource
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (data :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily) :
    Kakeya.Streamlined.TubeSubfamily data.targetFamily where
  family :=
    { card := selected.family.card
      tube := fun index =>
        data.targetFamily.tube
          (data.sourceEquiv.symm (selected.embedding index)) }
  embedding :=
    { toFun := fun index =>
        data.sourceEquiv.symm (selected.embedding index)
      inj' := fun first second heq =>
        selected.embedding.injective
          (data.sourceEquiv.symm.injective heq) }
  tube_eq _ := rfl

@[simp] theorem
    WZ2PaperLiteralUnitRescaledFamilyData.targetSubfamilyForSource_ambient
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (data :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily)
    (index : Fin selected.family.card) :
    data.sourceIndex
        ((data.targetSubfamilyForSource selected).embedding index) =
      selected.embedding index := by
  exact data.sourceEquiv.apply_symm_apply (selected.embedding index)

/--
Restrict a fixed literal family to one source subfamily while preserving the
same ambient target tubes definitionally.
-/
noncomputable def
    WZ2PaperLiteralUnitRescaledFamilyData.restrictToSourceSubfamily
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (data :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily) :
    WZ2PaperLiteralUnitRescaledFamilyData
      selected.family anchor hrho where
  targetFamily := (data.targetSubfamilyForSource selected).family
  sourceIndex := fun index => index
  sourceIndex_bijective := Function.bijective_id
  target_line_class :=
    data.target_line_class.subfamily
      (data.targetSubfamilyForSource selected)
  target_axis := by
    intro index
    rw [(data.targetSubfamilyForSource selected).tube_eq]
    rw [data.target_axis]
    congr 2
    rw [data.targetSubfamilyForSource_ambient selected index]
    exact (selected.tube_eq index).symm

@[simp] theorem
    WZ2PaperLiteralUnitRescaledFamilyData.restrictToSourceSubfamily_targetFamily
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (data :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily) :
    (data.restrictToSourceSubfamily selected).targetFamily =
      (data.targetSubfamilyForSource selected).family :=
  rfl

structure WZ2PaperLiteralPackedImageData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {ambientConstant selectedConstant : ENNReal}
    (historical :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho ambientConstant)
    (rootSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (fullLiteral :
      WZ2PaperLiteralUnitRescaledFamilyData
        rootSelected.family (coarse.tube parent) hrho)
    (packed :
      Kakeya.Streamlined.TubeSubfamily rootSelected.family)
    (sourceShading : WZ1PaperTubeShading packed.family) where
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      (fullLiteral.restrictToSourceSubfamily packed)
      sourceShading
  correspondence :
    WZ2PaperLiteralHistoricalCorrespondenceData
      historical (rootSelected.comp packed)
      (fullLiteral.restrictToSourceSubfamily packed)
  target_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct
      (fullLiteral.targetSubfamilyForSource packed).family
  target_convex_wolff :
    WZ2PaperConvexWolffBound
      (fullLiteral.targetSubfamilyForSource packed).family
      ((100 : ENNReal) * selectedConstant)
  image_measure :
    WZ2PaperLiteralImageMeasureData
      (fullLiteral.restrictToSourceSubfamily packed)
      sourceShading literalShading
  target_cubical :
    WZ1PaperIsCubicalShading literalShading.targetShading
  source_cardinality_eq :
    (fullLiteral.targetSubfamilyForSource packed).family.enncard =
      packed.family.enncard
  source_multiplicity_le :
    ∀ point,
      (sourceShading.pointMultiplicity point : ENNReal) ≤
        (literalShading.targetShading.pointMultiplicity
          (wz2PaperLiteralUnitRescalingMap
            (coarse.tube parent) hrho point) : ENNReal)

def WZ2PaperLiteralPackedImageStatement : Prop :=
  WZ2PaperLiteralUnitRescaledShadingStatement →
  WZ2PaperLiteralHistoricalCorrespondenceStatement →
  WZ2PaperHistoricalToLiteralCWAStatement →
  WZ2PaperLongitudinalCompressionLineDistanceStatement →
  WZ2PaperLiteralEssentialDistinctnessTransferStatement →
  WZ2PaperLiteralImageMeasureStatement →
  WZ2PaperLiteralImageMultiplicityStatement →
  ∀ {delta rho : ℝ},
    0 < delta →
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : WZ2PaperPartitioningCover fine coarse},
          ∀ {parent : Fin coarse.card},
            ∀ {hrho : 0 < rho},
              rho ≤ 1 →
              delta / rho ≤ 1 / 24 →
              ∀ {ambientConstant selectedConstant : ENNReal},
                ∀ (historical :
                    WZ2PaperUnitRescaledFamilyData
                      cover parent hrho ambientConstant),
                  ∀ (rootSelected :
                      Kakeya.Streamlined.TubeSubfamily
                        (cover.fullFiberSubfamily parent).family),
                    ∀ (fullLiteral :
                        WZ2PaperLiteralUnitRescaledFamilyData
                          rootSelected.family
                          (coarse.tube parent) hrho),
                      ∀ (packed :
                          Kakeya.Streamlined.TubeSubfamily
                            rootSelected.family),
                        ∀ (sourceShading :
                            WZ1PaperTubeShading packed.family),
                          WZ1PaperIsLineClass packed.family →
                          WZ1PaperTubeInLineClass
                            (coarse.tube parent) →
                          (∀ source,
                            WZ1PaperTubeCovers
                              (packed.family.tube source)
                              (coarse.tube parent)) →
                          WZ1PaperIsEssentiallyDistinct
                            (historical.targetSubfamilyForSource
                              (rootSelected.comp packed)).family →
                          WZ2PaperConvexWolffBound
                            (historical.targetSubfamilyForSource
                              (rootSelected.comp packed)).family
                            selectedConstant →
                            Nonempty
                              (WZ2PaperLiteralPackedImageData
                                (selectedConstant := selectedConstant)
                                historical rootSelected fullLiteral
                                packed sourceShading)

end Kakeya.Assouad

end
