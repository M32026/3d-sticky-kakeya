import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRepresentativeParent

/-!
# Centered representatives of the horizontal-normalized family

Definition 2.12 uses ordinary unit segments.  After an affine image we choose
the canonical midpoint-centered representative of each supporting line.
This changes neither the paper carrier nor any shading set.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Canonically centered representatives of the exact combined-image lines. -/
def pureWZ2HorizontalNormalizedCenteredFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2PaperCenteredTube
    ((pureWZ2HorizontalNormalizedExactFamily
      (targetDelta := targetDelta) sourceFamily g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube index)

@[simp] theorem pureWZ2HorizontalNormalizedCenteredFamily_tube
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (index : Fin sourceFamily.card) :
    (pureWZ2HorizontalNormalizedCenteredFamily (targetDelta := targetDelta)
      sourceFamily g c d m anisotropicCenter horizontalCenter lambda
        hcd hm hlambda).tube index =
      pureWZ2PaperCenteredTube
        ((pureWZ2HorizontalNormalizedExactFamily
          (targetDelta := targetDelta) sourceFamily g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
          index) :=
  rfl

/-- Centering preserves the exact combined-image supporting line. -/
theorem pureWZ2HorizontalNormalizedCenteredFamily_axis
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (index : Fin sourceFamily.card) :
    tubeAxisLine
        ((pureWZ2HorizontalNormalizedCenteredFamily
          (targetDelta := targetDelta) sourceFamily g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
          index) =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda ''
          tubeAxisLine (sourceFamily.tube index) := by
  change tubeAxisLine
      (pureWZ2PaperCenteredTube
        (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
          horizontalCenter lambda hcd hm hlambda
            (sourceFamily.tube index) : Kakeya.DeltaTube targetDelta)) = _
  rw [pureWZ2PaperCenteredTube_axis]
  exact pureWZ2HorizontalNormalizedExactTube_axis g c d m
    anisotropicCenter horizontalCenter lambda hcd hm hlambda
      (sourceFamily.tube index)

/-- Line class transfers from the exact representatives to their centered
versions. -/
theorem pureWZ2HorizontalNormalizedCenteredFamily_lineClass
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hline : WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda)) :
    WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedCenteredFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda) := by
  intro index
  exact pureWZ2PaperCenteredTube_lineClass (hline index)

/-- Every centered target tube is definitionally stable under a second
canonical centering. -/
theorem pureWZ2HorizontalNormalizedCenteredFamily_centered
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hline : WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda)) :
    ∀ index, pureWZ2PaperCenteredTube
      ((pureWZ2HorizontalNormalizedCenteredFamily
        (targetDelta := targetDelta) sourceFamily g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
        index) =
      (pureWZ2HorizontalNormalizedCenteredFamily
        (targetDelta := targetDelta) sourceFamily g c d m
          anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
        index := by
  intro index
  exact pureWZ2PaperCenteredTube_idempotent _ (hline index)

/-- Canonical centering supplies the fixed midpoint bound used by the
representative-parent construction. -/
theorem pureWZ2HorizontalNormalizedCenteredFamily_midpoint_local
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hline : WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda)) :
    ∀ index,
      ‖wz2PaperTubeMidpoint
        ((pureWZ2HorizontalNormalizedCenteredFamily
          (targetDelta := targetDelta) sourceFamily g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambda).tube
          index)‖ ≤ 3 := by
  intro index
  exact pureWZ2PaperCenteredTube_midpoint_norm_le_three _ (hline index)

/-- Retype the cubical shading along canonical centered representatives. -/
def pureWZ2HorizontalNormalizedCenteredShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2) :
    WZ1PaperTubeShading
      (pureWZ2HorizontalNormalizedCenteredFamily (targetDelta := targetDelta)
        sourceFamily g c d m anisotropicCenter horizontalCenter lambda
          hcd hm hlambda) where
  carrier index :=
    (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hsourceDelta htargetDelta hradius hcrop).carrier index
  measurable_carrier index :=
    (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hsourceDelta htargetDelta hradius hcrop).measurable_carrier index
  subset_body index := by
    change (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hsourceDelta htargetDelta hradius hcrop).carrier index ⊆
      wz1PaperTubeCarrier
        (pureWZ2PaperCenteredTube
          (pureWZ2HorizontalNormalizedExactTube g c d m anisotropicCenter
            horizontalCenter lambda hcd hm hlambda
              (sourceFamily.tube index) : Kakeya.DeltaTube targetDelta))
    rw [pureWZ2PaperCenteredTube_paperCarrier]
    exact (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hsourceDelta htargetDelta hradius hcrop).subset_body index

@[simp] theorem pureWZ2HorizontalNormalizedCenteredShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (hradius :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * sourceDelta) + 2 * targetDelta ≤ 6 * targetDelta)
    (hcrop : ∀ index,
      wz1PaperCubicalSaturation targetDelta
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' sourceShading.carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2)
    (index : Fin sourceFamily.card) :
    (pureWZ2HorizontalNormalizedCenteredShading sourceShading g c d m
      anisotropicCenter horizontalCenter lambda hcd hm hlambda
        hsourceDelta htargetDelta hradius hcrop).carrier index =
      (pureWZ2HorizontalNormalizedCubicalShading sourceShading g c d m
        anisotropicCenter horizontalCenter lambda hcd hm hlambda
          hsourceDelta htargetDelta hradius hcrop).carrier index :=
  rfl

end Kakeya.Assouad

end
