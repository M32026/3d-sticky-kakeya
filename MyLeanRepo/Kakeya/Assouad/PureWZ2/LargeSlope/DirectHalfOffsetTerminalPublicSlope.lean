import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CoupledIsotropicSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectExactSlopeGlobalADBridge

/-!
# Safe public slope for the direct half-offset terminal

The actual terminal uses the same half-offset shear as its affine map.  The
globally safe source representative is therefore the coupled two-jet
extension, translated by the exact change of shear.  The final public slope
is its line-class normalization about the selected terminal box center.

The translation changes no derivatives.  In particular, the endpoint-safe
coupled nonsingularity theorem still applies when the box center merely lies
in the closed paper window; no nonexistent endpoint margin is assumed.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The actual fixed shear selected on the retained horizontal source.  This
is exactly the coefficient used by the terminal affine and normal maps. -/
def safeHalfOffsetFrameSlope : ℝ :=
  PureWZ2HalfOffsetHorizontalSourceData.offset
    commonSource.halfOffsetAssembly.horizontalSource

/-- The exact intercept correction between the midpoint-centered coupled
slope and the half-offset affine shear. -/
def safeHalfOffsetSlopeShift : ℝ :=
  (commonSource.commonBand.band.lemma31.data.globalSlope
      commonSource.subband.anchor -
    safeHalfOffsetFrameSlope commonSource) /
      (((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale) *
        (commonSource.subband.right - commonSource.subband.left) / 2)

/-- Globally smooth source slope synchronized with the half-offset triangular
map.  Its base is the endpoint-safe coupled two-jet extension. -/
def safeHalfOffsetSourceSlope : SlopeFunction :=
  (pureWZ2CoupledMarginSlopeFunction commonSource.subband).addConstant
    (safeHalfOffsetSlopeShift commonSource)

/-- Paper-facing slope after the actual fixed line-class normalization. -/
def safePublicSlope (terminal : commonSource.TerminalGeometry) : SlopeFunction :=
  pureWZ2LineClassNormalizedSlope
    (safeHalfOffsetSourceSlope commonSource)
    (terminal.box.center 2) pureWZ2DirectHalfOffsetTerminalLambda

/-- The terminal box center has a legal paper height. -/
theorem box_center_height_mem
    (terminal : commonSource.TerminalGeometry) :
    terminal.box.center 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  exact abs_le.mp <| by
    simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using
      terminal.box.center_mem (2 : Fin 3)

/-- The safe public slope is nonsingular for every actually selected terminal
box, including boxes whose center touches an endpoint of `[-1,1]`. -/
theorem safePublicSlope_nonsingular
    (terminal : commonSource.TerminalGeometry) :
    (safePublicSlope commonSource terminal).IsNonsingular := by
  let lambda := pureWZ2DirectHalfOffsetTerminalLambda
  let shift := safeHalfOffsetSlopeShift commonSource
  have hbase :
      (pureWZ2CoupledPublicExactSlopeFunction commonSource.subband
        (terminal.box.center 2) lambda).IsNonsingular :=
    pureWZ2CoupledPublicExactSlopeFunction_nonsingular
      commonSource.subband pureWZ2DirectHalfOffsetTerminalLambda_one_le
      (box_center_height_mem commonSource terminal)
  have htranslated :
      ((pureWZ2CoupledPublicExactSlopeFunction commonSource.subband
        (terminal.box.center 2) lambda).addConstant
          (lambda * shift)).IsNonsingular :=
    SlopeFunction.addConstant_isNonsingular hbase (lambda * shift)
  intro t ht
  have hbounds := htranslated t ht
  simpa only [safePublicSlope, safeHalfOffsetSourceSlope,
    pureWZ2CoupledPublicExactSlopeFunction,
    pureWZ2LineClassNormalizedSlope, SlopeFunction.addConstant, lambda, shift,
    mul_add] using hbounds

/-- On every genuine normalized source height, the safe extension is exactly
the slope transported by the selected subband rescaling and its half-offset
shear. -/
theorem safeHalfOffsetSourceSlope_eq_transport
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    safeHalfOffsetSourceSlope commonSource t =
      anisotropicRescaledSlopeWithShear
        commonSource.commonBand.band.lemma31.data.globalSlope
        commonSource.subband.left commonSource.subband.right
        ((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale)
        (safeHalfOffsetFrameSlope commonSource) t := by
  have hsourceHeight :=
    pureWZ2CoupledSourceHeight_mem commonSource.subband ht
  have hsourceBand :
      pureWZ2CoupledSourceHeight commonSource.subband t ∈
        Set.Icc commonSource.commonBand.band.left
          commonSource.commonBand.band.right :=
    ⟨commonSource.subband.left_mem.trans hsourceHeight.1,
      hsourceHeight.2.trans commonSource.subband.right_mem⟩
  have hmidSubband :
      commonSource.subband.left +
          (commonSource.subband.right - commonSource.subband.left) / 2 ∈
        Set.Icc commonSource.subband.left commonSource.subband.right := by
    constructor <;> linarith [commonSource.subband.ordered]
  have hmidBand :
      commonSource.subband.left +
          (commonSource.subband.right - commonSource.subband.left) / 2 ∈
        Set.Icc commonSource.commonBand.band.left
          commonSource.commonBand.band.right :=
    ⟨commonSource.subband.left_mem.trans hmidSubband.1,
      hmidSubband.2.trans commonSource.subband.right_mem⟩
  rw [show safeHalfOffsetSourceSlope commonSource t =
      pureWZ2CoupledMarginSlopeFunction commonSource.subband t +
        safeHalfOffsetSlopeShift commonSource by rfl]
  change anisotropicRescaledSlope
      (pureWZ2CoupledSourceJetExtension commonSource.commonBand.band)
        commonSource.subband.left commonSource.subband.right
        ((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale) t +
      safeHalfOffsetSlopeShift commonSource = _
  unfold anisotropicRescaledSlope
  change
    pureWZ2CoupledSourceJetExtension commonSource.commonBand.band
          (pureWZ2CoupledSourceHeight commonSource.subband t) / _ -
        pureWZ2CoupledSourceJetExtension commonSource.commonBand.band
          (commonSource.subband.left +
            (commonSource.subband.right - commonSource.subband.left) / 2) / _ +
      safeHalfOffsetSlopeShift commonSource = _
  rw [pureWZ2CoupledSourceJetExtension_eq
      commonSource.commonBand.band hsourceBand,
    pureWZ2CoupledSourceJetExtension_eq
      commonSource.commonBand.band hmidBand]
  unfold safeHalfOffsetSlopeShift anisotropicRescaledSlopeWithShear
    pureWZ2CoupledSourceHeight
  rw [commonSource.subband.anchor_eq]
  ring

/-- The fixed shear appearing in the safe source slope is literally the
selected shear stored by the actual direct source assembly. -/
theorem safeHalfOffsetFrameSlope_eq_actual_geometry
    : safeHalfOffsetFrameSlope commonSource =
      commonSource.halfOffsetAssembly.horizontalSource.geometrySlope
        (commonSource.halfOffsetAssembly.horizontalSource.c +
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2) := by
  exact (commonSource.halfOffsetAssembly_geometry_fixedShear _).symm

/-- On the whole actual source parameter interval, the safe extension equals
the exact global slope chosen by the same half-offset assembly.  This is the
map/slope synchronization receipt used by the terminal transport. -/
theorem safeHalfOffsetSourceSlope_eq_exactGlobalSlope
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    safeHalfOffsetSourceSlope commonSource t =
      commonSource.halfOffsetAssembly.exactGlobalSlope t := by
  rw [safeHalfOffsetSourceSlope_eq_transport commonSource t ht,
    commonSource.halfOffsetAssembly.exactGlobalSlope_formula,
    commonSource.halfOffsetAssembly_globalSlope]
  rw [← safeHalfOffsetFrameSlope_eq_actual_geometry commonSource]
  rcases commonSource.halfOffsetAssembly_source_coordinates with
    ⟨hc, hd, hm⟩
  rw [hc, hd, hm]

/-- Pointwise form after the final line-class normalization.  The hypothesis
is precisely that the inverse terminal height is an actual normalized source
height; no assertion is made outside that range. -/
theorem safePublicSlope_eq_transport
    (terminal : commonSource.TerminalGeometry)
    (t : ℝ)
    (ht : terminal.box.center 2 +
      t / pureWZ2DirectHalfOffsetTerminalLambda ∈ Set.Icc (-1 : ℝ) 1) :
    safePublicSlope commonSource terminal t =
      pureWZ2DirectHalfOffsetTerminalLambda *
        anisotropicRescaledSlopeWithShear
          commonSource.commonBand.band.lemma31.data.globalSlope
          commonSource.subband.left commonSource.subband.right
          ((9 : ℝ) / 10 * commonSource.commonBand.band.slopeScale)
          (safeHalfOffsetFrameSlope commonSource)
          (terminal.box.center 2 +
            t / pureWZ2DirectHalfOffsetTerminalLambda) := by
  change pureWZ2DirectHalfOffsetTerminalLambda *
      safeHalfOffsetSourceSlope commonSource
        (terminal.box.center 2 +
          t / pureWZ2DirectHalfOffsetTerminalLambda) = _
  rw [safeHalfOffsetSourceSlope_eq_transport commonSource _ ht]

/-- On the actual inverse-height range, the endpoint-safe public slope is
pointwise equal to the slope currently transported by the terminal map. -/
theorem safePublicSlope_eq_exactGlobalSlope
    (terminal : commonSource.TerminalGeometry)
    (t : ℝ)
    (ht : terminal.box.center 2 +
      t / pureWZ2DirectHalfOffsetTerminalLambda ∈ Set.Icc (-1 : ℝ) 1) :
    safePublicSlope commonSource terminal t =
      pureWZ2LineClassNormalizedSlope
        commonSource.halfOffsetAssembly.exactGlobalSlope
        (terminal.box.center 2) pureWZ2DirectHalfOffsetTerminalLambda t := by
  change pureWZ2DirectHalfOffsetTerminalLambda *
      safeHalfOffsetSourceSlope commonSource
        (terminal.box.center 2 +
          t / pureWZ2DirectHalfOffsetTerminalLambda) =
    pureWZ2DirectHalfOffsetTerminalLambda *
      commonSource.halfOffsetAssembly.exactGlobalSlope
        (terminal.box.center 2 +
          t / pureWZ2DirectHalfOffsetTerminalLambda)
  rw [safeHalfOffsetSourceSlope_eq_exactGlobalSlope commonSource _ ht]

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
