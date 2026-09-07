import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetLineClassTerminal

/-!
# Incidence for the direct half-offset terminal

This file connects the source-scale projective incidence estimate to the
literal terminal tube direction and the exact terminal plane map.
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

/-- At a point in the selected raw carrier, the literal terminal direction
has source-scale incidence with the fixed projective terminal normal. -/
theorem halfOffsetLineClassTerminal_mappedPoint_incidence
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (terminalBox : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (index : Fin
      (wz2PaperNonemptyCarrierSubfamily terminalBox.restricted).family.card)
    (point : Point3)
    (hpoint : point ∈
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing
        terminalBox).carrier index) :
    let target : {point : Point3 // point ∈
        commonSource.halfOffsetTerminalExactSet retubing terminalBox
          (lambda := pureWZ2DirectHalfOffsetTerminalLambda)} :=
      ⟨pureWZ2LineClassNormalizationMap terminalBox.center
          pureWZ2DirectHalfOffsetTerminalLambda point,
        ⟨point, ⟨(wz2PaperNonemptyCarrierSubfamily
          terminalBox.restricted).embedding index, hpoint⟩, rfl⟩⟩
    |inner ℝ
        (pureWZ2LineClassNormalizationDirection
          pureWZ2DirectHalfOffsetTerminalLambda
          pureWZ2DirectHalfOffsetTerminalLambda_pos
          ((wz2PaperNonemptyCarrierSubfamily terminalBox.restricted).family.tube
            index).direction)
        (commonSource.halfOffsetTerminalExactPlaneMap retubing terminalBox
          target)| ≤ delta := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let lambda := pureWZ2DirectHalfOffsetTerminalLambda
  let target : {point : Point3 // point ∈
      commonSource.halfOffsetTerminalExactSet retubing terminalBox
        (lambda := lambda)} :=
    ⟨pureWZ2LineClassNormalizationMap terminalBox.center lambda point,
      ⟨point, ⟨(wz2PaperNonemptyCarrierSubfamily
        terminalBox.restricted).embedding index, hpoint⟩, rfl⟩⟩
  let rawIndex : Fin retubing.popular.family.card :=
    (wz2PaperNonemptyCarrierSubfamily terminalBox.restricted).embedding index
  have hrawCarrier : point ∈ retubing.raw.exactShading.carrier rawIndex :=
    terminalBox.restricted_subshading rawIndex hpoint
  rw [retubing.raw.exactShading_carrier] at hrawCarrier
  rcases hrawCarrier with ⟨sourcePoint, hsourcePoint, hsourceImage⟩
  let ambientIndex : Fin commonSource.halfOffsetAssembly.cfg.family.card :=
    (wz2PaperNonemptyCarrierSubfamily
      retubing.popular.popular.restricted).embedding rawIndex
  have hsourceAmbient : sourcePoint ∈ source.sourceShading.carrier ambientIndex := by
    exact retubing.popular.source_subshading rawIndex hsourcePoint.1
  let rawTarget : {point : Point3 // point ∈ retubing.raw.exactShading.union} :=
    ⟨point, ⟨rawIndex, terminalBox.restricted_subshading rawIndex hpoint⟩⟩
  have hrawPoint :
      commonSource.halfOffsetTerminalRawPoint retubing terminalBox
          pureWZ2DirectHalfOffsetTerminalLambda_pos target = rawTarget := by
    apply Subtype.ext
    apply (pureWZ2LineClassNormalizationAffineEquiv terminalBox.center lambda
      pureWZ2DirectHalfOffsetTerminalLambda_pos).injective
    rw [pureWZ2LineClassNormalizationAffineEquiv_apply,
      commonSource.halfOffsetTerminal_map_rawPoint retubing terminalBox
        pureWZ2DirectHalfOffsetTerminalLambda_pos]
    rw [pureWZ2LineClassNormalizationAffineEquiv_apply]
  let ambientSourcePoint : {point : Point3 //
      point ∈ source.sourceShading.union} :=
    ⟨sourcePoint, ⟨ambientIndex, hsourceAmbient⟩⟩
  have hsourcePreimage :
      commonSource.halfOffsetTerminalSourcePoint retubing terminalBox
          pureWZ2DirectHalfOffsetTerminalLambda_pos target = ambientSourcePoint := by
    apply Subtype.ext
    apply (anisotropicCenteredRescalingAffineEquiv
      (pureWZ2DirectGeometrySlope source) source.c source.d source.m
      (pureWZ2DirectAnisotropicCenter retubing.popular) source.ordered
      source.slopeScale_pos).injective
    rw [anisotropicCenteredRescalingAffineEquiv_apply]
    change anisotropicCenteredRescalingMap
        (pureWZ2DirectGeometrySlope source) source.c source.d source.m
        (pureWZ2DirectAnisotropicCenter retubing.popular)
        (retubing.raw.exactSourcePoint
          (commonSource.halfOffsetTerminalRawPoint retubing terminalBox
            pureWZ2DirectHalfOffsetTerminalLambda_pos target)) = _
    rw [hrawPoint, retubing.raw.map_exactSourcePoint]
    rw [anisotropicCenteredRescalingAffineEquiv_apply]
    exact hsourceImage.symm
  have hincidence := commonSource.halfOffset_normalizedDirection_incidence
    ambientIndex sourcePoint hsourceAmbient
  change |inner ℝ
      (pureWZ2LineClassNormalizationDirection lambda
        pureWZ2DirectHalfOffsetTerminalLambda_pos
        ((wz2PaperNonemptyCarrierSubfamily terminalBox.restricted).family.tube
          index).direction)
      (commonSource.halfOffsetTerminalExactPlaneMap retubing terminalBox target)| ≤
    delta
  rw [show ((wz2PaperNonemptyCarrierSubfamily terminalBox.restricted).family.tube
      index).direction = anisotropicAnchoredDirection
        (pureWZ2DirectGeometrySlope source) source.c source.d source.m
        (retubing.popular.family.tube rawIndex) by rfl]
  rw [show anisotropicAnchoredDirection
      (pureWZ2DirectGeometrySlope source) source.c source.d source.m
      (retubing.popular.family.tube rawIndex) =
        (‖dPhiLin (pureWZ2DirectGeometrySlope source) source.c source.d source.m
            (wz1PaperDirection (retubing.popular.family.tube rawIndex))‖⁻¹ : ℝ) •
          dPhiLin (pureWZ2DirectGeometrySlope source) source.c source.d source.m
            (wz1PaperDirection (retubing.popular.family.tube rawIndex)) by rfl]
  rw [pureWZ2LineClassNormalizationDirection_dPhi_eq
    (pureWZ2DirectGeometrySlope source) source.ordered source.slopeScale_pos
      pureWZ2DirectHalfOffsetTerminalLambda_pos (by
        intro hzero
        have hnorm := congrArg norm hzero
        rw [wz1PaperDirection_norm, norm_zero] at hnorm
        norm_num at hnorm)]
  rw [show pureWZ2DirectGeometrySlope source
      (source.c + (source.d - source.c) / 2) =
        PureWZ2HalfOffsetHorizontalSourceData.offset source by
      exact commonSource.halfOffsetAssembly_geometry_fixedShear _]
  unfold halfOffsetTerminalExactPlaneMap
  change |inner ℝ _
      (pureWZ2OffsetProjectiveTotalNormalizedNormal
        (source.m * (source.d - source.c) / 2)
        (2 / (source.d - source.c)) pureWZ2FixedProjectiveNormalLambda
        (pureWZ2OffsetShearProjectiveNormal
          (PureWZ2HalfOffsetHorizontalSourceData.offset source)
          (source.sourceLocalGrains.planeMap
            (commonSource.halfOffsetTerminalSourcePoint retubing terminalBox
              _ target))))| ≤ delta
  rw [show commonSource.halfOffsetTerminalSourcePoint retubing terminalBox
      _ target = ambientSourcePoint by exact hsourcePreimage]
  rw [show retubing.popular.family.tube rawIndex =
      commonSource.halfOffsetAssembly.cfg.family.tube ambientIndex by
        exact (wz2PaperNonemptyCarrierSubfamily
          retubing.popular.popular.restricted).tube_eq rawIndex]
  simpa [ambientIndex, rawIndex, source, lambda,
    pureWZ2DirectHalfOffsetTerminalLambda]
    using hincidence

/-- Caller-facing form using the direction stored by the literal terminal
family itself. -/
theorem halfOffsetLineClassTerminal_tube_mappedPoint_incidence
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (terminalBox : PureWZ2LineClassPopularBoxData retubing.raw.exactShading
      pureWZ2DirectHalfOffsetTerminalWidth)
    (targetDelta : ℝ)
    (index : Fin
      (wz2PaperNonemptyCarrierSubfamily terminalBox.restricted).family.card)
    (point : Point3)
    (hpoint : point ∈
      (commonSource.halfOffsetLineClassTerminalSourceShading retubing
        terminalBox).carrier index) :
    let target : {point : Point3 // point ∈
        commonSource.halfOffsetTerminalExactSet retubing terminalBox
          (lambda := pureWZ2DirectHalfOffsetTerminalLambda)} :=
      ⟨pureWZ2LineClassNormalizationMap terminalBox.center
          pureWZ2DirectHalfOffsetTerminalLambda point,
        ⟨point, ⟨(wz2PaperNonemptyCarrierSubfamily
          terminalBox.restricted).embedding index, hpoint⟩, rfl⟩⟩
    |inner ℝ
        ((commonSource.halfOffsetLineClassTerminalFamily retubing terminalBox
          targetDelta).tube index).direction
        (commonSource.halfOffsetTerminalExactPlaneMap retubing terminalBox
          target)| ≤ delta := by
  simpa [halfOffsetLineClassTerminalFamily,
    pureWZ2LineClassNormalizationFamily, pureWZ2LineClassNormalizationTube]
    using commonSource.halfOffsetLineClassTerminal_mappedPoint_incidence
      retubing terminalBox index point hpoint

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
