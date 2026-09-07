import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian

/-!
# Direct actual-John to caller-literal Convex-Wolff transport

An actual Definition 2.12 parent has radius `actual`, while the Section 6
caller anchor has radius `caller`.  The coordinate change used here sends
the actual parent's outer-John coordinates directly to the caller anchor's
literal WZ coordinates.

Its inverse-volume loss is

`4_000_000 * (caller / actual)^2`.

The scale ratio is essential and is deliberately exposed.  It is later
absorbed by the loss hierarchy; it must not be replaced by an absolute
constant.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Direct coordinate change from one actual parent's John chart to a
possibly different caller anchor's literal WZ chart. -/
noncomputable def wz2PaperActualJohnToCallerLiteralCoordinateChange
    {actual caller : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (callerAnchor : Kakeya.DeltaTube caller)
    (hcaller : 0 < caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  actualJohn.map.symm.trans
    (wz2PaperLiteralUnitRescalingAffineEquiv
      callerAnchor hcaller)

@[simp] theorem
    wz2PaperActualJohnToCallerLiteralCoordinateChange_apply_map
    {actual caller : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (callerAnchor : Kakeya.DeltaTube caller)
    (hcaller : 0 < caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent)
    (point : Point3) :
    wz2PaperActualJohnToCallerLiteralCoordinateChange
        callerAnchor hcaller actualJohn
        (actualJohn.map point) =
      wz2PaperLiteralUnitRescalingMap
        callerAnchor hcaller point := by
  simp [
    wz2PaperActualJohnToCallerLiteralCoordinateChange,
    AffineEquiv.trans_apply
  ]

/-- The direct coordinate change sends every actual-John image exactly to
the caller-literal image of the same physical set. -/
theorem wz2PaperActualJohnToCallerLiteralCoordinateChange_image
    {actual caller : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (callerAnchor : Kakeya.DeltaTube caller)
    (hcaller : 0 < caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent)
    (source : Set Point3) :
    wz2PaperActualJohnToCallerLiteralCoordinateChange
          callerAnchor hcaller actualJohn ''
        (actualJohn.map '' source) =
      wz2PaperLiteralUnitRescalingMap
          callerAnchor hcaller '' source := by
  ext point
  constructor
  · rintro
      ⟨johnPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    exact
      ⟨sourcePoint, hsourcePoint,
        (wz2PaperActualJohnToCallerLiteralCoordinateChange_apply_map
          callerAnchor hcaller actualJohn sourcePoint).symm⟩
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    exact
      ⟨actualJohn.map sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩,
        wz2PaperActualJohnToCallerLiteralCoordinateChange_apply_map
          callerAnchor hcaller actualJohn sourcePoint⟩

/-- Exact determinant of the direct actual-John to caller-literal map. -/
theorem wz2PaperActualJohnToCallerLiteralCoordinateChange_abs_det
    {actual caller : ℝ}
    {actualParent : Kakeya.DeltaTube actual}
    (callerAnchor : Kakeya.DeltaTube caller)
    (hcaller : 0 < caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent) :
    |LinearMap.det
        ((wz2PaperActualJohnToCallerLiteralCoordinateChange
          callerAnchor hcaller actualJohn).linear :
          Point3 →ₗ[ℝ] Point3)| =
      ((1 / 100 : ℝ) ^ 3 * (1 / caller) ^ 2) *
        |LinearMap.det
          (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| := by
  let literal :=
    wz2PaperLiteralUnitRescalingAffineEquiv
      callerAnchor hcaller
  have hlinear :
      (wz2PaperActualJohnToCallerLiteralCoordinateChange
        callerAnchor hcaller actualJohn).linear =
        actualJohn.map.symm.linear.trans literal.linear := rfl
  rw [hlinear]
  have hcomposition :
      ((actualJohn.map.symm.linear.trans literal.linear :
        Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
        (literal.linear : Point3 →ₗ[ℝ] Point3).comp
          (actualJohn.map.symm.linear :
            Point3 →ₗ[ℝ] Point3) := by
    ext point
    rfl
  rw [hcomposition, LinearMap.det_comp, abs_mul]
  have hJohn :
      (actualJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        actualJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  rw [hJohn,
    wz2PaperLiteralUnitRescalingAffineEquiv_abs_det
      callerAnchor hcaller]

/-- Lower determinant bound with the genuine caller/actual scale ratio. -/
theorem
    wz2PaperActualJohnToCallerLiteralCoordinateChange_abs_det_lower
    {actual caller : ℝ}
    (hactual : 0 < actual)
    (hcaller : 0 < caller)
    (actualParent : Kakeya.DeltaTube actual)
    (callerAnchor : Kakeya.DeltaTube caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent) :
    (4000000 * (caller / actual) ^ 2 : ℝ)⁻¹ ≤
      |LinearMap.det
        ((wz2PaperActualJohnToCallerLiteralCoordinateChange
          callerAnchor hcaller actualJohn).linear :
          Point3 →ₗ[ℝ] Point3)| := by
  rw [
    wz2PaperActualJohnToCallerLiteralCoordinateChange_abs_det
      callerAnchor hcaller actualJohn
  ]
  have hJohn :=
    wz2Paper_outerJohn_abs_det_lower
      actualParent hactual
  calc
    (4000000 * (caller / actual) ^ 2 : ℝ)⁻¹ =
        ((1 / 100 : ℝ) ^ 3 * (1 / caller) ^ 2) *
          (actual ^ 2 / 4) := by
      field_simp [hactual.ne', hcaller.ne']
      ring
    _ ≤
        ((1 / 100 : ℝ) ^ 3 * (1 / caller) ^ 2) *
          |LinearMap.det
            (actualJohn.parent_convex_body.outerJohnEllipsoidMap :
              Point3 →ₗ[ℝ] Point3)| := by
      gcongr

/-- Inverse-volume loss of the direct actual-John to caller-literal map. -/
theorem
    wz2PaperActualJohnToCallerLiteralCoordinateChange_inverse_volume
    {actual caller : ℝ}
    (hactual : 0 < actual)
    (hcaller : 0 < caller)
    (actualParent : Kakeya.DeltaTube actual)
    (callerAnchor : Kakeya.DeltaTube caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent)
    (targetSet : Set Point3) :
    volume
        ((wz2PaperActualJohnToCallerLiteralCoordinateChange
          callerAnchor hcaller actualJohn).symm '' targetSet) ≤
      ENNReal.ofReal
          (4000000 * (caller / actual) ^ 2) *
        volume targetSet := by
  let coordinateChange :=
    wz2PaperActualJohnToCallerLiteralCoordinateChange
      callerAnchor hcaller actualJohn
  rw [wz2PaperAffineEquiv_volume_image_eq]
  let loss : ℝ :=
    4000000 * (caller / actual) ^ 2
  have lossPos : 0 < loss := by
    dsimp only [loss]
    positivity
  have hdetLower :
      loss⁻¹ ≤
        |LinearMap.det
          (coordinateChange.linear :
            Point3 →ₗ[ℝ] Point3)| := by
    exact
      wz2PaperActualJohnToCallerLiteralCoordinateChange_abs_det_lower
        hactual hcaller actualParent callerAnchor actualJohn
  have hdetPos :
      0 <
        |LinearMap.det
          (coordinateChange.linear :
            Point3 →ₗ[ℝ] Point3)| := by
    exact
      lt_of_lt_of_le (inv_pos.mpr lossPos) hdetLower
  have hinverse :
      |LinearMap.det
          (coordinateChange.symm.linear :
            Point3 →ₗ[ℝ] Point3)| ≤
        loss := by
    have hsymm :
        coordinateChange.symm.linear =
          coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv]
    have hinverseOrder :
        |LinearMap.det
            (coordinateChange.linear :
              Point3 →ₗ[ℝ] Point3)|⁻¹ ≤
          (loss⁻¹)⁻¹ :=
      (inv_le_inv₀ hdetPos (inv_pos.mpr lossPos)).2
        hdetLower
    simpa using hinverseOrder
  have hENN :
      ENNReal.ofReal
          |LinearMap.det
            (coordinateChange.symm.linear :
              Point3 →ₗ[ℝ] Point3)| ≤
        ENNReal.ofReal loss :=
    ENNReal.ofReal_mono hinverse
  exact
    mul_le_mul_right' hENN (volume targetSet)

/-- Generic CWA transport from one actual-John body family into one caller
literal chart, with the exact scale-ratio loss exposed. -/
theorem
    wz2PaperBodyConvexWolffBound_of_actualJohnToCallerLiteral
    {actual caller : ℝ}
    (hactual : 0 < actual)
    (hcaller : 0 < caller)
    (actualParent : Kakeya.DeltaTube actual)
    (callerAnchor : Kakeya.DeltaTube caller)
    (actualJohn :
      WZ2PaperAssouadUnitRescalingData actualParent)
    {source target : Kakeya.Streamlined.BodyFamily}
    {C : ENNReal}
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (carrierContainment :
      ∀ targetIndex,
        wz2PaperActualJohnToCallerLiteralCoordinateChange
              callerAnchor hcaller actualJohn ''
            (source.body (indexEquiv targetIndex)).carrier ⊆
          (target.body targetIndex).carrier)
    (sourceCWA :
      WZ2PaperBodyConvexWolffBound source C) :
    WZ2PaperBodyConvexWolffBound target
      (ENNReal.ofReal
          (4000000 * (caller / actual) ^ 2) * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_affineTransport
      (wz2PaperActualJohnToCallerLiteralCoordinateChange
        callerAnchor hcaller actualJohn)
      indexEquiv carrierContainment
  · intro targetSet
    exact
      wz2PaperActualJohnToCallerLiteralCoordinateChange_inverse_volume
        hactual hcaller actualParent callerAnchor actualJohn targetSet
  · exact sourceCWA

end Kakeya.Assouad

end
