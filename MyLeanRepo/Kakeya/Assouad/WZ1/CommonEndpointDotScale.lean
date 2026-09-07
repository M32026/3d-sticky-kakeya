import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointAffineNormalization

/-!
# Quantitative dot scale of the common-endpoint normalization
-/

namespace Kakeya.Assouad

noncomputable section

/-- The two normalization similarities cost at most two inverse threshold factors. -/
theorem WZ1CommonEndpointAffineNormalization.dotScale_upper
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall}
    {raw : WZ1CommonEndpointRawLocalization ready}
    (affine : WZ1CommonEndpointAffineNormalization raw) :
    affine.dotScale ≤ 2 * raw.threshold⁻¹ ^ 2 := by
  have ht : 0 < raw.threshold := by
    rw [raw.threshold_eq]
    exact Real.rpow_pos_of_pos ready.deltaGraph_pos _
  have hg : 0 < raw.gridScale := by
    rw [raw.gridScale_eq]
    exact Real.rpow_pos_of_pos ready.deltaGraph_pos _
  have hF : raw.threshold ≤ dist affine.anchor.1 0 :=
    raw.localized.first_far affine.anchor affine.anchor_mem
  have hG : raw.threshold ≤ dist affine.anchor.2.1 affine.anchor.2.2 :=
    raw.localized.endpoints_far affine.anchor affine.anchor_mem
  have hdenomF : 0 < dist affine.anchor.1 0 + 2 * raw.gridScale := by
    positivity
  have hdenomG :
      0 < dist affine.anchor.2.1 affine.anchor.2.2 / 2 +
        2 * raw.gridScale := by
    positivity
  have hscaleF : affine.scaleF ≤ raw.threshold⁻¹ := by
    rw [affine.scaleF_eq]
    simpa [one_div] using one_div_le_one_div_of_le ht
      (show raw.threshold ≤ dist affine.anchor.1 0 +
          2 * raw.gridScale by linarith)
  have hscaleG : affine.scaleG ≤ 2 * raw.threshold⁻¹ := by
    rw [affine.scaleG_eq]
    have htHalf : 0 < raw.threshold / 2 := by positivity
    have hraw :
        (dist affine.anchor.2.1 affine.anchor.2.2 / 2 +
          2 * raw.gridScale)⁻¹ ≤ (raw.threshold / 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le htHalf
        (show raw.threshold / 2 ≤
            dist affine.anchor.2.1 affine.anchor.2.2 / 2 +
              2 * raw.gridScale by linarith)
    calc
      (dist affine.anchor.2.1 affine.anchor.2.2 / 2 +
          2 * raw.gridScale)⁻¹ ≤ (raw.threshold / 2)⁻¹ := hraw
      _ = 2 * raw.threshold⁻¹ := by field_simp [ht.ne']
  rw [affine.dotScale_eq]
  calc
    affine.scaleF * affine.scaleG ≤
        raw.threshold⁻¹ * (2 * raw.threshold⁻¹) := by
      exact mul_le_mul hscaleF hscaleG affine.scaleG_pos.le
        (inv_nonneg.mpr ht.le)
    _ = 2 * raw.threshold⁻¹ ^ 2 := by ring

end

end Kakeya.Assouad
