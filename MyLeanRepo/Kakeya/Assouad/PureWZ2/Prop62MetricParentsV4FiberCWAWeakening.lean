import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal

/-!
# Proposition 6.2 V4 metric-fiber CWA weakening

This module enlarges the exact constant in a frozen rescaled metric-fiber
certificate.  The underlying fiber, parent, literal rescaling, and fixed
`4000000` rescaling certificate are reconstructed from the same geometric
input; only the allowed CWA constants are weakened.
-/

noncomputable section

namespace Kakeya.Assouad

namespace Prop62PaperAudit.V4

namespace RescaledMetricFiberCWAData

/--
Enlarge the exact frozen fiber-CWA constant without changing the metric
parent or its physical fiber.

The source constant is reset canonically to `secondConstant / 81000000`, so
the output record retains the exact identity
`secondConstant = 81000000 * sourceConstant`.
-/
noncomputable def weakenConstant
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {rho_pos : 0 < rho}
    {firstConstant secondConstant : ENNReal}
    (data :
      RescaledMetricFiberCWAData
        cover parent rho_pos firstConstant)
    (constantLe : firstConstant ≤ secondConstant)
    (secondFinite : WZ2PaperFiniteErrorConstant secondConstant) :
    RescaledMetricFiberCWAData
      cover parent rho_pos secondConstant := by
  let sourceConstant : ENNReal := secondConstant / 81000000
  have sourceConstantFinite :
      WZ2PaperFiniteErrorConstant sourceConstant := by
    constructor
    · apply
        (ENNReal.le_div_iff_mul_le
          (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
      calc
        (1 : ENNReal) * 81000000 = 81000000 := by simp
        _ ≤ 81000000 * data.sourceConstant := by
          simpa only [mul_one] using
            mul_le_mul_left'
              data.rescalingInput.source_constant_finite.1 81000000
        _ = firstConstant := data.constant_eq.symm
        _ ≤ secondConstant := constantLe
    · exact ENNReal.div_ne_top secondFinite.2 (by norm_num)
  have sourceConstantLe :
      data.sourceConstant ≤ sourceConstant := by
    apply
      (ENNReal.le_div_iff_mul_le
        (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    calc
      data.sourceConstant * 81000000 =
          81000000 * data.sourceConstant := by ring
      _ = firstConstant := data.constant_eq.symm
      _ ≤ secondConstant := constantLe
  let input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant :=
    data.rescalingInput.mono sourceConstantLe sourceConstantFinite
  have constantEq :
      secondConstant =
        (81000000 : ENNReal) * sourceConstant := by
    exact (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
  exact
    {
      sourceConstant := sourceConstant
      rescalingInput := input
      familyData := input.literal
      familyData_eq := rfl
      rescalingCertificate := input.certificate
      rescalingCertificate_eq := HEq.rfl
      constant_eq := constantEq
      cwa := constantEq ▸ input.publicPureCWA
    }

@[simp] theorem weakenConstant_sourceConstant
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {rho_pos : 0 < rho}
    {firstConstant secondConstant : ENNReal}
    (data :
      RescaledMetricFiberCWAData
        cover parent rho_pos firstConstant)
    (constantLe : firstConstant ≤ secondConstant)
    (secondFinite : WZ2PaperFiniteErrorConstant secondConstant) :
    (data.weakenConstant constantLe secondFinite).sourceConstant =
      secondConstant / 81000000 :=
  rfl

end RescaledMetricFiberCWAData

end Prop62PaperAudit.V4

end Kakeya.Assouad

end
