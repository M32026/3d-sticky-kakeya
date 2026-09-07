import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADScaleRefinement
import Mathlib.Tactic

/-!
# Explicit loss-gap absorption for the aligned HIGH argument

The critical-scale Córdoba estimate is first refined to the requested scale
at paper level and is then bridged back to the internal AD predicate.  If the
critical scale is less than four times the requested scale, the complete cost
is at most `40000` times the critical-scale constant.  A strict loss gap
absorbs this fixed factor at an explicit sufficiently small fine scale.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open ENNReal

/-- The exact cost of paper scale refinement followed by the paper-to-internal
bridge is bounded by `40000`.  The four factors of ten are, respectively, the
final bridge, the two bridges surrounding WZ1 scale refinement, and the WZ1
covering factor inside `ofReal`. -/
lemma paper_refinement_internal_cost_le_forty_thousand
    {criticalScale queryScale : ℝ} {C : ENNReal}
    (hquery : 0 < queryScale)
    (hratio : criticalScale < 4 * queryScale) :
    10 * (10 * ((10 * C) *
        ENNReal.ofReal (10 * criticalScale / queryScale))) ≤
      40000 * C := by
  have hratio' : 10 * criticalScale / queryScale ≤ 40 := by
    apply (div_le_iff₀ hquery).2
    linarith
  have hofReal :
      ENNReal.ofReal (10 * criticalScale / queryScale) ≤ 40 := by
    simpa using ENNReal.ofReal_le_ofReal hratio'
  calc
    10 * (10 * ((10 * C) *
        ENNReal.ofReal (10 * criticalScale / queryScale)))
        ≤ 10 * (10 * ((10 * C) * 40)) := by gcongr
    _ = 40000 * C := by ring

/-- A strict loss gap absorbs a fixed positive real factor.  The threshold is
the literal solution of `factor * delta^(targetLoss-sourceLoss) ≤ 1`; no
asymptotic notation or hidden constant is used. -/
lemma realRpowENN_neg_loss_gap_absorb
    {factor delta sourceLoss targetLoss : ℝ}
    (hfactor : 0 < factor)
    (hgap : sourceLoss < targetLoss)
    (hdelta : 0 < delta)
    (hsmall :
      delta ≤ Real.rpow factor (-1 / (targetLoss - sourceLoss))) :
    ENNReal.ofReal factor * Kakeya.realRpowENN delta (-sourceLoss) ≤
      Kakeya.realRpowENN delta (-targetLoss) := by
  let gap : ℝ := targetLoss - sourceLoss
  have hgap_pos : 0 < gap := by
    dsimp only [gap]
    linarith
  let threshold : ℝ := Real.rpow factor (-1 / gap)
  have hthreshold_pos : 0 < threshold :=
    Real.rpow_pos_of_pos hfactor _
  have hpow_le : Real.rpow delta gap ≤ Real.rpow threshold gap :=
    Real.rpow_le_rpow hdelta.le
      (by simpa only [threshold, gap] using hsmall) hgap_pos.le
  have hthreshold_pow : Real.rpow threshold gap = factor⁻¹ := by
    dsimp only [threshold]
    have hexponent : (-1 / gap) * gap = -1 := by
      field_simp [hgap_pos.ne']
    calc
      Real.rpow (Real.rpow factor (-1 / gap)) gap =
          Real.rpow factor ((-1 / gap) * gap) :=
        (Real.rpow_mul hfactor.le (-1 / gap) gap).symm
      _ = Real.rpow factor (-1 : ℝ) := by rw [hexponent]
      _ = factor⁻¹ := by
        simpa [Real.rpow_neg hfactor.le] using rfl
  have hpow_le_inv : Real.rpow delta gap ≤ factor⁻¹ := by
    simpa only [hthreshold_pow] using hpow_le
  have hfactor_pow : factor * Real.rpow delta gap ≤ 1 := by
    calc
      factor * Real.rpow delta gap ≤ factor * factor⁻¹ := by
        exact mul_le_mul_of_nonneg_left hpow_le_inv hfactor.le
      _ = 1 := by exact mul_inv_cancel₀ hfactor.ne'
  have hneg_gap : factor ≤ Real.rpow delta (-gap) := by
    have hneg : Real.rpow delta (-gap) = (Real.rpow delta gap)⁻¹ :=
      Real.rpow_neg hdelta.le gap
    rw [hneg]
    exact (le_inv_comm₀ hfactor
      (Real.rpow_pos_of_pos hdelta gap)).2 hpow_le_inv
  have hreal :
      factor * Real.rpow delta (-sourceLoss) ≤
        Real.rpow delta (-targetLoss) := by
    have hsplit :
        Real.rpow delta (-targetLoss) =
          Real.rpow delta (-sourceLoss) * Real.rpow delta (-gap) := by
      have hadd := Real.rpow_add hdelta (-sourceLoss) (-gap)
      have hexponent : -sourceLoss + -gap = -targetLoss := by
        dsimp only [gap]
        ring
      rw [hexponent] at hadd
      exact hadd
    rw [hsplit]
    calc
      factor * Real.rpow delta (-sourceLoss) =
          Real.rpow delta (-sourceLoss) * factor := by ring
      _ ≤ Real.rpow delta (-sourceLoss) * Real.rpow delta (-gap) := by
        exact mul_le_mul_of_nonneg_left hneg_gap
          (Real.rpow_nonneg hdelta.le _)
  simpa only [Kakeya.realRpowENN, ← ENNReal.ofReal_mul hfactor.le] using
    ENNReal.ofReal_le_ofReal hreal

/-- Specialized form used by the aligned critical-scale HIGH chain. -/
lemma forty_thousand_mul_neg_loss_absorb
    {delta sourceLoss targetLoss : ℝ}
    (hgap : sourceLoss < targetLoss)
    (hdelta : 0 < delta)
    (hsmall :
      delta ≤ Real.rpow (40000 : ℝ)
        (-1 / (targetLoss - sourceLoss))) :
    (40000 : ENNReal) * Kakeya.realRpowENN delta (-sourceLoss) ≤
      Kakeya.realRpowENN delta (-targetLoss) := by
  simpa using realRpowENN_neg_loss_gap_absorb
    (factor := (40000 : ℝ)) (delta := delta)
    (sourceLoss := sourceLoss) (targetLoss := targetLoss)
    (by norm_num) hgap hdelta hsmall

/-- Refine a critical-scale paper AD estimate across an aligned factor-four
scale gap while exposing exactly the paper constant expected by the final
paper-to-internal bridge. -/
lemma aligned_critical_paper_ad_with_internal_budget
    {shadingSet : Set Point3}
    {plane q : Point3}
    {criticalScale queryScale alpha : ℝ}
    {sourceConstant targetInternalConstant : ENNReal}
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (hqueryPos : 0 < queryScale)
    (hquery : queryScale ≤ criticalScale)
    (hratio : criticalScale < 4 * queryScale)
    (hbounded :
      scalarProjection plane
          (shadingSet ∩
            Metric.closedBall q (Real.sqrt criticalScale)) ⊆
        Set.Icc (-4 : ℝ) 4)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection plane
        (shadingSet ∩
          Metric.closedBall q (Real.sqrt criticalScale)))
      criticalScale alpha sourceConstant)
    (hcost : 40000 * sourceConstant ≤ targetInternalConstant) :
    ∃ paperConstant : ENNReal,
      PureWZ2PaperADSet1
        (scalarProjection plane
          (shadingSet ∩
            Metric.closedBall q (Real.sqrt queryScale)))
        queryScale alpha paperConstant ∧
      10 * paperConstant ≤ targetInternalConstant := by
  let paperConstant : ENNReal :=
    10 * ((10 * sourceConstant) *
      ENNReal.ofReal (10 * criticalScale / queryScale))
  refine ⟨paperConstant, ?_, ?_⟩
  · exact local_projection_ad_below_critical_scale
      hcriticalPos hcriticalOne hqueryPos hquery hbounded hAD
  · exact (paper_refinement_internal_cost_le_forty_thousand
      hqueryPos hratio).trans hcost

/-- Loss-gap specialization of
`aligned_critical_paper_ad_with_internal_budget`. -/
lemma aligned_critical_paper_ad_of_loss_gap
    {shadingSet : Set Point3}
    {plane q : Point3}
    {criticalScale queryScale alpha delta sourceLoss targetLoss : ℝ}
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (hqueryPos : 0 < queryScale)
    (hquery : queryScale ≤ criticalScale)
    (hratio : criticalScale < 4 * queryScale)
    (hbounded :
      scalarProjection plane
          (shadingSet ∩
            Metric.closedBall q (Real.sqrt criticalScale)) ⊆
        Set.Icc (-4 : ℝ) 4)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection plane
        (shadingSet ∩
          Metric.closedBall q (Real.sqrt criticalScale)))
      criticalScale alpha
      (Kakeya.realRpowENN delta (-sourceLoss)))
    (hgap : sourceLoss < targetLoss)
    (hdelta : 0 < delta)
    (hsmall :
      delta ≤ Real.rpow (40000 : ℝ)
        (-1 / (targetLoss - sourceLoss))) :
    ∃ paperConstant : ENNReal,
      PureWZ2PaperADSet1
        (scalarProjection plane
          (shadingSet ∩
            Metric.closedBall q (Real.sqrt queryScale)))
        queryScale alpha paperConstant ∧
      10 * paperConstant ≤
        Kakeya.realRpowENN delta (-targetLoss) := by
  exact aligned_critical_paper_ad_with_internal_budget
    hcriticalPos hcriticalOne hqueryPos hquery hratio hbounded hAD
    (forty_thousand_mul_neg_loss_absorb hgap hdelta hsmall)

end Kakeya.Assouad.PureWZ2

end
