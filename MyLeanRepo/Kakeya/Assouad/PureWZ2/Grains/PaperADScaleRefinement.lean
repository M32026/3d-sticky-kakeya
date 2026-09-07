import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement

/-!
# Refining the minimum scale in paper AD bounds

The closed WZ1 scale-refinement theorem is stated for the internal bounded
predicate `IsADSet1`.  Local grain outputs use the literal paper predicate
`PureWZ2PaperADSet1`.  For the bounded scalar projections arising from paper
tubes, the two proved bridge directions convert the WZ1 refinement into a
paper-level theorem with an explicit finite constant.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

/-- Increasing the minimum scale in the paper AD predicate is free. -/
lemma paper_ad_coarsen_minimum_scale
    {E : Set ℝ} {fineScale coarseScale alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 E fineScale alpha C)
    (hcoarse : fineScale ≤ coarseScale) :
    PureWZ2PaperADSet1 E coarseScale alpha C := by
  rcases hAD with ⟨hfine, halpha, halphaOne, hC, hCtop, hcover⟩
  refine ⟨hfine.trans_le hcoarse, halpha, halphaOne, hC, hCtop, ?_⟩
  intro rho hrho hcoarseRho left length hrhoLength
  exact hcover rho hrho (hcoarse.trans hcoarseRho) left length hrhoLength

/-- Refine a paper AD bound from minimum scale `coarseScale` to a smaller
positive scale `fineScale`.  The explicit factor is the composition of the
two paper/internal bridge constants with the WZ1 covering refinement. -/
lemma paper_ad_weaken_minimum_scale
    {E : Set ℝ}
    {coarseScale fineScale alpha : ℝ}
    {C : ENNReal}
    (hbounded : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hAD : PureWZ2PaperADSet1 E coarseScale alpha C)
    (hfine : 0 < fineScale)
    (hscale : fineScale ≤ coarseScale)
    (hcoarseOne : coarseScale ≤ 1) :
    PureWZ2PaperADSet1 E fineScale alpha
      (10 * ((10 * C) *
        ENNReal.ofReal (10 * coarseScale / fineScale))) := by
  have hinternal :
      IsADSet1 E coarseScale alpha (10 * C) :=
    pure_wz2_paper_ad_bridge.1 E coarseScale alpha C hbounded hAD
  have hrefined :
      IsADSet1 E fineScale alpha
        ((10 * C) * ENNReal.ofReal
          (10 * coarseScale / fineScale)) :=
    hinternal.weaken_scale hfine hscale hcoarseOne
  have hconstantTop :
      (10 * C) * ENNReal.ofReal
          (10 * coarseScale / fineScale) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hAD.2.2.2.2.1)
      ENNReal.ofReal_ne_top
  exact pure_wz2_paper_ad_bridge.2 E fineScale alpha
    ((10 * C) * ENNReal.ofReal
      (10 * coarseScale / fineScale))
    hfine (hscale.trans hcoarseOne) hconstantTop hrefined

/-- Absorb the explicit refinement cost into a caller-supplied finite target
constant. -/
lemma paper_ad_weaken_minimum_scale_absorb
    {E : Set ℝ}
    {coarseScale fineScale alpha : ℝ}
    {sourceConstant targetConstant : ENNReal}
    (hbounded : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hAD : PureWZ2PaperADSet1
      E coarseScale alpha sourceConstant)
    (hfine : 0 < fineScale)
    (hscale : fineScale ≤ coarseScale)
    (hcoarseOne : coarseScale ≤ 1)
    (hcost :
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * coarseScale / fineScale)) ≤
        targetConstant)
    (htargetTop : targetConstant ≠ ⊤) :
    PureWZ2PaperADSet1 E fineScale alpha targetConstant := by
  exact PureWZ2PaperADSet1.mono_const
    (paper_ad_weaken_minimum_scale hbounded hAD hfine hscale hcoarseOne)
    hcost htargetTop

/-- A critical-scale local AD estimate controls every smaller positive query
scale on the same shading.  Both the localization ball and the scalar
projection set shrink; the minimum AD scale is then refined explicitly. -/
lemma local_projection_ad_below_critical_scale
    {shadingSet : Set Point3}
    {plane q : Point3}
    {criticalScale queryScale alpha : ℝ}
    {C : ENNReal}
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (hqueryPos : 0 < queryScale)
    (hquery : queryScale ≤ criticalScale)
    (hbounded :
      scalarProjection plane
          (shadingSet ∩
            Metric.closedBall q (Real.sqrt criticalScale)) ⊆
        Set.Icc (-4 : ℝ) 4)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection plane
        (shadingSet ∩
          Metric.closedBall q (Real.sqrt criticalScale)))
      criticalScale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection plane
        (shadingSet ∩
          Metric.closedBall q (Real.sqrt queryScale)))
      queryScale alpha
      (10 * ((10 * C) *
        ENNReal.ofReal (10 * criticalScale / queryScale))) := by
  let criticalSet := scalarProjection plane
    (shadingSet ∩ Metric.closedBall q (Real.sqrt criticalScale))
  let querySet := scalarProjection plane
    (shadingSet ∩ Metric.closedBall q (Real.sqrt queryScale))
  have hsqrt : Real.sqrt queryScale ≤ Real.sqrt criticalScale :=
    Real.sqrt_le_sqrt hquery
  have hquerySubset : querySet ⊆ criticalSet := by
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨hpoint.1, hpoint.2.trans hsqrt⟩, rfl⟩
  have hcriticalRefined : PureWZ2PaperADSet1 querySet
      criticalScale alpha C :=
    PureWZ2PaperADSet1.mono_set hAD hquerySubset
  exact paper_ad_weaken_minimum_scale
    (fun value hvalue => hbounded (hquerySubset hvalue))
    hcriticalRefined hqueryPos hquery hcriticalOne

/-- Absorbed-constant form of `local_projection_ad_below_critical_scale`. -/
lemma local_projection_ad_below_critical_scale_absorb
    {shadingSet : Set Point3}
    {plane q : Point3}
    {criticalScale queryScale alpha : ℝ}
    {sourceConstant targetConstant : ENNReal}
    (hcriticalPos : 0 < criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (hqueryPos : 0 < queryScale)
    (hquery : queryScale ≤ criticalScale)
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
    (hcost :
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / queryScale)) ≤
        targetConstant)
    (htargetTop : targetConstant ≠ ⊤) :
    PureWZ2PaperADSet1
      (scalarProjection plane
        (shadingSet ∩
          Metric.closedBall q (Real.sqrt queryScale)))
      queryScale alpha targetConstant := by
  exact PureWZ2PaperADSet1.mono_const
    (local_projection_ad_below_critical_scale
      hcriticalPos hcriticalOne hqueryPos hquery hbounded hAD)
    hcost htargetTop

end Kakeya.Assouad.PureWZ2

end
