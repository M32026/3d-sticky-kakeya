import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Joint finite iteration of plane-map variation and local AD

The plane-map and local-AD refinements cannot be selected independently: two
large independent subshadings may have empty intersection.  This module
isolates the paper-faithful interface.  At every scale one common spatial
restriction of the current shading must simultaneously preserve point
multiplicity, control plane-map variation, and establish the local AD bound.

Once such a one-scale producer is supplied, all nesting and mass bookkeeping
is formal.  Previous variation and AD estimates survive later steps by
subshading monotonicity.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Iterate a genuinely joint one-scale producer over a finite schedule. -/
theorem joint_finite_variation_local_ad_iteration
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading F)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (planeMap : Point3 → Point3)
    (N : ℕ)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (step : ∀ index : ℕ, index < N →
      ∀ current : WZ1PaperTubeShading F,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union,
          current.pointMultiplicity point = source.pointMultiplicity point) →
        ∃ next : WZ1PaperTubeShading F,
          PaperIsSubshading next current ∧
          WZ1PaperIsCubicalShading next ∧
          (∀ point ∈ next.union,
            next.pointMultiplicity point = current.pointMultiplicity point) ∧
          (∀ first ∈ next.union, ∀ second ∈ next.union,
            dist first second ≤ spatialScale index →
              dist (planeMap first) (planeMap second) ≤
                variationScale index) ∧
          (∀ point ∈ next.union,
            IsADSet1
              (scalarProjection (planeMap point)
                (next.union ∩ Metric.closedBall point
                  (Real.sqrt (localScale index))))
              (localScale index) (1 - sigma) constant) ∧
          leftFactor index * current.mass ≤
            rightFactor index * next.mass) :
    ∃ final : WZ1PaperTubeShading F,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ index, index < N →
        ∀ first ∈ final.union, ∀ second ∈ final.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass := by
  let P : ℕ → Prop := fun completed =>
    ∃ current : WZ1PaperTubeShading F,
      PaperIsSubshading current source ∧
      WZ1PaperIsCubicalShading current ∧
      (∀ point ∈ current.union,
        current.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ index, index < completed → index < N →
        ∀ first ∈ current.union, ∀ second ∈ current.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index) ∧
      (∀ index, index < completed → index < N →
        ∀ point ∈ current.union,
          IsADSet1
            (scalarProjection (planeMap point)
              (current.union ∩ Metric.closedBall point
                (Real.sqrt (localScale index))))
            (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range completed, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range completed, rightFactor index) * current.mass
  have hbase : P 0 := by
    refine ⟨source, fun _ => Set.Subset.rfl, hsourceCubical, ?_, ?_, ?_, ?_⟩
    · intro point _
      rfl
    · intro index hindex
      omega
    · intro index hindex
      omega
    · simp
  have hnext : ∀ completed, completed < N → P completed → P (completed + 1) := by
    intro completed hcompleted hP
    rcases hP with
      ⟨current, hcurrentSub, hcurrentCubical, hcurrentMultiplicity,
        hcurrentVariation, hcurrentAD, hcurrentMass⟩
    rcases step completed hcompleted current hcurrentSub hcurrentCubical
        hcurrentMultiplicity with
      ⟨next, hnextSub, hnextCubical, hnextMultiplicityCurrent,
        hnextVariation, hnextAD, hnextMass⟩
    have hnextSubSource : PaperIsSubshading next source := fun index =>
      (hnextSub index).trans (hcurrentSub index)
    have hnextMultiplicity : ∀ point ∈ next.union,
        next.pointMultiplicity point = source.pointMultiplicity point := by
      intro point hpoint
      have hpointCurrent : point ∈ current.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hnextSub index hindex⟩
      exact (hnextMultiplicityCurrent point hpoint).trans
        (hcurrentMultiplicity point hpointCurrent)
    have hvariation : ∀ index, index < completed + 1 → index < N →
        ∀ first ∈ next.union, ∀ second ∈ next.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index := by
      intro index hindex hindexN first hfirst second hsecond hdistance
      by_cases hlast : index = completed
      · subst index
        exact hnextVariation first hfirst second hsecond hdistance
      · have hindexOld : index < completed := by omega
        have hfirstCurrent : first ∈ current.union := by
          rcases hfirst with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        have hsecondCurrent : second ∈ current.union := by
          rcases hsecond with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        exact hcurrentVariation index hindexOld hindexN
          first hfirstCurrent second hsecondCurrent hdistance
    have hallAD : ∀ index, index < completed + 1 → index < N →
        ∀ point ∈ next.union,
          IsADSet1
            (scalarProjection (planeMap point)
              (next.union ∩ Metric.closedBall point
                (Real.sqrt (localScale index))))
            (localScale index) (1 - sigma) constant := by
      intro index hindex hindexN point hpoint
      by_cases hlast : index = completed
      · subst index
        exact hnextAD point hpoint
      · have hindexOld : index < completed := by omega
        have hpointCurrent : point ∈ current.union := by
          rcases hpoint with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        have hold := hcurrentAD index hindexOld hindexN point hpointCurrent
        apply hold.mono
        rintro value ⟨other, hother, rfl⟩
        have hotherCurrent : other ∈ current.union := by
          rcases hother.1 with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        exact ⟨other, ⟨hotherCurrent, hother.2⟩, rfl⟩
    have hmass :
        (∏ index ∈ Finset.range (completed + 1), leftFactor index) *
            source.mass ≤
          (∏ index ∈ Finset.range (completed + 1), rightFactor index) *
            next.mass := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ index ∈ Finset.range completed, leftFactor index) *
              leftFactor completed) * source.mass =
            leftFactor completed *
              ((∏ index ∈ Finset.range completed, leftFactor index) *
                source.mass) := by ring
        _ ≤ leftFactor completed *
              ((∏ index ∈ Finset.range completed, rightFactor index) *
                current.mass) := by gcongr
        _ = (∏ index ∈ Finset.range completed, rightFactor index) *
              (leftFactor completed * current.mass) := by ring
        _ ≤ (∏ index ∈ Finset.range completed, rightFactor index) *
              (rightFactor completed * next.mass) := by gcongr
        _ = ((∏ index ∈ Finset.range completed, rightFactor index) *
              rightFactor completed) * next.mass := by ring
    exact ⟨next, hnextSubSource, hnextCubical, hnextMultiplicity,
      hvariation, hallAD, hmass⟩
  have hinduction : ∀ completed, completed ≤ N → P completed := by
    intro completed hcompleted
    induction completed with
    | zero => exact hbase
    | succ completed ih =>
        exact hnext completed (by omega) (ih (by omega))
  rcases hinduction N le_rfl with
    ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
      hfinalVariation, hfinalAD, hfinalMass⟩
  exact ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
    (fun index hindex => hfinalVariation index hindex hindex),
    (fun index hindex => hfinalAD index hindex hindex), hfinalMass⟩

/-- Positive-mass form of the joint finite iteration.

Every paper step is applied to the actual current refinement.  Re-entry at
the next scale needs that refinement to have positive mass, so this version
records positivity as an induction invariant.  It follows from the step's
mass inequality as soon as the left factor is positive. -/
theorem joint_finite_variation_local_ad_iteration_of_mass_pos
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading F)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (hsourceMass : 0 < source.mass)
    (planeMap : Point3 → Point3)
    (N : ℕ)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (hleftFactorPos : ∀ index, index < N → 0 < leftFactor index)
    (step : ∀ index : ℕ, index < N →
      ∀ current : WZ1PaperTubeShading F,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union,
          current.pointMultiplicity point = source.pointMultiplicity point) →
        (∏ prior ∈ Finset.range index, leftFactor prior) * source.mass ≤
          (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass →
        0 < current.mass →
        ∃ next : WZ1PaperTubeShading F,
          PaperIsSubshading next current ∧
          WZ1PaperIsCubicalShading next ∧
          (∀ point ∈ next.union,
            next.pointMultiplicity point = current.pointMultiplicity point) ∧
          (∀ first ∈ next.union, ∀ second ∈ next.union,
            dist first second ≤ spatialScale index →
              dist (planeMap first) (planeMap second) ≤
                variationScale index) ∧
          (∀ point ∈ next.union,
            IsADSet1
              (scalarProjection (planeMap point)
                (next.union ∩ Metric.closedBall point
                  (Real.sqrt (localScale index))))
              (localScale index) (1 - sigma) constant) ∧
          leftFactor index * current.mass ≤
            rightFactor index * next.mass) :
    ∃ final : WZ1PaperTubeShading F,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ index, index < N →
        ∀ first ∈ final.union, ∀ second ∈ final.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  let P : ℕ → Prop := fun completed =>
    ∃ current : WZ1PaperTubeShading F,
      PaperIsSubshading current source ∧
      WZ1PaperIsCubicalShading current ∧
      (∀ point ∈ current.union,
        current.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ index, index < completed → index < N →
        ∀ first ∈ current.union, ∀ second ∈ current.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index) ∧
      (∀ index, index < completed → index < N →
        ∀ point ∈ current.union,
          IsADSet1
            (scalarProjection (planeMap point)
              (current.union ∩ Metric.closedBall point
                (Real.sqrt (localScale index))))
            (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range completed, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range completed, rightFactor index) * current.mass ∧
      0 < current.mass
  have hbase : P 0 := by
    refine ⟨source, fun _ => Set.Subset.rfl, hsourceCubical, ?_, ?_, ?_, ?_,
      hsourceMass⟩
    · intro point _
      rfl
    · intro index hindex
      omega
    · intro index hindex
      omega
    · simp
  have hnext : ∀ completed, completed < N → P completed → P (completed + 1) := by
    intro completed hcompleted hP
    rcases hP with
      ⟨current, hcurrentSub, hcurrentCubical, hcurrentMultiplicity,
        hcurrentVariation, hcurrentAD, hcurrentMassLedger, hcurrentMass⟩
    rcases step completed hcompleted current hcurrentSub hcurrentCubical
        hcurrentMultiplicity hcurrentMassLedger hcurrentMass with
      ⟨next, hnextSub, hnextCubical, hnextMultiplicityCurrent,
        hnextVariation, hnextAD, hnextMassLedger⟩
    have hnextSubSource : PaperIsSubshading next source := fun index =>
      (hnextSub index).trans (hcurrentSub index)
    have hnextMultiplicity : ∀ point ∈ next.union,
        next.pointMultiplicity point = source.pointMultiplicity point := by
      intro point hpoint
      have hpointCurrent : point ∈ current.union := by
        rcases hpoint with ⟨tube, htube⟩
        exact ⟨tube, hnextSub tube htube⟩
      exact (hnextMultiplicityCurrent point hpoint).trans
        (hcurrentMultiplicity point hpointCurrent)
    have hvariation : ∀ index, index < completed + 1 → index < N →
        ∀ first ∈ next.union, ∀ second ∈ next.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index := by
      intro index hindex hindexN first hfirst second hsecond hdistance
      by_cases hlast : index = completed
      · subst index
        exact hnextVariation first hfirst second hsecond hdistance
      · have hindexOld : index < completed := by omega
        have hfirstCurrent : first ∈ current.union := by
          rcases hfirst with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        have hsecondCurrent : second ∈ current.union := by
          rcases hsecond with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        exact hcurrentVariation index hindexOld hindexN
          first hfirstCurrent second hsecondCurrent hdistance
    have hallAD : ∀ index, index < completed + 1 → index < N →
        ∀ point ∈ next.union,
          IsADSet1
            (scalarProjection (planeMap point)
              (next.union ∩ Metric.closedBall point
                (Real.sqrt (localScale index))))
            (localScale index) (1 - sigma) constant := by
      intro index hindex hindexN point hpoint
      by_cases hlast : index = completed
      · subst index
        exact hnextAD point hpoint
      · have hindexOld : index < completed := by omega
        have hpointCurrent : point ∈ current.union := by
          rcases hpoint with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        have hold := hcurrentAD index hindexOld hindexN point hpointCurrent
        apply hold.mono
        rintro value ⟨other, hother, rfl⟩
        have hotherCurrent : other ∈ current.union := by
          rcases hother.1 with ⟨tube, htube⟩
          exact ⟨tube, hnextSub tube htube⟩
        exact ⟨other, ⟨hotherCurrent, hother.2⟩, rfl⟩
    have hmass :
        (∏ index ∈ Finset.range (completed + 1), leftFactor index) *
            source.mass ≤
          (∏ index ∈ Finset.range (completed + 1), rightFactor index) *
            next.mass := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        ((∏ index ∈ Finset.range completed, leftFactor index) *
              leftFactor completed) * source.mass =
            leftFactor completed *
              ((∏ index ∈ Finset.range completed, leftFactor index) *
                source.mass) := by ring
        _ ≤ leftFactor completed *
              ((∏ index ∈ Finset.range completed, rightFactor index) *
                current.mass) := by gcongr
        _ = (∏ index ∈ Finset.range completed, rightFactor index) *
              (leftFactor completed * current.mass) := by ring
        _ ≤ (∏ index ∈ Finset.range completed, rightFactor index) *
              (rightFactor completed * next.mass) := by gcongr
        _ = ((∏ index ∈ Finset.range completed, rightFactor index) *
              rightFactor completed) * next.mass := by ring
    have hleftCurrent : 0 < leftFactor completed * current.mass :=
      ENNReal.mul_pos (hleftFactorPos completed hcompleted).ne'
        hcurrentMass.ne'
    have hrightNext : 0 < rightFactor completed * next.mass :=
      hleftCurrent.trans_le hnextMassLedger
    have hnextMass : 0 < next.mass := by
      by_contra hnot
      have hzero : next.mass = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
      rw [hzero, mul_zero] at hrightNext
      exact (lt_irrefl 0) hrightNext
    exact ⟨next, hnextSubSource, hnextCubical, hnextMultiplicity,
      hvariation, hallAD, hmass, hnextMass⟩
  have hinduction : ∀ completed, completed ≤ N → P completed := by
    intro completed hcompleted
    induction completed with
    | zero => exact hbase
    | succ completed ih =>
        exact hnext completed (by omega) (ih (by omega))
  rcases hinduction N le_rfl with
    ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
      hfinalVariation, hfinalAD, hfinalMassLedger, hfinalMass⟩
  exact ⟨final, hfinalSub, hfinalCubical, hfinalMultiplicity,
    (fun index hindex => hfinalVariation index hindex hindex),
    (fun index hindex => hfinalAD index hindex hindex),
    hfinalMassLedger, hfinalMass⟩

end Kakeya.Assouad.PureWZ2

end
