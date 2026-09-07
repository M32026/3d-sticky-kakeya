import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialRebalancing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MetricFiberMassAverage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainRestriction

/-!
# Metric-fibre input for Proposition 6.3

Choose one complete parent fibre directly from the initial finite-planiness
refinement.  The record keeps the original frozen Node 3 rescaling
certificate, a per-tube density lower bound on the selected complete fibre,
and the local grains restricted to that exact selected fibre.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

def proposition63MetricFiberIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  wz2PaperFullFiberIndices fine coarse parent

def proposition63MetricFiberFamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) : Kakeya.Streamlined.TubeSubfamily fine :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset fine
    (proposition63MetricFiberIndices parent)

def proposition63MetricSourceFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (fineShading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) : WZ1PaperTubeShading
      (proposition63MetricFiberFamily
        (fine := fine) (coarse := coarse) parent).family :=
  restrictPaperShading
    (proposition63MetricFiberFamily
      (fine := fine) (coarse := coarse) parent) fineShading

def proposition63MetricSelectedFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (selected : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) : WZ1PaperTubeShading
      (proposition63MetricFiberFamily
        (fine := fine) (coarse := coarse) parent).family :=
  restrictPaperShading
    (proposition63MetricFiberFamily
      (fine := fine) (coarse := coarse) parent) selected

/-- One selected complete metric fibre aligned with the frozen rescaling
certificate and the initial local-grain data. -/
structure Proposition63MetricFiberInputData
    {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    (rebalanced : Proposition63InitialRebalancedData
      original initial hdelta)
    (hrho : 0 < rho) where
  parent : Fin coarse.card
  sourceDensity : ENNReal
  ambient_density :
    sourceDensity * fine.enncard *
        Kakeya.realRpowENN delta 2 ≤
      rebalanced.shading.mass
  selected_density :
    sourceDensity *
        ((proposition63MetricFiberIndices
          (fine := fine) (coarse := coarse) parent).card : ENNReal) *
        Kakeya.realRpowENN delta 2 ≤
      (proposition63MetricSelectedFiber
        (coarse := coarse)
        rebalanced.shading parent).mass
  ambient_mass_retained :
    rebalanced.shading.mass ≤
      coarse.enncard *
        (proposition63MetricSelectedFiber
          (coarse := coarse)
          rebalanced.shading parent).mass
  source_subshading : PaperIsSubshading
    (proposition63MetricSelectedFiber
      (coarse := coarse)
      rebalanced.shading parent)
    (proposition63MetricSourceFiber
      (coarse := coarse) fineShading parent)
  frozenRescaled : WZ2PaperPureRescaledFullFiberOutput
    (sigma := sigma) (loss := stickyLoss)
    (proposition63MetricSourceFiber
      (coarse := coarse) fineShading parent)
    (coarse.tube parent) hrho
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := initial.incidence)
    (proposition63MetricSelectedFiber
      (coarse := coarse)
      rebalanced.shading parent) sigma
    (Kakeya.realRpowENN delta (-localLoss))
    (Real.toNNReal coefficient)

namespace Proposition63MetricFiberInputData

def fiberIndices {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) :
    Finset (Fin fine.card) :=
  proposition63MetricFiberIndices
    (fine := fine) (coarse := coarse) input.parent

def fiberFamily {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  proposition63MetricFiberFamily
    (fine := fine) (coarse := coarse) input.parent

def sourceFiber {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) :
    WZ1PaperTubeShading
      (proposition63MetricFiberFamily
        (fine := fine) (coarse := coarse) input.parent).family :=
  proposition63MetricSourceFiber
    (coarse := coarse) fineShading input.parent

def selectedFiber {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) :
    WZ1PaperTubeShading
      (proposition63MetricFiberFamily
        (fine := fine) (coarse := coarse) input.parent).family :=
  proposition63MetricSelectedFiber
    (coarse := coarse)
    rebalanced.shading input.parent

end Proposition63MetricFiberInputData

/-- Select a mass-maximal complete metric fibre on the actual initial
finite-planiness refinement.  The same parent retains a `1 / #coarse`
fraction of the ambient shaded mass and has the corresponding per-tube
density.  Keeping both conclusions is what lets the later proof inherit the
ambient top-level CWA without changing the selected fibre. -/
theorem proposition63_metric_fiber_input_with_witness
    {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (stickyRescaled : ∀ parent : Fin coarse.card,
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := stickyLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse parent))
          fineShading)
        (coarse.tube parent) hrho)
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    (rebalanced : Proposition63InitialRebalancedData
      original initial hdelta)
    (sourceDensity : ENNReal)
    (hsourceDensity : sourceDensity * fine.enncard *
      Kakeya.realRpowENN delta 2 ≤
        rebalanced.shading.mass)
    (hcoarseNonempty : coarse.Nonempty) :
    ∃ input : Proposition63MetricFiberInputData
        (stickyLoss := stickyLoss) rebalanced hrho,
      input.frozenRescaled = stickyRescaled input.parent := by
  rcases exists_metric_fiber_density_and_retained_average cover
      rebalanced.shading hcoarseNonempty sourceDensity
      (Kakeya.realRpowENN delta 2) hsourceDensity with
    ⟨parent, hretained, hdensity⟩
  let fiberIndices := wz2PaperFullFiberIndices fine coarse parent
  let fiberFamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine fiberIndices
  let sourceFiber := restrictPaperShading fiberFamily fineShading
  let selectedFiber := restrictPaperShading fiberFamily
    rebalanced.shading
  have hsubAmbient : PaperIsSubshading
      rebalanced.shading fineShading :=
    rebalanced.subshading
  have hsubFiber : PaperIsSubshading selectedFiber sourceFiber := by
    intro index point hpoint
    exact hsubAmbient (fiberFamily.embedding index) hpoint
  have hunion : selectedFiber.union ⊆ rebalanced.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨fiberFamily.embedding index, hpoint⟩
  let localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := initial.incidence) selectedFiber sigma
      (Kakeya.realRpowENN delta (-localLoss))
      (Real.toNNReal coefficient) :=
    { planeMap := fun point => rebalanced.localGrains.planeMap
        ⟨point, hunion point.prop⟩
      planeMap_lipschitz := by
        intro first second
        exact rebalanced.localGrains.planeMap_lipschitz
          ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
      planeMap_unit := fun point =>
        rebalanced.localGrains.planeMap_unit ⟨point, hunion point.prop⟩
      planeMap_incidence := by
        intro index point hpoint
        have hraw := rebalanced.localGrains.planeMap_incidence
          (fiberFamily.embedding index) point hpoint
        simpa only [fiberFamily.tube_eq] using hraw
      local_ad := by
        intro queryScale hdeltaQuery hqueryOne point
        apply (rebalanced.localGrains.local_ad queryScale hdeltaQuery
          hqueryOne ⟨point, hunion point.prop⟩).mono_set
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩ }
  let frozenRescaled := stickyRescaled parent
  have hselectedDensity :
      (coarse.enncard⁻¹ * sourceDensity) *
          ((proposition63MetricFiberIndices
            (fine := fine) (coarse := coarse) parent).card : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤ selectedFiber.mass := by
    change (coarse.enncard⁻¹ * sourceDensity) *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading fiberFamily
          rebalanced.shading).mass
    rw [completeFiberShading_mass_eq_fiberShadedMass cover
      rebalanced.shading parent]
    exact hdensity
  have hcoarseOne : 1 ≤ coarse.enncard := by
    change (1 : ENNReal) ≤ (coarse.card : ENNReal)
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcoarseNonempty.ne')
  have hcoarseInv : coarse.enncard⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.mpr hcoarseOne
  have hambientDensity :
      (coarse.enncard⁻¹ * sourceDensity) * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤ rebalanced.shading.mass := by
    have hweighted : coarse.enncard⁻¹ * sourceDensity ≤ sourceDensity := by
      calc
        coarse.enncard⁻¹ * sourceDensity ≤
            1 * sourceDensity := by gcongr
        _ = sourceDensity := one_mul _
    calc
      (coarse.enncard⁻¹ * sourceDensity) * fine.enncard *
            Kakeya.realRpowENN delta 2 ≤
          sourceDensity * fine.enncard *
            Kakeya.realRpowENN delta 2 := by
        exact mul_le_mul_right'
          (mul_le_mul_right' hweighted fine.enncard)
          (Kakeya.realRpowENN delta 2)
      _ ≤ rebalanced.shading.mass := hsourceDensity
  have hambientMassRetained :
      rebalanced.shading.mass ≤
        coarse.enncard * selectedFiber.mass := by
    rw [completeFiberShading_mass_eq_fiberShadedMass cover
      rebalanced.shading parent]
    exact hretained
  let result : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho := {
    parent := parent
    sourceDensity := coarse.enncard⁻¹ * sourceDensity
    ambient_density := hambientDensity
    selected_density := hselectedDensity
    ambient_mass_retained := hambientMassRetained
    source_subshading := hsubFiber
    frozenRescaled := frozenRescaled
    localGrains := localGrains
  }
  exact ⟨result, rfl⟩

/-- Compatibility wrapper for callers that only retain existential rescaled
fibres. -/
theorem proposition63_metric_fiber_input
    {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (stickyRescaled : ∀ parent : Fin coarse.card,
      Nonempty (WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := stickyLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse parent))
          fineShading)
        (coarse.tube parent) hrho))
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    (rebalanced : Proposition63InitialRebalancedData
      original initial hdelta)
    (sourceDensity : ENNReal)
    (hsourceDensity : sourceDensity * fine.enncard *
      Kakeya.realRpowENN delta 2 ≤ rebalanced.shading.mass)
    (hcoarseNonempty : coarse.Nonempty) :
    Nonempty (Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) := by
  let selectedOutput : ∀ parent : Fin coarse.card,
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := stickyLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse parent))
          fineShading)
        (coarse.tube parent) hrho :=
    fun parent => Classical.choice (stickyRescaled parent)
  rcases proposition63_metric_fiber_input_with_witness selectedOutput
      rebalanced sourceDensity hsourceDensity hcoarseNonempty with
    ⟨input, _⟩
  exact ⟨input⟩

/-- Select the same mass-maximal fibre while transporting unit-ball support
attached to the caller's chosen rescaling witness. -/
theorem proposition63_metric_fiber_input_with_unit_ball
    {delta rho sigma stickyLoss localLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    (stickyRescaled : ∀ parent : Fin coarse.card,
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := stickyLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
            (wz2PaperFullFiberIndices fine coarse parent))
          fineShading)
        (coarse.tube parent) hrho)
    (stickyUnitBall : ∀ parent,
      (stickyRescaled parent).rescalingCertificate.publicFamily.IsInUnitBall)
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    (rebalanced : Proposition63InitialRebalancedData
      original initial hdelta)
    (sourceDensity : ENNReal)
    (hsourceDensity : sourceDensity * fine.enncard *
      Kakeya.realRpowENN delta 2 ≤ rebalanced.shading.mass)
    (hcoarseNonempty : coarse.Nonempty) :
    ∃ input : Proposition63MetricFiberInputData
        (stickyLoss := stickyLoss) rebalanced hrho,
      input.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall := by
  rcases proposition63_metric_fiber_input_with_witness stickyRescaled
      rebalanced sourceDensity hsourceDensity hcoarseNonempty with
    ⟨input, input_eq⟩
  refine ⟨input, ?_⟩
  rw [input_eq]
  exact stickyUnitBall input.parent

end Kakeya.Assouad.PureWZ2

end
