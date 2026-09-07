import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeSelectedLocalGrain
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruning
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.IntersectionMassRetention
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17GridPruningBudget

/-!
# A non-aligned whole-cell Property-Three pullback

The distinguished scale in Proposition 6.3 is an exact power and need not be
an integral multiple of the fine scale.  Before pulling a coarse whole-cell
restriction back to the fine family, delete the fine cells crossing the
coarse grid.  Intersecting the raw pullback with this boundary-safe shading
then gives a genuine fine-cubical subshading without changing the exact
coarse scale.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- The raw Property-Three pullback restricted to boundary-safe fine cells. -/
def proposition63SafePullbackShading
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta)
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := rho.1) sticky.refined hdelta
      (stickyCoarseMultiplicityCap sticky *
        stickyFiberMultiplicityCap sticky)) :
    WZ1PaperTubeShading sticky.selected.family :=
  intersectTwoShadings
    (propertyThreeFinePullbackShading
      sticky.cover sticky.refined propP.propertyThree)
    pruning.pruned

/-- Data retained by the boundary-safe pullback.  `targetMass` is chosen by
the outer loss hierarchy; keeping it abstract makes the exact bookkeeping
visible. -/
structure Proposition63SafePullbackData
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta)
    (targetMass : ENNReal) where
  pruning : WZ2PaperBoundaryCellPruningData
    (rho := rho.1) sticky.refined hdelta
    (stickyCoarseMultiplicityCap sticky *
      stickyFiberMultiplicityCap sticky)
  retained_mass : targetMass ≤
    (proposition63SafePullbackShading
      sticky propP hdelta pruning).mass

namespace Proposition63SafePullbackData

def shading
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃}
    {hdelta : 0 < delta}
    {targetMass : ENNReal}
    (data : Proposition63SafePullbackData
      sticky propP hdelta targetMass) :
    WZ1PaperTubeShading sticky.selected.family :=
  proposition63SafePullbackShading sticky propP hdelta data.pruning

theorem sub_pullback
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃}
    {hdelta : 0 < delta}
    {targetMass : ENNReal}
    (data : Proposition63SafePullbackData
      sticky propP hdelta targetMass) :
    PaperIsSubshading data.shading
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree) :=
  intersectTwoShadings_sub_left _ _

theorem sub_refined
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃}
    {hdelta : 0 < delta}
    {targetMass : ENNReal}
    (data : Proposition63SafePullbackData
      sticky propP hdelta targetMass) :
    PaperIsSubshading data.shading sticky.refined := by
  intro index point hpoint
  exact data.pruning.pruned_subshading index hpoint.2

theorem cubical
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃}
    {hdelta : 0 < delta}
    {targetMass : ENNReal}
    (data : Proposition63SafePullbackData
      sticky propP hdelta targetMass) :
    WZ1PaperIsCubicalShading data.shading := by
  intro index point hpoint other hother
  change point ∈
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree).carrier index ∧
      point ∈ data.pruning.pruned.carrier index at hpoint
  have hotherPruned : other ∈ data.pruning.pruned.carrier index :=
    data.pruning.pruned_cubical index point hpoint.2 hother
  have hpointSafe : point ∈
      ⋃ fineCell ∈ data.pruning.safeFineCells,
        wz1PaperGridCube delta fineCell := by
    rw [data.pruning.pruned_carrier_eq] at hpoint
    exact hpoint.2.2
  rcases Set.mem_iUnion₂.mp hpointSafe with
    ⟨fineCell, hfineCell, hpointFineCell⟩
  have hpointFineIndex :
      wz1PaperGridIndex delta point = fineCell :=
    (mem_wz1PaperGridCube delta fineCell point).mp hpointFineCell
  have hotherFineCell : other ∈ wz1PaperGridCube delta fineCell := by
    rwa [← hpointFineIndex]
  have hcoarseCell := data.pruning.safeFineCell_contained
    fineCell hfineCell
  have hpointCoarse := hcoarseCell hpointFineCell
  have hotherCoarse := hcoarseCell hotherFineCell
  have hrhoIndex :
      wz1PaperGridIndex rho.1 other =
        wz1PaperGridIndex rho.1 point := by
    exact ((mem_wz1PaperGridCube rho.1
      (data.pruning.coarseParent fineCell) other).mp hotherCoarse).trans
      ((mem_wz1PaperGridCube rho.1
        (data.pruning.coarseParent fineCell) point).mp hpointCoarse).symm
  change other ∈
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree).carrier index ∧
      other ∈ data.pruning.pruned.carrier index
  refine ⟨?_, hotherPruned⟩
  change other ∈ sticky.refined.carrier index ∧
    wz1PaperGridIndex rho.1 other ∈
      wz1PaperGridIndex rho.1 '' propP.propertyThree.union
  exact ⟨data.pruning.pruned_subshading index hotherPruned, by
    rw [hrhoIndex]
    exact hpoint.1.2⟩

/-- Rebase finite planiness constructed after non-aligned boundary pruning
onto the raw Property-Three pullback.  The final shading and plane map are
unchanged; only the explicit mass-retention factor is composed. -/
def rebasePlaniness
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ coefficient
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃}
    {hdelta : 0 < delta}
    (retainedFactor : ENNReal)
    (hretainedFactorPos : 0 < retainedFactor)
    (hretainedFactorTop : retainedFactor ≠ ⊤)
    (data : Proposition63SafePullbackData sticky propP hdelta
      (retainedFactor *
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass))
    (bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) data.shading incidenceBudget) :
    BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree)
      incidenceBudget :=
  bounded.rebaseOfRetained data.sub_pullback retainedFactor
    hretainedFactorPos hretainedFactorTop data.retained_mass

end Proposition63SafePullbackData

/-- Construct the non-aligned safe pullback.  The first inequality makes the
boundary pruning nonempty.  The second reserves `targetMass` after paying
the same boundary error from the raw Property-Three mass lower bound. -/
theorem proposition63_safe_pullback
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta)
    (hdeltaRho : delta ≤ rho.1)
    (hrhoOne : rho.1 ≤ 1)
    (targetMass : ENNReal)
    (hboundary :
      (stickyCoarseMultiplicityCap sticky *
          stickyFiberMultiplicityCap sticky) *
          ENNReal.ofReal (1000 * delta / rho.1) <
        sticky.refined.mass)
    (hretained :
      targetMass +
          (stickyCoarseMultiplicityCap sticky *
            stickyFiberMultiplicityCap sticky) *
            ENNReal.ofReal (1000 * delta / rho.1) ≤
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass) :
    Nonempty (Proposition63SafePullbackData
      sticky propP hdelta targetMass) := by
  let cap := stickyCoarseMultiplicityCap sticky *
    stickyFiberMultiplicityCap sticky
  have hfiberCap : ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity sticky.coarse
          sticky.refined parent point : ENNReal) ≤
        stickyFiberMultiplicityCap sticky := by
    intro parent point
    calc
      (wz2PaperFullFiberPointMultiplicity sticky.coarse
          sticky.refined parent point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - stickyLoss) *
            ((wz2PaperFullFiberIndices sticky.selected.family
              sticky.coarse parent).card : ENNReal) :=
        sticky.fiber_multiplicity_upper parent point
      _ ≤ stickyFiberMultiplicityCap sticky := by
        apply mul_le_mul_left'
        change
          ((wz2PaperFullFiberIndices sticky.selected.family
            sticky.coarse parent).card : ENNReal) ≤
          (sticky.selected.family.card : ENNReal)
        exact_mod_cast (show
          (wz2PaperFullFiberIndices sticky.selected.family
            sticky.coarse parent).card ≤ sticky.selected.family.card by
          simpa only [Fintype.card_fin] using
            (Finset.card_le_univ
              (s := wz2PaperFullFiberIndices sticky.selected.family
                sticky.coarse parent)))
  have hcap : ∀ point,
      (sticky.refined.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point
    exact fine_pointMultiplicity_le_coarse_mul_fiber
      sticky.balanced
      (stickyCoarseMultiplicityCap sticky)
      (stickyFiberMultiplicityCap sticky)
      sticky.coarse_multiplicity_upper
      hfiberCap point
  rcases wz2_prop_sticky_boundary_cell_pruning
      hdelta hdeltaRho sticky.coarse_extremal.delta_pos hrhoOne
      sticky.refined sticky.refined_cubical cap hcap
      (by simpa [cap] using hboundary) with ⟨pruning⟩
  let safe := proposition63SafePullbackShading
    sticky propP hdelta pruning
  have hrawSub : PaperIsSubshading
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree)
      sticky.refined :=
    propertyThreeFinePullbackShading_subshading _ _ _
  have hintersection := intersectTwoShadings_mass_ineq
    hrawSub pruning.pruned_subshading
  have hprunedTop : pruning.pruned.mass ≠ ⊤ := by
    change (∑ index : Fin sticky.selected.family.card,
      volume (pruning.pruned.carrier index)) ≠ ⊤
    apply ENNReal.sum_ne_top.2
    intro index _
    have hcarrier : volume (pruning.pruned.carrier index) ≤
        volume (Kakeya.Streamlined.axisBox 2 2 2) :=
      measure_mono <| (pruning.pruned.subset_body index).trans
        Set.inter_subset_right
    exact ne_top_of_le_ne_top (by
      rw [Kakeya.Streamlined.volume_axisBox
        2 2 2 (by norm_num) (by norm_num) (by norm_num)]
      exact ENNReal.ofReal_ne_top) hcarrier
  have herrorTop :
      cap * ENNReal.ofReal (1000 * delta / rho.1) ≠ ⊤ := by
    have hcoarseCapTop : stickyCoarseMultiplicityCap sticky ≠ ⊤ := by
      exact ENNReal.mul_ne_top
        (by simp [stickyCoarseMultiplicityCap, Kakeya.realRpowENN])
        (by simp [stickyCoarseMultiplicityCap,
          Kakeya.Streamlined.TubeFamily.enncard])
    have hfiberCapTop : stickyFiberMultiplicityCap sticky ≠ ⊤ := by
      exact ENNReal.mul_ne_top
        (by simp [stickyFiberMultiplicityCap, Kakeya.realRpowENN])
        (by simp [stickyFiberMultiplicityCap,
          Kakeya.Streamlined.TubeFamily.enncard])
    apply ENNReal.mul_ne_top
    · dsimp only [cap]
      exact ENNReal.mul_ne_top hcoarseCapTop hfiberCapTop
    · exact ENNReal.ofReal_ne_top
  have hrawLe :
      (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass ≤
        cap * ENNReal.ofReal (1000 * delta / rho.1) + safe.mass := by
    apply (ENNReal.add_le_add_iff_left hprunedTop).mp
    calc
      pruning.pruned.mass +
          (propertyThreeFinePullbackShading
            sticky.cover sticky.refined propP.propertyThree).mass =
        (propertyThreeFinePullbackShading
            sticky.cover sticky.refined propP.propertyThree).mass +
          pruning.pruned.mass := by ac_rfl
      _ ≤ sticky.refined.mass + safe.mass := by
        simpa [safe, proposition63SafePullbackShading] using hintersection
      _ ≤ (pruning.pruned.mass +
          cap * ENNReal.ofReal (1000 * delta / rho.1)) + safe.mass := by
        gcongr
        simpa [cap] using pruning.source_mass_le_explicit
      _ = pruning.pruned.mass +
          (cap * ENNReal.ofReal (1000 * delta / rho.1) + safe.mass) := by
        ac_rfl
  have htargetWithError :
      targetMass + cap * ENNReal.ofReal (1000 * delta / rho.1) ≤
        cap * ENNReal.ofReal (1000 * delta / rho.1) + safe.mass := by
    have hretained' :
        targetMass + cap * ENNReal.ofReal (1000 * delta / rho.1) ≤
          (propertyThreeFinePullbackShading
            sticky.cover sticky.refined propP.propertyThree).mass := by
      simpa [cap] using hretained
    exact hretained'.trans hrawLe
  have htarget : targetMass ≤ safe.mass := by
    apply (ENNReal.add_le_add_iff_left herrorTop).mp
    simpa [add_comm] using htargetWithError
  exact ⟨{ pruning := pruning, retained_mass := htarget }⟩

/-- Run finite planiness on the boundary-safe pullback, then attach the
Property-Three local AD estimate and rebase the resulting package on the
unchanged Node-3 fine shading.  This is the exact-power-scale replacement
for the old integer-alignment shortcut. -/
theorem proposition63_safe_initial_local_data
    {delta sigma stickyLoss sourceADLoss localLoss tau epsilon₁ epsilon₃
      coefficient incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hdelta : 0 < delta)
    (retainedFactor : ENNReal)
    (hretainedFactorPos : 0 < retainedFactor)
    (hretainedFactorTop : retainedFactor ≠ ⊤)
    (safe : Proposition63SafePullbackData sticky propP hdelta
      (retainedFactor *
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass))
    (bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient) safe.shading incidenceBudget)
    (hboundedMass : 0 < bounded.data.refinement.shading.mass)
    (hdeltaOne : delta < 1)
    (hlocalLoss : 0 < localLoss)
    (hsourceADLoss : 0 < sourceADLoss)
    (htau_def : tau = rho.1 * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (htau_le_20L : tau ≤ 20 * rho.1)
    (hL_le_tau : rho.1 ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * rho.1)
    (htau_le_one : tau ≤ 1)
    (hL_small : rho.1 ≤ 1 / 1000)
    (hL_pos : 0 < rho.1)
    (hL_half : rho.1 ≤ 1 / 2)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁)
    (heps₁_lt : epsilon₁ < 1 / 20)
    (heps₃_pos : 0 < epsilon₃)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (L₀_log : ℝ)
    (hL_le_L0_log : rho.1 ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀_log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_propertyThree_full :
      ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
        point ∈ propP.propertyThree.carrier parent →
          Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
              ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier parent ∩
              Metric.closedBall point tau))
    (h_ax_condition :
      4 * (6 * rho.1) ^ 2 ≤
        (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hL_lower : Real.rpow delta stickyLoss ≤ rho.1)
    (hL_bound : rho.1 ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (hstickyLoss_le_sourceAD : 3 * stickyLoss ≤ sourceADLoss)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      let sourceConstant := Kakeya.realRpowENN delta (-sourceADLoss)
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / delta)) ≤
        Kakeya.realRpowENN delta (-localLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        delta ^ (-localLoss)) :
    ∃ initial : PropertyThreeSelectedInitialLocalData
        (sigma := sigma) (outputLoss := localLoss)
        (coefficient := coefficient) sticky.refined,
      initial.incidence ≤ incidenceBudget := by
  let rebasedBounded := safe.rebasePlaniness retainedFactor
    hretainedFactorPos hretainedFactorTop bounded
  let rebased : BalancedFinitePlaninessData
      (coefficient := coefficient)
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree) :=
    rebasedBounded.data
  rcases propertyThree_selected_initial_local_data
      sticky propP rebased hboundedMass hdelta hdeltaOne hlocalLoss
      hsourceADLoss htau_def htau_pos htau_le_20L hL_le_tau htau_sq
      htau_le_one hL_small hL_pos hL_half hsigma_pos hsigma_lt_one
      heps₁_pos heps₁_lt heps₃_pos heps₃_def heps_sum L₀_log
      hL_le_L0_log h_log_main h_propertyThree_full h_ax_condition
      hL_lower hL_bound hstickyLoss_le_sourceAD hsmallCost
      hlargeEndpoint with ⟨initial, hinitialIncidence⟩
  refine ⟨initial.onStickyRefined sticky propP hdelta, ?_⟩
  change initial.incidence ≤ incidenceBudget
  rw [hinitialIncidence]
  exact bounded.incidence_le

end Kakeya.Assouad.PureWZ2

end
