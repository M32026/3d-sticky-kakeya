import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase3
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransverseFromBalancedCover

/-!
# Robust fine close count directly from frozen sticky data

This module records the part of the non-degenerate plane-map input that is
already forced by `PureWZ2PropStickyData`.  It deliberately keeps the full
fiber-cardinality factor visible: removing that factor requires an additional
density/cardinality comparison and must not be hidden in the plane-map
assembly.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- The universal coarse close-direction packing constant used at threshold
`10 * rho`. -/
def stickyCoarseCloseCount : ENNReal :=
  (2 * 4 * 601 ^ 3 * 12001 ^ 3 : ENNReal)

/-- The pointwise fiber-density power supplied by frozen sticky data. -/
def stickyFiberPower (delta rho sigma loss : ℝ) : ENNReal :=
  Kakeya.realRpowENN (delta / rho) (2 - sigma - loss)

/-- Frozen sticky data bounds the Phase-2 fiber multiplicity by the stated
power times the cardinality of the corresponding complete full fiber. -/
lemma sticky_fiber_multiplicity_upper
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := loss)
      sourceShading rho logExponent)
    (parent : Fin sticky.coarse.card) (point : Point3) :
    (fiberPointMultiplicity sticky.cover sticky.refined parent point : ENNReal) ≤
      stickyFiberPower delta rho.1 sigma loss *
        ((wz2PaperFullFiberIndices
          sticky.selected.family sticky.coarse parent).card : ENNReal) := by
  have hcard :
      fiberPointMultiplicity sticky.cover sticky.refined parent point ≤
        ((wz2PaperFullFiberIndices
          sticky.selected.family sticky.coarse parent).filter fun source =>
            point ∈ sticky.refined.carrier source).card := by
    unfold fiberPointMultiplicity
    apply Finset.card_le_card
    intro sourceIndex hsource
    rcases Finset.mem_filter.mp hsource with
      ⟨_, hparent, hpoint⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpoint⟩
    rw [mem_wz2PaperFullFiberIndices_iff]
    rw [← hparent]
    exact selectedParent_covers sticky.cover sourceIndex
  have hcardENN :
      (fiberPointMultiplicity sticky.cover sticky.refined parent point : ENNReal) ≤
        (((wz2PaperFullFiberIndices
          sticky.selected.family sticky.coarse parent).filter fun source =>
            point ∈ sticky.refined.carrier source).card : ENNReal) := by
    exact_mod_cast hcard
  exact hcardENN.trans (sticky.fiber_multiplicity_upper parent point)

/-- Every complete full fiber has cardinality at most the ambient selected
fine family. -/
lemma sticky_full_fiber_card_le_fine_card
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := loss)
      sourceShading rho logExponent)
    (parent : Fin sticky.coarse.card) :
    ((wz2PaperFullFiberIndices
      sticky.selected.family sticky.coarse parent).card : ENNReal) ≤
        sticky.selected.family.enncard := by
  change
    ((wz2PaperFullFiberIndices
      sticky.selected.family sticky.coarse parent).card : ENNReal) ≤
      (sticky.selected.family.card : ENNReal)
  have hcard :
      (wz2PaperFullFiberIndices
        sticky.selected.family sticky.coarse parent).card ≤
          sticky.selected.family.card := by
    simpa using Finset.card_le_univ
      (s := wz2PaperFullFiberIndices
        sticky.selected.family sticky.coarse parent)
  exact_mod_cast hcard

/-- Phase 1--3 instantiated from the frozen sticky record.  The bound is
non-vacuous and uses the actual selected fine family and refined shading.

The remaining plane-map input is precisely a lower multiplicity estimate that
dominates this displayed quantity (up to the factor required by transverse
pair counting). -/
lemma sticky_robust_close_count
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := loss)
      sourceShading rho logExponent)
    (hrho_small : rho.1 ≤ 1 / 10000) :
    ∀ point ∈ sticky.refined.union, ∀ index,
      point ∈ sticky.refined.carrier index →
        (paperCloseDirectionCount
          sticky.refined point index rho.1 : ENNReal) ≤
          stickyCoarseCloseCount *
            (stickyFiberPower delta rho.1 sigma loss *
              sticky.selected.family.enncard) := by
  have hrho_pos : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have halign : ∀ index : Fin sticky.selected.family.card,
      ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        ‖(sticky.coarse.tube (selectParent sticky.cover index)).direction -
            sign • (sticky.selected.family.tube index).direction‖ ≤ rho.1 / 2 :=
    fun index => directionAlignment_from_cover sticky.cover hrho_pos index
  have hfiber : ∀ (parent : Fin sticky.coarse.card) (point : Point3),
      (fiberPointMultiplicity sticky.cover sticky.refined parent point : ENNReal) ≤
        stickyFiberPower delta rho.1 sigma loss *
          sticky.selected.family.enncard := by
    intro parent point
    exact (sticky_fiber_multiplicity_upper sticky parent point).trans <| by
      gcongr
      exact sticky_full_fiber_card_le_fine_card sticky parent
  have hcoarse : ∀ point ∈ sticky.croppedCoarseShading.union, ∀ index,
      point ∈ sticky.croppedCoarseShading.carrier index →
        (paperCloseDirectionCount sticky.croppedCoarseShading point index
          (10 * rho.1) : ENNReal) ≤ stickyCoarseCloseCount := by
    intro point hpoint index hindex
    exact pureWz2_close_direction_count
      (delta := delta) (sigma := sigma)
      sticky.cover.coarse_essentially_distinct
      sticky.cover.coarse_line_class hrho_pos hrho_small
      point hpoint index hindex
  intro point _ index hpoint
  exact pureWz2_robust_close_count
    (hsub := fun _ => Set.Subset.rfl)
    halign sticky.balanced.point_compatibility
    (stickyFiberPower delta rho.1 sigma loss *
      sticky.selected.family.enncard) hfiber
    stickyCoarseCloseCount hcoarse hrho_pos point index hpoint

/-- Exact remaining gap for obtaining a non-degenerate transverse refinement
from the frozen sticky record.

All geometric close-count inputs are discharged here.  The caller supplies an
average fine multiplicity `A` and a natural threshold `m` strictly above the
displayed frozen-sticky close-count bound.  The output retains half the shaded
mass and has a genuine transverse pair through every surviving point.

Keeping `hgap` explicit is essential: the frozen record contains only the
one-sided fiber cap and does not itself compare complete-fiber cardinality to
fine point multiplicity. -/
lemma sticky_transverse_refinement_of_average_gap
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := loss)
      sourceShading rho logExponent)
    (hrho_small : rho.1 ≤ 1 / 10000)
    (A : ENNReal)
    (hA_top : A ≠ ⊤)
    (hvolume_top : volume sticky.refined.union ≠ ⊤)
    (hmass_top : sticky.refined.mass ≠ ⊤)
    (haverage : A * volume sticky.refined.union ≤ sticky.refined.mass)
    (m : ℕ)
    (hm_le : (m : ENNReal) ≤ A / 2)
    (hgap :
      stickyCoarseCloseCount *
          (stickyFiberPower delta rho.1 sigma loss *
            sticky.selected.family.enncard) <
        (m : ENNReal)) :
    ∃ selected : WZ1PaperTubeShading sticky.selected.family,
      PaperIsSubshading selected sticky.refined ∧
      (∀ point ∈ selected.union, m ≤ selected.pointMultiplicity point) ∧
      (∀ point ∈ selected.union, ∃ first second,
        point ∈ selected.carrier first ∧
        point ∈ selected.carrier second ∧
        rho.1 ≤ ‖wz1Cross
          (sticky.selected.family.tube first).direction
          (sticky.selected.family.tube second).direction‖) ∧
      (1 / 2 : ENNReal) * sticky.refined.mass ≤ selected.mass := by
  let closeBound : ENNReal :=
    stickyCoarseCloseCount *
      (stickyFiberPower delta rho.1 sigma loss *
        sticky.selected.family.enncard)
  have hcloseBound_top : closeBound ≠ ⊤ := by
    dsimp only [closeBound, stickyCoarseCloseCount, stickyFiberPower]
    apply ENNReal.mul_ne_top
    · norm_num
    · apply ENNReal.mul_ne_top
      · simp [Kakeya.realRpowENN]
      · simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hclose : ∀ point ∈ sticky.refined.union, ∀ index,
      point ∈ sticky.refined.carrier index →
        (paperCloseDirectionCount sticky.refined point index rho.1 : ENNReal) ≤
          closeBound := by
    simpa [closeBound] using sticky_robust_close_count sticky hrho_small
  exact transverse_subshading_from_close_count_and_avg
    closeBound A hcloseBound_top hA_top hvolume_top hmass_top
    hclose le_rfl haverage m hm_le hgap

end Kakeya.Assouad.PureWZ2

end
