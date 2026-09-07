import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDoubledParentCarrierCover
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedOrdinaryDistinctnessToLineDistance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalTubeCloseness

/-!
# Same-axis ordinary parents for localized public families

This module supplies the radius-only part of the nearby-scale construction.
The supporting line and ordinary unit segment are unchanged; only the tube
radius is enlarged.  Consequently strict ordinary carrier containment is
literal, while the localized doubled-fiber separation theorem applies with
no hidden whole-line substitution.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Enlarging only the radius preserves the ordinary axis segment and hence
monotonically enlarges the ordinary carrier. -/
theorem pureWZ2_relabel_carrier_mono
    {delta rho : ℝ}
    (hscale : delta ≤ rho)
    (tube : Kakeya.DeltaTube delta) :
    tube.carrier ⊆
      (wz2PaperRelabelTube (targetScale := rho) tube).carrier := by
  change Metric.cthickening delta
      (Kakeya.unitSegment tube.base tube.direction) ⊆
    Metric.cthickening rho
      (Kakeya.unitSegment tube.base tube.direction)
  exact Metric.cthickening_mono hscale _

/-- Relabel an entire localized ordinary family at a larger radius. -/
def pureWZ2LocalizedRelabelFamily
    {delta rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily rho :=
  wz2PaperRelabelFamily (targetScale := rho) family

@[simp] theorem pureWZ2LocalizedRelabelFamily_tube
    {delta rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (index : Fin family.card) :
    (pureWZ2LocalizedRelabelFamily (rho := rho) family).tube index =
      wz2PaperRelabelTube (targetScale := rho) (family.tube index) := rfl

theorem pureWZ2LocalizedRelabelFamily_lineClass
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family) :
    WZ1PaperIsLineClass
      (pureWZ2LocalizedRelabelFamily (rho := rho) family) :=
  hline.relabel

theorem pureWZ2LocalizedRelabelFamily_self_cover
    {delta rho : ℝ}
    (hscale : delta ≤ rho)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (index : Fin family.card) :
    (family.tube index).carrier ⊆
      ((pureWZ2LocalizedRelabelFamily (rho := rho) family).tube index).carrier :=
  pureWZ2_relabel_carrier_mono hscale (family.tube index)

/-- In the height-zero based ordinary model, paper line distance plus the
fine radius is enough for strict containment in a same-axis radius relabel of
the representative. -/
theorem pureWZ2_zeroBased_carrier_subset_relabel_of_lineDistance
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (first second : Kakeya.DeltaTube delta)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hbudget : wz1PaperLineDistance first second + delta ≤ rho) :
    (pureWZ2PaperZeroBasedTube first).carrier ⊆
      (wz2PaperRelabelTube (targetScale := rho)
        (pureWZ2PaperZeroBasedTube second)).carrier := by
  have hzeroFirst :
      wz1TubeAxisZeroPoint (pureWZ2PaperZeroBasedTube first) =
        wz1TubeAxisZeroPoint first :=
    pureWZ2PaperZeroBasedTube_zeroPoint first hfirst
  have hzeroSecond :
      wz1TubeAxisZeroPoint (pureWZ2PaperZeroBasedTube second) =
        wz1TubeAxisZeroPoint second :=
    pureWZ2PaperZeroBasedTube_zeroPoint second hsecond
  have hdirectionFirst :
      wz1PaperDirection (pureWZ2PaperZeroBasedTube first) =
        wz1PaperDirection first :=
    pureWZ2PaperZeroBasedTube_paperDirection first hfirst
  have hdirectionSecond :
      wz1PaperDirection (pureWZ2PaperZeroBasedTube second) =
        wz1PaperDirection second :=
    pureWZ2PaperZeroBasedTube_paperDirection second hsecond
  have hbase :
      ‖(pureWZ2PaperZeroBasedTube first).base -
          (pureWZ2PaperZeroBasedTube second).base‖ ≤
        dist (wz1TubeAxisZeroPoint first)
          (wz1TubeAxisZeroPoint second) := by
    change ‖wz1TubeAxisZeroPoint first -
        wz1TubeAxisZeroPoint second‖ ≤ _
    rw [dist_eq_norm]
  have hdirection :
      ‖(pureWZ2PaperZeroBasedTube first).direction -
          (pureWZ2PaperZeroBasedTube second).direction‖ ≤
        InnerProductGeometry.angle
          (wz1PaperDirection first) (wz1PaperDirection second) := by
    change ‖wz1PaperDirection first - wz1PaperDirection second‖ ≤ _
    exact unit_norm_sub_le_angle
      (wz1PaperDirection_norm first) (wz1PaperDirection_norm second)
  apply tube_containment_from_closeness hdelta.le hrho.le
  dsimp only [wz2PaperRelabelTube]
  have hmetric :
      dist (wz1TubeAxisZeroPoint first)
          (wz1TubeAxisZeroPoint second) +
        InnerProductGeometry.angle
          (wz1PaperDirection first) (wz1PaperDirection second) =
      wz1PaperLineDistance first second := rfl
  linarith

/-- In the midpoint-centered ordinary model, a paper line-distance budget
plus the fine radius gives strict containment after enlarging only the
representative radius.  The factor `3 / 2` is the sum of the direction loss
along the unit segment and the half-direction loss in the centered basepoint.
-/
theorem pureWZ2_centered_carrier_subset_relabel_of_lineDistance
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (first second : Kakeya.DeltaTube delta)
    (hbudget :
      (3 / 2 : ℝ) * wz1PaperLineDistance first second + delta ≤ rho) :
    (pureWZ2PaperCenteredTube first).carrier ⊆
      (wz2PaperRelabelTube (targetScale := rho)
        (pureWZ2PaperCenteredTube second)).carrier := by
  let firstCentered := pureWZ2PaperCenteredTube first
  let secondCentered := pureWZ2PaperCenteredTube second
  have hbase :
      ‖firstCentered.base - secondCentered.base‖ ≤
        dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          (1 / 2 : ℝ) *
            InnerProductGeometry.angle
              (wz1PaperDirection first) (wz1PaperDirection second) := by
    have hbaseVector :
        firstCentered.base - secondCentered.base =
          (wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second) -
            (1 / 2 : ℝ) •
              (wz1PaperDirection first - wz1PaperDirection second) := by
      change
        (wz1TubeAxisZeroPoint first -
            (1 / 2 : ℝ) • wz1PaperDirection first) -
          (wz1TubeAxisZeroPoint second -
            (1 / 2 : ℝ) • wz1PaperDirection second) = _
      module
    rw [hbaseVector]
    calc
      ‖(wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second) -
            (1 / 2 : ℝ) •
              (wz1PaperDirection first - wz1PaperDirection second)‖ ≤
          ‖wz1TubeAxisZeroPoint first - wz1TubeAxisZeroPoint second‖ +
            ‖(1 / 2 : ℝ) •
              (wz1PaperDirection first - wz1PaperDirection second)‖ :=
        norm_sub_le _ _
      _ = dist (wz1TubeAxisZeroPoint first)
              (wz1TubeAxisZeroPoint second) +
            (1 / 2 : ℝ) *
              ‖wz1PaperDirection first - wz1PaperDirection second‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
        norm_num
      _ ≤ dist (wz1TubeAxisZeroPoint first)
              (wz1TubeAxisZeroPoint second) +
            (1 / 2 : ℝ) *
              InnerProductGeometry.angle
                (wz1PaperDirection first) (wz1PaperDirection second) := by
        gcongr
        exact unit_norm_sub_le_angle
          (wz1PaperDirection_norm first)
          (wz1PaperDirection_norm second)
  have hdirection :
      ‖firstCentered.direction - secondCentered.direction‖ ≤
        InnerProductGeometry.angle
          (wz1PaperDirection first) (wz1PaperDirection second) := by
    exact unit_norm_sub_le_angle
      (wz1PaperDirection_norm first)
      (wz1PaperDirection_norm second)
  apply tube_containment_from_closeness hdelta.le hrho.le
  change
    ‖firstCentered.base - secondCentered.base‖ +
        ‖firstCentered.direction - secondCentered.direction‖ + delta ≤ rho
  have hmetric :
      dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          InnerProductGeometry.angle
            (wz1PaperDirection first) (wz1PaperDirection second) =
        wz1PaperLineDistance first second := rfl
  have hangleNonnegative :
      0 ≤ InnerProductGeometry.angle
        (wz1PaperDirection first) (wz1PaperDirection second) :=
    InnerProductGeometry.angle_nonneg _ _
  calc
    ‖firstCentered.base - secondCentered.base‖ +
          ‖firstCentered.direction - secondCentered.direction‖ + delta ≤
        dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) +
          (3 / 2 : ℝ) *
            InnerProductGeometry.angle
              (wz1PaperDirection first) (wz1PaperDirection second) +
          delta := by
      linarith
    _ ≤ (3 / 2 : ℝ) *
          wz1PaperLineDistance first second + delta := by
      rw [← hmetric]
      have hzeroNonnegative :
          0 ≤ dist (wz1TubeAxisZeroPoint first)
            (wz1TubeAxisZeroPoint second) := dist_nonneg
      linarith
    _ ≤ rho := hbudget

/-- Canonical midpoint-centering preserves membership in the fixed paper line
class. -/
theorem pureWZ2PaperCenteredTube_lineClass
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    WZ1PaperTubeInLineClass (pureWZ2PaperCenteredTube tube) := by
  have hzero := pureWZ2PaperCenteredTube_zeroPoint tube hline
  have hdirection := pureWZ2PaperCenteredTube_paperDirection tube hline
  exact ⟨by rw [hdirection]; exact hline.1,
    by rw [hzero]; exact hline.2.1,
    by rw [hzero]; exact hline.2.2⟩

/-- A tube whose stored direction is positively oriented and whose midpoint
lies at height zero is already the canonical centered representative of its
paper line. -/
theorem pureWZ2PaperCenteredTube_eq_self
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hline : WZ1PaperTubeInLineClass tube)
    (hdirection : 0 ≤ tube.direction 2)
    (hmidpoint : wz2PaperTubeMidpoint tube 2 = 0) :
    pureWZ2PaperCenteredTube tube = tube := by
  have hzero : wz1TubeAxisZeroPoint tube = wz2PaperTubeMidpoint tube := by
    apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hline.vertical
    · exact ⟨1 / 2, rfl⟩
    · exact hmidpoint
  have hpaperDirection : wz1PaperDirection tube = tube.direction := by
    unfold wz1PaperDirection
    rw [if_pos hdirection]
  rw [Kakeya.DeltaTube.mk.injEq]
  constructor
  · change wz1TubeAxisZeroPoint tube -
        (1 / 2 : ℝ) • wz1PaperDirection tube = tube.base
    rw [hzero, hpaperDirection]
    dsimp only [wz2PaperTubeMidpoint]
    module
  · exact hpaperDirection

/-- Strong separation of same-axis relabelled parents gives the exact public
centered-doubled-fiber disjointness required by Definition 2.12. -/
theorem pureWZ2_localized_relabel_doubledFibers_disjoint
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperIsLineClass fine)
    (hlocal : ∀ source,
      ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3)
    (hseparated : ∀ first second : Fin fine.card, first ≠ second →
      2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho <
        wz1PaperLineDistance (fine.tube first) (fine.tube second)) :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine
          (pureWZ2LocalizedRelabelFamily (rho := rho) fine) first)
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine
          (pureWZ2LocalizedRelabelFamily (rho := rho) fine) second) := by
  apply wz2_paper_localized_ordinary_dilatedFiberIndices_disjoint
      hdelta hrho hfine
      (pureWZ2LocalizedRelabelFamily_lineClass hfine) hlocal
  intro first second hne
  change
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho <
      wz1PaperLineDistance
        (wz2PaperRelabelTube (targetScale := rho) (fine.tube first))
        (wz2PaperRelabelTube (targetScale := rho) (fine.tube second))
  rw [wz2PaperRelabelTube_lineDistance_both]
  exact hseparated first second hne

/-- If the fine family itself is strongly separated at the parent radius,
same-index radius relabelling is already a literal public partitioning cover.
This is the singleton-fiber endpoint used at the top of a buffered schedule.
-/
def pureWZ2_localized_relabel_partitioningCover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hscale : delta ≤ rho)
    (hfine : WZ1PaperIsLineClass fine)
    (hlocal : ∀ source,
      ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3)
    (hseparated : ∀ first second : Fin fine.card, first ≠ second →
      2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho <
        wz1PaperLineDistance (fine.tube first) (fine.tube second)) :
    WZ2PaperPurePartitioningCover fine
      (pureWZ2LocalizedRelabelFamily (rho := rho) fine) where
  covers source := by
    refine ⟨source, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact pureWZ2LocalizedRelabelFamily_self_cover hscale fine source
  doubled_fibers_disjoint :=
    pureWZ2_localized_relabel_doubledFibers_disjoint
      hdelta hrho hfine hlocal hseparated

end Kakeya.Assouad

end
