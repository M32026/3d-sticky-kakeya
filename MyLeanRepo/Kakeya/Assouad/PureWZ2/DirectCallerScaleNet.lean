import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectCallerLineSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Intrinsic one-scale net on a centered caller family

At a requested scale `t ≥ rho`, take a maximal `t / 4` net in the WZ
supporting-line metric of the already midpoint-centered caller family.
Each caller is ordinarily contained in the radius-`19t` centered tube on its
owner line.  The raw parent conflict graph has a dimension-only degree bound.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

attribute [local instance] Classical.propDecidable

theorem wz2Paper_centered_carrier_subset_of_lineDistance
    {sourceScale parentScale : ℝ}
    (hsource : 0 < sourceScale)
    (hparent : 0 < parentScale)
    (hsourceParent : sourceScale ≤ parentScale)
    {sourceTube centerTube : Kakeya.DeltaTube sourceScale}
    (sourceLine : WZ1PaperTubeInLineClass sourceTube)
    (centerLine : WZ1PaperTubeInLineClass centerTube)
    (distanceBound :
      wz1PaperLineDistance sourceTube centerTube ≤ parentScale) :
    (wz2PaperCenteredLineTube
        (targetScale := sourceScale) sourceTube).carrier ⊆
      (wz2PaperCenteredLineTube
        (targetScale := 19 * parentScale) centerTube).carrier := by
  intro point hpoint
  let sourceCentered :=
    wz2PaperCenteredLineTube
      (targetScale := sourceScale) sourceTube
  let parentCentered :=
    wz2PaperCenteredLineTube
      (targetScale := 19 * parentScale) centerTube
  have sourceSegmentCompact :
      IsCompact
        (Kakeya.unitSegment
          sourceCentered.base sourceCentered.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change
    point ∈
      Metric.cthickening sourceScale
        (Kakeya.unitSegment
          sourceCentered.base sourceCentered.direction) at hpoint
  rw [sourceSegmentCompact.cthickening_eq_biUnion_closedBall
    hsource.le] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨sourceAxisPoint, hsourceAxisPoint, hpointSource⟩
  rcases hsourceAxisPoint with
    ⟨parameter, hparameter, rfl⟩
  let parentAxisPoint :=
    parentCentered.base + parameter • parentCentered.direction
  have parentAxisMem :
      parentAxisPoint ∈
        Kakeya.unitSegment
          parentCentered.base parentCentered.direction :=
    ⟨parameter, hparameter, rfl⟩
  have zeroDistance :
      dist (wz1TubeAxisZeroPoint sourceTube)
          (wz1TubeAxisZeroPoint centerTube) ≤
        parentScale := by
    unfold wz1PaperLineDistance at distanceBound
    linarith [InnerProductGeometry.angle_nonneg
      (wz1PaperDirection sourceTube)
      (wz1PaperDirection centerTube)]
  have directionDistance :
      ‖wz1PaperDirection sourceTube -
          wz1PaperDirection centerTube‖ ≤
        parentScale := by
    have angleBound :
        InnerProductGeometry.angle
            (wz1PaperDirection sourceTube)
            (wz1PaperDirection centerTube) ≤
          parentScale := by
      unfold wz1PaperLineDistance at distanceBound
      linarith [show
        0 ≤ dist
          (wz1TubeAxisZeroPoint sourceTube)
          (wz1TubeAxisZeroPoint centerTube) from dist_nonneg]
    exact
      (unit_norm_sub_le_angle
        (wz1PaperDirection_norm sourceTube)
        (wz1PaperDirection_norm centerTube)).trans angleBound
  have centeredParameter :
      |parameter - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have axisDifference :
      (sourceCentered.base +
          parameter • sourceCentered.direction) -
        parentAxisPoint =
      (wz1TubeAxisZeroPoint sourceTube -
          wz1TubeAxisZeroPoint centerTube) +
        (parameter - 1 / 2) •
          (wz1PaperDirection sourceTube -
            wz1PaperDirection centerTube) := by
    dsimp only [sourceCentered, parentCentered, parentAxisPoint,
      wz2PaperCenteredLineTube]
    module
  have axisDistance :
      dist
          (sourceCentered.base +
            parameter • sourceCentered.direction)
          parentAxisPoint ≤
        3 * parentScale / 2 := by
    rw [dist_eq_norm, axisDifference]
    calc
      ‖(wz1TubeAxisZeroPoint sourceTube -
            wz1TubeAxisZeroPoint centerTube) +
          (parameter - 1 / 2) •
            (wz1PaperDirection sourceTube -
              wz1PaperDirection centerTube)‖ ≤
          ‖wz1TubeAxisZeroPoint sourceTube -
            wz1TubeAxisZeroPoint centerTube‖ +
          ‖(parameter - 1 / 2) •
            (wz1PaperDirection sourceTube -
              wz1PaperDirection centerTube)‖ :=
        norm_add_le _ _
      _ =
          dist (wz1TubeAxisZeroPoint sourceTube)
              (wz1TubeAxisZeroPoint centerTube) +
          |parameter - 1 / 2| *
            ‖wz1PaperDirection sourceTube -
              wz1PaperDirection centerTube‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ ≤ parentScale +
          (1 / 2) * parentScale := by
        gcongr
      _ = 3 * parentScale / 2 := by ring
  have pointParentDistance :
      dist point parentAxisPoint ≤ 19 * parentScale := by
    calc
      dist point parentAxisPoint ≤
          dist point
              (sourceCentered.base +
                parameter • sourceCentered.direction) +
            dist
              (sourceCentered.base +
                parameter • sourceCentered.direction)
              parentAxisPoint :=
        dist_triangle _ _ _
      _ ≤ sourceScale + 3 * parentScale / 2 := by
        gcongr
        simpa [Metric.mem_closedBall] using hpointSource
      _ ≤ 19 * parentScale := by
        nlinarith
  exact
    Metric.mem_cthickening_of_dist_le
      point parentAxisPoint (19 * parentScale)
      (Kakeya.unitSegment
        parentCentered.base parentCentered.direction)
      parentAxisMem pointParentDistance

def pureWZ2DirectScaleConflictDegree : ℕ :=
  145921 ^ 5

noncomputable def pureWZ2DirectScaleParentFamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {caller : WZ2PaperRequestedScale delta}
    (direct :
      PureWZ2DirectCallerLineSelectionData fine shading caller)
    (requested : WZ2PaperRequestedScale caller.1)
    (net :
      WZ2FiniteMaximalQuotientNetData
        direct.coarse.card
        (fun first second =>
          wz1PaperLineDistance
            (direct.coarse.tube first)
            (direct.coarse.tube second))
        (requested.1 / 4)) :
    Kakeya.Streamlined.TubeFamily (19 * requested.1) where
  card := net.centers.card
  tube parent :=
    wz2PaperCenteredLineTube
      (targetScale := 19 * requested.1)
      (direct.coarse.tube (net.centerEmbedding parent))

noncomputable def pureWZ2DirectScaleCenterFamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {caller : WZ2PaperRequestedScale delta}
    (direct :
      PureWZ2DirectCallerLineSelectionData fine shading caller)
    (requested : WZ2PaperRequestedScale caller.1)
    (net :
      WZ2FiniteMaximalQuotientNetData
        direct.coarse.card
        (fun first second =>
          wz1PaperLineDistance
            (direct.coarse.tube first)
            (direct.coarse.tube second))
        (requested.1 / 4)) :
    Kakeya.Streamlined.TubeFamily (requested.1 / 4) where
  card := net.centers.card
  tube parent :=
    wz2PaperCenteredLineTube
      (targetScale := requested.1 / 4)
      (direct.coarse.tube (net.centerEmbedding parent))

theorem pureWZ2_direct_scale_owner_containment
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {caller : WZ2PaperRequestedScale delta}
    (direct :
      PureWZ2DirectCallerLineSelectionData fine shading caller)
    (requested : WZ2PaperRequestedScale caller.1)
    (net :
      WZ2FiniteMaximalQuotientNetData
        direct.coarse.card
        (fun first second =>
          wz1PaperLineDistance
            (direct.coarse.tube first)
            (direct.coarse.tube second))
        (requested.1 / 4))
    (source : Fin direct.coarse.card) :
    (direct.coarse.tube source).carrier ⊆
      ((pureWZ2DirectScaleParentFamily
        direct requested net).tube (net.center source)).carrier := by
  let center := net.center source
  change
    (direct.coarse.tube source).carrier ⊆
      (wz2PaperCenteredLineTube
        (targetScale := 19 * requested.1)
        (direct.coarse.tube (net.centerEmbedding center))).carrier
  rw [← direct.coarse_centered source]
  apply
    wz2Paper_centered_carrier_subset_of_lineDistance
      direct.caller_pos
      (direct.caller_pos.trans_le requested.2.1)
      requested.2.1
      (direct.section6Cover.coarse_line_class source)
      (direct.section6Cover.coarse_line_class
        (net.centerEmbedding center))
  exact (net.center_close source).trans <| by
    nlinarith [direct.caller_pos.trans_le requested.2.1]

structure PureWZ2DirectCallerScaleNetData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {caller : WZ2PaperRequestedScale delta}
    (direct :
      PureWZ2DirectCallerLineSelectionData fine shading caller)
    (requested : WZ2PaperRequestedScale caller.1) where
  net :
    WZ2FiniteMaximalQuotientNetData
      direct.coarse.card
      (fun first second =>
        wz1PaperLineDistance
          (direct.coarse.tube first)
          (direct.coarse.tube second))
      (requested.1 / 4)
  owner_containment :
    ∀ source,
      (direct.coarse.tube source).carrier ⊆
        ((pureWZ2DirectScaleParentFamily
          direct requested net).tube (net.center source)).carrier
  parent_line_class :
    WZ1PaperIsLineClass
      (pureWZ2DirectScaleParentFamily direct requested net)
  parent_midpoint_local :
    ∀ parent,
      ‖wz2PaperTubeMidpoint
        ((pureWZ2DirectScaleParentFamily
          direct requested net).tube parent)‖ ≤ 1
  center_distinct :
    WZ1PaperIsEssentiallyDistinct
      (pureWZ2DirectScaleCenterFamily direct requested net)
  conflict_degree :
    ∀ fixed : Fin net.centers.card,
      (Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 direct.coarse
                (pureWZ2DirectScaleParentFamily direct requested net)
                fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 direct.coarse
                (pureWZ2DirectScaleParentFamily direct requested net)
                other).Nonempty).card ≤
        pureWZ2DirectScaleConflictDegree

theorem pureWZ2_direct_caller_scale_net
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {caller : WZ2PaperRequestedScale delta}
    (direct :
      PureWZ2DirectCallerLineSelectionData fine shading caller)
    (requested : WZ2PaperRequestedScale caller.1) :
    Nonempty (PureWZ2DirectCallerScaleNetData direct requested) := by
  have callerPos : 0 < caller.1 :=
    direct.caller_pos
  have requestedPos : 0 < requested.1 :=
    callerPos.trans_le requested.2.1
  let distance : Fin direct.coarse.card →
      Fin direct.coarse.card → ℝ :=
    fun first second =>
      wz1PaperLineDistance
        (direct.coarse.tube first)
        (direct.coarse.tube second)
  have distanceSymmetric :
      ∀ first second, distance first second = distance second first :=
    fun _ _ => wz1PaperLineDistance_symm _ _
  have distanceSelf : ∀ index, distance index index = 0 := by
    intro index
    have directionNe :
        wz1PaperDirection (direct.coarse.tube index) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm (direct.coarse.tube index)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [distance, wz1PaperLineDistance,
      InnerProductGeometry.angle_self directionNe]
  let net :=
    Classical.choice <|
      wz2_finite_maximal_quotient_net
        direct.coarse.card direct.coarse_nonempty
        distance distanceSymmetric distanceSelf
        (requested.1 / 4) (by positivity)
  let parentFamily :
      Kakeya.Streamlined.TubeFamily (19 * requested.1) :=
    pureWZ2DirectScaleParentFamily direct requested net
  let centerFamily :
      Kakeya.Streamlined.TubeFamily (requested.1 / 4) :=
    pureWZ2DirectScaleCenterFamily direct requested net
  have centerLine : WZ1PaperIsLineClass centerFamily := by
    intro parent
    exact
      wz2PaperCenteredLineTube_lineClass
        (direct.section6Cover.coarse_line_class
          (net.centerEmbedding parent))
  have centerDistinct : WZ1PaperIsEssentiallyDistinct centerFamily := by
    intro first second hne
    change
      requested.1 / 4 <
        wz1PaperLineDistance
          (wz2PaperCenteredLineTube
            (direct.coarse.tube (net.centerEmbedding first)))
          (wz2PaperCenteredLineTube
            (direct.coarse.tube (net.centerEmbedding second)))
    rw [wz1PaperLineDistance_centeredLineTube_both
      (direct.section6Cover.coarse_line_class
        (net.centerEmbedding first))
      (direct.section6Cover.coarse_line_class
        (net.centerEmbedding second))]
    exact net.centers_separated first second hne
  have conflictDegree :
      ∀ fixed : Fin net.centers.card,
        (Finset.univ.filter fun other =>
          other ≠ fixed ∧
            (wz2PaperOrdinaryDilatedFiberIndices
                2 direct.coarse parentFamily fixed ∩
              wz2PaperOrdinaryDilatedFiberIndices
                2 direct.coarse parentFamily other).Nonempty).card ≤
          pureWZ2DirectScaleConflictDegree := by
    intro fixed
    let conflicts :=
      Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 direct.coarse parentFamily fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 direct.coarse parentFamily other).Nonempty
    have conflictLineDistance :
        ∀ other ∈ conflicts,
          wz1PaperLineDistance
              (centerFamily.tube other)
              (centerFamily.tube fixed) ≤
            2280 * requested.1 := by
      intro other hother
      rcases (Finset.mem_filter.mp hother).2.2 with
        ⟨source, hsource⟩
      rcases Finset.mem_inter.mp hsource with
        ⟨hfixed, hother'⟩
      rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        at hfixed hother'
      have firstDistance :=
        wz2_paper_bounded_centered_doubled_containment_lineDistance_le
          callerPos (mul_pos (by norm_num) requestedPos)
          (direct.section6Cover.coarse_line_class source)
          (by
            change WZ1PaperTubeInLineClass
              (wz2PaperCenteredLineTube
                (direct.coarse.tube (net.centerEmbedding fixed)))
            exact
              wz2PaperCenteredLineTube_lineClass
                (direct.section6Cover.coarse_line_class
                  (net.centerEmbedding fixed)))
          1 (direct.midpoint_local source) hfixed
      have secondDistance :=
        wz2_paper_bounded_centered_doubled_containment_lineDistance_le
          callerPos (mul_pos (by norm_num) requestedPos)
          (direct.section6Cover.coarse_line_class source)
          (by
            change WZ1PaperTubeInLineClass
              (wz2PaperCenteredLineTube
                (direct.coarse.tube (net.centerEmbedding other)))
            exact
              wz2PaperCenteredLineTube_lineClass
                (direct.section6Cover.coarse_line_class
                  (net.centerEmbedding other)))
          1 (direct.midpoint_local source) hother'
      have triangle :=
        wz1PaperLineDistance_triangle
          (parentFamily.tube other)
          (direct.coarse.tube source)
          (parentFamily.tube fixed)
      have symmetry :
          wz1PaperLineDistance
              (parentFamily.tube other)
              (direct.coarse.tube source) =
            wz1PaperLineDistance
              (direct.coarse.tube source)
              (parentFamily.tube other) :=
        wz1PaperLineDistance_symm _ _
      rw [symmetry] at triangle
      have raw :
          wz1PaperLineDistance
              (parentFamily.tube other)
              (parentFamily.tube fixed) ≤
            2 * ((16 * 1 + 44) * (19 * requested.1)) := by
        linarith
      have hsame :
          wz1PaperLineDistance
              (parentFamily.tube other)
              (parentFamily.tube fixed) =
            wz1PaperLineDistance
              (centerFamily.tube other)
              (centerFamily.tube fixed) := by
        change
          wz1PaperLineDistance
              (wz2PaperCenteredLineTube
                (direct.coarse.tube (net.centerEmbedding other)))
              (wz2PaperCenteredLineTube
                (direct.coarse.tube (net.centerEmbedding fixed))) =
            wz1PaperLineDistance
              (wz2PaperCenteredLineTube
                (direct.coarse.tube (net.centerEmbedding other)))
              (wz2PaperCenteredLineTube
                (direct.coarse.tube (net.centerEmbedding fixed)))
        rfl
      rw [← hsame]
      convert raw using 1 <;> ring
    have packing :=
      tube_packing_bound_general
        centerDistinct centerLine
        (by positivity : 0 < requested.1 / 4)
        (2280 * requested.1) (by positivity) fixed
    have ceilEq :
        Nat.ceil
            (8 * (2280 * requested.1) /
              (requested.1 / 4)) =
          72960 := by
      have algebra :
          8 * (2280 * requested.1) /
              (requested.1 / 4) =
            72960 := by
        field_simp [requestedPos.ne']
        ring
      rw [algebra]
      norm_num
    rw [ceilEq] at packing
    have subset :
        conflicts ⊆
          Finset.univ.filter fun other =>
            wz1PaperLineDistance
                (centerFamily.tube other)
                (centerFamily.tube fixed) ≤
              2280 * requested.1 := by
      intro other hother
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, conflictLineDistance other hother⟩
    exact
      (Finset.card_le_card subset).trans <| by
        change
          (Finset.univ.filter fun j =>
            wz1PaperLineDistance
                (centerFamily.tube j)
                (centerFamily.tube fixed) ≤
              2280 * requested.1).card ≤
            pureWZ2DirectScaleConflictDegree
        simpa [pureWZ2DirectScaleConflictDegree] using packing
  exact
    ⟨{
      net := net
      owner_containment :=
        pureWZ2_direct_scale_owner_containment
          direct requested net
      parent_line_class := by
        intro parent
        exact
          wz2PaperCenteredLineTube_lineClass
            (direct.section6Cover.coarse_line_class
              (net.centerEmbedding parent))
      parent_midpoint_local := by
        intro parent
        exact
          wz2PaperCenteredLineTube_midpoint_norm_le_one
            (direct.section6Cover.coarse_line_class
              (net.centerEmbedding parent))
      center_distinct := centerDistinct
      conflict_degree := conflictDegree
    }⟩

end Kakeya.Assouad

end
