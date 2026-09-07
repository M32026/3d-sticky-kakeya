import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DirectionPacking2D
import MyLeanRepo.Kakeya.Cinematic.Section5.MaximalSeparatedCover

/-!
# Source directional fiber cardinality for WZ2 `prop: sticky`

This is the three-dimensional cardinality estimate used in Step 3 of the
paper.  Definition 2.1(b) controls the number of radius-`delta` covering
tubes in one radius-`delta` direction cap.  A maximal separated net covers
the radius-`rho` direction cap of one caller fiber by at most
`300 * (rho / delta)^2` such caps.
-/

noncomputable section

namespace Kakeya.Assouad

open InnerProductGeometry

attribute [local instance] Classical.propDecidable

private lemma paper_same_scale_cover_parent_injective
    {delta : ℝ}
    (hdelta : 0 < delta)
    {fine coarse : Kakeya.Streamlined.TubeFamily delta}
    (hfineDistinct : WZ1PaperIsEssentiallyDistinct fine)
    (parent : Fin fine.card → Fin coarse.card)
    (parentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube (parent source))) :
    Function.Injective parent := by
  intro first second hparent
  by_contra hne
  have hfirst :=
    parentCovers first
  have hsecond :=
    parentCovers second
  have hsecond' :
      WZ1PaperTubeCovers
        (fine.tube second) (coarse.tube (parent first)) := by
    rw [hparent]
    exact hsecond
  have htriangle :=
    wz1PaperLineDistance_triangle
      (fine.tube first)
      (coarse.tube (parent first))
      (fine.tube second)
  have hsymm :
      wz1PaperLineDistance
          (coarse.tube (parent first)) (fine.tube second) =
        wz1PaperLineDistance
          (fine.tube second) (coarse.tube (parent first)) :=
    wz1PaperLineDistance_symm _ _
  rw [hsymm] at htriangle
  have hle :
      wz1PaperLineDistance
          (fine.tube first) (fine.tube second) ≤ delta := by
    dsimp only [WZ1PaperTubeCovers] at hfirst hsecond'
    linarith
  exact (not_le_of_gt (hfineDistinct first second hne)) hle

private lemma hairbrushAcuteDirectionAngle_le_angle_of_unit
    {first second : Point3}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1) :
    hairbrushAcuteDirectionAngle first second ≤
      InnerProductGeometry.angle first second := by
  have hangle :
      InnerProductGeometry.angle first second =
        Real.arccos (inner ℝ first second) := by
    unfold InnerProductGeometry.angle
    rw [hfirst, hsecond]
    norm_num
  rw [hangle]
  exact min_le_left _ _

/--
Paper Step 3, equation preceding `upperBdWeightOfQ`, in dimension three.

The bound uses only the literal Definition 2.1(b) source condition and one
caller-scale geometric fiber.  The caller cover may be any partitioning
cover; no second regularization or owner selection is involved.
-/
theorem wz2_paper_source_directional_full_fiber_cardinality
    {delta rho sigma loss : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {ambientShading : WZ1PaperTubeShading ambient}
    (source :
      WZ2PaperExactScaleExtremal
        sigma loss ambient ambientShading)
    (selected : Kakeya.Streamlined.TubeSubfamily ambient)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover selected.family coarse)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (hdeltaRho : delta ≤ rho)
    (hrhoHalf : rho ≤ 1 / 2)
    (parent : Fin coarse.card) :
    wz2PaperFullFiberCount selected.family coarse parent ≤
      ENNReal.ofReal (300 * (rho / delta) ^ 2) *
        Kakeya.realRpowENN delta (-loss) := by
  classical
  let deltaScale : Kakeya.Streamlined.AdmissibleScale delta :=
    ⟨delta, le_rfl, source.delta_le_one⟩
  rcases source.multiscale_covering deltaScale with
    ⟨deltaCoarse, deltaCoarseLine, deltaCovers, deltaParallel⟩
  choose ambientDeltaParent ambientDeltaParentCovers using deltaCovers
  let deltaParent : Fin selected.family.card → Fin deltaCoarse.card :=
    fun index => ambientDeltaParent (selected.embedding index)
  have deltaParentCovers :
      ∀ index,
        WZ1PaperTubeCovers
          (selected.family.tube index)
          (deltaCoarse.tube (deltaParent index)) := by
    intro index
    rw [selected.tube_eq]
    exact ambientDeltaParentCovers (selected.embedding index)
  have deltaParentInjective : Function.Injective deltaParent :=
    paper_same_scale_cover_parent_injective
      source.delta_pos
      (by
        intro first second hne
        rw [selected.tube_eq, selected.tube_eq]
        exact
          source.cwa_exact_scales.2.2.1
            (selected.embedding first)
            (selected.embedding second)
            (selected.embedding.injective.ne hne))
      deltaParent deltaParentCovers
  let fiber : Finset (Fin selected.family.card) :=
    wz2PaperFullFiberIndices selected.family coarse parent
  let selectedDelta : Finset (Fin deltaCoarse.card) :=
    fiber.image deltaParent
  have selectedDeltaCard :
      selectedDelta.card = fiber.card := by
    exact Finset.card_image_of_injOn fun _ _ _ _ h =>
      deltaParentInjective h
  let direction : Fin deltaCoarse.card → Point3 :=
    fun index => wz1PaperDirection (deltaCoarse.tube index)
  let directionSet : Finset Point3 :=
    selectedDelta.image direction
  rcases
      Kakeya.Cinematic.exists_maximal_separated_cover
        (S := directionSet) source.delta_pos with
    ⟨centers, centersSubset, centersSeparated, centersCover⟩
  let capSet : Point3 → Finset (Fin deltaCoarse.card) :=
    fun center =>
      selectedDelta.filter fun index =>
        ‖direction index - center‖ ≤ delta
  have centerRepresentative :
      ∀ center ∈ centers,
        ∃ index ∈ selectedDelta, direction index = center := by
    intro center hcenter
    have hmem : center ∈ directionSet :=
      centersSubset hcenter
    simpa [directionSet] using hmem
  have capSetCard :
      ∀ center ∈ centers,
        ((capSet center).card : ENNReal) ≤
          Kakeya.realRpowENN delta (-loss) := by
    intro center hcenter
    rcases centerRepresentative center hcenter with
      ⟨reference, _href, hreference⟩
    have hparallel :=
      deltaParallel
        (deltaCoarse.tube reference)
        (deltaCoarseLine reference)
    have hsubset :
        capSet center ⊆
          Finset.univ.filter fun index =>
            WZ1PaperEssentiallyParallel
              (deltaCoarse.tube index)
              (deltaCoarse.tube reference) := by
      intro index hindex
      have hcap := (Finset.mem_filter.mp hindex).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [capSet, direction, WZ1PaperEssentiallyParallel,
        hreference] using hcap
    have hcardNat :
        (capSet center).card ≤
          (Finset.univ.filter fun index =>
            WZ1PaperEssentiallyParallel
              (deltaCoarse.tube index)
              (deltaCoarse.tube reference)).card :=
      Finset.card_le_card hsubset
    have hcardENN :
        ((capSet center).card : ENNReal) ≤
          ((Finset.univ.filter fun index =>
            WZ1PaperEssentiallyParallel
              (deltaCoarse.tube index)
              (deltaCoarse.tube reference)).card : ENNReal) := by
      exact_mod_cast hcardNat
    exact hcardENN.trans hparallel
  have selectedDeltaCover :
      selectedDelta ⊆
        centers.biUnion capSet := by
    intro index hindex
    have hdirection :
        direction index ∈ directionSet := by
      exact Finset.mem_image.mpr ⟨index, hindex, rfl⟩
    rcases centersCover (direction index) hdirection with
      ⟨center, hcenter, hdist⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨center, hcenter, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hindex, ?_⟩
    simpa [dist_eq_norm] using hdist
  have selectedDeltaCardUpper :
      (selectedDelta.card : ENNReal) ≤
        (centers.card : ENNReal) *
          Kakeya.realRpowENN delta (-loss) := by
    have hcard :
        selectedDelta.card ≤
          ∑ center ∈ centers, (capSet center).card := by
      exact
        (Finset.card_le_card selectedDeltaCover).trans
          Finset.card_biUnion_le
    have hcast :
        (selectedDelta.card : ENNReal) ≤
          ∑ center ∈ centers,
            ((capSet center).card : ENNReal) := by
      exact_mod_cast hcard
    calc
      (selectedDelta.card : ENNReal) ≤
          ∑ center ∈ centers,
            ((capSet center).card : ENNReal) := hcast
      _ ≤
          ∑ _center ∈ centers,
            Kakeya.realRpowENN delta (-loss) :=
        Finset.sum_le_sum fun center hcenter =>
          capSetCard center hcenter
      _ =
          (centers.card : ENNReal) *
            Kakeya.realRpowENN delta (-loss) := by
        simp [Finset.sum_const]
  have centersUnit :
      ∀ center ∈ centers, ‖center‖ = 1 := by
    intro center hcenter
    have hmem : center ∈ directionSet :=
      centersSubset hcenter
    rcases Finset.mem_image.mp hmem with
      ⟨index, _hindex, rfl⟩
    exact wz1PaperDirection_norm _
  have centersPackingSeparated :
      ∀ first ∈ centers, ∀ second ∈ centers,
        first ≠ second →
          2 * delta / Real.pi ≤ dist first second := by
    intro first hfirst second hsecond hne
    have hsep :=
      centersSeparated first hfirst second hsecond hne
    have hcoefficient :
        2 * delta / Real.pi < delta := by
      apply (div_lt_iff₀ Real.pi_pos).2
      nlinarith [Real.pi_gt_three, source.delta_pos]
    exact (le_of_lt hcoefficient).trans (le_of_lt hsep)
  have centersCap :
      ∀ center ∈ centers,
        hairbrushAcuteDirectionAngle
            center (wz1PaperDirection (coarse.tube parent)) ≤
          rho := by
    intro center hcenter
    rcases centerRepresentative center hcenter with
      ⟨deltaIndex, hdeltaIndex, hcenterEq⟩
    rcases Finset.mem_image.mp hdeltaIndex with
      ⟨sourceIndex, hsourceFiber, hdeltaParent⟩
    have hdeltaCover :=
      deltaParentCovers sourceIndex
    have hcallerCover :
        WZ1PaperTubeCovers
          (selected.family.tube sourceIndex)
          (coarse.tube parent) := by
      exact
        (mem_wz2PaperFullFiberIndices_iff
          parent sourceIndex).mp hsourceFiber
    have hdeltaAngle :
        InnerProductGeometry.angle
            (wz1PaperDirection (deltaCoarse.tube deltaIndex))
            (wz1PaperDirection
              (selected.family.tube sourceIndex)) ≤
          delta / 2 := by
      have hangle :
          InnerProductGeometry.angle
              (wz1PaperDirection
                (selected.family.tube sourceIndex))
              (wz1PaperDirection
                (deltaCoarse.tube (deltaParent sourceIndex))) ≤
            delta / 2 := by
        dsimp only [WZ1PaperTubeCovers, wz1PaperLineDistance] at hdeltaCover
        have hdist :
            0 ≤ dist
              (wz1TubeAxisZeroPoint
                (selected.family.tube sourceIndex))
              (wz1TubeAxisZeroPoint
                (deltaCoarse.tube (deltaParent sourceIndex))) :=
          dist_nonneg
        linarith
      simpa only [hdeltaParent, InnerProductGeometry.angle_comm] using
        hangle
    have hcallerAngle :
        InnerProductGeometry.angle
            (wz1PaperDirection
              (selected.family.tube sourceIndex))
            (wz1PaperDirection (coarse.tube parent)) ≤
          rho / 2 := by
      dsimp only [WZ1PaperTubeCovers, wz1PaperLineDistance] at hcallerCover
      have hdist :
          0 ≤ dist
            (wz1TubeAxisZeroPoint
              (selected.family.tube sourceIndex))
            (wz1TubeAxisZeroPoint (coarse.tube parent)) :=
        dist_nonneg
      linarith
    have hangle :
        InnerProductGeometry.angle
            (wz1PaperDirection (deltaCoarse.tube deltaIndex))
            (wz1PaperDirection (coarse.tube parent)) ≤
          rho := by
      calc
        InnerProductGeometry.angle
            (wz1PaperDirection (deltaCoarse.tube deltaIndex))
            (wz1PaperDirection (coarse.tube parent)) ≤
          InnerProductGeometry.angle
              (wz1PaperDirection (deltaCoarse.tube deltaIndex))
              (wz1PaperDirection
                (selected.family.tube sourceIndex)) +
            InnerProductGeometry.angle
              (wz1PaperDirection
                (selected.family.tube sourceIndex))
              (wz1PaperDirection (coarse.tube parent)) :=
          InnerProductGeometry.angle_le_angle_add_angle _ _ _
        _ ≤ rho := by
          linarith
    rw [← hcenterEq]
    exact
      (hairbrushAcuteDirectionAngle_le_angle_of_unit
        (wz1PaperDirection_norm _)
        (wz1PaperDirection_norm _)).trans hangle
  have centersCardReal :
      (centers.card : ℝ) ≤
        300 * (rho / delta) ^ 2 :=
    direction_cap_packing_2d
      (δ := delta) (theta := rho)
      source.delta_pos source.delta_le_one hdeltaRho
      (by linarith) centersUnit centersPackingSeparated
      (wz1PaperDirection (coarse.tube parent))
      (wz1PaperDirection_norm _) centersCap
  have centersCardENN :
      (centers.card : ENNReal) ≤
        ENNReal.ofReal (300 * (rho / delta) ^ 2) := by
    have hnonneg : 0 ≤ 300 * (rho / delta) ^ 2 := by positivity
    have hofReal :=
      ENNReal.ofReal_mono centersCardReal
    simpa [ENNReal.ofReal_natCast, hnonneg] using hofReal
  have hfiberCard :
      wz2PaperFullFiberCount selected.family coarse parent =
        (fiber.card : ENNReal) := by
    rfl
  rw [hfiberCard]
  have hselectedCard :
      (fiber.card : ENNReal) =
        (selectedDelta.card : ENNReal) := by
    exact_mod_cast selectedDeltaCard.symm
  rw [hselectedCard]
  exact selectedDeltaCardUpper.trans (by gcongr)

end Kakeya.Assouad

end
