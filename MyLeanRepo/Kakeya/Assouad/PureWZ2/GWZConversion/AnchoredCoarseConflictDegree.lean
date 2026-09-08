import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ActiveParentGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.OneScaleAnchoredOwnerCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ParametricMidpointBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ProjectiveDirectionTriangle
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness

/-!
# Anchored coarse-parent conflict degree

For the one-scale active-parent cover, bound the doubled-fiber conflict graph
by a constant depending only on the fixed dilation.  The packing is performed
on the original essentially-distinct GWZ parents.  Canonical parent
reanchoring changes only the longitudinal midpoint parameter, and active
parent geometry bounds that translation.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas

attribute [local instance] Classical.propDecidable

private theorem pureWZ2_point3_coord_le_norm
    (vector : Point3) (coordinate : Fin 3) :
    |vector coordinate| ≤ ‖vector‖ := by
  have hsum :
      0 ≤ vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2 := by
    positivity
  have hsqrt :
      ‖vector‖ =
        Real.sqrt
          (vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    congr 1
    ring
  have hnorm :
      ‖vector‖ ^ 2 =
        vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2 := by
    rw [hsqrt, Real.sq_sqrt hsum]
  have hcoordinate :
      vector coordinate ^ 2 ≤ ‖vector‖ ^ 2 := by
    rw [hnorm]
    fin_cases coordinate <;>
      simp <;> ring_nf <;>
      nlinarith [sq_nonneg (vector 0),
        sq_nonneg (vector 1), sq_nonneg (vector 2)]
  calc
    |vector coordinate| =
        Real.sqrt (vector coordinate ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (‖vector‖ ^ 2) :=
      Real.sqrt_le_sqrt hcoordinate
    _ = ‖vector‖ := by
      rw [Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg vector)]

private theorem pureWZ2_affine_midpoint
    (equivalence : Point3 ≃ᵃⁱ[ℝ] Point3)
    (base direction : Point3) :
    equivalence (base + (1 / 2 : ℝ) • direction) =
      equivalence base +
        (1 / 2 : ℝ) •
          equivalence.linearIsometryEquiv direction := by
  have hmap :=
    equivalence.map_vadd base ((1 / 2 : ℝ) • direction)
  rw [equivalence.linearIsometryEquiv.map_smul] at hmap
  simpa [vadd_eq_add, add_comm] using hmap

private theorem pureWZ2_abs_add_mul_sub_le
    (first coefficient innerCoefficient last : ℝ)
    (hinner : |innerCoefficient| ≤ 1) :
    |first + coefficient * innerCoefficient - last| ≤
      |first| + |coefficient| * 1 + |last| := by
  calc
    _ = |first + coefficient * innerCoefficient + (-last)| := by
      simp only [sub_eq_add_neg]
    _ ≤
        |first| + |coefficient * innerCoefficient| + |-last| :=
      abs_add_three _ _ _
    _ =
        |first| + |coefficient| * |innerCoefficient| + |last| := by
      rw [abs_neg, abs_mul]
    _ ≤ |first| + |coefficient| * 1 + |last| := by
      gcongr

private theorem pureWZ2_transverse_norm_of_frame_coordinates
    (linear : Point3 ≃ₗᵢ[ℝ] Point3)
    (reference : Point3)
    (hreference :
      linear reference = EuclideanSpace.single 2 1)
    (vector : Point3)
    {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hzero : |(linear vector) 0| ≤ bound)
    (hone : |(linear vector) 1| ≤ bound) :
    ‖vector - inner ℝ vector reference • reference‖ ≤
      2 * bound := by
  let transformed :=
    linear
      (vector - inner ℝ vector reference • reference)
  have htransformed :
      transformed =
        linear vector -
          inner ℝ (linear vector) (linear reference) •
            linear reference := by
    dsimp only [transformed]
    rw [linear.map_sub, linear.map_smul,
      linear.inner_map_map]
  have hcoordinateZero :
      transformed 0 = (linear vector) 0 := by
    rw [htransformed, hreference]
    simp [EuclideanSpace.single, Pi.sub_apply,
      Pi.smul_apply]
  have hcoordinateOne :
      transformed 1 = (linear vector) 1 := by
    rw [htransformed, hreference]
    simp [EuclideanSpace.single, Pi.sub_apply,
      Pi.smul_apply]
  have hcoordinateTwo :
      transformed 2 = 0 := by
    rw [htransformed, hreference]
    have hinner :
        inner ℝ (linear vector)
            (EuclideanSpace.single 2 1 : Point3) =
          (linear vector) 2 := by
      simpa using
        EuclideanSpace.inner_single_right
          (2 : Fin 3) (1 : ℝ) (linear vector)
    rw [hinner]
    simp [EuclideanSpace.single, Pi.sub_apply,
      Pi.smul_apply]
  have hnormSquared :
      ‖transformed‖ ^ 2 =
        transformed 0 ^ 2 +
          transformed 1 ^ 2 +
            transformed 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hzeroSquared :
      transformed 0 ^ 2 ≤ bound ^ 2 := by
    rw [hcoordinateZero]
    apply sq_le_sq.mpr
    simpa [abs_of_nonneg hbound] using hzero
  have honeSquared :
      transformed 1 ^ 2 ≤ bound ^ 2 := by
    rw [hcoordinateOne]
    apply sq_le_sq.mpr
    simpa [abs_of_nonneg hbound] using hone
  have hnorm :
      ‖transformed‖ ≤ 2 * bound := by
    have hnormBound :
        ‖transformed‖ ^ 2 ≤ (2 * bound) ^ 2 := by
      rw [hnormSquared, hcoordinateTwo]
      nlinarith
    nlinarith [norm_nonneg transformed]
  rw [show ‖transformed‖ =
      ‖vector - inner ℝ vector reference • reference‖ by
    exact linear.norm_map _] at hnorm
  exact hnorm

private theorem pureWZ2_oriented_midpoint
    {rho : ℝ}
    (reference : Point3)
    (tube : Kakeya.DeltaTube rho) :
    wz2PaperTubeMidpoint
        (pureWZ2OrientedParent reference tube) =
      wz2PaperTubeMidpoint tube :=
  pureWZ2OrientedParent_midpoint reference tube

/-- A scale-independent degree bound for the anchored coarse conflict graph. -/
def pureWZ2AnchoredCoarseConflictDegree (A : ℝ) : ℕ :=
  let shiftBound := A / 2 + 1
  let transverseCoefficient :=
    (40 + 16 * shiftBound) * (8 * A)
  let longitudinalBound := A + 5
  let directionConstant := 128 * A
  (2 * Nat.ceil
      (200 * transverseCoefficient) + 1) ^ 2 *
    (2 * Nat.ceil
      ((400 * max directionConstant 16) *
        longitudinalBound) + 1) *
    (2 * Nat.ceil (200 * directionConstant) + 1) ^ 2

/--
The doubled-fiber overlap graph of one active anchored owner cover has
uniformly bounded degree.
-/
theorem pureWZ2_anchored_coarse_conflict_degree
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (hfineRadius : fine.radius ≤ 1 / 4)
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A))
    (oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData) :
    ∀ fixed : Fin oneScale.coarse.card,
      (Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 fine.family oneScale.coarse fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 fine.family oneScale.coarse other).Nonempty).card ≤
        pureWZ2AnchoredCoarseConflictDegree A := by
  let rho := scale.1
  let anchoredScale := 8 * A * rho
  let shiftBound := A / 2 + 1
  let transverseBound :=
    (40 + 16 * shiftBound) * anchoredScale
  let longitudinalBound := A + 5
  let directionConstant := 128 * A
  intro fixed
  let conflicting : Finset (Fin oneScale.coarse.card) :=
    Finset.univ.filter fun other =>
      other ≠ fixed ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 fine.family oneScale.coarse fixed ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 fine.family oneScale.coarse other).Nonempty
  let fixedOriginal :=
    scaleData.coarse.tube
      (oneScale.originalParent fixed)
  let original (index : Fin oneScale.coarse.card) :=
    scaleData.coarse.tube
      (oneScale.originalParent index)
  let oriented (index : Fin oneScale.coarse.card) :=
    pureWZ2OrientedParent fixedOriginal.direction
      (original index)
  have hrho : 0 < rho := by
    have := scale.property.1
    linarith
  have hrhoSmall : rho ≤ 1 / 100 := by
    have hApos : 0 < A := by linarith
    calc
      rho ≤ 1 / (200 * A) := hscaleSmall
      _ ≤ 1 / 200 := by
        apply one_div_le_one_div_of_le
        · norm_num
        · nlinarith
      _ ≤ 1 / 100 := by norm_num
  have hanchoredScale : 0 < anchoredScale := by
    dsimp only [anchoredScale]
    positivity
  have hanchoredSmall :
      anchoredScale ≤ 1 / 20 := by
    dsimp only [anchoredScale]
    have hApos : 0 < A := by linarith
    calc
      8 * A * rho ≤ 8 * A * (1 / (200 * A)) := by
        gcongr
      _ = 1 / 25 := by
        field_simp [hApos.ne']
        norm_num
      _ ≤ 1 / 20 := by norm_num
  have hdeltaAnchored :
      delta ≤ anchoredScale := by
    have hdeltaRho := scale.property.1
    have hrhoAnchored : rho ≤ anchoredScale := by
      dsimp only [anchoredScale]
      nlinarith
    exact hdeltaRho.trans hrhoAnchored
  have horiginalDistinct :
      ∀ first second,
        first ∈ insert fixed conflicting →
        second ∈ insert fixed conflicting →
        first ≠ second →
        (oriented first).EssentiallyDistinct
          (oriented second) := by
    intro first second _ _ hne
    apply pureWZ2OrientedParent_distinct
    exact scaleData.coarse_distinct
      (oneScale.originalParent first)
      (oneScale.originalParent second)
      (fun heq => hne
        (oneScale.originalParent.injective heq))
  have hfixedOriented :
      oriented fixed = fixedOriginal := by
    dsimp only [oriented, original, fixedOriginal,
      pureWZ2OrientedParent]
    rw [if_pos]
    rw [real_inner_self_eq_norm_sq,
      (scaleData.coarse.tube
        (oneScale.originalParent fixed)).direction_unit]
    norm_num
  have hconflictWitness :
      ∀ other ∈ conflicting,
        ∃ child : Fin fine.family.card,
          (fine.family.tube child).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2
              (oneScale.coarse.tube fixed) ∧
          (fine.family.tube child).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2
              (oneScale.coarse.tube other) := by
    intro other hother
    have hoverlap :=
      (Finset.mem_filter.mp hother).2.2
    rcases hoverlap with ⟨child, hchild⟩
    exact
      ⟨child,
        (mem_wz2PaperOrdinaryDilatedFiberIndices_iff
          fixed child).mp (Finset.mem_inter.mp hchild).1,
        (mem_wz2PaperOrdinaryDilatedFiberIndices_iff
          other child).mp (Finset.mem_inter.mp hchild).2⟩
  choose child hchildFixed hchildOther using hconflictWitness
  have hdirectionProjective :
      ∀ other ∈ conflicting,
        ‖(original other).direction -
            inner ℝ (original other).direction
                fixedOriginal.direction •
              fixedOriginal.direction‖ ≤
          16 * anchoredScale := by
    intro other hother
    let childTube := fine.family.tube (child other hother)
    let fixedAnchored := oneScale.coarse.tube fixed
    let otherAnchored := oneScale.coarse.tube other
    have hchildFixedDirection :
        ‖childTube.direction -
            inner ℝ childTube.direction
                fixedAnchored.direction •
              fixedAnchored.direction‖ ≤
          4 * anchoredScale := by
      exact
        (gwz_direction_constraint
          hdelta hanchoredScale
          (show (1 : ℝ) ≤ 2 by norm_num)
          (by linarith)
          childTube fixedAnchored
          (hchildFixed other hother)).trans
          (by linarith)
    have hchildOtherDirection :
        ‖childTube.direction -
            inner ℝ childTube.direction
                otherAnchored.direction •
              otherAnchored.direction‖ ≤
          4 * anchoredScale := by
      exact
        (gwz_direction_constraint
          hdelta hanchoredScale
          (show (1 : ℝ) ≤ 2 by norm_num)
          (by linarith)
          childTube otherAnchored
          (hchildOther other hother)).trans
          (by linarith)
    have htriangle :=
      pureWZ2_projective_direction_triangle
        fixedAnchored.direction_unit
        otherAnchored.direction_unit
        childTube.direction_unit
        (show 0 ≤ 4 * anchoredScale by positivity)
        (by linarith [hanchoredSmall])
        hchildFixedDirection hchildOtherDirection
    dsimp only [fixedAnchored, otherAnchored] at htriangle
    rw [oneScale.tube_eq_reanchored_parent,
      oneScale.tube_eq_reanchored_parent] at htriangle
    change
      ‖(original other).direction -
          inner ℝ (original other).direction
              fixedOriginal.direction •
            fixedOriginal.direction‖ ≤
        16 * anchoredScale
    simp only [pureWZ2ReanchoredParentTube_direction] at htriangle
    dsimp only [original, fixedOriginal]
    convert htriangle using 1 <;> ring
  have hdirectionOriented :
      ∀ other ∈ conflicting,
        ‖(oriented other).direction -
            inner ℝ (oriented other).direction
                (oriented fixed).direction •
              (oriented fixed).direction‖ ≤
          directionConstant * rho := by
    intro other hother
    rw [hfixedOriented,
      pureWZ2OrientedParent_transverse]
    have h := hdirectionProjective other hother
    dsimp only [directionConstant, anchoredScale]
    nlinarith
  have hpositiveDirection :
      ∀ other ∈ conflicting,
        inner ℝ (oriented other).direction
            (oriented fixed).direction ≥
          1 / 2 := by
    intro other hother
    rw [hfixedOriented]
    rw [pureWZ2OrientedParent_inner_eq_abs]
    let coefficient :=
      inner ℝ (original other).direction
        fixedOriginal.direction
    have htransverse := hdirectionProjective other hother
    have hnorm :
        ‖(original other).direction -
            coefficient • fixedOriginal.direction‖ ^ 2 =
          1 - coefficient ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right,
        norm_smul, (original other).direction_unit,
        fixedOriginal.direction_unit]
      simp [coefficient, Real.norm_eq_abs, sq_abs]
      ring
    have hsquared :
        ‖(original other).direction -
            coefficient • fixedOriginal.direction‖ ^ 2 ≤
          (16 * anchoredScale) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        htransverse
    have hcoefficient :
        (1 / 2 : ℝ) ^ 2 ≤ coefficient ^ 2 := by
      rw [hnorm] at hsquared
      nlinarith [hanchoredSmall]
    change 1 / 2 ≤ |coefficient|
    nlinarith [sq_abs coefficient,
      abs_nonneg coefficient]
  have hactiveShift :
      ∀ index : Fin oneScale.coarse.card,
        |pureWZ2AxialShift fine.center (original index)| ≤
          shiftBound := by
    intro index
    rcases oneScale.cover.parent_surjective index with
      ⟨fineIndex, hfineIndex⟩
    rcases fine.source_meets_ball fineIndex with
      ⟨point, hpointShading, hpointBall⟩
    have hpointSource :
        point ∈
          (source.tube
            (fine.sourceIndex fineIndex)).carrier :=
      sourceShading.subset_body
        (fine.sourceIndex fineIndex) hpointShading
    have howner :
        oneScale.owner fineIndex =
          oneScale.originalParent index := by
      have horiginal :=
        oneScale.cover_original_owner fineIndex
      rw [hfineIndex] at horiginal
      exact horiginal.symm
    have hcomplete :
        (source.tube
          (fine.sourceIndex fineIndex)).carrier ⊆
          wz2PaperCenteredDilatedCarrier A
            (original index) := by
      have hmember := oneScale.owner_mem fineIndex
      rw [howner, scaleData.fullFiberIndices_eq] at hmember
      exact (Finset.mem_filter.mp hmember).2
    have hshift :=
      pureWZ2_active_parent_axial_shift
        hdelta hrho hA hpointSource hpointBall hcomplete
    dsimp only [shiftBound]
    have hArho : A * rho ≤ 1 / 200 := by
      have hApos : 0 < A := by linarith
      calc
        A * rho ≤ A * (1 / (200 * A)) := by
          gcongr
        _ = 1 / 200 := by
          field_simp [hApos.ne']
    have hdeltaSmall : delta ≤ 1 / 200 :=
      scale.property.1.trans
        ((show rho ≤ A * rho by nlinarith).trans hArho)
    linarith [fine.radius_pos, hfineRadius]
  rcases frame_of_axis fixedOriginal.direction
      fixedOriginal.direction_unit with
    ⟨_, _, frame, hframeTwo, hframeZero, hframeOne⟩
  let linear := frame.symm.linearIsometryEquiv
  have hlinearFixed :
      linear fixedOriginal.direction =
        EuclideanSpace.single 2 1 := by
    ext coordinate
    fin_cases coordinate
    · simpa [linear, EuclideanSpace.single] using hframeZero
    · simpa [linear, EuclideanSpace.single] using hframeOne
    · simpa [linear, EuclideanSpace.single] using hframeTwo
  let anchoredMidpoint (index : Fin oneScale.coarse.card) :=
    wz2PaperTubeMidpoint (oneScale.coarse.tube index)
  let transformedDirection (index : Fin oneScale.coarse.card) :=
    linear (oneScale.coarse.tube index).direction
  have hanchoredBounds :
      ∀ other ∈ conflicting,
        |(linear
            (anchoredMidpoint other -
              anchoredMidpoint fixed)) 0| ≤
            20 * anchoredScale ∧
        |(linear
            (anchoredMidpoint other -
              anchoredMidpoint fixed)) 1| ≤
            20 * anchoredScale ∧
        |(linear
            (anchoredMidpoint other -
              anchoredMidpoint fixed)) 2| ≤
            2 + 4 * anchoredScale := by
    intro other hother
    let fixedTube := oneScale.coarse.tube fixed
    let otherTube := oneScale.coarse.tube other
    let childTube := fine.family.tube (child other hother)
    let pFixed := frame.symm fixedTube.base
    let fixedDirection := linear fixedTube.direction
    let mFixed := frame.symm
      (wz2PaperTubeMidpoint fixedTube)
    let otherDirection := linear otherTube.direction
    let mOther := frame.symm
      (wz2PaperTubeMidpoint otherTube)
    have hfixedDirection :
        fixedDirection = EuclideanSpace.single 2 1 := by
      dsimp only [fixedDirection, fixedTube]
      rw [oneScale.tube_eq_reanchored_parent]
      exact hlinearFixed
    have hotherDirection :
        |otherDirection 0| ≤ 16 * anchoredScale ∧
        |otherDirection 1| ≤ 16 * anchoredScale := by
      have hnorm := hdirectionProjective other hother
      have hmap :
          ‖linear
            ((original other).direction -
              inner ℝ (original other).direction
                fixedOriginal.direction •
                fixedOriginal.direction)‖ ≤
            16 * anchoredScale := by
        rw [linear.norm_map]
        exact hnorm
      have hvector :
          linear
            ((original other).direction -
              inner ℝ (original other).direction
                fixedOriginal.direction •
                fixedOriginal.direction) =
            otherDirection -
              inner ℝ otherDirection fixedDirection •
                fixedDirection := by
        dsimp only [otherDirection, fixedDirection]
        rw [linear.map_sub, linear.map_smul,
          linear.inner_map_map]
        dsimp only [otherTube, fixedTube]
        rw [oneScale.tube_eq_reanchored_parent,
          oneScale.tube_eq_reanchored_parent]
        simp only [pureWZ2ReanchoredParentTube_direction,
          original, fixedOriginal]
      rw [hvector] at hmap
      rw [hfixedDirection] at hmap
      constructor
      · have hcoord := pureWZ2_point3_coord_le_norm
          (otherDirection -
            inner ℝ otherDirection
              (EuclideanSpace.single 2 1 : Point3) •
              EuclideanSpace.single 2 1) 0
        have heq :
            (otherDirection -
              inner ℝ otherDirection
                (EuclideanSpace.single 2 1 : Point3) •
                EuclideanSpace.single 2 1).ofLp 0 =
              otherDirection 0 := by
          simp [EuclideanSpace.single,
            Pi.sub_apply, Pi.smul_apply]
        rw [heq] at hcoord
        exact hcoord.trans hmap
      · have hcoord := pureWZ2_point3_coord_le_norm
          (otherDirection -
            inner ℝ otherDirection
              (EuclideanSpace.single 2 1 : Point3) •
              EuclideanSpace.single 2 1) 1
        have heq :
            (otherDirection -
              inner ℝ otherDirection
                (EuclideanSpace.single 2 1 : Point3) •
                EuclideanSpace.single 2 1).ofLp 1 =
              otherDirection 1 := by
          simp [EuclideanSpace.single,
            Pi.sub_apply, Pi.smul_apply]
        rw [heq] at hcoord
        exact hcoord.trans hmap
    have hraw :=
      parametric_midpoint_bounds
        hdelta hanchoredScale
        (show (1 : ℝ) ≤ 2 by norm_num)
        (by linarith [hanchoredSmall])
        (by linarith)
        (hchildFixed other hother)
        (hchildOther other hother)
        frame
        pFixed fixedDirection mFixed
        otherDirection mOther
        rfl rfl
        (by simpa [hfixedDirection, EuclideanSpace.single])
        (by simpa [hfixedDirection, EuclideanSpace.single])
        (by simpa [hfixedDirection, EuclideanSpace.single])
        (by
          dsimp only [mFixed, pFixed]
          rw [wz2PaperTubeMidpoint]
          exact pureWZ2_affine_midpoint frame.symm
            fixedTube.base fixedTube.direction)
        rfl
        (by
          dsimp only [mOther]
          rw [wz2PaperTubeMidpoint]
          exact pureWZ2_affine_midpoint frame.symm
            otherTube.base otherTube.direction)
        (16 * anchoredScale) (by positivity)
        hotherDirection.1 hotherDirection.2
    have hmidMap :
        linear
            (anchoredMidpoint other -
              anchoredMidpoint fixed) =
          mOther - mFixed := by
      dsimp only [anchoredMidpoint, mOther, mFixed, linear]
      simpa [vsub_eq_sub] using
        (frame.symm.map_vsub
          (wz2PaperTubeMidpoint
            (oneScale.coarse.tube other))
          (wz2PaperTubeMidpoint
            (oneScale.coarse.tube fixed)))
    rw [hmidMap]
    constructor
    · linarith [hraw.1]
    constructor
    · linarith [hraw.2.1]
    · norm_num at hraw
      exact hraw.2.2
  have horiginalMidpoint :
      ∀ index,
        wz2PaperTubeMidpoint (original index) =
          anchoredMidpoint index +
            pureWZ2AxialShift fine.center
              (original index) •
              (original index).direction := by
    intro index
    dsimp only [anchoredMidpoint, original]
    rw [oneScale.tube_eq_reanchored_parent,
      pureWZ2ReanchoredParentTube_midpoint]
    simpa [pureWZ2ReanchoredTube_midpoint] using
      pureWZ2ReanchoredTube_source_midpoint
        fine.center
        (scaleData.coarse.tube
          (oneScale.originalParent index))
  have hmidTransverse :
      ∀ other ∈ conflicting,
        ‖(wz2PaperTubeMidpoint (oriented other) -
              wz2PaperTubeMidpoint (oriented fixed)) -
            inner ℝ
                (wz2PaperTubeMidpoint (oriented other) -
                  wz2PaperTubeMidpoint (oriented fixed))
                (oriented fixed).direction •
              (oriented fixed).direction‖ ≤
          transverseBound := by
    intro other hother
    rw [pureWZ2OrientedParent_midpoint,
      pureWZ2OrientedParent_midpoint,
      hfixedOriented]
    let anchoredDifference :=
      anchoredMidpoint other - anchoredMidpoint fixed
    have hanchoredTransverse :
        ‖anchoredDifference -
            inner ℝ anchoredDifference
                fixedOriginal.direction •
              fixedOriginal.direction‖ ≤
          40 * anchoredScale := by
      have hbound :=
        pureWZ2_transverse_norm_of_frame_coordinates
          linear fixedOriginal.direction hlinearFixed
          anchoredDifference
          (show 0 ≤ 20 * anchoredScale by positivity)
          (hanchoredBounds other hother).1
          (hanchoredBounds other hother).2.1
      nlinarith
    have hdecomposition :
        wz2PaperTubeMidpoint (original other) -
            wz2PaperTubeMidpoint (original fixed) =
          anchoredDifference +
            pureWZ2AxialShift fine.center
                (original other) •
              (original other).direction -
            pureWZ2AxialShift fine.center
                (original fixed) •
              fixedOriginal.direction := by
      rw [horiginalMidpoint other,
        horiginalMidpoint fixed]
      dsimp only [anchoredDifference, fixedOriginal]
      abel
    rw [hdecomposition, inner_sub_left,
      inner_add_left, real_inner_smul_left,
      real_inner_smul_left,
      real_inner_self_eq_norm_sq,
      fixedOriginal.direction_unit]
    norm_num
    have hfixedCancels :
        -pureWZ2AxialShift fine.center
              (original fixed) •
            fixedOriginal.direction -
          (-pureWZ2AxialShift fine.center
              (original fixed)) •
            fixedOriginal.direction = 0 := by
      module
    have hvector :
        (anchoredDifference +
              pureWZ2AxialShift fine.center
                  (original other) •
                (original other).direction -
              pureWZ2AxialShift fine.center
                  (original fixed) •
                fixedOriginal.direction) -
            (inner ℝ anchoredDifference
                fixedOriginal.direction +
              pureWZ2AxialShift fine.center
                  (original other) *
                inner ℝ (original other).direction
                  fixedOriginal.direction -
              pureWZ2AxialShift fine.center
                  (original fixed)) •
              fixedOriginal.direction =
          (anchoredDifference -
            inner ℝ anchoredDifference
                fixedOriginal.direction •
              fixedOriginal.direction) +
          pureWZ2AxialShift fine.center
              (original other) •
            ((original other).direction -
              inner ℝ (original other).direction
                  fixedOriginal.direction •
                fixedOriginal.direction) := by
      module
    rw [hvector]
    calc
      _ ≤
        ‖anchoredDifference -
            inner ℝ anchoredDifference
                fixedOriginal.direction •
              fixedOriginal.direction‖ +
        ‖pureWZ2AxialShift fine.center
              (original other) •
            ((original other).direction -
              inner ℝ (original other).direction
                  fixedOriginal.direction •
                fixedOriginal.direction)‖ :=
        norm_add_le _ _
      _ ≤
          40 * anchoredScale +
            shiftBound * (16 * anchoredScale) := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        · exact hactiveShift other
        · exact hdirectionProjective other hother
      _ = transverseBound := by
        dsimp only [transverseBound]
        ring
  have hmidLongitudinal :
      ∀ other ∈ conflicting,
        |inner ℝ
            (wz2PaperTubeMidpoint (oriented other) -
              wz2PaperTubeMidpoint (oriented fixed))
            (oriented fixed).direction| ≤
          longitudinalBound := by
    intro other hother
    rw [pureWZ2OrientedParent_midpoint,
      pureWZ2OrientedParent_midpoint,
      hfixedOriented]
    have hdecomposition :
        wz2PaperTubeMidpoint (original other) -
            wz2PaperTubeMidpoint (original fixed) =
          (anchoredMidpoint other -
            anchoredMidpoint fixed) +
          pureWZ2AxialShift fine.center
              (original other) •
            (original other).direction -
          pureWZ2AxialShift fine.center
              (original fixed) •
            fixedOriginal.direction := by
      rw [horiginalMidpoint other,
        horiginalMidpoint fixed]
      abel
    have hinner :
        |inner ℝ (original other).direction
            fixedOriginal.direction| ≤ 1 := by
      exact
        (abs_real_inner_le_norm
          (original other).direction
          fixedOriginal.direction).trans
          (by
            rw [(original other).direction_unit,
              fixedOriginal.direction_unit]
            norm_num)
    have hscalar :
        |inner ℝ
              (anchoredMidpoint other -
                anchoredMidpoint fixed)
              fixedOriginal.direction +
            pureWZ2AxialShift fine.center
                (original other) *
              inner ℝ (original other).direction
                fixedOriginal.direction -
            pureWZ2AxialShift fine.center
              (original fixed)| ≤
          |inner ℝ
              (anchoredMidpoint other -
                anchoredMidpoint fixed)
              fixedOriginal.direction| +
            |pureWZ2AxialShift fine.center
                (original other)| * 1 +
            |pureWZ2AxialShift fine.center
              (original fixed)| :=
      pureWZ2_abs_add_mul_sub_le _ _ _ _ hinner
    rw [hdecomposition, inner_sub_left,
      inner_add_left, real_inner_smul_left,
      real_inner_smul_left,
      real_inner_self_eq_norm_sq,
      fixedOriginal.direction_unit]
    norm_num only [one_pow, mul_one]
    calc
      _ ≤
          |inner ℝ
              (anchoredMidpoint other -
                anchoredMidpoint fixed)
              fixedOriginal.direction| +
            |pureWZ2AxialShift fine.center
                (original other)| * 1 +
            |pureWZ2AxialShift fine.center
              (original fixed)| :=
        by simpa only [one_pow, mul_one] using hscalar
    _ ≤
        (2 + 4 * anchoredScale) +
          shiftBound + shiftBound := by
      gcongr
      · have hcoordinate :=
          (hanchoredBounds other hother).2.2
        have hinnerMap :
            inner ℝ
                (anchoredMidpoint other -
                  anchoredMidpoint fixed)
                fixedOriginal.direction =
              (linear
                (anchoredMidpoint other -
                  anchoredMidpoint fixed)) 2 := by
          have hmap :=
            linear.inner_map_map
              (anchoredMidpoint other -
                anchoredMidpoint fixed)
              fixedOriginal.direction
          rw [hlinearFixed] at hmap
          have hsingle :
              inner ℝ
                  (linear
                    (anchoredMidpoint other -
                      anchoredMidpoint fixed))
                  (EuclideanSpace.single 2 1 : Point3) =
                (linear
                  (anchoredMidpoint other -
                    anchoredMidpoint fixed)) 2 := by
            simpa using
              EuclideanSpace.inner_single_right
                (2 : Fin 3) (1 : ℝ)
                (linear
                  (anchoredMidpoint other -
                    anchoredMidpoint fixed))
          linarith
        rw [hinnerMap]
        exact hcoordinate
      · simpa using hactiveShift other
      · exact hactiveShift fixed
    _ ≤ longitudinalBound := by
      dsimp only [longitudinalBound, shiftBound]
      linarith [hanchoredSmall]
  have hdegreeBound :=
    large_scale_packing_bound
      (T := oriented)
      hrho scale.property.2
      (show 0 ≤ transverseBound by positivity)
      (show 0 ≤ longitudinalBound by positivity)
      (show 0 ≤ directionConstant by positivity)
      (insert fixed conflicting)
      (wz2PaperTubeMidpoint (oriented fixed))
      (oriented fixed).direction
      (oriented fixed).direction_unit
      (by
        intro index hindex
        by_cases heq : index = fixed
        · rw [heq]
          have hmidpoint :
              (oriented fixed).base +
                    (1 / 2 : ℝ) • (oriented fixed).direction -
                  wz2PaperTubeMidpoint (oriented fixed) =
                0 := by
            simp [wz2PaperTubeMidpoint]
          rw [hmidpoint]
          simp only [inner_zero_left, zero_smul,
            sub_zero, norm_zero]
          positivity
        · have hmember : index ∈ conflicting := by
            simpa [Finset.mem_insert, heq] using hindex
          exact hmidTransverse index hmember)
      (by
        intro index hindex
        by_cases heq : index = fixed
        · rw [heq]
          have hmidpoint :
              (oriented fixed).base +
                    (1 / 2 : ℝ) • (oriented fixed).direction -
                  wz2PaperTubeMidpoint (oriented fixed) =
                0 := by
            simp [wz2PaperTubeMidpoint]
          rw [hmidpoint]
          simp only [inner_zero_left, abs_zero]
          positivity
        · have hmember : index ∈ conflicting := by
            simpa [Finset.mem_insert, heq] using hindex
          exact hmidLongitudinal index hmember)
      (by
        intro index hindex
        by_cases heq : index = fixed
        · rw [heq]
          have hinner :
              inner ℝ (oriented fixed).direction
                  (oriented fixed).direction = 1 := by
            rw [real_inner_self_eq_norm_sq,
              (oriented fixed).direction_unit]
            norm_num
          rw [hinner]
          rw [one_smul, sub_self, norm_zero]
          positivity
        · have hmember : index ∈ conflicting := by
            simpa [Finset.mem_insert, heq] using hindex
          exact hdirectionOriented index hmember)
      (by
        intro index hindex
        by_cases heq : index = fixed
        · rw [heq]
          rw [real_inner_self_eq_norm_sq,
            (oriented fixed).direction_unit]
          norm_num
        · have hmember : index ∈ conflicting := by
            simpa [Finset.mem_insert, heq] using hindex
          exact hpositiveDirection index hmember)
      horiginalDistinct
      capsule_lower_bound_instantiation
      capsule_upper_bound_instantiation
  have hsubset :
      conflicting ⊆ insert fixed conflicting :=
    Finset.subset_insert fixed conflicting
  have htransverseRatio :
      200 * transverseBound / rho =
        200 *
          ((40 + 16 * (A / 2 + 1)) * (8 * A)) := by
    dsimp only [transverseBound, shiftBound, anchoredScale, rho]
    field_simp [hrho.ne']
    exact mul_inv_cancel₀ hrho.ne'
  rw [htransverseRatio] at hdegreeBound
  simpa only [
    pureWZ2AnchoredCoarseConflictDegree,
    directionConstant, longitudinalBound
  ] using
    (Finset.card_le_card hsubset).trans hdegreeBound

end Kakeya.Assouad

end
