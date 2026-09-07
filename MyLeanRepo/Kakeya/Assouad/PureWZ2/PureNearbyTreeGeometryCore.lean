import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import Mathlib.Tactic

/-!
# Geometry core for the pure nearby-scale tree

Carrier containment of an ordinary tube controls the Hausdorff distance
between the two unit axis segments.  This is the geometric input needed to
compare independently chosen nearby-scale Definition 2.12 covers.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
If an ordinary `delta`-tube carrier is contained in an ordinary `scale`-tube
carrier, every point of the fine unit segment is within `scale - delta` of
the coarse unit segment.
-/
lemma wz2_pure_segment_hausdorff_from_containment
    {delta scale : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube scale}
    (hdelta : 0 ≤ delta)
    (hscale : 0 ≤ scale)
    (hdeltaScale : delta ≤ scale)
    (hcontain : fine.carrier ⊆ coarse.carrier) :
    ∀ point : Point3,
      point ∈
          Kakeya.unitSegment fine.base fine.direction →
        Metric.infDist point
            (Kakeya.unitSegment
              coarse.base coarse.direction) ≤
          scale - delta := by
  let fineSegment :=
    Kakeya.unitSegment fine.base fine.direction
  let coarseSegment :=
    Kakeya.unitSegment coarse.base coarse.direction
  have coarseSegmentEq :
      coarseSegment =
        segment ℝ coarse.base
          (coarse.base + coarse.direction) := by
    unfold coarseSegment Kakeya.unitSegment
    rw [segment_eq_image]
    congr with parameter
    simp [add_smul, sub_smul]
    abel
  have coarseConvex : Convex ℝ coarseSegment := by
    rw [coarseSegmentEq]
    exact convex_segment _ _
  have coarseCompact : IsCompact coarseSegment := by
    rw [coarseSegmentEq, segment_eq_image]
    have hcontinuous :
        Continuous
          (fun parameter : ℝ =>
            (1 - parameter) • coarse.base +
              parameter •
                (coarse.base + coarse.direction)) := by
      continuity
    exact
      (show IsCompact (Set.Icc (0 : ℝ) 1) from
          isCompact_Icc).image hcontinuous
  have coarseNonempty : coarseSegment.Nonempty := by
    rw [coarseSegmentEq, segment_eq_image]
    exact ⟨coarse.base, 0, by norm_num, by simp⟩
  have coarseComplete : IsComplete coarseSegment :=
    coarseCompact.isComplete
  intro point hpoint
  by_cases hdistance :
      Metric.infDist point coarseSegment ≤ scale - delta
  · exact hdistance
  · rcases
        exists_norm_eq_iInf_of_complete_convex
          coarseNonempty coarseComplete coarseConvex point with
      ⟨closest, hclosest, hclosestIInf⟩
    have infDistIInf :
        Metric.infDist point coarseSegment =
          ⨅ member : coarseSegment,
            dist point member :=
      Metric.infDist_eq_iInf
    have iInfNorm :
        (⨅ member : coarseSegment, dist point member) =
          ⨅ member : coarseSegment,
            ‖point - member‖ := by
      rfl
    have infDistEq :
        Metric.infDist point coarseSegment =
          ‖point - closest‖ := by
      rw [infDistIInf, iInfNorm, hclosestIInf]
    have obtuse :
        ∀ member : Point3,
          member ∈ coarseSegment →
            inner ℝ (point - closest)
                (member - closest) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero
        coarseConvex hclosest).mp hclosestIInf
    let distance : ℝ := ‖point - closest‖
    have distancePositive : 0 < distance := by
      by_contra hnonpositive
      have distanceZero : distance = 0 := by
        linarith [norm_nonneg (point - closest)]
      have infDistZero :
          Metric.infDist point coarseSegment = 0 := by
        rw [infDistEq]
        exact distanceZero
      rw [infDistZero] at hdistance
      linarith [sub_nonneg.mpr hdeltaScale]
    let direction : Point3 :=
      (1 / distance) • (point - closest)
    let displaced : Point3 :=
      point + delta • direction
    have displacedSub :
        displaced - point = delta • direction := by
      dsimp only [displaced]
      abel
    have directionNorm : ‖direction‖ = 1 := by
      dsimp only [direction, distance]
      calc
        ‖(1 / ‖point - closest‖) •
            (point - closest)‖ =
            |1 / ‖point - closest‖| *
              ‖point - closest‖ := by
                rw [norm_smul, Real.norm_eq_abs]
        _ =
            (1 / ‖point - closest‖) *
              ‖point - closest‖ := by
                rw [abs_of_pos]
                exact one_div_pos.mpr distancePositive
        _ = 1 := by
              simpa [one_div] using
                inv_mul_cancel₀
                  (show ‖point - closest‖ ≠ 0 by
                    simpa [distance] using
                      distancePositive.ne')
    have displacedFine : displaced ∈ fine.carrier := by
      have hdist :
          dist displaced point = delta := by
        rw [dist_eq_norm, displacedSub, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hdelta,
          directionNorm]
        ring
      exact
        Metric.mem_cthickening_of_dist_le
          displaced point delta fineSegment hpoint
          (by linarith)
    have displacedCoarse :
        displaced ∈ coarse.carrier :=
      hcontain displacedFine
    have distanceLower :
        ∀ member : Point3,
          member ∈ coarseSegment →
            distance + delta ≤ dist displaced member := by
      intro member hmember
      have hinner :=
        obtuse member hmember
      let sourceVector : Point3 :=
        point - closest
      let memberVector : Point3 :=
        member - closest
      have sourceNorm :
          ‖sourceVector‖ = distance := by
        rfl
      have hinner' :
          inner ℝ sourceVector memberVector ≤ 0 := by
        simpa [sourceVector, memberVector] using hinner
      have vectorEq :
          displaced - member =
            (1 + delta / distance) •
                sourceVector -
              memberVector := by
        dsimp only [displaced, direction, sourceVector,
          memberVector]
        have hsmul :
            delta •
                ((1 / distance) •
                  (point - closest)) =
              (delta / distance) •
                (point - closest) := by
          rw [smul_smul]
          congr 1
          ring
        rw [hsmul]
        have hpoint :
            point =
              (point - closest) + closest := by
          abel
        rw [hpoint]
        simp [add_smul, sub_smul]
        abel
      let scaled : Point3 :=
        (1 + delta / distance) • sourceVector
      let difference : Point3 :=
        scaled - memberVector
      have normSquare :
          ‖difference‖ ^ 2 =
            inner ℝ difference difference :=
        Eq.symm (real_inner_self_eq_norm_sq difference)
      have innerExpand :
          inner ℝ difference difference =
            ‖scaled‖ ^ 2 +
              ‖memberVector‖ ^ 2 -
              2 * inner ℝ scaled memberVector := by
        have h1 :
            inner ℝ
                (scaled - memberVector)
                (scaled - memberVector) =
              inner ℝ scaled
                  (scaled - memberVector) -
                inner ℝ memberVector
                  (scaled - memberVector) := by
          rw [inner_sub_left]
        have h2 :
            inner ℝ scaled
                (scaled - memberVector) =
              inner ℝ scaled scaled -
                inner ℝ scaled memberVector := by
          rw [inner_sub_right]
        have h3 :
            inner ℝ memberVector
                (scaled - memberVector) =
              inner ℝ memberVector scaled -
                inner ℝ memberVector memberVector := by
          rw [inner_sub_right]
        rw [h1, h2, h3,
          real_inner_comm memberVector scaled,
          real_inner_self_eq_norm_sq,
          real_inner_self_eq_norm_sq]
        ring
      have scaledInner :
          inner ℝ scaled memberVector =
            (1 + delta / distance) *
              inner ℝ sourceVector memberVector := by
        simp [scaled, inner_smul_left]
      have scaledNorm :
          ‖scaled‖ = distance + delta := by
        dsimp only [scaled]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg, sourceNorm]
        · field_simp [distancePositive.ne']
        · positivity
      have scaledInnerNonpositive :
          (1 + delta / distance) *
              inner ℝ sourceVector memberVector ≤ 0 := by
        have hcoefficient :
            0 ≤ 1 + delta / distance := by
          positivity
        exact mul_nonpos_of_nonneg_of_nonpos
          hcoefficient hinner'
      have squareLower :
          (distance + delta) ^ 2 ≤
            ‖difference‖ ^ 2 := by
        rw [normSquare, innerExpand, scaledInner,
          scaledNorm]
        nlinarith [norm_nonneg memberVector,
          scaledInnerNonpositive]
      have differenceNormNonnegative :
          0 ≤ ‖difference‖ := norm_nonneg _
      have targetNonnegative :
          0 ≤ distance + delta := by
        positivity
      have hnorm :
          distance + delta ≤ ‖difference‖ := by
        nlinarith
      rw [dist_eq_norm, vectorEq]
      exact hnorm
    have infEDistUpper :
        Metric.infEDist displaced coarseSegment ≤
          ENNReal.ofReal scale := by
      simpa [Kakeya.DeltaTube.carrier,
        Metric.mem_cthickening_iff] using displacedCoarse
    rcases
        coarseCompact.exists_infEDist_eq_edist
          coarseNonempty displaced with
      ⟨member, hmember, hmemberEq⟩
    have memberUpper :
        dist displaced member ≤ scale := by
      have hedistance :
          edist displaced member ≤
            ENNReal.ofReal scale := by
        rw [← hmemberEq]
        exact infEDistUpper
      have hofReal :
          ENNReal.ofReal (dist displaced member) ≤
            ENNReal.ofReal scale := by
        simpa [edist_dist] using hedistance
      exact
        (ENNReal.ofReal_le_ofReal_iff
          (by positivity)).mp hofReal
    have memberLower :
        distance + delta ≤
          dist displaced member :=
      distanceLower member hmember
    have distanceUpper :
        distance + delta ≤ scale :=
      memberLower.trans memberUpper
    have distanceStrict :
        scale - delta < distance := by
      rw [infDistEq] at hdistance
      exact lt_of_not_ge hdistance
    linarith

/-- Extract the value inequality from a minimum on a set. -/
private lemma pureTree_isMinOn_le
    {α β : Type _}
    [Preorder β]
    {function : α → β}
    {source : Set α}
    {minimum point : α}
    (hminimum : IsMinOn function source minimum)
    (hminimumMem : minimum ∈ source)
    (hpointMem : point ∈ source) :
    function minimum ≤ function point := by
  have hglb :
      IsGLB (function '' source) (function minimum) :=
    hminimum.isGLB hminimumMem
  exact hglb.1 ⟨point, hpointMem, rfl⟩

/--
A one-sided Hausdorff bound between two unit segments reverses with loss
three.
-/
lemma wz2_pure_unit_segment_reverse_hausdorff
    (epsilon : ℝ)
    {firstBase secondBase firstDirection secondDirection : Point3}
    (hfirstDirection : ‖firstDirection‖ = 1)
    (hsecondDirection : ‖secondDirection‖ = 1)
    (hepsilon : 0 ≤ epsilon)
    (hforward :
      ∀ point ∈
          Kakeya.unitSegment firstBase firstDirection,
        infDist point
            (Kakeya.unitSegment
              secondBase secondDirection) ≤
          epsilon) :
    ∀ point ∈
        Kakeya.unitSegment secondBase secondDirection,
      infDist point
          (Kakeya.unitSegment
            firstBase firstDirection) ≤
        3 * epsilon := by
  let firstSegment :=
    Kakeya.unitSegment firstBase firstDirection
  let secondSegment :=
    Kakeya.unitSegment secondBase secondDirection
  have secondCompact : IsCompact secondSegment := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  have secondNonempty : secondSegment.Nonempty :=
    ⟨secondBase, ⟨0, by norm_num, by simp⟩⟩
  by_cases hlarge : 1 / 2 ≤ epsilon
  · let firstEndpoint := firstBase
    have firstEndpointMem :
        firstEndpoint ∈ firstSegment :=
      ⟨0, by norm_num, by simp [firstEndpoint]⟩
    have firstEndpointDistance :
        infDist firstEndpoint secondSegment ≤ epsilon :=
      hforward firstEndpoint firstEndpointMem
    have hcontinuous :
        Continuous
          (fun point => dist firstEndpoint point) :=
      continuous_const.dist continuous_id
    rcases
        secondCompact.exists_isMinOn
          secondNonempty hcontinuous.continuousOn with
      ⟨closest, hclosest, hminimum⟩
    have closestEq :
        dist firstEndpoint closest =
          infDist firstEndpoint secondSegment := by
      apply le_antisymm
      · rw [Metric.le_infDist secondNonempty]
        intro point hpoint
        exact
          pureTree_isMinOn_le
            hminimum hclosest hpoint
      · exact Metric.infDist_le_dist_of_mem hclosest
    have closestDistance :
        dist firstEndpoint closest ≤ epsilon := by
      rw [closestEq]
      exact firstEndpointDistance
    intro point hpoint
    have segmentDistance :
        dist point closest ≤ 1 := by
      rcases hpoint with ⟨parameter, hparameter, rfl⟩
      rcases hclosest with
        ⟨closestParameter, hclosestParameter, rfl⟩
      have hdist :
          dist
              (secondBase +
                parameter • secondDirection)
              (secondBase +
                closestParameter • secondDirection) =
            |parameter - closestParameter| := by
        have hsub :
            (secondBase +
                parameter • secondDirection) -
              (secondBase +
                closestParameter • secondDirection) =
            (parameter - closestParameter) •
              secondDirection := by
          simp [sub_smul]
        rw [dist_eq_norm, hsub, norm_smul,
          Real.norm_eq_abs, hsecondDirection]
        ring
      rw [hdist, abs_le]
      constructor <;>
        linarith [hparameter.1, hparameter.2,
          hclosestParameter.1, hclosestParameter.2]
    have pointDistance :
        dist point firstEndpoint ≤ 1 + epsilon := by
      calc
        dist point firstEndpoint ≤
            dist point closest +
              dist closest firstEndpoint :=
          dist_triangle _ _ _
        _ ≤ 1 + epsilon := by
          linarith [closestDistance,
            dist_comm closest firstEndpoint]
    have pointDistance' :
        dist point firstEndpoint ≤ 3 * epsilon := by
      linarith
    exact
      (Metric.infDist_le_dist_of_mem firstEndpointMem).trans
        pointDistance'
  · have hsmall : epsilon < 1 / 2 := by
      linarith
    let firstStart := firstBase
    let firstEnd := firstBase + firstDirection
    have firstStartMem :
        firstStart ∈ firstSegment :=
      ⟨0, by norm_num, by simp [firstStart]⟩
    have firstEndMem :
        firstEnd ∈ firstSegment :=
      ⟨1, by norm_num, by simp [firstEnd]⟩
    have startInf :
        infDist firstStart secondSegment ≤ epsilon :=
      hforward firstStart firstStartMem
    have endInf :
        infDist firstEnd secondSegment ≤ epsilon :=
      hforward firstEnd firstEndMem
    have startContinuous :
        Continuous (fun point => dist firstStart point) :=
      continuous_const.dist continuous_id
    have endContinuous :
        Continuous (fun point => dist firstEnd point) :=
      continuous_const.dist continuous_id
    rcases
        secondCompact.exists_isMinOn secondNonempty
          startContinuous.continuousOn with
      ⟨startClosest, hstartClosest, hstartMinimum⟩
    rcases
        secondCompact.exists_isMinOn secondNonempty
          endContinuous.continuousOn with
      ⟨endClosest, hendClosest, hendMinimum⟩
    have startClosestDistance :
        dist firstStart startClosest ≤ epsilon := by
      have heq :
          dist firstStart startClosest =
            infDist firstStart secondSegment := by
        apply le_antisymm
        · rw [Metric.le_infDist secondNonempty]
          intro point hpoint
          exact
            pureTree_isMinOn_le
              hstartMinimum hstartClosest hpoint
        · exact
            Metric.infDist_le_dist_of_mem hstartClosest
      rw [heq]
      exact startInf
    have endClosestDistance :
        dist firstEnd endClosest ≤ epsilon := by
      have heq :
          dist firstEnd endClosest =
            infDist firstEnd secondSegment := by
        apply le_antisymm
        · rw [Metric.le_infDist secondNonempty]
          intro point hpoint
          exact
            pureTree_isMinOn_le
              hendMinimum hendClosest hpoint
        · exact
            Metric.infDist_le_dist_of_mem hendClosest
      rw [heq]
      exact endInf
    have closestGap :
        1 - 2 * epsilon ≤
          dist startClosest endClosest := by
      have endpointDistance :
          dist firstStart firstEnd = 1 := by
        simp [firstStart, firstEnd, dist_eq_norm,
          hfirstDirection]
      have htriangle :
          dist firstStart firstEnd ≤
            dist firstStart startClosest +
              dist startClosest endClosest +
              dist endClosest firstEnd :=
        dist_triangle4 _ _ _ _
      linarith [endpointDistance,
        startClosestDistance, endClosestDistance,
        dist_comm endClosest firstEnd]
    rcases hstartClosest with
      ⟨startParameter, hstartParameter, rfl⟩
    rcases hendClosest with
      ⟨endParameter, hendParameter, rfl⟩
    let startPoint :=
      secondBase +
        startParameter • secondDirection
    let endPoint :=
      secondBase +
        endParameter • secondDirection
    have parameterGap :
        1 - 2 * epsilon ≤
          |endParameter - startParameter| := by
      have hdist :
          dist startPoint endPoint =
            |endParameter - startParameter| := by
        have hsub :
            endPoint - startPoint =
              (endParameter - startParameter) •
                secondDirection := by
          simp [startPoint, endPoint, sub_smul]
        rw [dist_eq_norm,
          show startPoint - endPoint =
              -(endPoint - startPoint) by
            abel,
          norm_neg, hsub, norm_smul,
          Real.norm_eq_abs, hsecondDirection]
        ring
      simpa [startPoint, endPoint] using
        closestGap.trans_eq hdist
    have parametersDistinct :
        startParameter ≠ endParameter := by
      intro heq
      rw [heq] at parameterGap
      norm_num at parameterGap
      linarith
    intro point hpoint
    rcases hpoint with ⟨parameter, hparameter, rfl⟩
    let currentPoint :=
      secondBase + parameter • secondDirection
    have segmentDistance :
        ∀ firstParameter secondParameter : ℝ,
          firstParameter ≤ secondParameter →
          dist
              (secondBase +
                firstParameter • secondDirection)
              (secondBase +
                secondParameter • secondDirection) =
            secondParameter - firstParameter := by
      intro firstParameter secondParameter hle
      have hsub :
          (secondBase +
              secondParameter • secondDirection) -
            (secondBase +
              firstParameter • secondDirection) =
          (secondParameter - firstParameter) •
            secondDirection := by
        simp [sub_smul]
      rw [dist_eq_norm,
        show
          (secondBase +
              firstParameter • secondDirection) -
            (secondBase +
              secondParameter • secondDirection) =
          -((secondBase +
              secondParameter • secondDirection) -
            (secondBase +
              firstParameter • secondDirection)) by
          abel,
        norm_neg, hsub, norm_smul,
        Real.norm_eq_abs, hsecondDirection,
        abs_of_nonneg (by linarith)]
      ring
    by_cases horder :
        startParameter ≤ endParameter
    · have hstrict :
          startParameter < endParameter :=
        lt_of_le_of_ne horder parametersDistinct
      have hgap :
          1 - 2 * epsilon ≤
            endParameter - startParameter := by
        rw [abs_of_nonneg (by linarith)] at parameterGap
        exact parameterGap
      by_cases hmiddle :
          startParameter ≤ parameter ∧
            parameter ≤ endParameter
      · let coefficient :=
          (parameter - startParameter) /
            (endParameter - startParameter)
        have hdenominator :
            0 < endParameter - startParameter := by
          linarith
        have hcoefficientZero :
            0 ≤ coefficient := by
          exact div_nonneg
            (by linarith [hmiddle.1])
            hdenominator.le
        have hcoefficientOne :
            coefficient ≤ 1 := by
          change
            (parameter - startParameter) /
                (endParameter - startParameter) ≤ 1
          rw [div_le_one hdenominator]
          linarith [hmiddle.2]
        let firstPoint :=
          firstBase + coefficient • firstDirection
        have hfirstPointMem :
            firstPoint ∈ firstSegment :=
          ⟨coefficient,
            ⟨hcoefficientZero, hcoefficientOne⟩,
            by simp [firstPoint]⟩
        have currentInterpolation :
            currentPoint =
              (1 - coefficient) • startPoint +
                coefficient • endPoint := by
          ext coordinate
          dsimp only [currentPoint, startPoint, endPoint,
            coefficient]
          simp only [PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul]
          field_simp [hdenominator.ne']
          ring
        have firstInterpolation :
            firstPoint =
              (1 - coefficient) • firstStart +
                coefficient • firstEnd := by
          simp [firstPoint, firstStart, firstEnd,
            smul_add, add_smul]
          module
        have interpolationDifference :
            (1 - coefficient) • startPoint +
                  coefficient • endPoint -
                ((1 - coefficient) • firstStart +
                  coefficient • firstEnd) =
              (1 - coefficient) •
                  (startPoint - firstStart) +
                coefficient •
                  (endPoint - firstEnd) := by
          module
        have interpolationNorm :
            ‖(1 - coefficient) •
                  (startPoint - firstStart) +
                coefficient •
                  (endPoint - firstEnd)‖ ≤
              (1 - coefficient) *
                  ‖startPoint - firstStart‖ +
                coefficient *
                  ‖endPoint - firstEnd‖ := by
          calc
            _ ≤
                ‖(1 - coefficient) •
                    (startPoint - firstStart)‖ +
                  ‖coefficient •
                    (endPoint - firstEnd)‖ :=
              norm_add_le _ _
            _ =
                (1 - coefficient) *
                    ‖startPoint - firstStart‖ +
                  coefficient *
                    ‖endPoint - firstEnd‖ := by
              rw [norm_smul, norm_smul,
                Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hcoefficientZero,
                abs_of_nonneg
                  (sub_nonneg.mpr hcoefficientOne)]
        have currentDistance :
            dist currentPoint firstPoint ≤ epsilon := by
          rw [currentInterpolation, firstInterpolation,
            dist_eq_norm, interpolationDifference]
          calc
            _ ≤
                (1 - coefficient) *
                    ‖startPoint - firstStart‖ +
                  coefficient *
                    ‖endPoint - firstEnd‖ :=
              interpolationNorm
            _ =
                (1 - coefficient) *
                    dist startPoint firstStart +
                  coefficient *
                    dist endPoint firstEnd := by
              rw [dist_eq_norm, dist_eq_norm]
            _ ≤
                (1 - coefficient) * epsilon +
                  coefficient * epsilon := by
              gcongr
              · simpa [dist_comm, startPoint, firstStart] using
                  startClosestDistance
              · simpa [dist_comm, endPoint, firstEnd] using
                  endClosestDistance
            _ = epsilon := by ring
        exact
          (Metric.infDist_le_dist_of_mem
            hfirstPointMem).trans <| by
              have hmain :
                  dist currentPoint firstPoint ≤
                    3 * epsilon :=
                currentDistance.trans (by linarith)
              simpa [currentPoint] using hmain
      · by_cases hleft : parameter < startParameter
        · have hstartBound :
              startParameter ≤ 2 * epsilon := by
            linarith [hgap, hendParameter.2]
          have hcurrentStart :
              dist currentPoint startPoint =
                startParameter - parameter := by
            exact
              segmentDistance parameter startParameter
                (by linarith)
          have hcurrent :
              dist currentPoint firstStart ≤
                3 * epsilon := by
            calc
              _ ≤
                  dist currentPoint startPoint +
                    dist startPoint firstStart :=
                dist_triangle _ _ _
              _ =
                  (startParameter - parameter) +
                    dist startPoint firstStart := by
                rw [hcurrentStart]
              _ ≤ startParameter + epsilon := by
                have hfirst :
                    startParameter - parameter ≤
                      startParameter := by
                  linarith [hparameter.1]
                have hsecond :
                    dist startPoint firstStart ≤ epsilon := by
                  simpa [dist_comm, startPoint, firstStart] using
                    startClosestDistance
                linarith
              _ ≤ 3 * epsilon := by
                linarith
          exact
            (Metric.infDist_le_dist_of_mem
              firstStartMem).trans hcurrent
        · have hright :
              endParameter < parameter := by
            have hstart :
                startParameter ≤ parameter :=
              le_of_not_gt hleft
            have hnot :
                ¬ parameter ≤ endParameter := by
              intro hend
              exact hmiddle ⟨hstart, hend⟩
            exact lt_of_not_ge hnot
          have hendBound :
              1 - endParameter ≤ 2 * epsilon := by
            linarith [hgap, hstartParameter.1]
          have hcurrentEnd :
              dist currentPoint endPoint =
                parameter - endParameter := by
            rw [dist_comm]
            exact
              segmentDistance endParameter parameter
                (by linarith)
          have hcurrent :
              dist currentPoint firstEnd ≤
                3 * epsilon := by
            calc
              _ ≤
                  dist currentPoint endPoint +
                    dist endPoint firstEnd :=
                dist_triangle _ _ _
              _ =
                  (parameter - endParameter) +
                    dist endPoint firstEnd := by
                rw [hcurrentEnd]
              _ ≤
                  (1 - endParameter) + epsilon := by
                have hfirst :
                    parameter - endParameter ≤
                      1 - endParameter := by
                  linarith [hparameter.2]
                have hsecond :
                    dist endPoint firstEnd ≤ epsilon := by
                  simpa [dist_comm, endPoint, firstEnd] using
                    endClosestDistance
                linarith
              _ ≤ 3 * epsilon := by
                linarith
          exact
            (Metric.infDist_le_dist_of_mem
              firstEndMem).trans hcurrent
    · have hstrict :
          endParameter < startParameter := lt_of_not_ge horder
      have hgap :
          1 - 2 * epsilon ≤
            startParameter - endParameter := by
        have h := parameterGap
        rw [abs_of_neg (by linarith)] at h
        linarith
      by_cases hmiddle :
          endParameter ≤ parameter ∧
            parameter ≤ startParameter
      · let coefficient :=
          (parameter - endParameter) /
            (startParameter - endParameter)
        have hdenominator :
            0 < startParameter - endParameter := by
          linarith
        have hcoefficientZero :
            0 ≤ coefficient := by
          exact div_nonneg
            (by linarith [hmiddle.1])
            hdenominator.le
        have hcoefficientOne :
            coefficient ≤ 1 := by
          change
            (parameter - endParameter) /
                (startParameter - endParameter) ≤ 1
          rw [div_le_one hdenominator]
          linarith [hmiddle.2]
        let firstPoint :=
          firstBase +
            (1 - coefficient) • firstDirection
        have hfirstPointMem :
            firstPoint ∈ firstSegment :=
          ⟨1 - coefficient,
            ⟨sub_nonneg.mpr hcoefficientOne,
              by linarith [hcoefficientZero]⟩,
            by simp [firstPoint]⟩
        have currentInterpolation :
            currentPoint =
              (1 - coefficient) • endPoint +
                coefficient • startPoint := by
          ext coordinate
          dsimp only [currentPoint, startPoint, endPoint,
            coefficient]
          simp only [PiLp.add_apply, PiLp.smul_apply,
            smul_eq_mul]
          field_simp [hdenominator.ne']
          ring
        have firstInterpolation :
            firstPoint =
              (1 - coefficient) • firstEnd +
                coefficient • firstStart := by
          simp [firstPoint, firstStart, firstEnd,
            smul_add, add_smul]
          module
        have interpolationDifference :
            (1 - coefficient) • endPoint +
                  coefficient • startPoint -
                ((1 - coefficient) • firstEnd +
                  coefficient • firstStart) =
              (1 - coefficient) •
                  (endPoint - firstEnd) +
                coefficient •
                  (startPoint - firstStart) := by
          module
        have interpolationNorm :
            ‖(1 - coefficient) •
                  (endPoint - firstEnd) +
                coefficient •
                  (startPoint - firstStart)‖ ≤
              (1 - coefficient) *
                  ‖endPoint - firstEnd‖ +
                coefficient *
                  ‖startPoint - firstStart‖ := by
          calc
            _ ≤
                ‖(1 - coefficient) •
                    (endPoint - firstEnd)‖ +
                  ‖coefficient •
                    (startPoint - firstStart)‖ :=
              norm_add_le _ _
            _ =
                (1 - coefficient) *
                    ‖endPoint - firstEnd‖ +
                  coefficient *
                    ‖startPoint - firstStart‖ := by
              rw [norm_smul, norm_smul,
                Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hcoefficientZero,
                abs_of_nonneg
                  (sub_nonneg.mpr hcoefficientOne)]
        have currentDistance :
            dist currentPoint firstPoint ≤ epsilon := by
          rw [currentInterpolation, firstInterpolation,
            dist_eq_norm, interpolationDifference]
          calc
            _ ≤
                (1 - coefficient) *
                    ‖endPoint - firstEnd‖ +
                  coefficient *
                    ‖startPoint - firstStart‖ :=
              interpolationNorm
            _ =
                (1 - coefficient) *
                    dist endPoint firstEnd +
                  coefficient *
                    dist startPoint firstStart := by
              rw [dist_eq_norm, dist_eq_norm]
            _ ≤
                (1 - coefficient) * epsilon +
                  coefficient * epsilon := by
              gcongr
              · simpa [dist_comm, endPoint, firstEnd] using
                  endClosestDistance
              · simpa [dist_comm, startPoint, firstStart] using
                  startClosestDistance
            _ = epsilon := by ring
        exact
          (Metric.infDist_le_dist_of_mem
            hfirstPointMem).trans <| by
              have hmain :
                  dist currentPoint firstPoint ≤
                    3 * epsilon :=
                currentDistance.trans (by linarith)
              simpa [currentPoint] using hmain
      · by_cases hleft : parameter < endParameter
        · have hendBound :
              endParameter ≤ 2 * epsilon := by
            linarith [hgap, hstartParameter.2]
          have hcurrentEnd :
              dist currentPoint endPoint =
                endParameter - parameter := by
            exact
              segmentDistance parameter endParameter
                (by linarith)
          have hcurrent :
              dist currentPoint firstEnd ≤
                3 * epsilon := by
            calc
              _ ≤
                  dist currentPoint endPoint +
                    dist endPoint firstEnd :=
                dist_triangle _ _ _
              _ =
                  (endParameter - parameter) +
                    dist endPoint firstEnd := by
                rw [hcurrentEnd]
              _ ≤ endParameter + epsilon := by
                have hfirst :
                    endParameter - parameter ≤
                      endParameter := by
                  linarith [hparameter.1]
                have hsecond :
                    dist endPoint firstEnd ≤ epsilon := by
                  simpa [dist_comm, endPoint, firstEnd] using
                    endClosestDistance
                linarith
              _ ≤ 3 * epsilon := by
                linarith
          exact
            (Metric.infDist_le_dist_of_mem
              firstEndMem).trans hcurrent
        · have hright :
              startParameter < parameter := by
            have hend :
                endParameter ≤ parameter :=
              le_of_not_gt hleft
            have hnot :
                ¬ parameter ≤ startParameter := by
              intro hstart
              exact hmiddle ⟨hend, hstart⟩
            exact lt_of_not_ge hnot
          have hstartBound :
              1 - startParameter ≤ 2 * epsilon := by
            linarith [hgap, hendParameter.1]
          have hcurrentStart :
              dist currentPoint startPoint =
                parameter - startParameter := by
            rw [dist_comm]
            exact
              segmentDistance startParameter parameter
                (by linarith)
          have hcurrent :
              dist currentPoint firstStart ≤
                3 * epsilon := by
            calc
              _ ≤
                  dist currentPoint startPoint +
                    dist startPoint firstStart :=
                dist_triangle _ _ _
              _ =
                  (parameter - startParameter) +
                    dist startPoint firstStart := by
                rw [hcurrentStart]
              _ ≤
                  (1 - startParameter) + epsilon := by
                have hfirst :
                    parameter - startParameter ≤
                      1 - startParameter := by
                  linarith [hparameter.2]
                have hsecond :
                    dist startPoint firstStart ≤ epsilon := by
                  simpa [dist_comm, startPoint, firstStart] using
                    startClosestDistance
                linarith
              _ ≤ 3 * epsilon := by
                linarith
          exact
            (Metric.infDist_le_dist_of_mem
              firstStartMem).trans hcurrent

end Kakeya.Assouad

end
