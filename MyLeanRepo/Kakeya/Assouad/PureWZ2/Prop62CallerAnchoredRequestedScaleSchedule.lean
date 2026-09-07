import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62RequestedScaleScheduleProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerParameterAbsorption
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Proposition 6.2 caller-anchored requested scales

This file records the closed part of the caller-anchor interface.  The
requested scale is literally

`q0 = rho / (K * ambientConstant.toReal)`.

For any already verified requested-scale schedule containing that coordinate,
the Definition 2.12 witness is chosen directly and assembled with the public
independent-schedule constructor.  In particular, the requested window stays
an independent parameter and the resulting laminar window is exactly
`ambientConstant * requestedWindow`.

At the original requested window `R`, the single top-gap condition is
necessary but not sufficient.  If

`R * q0 < 1 < (4 * ambientConstant.toReal) ^ 2 * q0`

rounding forces a requested scale strictly between `q0` and `1`, whereas two
applications of separation make such a scale impossible.  We therefore
delete the old points in the open conflict band around `q0`, insert `q0`, and
allow the requested window `R^2`.  This produces the complete constructor
below without exposing an insertion position or adjacent-gap assumptions.
-/

noncomputable section

namespace Kakeya.Assouad

def pureWZ2Prop62CallerAnchorValue
    (rho K : ℝ) (ambientConstant : ENNReal) : ℝ :=
  rho / (K * ambientConstant.toReal)

def pureWZ2Prop62CallerAnchorRequestedScale
    (delta rho K : ℝ)
    (ambientConstant : ENNReal)
    (lower :
      delta ≤ pureWZ2Prop62CallerAnchorValue rho K ambientConstant)
    (upper :
      pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1) :
    WZ2PaperRequestedScale delta :=
  ⟨pureWZ2Prop62CallerAnchorValue rho K ambientConstant, lower, upper⟩

/--
The direct Definition 2.12 choice at every requested coordinate.  Keeping
this family named makes the caller anchor's provenance definitionally visible.
-/
noncomputable def pureWZ2Prop62DirectNearbyFamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant requestedWindow : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (requestedSchedule :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (coordinate : Fin requestedSchedule.levelCount) :
    WZ2PaperPureNearbyScaleCoverData
      fine (requestedSchedule.requested coordinate) ambientConstant :=
  Classical.choice <|
    ambient.2.2.2 (requestedSchedule.requested coordinate)

private theorem pureWZ2Prop62DirectNearby_rho_lt
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant requestedWindow : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (requestedSchedule :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (coordinate : Fin requestedSchedule.levelCount) :
    (pureWZ2Prop62DirectNearbyFamily
        ambient requestedSchedule coordinate).rho <
      ambientConstant.toReal *
        (requestedSchedule.requested coordinate).1 := by
  let nearby :=
    pureWZ2Prop62DirectNearbyFamily
      ambient requestedSchedule coordinate
  have constantRealPos : 0 < ambientConstant.toReal :=
    ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le ambient.2.1.1))
      ambient.2.1.2
  have requestedPos :
      0 < (requestedSchedule.requested coordinate).1 :=
    ambient.1.trans_le
      (requestedSchedule.requested coordinate).2.1
  have targetPos :
      0 <
        ambientConstant.toReal *
          (requestedSchedule.requested coordinate).1 :=
    mul_pos constantRealPos requestedPos
  apply (ENNReal.ofReal_lt_ofReal_iff targetPos).mp
  calc
    ENNReal.ofReal nearby.rho <
        ambientConstant *
          ENNReal.ofReal
            (requestedSchedule.requested coordinate).1 :=
      nearby.within_factor
    _ =
        ENNReal.ofReal
          (ambientConstant.toReal *
            (requestedSchedule.requested coordinate).1) := by
      rw [ENNReal.ofReal_mul constantRealPos.le,
        ENNReal.ofReal_toReal ambient.2.1.2]

/--
Direct provenance and the paper's caller-scale window at a literal anchor.
-/
theorem WZ2PaperPureCWAAtNearbyScales.toProp62LaminarSchedule_anchor_bounds
    {delta rho K : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant requestedWindow : ENNReal}
    (ambient : WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (requestedSchedule :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchorCoordinate : Fin requestedSchedule.levelCount)
    (KPos : 0 < K)
    (q0Lower :
      delta ≤ pureWZ2Prop62CallerAnchorValue rho K ambientConstant)
    (q0Upper :
      pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1)
    (requestedAnchor :
      requestedSchedule.requested anchorCoordinate =
        pureWZ2Prop62CallerAnchorRequestedScale
          delta rho K ambientConstant
            q0Lower q0Upper) :
    pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤
        (ambient.toProp62LaminarSchedule
          requestedSchedule).actualScale anchorCoordinate ∧
      (ambient.toProp62LaminarSchedule
          requestedSchedule).actualScale anchorCoordinate <
        rho / K := by
  have anchorValue :
      (requestedSchedule.requested anchorCoordinate).1 =
        pureWZ2Prop62CallerAnchorValue rho K ambientConstant := by
    exact congrArg Subtype.val requestedAnchor
  have ambientRealPos : 0 < ambientConstant.toReal :=
    ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le ambient.2.1.1))
      ambient.2.1.2
  constructor
  · rw [← anchorValue]
    exact
      (pureWZ2Prop62DirectNearbyFamily
        ambient requestedSchedule anchorCoordinate).requested_le
  · calc
      (pureWZ2Prop62DirectNearbyFamily
          ambient requestedSchedule anchorCoordinate).rho <
          ambientConstant.toReal *
            (requestedSchedule.requested anchorCoordinate).1 :=
        pureWZ2Prop62DirectNearby_rho_lt
          ambient requestedSchedule anchorCoordinate
      _ =
          ambientConstant.toReal *
            pureWZ2Prop62CallerAnchorValue
              rho K ambientConstant := by rw [anchorValue]
      _ = rho / K := by
        unfold pureWZ2Prop62CallerAnchorValue
        field_simp [KPos.ne', ambientRealPos.ne']

/-! ## Anchored deletion net with a squared requested window -/

private def pureWZ2Prop62RetainedRequestedScales
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta) :
    Finset (WZ2PaperRequestedScale delta) :=
  insert anchor <|
    (Finset.univ.filter fun coordinate : Fin base.levelCount =>
      4 * ambientConstant.toReal * anchor.1 ≤
          (base.requested coordinate).1 ∨
        4 * ambientConstant.toReal *
            (base.requested coordinate).1 ≤ anchor.1).image
      base.requested

private lemma pureWZ2Prop62RetainedRequestedScales_anchor_mem
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta) :
    anchor ∈ pureWZ2Prop62RetainedRequestedScales base anchor := by
  simp [pureWZ2Prop62RetainedRequestedScales]

private lemma pureWZ2Prop62RetainedRequestedScales_card_le
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta) :
    (pureWZ2Prop62RetainedRequestedScales base anchor).card ≤
      base.levelCount + 1 := by
  calc
    (pureWZ2Prop62RetainedRequestedScales base anchor).card ≤
        ((Finset.univ.filter fun coordinate : Fin base.levelCount =>
          4 * ambientConstant.toReal * anchor.1 ≤
              (base.requested coordinate).1 ∨
            4 * ambientConstant.toReal *
                (base.requested coordinate).1 ≤ anchor.1).image
          base.requested).card + 1 := by
      exact
        Finset.card_insert_le
          anchor
          ((Finset.univ.filter fun coordinate : Fin base.levelCount =>
            4 * ambientConstant.toReal * anchor.1 ≤
                (base.requested coordinate).1 ∨
              4 * ambientConstant.toReal *
                  (base.requested coordinate).1 ≤ anchor.1).image
            base.requested)
    _ ≤
        (Finset.univ.filter fun coordinate : Fin base.levelCount =>
          4 * ambientConstant.toReal * anchor.1 ≤
              (base.requested coordinate).1 ∨
            4 * ambientConstant.toReal *
                (base.requested coordinate).1 ≤ anchor.1).card + 1 := by
      gcongr
      exact Finset.card_image_le
    _ ≤ base.levelCount + 1 := by
      gcongr
      simpa using
        Finset.card_filter_le
          (Finset.univ : Finset (Fin base.levelCount))
          (fun coordinate =>
            4 * ambientConstant.toReal * anchor.1 ≤
                (base.requested coordinate).1 ∨
              4 * ambientConstant.toReal *
                  (base.requested coordinate).1 ≤ anchor.1)

private lemma pureWZ2Prop62RetainedRequestedScales_pair_separated
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta)
    {lower upper : WZ2PaperRequestedScale delta}
    (lowerMem :
      lower ∈ pureWZ2Prop62RetainedRequestedScales base anchor)
    (upperMem :
      upper ∈ pureWZ2Prop62RetainedRequestedScales base anchor)
    (lowerLtUpper : lower < upper) :
    4 * ambientConstant.toReal * lower.1 ≤ upper.1 := by
  have constantOne : (1 : ℝ) ≤ ambientConstant.toReal := by
    simpa using ENNReal.toReal_mono ambientFinite ambientOne
  have factorOne : (1 : ℝ) ≤ 4 * ambientConstant.toReal := by
    nlinarith
  have lowerPos : 0 < lower.1 :=
    deltaPos.trans_le lower.2.1
  have upperPos : 0 < upper.1 :=
    deltaPos.trans_le upper.2.1
  simp only [pureWZ2Prop62RetainedRequestedScales,
    Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at lowerMem upperMem
  rcases lowerMem with lowerEq | ⟨lowerCoordinate, lowerGap, lowerEq⟩
  ·
    rcases upperMem with upperEq | ⟨upperCoordinate, upperGap, upperEq⟩
    · have impossible : anchor < anchor := by
        simp [lowerEq, upperEq] at lowerLtUpper
      exact False.elim (lt_irrefl anchor impossible)
    ·
      rcases upperGap with gap | gap
      · simpa [lowerEq, upperEq] using gap
      · have :
            upper.1 ≤ anchor.1 := by
          calc
            upper.1 ≤
                4 * ambientConstant.toReal * upper.1 := by
              nlinarith
            _ ≤ anchor.1 := by simpa [upperEq] using gap
        have anchorLtUpper : anchor < upper := by
          simpa [lowerEq] using lowerLtUpper
        exact False.elim (not_lt_of_ge this anchorLtUpper)
  ·
    rcases upperMem with upperEq | ⟨upperCoordinate, upperGap, upperEq⟩
    ·
      rcases lowerGap with gap | gap
      · have :
            anchor.1 ≤ lower.1 := by
          calc
            anchor.1 ≤
                4 * ambientConstant.toReal * anchor.1 := by
              have anchorPos : 0 < anchor.1 :=
                deltaPos.trans_le anchor.2.1
              nlinarith
            _ ≤ lower.1 := by simpa [lowerEq] using gap
        have lowerLtAnchor : lower < anchor := by
          simpa [upperEq] using lowerLtUpper
        exact False.elim (not_lt_of_ge this lowerLtAnchor)
      · simpa [lowerEq, upperEq] using gap
    ·
      have baseValueLt :
          base.requested lowerCoordinate <
            base.requested upperCoordinate := by
        simpa [lowerEq, upperEq] using lowerLtUpper
      have coordinateOrder :
          upperCoordinate.1 < lowerCoordinate.1 := by
        by_contra notOrder
        have lowerLeUpper :
            lowerCoordinate.1 ≤ upperCoordinate.1 := by omega
        by_cases coordinateEq : lowerCoordinate = upperCoordinate
        · subst upperCoordinate
          exact False.elim <|
            lt_irrefl (base.requested lowerCoordinate) baseValueLt
        · have lowerCoordinateLt :
              lowerCoordinate.1 < upperCoordinate.1 := by
            exact lt_of_le_of_ne lowerLeUpper <|
              fun equality => coordinateEq (Fin.ext equality)
          have separated :=
            base.requested_separated
              lowerCoordinate upperCoordinate lowerCoordinateLt
          have upperLeScaled :
              (base.requested upperCoordinate).1 ≤
                4 * ambientConstant.toReal *
                  (base.requested upperCoordinate).1 := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right factorOne <|
                deltaPos.le.trans
                  (base.requested upperCoordinate).2.1
          exact False.elim <|
            (not_lt_of_ge (upperLeScaled.trans separated)) baseValueLt
      simpa [lowerEq, upperEq] using
        base.requested_separated
          upperCoordinate lowerCoordinate coordinateOrder

private def pureWZ2Prop62RetainedRequestedScale
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta)
    (coordinate :
      Fin (pureWZ2Prop62RetainedRequestedScales base anchor).card) :
    WZ2PaperRequestedScale delta :=
  (pureWZ2Prop62RetainedRequestedScales base anchor).orderEmbOfFin rfl
    coordinate.rev

private lemma pureWZ2Prop62RetainedRequestedScale_surjective
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta)
    {scale : WZ2PaperRequestedScale delta}
    (scaleMem :
      scale ∈ pureWZ2Prop62RetainedRequestedScales base anchor) :
    ∃ coordinate :
        Fin (pureWZ2Prop62RetainedRequestedScales base anchor).card,
      pureWZ2Prop62RetainedRequestedScale base anchor coordinate =
        scale := by
  have scaleInRange :
      scale ∈
        Set.range
          ((pureWZ2Prop62RetainedRequestedScales base anchor).orderEmbOfFin
            rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact scaleMem
  rcases scaleInRange with ⟨coordinate, coordinateEq⟩
  refine ⟨coordinate.rev, ?_⟩
  simpa [pureWZ2Prop62RetainedRequestedScale] using coordinateEq

private lemma pureWZ2Prop62RetainedRequestedScale_separated
    {delta : ℝ}
    {ambientConstant requestedWindow : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow)
    (anchor : WZ2PaperRequestedScale delta)
    (first second :
      Fin (pureWZ2Prop62RetainedRequestedScales base anchor).card)
    (firstLtSecond : first.1 < second.1) :
    4 * ambientConstant.toReal *
        (pureWZ2Prop62RetainedRequestedScale
          base anchor second).1 ≤
      (pureWZ2Prop62RetainedRequestedScale base anchor first).1 := by
  have reversed :
      second.rev < first.rev := by
    exact Fin.rev_lt_rev.mpr firstLtSecond
  have valueLt :
      pureWZ2Prop62RetainedRequestedScale base anchor second <
        pureWZ2Prop62RetainedRequestedScale base anchor first := by
    exact
      (pureWZ2Prop62RetainedRequestedScales base anchor).orderEmbOfFin
        rfl |>.strictMono reversed
  exact
    pureWZ2Prop62RetainedRequestedScales_pair_separated
      ambientOne ambientFinite deltaPos base anchor
      (Finset.orderEmbOfFin_mem _ _ _)
      (Finset.orderEmbOfFin_mem _ _ _) valueLt

private lemma pureWZ2Prop62RetainedRequestedScale_rounding
    {delta R : ℝ}
    {ambientConstant : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (RPos : 0 < R)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (anchor : WZ2PaperRequestedScale delta)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (topGap :
      4 * ambientConstant.toReal * anchor.1 ≤ 1)
    (target : WZ2PaperRequestedScale delta) :
    ∃ coordinate :
        Fin (pureWZ2Prop62RetainedRequestedScales base anchor).card,
      target.1 ≤
          (pureWZ2Prop62RetainedRequestedScale
            base anchor coordinate).1 ∧
        ENNReal.ofReal
            (pureWZ2Prop62RetainedRequestedScale
              base anchor coordinate).1 <
          ENNReal.ofReal (R ^ 2) * ENNReal.ofReal target.1 := by
  let factor := 4 * ambientConstant.toReal
  have constantOne : (1 : ℝ) ≤ ambientConstant.toReal := by
    simpa using ENNReal.toReal_mono ambientFinite ambientOne
  have factorOne : (1 : ℝ) ≤ factor := by
    dsimp only [factor]
    nlinarith
  have ROne : 1 ≤ R := factorOne.trans ratioLe
  have targetPos : 0 < target.1 :=
    deltaPos.trans_le target.2.1
  have anchorPos : 0 < anchor.1 :=
    deltaPos.trans_le anchor.2.1
  rcases base.rounding target with
    ⟨oldCoordinate, targetLeOld, oldUpper⟩
  let oldScale := base.requested oldCoordinate
  have oldScalePos : 0 < oldScale.1 :=
    deltaPos.trans_le oldScale.2.1
  have oldUpperReal : oldScale.1 < R * target.1 := by
    apply
      (ENNReal.ofReal_lt_ofReal_iff
        (mul_pos RPos targetPos)).mp
    calc
      ENNReal.ofReal oldScale.1 <
          ENNReal.ofReal R * ENNReal.ofReal target.1 := oldUpper
      _ = ENNReal.ofReal (R * target.1) := by
        rw [ENNReal.ofReal_mul RPos.le]
  by_cases oldRetained :
      factor * anchor.1 ≤ oldScale.1 ∨
        factor * oldScale.1 ≤ anchor.1
  · have oldMem :
        oldScale ∈
          pureWZ2Prop62RetainedRequestedScales base anchor := by
      simp only [pureWZ2Prop62RetainedRequestedScales,
        Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact Or.inr ⟨oldCoordinate, oldRetained, rfl⟩
    rcases
        pureWZ2Prop62RetainedRequestedScale_surjective
          base anchor oldMem with
      ⟨coordinate, coordinateEq⟩
    refine ⟨coordinate, ?_, ?_⟩
    · simpa [coordinateEq, oldScale] using targetLeOld
    · rw [coordinateEq]
      have upperReal : oldScale.1 < R ^ 2 * target.1 := by
        calc
          oldScale.1 < R * target.1 := oldUpperReal
          _ ≤ R ^ 2 * target.1 := by
            have := mul_le_mul_of_nonneg_right ROne targetPos.le
            nlinarith
      rw [← ENNReal.ofReal_mul (sq_nonneg R)]
      exact
        (ENNReal.ofReal_lt_ofReal_iff
          (mul_pos (sq_pos_of_pos RPos) targetPos)).2 upperReal
  · have oldBelowUpperBand :
        oldScale.1 < factor * anchor.1 :=
      lt_of_not_ge fun inequality =>
        oldRetained (Or.inl inequality)
    have anchorBelowScaledOld :
        anchor.1 < factor * oldScale.1 :=
      lt_of_not_ge fun inequality =>
        oldRetained (Or.inr inequality)
    by_cases targetLeAnchor : target.1 ≤ anchor.1
    · rcases
          pureWZ2Prop62RetainedRequestedScale_surjective
            base anchor
              (pureWZ2Prop62RetainedRequestedScales_anchor_mem
                base anchor) with
        ⟨coordinate, coordinateEq⟩
      refine ⟨coordinate, ?_, ?_⟩
      · simpa [coordinateEq] using targetLeAnchor
      · rw [coordinateEq]
        have upperReal : anchor.1 < R ^ 2 * target.1 := by
          calc
            anchor.1 < factor * oldScale.1 :=
              anchorBelowScaledOld
            _ ≤ R * oldScale.1 := by
              exact mul_le_mul_of_nonneg_right ratioLe oldScalePos.le
            _ < R * (R * target.1) := by
              exact mul_lt_mul_of_pos_left oldUpperReal RPos
            _ = R ^ 2 * target.1 := by ring
        rw [← ENNReal.ofReal_mul (sq_nonneg R)]
        exact
          (ENNReal.ofReal_lt_ofReal_iff
            (mul_pos (sq_pos_of_pos RPos) targetPos)).2 upperReal
    · have anchorLtTarget : anchor.1 < target.1 :=
        lt_of_not_ge targetLeAnchor
      have scaledAnchorLower :
          delta ≤ factor * anchor.1 := by
        calc
          delta ≤ anchor.1 := anchor.2.1
          _ ≤ factor * anchor.1 := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right factorOne anchorPos.le
      let scaledAnchor : WZ2PaperRequestedScale delta :=
        ⟨factor * anchor.1, scaledAnchorLower, topGap⟩
      rcases base.rounding scaledAnchor with
        ⟨upperCoordinate, scaledAnchorLeUpper, upperWindow⟩
      let upperScale := base.requested upperCoordinate
      have upperScalePos : 0 < upperScale.1 :=
        deltaPos.trans_le upperScale.2.1
      have upperMem :
          upperScale ∈
            pureWZ2Prop62RetainedRequestedScales base anchor := by
        simp only [pureWZ2Prop62RetainedRequestedScales,
          Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact Or.inr <|
          ⟨upperCoordinate, Or.inl scaledAnchorLeUpper, rfl⟩
      rcases
          pureWZ2Prop62RetainedRequestedScale_surjective
            base anchor upperMem with
        ⟨coordinate, coordinateEq⟩
      refine ⟨coordinate, ?_, ?_⟩
      · rw [coordinateEq]
        exact targetLeOld.trans <|
          oldBelowUpperBand.le.trans scaledAnchorLeUpper
      · rw [coordinateEq]
        have upperWindowReal :
            upperScale.1 < R * (factor * anchor.1) := by
          apply
            (ENNReal.ofReal_lt_ofReal_iff
              (mul_pos RPos <| mul_pos (lt_of_lt_of_le zero_lt_one factorOne)
                anchorPos)).mp
          calc
            ENNReal.ofReal upperScale.1 <
                ENNReal.ofReal R *
                  ENNReal.ofReal (factor * anchor.1) :=
              upperWindow
            _ =
                ENNReal.ofReal (R * (factor * anchor.1)) := by
              rw [ENNReal.ofReal_mul RPos.le]
        have upperReal :
            upperScale.1 < R ^ 2 * target.1 := by
          calc
            upperScale.1 < R * (factor * anchor.1) :=
              upperWindowReal
            _ ≤ R * (R * anchor.1) := by
              gcongr
            _ < R * (R * target.1) := by
              gcongr
            _ = R ^ 2 * target.1 := by ring
        rw [← ENNReal.ofReal_mul (sq_nonneg R)]
        exact
          (ENNReal.ofReal_lt_ofReal_iff
            (mul_pos (sq_pos_of_pos RPos) targetPos)).2 upperReal

/--
Delete every old requested scale in the open conflict band around `anchor`,
insert `anchor`, and enumerate the retained finite set in decreasing order.

One deleted geometric step is paid by squaring the old requested window.
-/
noncomputable def pureWZ2Prop62AnchoredDeletionSchedule
    {delta R : ℝ}
    {ambientConstant : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (RPos : 0 < R)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (anchor : WZ2PaperRequestedScale delta)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (topGap :
      4 * ambientConstant.toReal * anchor.1 ≤ 1) :
    PureWZ2Prop62RequestedScaleSchedule
      delta ambientConstant (ENNReal.ofReal (R ^ 2)) where
  scaleWindow_finite := by
    constructor
    · have ROne : 1 ≤ R := by
        have constantOne : (1 : ℝ) ≤ ambientConstant.toReal := by
          simpa using ENNReal.toReal_mono ambientFinite ambientOne
        have factorOne :
            (1 : ℝ) ≤ 4 * ambientConstant.toReal := by nlinarith
        exact factorOne.trans ratioLe
      have squareOne : (1 : ℝ) ≤ R ^ 2 := by nlinarith
      simpa using ENNReal.ofReal_mono squareOne
    · exact ENNReal.ofReal_ne_top
  levelCount :=
    (pureWZ2Prop62RetainedRequestedScales base anchor).card
  levelCount_pos := by
    exact Finset.card_pos.mpr <|
      ⟨anchor,
        pureWZ2Prop62RetainedRequestedScales_anchor_mem base anchor⟩
  requested :=
    pureWZ2Prop62RetainedRequestedScale base anchor
  requested_separated :=
    pureWZ2Prop62RetainedRequestedScale_separated
      ambientOne ambientFinite deltaPos base anchor
  rounding :=
    pureWZ2Prop62RetainedRequestedScale_rounding
      ambientOne ambientFinite deltaPos RPos base anchor ratioLe topGap

theorem pureWZ2Prop62AnchoredDeletionSchedule_levelCount_le
    {delta R : ℝ}
    {ambientConstant : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (RPos : 0 < R)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (anchor : WZ2PaperRequestedScale delta)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (topGap :
      4 * ambientConstant.toReal * anchor.1 ≤ 1) :
    (pureWZ2Prop62AnchoredDeletionSchedule
      ambientOne ambientFinite deltaPos RPos base anchor
        ratioLe topGap).levelCount ≤
      base.levelCount + 1 :=
  pureWZ2Prop62RetainedRequestedScales_card_le base anchor

theorem pureWZ2Prop62AnchoredDeletionSchedule_anchor
    {delta R : ℝ}
    {ambientConstant : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (RPos : 0 < R)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (anchor : WZ2PaperRequestedScale delta)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (topGap :
      4 * ambientConstant.toReal * anchor.1 ≤ 1) :
    ∃ coordinate :
        Fin
          (pureWZ2Prop62AnchoredDeletionSchedule
            ambientOne ambientFinite deltaPos RPos base anchor
              ratioLe topGap).levelCount,
      (pureWZ2Prop62AnchoredDeletionSchedule
        ambientOne ambientFinite deltaPos RPos base anchor
          ratioLe topGap).requested coordinate = anchor :=
  pureWZ2Prop62RetainedRequestedScale_surjective
    base anchor <|
      pureWZ2Prop62RetainedRequestedScales_anchor_mem base anchor

theorem pureWZ2Prop62AnchoredDeletionSchedule_requested_antitone
    {delta R : ℝ}
    {ambientConstant : ENNReal}
    (ambientOne : 1 ≤ ambientConstant)
    (ambientFinite : ambientConstant ≠ ⊤)
    (deltaPos : 0 < delta)
    (RPos : 0 < R)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (anchor : WZ2PaperRequestedScale delta)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (topGap :
      4 * ambientConstant.toReal * anchor.1 ≤ 1)
    (first second :
      Fin
        (pureWZ2Prop62AnchoredDeletionSchedule
          ambientOne ambientFinite deltaPos RPos base anchor
            ratioLe topGap).levelCount)
    (firstLeSecond : first.1 ≤ second.1) :
    (pureWZ2Prop62AnchoredDeletionSchedule
        ambientOne ambientFinite deltaPos RPos base anchor
          ratioLe topGap).requested second ≤
      (pureWZ2Prop62AnchoredDeletionSchedule
        ambientOne ambientFinite deltaPos RPos base anchor
          ratioLe topGap).requested first := by
  by_cases equal : first = second
  · subst second
    exact le_rfl
  · have firstLtSecond : first.1 < second.1 :=
      lt_of_le_of_ne firstLeSecond <|
        fun equality => equal (Fin.ext equality)
    have separated :=
      (pureWZ2Prop62AnchoredDeletionSchedule
        ambientOne ambientFinite deltaPos RPos base anchor
          ratioLe topGap).requested_separated
        first second firstLtSecond
    apply Subtype.coe_le_coe.mp
    have constantOne : (1 : ℝ) ≤ ambientConstant.toReal := by
      simpa using ENNReal.toReal_mono ambientFinite ambientOne
    have factorOne : (1 : ℝ) ≤ 4 * ambientConstant.toReal := by
      nlinarith
    have secondNonnegative :
        0 ≤
          ((pureWZ2Prop62AnchoredDeletionSchedule
            ambientOne ambientFinite deltaPos RPos base anchor
              ratioLe topGap).requested second).1 :=
      deltaPos.le.trans <|
        ((pureWZ2Prop62AnchoredDeletionSchedule
          ambientOne ambientFinite deltaPos RPos base anchor
            ratioLe topGap).requested second).2.1
    have secondLeScaled :
        ((pureWZ2Prop62AnchoredDeletionSchedule
          ambientOne ambientFinite deltaPos RPos base anchor
            ratioLe topGap).requested second).1 ≤
          4 * ambientConstant.toReal *
            ((pureWZ2Prop62AnchoredDeletionSchedule
              ambientOne ambientFinite deltaPos RPos base anchor
                ratioLe topGap).requested second).1 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right factorOne secondNonnegative
    exact secondLeScaled.trans separated

/--
The complete caller-facing output of conflict-band deletion.  The anchor is
a literal requested coordinate, and the laminar witness at that coordinate is
the named direct Definition 2.12 choice.
-/
structure PureWZ2Prop62CallerAnchoredScheduleData
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R)) where
  requestedSchedule :
    PureWZ2Prop62RequestedScaleSchedule
      delta ambientConstant (ENNReal.ofReal (R ^ 2))
  anchorCoordinate : Fin requestedSchedule.levelCount
  requested_anchor :
    (requestedSchedule.requested anchorCoordinate).1 =
      pureWZ2Prop62CallerAnchorValue rho K ambientConstant
  requested_antitone :
    ∀ first second : Fin requestedSchedule.levelCount,
      first.1 ≤ second.1 →
        requestedSchedule.requested second ≤
          requestedSchedule.requested first
  levelCount_le :
    requestedSchedule.levelCount ≤ base.levelCount + 1
  laminar :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant
        (ambientConstant * ENNReal.ofReal (R ^ 2))
  laminar_eq :
    laminar =
      ambient.toProp62LaminarSchedule requestedSchedule
  laminar_levelCount_eq :
    laminar.levelCount = requestedSchedule.levelCount
  anchorNearby :
    WZ2PaperPureNearbyScaleCoverData
      fine (requestedSchedule.requested anchorCoordinate)
        ambientConstant
  anchor_actual_eq :
    laminar.actualScale
        (Fin.cast laminar_levelCount_eq.symm anchorCoordinate) =
      anchorNearby.rho
  anchor_scaleData_eq :
    HEq
      (laminar.scaleData
        (Fin.cast laminar_levelCount_eq.symm anchorCoordinate))
      anchorNearby.scaleData
  anchor_actual_lower :
    pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤
      laminar.actualScale
        (Fin.cast laminar_levelCount_eq.symm anchorCoordinate)
  anchor_actual_upper :
    laminar.actualScale
        (Fin.cast laminar_levelCount_eq.symm anchorCoordinate) <
      rho / K

/--
Full caller-anchored constructor.  The only extra endpoint condition is the
top gap; the insertion coordinate and all adjacent gaps are constructed
internally by deleting the open conflict band.
-/
theorem pureWZ2_prop62_caller_anchored_schedule
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R))
    (KPos : 0 < K)
    (RPos : 0 < R)
    (ratioLe :
      4 * ambientConstant.toReal ≤ R)
    (q0Lower :
      delta ≤ pureWZ2Prop62CallerAnchorValue rho K ambientConstant)
    (q0Upper :
      pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1)
    (topGap :
      4 * ambientConstant.toReal *
          pureWZ2Prop62CallerAnchorValue rho K ambientConstant ≤ 1) :
    Nonempty
      (PureWZ2Prop62CallerAnchoredScheduleData
        (rho := rho) (K := K) (R := R) ambient base) := by
  let anchor :=
    pureWZ2Prop62CallerAnchorRequestedScale
      delta rho K ambientConstant q0Lower q0Upper
  let requestedSchedule :=
    pureWZ2Prop62AnchoredDeletionSchedule
      ambient.2.1.1 ambient.2.1.2 ambient.1 RPos base anchor
        ratioLe topGap
  rcases
      pureWZ2Prop62AnchoredDeletionSchedule_anchor
        ambient.2.1.1 ambient.2.1.2 ambient.1 RPos base anchor
          ratioLe topGap with
    ⟨anchorCoordinate, anchorCoordinateEq⟩
  let laminar :=
    ambient.toProp62LaminarSchedule requestedSchedule
  let anchorNearby :=
    pureWZ2Prop62DirectNearbyFamily
      ambient requestedSchedule anchorCoordinate
  have requestedAnchor :
      (requestedSchedule.requested anchorCoordinate).1 =
        pureWZ2Prop62CallerAnchorValue rho K ambientConstant := by
    rw [anchorCoordinateEq]
    rfl
  have requestedAnchorSubtype :
      requestedSchedule.requested anchorCoordinate =
        pureWZ2Prop62CallerAnchorRequestedScale
          delta rho K ambientConstant q0Lower q0Upper := by
    exact Subtype.ext requestedAnchor
  have anchorBounds :=
    ambient.toProp62LaminarSchedule_anchor_bounds
      requestedSchedule anchorCoordinate KPos
        q0Lower q0Upper requestedAnchorSubtype
  exact
    ⟨{
      requestedSchedule := requestedSchedule
      anchorCoordinate := anchorCoordinate
      requested_anchor := requestedAnchor
      requested_antitone :=
        pureWZ2Prop62AnchoredDeletionSchedule_requested_antitone
          ambient.2.1.1 ambient.2.1.2 ambient.1 RPos base anchor
            ratioLe topGap
      levelCount_le :=
        pureWZ2Prop62AnchoredDeletionSchedule_levelCount_le
          ambient.2.1.1 ambient.2.1.2 ambient.1 RPos base anchor
            ratioLe topGap
      laminar := laminar
      laminar_eq := rfl
      laminar_levelCount_eq := rfl
      anchorNearby := anchorNearby
      anchor_actual_eq := rfl
      anchor_scaleData_eq := by rfl
      anchor_actual_lower := anchorBounds.1
      anchor_actual_upper := anchorBounds.2
    }⟩

namespace PureWZ2Prop62CallerAnchoredScheduleData

variable
    {delta rho K R : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant}
    {base :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant (ENNReal.ofReal R)}
    (data :
      PureWZ2Prop62CallerAnchoredScheduleData
        (rho := rho) (K := K) (R := R) ambient base)

theorem laminar_levelCount_le :
    data.laminar.levelCount ≤ base.levelCount + 1 := by
  rw [data.laminar_eq]
  exact data.levelCount_le

theorem laminar_rounding :
    ∀ target : WZ2PaperRequestedScale delta,
      ∃ coordinate : Fin data.laminar.levelCount,
        target.1 ≤ data.laminar.actualScale coordinate ∧
          ENNReal.ofReal (data.laminar.actualScale coordinate) <
            (ambientConstant * ENNReal.ofReal (R ^ 2)) *
              ENNReal.ofReal target.1 :=
  data.laminar.rounding

end PureWZ2Prop62CallerAnchoredScheduleData

/-- The geometric base gives the requested `ceil (1 / step) + 2` depth. -/
theorem pureWZ2Prop62CallerAnchoredScheduleData_geometric_levelCount_le
    {delta rho K step : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (deltaLtOne : delta < 1)
    (stepPos : 0 < step)
    (separation :
      4 * ambientConstant.toReal ≤ Real.rpow delta (-step))
    (data :
      PureWZ2Prop62CallerAnchoredScheduleData
        (rho := rho) (K := K)
        (R := Real.rpow delta (-step)) ambient
          (pureWZ2Prop62RequestedScaleSchedule
            delta step ambientConstant ambient.1 deltaLtOne
              stepPos separation)) :
    data.laminar.levelCount ≤ Nat.ceil (1 / step) + 2 := by
  calc
    data.laminar.levelCount ≤
        (pureWZ2Prop62RequestedScaleSchedule
          delta step ambientConstant ambient.1 deltaLtOne
            stepPos separation).levelCount + 1 :=
      data.laminar_levelCount_le
    _ ≤ (Nat.ceil (1 / step) + 1) + 1 := by
      gcongr
      exact
        pureWZ2Prop62RequestedScaleSchedule_levelCount_le
          delta step ambientConstant ambient.1 deltaLtOne
            stepPos separation
    _ = Nat.ceil (1 / step) + 2 := by omega

/--
If the old geometric requested window is `Cstar^2`, conflict-band deletion
gives requested window `Cstar^4`, and the public nearby conversion gives
exactly `Cstar^5`.
-/
theorem pureWZ2Prop62_anchored_finalWindow_eq_fifth
    (Cstar : ENNReal)
    {R : ℝ}
    (RNonnegative : 0 ≤ R)
    (baseWindowEq : ENNReal.ofReal R = Cstar ^ 2) :
    Cstar * ENNReal.ofReal (R ^ 2) = Cstar ^ 5 := by
  have squareWindow :
      ENNReal.ofReal (R ^ 2) = (ENNReal.ofReal R) ^ 2 := by
    calc
      ENNReal.ofReal (R ^ 2) =
          ENNReal.ofReal (R * R) := by rw [pow_two]
      _ =
          ENNReal.ofReal R * ENNReal.ofReal R :=
        ENNReal.ofReal_mul RNonnegative
      _ = (ENNReal.ofReal R) ^ 2 := by ring
  rw [squareWindow, baseWindowEq]
  ring

/--
Paper-facing specialization of the deletion window.  At
`step = 2 * A * eta` and `Cstar = delta ^ (-A * eta)`, the original
geometric requested window is `Cstar^2`; after deletion and the public nearby
conversion the laminar window is exactly `Cstar^5`.
-/
theorem pureWZ2Prop62_geometric_anchored_finalWindow_eq_fifth
    {delta step A eta : ℝ}
    (deltaPos : 0 < delta)
    (stepEq : step = 2 * A * eta)
    (Cstar : ENNReal)
    (CstarEq :
      Cstar = ENNReal.ofReal (Real.rpow delta (-A * eta))) :
    Cstar *
        ENNReal.ofReal ((Real.rpow delta (-step)) ^ 2) =
      Cstar ^ 5 := by
  have exponentEq :
      (-step : ℝ) = (-A * eta) + (-A * eta) := by
    rw [stepEq]
    ring
  have rpowSquare :
      Real.rpow delta (-step) =
        Real.rpow delta (-A * eta) *
          Real.rpow delta (-A * eta) := by
    rw [exponentEq]
    exact Real.rpow_add deltaPos (-A * eta) (-A * eta)
  have baseWindowEq :
      ENNReal.ofReal (Real.rpow delta (-step)) = Cstar ^ 2 := by
    have ofRealSquare :
        ENNReal.ofReal
            (Real.rpow delta (-A * eta) *
              Real.rpow delta (-A * eta)) =
          ENNReal.ofReal (Real.rpow delta (-A * eta)) *
            ENNReal.ofReal (Real.rpow delta (-A * eta)) :=
      ENNReal.ofReal_mul (Real.rpow_pos_of_pos deltaPos _).le
    rw [rpowSquare, ofRealSquare, CstarEq]
    ring
  exact
    pureWZ2Prop62_anchored_finalWindow_eq_fifth
      Cstar (Real.rpow_nonneg deltaPos.le _) baseWindowEq

namespace PureWZ2Prop62CallerParameterAbsorptionData

variable
    {A : ℕ} {epsilon eta c0 delta rho : ℝ}
    (data :
      PureWZ2Prop62CallerParameterAbsorptionData
        A epsilon eta c0 delta rho)

/-- The geometric requested-scale net associated to the absorbed caller data. -/
noncomputable def geometricRequestedSchedule :
    PureWZ2Prop62RequestedScaleSchedule
      delta (pureWZ2Prop62CallerCstar delta A eta)
        (ENNReal.ofReal
          (Real.rpow delta (-pureWZ2Prop62CallerStep A eta))) :=
  pureWZ2Prop62RequestedScaleSchedule
    delta (pureWZ2Prop62CallerStep A eta)
      (pureWZ2Prop62CallerCstar delta A eta)
      data.delta_pos data.delta_lt_one data.step_pos
      data.requested_separation

/--
Construct the complete caller-anchored schedule from the absorbed parameters.
The literal anchor, the top gap, and every adjacent separation inequality are
internal; callers supply only the public nearby-scale CWA datum.
-/
theorem callerAnchoredSchedule
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine
        (pureWZ2Prop62CallerCstar delta A eta)) :
    Nonempty
      (PureWZ2Prop62CallerAnchoredScheduleData
        (rho := rho) (K := data.parameters.K)
        (R := Real.rpow delta (-pureWZ2Prop62CallerStep A eta))
        ambient data.geometricRequestedSchedule) := by
  have q0Eq :
      pureWZ2Prop62CallerQ0 delta rho c0 A eta =
        pureWZ2Prop62CallerAnchorValue rho data.parameters.K
          (pureWZ2Prop62CallerCstar delta A eta) := by
    simp only [pureWZ2Prop62CallerQ0,
      pureWZ2Prop62CallerAnchorValue, data.parameters.K_eq]
  have q0Lower :
      delta ≤
        pureWZ2Prop62CallerAnchorValue rho data.parameters.K
          (pureWZ2Prop62CallerCstar delta A eta) := by
    rw [← q0Eq]
    exact data.q0_lower
  have q0Upper :
      pureWZ2Prop62CallerAnchorValue rho data.parameters.K
          (pureWZ2Prop62CallerCstar delta A eta) ≤ 1 := by
    rw [← q0Eq]
    exact data.q0_upper
  have topGap :
      4 * (pureWZ2Prop62CallerCstar delta A eta).toReal *
          pureWZ2Prop62CallerAnchorValue rho data.parameters.K
            (pureWZ2Prop62CallerCstar delta A eta) ≤ 1 := by
    rw [← q0Eq]
    exact data.q0_top_gap
  exact
    pureWZ2_prop62_caller_anchored_schedule
      ambient data.geometricRequestedSchedule data.parameters.K_pos
      (Real.rpow_pos_of_pos data.delta_pos _)
      data.requested_separation q0Lower q0Upper topGap

end PureWZ2Prop62CallerParameterAbsorptionData

end Kakeya.Assouad

end
