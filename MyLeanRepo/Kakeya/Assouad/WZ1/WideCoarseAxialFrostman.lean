import MyLeanRepo.Kakeya.Assouad.WZ1.StripGeometry

/-!
# Two-strip Frostman count for the wide coarse axial branch

The axial pullback in PDF Proposition 8.9 is intersected with the original
common strip.  When the two strip normals are transverse, the intersection
lies in one controlled ball, so the ambient Frostman estimate gives the
required finite cardinality bound.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
Bound the points of a Frostman set lying in two transverse strips of possibly
different widths.

The radius is the one supplied by `strip_intersection_subset_ball` after
enlarging both strips to their maximum width.
-/
lemma frostman_two_strip_intersection_card
    {E : DiscreteSet 2}
    {delta firstRadius secondRadius theta : ℝ}
    {constant : ENNReal}
    (hfirstRadius : 0 < firstRadius)
    (hsecondRadius : 0 < secondRadius)
    (htheta : 0 < theta)
    (hthetaOne : theta ≤ 1)
    (firstNormal secondNormal : Point2)
    (hfirstNormal : ‖firstNormal‖ = 1)
    (hsecondNormal : ‖secondNormal‖ = 1)
    (hangleLower :
      theta ≤ ‖firstNormal - secondNormal‖)
    (hangleUpper :
      ‖firstNormal - secondNormal‖ ≤ Real.sqrt 2)
    (firstBase secondBase : Point2)
    (hdeltaRadius :
      delta ≤
        6 * max firstRadius secondRadius / theta)
    (hradiusOne :
      6 * max firstRadius secondRadius / theta ≤ 1)
    (hFrostman :
      E.IsFrostman delta 1 constant) :
    ((E.filter fun point =>
      |inner ℝ (point - firstBase) firstNormal| ≤ firstRadius ∧
        |inner ℝ (point - secondBase) secondNormal| ≤
          secondRadius).card : ENNReal) ≤
      constant *
        Kakeya.realRpowENN
          (6 * max firstRadius secondRadius / theta) 1 *
        E.enncard := by
  classical
  let selected : DiscreteSet 2 :=
    E.filter fun point =>
      |inner ℝ (point - firstBase) firstNormal| ≤ firstRadius ∧
        |inner ℝ (point - secondBase) secondNormal| ≤ secondRadius
  by_cases hselected : selected = ∅
  · simp [selected, hselected]
  · have hselectedNonempty : selected.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hselected
    rcases hselectedNonempty with ⟨center, hcenter⟩
    have hcenterData := (Finset.mem_filter.mp hcenter).2
    let radius := max firstRadius secondRadius
    have hradius : 0 < radius := by
      dsimp only [radius]
      exact hfirstRadius.trans_le (le_max_left _ _)
    have hfirstLe : firstRadius ≤ radius := by
      exact le_max_left _ _
    have hsecondLe : secondRadius ≤ radius := by
      exact le_max_right _ _
    have hcenterFirst :
        |inner ℝ (center - firstBase) firstNormal| ≤ radius :=
      hcenterData.1.trans hfirstLe
    have hcenterSecond :
        |inner ℝ (center - secondBase) secondNormal| ≤ radius :=
      hcenterData.2.trans hsecondLe
    have hgeometry :=
      strip_intersection_subset_ball
        hradius htheta hthetaOne
        firstNormal secondNormal
        hfirstNormal hsecondNormal
        hangleLower hangleUpper
        firstBase secondBase center
        hcenterFirst hcenterSecond
    have hselectedBall :
        selected ⊆
          E.filter fun point =>
            dist point center ≤ 6 * radius / theta := by
      intro point hpoint
      have hpointData := (Finset.mem_filter.mp hpoint).2
      have hpointFirst :
          |inner ℝ (point - firstBase) firstNormal| ≤ radius :=
        hpointData.1.trans hfirstLe
      have hpointSecond :
          |inner ℝ (point - secondBase) secondNormal| ≤ radius :=
        hpointData.2.trans hsecondLe
      have hpointBall :=
        hgeometry ⟨hpointFirst, hpointSecond⟩
      exact
        Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hpoint).1,
            by
              simpa [Metric.mem_closedBall] using hpointBall⟩
    have hcard :
        (selected.card : ENNReal) ≤
          E.ballCount center (6 * radius / theta) := by
      simpa [DiscreteSet.ballCount] using
        (show (selected.card : ENNReal) ≤
            ((E.filter fun point =>
              dist point center ≤ 6 * radius / theta).card :
                ENNReal) by
          exact_mod_cast Finset.card_le_card hselectedBall)
    have hfrost :=
      hFrostman center (6 * radius / theta)
        (by simpa [radius] using hdeltaRadius)
        (by simpa [radius] using hradiusOne)
    simpa [selected, radius] using hcard.trans hfrost

end Kakeya.Assouad
