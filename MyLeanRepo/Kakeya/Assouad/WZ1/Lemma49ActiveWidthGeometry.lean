import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements

/-!
# Active-width geometry for WZ1 Lemma 49

The outer localization argument uses the maximum strip width only over the
second and third coordinate projections that actually occur in the supplied
tripartite graph.  This module proves the elementary properties of that exact
finite maximum and closes the small-common-width branch of Lemma 49.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The active common width is at least the base discretization scale. -/
lemma wz1Lemma49_delta_le_activeCommonWidth
    {delta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hH : H.Nonempty) (base direction : Point2) :
    delta ≤
      wz1ActiveCommonWidth delta H hH base direction := by
  simp only [wz1ActiveCommonWidth]
  exact le_max_left _ _

/-- Every active second-coordinate vertex lies in the common active strip. -/
lemma wz1Lemma49_second_mem_activeCommonStrip
    {delta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hH : H.Nonempty) (base direction : Point2)
    {edge : Point2 × Point2 × Point2} (hedge : edge ∈ H) :
    edge.2.1 ∈
      wz1LineNeighborhood base direction
        (wz1ActiveCommonWidth delta H hH base direction) := by
  let perpendicular := wz1Perp2 direction
  let widths : Finset ℝ :=
    H.image fun current =>
      max
        |inner ℝ (current.2.1 - base) perpendicular|
        |inner ℝ (current.2.2 - base) perpendicular|
  have hwidths : widths.Nonempty :=
    hH.image fun current =>
      max
        |inner ℝ (current.2.1 - base) perpendicular|
        |inner ℝ (current.2.2 - base) perpendicular|
  have hedgeWidth :
      max
          |inner ℝ (edge.2.1 - base) perpendicular|
          |inner ℝ (edge.2.2 - base) perpendicular| ∈
        widths :=
    Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  have hmax :
      max
          |inner ℝ (edge.2.1 - base) perpendicular|
          |inner ℝ (edge.2.2 - base) perpendicular| ≤
        widths.max' hwidths :=
    Finset.le_max' widths _ hedgeWidth
  change
    |inner ℝ (edge.2.1 - base) (wz1Perp2 direction)| ≤
      wz1ActiveCommonWidth delta H hH base direction
  calc
    |inner ℝ (edge.2.1 - base) perpendicular|
        ≤ max
            |inner ℝ (edge.2.1 - base) perpendicular|
            |inner ℝ (edge.2.2 - base) perpendicular| :=
      le_max_left _ _
    _ ≤ widths.max' hwidths := hmax
    _ ≤ max delta (widths.max' hwidths) :=
      le_max_right _ _
    _ =
        wz1ActiveCommonWidth delta H hH base direction := by
      rfl

/-- Every active third-coordinate vertex lies in the common active strip. -/
lemma wz1Lemma49_third_mem_activeCommonStrip
    {delta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hH : H.Nonempty) (base direction : Point2)
    {edge : Point2 × Point2 × Point2} (hedge : edge ∈ H) :
    edge.2.2 ∈
      wz1LineNeighborhood base direction
        (wz1ActiveCommonWidth delta H hH base direction) := by
  let perpendicular := wz1Perp2 direction
  let widths : Finset ℝ :=
    H.image fun current =>
      max
        |inner ℝ (current.2.1 - base) perpendicular|
        |inner ℝ (current.2.2 - base) perpendicular|
  have hwidths : widths.Nonempty :=
    hH.image fun current =>
      max
        |inner ℝ (current.2.1 - base) perpendicular|
        |inner ℝ (current.2.2 - base) perpendicular|
  have hedgeWidth :
      max
          |inner ℝ (edge.2.1 - base) perpendicular|
          |inner ℝ (edge.2.2 - base) perpendicular| ∈
        widths :=
    Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  have hmax :
      max
          |inner ℝ (edge.2.1 - base) perpendicular|
          |inner ℝ (edge.2.2 - base) perpendicular| ≤
        widths.max' hwidths :=
    Finset.le_max' widths _ hedgeWidth
  change
    |inner ℝ (edge.2.2 - base) (wz1Perp2 direction)| ≤
      wz1ActiveCommonWidth delta H hH base direction
  calc
    |inner ℝ (edge.2.2 - base) perpendicular|
        ≤ max
            |inner ℝ (edge.2.1 - base) perpendicular|
            |inner ℝ (edge.2.2 - base) perpendicular| :=
      le_max_right _ _
    _ ≤ widths.max' hwidths := hmax
    _ ≤ max delta (widths.max' hwidths) :=
      le_max_right _ _
    _ =
        wz1ActiveCommonWidth delta H hH base direction := by
      rfl

/--
If active first-coordinate vertices already lie in the orthogonal strip of
width `delta^(-epsilonAux) * t`, and the active common width satisfies

`t ≤ delta^(-epsilon + epsilonAux) * w`,

then the elementary localization alternative of Lemma 49 holds.
-/
theorem wz1_lemma49_small_active_width_localization
    {delta epsilon epsilonAux w : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hH : H.Nonempty)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilonAux : 0 ≤ epsilonAux)
    (base direction : Point2)
    (hw : 0 ≤ w)
    (hfirst :
      ∀ edge ∈ H,
        edge.1 ∈
          wz1LineNeighborhood 0 (wz1Perp2 direction)
            (Real.rpow delta (-epsilonAux) *
              wz1ActiveCommonWidth delta H hH base direction))
    (hwidth :
      wz1ActiveCommonWidth delta H hH base direction ≤
        Real.rpow delta (-epsilon + epsilonAux) * w) :
    (∀ edge ∈ H,
        edge.2.2 ∈
          wz1LineNeighborhood base direction
            (Real.rpow delta (-epsilon) * w)) ∧
      ∀ edge ∈ H,
        edge.1 ∈
          wz1LineNeighborhood 0 (wz1Perp2 direction)
            (Real.rpow delta (-epsilon) * w) := by
  have hscale :
      Real.rpow delta (-epsilon + epsilonAux) ≤
        Real.rpow delta (-epsilon) := by
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta hdelta_one (by linarith)
  have hthirdWidth :
      wz1ActiveCommonWidth delta H hH base direction ≤
        Real.rpow delta (-epsilon) * w := by
    calc
      wz1ActiveCommonWidth delta H hH base direction
          ≤ Real.rpow delta (-epsilon + epsilonAux) * w :=
        hwidth
      _ ≤ Real.rpow delta (-epsilon) * w := by
        gcongr
  have hpower :
      Real.rpow delta (-epsilonAux) *
          Real.rpow delta (-epsilon + epsilonAux) =
        Real.rpow delta (-epsilon) := by
    calc
      Real.rpow delta (-epsilonAux) *
            Real.rpow delta (-epsilon + epsilonAux)
          =
            Real.rpow delta
              (-epsilonAux + (-epsilon + epsilonAux)) :=
        (Real.rpow_add hdelta
          (-epsilonAux) (-epsilon + epsilonAux)).symm
      _ = Real.rpow delta (-epsilon) := by
        congr 1
        ring
  constructor
  · intro edge hedge
    have hmem :=
      wz1Lemma49_third_mem_activeCommonStrip
        (delta := delta) hH base direction hedge
    change
      |inner ℝ (edge.2.2 - base) (wz1Perp2 direction)| ≤
        wz1ActiveCommonWidth delta H hH base direction at hmem
    change
      |inner ℝ (edge.2.2 - base) (wz1Perp2 direction)| ≤
        Real.rpow delta (-epsilon) * w
    exact hmem.trans hthirdWidth
  · intro edge hedge
    have hedgeFirst := hfirst edge hedge
    change
      |inner ℝ (edge.1 - 0)
          (wz1Perp2 (wz1Perp2 direction))| ≤
        Real.rpow delta (-epsilonAux) *
          wz1ActiveCommonWidth delta H hH base direction at hedgeFirst
    change
      |inner ℝ (edge.1 - 0)
          (wz1Perp2 (wz1Perp2 direction))| ≤
        Real.rpow delta (-epsilon) * w
    exact hedgeFirst.trans
      (by
    calc
      Real.rpow delta (-epsilonAux) *
            wz1ActiveCommonWidth delta H hH base direction
          ≤ Real.rpow delta (-epsilonAux) *
              (Real.rpow delta (-epsilon + epsilonAux) * w) := by
        gcongr
        exact Real.rpow_nonneg hdelta.le _
      _ =
          (Real.rpow delta (-epsilonAux) *
              Real.rpow delta (-epsilon + epsilonAux)) * w := by
        ring
      _ = Real.rpow delta (-epsilon) * w := by
        rw [hpower])

end

end Kakeya.Assouad
