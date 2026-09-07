import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveWidthGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph

/-!
# Active viewpoint selection for the WZ1 Lemma 49 Kaufman branch

When the active common width is strictly larger than the input `G₁` strip
width, an actual active `G₂` coordinate attains that width.  Fixing the first
and third coordinates of the same actual edge gives a dense `G₁` fiber.
After orienting the strip direction, that entire fiber lies on one positive
side of the selected viewpoint.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/-- The actual viewpoint, source fiber, and one-sided strip geometry selected
from the graph-active width maximum. -/
structure WZ1Lemma49ActiveViewpointData
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2))
    (density : ENNReal)
    (base direction : Point2)
    (width activeWidth : ℝ) where
  sourceEdge : Point2 × Point2 × Point2
  sourceEdge_mem : sourceEdge ∈ H
  viewpoint : Point2 := sourceEdge.2.2
  viewpoint_eq : viewpoint = sourceEdge.2.2
  viewpoint_mem : viewpoint ∈ G₂
  orientedDirection : Point2
  orientedDirection_unit : ‖orientedDirection‖ = 1
  orientedDirection_eq :
    orientedDirection = direction ∨
      orientedDirection = -direction
  source : DiscreteSet 2 :=
    kaufmanSecondFiber H sourceEdge.1 viewpoint
  source_eq :
    source = kaufmanSecondFiber H sourceEdge.1 viewpoint
  source_nonempty : source.Nonempty
  source_subset : source ⊆ G₁
  source_density :
    density * G₁.enncard ≤ (source.card : ENNReal)
  source_actual :
    ∀ second ∈ source, (sourceEdge.1, second, viewpoint) ∈ H
  source_strip :
    ∀ second ∈ source,
      |inner ℝ (second - base)
        (wz1Perp2 orientedDirection)| ≤ (2 * width) / 2
  side : ℝ := 2 * (activeWidth - width)
  side_eq : side = 2 * (activeWidth - width)
  side_pos : 0 < side
  source_side :
    ∀ second ∈ source,
      side / 2 ≤
        inner ℝ (second - viewpoint)
          (wz1Perp2 orientedDirection)

lemma wz1Lemma49_perp_neg (vector : Point2) :
    wz1Perp2 (-vector) = -wz1Perp2 vector := by
  ext i
  fin_cases i <;> simp [wz1Perp2]

/-- Absolute perpendicular coordinates are unchanged by the selected
orientation sign. -/
lemma WZ1Lemma49ActiveViewpointData.abs_inner_perp_oriented
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    {base direction : Point2}
    {width activeWidth : ℝ}
    (data :
      WZ1Lemma49ActiveViewpointData
        F G₁ G₂ H density base direction width activeWidth)
    (vector : Point2) :
    |inner ℝ vector (wz1Perp2 data.orientedDirection)| =
      |inner ℝ vector (wz1Perp2 direction)| := by
  rcases data.orientedDirection_eq with h | h
  · rw [h]
  · rw [h, wz1Lemma49_perp_neg, inner_neg_right, abs_neg]

/-- The oriented perpendicular coordinate is the original coordinate or its
negative. -/
lemma WZ1Lemma49ActiveViewpointData.inner_perp_oriented_eq
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    {base direction : Point2}
    {width activeWidth : ℝ}
    (data :
      WZ1Lemma49ActiveViewpointData
        F G₁ G₂ H density base direction width activeWidth)
    (vector : Point2) :
    inner ℝ vector (wz1Perp2 data.orientedDirection) =
        inner ℝ vector (wz1Perp2 direction) ∨
      inner ℝ vector (wz1Perp2 data.orientedDirection) =
        -inner ℝ vector (wz1Perp2 direction) := by
  rcases data.orientedDirection_eq with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by
      rw [h, wz1Lemma49_perp_neg, inner_neg_right])

/-- The residual width inequality implies that the active common width is
strictly larger than the original `G₁` strip width. -/
lemma wz1Lemma49_input_width_lt_active_width
    {delta epsilon width activeWidth : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hwidth : 0 < width)
    (hlarge :
      Real.rpow delta
          (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) *
        width < activeWidth) :
    width < activeWidth := by
  have hauxLt :
      wz1Lemma49AuxiliaryEpsilon epsilon < epsilon := by
    dsimp only [wz1Lemma49AuxiliaryEpsilon]
    have hepsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hepsilonHundred : epsilon < 100 := hepsilonOne.trans (by norm_num)
    nlinarith [mul_lt_mul_of_pos_left hepsilonHundred hepsilon]
  have hexponent :
      -epsilon + wz1Lemma49AuxiliaryEpsilon epsilon ≤ 0 := by
    linarith
  have hfactor :
      1 ≤
        Real.rpow delta
          (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdeltaOne hexponent
  calc
    width = 1 * width := by ring
    _ ≤
        Real.rpow delta
            (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) *
          width := by
      gcongr
    _ < activeWidth := hlarge

/-- Select the paper's actual active `G₂` viewpoint and its dense actual
`G₁` fiber. -/
theorem wz1_lemma49_active_viewpoint
    {delta width density : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity :
      WZ1UniformTripleDensity
        (ENNReal.ofReal density) F G₁ G₂ H)
    (base direction : Point2)
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width)
    (hdeltaWidth : delta ≤ width)
    (hG₁strip :
      ∀ second ∈ G₁,
        second ∈ wz1LineNeighborhood base direction width)
    (hactiveLarge :
      width <
        wz1ActiveCommonWidth
          delta H hDensity.1 base direction) :
    Nonempty
      (WZ1Lemma49ActiveViewpointData
        F G₁ G₂ H (ENNReal.ofReal density)
        base direction width
        (wz1ActiveCommonWidth
          delta H hDensity.1 base direction)) := by
  classical
  let perpendicular := wz1Perp2 direction
  let widths : Finset ℝ :=
    H.image fun edge =>
      max
        |inner ℝ (edge.2.1 - base) perpendicular|
        |inner ℝ (edge.2.2 - base) perpendicular|
  have hwidths : widths.Nonempty :=
    hDensity.1.image fun edge =>
      max
        |inner ℝ (edge.2.1 - base) perpendicular|
        |inner ℝ (edge.2.2 - base) perpendicular|
  let rawWidth := widths.max' hwidths
  let activeWidth :=
    wz1ActiveCommonWidth delta H hDensity.1 base direction
  have hdeltaActive : delta < activeWidth :=
    hdeltaWidth.trans_lt hactiveLarge
  have hactiveEq :
      activeWidth = max delta rawWidth := by
    rfl
  have hdeltaRaw : delta ≤ rawWidth := by
    by_contra hnot
    have hrawDelta : rawWidth < delta := lt_of_not_ge hnot
    have heq : activeWidth = delta := by
      rw [hactiveEq, max_eq_left hrawDelta.le]
    rw [heq] at hdeltaActive
    exact (lt_irrefl delta) hdeltaActive
  have hactiveRaw : activeWidth = rawWidth := by
    rw [hactiveEq, max_eq_right hdeltaRaw]
  have hrawMem : rawWidth ∈ widths :=
    Finset.max'_mem widths hwidths
  rcases Finset.mem_image.mp hrawMem with
    ⟨sourceEdge, hsourceEdge, hsourceWidth⟩
  have hsourceMax :
      max
          |inner ℝ (sourceEdge.2.1 - base) perpendicular|
          |inner ℝ (sourceEdge.2.2 - base) perpendicular| =
        activeWidth := by
    exact hsourceWidth.trans hactiveRaw.symm
  let encodedEdge := wz1TripleCoordinate sourceEdge
  have hencoded :
      encodedEdge ∈ wz1EncodeTriples H :=
    Finset.mem_image.mpr ⟨sourceEdge, hsourceEdge, rfl⟩
  have hsecondG₁ : sourceEdge.2.1 ∈ G₁ := by
    have hsupported := hDensity.2.1 encodedEdge hencoded 1
    simpa [encodedEdge, wz1TripleCoordinate,
      wz1TripleVertexClasses] using hsupported
  have hviewpointG₂ : sourceEdge.2.2 ∈ G₂ := by
    have hsupported := hDensity.2.1 encodedEdge hencoded 2
    simpa [encodedEdge, wz1TripleCoordinate,
      wz1TripleVertexClasses] using hsupported
  have hsecondBound :
      |inner ℝ (sourceEdge.2.1 - base) perpendicular| ≤ width := by
    exact hG₁strip sourceEdge.2.1 hsecondG₁
  have hsecondStrict :
      |inner ℝ (sourceEdge.2.1 - base) perpendicular| < activeWidth :=
    hsecondBound.trans_lt hactiveLarge
  have hviewpointAbs :
      |inner ℝ (sourceEdge.2.2 - base) perpendicular| = activeWidth := by
    have hviewpointLe :
        |inner ℝ (sourceEdge.2.2 - base) perpendicular| ≤ activeWidth := by
      rw [← hsourceMax]
      exact le_max_right _ _
    have hactiveLe :
        activeWidth ≤
          |inner ℝ (sourceEdge.2.2 - base) perpendicular| := by
      by_contra hnot
      have hviewpointStrict :
          |inner ℝ (sourceEdge.2.2 - base) perpendicular| <
            activeWidth := lt_of_not_ge hnot
      have hmaxStrict :
          max
              |inner ℝ (sourceEdge.2.1 - base) perpendicular|
              |inner ℝ (sourceEdge.2.2 - base) perpendicular| <
            activeWidth :=
        (max_lt_iff.mpr ⟨hsecondStrict, hviewpointStrict⟩)
      rw [hsourceMax] at hmaxStrict
      exact (lt_irrefl activeWidth) hmaxStrict
    exact le_antisymm hviewpointLe hactiveLe
  let viewpoint := sourceEdge.2.2
  let viewpointCoordinate :=
    inner ℝ (viewpoint - base) perpendicular
  let orientedDirection :=
    if 0 ≤ viewpointCoordinate then -direction else direction
  have horientedUnit : ‖orientedDirection‖ = 1 := by
    dsimp only [orientedDirection]
    split_ifs <;> simp [hdirection]
  have horientedEq :
      orientedDirection = direction ∨
        orientedDirection = -direction := by
    dsimp only [orientedDirection]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have horientedPerp :
      wz1Perp2 orientedDirection =
        if 0 ≤ viewpointCoordinate then -perpendicular else perpendicular := by
    dsimp only [orientedDirection]
    split_ifs
    · rw [wz1Lemma49_perp_neg]
    · rfl
  let source :=
    kaufmanSecondFiber H sourceEdge.1 viewpoint
  have hsourceNonempty : source.Nonempty := by
    refine ⟨sourceEdge.2.1, ?_⟩
    dsimp only [source, viewpoint, kaufmanSecondFiber]
    exact Finset.mem_image.mpr
      ⟨sourceEdge,
        Finset.mem_filter.mpr ⟨hsourceEdge, rfl, rfl⟩,
        rfl⟩
  have hsourceActual :
      ∀ second ∈ source,
        (sourceEdge.1, second, viewpoint) ∈ H := by
    intro second hsecond
    rcases Finset.mem_image.mp hsecond with
      ⟨edge, hedge, hedgeSecond⟩
    have hedgeH := (Finset.mem_filter.mp hedge).1
    have hedgeFirst := (Finset.mem_filter.mp hedge).2.1
    have hedgeThird := (Finset.mem_filter.mp hedge).2.2
    have hedgeTuple :
        edge = (sourceEdge.1, second, viewpoint) := by
      exact Prod.ext hedgeFirst
        (Prod.ext hedgeSecond hedgeThird)
    rw [← hedgeTuple]
    exact hedgeH
  have hsourceSubset : source ⊆ G₁ := by
    intro second hsecond
    have hedge :=
      hsourceActual second hsecond
    let encoded := wz1TripleCoordinate
      (sourceEdge.1, second, viewpoint)
    have hencoded' :
        encoded ∈ wz1EncodeTriples H :=
      Finset.mem_image.mpr
        ⟨(sourceEdge.1, second, viewpoint), hedge, rfl⟩
    have hsupported := hDensity.2.1 encoded hencoded' 1
    simpa [encoded, wz1TripleCoordinate,
      wz1TripleVertexClasses] using hsupported
  have hsourceDensity :
      ENNReal.ofReal density * G₁.enncard ≤
        (source.card : ENNReal) := by
    dsimp only [source, viewpoint]
    exact
      uniform_density_second_fiber_bound
        hDensity sourceEdge hsourceEdge
  have hsourceStrip :
      ∀ second ∈ source,
        |inner ℝ (second - base)
          (wz1Perp2 orientedDirection)| ≤ (2 * width) / 2 := by
    intro second hsecond
    have hstrip := hG₁strip second (hsourceSubset hsecond)
    change
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ width
        at hstrip
    rw [show (2 * width) / 2 = width by ring]
    change
      |inner ℝ (second - base)
          (wz1Perp2 orientedDirection)| ≤ width
    rw [horientedPerp]
    split_ifs
    · simpa [inner_neg_right, abs_neg] using hstrip
    · exact hstrip
  have hsidePos : 0 < 2 * (activeWidth - width) := by
    linarith
  have hsourceSide :
      ∀ second ∈ source,
        (2 * (activeWidth - width)) / 2 ≤
          inner ℝ (second - viewpoint)
            (wz1Perp2 orientedDirection) := by
    intro second hsecond
    have hstrip := hG₁strip second (hsourceSubset hsecond)
    rw [show (2 * (activeWidth - width)) / 2 =
      activeWidth - width by ring]
    change
      activeWidth - width ≤
        inner ℝ (second - viewpoint)
          (wz1Perp2 orientedDirection)
    rw [horientedPerp]
    by_cases hsign : 0 ≤ viewpointCoordinate
    · rw [if_pos hsign, inner_neg_right]
      have hviewpointCoordinate :
          viewpointCoordinate = activeWidth := by
        have habs :
            |viewpointCoordinate| = activeWidth := by
          simpa [viewpointCoordinate, viewpoint, perpendicular]
            using hviewpointAbs
        rw [abs_of_nonneg hsign] at habs
        exact habs
      have hsecondUpper :
          inner ℝ (second - base) perpendicular ≤ width :=
        (abs_le.mp hstrip).2
      have heq :
          -inner ℝ (second - viewpoint) perpendicular =
            viewpointCoordinate -
              inner ℝ (second - base) perpendicular := by
        dsimp only [viewpointCoordinate]
        simp only [inner_sub_left]
        ring
      rw [heq, hviewpointCoordinate]
      linarith
    · rw [if_neg hsign]
      have hsign' : viewpointCoordinate < 0 := lt_of_not_ge hsign
      have hviewpointCoordinate :
          viewpointCoordinate = -activeWidth := by
        have habs :
            |viewpointCoordinate| = activeWidth := by
          simpa [viewpointCoordinate, viewpoint, perpendicular]
            using hviewpointAbs
        rw [abs_of_neg hsign'] at habs
        linarith
      have hsecondLower :
          -width ≤ inner ℝ (second - base) perpendicular :=
        (abs_le.mp hstrip).1
      have heq :
          inner ℝ (second - viewpoint) perpendicular =
            inner ℝ (second - base) perpendicular -
              viewpointCoordinate := by
        dsimp only [viewpointCoordinate]
        simp only [inner_sub_left]
        ring
      rw [heq, hviewpointCoordinate]
      linarith
  exact
    ⟨{ sourceEdge := sourceEdge
       sourceEdge_mem := hsourceEdge
       viewpoint := viewpoint
       viewpoint_eq := rfl
       viewpoint_mem := hviewpointG₂
       orientedDirection := orientedDirection
       orientedDirection_unit := horientedUnit
       orientedDirection_eq := horientedEq
       source := source
       source_eq := rfl
       source_nonempty := hsourceNonempty
       source_subset := hsourceSubset
       source_density := hsourceDensity
       source_actual := hsourceActual
       source_strip := hsourceStrip
       side := 2 * (activeWidth - width)
       side_eq := rfl
       side_pos := hsidePos
       source_side := hsourceSide }⟩

end

end Kakeya.Assouad
