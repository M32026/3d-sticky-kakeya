import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GraphKatzTao

/-!
# Unit-ball normalization of the actual WZ1 Lemma 23 graph

The paper-normalized graph lies in fixed balls of radii `2,5,5`.  This module
applies the common homothety `point ↦ (1/5) • point` to all three vertex
classes and all three coordinates of every edge.  The resulting graph lies
in the unit ball, stays separated and Katz--Tao at scale
`sqrt rho / (5 * sqrt 3)`, preserves edge cardinality, and scales every
dot-difference value by `1/25`.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Common `1/5` scaling of a Lemma 23 planar vertex. -/
def wz1Lemma23UnitBallPoint (point : Point2) : Point2 :=
  (1 / 5 : ℝ) • point

/-- Common `1/5` scaling of all three vertices of one tripartite edge. -/
def wz1Lemma23UnitBallEdge
    (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  (wz1Lemma23UnitBallPoint edge.1,
    wz1Lemma23UnitBallPoint edge.2.1,
    wz1Lemma23UnitBallPoint edge.2.2)

/-- Image of a finite planar set under the common unit-ball homothety. -/
def wz1Lemma23UnitBallVertices
    (vertices : DiscreteSet 2) : DiscreteSet 2 :=
  vertices.image wz1Lemma23UnitBallPoint

/-- Image of a tripartite graph under the common unit-ball homothety. -/
def wz1Lemma23UnitBallEdges
    (edges : Finset (Point2 × Point2 × Point2)) :
    Finset (Point2 × Point2 × Point2) :=
  edges.image wz1Lemma23UnitBallEdge

private lemma wz1Lemma23UnitBallPoint_injective :
    Function.Injective wz1Lemma23UnitBallPoint := by
  intro first second h
  exact
    smul_right_injective Point2 (by norm_num : (1 / 5 : ℝ) ≠ 0) h

private lemma wz1Lemma23UnitBallEdge_injective :
    Function.Injective wz1Lemma23UnitBallEdge := by
  intro first second h
  have hfirst :
      wz1Lemma23UnitBallPoint first.1 =
        wz1Lemma23UnitBallPoint second.1 :=
    congr_arg Prod.fst h
  have hsecond1 :
      wz1Lemma23UnitBallPoint first.2.1 =
        wz1Lemma23UnitBallPoint second.2.1 :=
    congr_arg (fun edge => edge.2.1) h
  have hsecond2 :
      wz1Lemma23UnitBallPoint first.2.2 =
        wz1Lemma23UnitBallPoint second.2.2 :=
    congr_arg (fun edge => edge.2.2) h
  exact
    Prod.ext
      (wz1Lemma23UnitBallPoint_injective hfirst)
      (Prod.ext
        (wz1Lemma23UnitBallPoint_injective hsecond1)
        (wz1Lemma23UnitBallPoint_injective hsecond2))

/-- One coordinate difference is divided by five by the common homothety. -/
private lemma wz1Lemma23UnitBallPoint_coord_diff
    (first second : Point2) (coordinate : Fin 2) :
    |(wz1Lemma23UnitBallPoint first) coordinate -
        (wz1Lemma23UnitBallPoint second) coordinate| =
      |first coordinate - second coordinate| / 5 := by
  simp [wz1Lemma23UnitBallPoint]
  rw [show (5 : ℝ)⁻¹ * first coordinate -
      (5 : ℝ)⁻¹ * second coordinate =
        (first coordinate - second coordinate) / 5 by ring]
  rw [abs_div]
  norm_num

/-- Scaling all three vertices divides a tripartite dot difference by 25. -/
private lemma wz1Lemma23UnitBallEdge_dot
    (edge : Point2 × Point2 × Point2) :
    inner ℝ (wz1Lemma23UnitBallEdge edge).1
        ((wz1Lemma23UnitBallEdge edge).2.1 -
          (wz1Lemma23UnitBallEdge edge).2.2) =
      inner ℝ edge.1 (edge.2.1 - edge.2.2) / 25 := by
  change
    inner ℝ ((1 / 5 : ℝ) • edge.1)
        (((1 / 5 : ℝ) • edge.2.1) -
          ((1 / 5 : ℝ) • edge.2.2)) =
      inner ℝ edge.1 (edge.2.1 - edge.2.2) / 25
  rw [← smul_sub, inner_smul_left, inner_smul_right]
  norm_num
  ring

/--
The actual normalized graph after the final common homothety into the unit
ball.
-/
structure WZ1Lemma23UnitBallGraph
    (rho : ℝ)
    (sourceF sourceG₁ sourceG₂ : DiscreteSet 2)
    (sourceH : Finset (Point2 × Point2 × Point2)) where
  F : DiscreteSet 2 :=
    wz1Lemma23UnitBallVertices sourceF
  G₁ : DiscreteSet 2 :=
    wz1Lemma23UnitBallVertices sourceG₁
  G₂ : DiscreteSet 2 :=
    wz1Lemma23UnitBallVertices sourceG₂
  H : Finset (Point2 × Point2 × Point2) :=
    wz1Lemma23UnitBallEdges sourceH
  F_eq : F = wz1Lemma23UnitBallVertices sourceF
  G₁_eq : G₁ = wz1Lemma23UnitBallVertices sourceG₁
  G₂_eq : G₂ = wz1Lemma23UnitBallVertices sourceG₂
  H_eq : H = wz1Lemma23UnitBallEdges sourceH
  edge_support :
    ∀ edge ∈ H,
      edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂
  edge_card : H.card = sourceH.card
  F_unit : F.IsInUnitBall
  G₁_unit : G₁.IsInUnitBall
  G₂_unit : G₂.IsInUnitBall
  F_separated :
    F.IsDeltaSeparated
      (Real.sqrt rho / (5 * Real.sqrt 3))
  G₁_separated :
    G₁.IsDeltaSeparated
      (Real.sqrt rho / (5 * Real.sqrt 3))
  G₂_separated :
    G₂.IsDeltaSeparated
      (Real.sqrt rho / (5 * Real.sqrt 3))
  F_katzTao :
    F.IsKatzTao
      (Real.sqrt rho / (5 * Real.sqrt 3)) 1 4
  G₁_katzTao :
    G₁.IsKatzTao
      (Real.sqrt rho / (5 * Real.sqrt 3)) 1 4
  G₂_katzTao :
    G₂.IsKatzTao
      (Real.sqrt rho / (5 * Real.sqrt 3)) 1 4
  dot_image :
    wz1DotDifferenceSet H =
      (fun value : ℝ => value / 25) ''
        wz1DotDifferenceSet sourceH

/--
Construct the final common unit-ball normalization from one bounded,
coordinate-separated actual graph.
-/
theorem wz1_lemma23_unit_ball_graph
    {rho : ℝ} (hrho : 0 < rho)
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    (hsupport :
      ∀ edge ∈ sourceH,
        edge.1 ∈ sourceF ∧
          edge.2.1 ∈ sourceG₁ ∧ edge.2.2 ∈ sourceG₂)
    (hFbound : ∀ point ∈ sourceF, dist point 0 ≤ 2)
    (hG₁bound : ∀ point ∈ sourceG₁, dist point 0 ≤ 5)
    (hG₂bound : ∀ point ∈ sourceG₂, dist point 0 ≤ 5)
    (hFcoord :
      ∀ first ∈ sourceF, ∀ second ∈ sourceF,
        first ≠ second →
          Real.sqrt rho / Real.sqrt 3 ≤
            |first 0 - second 0|)
    (hG₁coord :
      ∀ first ∈ sourceG₁, ∀ second ∈ sourceG₁,
        first ≠ second →
          Real.sqrt rho / Real.sqrt 3 ≤
            |first 1 - second 1|)
    (hG₂coord :
      ∀ first ∈ sourceG₂, ∀ second ∈ sourceG₂,
        first ≠ second →
          Real.sqrt rho / Real.sqrt 3 ≤
            |first 1 - second 1|) :
    Nonempty
      (WZ1Lemma23UnitBallGraph
        rho sourceF sourceG₁ sourceG₂ sourceH) := by
  let F := wz1Lemma23UnitBallVertices sourceF
  let G₁ := wz1Lemma23UnitBallVertices sourceG₁
  let G₂ := wz1Lemma23UnitBallVertices sourceG₂
  let H := wz1Lemma23UnitBallEdges sourceH
  have hscale :
      (Real.sqrt rho / Real.sqrt 3) / 5 =
        Real.sqrt rho / (5 * Real.sqrt 3) := by
    ring
  have hsupportScaled :
      ∀ edge ∈ H,
        edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂ := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with
      ⟨sourceEdge, hsourceEdge, rfl⟩
    have hs := hsupport sourceEdge hsourceEdge
    exact
      ⟨Finset.mem_image.mpr ⟨sourceEdge.1, hs.1, rfl⟩,
        Finset.mem_image.mpr ⟨sourceEdge.2.1, hs.2.1, rfl⟩,
        Finset.mem_image.mpr ⟨sourceEdge.2.2, hs.2.2, rfl⟩⟩
  have hcard : H.card = sourceH.card :=
    Finset.card_image_of_injective
      sourceH wz1Lemma23UnitBallEdge_injective
  have hFunit : F.IsInUnitBall := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsource : ‖sourcePoint‖ ≤ 2 := by
      simpa [dist_zero_right] using
        hFbound sourcePoint hsourcePoint
    rw [dist_zero_right]
    calc
      ‖wz1Lemma23UnitBallPoint sourcePoint‖ =
          (1 / 5 : ℝ) * ‖sourcePoint‖ := by
        simp [wz1Lemma23UnitBallPoint, norm_smul,
          Real.norm_eq_abs]
      _ ≤ (1 / 5 : ℝ) * 2 := by gcongr
      _ ≤ 1 := by norm_num
  have hG₁unit : G₁.IsInUnitBall := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsource : ‖sourcePoint‖ ≤ 5 := by
      simpa [dist_zero_right] using
        hG₁bound sourcePoint hsourcePoint
    rw [dist_zero_right]
    calc
      ‖wz1Lemma23UnitBallPoint sourcePoint‖ =
          (1 / 5 : ℝ) * ‖sourcePoint‖ := by
        simp [wz1Lemma23UnitBallPoint, norm_smul,
          Real.norm_eq_abs]
      _ ≤ (1 / 5 : ℝ) * 5 := by gcongr
      _ = 1 := by norm_num
  have hG₂unit : G₂.IsInUnitBall := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsource : ‖sourcePoint‖ ≤ 5 := by
      simpa [dist_zero_right] using
        hG₂bound sourcePoint hsourcePoint
    rw [dist_zero_right]
    calc
      ‖wz1Lemma23UnitBallPoint sourcePoint‖ =
          (1 / 5 : ℝ) * ‖sourcePoint‖ := by
        simp [wz1Lemma23UnitBallPoint, norm_smul,
          Real.norm_eq_abs]
      _ ≤ (1 / 5 : ℝ) * 5 := by gcongr
      _ = 1 := by norm_num
  have hFcoordScaled :
      ∀ first ∈ F, ∀ second ∈ F, first ≠ second →
        Real.sqrt rho / (5 * Real.sqrt 3) ≤
          |first 0 - second 0| := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro h
      exact hne (congr_arg wz1Lemma23UnitBallPoint h)
    have hsource := hFcoord firstSource hfirstSource
      secondSource hsecondSource hsourceNe
    rw [← hscale]
    rw [wz1Lemma23UnitBallPoint_coord_diff]
    exact
      div_le_div_of_nonneg_right hsource
        (by norm_num : (0 : ℝ) ≤ 5)
  have hG₁coordScaled :
      ∀ first ∈ G₁, ∀ second ∈ G₁, first ≠ second →
        Real.sqrt rho / (5 * Real.sqrt 3) ≤
          |first 1 - second 1| := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro h
      exact hne (congr_arg wz1Lemma23UnitBallPoint h)
    have hsource := hG₁coord firstSource hfirstSource
      secondSource hsecondSource hsourceNe
    rw [← hscale]
    rw [wz1Lemma23UnitBallPoint_coord_diff]
    exact
      div_le_div_of_nonneg_right hsource
        (by norm_num : (0 : ℝ) ≤ 5)
  have hG₂coordScaled :
      ∀ first ∈ G₂, ∀ second ∈ G₂, first ≠ second →
        Real.sqrt rho / (5 * Real.sqrt 3) ≤
          |first 1 - second 1| := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro h
      exact hne (congr_arg wz1Lemma23UnitBallPoint h)
    have hsource := hG₂coord firstSource hfirstSource
      secondSource hsecondSource hsourceNe
    rw [← hscale]
    rw [wz1Lemma23UnitBallPoint_coord_diff]
    exact
      div_le_div_of_nonneg_right hsource
        (by norm_num : (0 : ℝ) ≤ 5)
  have hscalePos :
      0 < Real.sqrt rho / (5 * Real.sqrt 3) := by
    positivity
  have hdot :
      wz1DotDifferenceSet H =
        (fun value : ℝ => value / 25) ''
          wz1DotDifferenceSet sourceH := by
    ext value
    constructor
    · intro hvalue
      change value ∈
        H.image (fun edge =>
          inner ℝ edge.1 (edge.2.1 - edge.2.2)) at hvalue
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hvalue) with
        ⟨edge, hedge, rfl⟩
      rcases Finset.mem_image.mp hedge with
        ⟨sourceEdge, hsourceEdge, rfl⟩
      refine ⟨inner ℝ sourceEdge.1
          (sourceEdge.2.1 - sourceEdge.2.2), ?_, ?_⟩
      · change inner ℝ sourceEdge.1
            (sourceEdge.2.1 - sourceEdge.2.2) ∈
          sourceH.image (fun edge =>
            inner ℝ edge.1 (edge.2.1 - edge.2.2))
        exact Finset.mem_image.mpr ⟨sourceEdge, hsourceEdge, rfl⟩
      · exact (wz1Lemma23UnitBallEdge_dot sourceEdge).symm
    · rintro ⟨sourceValue, hsourceValue, rfl⟩
      change sourceValue / 25 ∈
        H.image (fun edge =>
          inner ℝ edge.1 (edge.2.1 - edge.2.2))
      change sourceValue ∈
        sourceH.image (fun edge =>
          inner ℝ edge.1 (edge.2.1 - edge.2.2)) at hsourceValue
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hsourceValue) with
        ⟨sourceEdge, hsourceEdge, rfl⟩
      apply Finset.mem_coe.mpr
      refine Finset.mem_image.mpr
        ⟨wz1Lemma23UnitBallEdge sourceEdge, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨sourceEdge, hsourceEdge, rfl⟩
      · exact wz1Lemma23UnitBallEdge_dot sourceEdge
  exact
    ⟨{ F := F
       G₁ := G₁
       G₂ := G₂
       H := H
       F_eq := rfl
       G₁_eq := rfl
       G₂_eq := rfl
       H_eq := rfl
       edge_support := hsupportScaled
       edge_card := hcard
       F_unit := hFunit
       G₁_unit := hG₁unit
       G₂_unit := hG₂unit
       F_separated :=
         coordinateSeparated_isDeltaSeparated 0 hFcoordScaled
       G₁_separated :=
         coordinateSeparated_isDeltaSeparated 1 hG₁coordScaled
       G₂_separated :=
         coordinateSeparated_isDeltaSeparated 1 hG₂coordScaled
       F_katzTao :=
         coordinateSeparated_isKatzTao hscalePos 0 hFcoordScaled
       G₁_katzTao :=
         coordinateSeparated_isKatzTao hscalePos 1 hG₁coordScaled
       G₂_katzTao :=
         coordinateSeparated_isKatzTao hscalePos 1 hG₂coordScaled
       dot_image := hdot }⟩

/--
Apply the final common unit-ball normalization to a completed windowed
prepared graph.
-/
theorem WZ1Lemma23WindowedPreparedGraph.toUnitBallGraph
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    (package : WZ1Lemma23WindowedPreparedGraph windowed) :
    Nonempty
      (WZ1Lemma23UnitBallGraph
        rho package.graph.prepared.normalized.F
        package.graph.prepared.normalized.G₁
        package.graph.prepared.normalized.G₂
        package.graph.prepared.normalized.H) := by
  rcases package.vertex_bounds with
    ⟨hFbound, hG₁bound, hG₂bound⟩
  rcases package.graph.vertex_coordinate_separation with
    ⟨hFcoord, hG₁coord, hG₂coord⟩
  exact
    wz1_lemma23_unit_ball_graph
      windowed.global.rho_pos
      package.graph.prepared.normalized.edge_support
      hFbound hG₁bound hG₂bound
      hFcoord hG₁coord hG₂coord

end

end Kakeya.Assouad
