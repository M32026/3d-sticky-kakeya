import MyLeanRepo.Kakeya.Assouad.WZ1.GridPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements

/-!
# Paper localization for a common-endpoint projection graph

The final reduction from WZ1 Theorem 22 first removes edges whose first
vertex is too close to the origin or whose two endpoint vertices are too
close to one another.  It then pigeonholes the remaining graph into three
small planar grid cells.

This module records that literal operation.  In particular, the selected
vertex classes are the *active coordinate projections* of the selected
subgraph; no unused ambient vertices are inserted.  Quantitative removal,
Frostman normalization, and the later affine similarities are deliberately
left to separate modules.
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

/-- Edges on which both non-degeneracy conditions in the final reduction
hold. -/
def wz1CommonEndpointGoodEdges
    (threshold : ℝ)
    (H : Finset (Point2 × Point2 × Point2)) :
    Finset (Point2 × Point2 × Point2) :=
  H.filter fun edge =>
    threshold ≤ dist edge.1 0 ∧
      threshold ≤ dist edge.2.1 edge.2.2

/-- The part of a tripartite graph lying in three prescribed planar grid
cells. -/
def wz1CommonEndpointGridBlock
    (gridScale : ℝ)
    (centerF centerG₁ centerG₂ : Point2)
    (H : Finset (Point2 × Point2 × Point2)) :
    Finset (Point2 × Point2 × Point2) :=
  H.filter fun edge =>
    gridCenter gridScale edge.1 = centerF ∧
      gridCenter gridScale edge.2.1 = centerG₁ ∧
      gridCenter gridScale edge.2.2 = centerG₂

/-- The exact output of the good-edge and product-grid localization step. -/
structure WZ1CommonEndpointLocalizedGraph
    (threshold gridScale : ℝ)
    (F G : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) where
  good : Finset (Point2 × Point2 × Point2)
  good_eq : good = wz1CommonEndpointGoodEdges threshold H
  centerF : Point2
  centerG₁ : Point2
  centerG₂ : Point2
  block : Finset (Point2 × Point2 × Point2)
  block_eq :
    block =
      wz1CommonEndpointGridBlock gridScale
        centerF centerG₁ centerG₂ good
  block_card :
    Nat.ceil ((good.card : ℝ) / (1000000 / gridScale ^ 6)) ≤
      block.card
  selectedF : DiscreteSet 2 := wz1ActiveTripleProjection block 0
  selectedG₁ : DiscreteSet 2 := wz1ActiveTripleProjection block 1
  selectedG₂ : DiscreteSet 2 := wz1ActiveTripleProjection block 2
  selectedF_eq : selectedF = wz1ActiveTripleProjection block 0
  selectedG₁_eq : selectedG₁ = wz1ActiveTripleProjection block 1
  selectedG₂_eq : selectedG₂ = wz1ActiveTripleProjection block 2
  edge_support :
    ∀ edge ∈ block,
      edge.1 ∈ selectedF ∧
        edge.2.1 ∈ selectedG₁ ∧
        edge.2.2 ∈ selectedG₂
  selectedF_subset : selectedF ⊆ F
  selectedG₁_subset : selectedG₁ ⊆ G
  selectedG₂_subset : selectedG₂ ⊆ G
  first_grid :
    ∀ edge ∈ block, gridCenter gridScale edge.1 = centerF
  second_grid :
    ∀ edge ∈ block, gridCenter gridScale edge.2.1 = centerG₁
  third_grid :
    ∀ edge ∈ block, gridCenter gridScale edge.2.2 = centerG₂
  first_far :
    ∀ edge ∈ block, threshold ≤ dist edge.1 0
  endpoints_far :
    ∀ edge ∈ block, threshold ≤ dist edge.2.1 edge.2.2

/-- Select the paper localization from a graph supported in `F × G × G`. -/
theorem wz1_common_endpoint_localize
    {threshold gridScale : ℝ}
    {F G : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hgrid : 0 < gridScale) (hgridOne : gridScale ≤ 1)
    (hsupport :
      ∀ edge ∈ H, edge.1 ∈ F ∧ edge.2.1 ∈ G ∧ edge.2.2 ∈ G)
    (hFball : F.IsInUnitBall) (hGball : G.IsInUnitBall) :
    Nonempty
      (WZ1CommonEndpointLocalizedGraph
        threshold gridScale F G H) := by
  let good := wz1CommonEndpointGoodEdges threshold H
  have hgoodSupport :
      ∀ edge ∈ good,
        edge.1 ∈ F ∧ edge.2.1 ∈ G ∧ edge.2.2 ∈ G := by
    intro edge hedge
    exact hsupport edge (Finset.mem_filter.mp hedge).1
  rcases grid_pigeonhole_edges hgrid hgridOne hgoodSupport
      hFball hGball hGball with
    ⟨centerF, centerG₁, centerG₂, hcard⟩
  let block :=
    wz1CommonEndpointGridBlock gridScale
      centerF centerG₁ centerG₂ good
  let selectedF := wz1ActiveTripleProjection block 0
  let selectedG₁ := wz1ActiveTripleProjection block 1
  let selectedG₂ := wz1ActiveTripleProjection block 2
  have hblockGood : block ⊆ good := by
    exact Finset.filter_subset _ _
  have hblockH : block ⊆ H := by
    intro edge hedge
    exact (Finset.mem_filter.mp (hblockGood hedge)).1
  have hedgeSupport :
      ∀ edge ∈ block,
        edge.1 ∈ selectedF ∧
          edge.2.1 ∈ selectedG₁ ∧
          edge.2.2 ∈ selectedG₂ := by
    intro edge hedge
    refine ⟨?_, ?_, ?_⟩
    all_goals
      exact Finset.mem_image.mpr ⟨edge, hedge, by rfl⟩
  have hFsubset : selectedF ⊆ F := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    exact (hsupport edge (hblockH hedge)).1
  have hG₁subset : selectedG₁ ⊆ G := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    exact (hsupport edge (hblockH hedge)).2.1
  have hG₂subset : selectedG₂ ⊆ G := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    exact (hsupport edge (hblockH hedge)).2.2
  have hblockRelations :
      ∀ edge ∈ block,
        gridCenter gridScale edge.1 = centerF ∧
          gridCenter gridScale edge.2.1 = centerG₁ ∧
          gridCenter gridScale edge.2.2 = centerG₂ := by
    intro edge hedge
    exact (Finset.mem_filter.mp hedge).2
  have hgoodRelations :
      ∀ edge ∈ block,
        threshold ≤ dist edge.1 0 ∧
          threshold ≤ dist edge.2.1 edge.2.2 := by
    intro edge hedge
    exact (Finset.mem_filter.mp (hblockGood hedge)).2
  exact ⟨{
    good := good
    good_eq := rfl
    centerF := centerF
    centerG₁ := centerG₁
    centerG₂ := centerG₂
    block := block
    block_eq := rfl
    block_card := by simpa [block, wz1CommonEndpointGridBlock] using hcard
    selectedF := selectedF
    selectedG₁ := selectedG₁
    selectedG₂ := selectedG₂
    selectedF_eq := rfl
    selectedG₁_eq := rfl
    selectedG₂_eq := rfl
    edge_support := hedgeSupport
    selectedF_subset := hFsubset
    selectedG₁_subset := hG₁subset
    selectedG₂_subset := hG₂subset
    first_grid := fun edge hedge => (hblockRelations edge hedge).1
    second_grid := fun edge hedge => (hblockRelations edge hedge).2.1
    third_grid := fun edge hedge => (hblockRelations edge hedge).2.2
    first_far := fun edge hedge => (hgoodRelations edge hedge).1
    endpoints_far := fun edge hedge => (hgoodRelations edge hedge).2
  }⟩

namespace WZ1CommonEndpointLocalizedGraph

/-- Every selected coordinate class lies in one grid cell and hence has
diameter at most twice the grid scale. -/
lemma selected_diameter
    {threshold gridScale : ℝ}
    {F G : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (localized :
      WZ1CommonEndpointLocalizedGraph threshold gridScale F G H)
    (hgrid : 0 < gridScale) :
    (∀ first ∈ localized.selectedF,
      ∀ second ∈ localized.selectedF,
        dist first second ≤ 2 * gridScale) ∧
    (∀ first ∈ localized.selectedG₁,
      ∀ second ∈ localized.selectedG₁,
        dist first second ≤ 2 * gridScale) ∧
    (∀ first ∈ localized.selectedG₂,
      ∀ second ∈ localized.selectedG₂,
        dist first second ≤ 2 * gridScale) := by
  have hdiam :
      ∀ (index : Fin 3) (center : Point2),
        (∀ edge ∈ localized.block,
          gridCenter gridScale (wz1TripleCoordinate edge index) = center) →
        ∀ first ∈ wz1ActiveTripleProjection localized.block index,
          ∀ second ∈ wz1ActiveTripleProjection localized.block index,
            dist first second ≤ 2 * gridScale := by
    intro index center hcenter first hfirst second hsecond
    rcases Finset.mem_image.mp hfirst with ⟨firstEdge, hfirstEdge, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondEdge, hsecondEdge, rfl⟩
    apply grid_cell_diameter_2d gridScale hgrid
    exact (hcenter firstEdge hfirstEdge).trans
      (hcenter secondEdge hsecondEdge).symm
  constructor
  · intro first hfirst second hsecond
    rw [localized.selectedF_eq] at hfirst hsecond
    exact hdiam 0 localized.centerF
      (fun edge hedge => localized.first_grid edge hedge)
      first hfirst second hsecond
  constructor
  · intro first hfirst second hsecond
    rw [localized.selectedG₁_eq] at hfirst hsecond
    exact hdiam 1 localized.centerG₁
      (fun edge hedge => localized.second_grid edge hedge)
      first hfirst second hsecond
  · intro first hfirst second hsecond
    rw [localized.selectedG₂_eq] at hfirst hsecond
    exact hdiam 2 localized.centerG₂
      (fun edge hedge => localized.third_grid edge hedge)
      first hfirst second hsecond

/-- The non-degeneracy retained on actual edges propagates to every active
vertex and every cross-class endpoint pair, paying at most two grid-cell
diameters. -/
lemma selected_far
    {threshold gridScale : ℝ}
    {F G : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (localized :
      WZ1CommonEndpointLocalizedGraph threshold gridScale F G H)
    (hgrid : 0 < gridScale) :
    (∀ point ∈ localized.selectedF,
      threshold - 2 * gridScale ≤ dist point 0) ∧
    WZ1MutuallySeparated localized.selectedG₁ localized.selectedG₂
      (threshold - 4 * gridScale) := by
  rcases localized.selected_diameter hgrid with
    ⟨hFdiam, hG₁diam, hG₂diam⟩
  constructor
  · intro point hpoint
    rw [localized.selectedF_eq] at hpoint
    rcases Finset.mem_image.mp hpoint with ⟨edge, hedge, rfl⟩
    have hfar : threshold ≤ dist edge.1 0 :=
      localized.first_far edge hedge
    simpa [wz1TripleCoordinate] using
      (show threshold - 2 * gridScale ≤ dist edge.1 0 by linarith)
  · intro first hfirst second hsecond
    rw [localized.selectedG₁_eq] at hfirst
    rw [localized.selectedG₂_eq] at hsecond
    rcases Finset.mem_image.mp hfirst with ⟨firstEdge, hfirstEdge, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondEdge, hsecondEdge, rfl⟩
    have hfirstG₂ : firstEdge.2.2 ∈ localized.selectedG₂ := by
      rw [localized.selectedG₂_eq]
      exact Finset.mem_image.mpr
        ⟨firstEdge, hfirstEdge, by simp [wz1TripleCoordinate]⟩
    have hsecondG₂ : secondEdge.2.2 ∈ localized.selectedG₂ := by
      rw [localized.selectedG₂_eq]
      exact Finset.mem_image.mpr
        ⟨secondEdge, hsecondEdge, by simp [wz1TripleCoordinate]⟩
    have hsameSecond :
        dist firstEdge.2.2 secondEdge.2.2 ≤ 2 * gridScale := by
      exact hG₂diam firstEdge.2.2 hfirstG₂
        secondEdge.2.2 hsecondG₂
    have htriangle :
        dist firstEdge.2.1 firstEdge.2.2 ≤
          dist firstEdge.2.1 secondEdge.2.2 +
            dist secondEdge.2.2 firstEdge.2.2 :=
      dist_triangle firstEdge.2.1 secondEdge.2.2 firstEdge.2.2
    have hdist :
        threshold ≤
          dist firstEdge.2.1 secondEdge.2.2 + 2 * gridScale := by
      calc
        threshold ≤ dist firstEdge.2.1 firstEdge.2.2 :=
          localized.endpoints_far firstEdge hfirstEdge
        _ ≤ dist firstEdge.2.1 secondEdge.2.2 +
              dist secondEdge.2.2 firstEdge.2.2 := htriangle
        _ ≤ dist firstEdge.2.1 secondEdge.2.2 + 2 * gridScale := by
          have hsameSecond' :
              dist secondEdge.2.2 firstEdge.2.2 ≤ 2 * gridScale := by
            simpa only [dist_comm] using hsameSecond
          simpa [add_comm] using
            add_le_add_left hsameSecond'
              (dist firstEdge.2.1 secondEdge.2.2)
    simpa [wz1TripleCoordinate] using
      (show threshold - 4 * gridScale ≤
          dist firstEdge.2.1 secondEdge.2.2 by linarith)

/-- The localized active projections satisfy the exact standard-separation
predicate once the paper scale hierarchy is imposed. -/
theorem toStandardSeparation
    {threshold gridScale : ℝ}
    {F G : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (localized :
      WZ1CommonEndpointLocalizedGraph threshold gridScale F G H)
    (hgrid : 0 < gridScale)
    (hdiameter : 2 * gridScale ≤ 1 / 10)
    (hfar : 1 / 2 + 4 * gridScale ≤ threshold) :
    WZ1StandardSeparation
      localized.selectedF localized.selectedG₁ localized.selectedG₂ := by
  rcases localized.selected_diameter hgrid with
    ⟨hFdiam, hG₁diam, hG₂diam⟩
  rcases localized.selected_far hgrid with ⟨hFfar, hGfar⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro first hfirst second hsecond
    exact (hFdiam first hfirst second hsecond).trans hdiameter
  · intro first hfirst second hsecond
    exact (hG₁diam first hfirst second hsecond).trans hdiameter
  · intro first hfirst second hsecond
    exact (hG₂diam first hfirst second hsecond).trans hdiameter
  · intro first hfirst second hsecond
    exact (by linarith : 1 / 2 ≤ threshold - 4 * gridScale).trans
      (hGfar first hfirst second hsecond)
  · intro point hpoint
    have hfarTwo : 1 / 2 + 2 * gridScale ≤ threshold := by linarith
    exact (by linarith : 1 / 2 ≤ threshold - 2 * gridScale).trans
      (hFfar point hpoint)

end WZ1CommonEndpointLocalizedGraph

end

end Kakeya.Assouad
