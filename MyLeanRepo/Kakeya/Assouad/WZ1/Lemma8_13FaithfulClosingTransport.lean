import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements

/-!
# Exact graph transport for the faithful Lemma 8.13 closing

These lemmas retain the actual incidence-graph fiber and transport its
normalized projection back to source dot differences with the exact affine
factor `4 * normalizationWidth * endpointDistance`.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The selected incidence-graph fiber is contained in the corresponding
fiber of the same final tripartite graph. -/
lemma wz1Lemma8_13_faithful_closing_fiber_subset
    {delta epsilon : ℝ}
    {input :
      WZ1Lemma8_13ResidualInput delta epsilon
        (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine :
      WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    {kaufman :
      WZ1Lemma8_13FaithfulKaufmanInputData affine}
    (direction : Point2)
    (incidenceGraph : Finset (Point2 × Point2))
    (incidenceWitness :
      ∀ edge ∈ incidenceGraph,
        ∃ finalEdge ∈ kaufman.finalH,
          finalEdge.1 = edge.2 ∧
            finalEdge.2.1 =
              kaufman.firstEndpoint edge.1 ∧
            finalEdge.2.2 =
              kaufman.secondEndpoint edge.1) :
    (incidenceGraph.filter fun edge =>
        edge.1 = direction).image Prod.snd ⊆
      kaufmanFiber kaufman.finalH
        (kaufman.firstEndpoint direction)
        (kaufman.secondEndpoint direction) := by
  intro point hpoint
  rcases Finset.mem_image.mp hpoint with
    ⟨edge, hedge, rfl⟩
  have hedgeGraph : edge ∈ incidenceGraph :=
    (Finset.mem_filter.mp hedge).1
  have hedgeDirection : edge.1 = direction :=
    (Finset.mem_filter.mp hedge).2
  rcases incidenceWitness edge hedgeGraph with
    ⟨finalEdge, hfinalEdge, hfirst, hsecond, hthird⟩
  have hsecondDirection :
      finalEdge.2.1 =
        kaufman.firstEndpoint direction := by
    rw [← hedgeDirection]
    exact hsecond
  have hthirdDirection :
      finalEdge.2.2 =
        kaufman.secondEndpoint direction := by
    rw [← hedgeDirection]
    exact hthird
  exact Finset.mem_image.mpr
    ⟨finalEdge,
      Finset.mem_filter.mpr
        ⟨hfinalEdge, hsecondDirection, hthirdDirection⟩,
      hfirst⟩

/-- The exact affine dot identity transports the normalized selected
incidence fiber into the original dot-difference set, while unit-ball
containment bounds the transported values by the same radius. -/
lemma wz1Lemma8_13_faithful_closing_transport_subset
    {delta epsilon : ℝ}
    {input :
      WZ1Lemma8_13ResidualInput delta epsilon
        (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine :
      WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    {kaufman :
      WZ1Lemma8_13FaithfulKaufmanInputData affine}
    (direction : Point2)
    (hdirection : direction ∈ kaufman.radial.directions)
    (incidenceGraph : Finset (Point2 × Point2))
    (incidenceWitness :
      ∀ edge ∈ incidenceGraph,
        ∃ finalEdge ∈ kaufman.finalH,
          finalEdge.1 = edge.2 ∧
            finalEdge.2.1 =
              kaufman.firstEndpoint edge.1 ∧
            finalEdge.2.2 =
              kaufman.secondEndpoint edge.1) :
    let normalizationWidth :=
      wz1Lemma8_13FaithfulNormalizationWidth input
    let endpointDistance :=
      dist (kaufman.firstEndpoint direction)
        (kaufman.secondEndpoint direction)
    let transportedRadius :=
      4 * normalizationWidth * endpointDistance
    (fun value : ℝ => transportedRadius * value) ''
          (inner ℝ direction ''
            ((incidenceGraph.filter fun edge =>
              edge.1 = direction).image Prod.snd :
                Set Point2)) ⊆
      wz1DotDifferenceSet input.H ∩
        Metric.closedBall 0 transportedRadius := by
  dsimp only
  let normalizationWidth :=
    wz1Lemma8_13FaithfulNormalizationWidth input
  let endpointDistance :=
    dist (kaufman.firstEndpoint direction)
      (kaufman.secondEndpoint direction)
  let transportedRadius :=
    4 * normalizationWidth * endpointDistance
  intro value hvalue
  rcases hvalue with ⟨projection, hprojection, rfl⟩
  rcases hprojection with ⟨point, hpoint, rfl⟩
  rcases Finset.mem_image.mp hpoint with
    ⟨edge, hedge, hpointEdge⟩
  have hedgeGraph : edge ∈ incidenceGraph :=
    (Finset.mem_filter.mp hedge).1
  have hedgeDirection : edge.1 = direction :=
    (Finset.mem_filter.mp hedge).2
  rcases incidenceWitness edge hedgeGraph with
    ⟨finalEdge, hfinalEdge, hfirst, hsecond, hthird⟩
  have hpointFinal : point = finalEdge.1 :=
    hpointEdge.symm.trans hfirst.symm
  have hsecondDirection :
      finalEdge.2.1 =
        kaufman.firstEndpoint direction := by
    rw [← hedgeDirection]
    exact hsecond
  have hthirdDirection :
      finalEdge.2.2 =
        kaufman.secondEndpoint direction := by
    rw [← hedgeDirection]
    exact hthird
  rcases kaufman.sourceWitness finalEdge hfinalEdge with
    ⟨sourceEdge, hsourceEdge, _, hfinalSource⟩
  have hnormalizationWidth :
      0 < normalizationWidth := by
    simpa [normalizationWidth] using
      affine.normalizationWidth_pos
  have haspect :
      0 < wz1Lemma8_13FaithfulAspect input :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hendpointDistance :
      0 < endpointDistance := by
    have hlower :=
      kaufman.endpointDistance_lower direction hdirection
    have hpositive :
        0 <
          1 / (4 * wz1Lemma8_13FaithfulAspect input) := by
      positivity
    simpa [endpointDistance] using hpositive.trans_le hlower
  let endpointVector :=
    kaufman.firstEndpoint direction -
      kaufman.secondEndpoint direction
  have hendpointNorm :
      ‖endpointVector‖ = endpointDistance := by
    simp [endpointVector, endpointDistance, dist_eq_norm]
  have hdirectionEq :
      direction =
        (‖endpointVector‖⁻¹ : ℝ) • endpointVector := by
    simpa [endpointVector] using
      kaufman.direction_eq direction hdirection
  have hendpointVector :
      endpointVector = endpointDistance • direction := by
    have hscaled :
        endpointDistance • direction = endpointVector := by
      rw [hdirectionEq, smul_smul, hendpointNorm]
      rw [mul_inv_cancel₀ hendpointDistance.ne', one_smul]
    exact hscaled.symm
  have hfinalF : finalEdge.1 ∈ kaufman.finalF :=
    (kaufman.finalSupport finalEdge hfinalEdge).1
  have hfinalFNorm : ‖finalEdge.1‖ ≤ 1 := by
    simpa [dist_zero_right] using
      kaufman.finalF_ball finalEdge.1 hfinalF
  have hdirectionNorm : ‖direction‖ = 1 :=
    kaufman.radial.unit direction hdirection
  have hinner :
      |inner ℝ finalEdge.1 direction| ≤ 1 := by
    calc
      |inner ℝ finalEdge.1 direction| ≤
          ‖finalEdge.1‖ * ‖direction‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [hdirectionNorm, mul_one]; exact hfinalFNorm
  have hsourceDot :
      inner ℝ sourceEdge.1
          (sourceEdge.2.1 - sourceEdge.2.2) =
        4 * normalizationWidth *
          inner ℝ finalEdge.1
            (finalEdge.2.1 - finalEdge.2.2) := by
    have htransport :=
      kaufman.sourceDot_eq sourceEdge hsourceEdge
    simpa [normalizationWidth, hfinalSource,
      wz1Lemma8_13FaithfulTripleMap] using htransport
  have hnormalizedDot :
      inner ℝ finalEdge.1
          (finalEdge.2.1 - finalEdge.2.2) =
        endpointDistance *
          inner ℝ finalEdge.1 direction := by
    have hdifference :
        finalEdge.2.1 - finalEdge.2.2 =
          endpointVector := by
      rw [hsecondDirection, hthirdDirection]
    rw [hdifference, hendpointVector, inner_smul_right]
  have hinnerPoint :
      inner ℝ direction point =
        inner ℝ finalEdge.1 direction := by
    calc
      inner ℝ direction point =
          inner ℝ point direction :=
        (real_inner_comm direction point).symm
      _ = inner ℝ finalEdge.1 direction := by
        rw [hpointFinal]
  have htransport :
      transportedRadius * inner ℝ direction point =
        inner ℝ sourceEdge.1
          (sourceEdge.2.1 - sourceEdge.2.2) := by
    calc
      transportedRadius * inner ℝ direction point =
          transportedRadius *
            inner ℝ finalEdge.1 direction := by
        rw [hinnerPoint]
      _ =
          4 * normalizationWidth *
            (endpointDistance *
              inner ℝ finalEdge.1 direction) := by
        dsimp only [transportedRadius]
        ring
      _ =
          inner ℝ sourceEdge.1
            (sourceEdge.2.1 - sourceEdge.2.2) := by
        rw [← hnormalizedDot, ← hsourceDot]
  have hdotDifference :
      transportedRadius * inner ℝ direction point ∈
        wz1DotDifferenceSet input.H := by
    rw [htransport]
    exact Finset.mem_image.mpr
      ⟨sourceEdge, hsourceEdge, rfl⟩
  have htransportedRadius :
      0 ≤ transportedRadius := by
    dsimp only [transportedRadius]
    positivity
  have hball :
      |transportedRadius *
          inner ℝ direction point| ≤ transportedRadius := by
    calc
      |transportedRadius * inner ℝ direction point| =
          transportedRadius *
            |inner ℝ finalEdge.1 direction| := by
        rw [abs_mul, abs_of_nonneg htransportedRadius,
          hinnerPoint]
      _ ≤ transportedRadius * 1 :=
        mul_le_mul_of_nonneg_left hinner htransportedRadius
      _ = transportedRadius := mul_one _
  have hclosedBall :
      transportedRadius * inner ℝ direction point ∈
        Metric.closedBall 0 transportedRadius := by
    simpa [Metric.mem_closedBall, dist_eq_norm,
      Real.norm_eq_abs] using hball
  exact ⟨hdotDifference, hclosedBall⟩

end

end Kakeya.Assouad
