import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointWellSeparatedInput
import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Pull back Alternative A through the two paper similarities
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

attribute [local instance] Classical.propDecidable

lemma wz1PositiveSimilarity_mem_lineNeighborhood_pullback
    {center base direction point : Point2} {scale radius : ℝ}
    (hscale : 0 < scale) :
    wz1PositiveSimilarity center scale point ∈
        wz1LineNeighborhood base direction radius →
      point ∈ wz1LineNeighborhood
        (wz1PositiveSimilarityInv center scale base) direction
        (radius / scale) := by
  intro himage
  have hbase :
      base = wz1PositiveSimilarity center scale
        (wz1PositiveSimilarityInv center scale base) :=
    (wz1PositiveSimilarity_apply_inv hscale base).symm
  change |inner ℝ
      (wz1PositiveSimilarity center scale point - base)
      (wz1Perp2 direction)| ≤ radius at himage
  change |inner ℝ
      (point - wz1PositiveSimilarityInv center scale base)
      (wz1Perp2 direction)| ≤ radius / scale
  have hdiff :
      wz1PositiveSimilarity center scale point -
          wz1PositiveSimilarity center scale
            (wz1PositiveSimilarityInv center scale base) =
        scale • (point -
          wz1PositiveSimilarityInv center scale base) := by
    simp [wz1PositiveSimilarity, smul_sub]
  have hinv :
      wz1PositiveSimilarityInv center scale
          (wz1PositiveSimilarity center scale
            (wz1PositiveSimilarityInv center scale base)) =
        wz1PositiveSimilarityInv center scale base := by
    rw [wz1PositiveSimilarityInv_apply hscale]
  have hscaled :
      scale * |inner ℝ
          (point - wz1PositiveSimilarityInv center scale base)
          (wz1Perp2 direction)| ≤ radius := by
    rw [hbase, hdiff, inner_smul_left] at himage
    simpa [abs_mul, abs_of_pos hscale] using himage
  exact (le_div_iff₀ hscale).2 (by simpa [mul_comm] using hscaled)

/-- A line count on a similarity image pulls back to the source at the
inverse-scaled radius. -/
lemma wz1DiscreteLineCount_image_similarity_le
    {A : DiscreteSet 2} {center base direction : Point2}
    {scale imageRadius sourceRadius : ℝ}
    (hscale : 0 < scale)
    (hradius : imageRadius / scale ≤ sourceRadius) :
    wz1DiscreteLineCount
        (A.image (wz1PositiveSimilarity center scale))
        base direction imageRadius ≤
      wz1DiscreteLineCount A
        (wz1PositiveSimilarityInv center scale base)
        direction sourceRadius := by
  let imageSelected :=
    (A.image (wz1PositiveSimilarity center scale)).filter fun point =>
      point ∈ wz1LineNeighborhood base direction imageRadius
  let sourceSelected := A.filter fun point =>
    point ∈ wz1LineNeighborhood
      (wz1PositiveSimilarityInv center scale base) direction sourceRadius
  have hsub : imageSelected ⊆
      sourceSelected.image (wz1PositiveSimilarity center scale) := by
    intro image himage
    rcases Finset.mem_filter.mp himage with ⟨himageMem, himageLine⟩
    rcases Finset.mem_image.mp himageMem with ⟨source, hsource, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨source, Finset.mem_filter.mpr ⟨hsource, ?_⟩, rfl⟩
    have hpull :=
      wz1PositiveSimilarity_mem_lineNeighborhood_pullback hscale himageLine
    exact hpull.trans hradius
  change (((A.image (wz1PositiveSimilarity center scale)).filter fun point =>
      point ∈ wz1LineNeighborhood base direction imageRadius).card : ENNReal) ≤
    ((A.filter fun point => point ∈ wz1LineNeighborhood
      (wz1PositiveSimilarityInv center scale base) direction sourceRadius).card : ENNReal)
  change (imageSelected.card : ENNReal) ≤ (sourceSelected.card : ENNReal)
  calc
    (imageSelected.card : ENNReal) ≤
        ((sourceSelected.image
          (wz1PositiveSimilarity center scale)).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = (sourceSelected.card : ENNReal) := by
      rw [Finset.card_image_of_injective _
        (wz1PositiveSimilarity_injective hscale)]

/-- The half-loss theorem at scale `delta/2` gives the requested source
line-count threshold. -/
lemma common_endpoint_line_threshold
    {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1) :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      Kakeya.realRpowENN (delta / 2) (epsilon / 2 - 1) := by
  apply ENNReal.ofReal_mono
  have hdeltaOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hexponent : epsilon / 2 - 1 ≤ epsilon - 1 := by linarith
  have hfirst :
      Real.rpow delta (epsilon - 1) ≤
        Real.rpow delta (epsilon / 2 - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hexponent
  have hbase : delta / 2 ≤ delta := by linarith
  have hsecond :
      Real.rpow delta (epsilon / 2 - 1) ≤
        Real.rpow (delta / 2) (epsilon / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  exact hfirst.trans hsecond

/-- Pull the union-valued Proposition-45 line alternative back to the
original common ambient graph. -/
theorem WZ1CommonEndpointAffineNormalization.pullbackAlternativeA
    {rho eta epsilon : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall}
    {raw : WZ1CommonEndpointRawLocalization ready}
    (affine : WZ1CommonEndpointAffineNormalization raw)
    (budget : WZ1CommonEndpointParameterBudget eta ready.deltaGraph)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hA : WZ1Proposition8_9AlternativeAUnion
      (ready.deltaGraph / 2) (epsilon / 2)
      affine.F affine.G₁ affine.G₂) :
    WZ1Proposition8_9AlternativeAUnion
      ready.deltaGraph epsilon unitBall.F unitBall.G₁ unitBall.G₁ := by
  rcases hA with ⟨base, direction, hdirection, hF, hEndpoint⟩
  let sourceBase :=
    wz1PositiveSimilarityInv affine.midpointG affine.scaleG base
  have hthreshold := common_endpoint_line_threshold
    ready.deltaGraph_pos budget.delta_half
    hepsilon hepsilonOne
  have hFpull :
      wz1DiscreteLineCount affine.F 0 (wz1Perp2 direction)
          (ready.deltaGraph / 2) ≤
        wz1DiscreteLineCount raw.localized.selectedF 0
          (wz1Perp2 direction) ready.deltaGraph := by
    rw [affine.F_eq, affine.mapF_eq]
    have hinvZero :
        wz1PositiveSimilarityInv 0 affine.scaleF 0 = (0 : Point2) := by
      simp [wz1PositiveSimilarityInv]
    simpa [hinvZero] using
      wz1DiscreteLineCount_image_similarity_le
        (A := raw.localized.selectedF)
        (center := (0 : Point2)) (base := (0 : Point2))
        (direction := wz1Perp2 direction)
        affine.scaleF_pos
        (by
          have hhalf : 1 / 2 ≤ affine.scaleF := affine.scaleF_half
          have hpos := ready.deltaGraph_pos
          exact (div_le_iff₀ affine.scaleF_pos).2 (by nlinarith))
  have hFambient :
      wz1DiscreteLineCount raw.localized.selectedF 0
          (wz1Perp2 direction) ready.deltaGraph ≤
        wz1DiscreteLineCount unitBall.F 0
          (wz1Perp2 direction) ready.deltaGraph := by
    simp [wz1DiscreteLineCount]
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter
        (fun point => point ∈ wz1LineNeighborhood 0
          (wz1Perp2 direction) ready.deltaGraph)
        raw.localized.selectedF_subset)
  have hFfinal :
      Kakeya.realRpowENN ready.deltaGraph (epsilon - 1) ≤
        wz1DiscreteLineCount unitBall.F 0
          (wz1Perp2 direction) ready.deltaGraph :=
    hthreshold.trans (hF.trans (hFpull.trans hFambient))
  have pullG₁ :
      wz1DiscreteLineCount affine.G₁ base direction
          (ready.deltaGraph / 2) ≤
        wz1DiscreteLineCount unitBall.G₁ sourceBase direction
          ready.deltaGraph := by
    rw [affine.G₁_eq, affine.mapG_eq]
    calc
      wz1DiscreteLineCount
          (raw.localized.selectedG₁.image
            (wz1PositiveSimilarity affine.midpointG affine.scaleG))
          base direction (ready.deltaGraph / 2)
          ≤ wz1DiscreteLineCount raw.localized.selectedG₁ sourceBase
              direction ready.deltaGraph := by
            apply wz1DiscreteLineCount_image_similarity_le affine.scaleG_pos
            exact (div_le_iff₀ affine.scaleG_pos).2
              (by nlinarith [affine.scaleG_half, ready.deltaGraph_pos])
      _ ≤ wz1DiscreteLineCount unitBall.G₁ sourceBase direction
            ready.deltaGraph := by
          simp only [wz1DiscreteLineCount]
          exact_mod_cast Finset.card_le_card
            (Finset.filter_subset_filter
              (fun point => point ∈ wz1LineNeighborhood
                sourceBase direction ready.deltaGraph)
              raw.localized.selectedG₁_subset)
  have pullG₂ :
      wz1DiscreteLineCount affine.G₂ base direction
          (ready.deltaGraph / 2) ≤
        wz1DiscreteLineCount unitBall.G₁ sourceBase direction
          ready.deltaGraph := by
    rw [affine.G₂_eq, affine.mapG_eq]
    calc
      wz1DiscreteLineCount
          (raw.localized.selectedG₂.image
            (wz1PositiveSimilarity affine.midpointG affine.scaleG))
          base direction (ready.deltaGraph / 2)
          ≤ wz1DiscreteLineCount raw.localized.selectedG₂ sourceBase
              direction ready.deltaGraph := by
            apply wz1DiscreteLineCount_image_similarity_le affine.scaleG_pos
            exact (div_le_iff₀ affine.scaleG_pos).2
              (by nlinarith [affine.scaleG_half, ready.deltaGraph_pos])
      _ ≤ wz1DiscreteLineCount unitBall.G₁ sourceBase direction
            ready.deltaGraph := by
          simp only [wz1DiscreteLineCount]
          exact_mod_cast Finset.card_le_card
            (Finset.filter_subset_filter
              (fun point => point ∈ wz1LineNeighborhood
                sourceBase direction ready.deltaGraph)
              raw.localized.selectedG₂_subset)
  refine ⟨sourceBase, direction, hdirection, hFfinal, ?_⟩
  rcases hEndpoint with hG₁ | hG₂
  · exact Or.inl (hthreshold.trans (hG₁.trans pullG₁))
  · exact Or.inr (hthreshold.trans (hG₂.trans pullG₂))

end

end Kakeya.Assouad
