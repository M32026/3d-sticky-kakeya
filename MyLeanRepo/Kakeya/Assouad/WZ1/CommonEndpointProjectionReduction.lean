import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointAlternativeATransport
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9UnionSplitAssembly

/-!
# Final common-endpoint reduction to Proposition 45

The long-projection branch remains in its normalized coordinates.  The
one-scale Lemma-23 caller excludes it there using the normalized
dot-difference AD estimate; it is not silently identified with a source
graph conclusion.
-/

namespace Kakeya.Assouad

noncomputable section

/-- All provenance retained when Proposition 45 returns its long branch. -/
structure WZ1CommonEndpointProjectionLongData
    {rho sourceEta epsilon : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    (ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall) where
  projectionEta : ℝ
  projectionEta_pos : 0 < projectionEta
  sourceEta_budget : 100 * sourceEta ≤ projectionEta
  raw : WZ1CommonEndpointRawLocalization ready
  affine : WZ1CommonEndpointAffineNormalization raw
  wellSeparated : WZ1CommonEndpointWellSeparatedInput affine
  long :
    WZ1StripLocalizationLongProjection
      (ready.deltaGraph / 2) (epsilon / 2) projectionEta
      wellSeparated.refinedH

/-- Apply the union-valued well-separated theorem to a ready common graph. -/
theorem wz1_common_endpoint_projection_reduction
    (hWell : WZ1WellSeparatedProjectionUnionConclusion) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ sourceEta delta₀ : ℝ,
        0 < sourceEta ∧ sourceEta ≤ 1 / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
        ∀ {rho : ℝ}
          {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
          {sourceH : Finset (Point2 × Point2 × Point2)}
          {unitBall :
            WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
          (ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall),
          ready.deltaGraph ≤ delta₀ →
          unitBall.G₂ = unitBall.G₁ →
            WZ1Proposition8_9AlternativeAUnion
                ready.deltaGraph epsilon
                unitBall.F unitBall.G₁ unitBall.G₁ ∨
              Nonempty
                (WZ1CommonEndpointProjectionLongData
                  (epsilon := epsilon) ready) := by
  intro epsilon hepsilon hepsilonOne
  have hhalfEpsilon : 0 < epsilon / 2 := by linarith
  rcases hWell (epsilon / 2) hhalfEpsilon with
    ⟨projectionEta, projectionDelta₀, hprojectionEta,
      hprojectionDelta₀, hprojectionDelta₀One, hprojection⟩
  let sourceEta := min (projectionEta / 100) (1 / 100 : ℝ)
  have hsourceEta : 0 < sourceEta := by
    dsimp only [sourceEta]
    positivity
  have hsourceEtaSmall : sourceEta ≤ 1 / 100 := min_le_right _ _
  have hsourceBudget : 100 * sourceEta ≤ projectionEta := by
    have h := min_le_left (projectionEta / 100) (1 / 100 : ℝ)
    dsimp only [sourceEta]
    linarith
  rcases exists_common_endpoint_parameter_budget sourceEta hsourceEta with
    ⟨budgetDelta₀, hbudgetDelta₀, hbudgetDelta₀Half, hbudget⟩
  let delta₀ := min budgetDelta₀ projectionDelta₀
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀Half : delta₀ ≤ 1 / 2 :=
    (min_le_left _ _).trans hbudgetDelta₀Half
  refine ⟨sourceEta, delta₀, hsourceEta, hsourceEtaSmall,
    hdelta₀, hdelta₀Half, ?_⟩
  intro rho sourceF sourceG₁ sourceG₂ sourceH unitBall ready
    hdeltaSmall hcommon
  have hdeltaBudget : ready.deltaGraph ≤ budgetDelta₀ :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaProjection : ready.deltaGraph / 2 ≤ projectionDelta₀ := by
    calc
      ready.deltaGraph / 2 ≤ ready.deltaGraph := by
        linarith [ready.deltaGraph_pos]
      _ ≤ projectionDelta₀ := hdeltaSmall.trans (min_le_right _ _)
  rcases hbudget ready.deltaGraph ready.deltaGraph_pos hdeltaBudget with
    ⟨budget⟩
  have hsourceEtaFive : 5 * sourceEta ≤ 1 := by
    linarith [hsourceEtaSmall]
  rcases ready.toRawLocalization hsourceEta hsourceEtaFive hcommon budget with
    ⟨raw⟩
  rcases raw.toAffineNormalization hsourceEta budget with ⟨affine⟩
  rcases affine.toWellSeparatedInput hsourceEta budget with ⟨well⟩
  have hdelta' : 0 < ready.deltaGraph / 2 :=
    div_pos ready.deltaGraph_pos (by norm_num)
  have hdelta'One : ready.deltaGraph / 2 ≤ 1 := by
    exact (div_le_self ready.deltaGraph_pos.le (by norm_num)).trans
      (budget.delta_half.trans (by norm_num))
  have hconstant :
      Kakeya.realRpowENN (ready.deltaGraph / 2) (-100 * sourceEta) ≤
        Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta' hdelta'One (by linarith [hsourceBudget])
  have hFfrost : affine.F.IsFrostman (ready.deltaGraph / 2) 1
      (Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta)) := by
    rw [← well.delta_eq]
    exact well.F_frostman.mono (by simpa [well.delta_eq] using hconstant)
  have hG₁frost : affine.G₁.IsFrostman (ready.deltaGraph / 2) 1
      (Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta)) := by
    rw [← well.delta_eq]
    exact well.G₁_frostman.mono (by simpa [well.delta_eq] using hconstant)
  have hG₂frost : affine.G₂.IsFrostman (ready.deltaGraph / 2) 1
      (Kakeya.realRpowENN (ready.deltaGraph / 2) (-projectionEta)) := by
    rw [← well.delta_eq]
    exact well.G₂_frostman.mono (by simpa [well.delta_eq] using hconstant)
  have hdensity :
      Kakeya.realRpowENN (ready.deltaGraph / 2) projectionEta ≤
        Kakeya.realRpowENN (ready.deltaGraph / 2) (100 * sourceEta) := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      hdelta' hdelta'One hsourceBudget
  have huniform := well.uniform.mono (by simpa [well.delta_eq] using hdensity)
  rcases hprojection (ready.deltaGraph / 2) hdelta' hdeltaProjection
      affine.F affine.G₁ affine.G₂
      affine.F_nonempty affine.G₁_nonempty affine.G₂_nonempty
      affine.F_unit affine.G₁_unit affine.G₂_unit
      affine.F_separated affine.G₁_separated affine.G₂_separated
      hFfrost hG₁frost hG₂frost affine.standardSeparation
      well.refinedH huniform with hA | hlong
  · exact Or.inl
      (affine.pullbackAlternativeA budget hepsilon hepsilonOne.le hA)
  · exact Or.inr ⟨{
      projectionEta := projectionEta
      projectionEta_pos := hprojectionEta
      sourceEta_budget := hsourceBudget
      raw := raw
      affine := affine
      wellSeparated := well
      long := hlong
    }⟩

end

end Kakeya.Assouad
