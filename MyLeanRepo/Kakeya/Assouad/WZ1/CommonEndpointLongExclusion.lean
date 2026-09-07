import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointProjectionReduction
import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointDotScale
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.AlternativeBExclusion
import MyLeanRepo.Kakeya.Assouad.WZ1.ArbitraryPositiveAffineAD
import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement

/-!
# Exclude the normalized common-endpoint long branch
-/

namespace Kakeya.Assouad

noncomputable section

open Metric Set

/-- Dot differences are monotone under restriction of the edge set. -/
lemma wz1DotDifferenceSet_mono
    {H₁ H₂ : Finset (Point2 × Point2 × Point2)}
    (hH : H₁ ⊆ H₂) :
    wz1DotDifferenceSet H₁ ⊆ wz1DotDifferenceSet H₂ := by
  intro value hvalue
  change value ∈ H₁.image
    (fun edge => inner ℝ edge.1 (edge.2.1 - edge.2.2)) at hvalue
  change value ∈ H₂.image
    (fun edge => inner ℝ edge.1 (edge.2.1 - edge.2.2))
  rcases Finset.mem_image.mp (Finset.mem_coe.mp hvalue) with
    ⟨edge, hedge, rfl⟩
  exact Finset.mem_image.mpr ⟨edge, hH hedge, rfl⟩

/--
Transport a source common-graph AD bound through localization, the two paper
similarities, and the final hypergraph refinement.  The output constant keeps
the exact similarity/refinement cost visible.
-/
theorem WZ1CommonEndpointProjectionLongData.refined_dot_ad
    {rho sourceEta epsilon sigma deltaAD : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall}
    (data : WZ1CommonEndpointProjectionLongData
      (epsilon := epsilon) ready)
    {C : ENNReal}
    (hsourceAD : IsADSet1 (wz1DotDifferenceSet unitBall.H)
      deltaAD (1 - sigma) C)
    (hscaledOne : data.affine.dotScale * deltaAD ≤ 1)
    (htargetPos : 0 < ready.deltaGraph / 2)
    (htargetOne : ready.deltaGraph / 2 ≤ 1) :
    IsADSet1 (wz1DotDifferenceSet data.wellSeparated.refinedH)
      (ready.deltaGraph / 2) (1 - sigma)
      ((5 * C) *
        ENNReal.ofReal
          (max 1 (10 * (data.affine.dotScale * deltaAD) /
            (ready.deltaGraph / 2)))) := by
  have hblock : data.raw.localized.block ⊆ unitBall.H := by
    intro edge hedge
    rw [data.raw.localized.block_eq, wz1CommonEndpointGridBlock] at hedge
    have hgood : edge ∈ data.raw.localized.good :=
      (Finset.mem_filter.mp hedge).1
    rw [data.raw.localized.good_eq, wz1CommonEndpointGoodEdges] at hgood
    exact (Finset.mem_filter.mp hgood).1
  have hblockAD :
      IsADSet1 (wz1DotDifferenceSet data.raw.localized.block)
        deltaAD (1 - sigma) C :=
    hsourceAD.mono (wz1DotDifferenceSet_mono hblock)
  have himageAD :
      IsADSet1
        (((fun value : ℝ => data.affine.dotScale * value) ''
            wz1DotDifferenceSet data.raw.localized.block) ∩
          Set.Icc (-4 : ℝ) 4)
        (data.affine.dotScale * deltaAD) (1 - sigma) (5 * C) := by
    have h := hblockAD.affine_image_arbitrary_positive (b := 0)
      data.affine.dotScale_pos hblockAD.2.2.2.2.1 hscaledOne
    simpa only [mul_zero, add_zero] using h
  have haffineAD :
      IsADSet1 (wz1DotDifferenceSet data.affine.H)
        (data.affine.dotScale * deltaAD) (1 - sigma) (5 * C) := by
    apply himageAD.mono
    intro value hvalue
    refine ⟨?_, ?_⟩
    · rwa [data.affine.dot_image] at hvalue
    · change value ∈ data.affine.H.image
        (fun edge => inner ℝ edge.1 (edge.2.1 - edge.2.2)) at hvalue
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hvalue) with
        ⟨edge, hedge, rfl⟩
      have hs := data.affine.edge_support edge hedge
      have hfirst := data.affine.F_unit edge.1 hs.1
      have hsecond := data.affine.G₁_unit edge.2.1 hs.2.1
      have hthird := data.affine.G₂_unit edge.2.2 hs.2.2
      rw [dist_zero_right] at hfirst hsecond hthird
      have hdot : |inner ℝ edge.1 (edge.2.1 - edge.2.2)| ≤ 2 := by
        calc
          |inner ℝ edge.1 (edge.2.1 - edge.2.2)|
              ≤ ‖edge.1‖ * ‖edge.2.1 - edge.2.2‖ :=
            abs_real_inner_le_norm _ _
          _ ≤ 1 * (‖edge.2.1‖ + ‖edge.2.2‖) := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ 1 * (1 + 1) := by gcongr
          _ = 2 := by norm_num
      exact ⟨by linarith [abs_le.mp hdot], by linarith [abs_le.mp hdot]⟩
  have hrefinedAD :
      IsADSet1 (wz1DotDifferenceSet data.wellSeparated.refinedH)
        (data.affine.dotScale * deltaAD) (1 - sigma) (5 * C) :=
    haffineAD.mono
      (wz1DotDifferenceSet_mono data.wellSeparated.refinedH_subset)
  by_cases hcoarse : data.affine.dotScale * deltaAD ≤ ready.deltaGraph / 2
  · have h := hrefinedAD.coarsen_scale htargetPos hcoarse htargetOne
    apply h.mono_constant
    have hfactor : (1 : ENNReal) ≤ ENNReal.ofReal
        (max 1 (10 * (data.affine.dotScale * deltaAD) /
          (ready.deltaGraph / 2))) := by
      exact ENNReal.one_le_ofReal.mpr (le_max_left _ _)
    calc
      5 * C = (5 * C) * 1 := by simp
      _ ≤ (5 * C) * ENNReal.ofReal
          (max 1 (10 * (data.affine.dotScale * deltaAD) /
            (ready.deltaGraph / 2))) := by gcongr
  · have htargetFine : ready.deltaGraph / 2 <
        data.affine.dotScale * deltaAD := lt_of_not_ge hcoarse
    have h := hrefinedAD.weaken_scale htargetPos htargetFine.le hscaledOne
    apply h.mono_constant
    have hnonneg : 0 ≤ 10 * (data.affine.dotScale * deltaAD) /
        (ready.deltaGraph / 2) := by
      exact div_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg data.affine.dotScale_pos.le hsourceAD.1.le))
        htargetPos.le
    exact mul_le_mul_left' (ENNReal.ofReal_mono
      (le_max_right 1 (10 * (data.affine.dotScale * deltaAD) /
        (ready.deltaGraph / 2)))) (5 * C)

/-- Apply the abstract AD contradiction to the normalized long branch. -/
theorem WZ1CommonEndpointProjectionLongData.false_of_dot_ad
    {rho sourceEta epsilon sigma deltaAD : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall : WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho sourceEta unitBall}
    (data : WZ1CommonEndpointProjectionLongData
      (epsilon := epsilon) ready)
    {C : ENNReal}
    (hsourceAD : IsADSet1 (wz1DotDifferenceSet unitBall.H)
      deltaAD (1 - sigma) C)
    (hCtop : C ≠ ⊤)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon / 2) (hepsilonSigma : epsilon / 2 < sigma)
    (hscaledOne : data.affine.dotScale * deltaAD ≤ 1)
    (htargetPos : 0 < ready.deltaGraph / 2)
    (htargetOne : ready.deltaGraph / 2 ≤ 1)
    (htargetStrict : ready.deltaGraph / 2 < 1)
    (hconstant :
      ((5 * C) * ENNReal.ofReal
            (max 1 (10 * (data.affine.dotScale * deltaAD) /
              (ready.deltaGraph / 2)))) * 100 *
          Kakeya.realRpowENN (ready.deltaGraph / 2)
            (data.projectionEta * (sigma - epsilon / 2)) < 1) :
    False := by
  have hAD := data.refined_dot_ad hsourceAD hscaledOne
    htargetPos htargetOne
  rcases data.long with
    ⟨rhoB, center, radius, hrhoLower, hrhoUpper, hradius, hlength, hcover⟩
  exact alternative_b_exclusion htargetPos htargetStrict hsigma hsigmaOne
    hepsilon hepsilonSigma data.projectionEta_pos
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hCtop)
      ENNReal.ofReal_ne_top)
    hAD rhoB center radius hrhoLower hrhoUpper
    hradius hlength hcover hconstant

end

end Kakeya.Assouad
