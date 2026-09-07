import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowConcentrationReduction
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadSpreadBranch
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowStripCoveringTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleRotatedEndpointLines
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9CommonStripHelpers

/-!
# Paper-facing narrow branch with one significant endpoint class

The prose of Proposition 45 asks for a significant intersection with
`G₁ ∪ G₂`.  Once the triple obstruction supplies an exact origin line, one
of its doubled endpoint fibers is enough: rotate that single literal fiber
to the selected direction and obtain the union alternative.  No
`G₁`/`G₂` affine-level synchronization is required.
-/

namespace Kakeya.Assouad

open scoped ENNReal

private theorem narrow_union_long_projection_of_spread
    {delta epsilon eta : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (spread :
      WZ1Proposition8_9NarrowDotSpreadData
        delta epsilon eta H) :
    WZ1StripLocalizationLongProjection
      delta epsilon eta H :=
  separated_dot_values_interval_to_long_projection
    hdelta hdeltaOne
    spread.separated spread.values_dot
    spread.lower spread.upper
    spread.lower_mem spread.upper_mem
    spread.between spread.cardinality

theorem wz1_proposition8_9_narrow_union :
    WZ1Proposition8_9NarrowStripStatement := by
  intro epsilon parameters hepsilon hepsilonOne
  let etaCap : ℝ := epsilon / 20
  have hetaCap : 0 < etaCap := by
    dsimp only [etaCap]
    positivity
  have hwidthExponent : 0 < 1 - epsilon / 10 := by
    linarith
  have hsmallExponent : 0 < 7 * epsilon / 10 := by
    positivity
  rcases
      exists_delta_rpow_le_single
        (1 - epsilon / 10) (1 / 4)
        hwidthExponent (by norm_num) (by norm_num) with
    ⟨widthScale, hwidthScale, hwidthScaleOne, hwidthSmall⟩
  rcases
      exists_delta_rpow_le_single
        (7 * epsilon / 10) (1 / 1200000)
        hsmallExponent (by norm_num) (by norm_num) with
    ⟨exponentScale, hexponentScale,
      hexponentScaleOne, hexponentSmall⟩
  let delta₀ : ℝ := min widthScale exponentScale
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hwidthScale, hexponentScale]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hwidthScaleOne
  refine
    ⟨etaCap, delta₀, hetaCap, hdelta₀, hdelta₀One, ?_⟩
  intro delta eta F G₁ G₂ H
    hdelta hdeltaThreshold heta hetaBound data hnarrow
  have hdeltaWidth : delta ≤ widthScale :=
    hdeltaThreshold.trans (min_le_left _ _)
  have hdeltaExponent : delta ≤ exponentScale :=
    hdeltaThreshold.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaThreshold.trans hdelta₀One
  have hwidthQuarter : data.width ≤ 1 / 4 :=
    hnarrow.trans
      (hwidthSmall delta hdelta hdeltaWidth)
  have hsmallPower :
      Real.rpow delta (7 * epsilon / 10) ≤
        1 / 1200000 :=
    hexponentSmall delta hdelta hdeltaExponent
  have hsmall :
      (1200000 : ℝ) *
          Real.rpow delta (7 * epsilon / 10) ≤ 1 := by
    nlinarith
  rcases data.uniform.1 with ⟨edge, hedge⟩
  let encoded : Fin 3 → Point2 :=
    wz1TripleCoordinate edge
  have hencoded :
      encoded ∈ wz1EncodeTriples data.refinedH :=
    Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  have hfirst : edge.1 ∈ data.selectedF :=
    data.uniform.2.1 encoded hencoded 0
  have hsecond : edge.2.1 ∈ data.selectedG₁ :=
    data.uniform.2.1 encoded hencoded 1
  have hthird : edge.2.2 ∈ data.selectedG₂ :=
    data.uniform.2.1 encoded hencoded 2
  rcases
      narrow_dot_spread_spread_branch
        data.direction_unit hdelta hdeltaOne
        hepsilon hepsilonOne heta
        parameters.workingLambda_pos
        parameters.workingLambda_le_epsilon
        (by simpa [etaCap] using hetaBound)
        data.width_pos hwidthQuarter data.delta_le_width
        hnarrow
        data.selectedG₁_ball data.selectedG₂_ball
        data.selectedF_ball data.selectedG₁_separated
        data.selectedG₁_frostman
        data.standardSeparation.2.2.2.2
        data.orthogonal_strip data.first_strip data.second_strip
        (c := (1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta)
        rfl data.uniform
        edge.1 hfirst edge.2.1 hsecond
        edge.2.2 hthird hedge hsmall with
    hSpread | hConcentrated
  · rcases hSpread with ⟨spread⟩
    right
    exact
      narrow_union_long_projection_of_spread
        hdelta hdeltaOne
        (dot_spread_data_mono data.refinedH_subset spread)
  · rcases hConcentrated with ⟨concentration, _⟩
    rcases
        wz1_narrow_triple_concentrated_production
          parameters hdelta hdeltaOne hepsilon hepsilonOne
          heta (by simpa [etaCap] using hetaBound)
          data hwidthQuarter hnarrow hsmall
          concentration with
      hSpread | hObstruction
    · rcases hSpread with ⟨spread⟩
      right
      exact
        narrow_union_long_projection_of_spread
          hdelta hdeltaOne
          (dot_spread_data_mono data.refinedH_subset spread)
    · rcases hObstruction with ⟨obstruction⟩
      rcases
          obstruction.origin_direction_pigeonhole
            hdelta hdeltaOne hepsilon hwidthQuarter hnarrow with
        ⟨origin⟩
      rcases origin.rotate_endpoint_fibers hdelta with ⟨lines⟩
      left
      exact
        (show
          WZ1Proposition8_9AlternativeAUnion
            delta epsilon
            data.selectedF data.selectedG₁ data.selectedG₂ from
          ⟨lines.firstBase, origin.direction,
            origin.direction_unit,
            origin.first_line_count,
            Or.inl lines.first_line_count⟩).mono
          data.selectedF_subset
          data.selectedG₁_subset
          data.selectedG₂_subset

/--
Specialize the union-valued narrow theorem to the repeated endpoint set used
by the two-set Theorem 22 application.
-/
theorem wz1_proposition8_9_narrow_same_endpoint :
    WZ1Proposition8_9NarrowSameEndpointStatement := by
  intro epsilon parameters hepsilon hepsilonOne
  rcases
      wz1_proposition8_9_narrow_union
        epsilon parameters hepsilon hepsilonOne with
    ⟨etaCap, delta₀, hetaCap, hdelta₀, hdelta₀One, hNarrow⟩
  refine
    ⟨etaCap, delta₀, hetaCap, hdelta₀, hdelta₀One, ?_⟩
  intro delta eta F G H
    hdelta hdeltaThreshold heta hetaBound data hnarrow
  rcases
      hNarrow hdelta hdeltaThreshold heta hetaBound data hnarrow with
    hAlternative | hProjection
  · exact Or.inl hAlternative.same_endpoint
  · exact Or.inr hProjection

end Kakeya.Assouad
