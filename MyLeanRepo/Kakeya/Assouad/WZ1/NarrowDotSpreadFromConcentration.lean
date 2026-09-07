import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadConcentrationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadCountingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadSpreadBranch

/-!
# Assemble the narrow dot-spread theorem from the concentration leaf

All finite counting, longitudinal pigeonholing, exponent absorption, and the
spread branch are closed.  This module selects the small parameter window,
applies the recovered spread-or-concentration provider to one actual graph
edge, and delegates only the concentration synchronization case.
-/

namespace Kakeya.Assouad

open scoped ENNReal

theorem wz1_proposition8_9_narrow_from_concentration :
    WZ1Proposition8_9NarrowFromConcentrationStatement := by
  intro hSynchronization
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
  have hencoded : encoded ∈ wz1EncodeTriples data.refinedH :=
    Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  have hfirst : edge.1 ∈ data.selectedF := by
    exact data.uniform.2.1 encoded hencoded 0
  have hsecond : edge.2.1 ∈ data.selectedG₁ := by
    exact data.uniform.2.1 encoded hencoded 1
  have hthird : edge.2.2 ∈ data.selectedG₂ := by
    exact data.uniform.2.1 encoded hencoded 2
  have hstandardF :
      ∀ point ∈ data.selectedF, 1 / 2 ≤ dist point 0 :=
    data.standardSeparation.2.2.2.2
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
        hstandardF data.orthogonal_strip
        data.first_strip data.second_strip
        (c := (1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta)
        rfl data.uniform
        edge.1 hfirst edge.2.1 hsecond
        edge.2.2 hthird hedge hsmall with
    hSpread | hConcentrated
  · rcases hSpread with ⟨spread⟩
    exact Or.inr
      ⟨dot_spread_data_mono
        data.refinedH_subset spread⟩
  · rcases hConcentrated with ⟨concentration, _⟩
    rcases
        hSynchronization parameters
          hdelta hdeltaOne hepsilon hepsilonOne
          heta (by simpa [etaCap] using hetaBound)
          data hwidthQuarter hnarrow hsmall concentration with
      hAlternative | hSpread
    · exact Or.inl
        (alternative_a_mono hAlternative
          data.selectedF_subset
          data.selectedG₁_subset
          data.selectedG₂_subset)
    · rcases hSpread with ⟨spread⟩
      exact Or.inr
        ⟨dot_spread_data_mono
          (data.refinedH_subset) spread⟩

end Kakeya.Assouad
