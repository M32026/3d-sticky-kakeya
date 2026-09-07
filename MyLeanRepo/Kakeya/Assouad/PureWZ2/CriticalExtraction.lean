import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Core

/-!
# Helper lemmas for pure WZ2 critical extraction

Admissibility monotonicity, failure-to-admissible, non-admissibility spec,
and density weakening for the pure Definition 2.12 model.
These mirror the sticky-model helpers in `ExtremalHelpers.lean`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Downward closure of pure WZ2 admissibility. -/
lemma PureWZ2Admissible.mono {s t : ℝ}
    (h : PureWZ2Admissible s) (hst : t ≤ s) :
    PureWZ2Admissible t := by
  intro eta heta delta₀ hdelta₀
  rcases h eta heta delta₀ hdelta₀ with
    ⟨delta, hdelta_pos, hdelta_le, hdelta_one, family, shading,
      hF_nonempty, hCWA, hDense, hVolume⟩
  refine ⟨delta, hdelta_pos, hdelta_le, hdelta_one, family, shading,
    hF_nonempty, hCWA, hDense, ?_⟩
  have h_power :
      Kakeya.realRpowENN delta s ≤
        Kakeya.realRpowENN delta t :=
    realRpowENN_antitone hdelta_pos hdelta_one hst
  exact hVolume.trans h_power

/-- Failure of pure WZ2 Theorem 5.2 gives a positive admissible exponent. -/
lemma pure_wz2_failure_admissible
    (h : ¬ PureWZ2Theorem5_2Statement) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ PureWZ2Admissible ε₀ := by
  have h1 := h
  simp only [PureWZ2Theorem5_2Statement] at h1
  push Not at h1
  rcases h1 with ⟨ε₀, hε₀_pos, h_failure⟩
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro eta heta delta₀ hdelta₀
  let delta₀' := min delta₀ 1
  have hdelta₀'_pos : 0 < delta₀' := by positivity
  have hdelta₀'_one : delta₀' ≤ 1 := min_le_right _ _
  have hdelta₀'_le : delta₀' ≤ delta₀ := min_le_left _ _
  rcases h_failure eta delta₀' heta hdelta₀'_pos hdelta₀'_one with
    ⟨delta, hdelta_pos, hdelta_le, family, hF_nonempty, hCWA,
      shading, hDense, hVolume_lt⟩
  refine ⟨delta, hdelta_pos, hdelta_le.trans hdelta₀'_le,
    hdelta_le.trans hdelta₀'_one, family, shading,
    hF_nonempty, hCWA, hDense, le_of_lt hVolume_lt⟩

/-- Non-admissibility gives a uniform strict lower-volume bound. -/
lemma pure_wz2_non_admissible_spec {s : ℝ}
    (h : ¬ PureWZ2Admissible s) :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ family : Kakeya.Streamlined.TubeFamily delta,
            family.Nonempty →
            WZ2PaperPureCWAAtNearbyScales family
              (Kakeya.realRpowENN delta (-eta₀)) →
            ∀ shading : Kakeya.Streamlined.TubeShading family,
              shading.IsLambdaDense
                (Kakeya.realRpowENN delta eta₀) →
              Kakeya.realRpowENN delta s <
                MeasureTheory.volume shading.union := by
  by_contra h_main
  push Not at h_main
  have h_adm : PureWZ2Admissible s := by
    intro eta heta delta₀ hdelta₀
    let delta₀' := min delta₀ 1
    have hdelta₀'_pos : 0 < delta₀' := by positivity
    have hdelta₀'_one : delta₀' ≤ 1 := min_le_right _ _
    have hdelta₀'_le : delta₀' ≤ delta₀ := min_le_left _ _
    rcases h_main eta heta delta₀' hdelta₀'_pos hdelta₀'_one with
      ⟨delta, hdelta_pos, hdelta_le, family, hF_nonempty, hCWA,
        shading, hDense, hVolume_le⟩
    refine ⟨delta, hdelta_pos, hdelta_le.trans hdelta₀'_le,
      hdelta_le.trans hdelta₀'_one, family, shading,
      hF_nonempty, hCWA, hDense, hVolume_le⟩
  exact h h_adm

/-- Density at a stronger loss implies density at a weaker threshold. -/
lemma pure_wz2_dense_weaken {δ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily δ}
    {shading : Kakeya.Streamlined.TubeShading family}
    {η₁ η₂ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : η₁ ≤ η₂)
    (hDense : shading.IsLambdaDense
      (Kakeya.realRpowENN δ η₁)) :
    shading.IsLambdaDense
      (Kakeya.realRpowENN δ η₂) := by
  have h1 :
      Kakeya.realRpowENN δ η₂ ≤
        Kakeya.realRpowENN δ η₁ :=
    realRpowENN_antitone hδ hδ1 h
  have h2 :
      Kakeya.realRpowENN δ η₂ * family.toBodyFamily.mass ≤
        Kakeya.realRpowENN δ η₁ * family.toBodyFamily.mass := by
    gcongr
  exact h2.trans hDense

end Kakeya.Assouad

end
