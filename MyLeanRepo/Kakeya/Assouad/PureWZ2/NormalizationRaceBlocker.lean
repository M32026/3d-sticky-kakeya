import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky

/-!
# Normalization race: exact top-level blockers

The frozen critical package supplies arbitrarily small pure extremizers, but
does not localize their shaded union in a fixed spatial window.  This module
separates the quantifier-correct ways to finish the normalization leaf:

* prove a source-uniform normalization theorem; or
* prove a normalization theorem for localized sources together with a
  locality-preserving strengthening of the critical extremal sequence; or
* start from a stronger-loss extremizer and construct a new localized
  extremizer at the output loss before applying normalization.

Both reductions keep the normalization exponent fixed before the critical
package and preserve the exact frozen output.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
A source-uniform normalization leaf.

The small-scale threshold is selected before the source extremizer.  This is
the interface needed to apply the frozen `extremal_sequence` directly.
-/
def PureWZ2CroppedCriticalNormalizationRaceUniformLeafAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ inputLoss delta₁ : ℝ,
        0 < inputLoss ∧
        inputLoss ≤ outputLoss ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma inputLoss delta,
            Nonempty
              (PureWZ2CroppedCriticalNormalizationData
                (outputLoss := outputLoss)
                source normalizationExponent)

/--
The frozen normalization target follows from a source-uniform normalization
leaf.  This theorem discharges all top-level quantifier wiring.
-/
theorem pureWZ2_cropped_critical_normalization_race_of_uniform_leaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationRaceUniformLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent := by
  intro sigma critical outputLoss delta₀ outputLossPos delta₀Pos
  rcases leaf sigma outputLoss outputLossPos with
    ⟨inputLoss, delta₁, inputLossPos, inputLossLe,
      delta₁Pos, normalize⟩
  let threshold := min delta₀ delta₁
  have thresholdPos : 0 < threshold := by
    exact lt_min delta₀Pos delta₁Pos
  rcases
      critical.extremal_sequence
        inputLoss threshold inputLossPos thresholdPos
    with
    ⟨delta, deltaPos, deltaLe, ⟨source⟩⟩
  have deltaLeInput : delta ≤ delta₁ :=
    deltaLe.trans (min_le_right delta₀ delta₁)
  have deltaLeOutput : delta ≤ delta₀ :=
    deltaLe.trans (min_le_left delta₀ delta₁)
  exact
    ⟨inputLoss, delta, inputLossPos, inputLossLe,
      deltaPos, deltaLeOutput, source,
      normalize delta deltaPos deltaLeInput source⟩

/--
The exact locality strengthening absent from
`PureWZ2CriticalPackage.extremal_sequence`.

The loss is fixed before the scale threshold, and the returned source is an
actual extremal configuration at that same loss and scale.
-/
def PureWZ2CriticalAxisBoxExtremalSequence : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ loss delta₀ : ℝ,
        0 < loss →
        0 < delta₀ →
          ∃ delta : ℝ,
            0 < delta ∧
            delta ≤ delta₀ ∧
            ∃ source :
                PureWZ2ExtremalConfiguration sigma loss delta,
              source.shading.union ⊆
                Kakeya.Streamlined.axisBox 2 2 2

/--
A normalization leaf whose geometry is valid only for sources already
localized in the fixed box used by the Section 6 direction-position
pigeonhole.
-/
def PureWZ2CroppedCriticalNormalizationRaceLocalLeafAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ inputLoss delta₁ : ℝ,
        0 < inputLoss ∧
        inputLoss ≤ outputLoss ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma inputLoss delta,
            source.shading.union ⊆
                Kakeya.Streamlined.axisBox 2 2 2 →
              Nonempty
                (PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := outputLoss)
                  source normalizationExponent)

/--
A localized normalization leaf closes the frozen target exactly when paired
with the missing locality-preserving critical-sequence interface.
-/
theorem pureWZ2_cropped_critical_normalization_race_of_local_leaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationRaceLocalLeafAt
        normalizationExponent)
    (localizedSequence : PureWZ2CriticalAxisBoxExtremalSequence) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent := by
  intro sigma critical outputLoss delta₀ outputLossPos delta₀Pos
  rcases leaf sigma outputLoss outputLossPos with
    ⟨inputLoss, delta₁, inputLossPos, inputLossLe,
      delta₁Pos, normalize⟩
  let threshold := min delta₀ delta₁
  have thresholdPos : 0 < threshold := by
    exact lt_min delta₀Pos delta₁Pos
  rcases
      localizedSequence sigma critical
        inputLoss threshold inputLossPos thresholdPos
    with
    ⟨delta, deltaPos, deltaLe, source, sourceLocal⟩
  have deltaLeInput : delta ≤ delta₁ :=
    deltaLe.trans (min_le_right delta₀ delta₁)
  have deltaLeOutput : delta ≤ delta₀ :=
    deltaLe.trans (min_le_left delta₀ delta₁)
  exact
    ⟨inputLoss, delta, inputLossPos, inputLossLe,
      deltaPos, deltaLeOutput, source,
      normalize delta deltaPos deltaLeInput source sourceLocal⟩

/--
The paper-faithful derived-localization route.

The critical package is queried at `sourceLoss`.  The leaf may then perform
spatial localization, reanchoring, subfamily selection, and pure-CWA
restoration to construct a new extremal configuration at `inputLoss`.
Normalization retention is measured relative to that new configuration, not
relative to the stronger source extremizer.
-/
def PureWZ2CroppedCriticalNormalizationRaceDerivedLeafAt
    (normalizationExponent : ℕ) : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
      ∃ sourceLoss inputLoss delta₁ : ℝ,
        0 < sourceLoss ∧
        0 < inputLoss ∧
        inputLoss ≤ outputLoss ∧
        0 < delta₁ ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₁ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∃ localized :
                PureWZ2ExtremalConfiguration
                  sigma inputLoss delta,
              Nonempty
                (PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := outputLoss)
                  localized normalizationExponent)

/--
A stronger-source derived-localization leaf closes the frozen normalization
target without strengthening `PureWZ2CriticalPackage.extremal_sequence`.
-/
theorem pureWZ2_cropped_critical_normalization_race_of_derived_leaf
    (normalizationExponent : ℕ)
    (leaf :
      PureWZ2CroppedCriticalNormalizationRaceDerivedLeafAt
        normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent := by
  intro sigma critical outputLoss delta₀ outputLossPos delta₀Pos
  rcases leaf sigma outputLoss outputLossPos with
    ⟨sourceLoss, inputLoss, delta₁,
      sourceLossPos, inputLossPos, inputLossLe,
      delta₁Pos, normalize⟩
  let threshold := min delta₀ delta₁
  have thresholdPos : 0 < threshold := by
    exact lt_min delta₀Pos delta₁Pos
  rcases
      critical.extremal_sequence
        sourceLoss threshold sourceLossPos thresholdPos
    with
    ⟨delta, deltaPos, deltaLe, ⟨source⟩⟩
  have deltaLeInput : delta ≤ delta₁ :=
    deltaLe.trans (min_le_right delta₀ delta₁)
  have deltaLeOutput : delta ≤ delta₀ :=
    deltaLe.trans (min_le_left delta₀ delta₁)
  rcases
      normalize delta deltaPos deltaLeInput source
    with
    ⟨localized, normalized⟩
  exact
    ⟨inputLoss, delta, inputLossPos, inputLossLe,
      deltaPos, deltaLeOutput, localized, normalized⟩

end Kakeya.Assouad

end
