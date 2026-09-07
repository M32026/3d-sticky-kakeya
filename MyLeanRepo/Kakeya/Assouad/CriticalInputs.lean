import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Critical-volume and WZ1 inputs for WZ2 Theorem 5.2

These proposition-only inputs are kept separate from the cinematic maximal
estimate so WZ1 targets do not load the Section 7 `eLpNorm` dependency chain.
They are ordinary hypotheses, not axioms.
-/

namespace Kakeya.Assouad

/--
An exponent is admissible when counterexamples with union volume at most
`delta ^ sigma` exist for every structural loss and at arbitrarily small
scales.
-/
def Admissible (sigma : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∀ delta₀ : ℝ, 0 < delta₀ →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
        ∃ F : Kakeya.Streamlined.TubeFamily delta,
          ∃ U : Kakeya.Streamlined.UniformTubeStructure F,
            ∃ Y : Kakeya.Streamlined.TubeShading F,
              0 < delta ∧ delta ≤ 1 ∧
              F.Nonempty ∧ F.IsInUnitBall ∧ F.IsEssentiallyDistinct ∧
              U.uniformity ≤ Kakeya.realRpowENN delta (-eta) ∧
              U.IsFrostmanAtEveryScale
                (Kakeya.realRpowENN delta (-eta)) ∧
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) ∧
              MeasureTheory.volume Y.union ≤
                Kakeya.realRpowENN delta sigma

/--
The second ordinary input to WZ2 Theorem 5.2: one exponent strictly below one
is not admissible.  This is exactly the subunit ceiling needed to bound the
critical supremum away from one.
-/
def SubunitAdmissibleCeilingInput : Prop :=
  ∃ a : ℝ, a < 1 ∧ ¬Admissible a

/--
Extremal counterexamples at arbitrarily small scales for one critical
exponent.  WZ1 Propositions 9 and 21 select and rescale from this sequence;
they do not transform every individual extremal configuration at the same
scale.
-/
def HasExtremalCounterexampleSequence (sigma : ℝ) : Prop :=
  ∀ epsilon delta₀ : ℝ, 0 < epsilon → 0 < delta₀ →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
      ∃ F : Kakeya.Streamlined.TubeFamily delta,
        ∃ U : Kakeya.Streamlined.UniformTubeStructure F,
          ∃ Y : Kakeya.Streamlined.TubeShading F,
            IsExtremalPair sigma epsilon F U Y

/--
The global lower-volume consequence of the critical definition of `sigma`.

For every requested loss, non-admissibility above the critical exponent
supplies its own structural parameter and scale threshold.  This is a
statement about all configurations satisfying those structural bounds; it
does not assert that one previously selected near-minimizer has a hereditary
volume floor at every loss.
-/
def HasCriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
            U.uniformity ≤ Kakeya.realRpowENN delta (-eta) →
            U.IsFrostmanAtEveryScale
              (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
                Kakeya.realRpowENN delta (sigma + loss) ≤
                  MeasureTheory.volume Y.union

/--
Combined output of the WZ1 planiness/graininess argument together with its
CV and OSW inputs.  From an arbitrarily small extremal sequence, and after the
target loss and scale threshold are known, it selects a coordinate-normalized
extremal configuration with global and local `C²` grain data.
-/
def C2GrainsInput : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasExtremalCounterexampleSequence sigma →
    HasCriticalVolumeFloor sigma →
      ∀ epsilon delta₀ : ℝ,
        0 < epsilon → 0 < delta₀ →
          ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
            ∃ F : Kakeya.Streamlined.TubeFamily delta,
              ∃ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∃ Y : Kakeya.Streamlined.TubeShading F,
                  ∃ C : ENNReal,
                    IsExtremalPair sigma epsilon F U Y ∧
                      HasExtremalCardinalityUpper F epsilon ∧
                      IsInVerticalChart F ∧
                      1 ≤ C ∧ C ≠ ⊤ ∧
                      C ≤ Kakeya.realRpowENN delta (-epsilon) ∧
                      Nonempty (C2GrainStructure Y sigma C)

end Kakeya.Assouad
