import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Scale-changed cubical plane-map boundary

This lightweight module isolates the WZ1 Lemma 12 / Lemma 16 producer from
the CV-dependent planiness statements.
-/

namespace Kakeya.Assouad

/--
Complete WZ1 Lemma 11 output with extremality restored on the selected
weak-plane-map shading.
-/
def WZ1ExtremalWeakPlaneMapConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
        HasExtremalCounterexampleSequence sigma →
        HasCriticalVolumeFloor sigma →
          ∀ outputLoss delta₀ : ℝ,
            0 < outputLoss → 0 < delta₀ →
              ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
                Nonempty
                  (WZ1ExtremalWeakPlaneMapData
                    sigma outputLoss delta)

/--
WZ1 Lemma 12 / Lemma 16 preparation boundary at the new coarse scale.

The output is a genuinely new tube family with its own coherent
`UniformTubeStructure`, extremal shading, and cube-constant plane map.
-/
def WZ1CubicalPlaneMapConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasExtremalCounterexampleSequence sigma →
    HasCriticalVolumeFloor sigma →
      ∀ outputLoss delta₀ : ℝ,
        0 < outputLoss → 0 < delta₀ →
          ∃ delta inputLoss : ℝ,
            0 < delta ∧ delta ≤ delta₀ ∧
            0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
              Nonempty
                (WZ1CubicalPlaneMapData
                  sigma inputLoss delta)

/--
Construct the paper's cube-constant plane map from the weak-plane producer,
the balanced-cover producer, the direct coarse-plane-map conclusion, and the
finest-cell selection that makes constancy valid at the formal metric scale.

The balanced-cover package supplies the coarse coherent uniform structure and
coarse WZ1 extremality; this theorem must not reconstruct them from carrier
containment.
-/
def WZ1CubicalPlaneMapStatement : Prop :=
  WZ1ExtremalWeakPlaneMapConclusion →
    WZ1BalancedCoverStatement →
      WZ1CoarsePlaneMapConclusion →
        WZ1FinestCellPlaneMapStatement →
          WZ1CubicalPlaneMapConclusion

end Kakeya.Assouad
