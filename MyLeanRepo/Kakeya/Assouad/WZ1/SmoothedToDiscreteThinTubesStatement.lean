import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic

/-!
# Unsmoothing measure thin tubes at the original discrete scale

The OSW iteration is applied to measures smoothed at radius `delta / 10`,
while Lemma 40 consumes a discrete witness at scale `delta`.  These two
scales must remain distinct in the interface.
-/

namespace Kakeya.Assouad

/--
Recover a scale-`delta` discrete thin-tubes witness from thin tubes for the
measures smoothed at radius `delta / 10`.

The good finite relation consists of center pairs whose product smoothing
cell has at least one-half of its mass in the measure-level good set.  Markov
retains exceptional fraction `2 * c`.  For `r >= delta`, averaging the
measure tube bound over the source smoothing cell enlarges the tube radius by
at most `2 * (delta / 10)`, and the one-half threshold costs another factor
two.  The fixed constant `20` absorbs these losses for `0 <= beta <= 1`.
-/
def WZ1SmoothedToDiscreteThinTubesStatement : Prop :=
  ∀ {delta beta K c : ℝ}
      (G₁ G₂ : DiscreteSet 2)
      (hG₁ : G₁.Nonempty) (hG₂ : G₂.Nonempty),
    ∀ hdelta : 0 < delta,
    beta ≤ 1 →
    0 ≤ c →
    2 * c < 1 →
    HasMeasureThinTubes beta K c
        (smoothMeasure G₁ hG₁ (delta / 10) (by linarith))
        (smoothMeasure G₂ hG₂ (delta / 10) (by linarith)) →
      HasDiscreteThinTubes delta beta (20 * K) (2 * c) G₁ G₂

end Kakeya.Assouad
