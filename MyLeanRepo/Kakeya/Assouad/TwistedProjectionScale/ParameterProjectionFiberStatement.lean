import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Three-parameter projection fiber bound

The positive-window cinematic reduction forgets the fourth line parameter
`c`.  This statement records the exact multiplicity loss of that projection.
Inside one common `c`-window, each `(a,b,d)` fiber lies in one four-parameter
box, so indexed parameter Frostman control bounds every fiber and hence the
total active cardinality by fiber cap times image cardinality.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The normalized three-parameter point used by the cinematic reduction.

The factors agree with the half-ball cinematic bridge: the raw parameters are
recovered as `(24 * p₀, 24 * p₁, 4 * p₂)`.
-/
def tubeParameterPoint3
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (i : Fin F.card) : Point 3 :=
  point3
    ((tubeParams i).a / 24)
    ((tubeParams i).b / 24)
    ((tubeParams i).d / 4)

/--
Indexed fiber control for the projection `(a,b,c,d) ↦ (a,b,d)`.

No injectivity or essential-distinctness premise is used.  The first
conclusion bounds each actual image fiber.  The second is the finite
fiber-sum inequality needed to lower-bound the number of distinct cinematic
parameter points.
-/
def TubeParameterProjectionFiberBoundStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ C : ENNReal,
        TubeParameterFrostmanBound F C →
          ∀ w : ℝ, delta ≤ w → w ≤ 1 →
            ∀ active : Finset (Fin F.card),
              ∀ c0 : ℝ,
                (∀ i ∈ active,
                  |(tubeParams i).c - c0| ≤ w / 2) →
                  (∀ p ∈ active.image tubeParameterPoint3,
                    ((active.filter fun i =>
                      tubeParameterPoint3 i = p).card : ENNReal) ≤
                        C * Kakeya.realRpowENN w 2 * F.enncard) ∧
                  (active.card : ENNReal) ≤
                    (C * Kakeya.realRpowENN w 2 * F.enncard) *
                      ((active.image tubeParameterPoint3).card : ENNReal)

end Kakeya.Assouad
