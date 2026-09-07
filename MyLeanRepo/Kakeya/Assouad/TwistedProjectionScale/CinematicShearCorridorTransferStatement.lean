import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockTranslation
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridCinematicCorridorCountStatement

/-!
# Transfer a cinematic corridor through the Section 7 shear

The shear `(u,z) ↦ (z,u-c₀z)` is volume preserving but is not an isometry.
The preimage of a standard cinematic graph corridor is nevertheless contained
in a controlled corridor around the graph obtained by adding the linear drift
`c₀z`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The identity slope function used to package the linear cinematic drift. -/
def identitySlopeFunction : SlopeFunction where
  toFun := id
  contDiff := contDiff_id

/-- The cinematic function `t ↦ c * t`. -/
def cinematicLinearDrift
    (c : ℝ) : Kakeya.Cinematic.C2Function :=
  slopeCurve identitySlopeFunction 0 c 0

/-- Undo the common `c₀z` shear on one cinematic curve. -/
def unshearedCinematicCurve
    (g : Kakeya.Cinematic.C2Function)
    (c₀ : ℝ) : Kakeya.Cinematic.C2Function :=
  g.add (cinematicLinearDrift c₀)

/--
Transfer graph containment and the first-derivative bound from sheared to
original projection coordinates.

If `|c₀| ≤ B`, then the inverse shear costs at most the factor `2+B` in the
Euclidean corridor radius, and adds at most `B` to the Lipschitz constant on
the unit interval.
-/
def CinematicShearCorridorTransferStatement : Prop :=
  ∀ g : Kakeya.Cinematic.C2Function,
    ∀ c₀ : ℝ,
      ∀ B L : NNReal,
        |c₀| ≤ (B : ℝ) →
        LipschitzOnWith L g.extension (Set.Icc (0 : ℝ) 1) →
        ∀ r : ℝ, 0 ≤ r →
          {q : Point2 |
              cinematicShear c₀ q ∈
                Kakeya.Cinematic.graphNeighborhood g r} ⊆
            Metric.cthickening
              ((2 + (B : ℝ)) * r)
              (cinematicExtensionGraph
                (unshearedCinematicCurve g c₀)) ∧
          LipschitzOnWith (L + B)
            (unshearedCinematicCurve g c₀).extension
            (Set.Icc (0 : ℝ) 1)

end Kakeya.Assouad
