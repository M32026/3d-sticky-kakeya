import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Projecting a local plane normal onto the xz-plane

Paper Section 6, Step 3 chooses one horizontal-in-the-y-direction slice
`{y = y₀}` and replaces the local plane normal `V = (Vₓ,Vᵧ,V_z)` by
`Ṽ = (Vₓ,0,V_z)`.  On that slice the two scalar projections differ by the
constant `y₀ Vᵧ`, so the one-dimensional AD estimate is unchanged.

This is the faithful replacement for the old Step 4 API, which attached the
full three-dimensional plane-map normal to a prism extended through all
y-coordinates.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Delete the y-coordinate of a vector while retaining its xz-components. -/
def xzProjectedNormal (v : Point3) : Point3 :=
  EuclideanSpace.single (0 : Fin 3) (v 0) +
    EuclideanSpace.single (2 : Fin 3) (v 2)

/-- Normalize the xz-component of a plane normal. -/
def normalizedXZNormal (v : Point3) : Point3 :=
  ‖xzProjectedNormal v‖⁻¹ • xzProjectedNormal v

/--
Exact scalar-projection identity and AD transfer on one fixed y-slice.

The unit-ball and unit-normal hypotheses ensure that the projected-normal
image satisfies the boundedness clause built into `IsADSet1`; the covering
estimate itself is transported by the displayed translation identity.
-/
def LargeSlopeProjectedNormalSliceStatement : Prop :=
  ∀ (E : Set Point3) (v : Point3) (y₀ rho alpha : ℝ) (C : ENNReal),
    ‖v‖ = 1 →
    E ⊆ Kakeya.DeltaTube.unitBall →
    (∀ p ∈ E, p (1 : Fin 3) = y₀) →
      scalarProjection (xzProjectedNormal v) E =
          (fun t : ℝ => t - y₀ * v (1 : Fin 3)) ''
            scalarProjection v E ∧
        (IsADSet1 (scalarProjection v E) rho alpha C →
          IsADSet1
            (scalarProjection (xzProjectedNormal v) E)
            rho alpha C)

end Kakeya.Assouad
