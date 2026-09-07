import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallRestriction

/-!
# Fixed ambient geometry after fine-shading transport

The faithful Section 5 normal argument first restricts the dyadic pointwise
data to one ambient ball and only then runs the fine-shading cover.  The cover
may enlarge `C_R`, but it preserves each pointwise fiber.  This statement
packages the two consequences needed by the later normalized count:

* every transported fiber lies in the fixed ambient family `F_B`; and
* `F_B` has diameter at most the coarse second scale `6 * (C_R * tRep)`.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedFSVGeometryStatement : Prop :=
  ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ C_R : ℝ},
    ∀ (data : DyadicFineAssignmentData
        family E K delta diameter epsilon eta tRep DeltaRep C_R₀),
      0 < delta →
      ∀ (center : C2Function) (hE : MeasurableSet E),
        ∀ pointData : FineRectangleAssignmentData
            family (ambientRestrictedSet data center)
              K delta tRep DeltaRep C_R,
          (∀ p,
            pointData.fiber p =
              (ambientRestrictedData data center hE).assignment.fiber p) →
          1 ≤ C_R →
          (∀ p,
            (pointData.fiber p).carrier ⊆
              (data.ambientSource.cluster center (3 * tRep)).carrier) ∧
          ∀ f ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
            ∀ g ∈ (data.ambientSource.cluster center (3 * tRep)).carrier,
              dist f g ≤ 6 * (C_R * tRep)

end Kakeya.Cinematic
