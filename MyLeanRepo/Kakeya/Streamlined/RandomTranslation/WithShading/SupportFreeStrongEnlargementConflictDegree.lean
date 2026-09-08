import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.StrongEDConflictDegree

/-!
# Support-free K-strong conflict degree after coaxial enlargement

The finite-grid Frostman construction needs to enlarge one selected
essentially-distinct lower-scale family to the next upper bracket.  The
selected family is supported in a fixed ball, but that support radius should
not enter the packing constant.

A K-strong overlap can be normalized by translating both tubes by the
negative midpoint of the reference tube.  The overlap is nonempty, so both
normalized midpoints satisfy the local bound used by the existing strong
dilated-containment theorem.  The conflicting lower-scale tubes then lie in
one common dilated plank and are counted by phase-space packing.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/--
An arbitrary essentially-distinct radius-`sigma` family has uniformly bounded
K-strong conflict degree after coaxial enlargement to radius `rho`.

The constant depends only on `K`, not on an ambient support ball, the two
scales, or the family.  This is the support-free form needed after the
same-witness selected-cover restriction.
-/
def SupportFreeStrongEnlargementConflictDegreeStatement : Prop :=
  ∀ K : ℝ, 2 ≤ K →
    ∃ C_K : ℝ, 0 < C_K ∧
      ∀ {sigma rho : ℝ},
        0 < sigma →
        sigma ≤ rho →
        rho ≤ 1 →
        ∀ G : TubeFamily sigma,
          G.IsEssentiallyDistinct →
          ∀ j : Fin G.card,
            tubeConflictDegreeStrong
                (sameAxisEnlargedFamily
                  (rho := rho) G)
                (Kakeya.deltaTubeVolume rho)
                (ENNReal.ofReal K) j ≤
              Nat.ceil
                (C_K * (rho / sigma) ^ 4)

end Kakeya.Streamlined.RandomTranslation.WithShading
