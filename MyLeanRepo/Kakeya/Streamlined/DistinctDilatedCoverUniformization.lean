import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization.Proof

/-!
# Distinct assigned-cell uniformization of a dilated tube cover

This internal theorem adds coarse essential distinctness while balancing the
auxiliary assigned parent fibers.  It does not assert full-containment
branching uniformity.
-/

noncomputable section

namespace Kakeya.Streamlined

def AssignedDistinctDilatedCoverUniformizationStatement : Prop :=
  ∀ {δ ρ A : ℝ},
    ∀ {fine : TubeFamily δ} {coarse : TubeFamily ρ},
      coarse.IsEssentiallyDistinct →
      ∀ P : DilatedTubeCover A fine coarse,
      ∀ Y : TubeShading fine,
        0 < Y.mass →
        ∃ S : TubeSubfamily fine,
          S.Nonempty ∧
          Y.mass ≤
            (Nat.log 2 fine.card + 1 : ENNReal) *
              (S.restrictShading Y).mass ∧
          ∃ C : TubeSubfamily coarse,
            C.family.IsEssentiallyDistinct ∧
            ∃ Q : DilatedTubeCover A S.family C.family,
              Q.toFactoring.FibersAreCUniform 2

/-- Legacy compatibility name for the explicitly assigned statement. -/
abbrev LegacyDistinctDilatedCoverUniformizationStatement : Prop :=
  AssignedDistinctDilatedCoverUniformizationStatement

end Kakeya.Streamlined
