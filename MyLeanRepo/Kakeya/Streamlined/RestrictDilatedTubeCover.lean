import MyLeanRepo.Kakeya.Streamlined.DistinctDilatedCoverUniformization.Proof

/-!
# Restrict a dilated tube cover to a fine subfamily

This records the identity-compatible restriction operation needed when the
same selected fine family is used across several distinguished scales.
-/

noncomputable section

namespace Kakeya.Streamlined

def RestrictDilatedTubeCoverStatement : Prop :=
  ∀ {δ ρ A : ℝ},
    ∀ {fine : TubeFamily δ} {coarse : TubeFamily ρ},
      ∀ P : DilatedTubeCover A fine coarse,
      ∀ S : TubeSubfamily fine,
        ∃ C : TubeSubfamily coarse,
          ∃ Q : DilatedTubeCover A S.family C.family,
            ∀ i,
              C.embedding (Q.parent i) =
                P.parent (S.embedding i)

end Kakeya.Streamlined
