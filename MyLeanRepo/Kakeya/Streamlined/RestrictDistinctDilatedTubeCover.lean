import MyLeanRepo.Kakeya.Streamlined.RestrictDilatedTubeCover.Proof

/-!
# Restrict a distinct dilated tube cover

This is the one-scale cover-system record needed after selecting a common
fine tube subfamily.
-/

noncomputable section

namespace Kakeya.Streamlined

def RestrictDistinctDilatedTubeCoverStatement : Prop :=
  ∀ {δ ρ A : ℝ},
    ∀ {fine : TubeFamily δ} {coarse : TubeFamily ρ},
      coarse.IsEssentiallyDistinct →
      ∀ P : DilatedTubeCover A fine coarse,
      ∀ S : TubeSubfamily fine,
        ∃ C : TubeSubfamily coarse,
          C.family.IsEssentiallyDistinct ∧
          ∃ Q : DilatedTubeCover A S.family C.family,
            ∀ i,
              C.embedding (Q.parent i) =
                P.parent (S.embedding i)

end Kakeya.Streamlined
