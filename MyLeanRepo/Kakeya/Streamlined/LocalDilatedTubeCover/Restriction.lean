import MyLeanRepo.Kakeya.Streamlined.RestrictDistinctDilatedTubeCover.Proof
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Restricting a coaxial-local dilated tube cover

An arbitrary fine subfamily retains exactly the coarse parents that it uses.
The restricted cover preserves dilation, transverse midpoint control, and
orientation-free direction control with exact parent-index compatibility.
-/

noncomputable section

namespace Kakeya.Streamlined

theorem restrict_local_dilated_tube_cover
    {delta rho A C : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (hcoarse : coarse.IsEssentiallyDistinct)
    (P : LocalDilatedTubeCover A C fine coarse)
    (S : TubeSubfamily fine) :
    ∃ R : TubeSubfamily coarse,
      R.family.IsEssentiallyDistinct ∧
      ∃ Q : LocalDilatedTubeCover A C S.family R.family,
        ∀ i,
          R.embedding (Q.parent i) =
            P.parent (S.embedding i) := by
  rcases restrict_distinct_dilated_tube_cover_main
      hcoarse P.toDilatedTubeCover S with
    ⟨R, hR_distinct, Q, hQ_compatible⟩
  let localQ : LocalDilatedTubeCover A C S.family R.family :=
    { toDilatedTubeCover := Q
      transverse_midpoint_close := by
        intro i
        rw [S.tube_eq i, R.tube_eq (Q.parent i), hQ_compatible i]
        exact P.transverse_midpoint_close (S.embedding i)
      direction_close_or_reverse := by
        intro i
        rw [S.tube_eq i, R.tube_eq (Q.parent i), hQ_compatible i]
        exact P.direction_close_or_reverse (S.embedding i) }
  exact ⟨R, hR_distinct, localQ, hQ_compatible⟩

end Kakeya.Streamlined
