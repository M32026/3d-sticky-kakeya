import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Separation constants for literal recursive partitioning

Literal doubled-fiber partitioning requires a larger fixed margin than the
historical essentially-distinctness argument.  The constants here are chosen
so that the closed lower-distortion bound `7350` leaves more than
`1600 * (rho / sigma)` separation in the rescaled family.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Source-parent separation factor used for literal partitioning after
rescaling. -/
def wz2PaperLiteralSourceSeparationFactor : ℕ :=
  12000000

/-- Packing loss for a `12000000 * rho` conflict neighborhood. -/
def wz2PaperLiteralSeparationPackingConstant : ℕ :=
  192000001 ^ 5

lemma tube_packing_bound_literalSeparation
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hed : WZ1PaperIsEssentiallyDistinct fine)
    (hline : WZ1PaperIsLineClass fine)
    (hdelta : 0 < delta)
    (i : Fin fine.card) :
    (Finset.univ.filter fun j =>
      wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤
        wz2PaperLiteralSourceSeparationFactor * delta).card ≤
      wz2PaperLiteralSeparationPackingConstant := by
  have h :=
    tube_packing_bound_general hed hline hdelta
      (wz2PaperLiteralSourceSeparationFactor * delta)
      (by
        unfold wz2PaperLiteralSourceSeparationFactor
        positivity)
      i
  have hceil :
      Nat.ceil
          (8 * (wz2PaperLiteralSourceSeparationFactor * delta) /
            delta) =
        96000000 := by
    have halgebra :
        8 * (wz2PaperLiteralSourceSeparationFactor * delta) /
            delta =
          96000000 := by
      unfold wz2PaperLiteralSourceSeparationFactor
      field_simp [hdelta.ne']
      ring
    rw [halgebra]
    norm_num
  rw [hceil] at h
  simpa [wz2PaperLiteralSeparationPackingConstant] using h

end Kakeya.Assouad

end
