import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeFineProjectionCoveringTransfer

/-!
# Cell-normal projection transfer for WZ1 Lemma 18

After the two Lemma 17 refinements, the paper has a projection estimate in
the normal attached to a `tau`-cell.  Lemma 18 needs the normal attached to
the containing `sqrt rho` cell.  Lipschitz variation of the plane map and
`tau ≤ sqrt rho` make the two centered projections differ by `O(L * rho)`.

This is a purely metric leaf.  It does not select a good line, construct full
grains, or assert an interval-localized estimate.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Scalar projection centered at a specified spatial point. -/
def wz1CenteredScalarProjection
    (center normal : Point3) (E : Set Point3) : Set ℝ :=
  (fun point => inner ℝ (point - center) normal) '' E

/--
Transfer a local projection estimate from the normal at one `tau`-cell
center to the normal at the containing `sqrt rho`-cell center.

The hypothesis `1 ≤ K` is the paper-normalized Lipschitz constant
`max 1 L`.  The conclusion first records the exact centered containment and
then the covering-number loss from its `2 * K * rho` thickening.  Translation
invariance of external covering numbers converts the centered projections
back to the repository's ordinary `scalarProjection`.
-/
def WZ1Lemma18CellNormalProjectionTransferStatement : Prop :=
  ∀ rho tau K : ℝ,
    0 < rho →
    0 ≤ tau →
    tau ≤ Real.sqrt rho →
    1 ≤ K →
      ∀ (E : Set Point3) (planeMap : Point3 → Point3),
        ∀ localCenter cellCenter : Point3,
          dist localCenter cellCenter ≤ 2 * Real.sqrt rho →
          dist (planeMap localCenter) (planeMap cellCenter) ≤
            K * dist localCenter cellCenter →
            let localPiece :=
              E ∩ Metric.closedBall localCenter tau
            wz1CenteredScalarProjection
                localCenter (planeMap cellCenter) localPiece ⊆
              Metric.cthickening (2 * K * rho)
                (wz1CenteredScalarProjection
                  localCenter (planeMap localCenter) localPiece) ∧
            (↑(Metric.externalCoveringNumber
                (Real.toNNReal rho)
                (scalarProjection (planeMap cellCenter) localPiece)) :
                ENNReal) ≤
              (2 * Nat.ceil ((2 * K * rho) / rho) + 2 : ENNReal) *
                (↑(Metric.externalCoveringNumber
                  (Real.toNNReal rho)
                  (scalarProjection
                    (planeMap localCenter) localPiece)) : ENNReal)

end Kakeya.Assouad
