import MyLeanRepo.Kakeya.Assouad.PropStickyStatements

/-!
# Finite capsule control of cropped paper tubes

The paper carrier is the `6 * delta` closed neighborhood of the full coaxial
line, cropped to `[-1,1]^3`.  For an `L₃` line, the positive vertical
component is at least `1/2`.  Hence every same-height axis point above the
cropped box has axis parameter in `[-2,2]`.

The radius `24 * delta` leaves room to choose a point within `7 * delta` of
the full line and then move along the line to the same height.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The length-four axis segment with paper parameter in `[-2,2]`. -/
def wz2PaperAxisCoreSegment
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Set Point3 :=
  (fun parameter : ℝ =>
      wz1TubeAxisZeroPoint tube +
        (parameter - 2) • wz1PaperDirection tube) ''
    Set.Icc 0 4

def WZ2PaperTubeCarrierGeometryStatement : Prop :=
  ∀ {delta : ℝ},
    0 < delta →
    ∀ tube : Kakeya.DeltaTube delta,
      WZ1PaperTubeInLineClass tube →
        Convex ℝ (wz1PaperTubeCarrier tube) ∧
          wz1PaperTubeCarrier tube ⊆
            Metric.cthickening (24 * delta)
              (wz2PaperAxisCoreSegment tube)

end Kakeya.Assouad

end
