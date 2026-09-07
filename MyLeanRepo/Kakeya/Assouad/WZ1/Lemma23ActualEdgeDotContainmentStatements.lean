import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23BaseCyclePigeonholeStatements

/-!
# Actual-edge dot containment in WZ1 Lemma 23

After fixing the first cube's snapped height and global scalar bin, every
actual centered tripartite edge comes from an actual base four-cycle.  The
four-cycle telescope places its dot difference within `4 * rho` of the
snapped global coordinate of that cycle's fourth cube, which lies on the
same fixed snapped height.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Global scalar values of actual snapped cells on one fixed height layer. -/
def wz1Lemma23SnappedBaseSliceValues
    (rho : ℝ) (f : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (baseHeightIndex baseGlobalBin : ℤ) : Finset ℝ :=
  (cells.filter fun idx =>
    wz1Lemma23SnappedHeight idx = baseHeightIndex).image fun idx =>
      wz1Lemma23GlobalCoordinate f
          (wz1Lemma23SnappedPoint rho idx) -
        (baseGlobalBin : ℝ) * rho

/--
The dot-difference set of the actual centered tripartite edge image is
contained in the `4 * rho` thickening of the actual snapped base-slice values.
-/
def WZ1Lemma23ActualEdgeDotContainmentStatement : Prop :=
  ∀ (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (baseHeightIndex baseGlobalBin : ℤ),
    0 < rho →
      let baseCycles :=
        wz1Lemma23SnappedBaseCycles
          rho f g cells baseHeightIndex baseGlobalBin
      let edge :=
        wz1Lemma23SnappedTripartiteEdge
          rho f g baseHeightIndex
      let edges := baseCycles.image edge
      wz1DotDifferenceSet edges ⊆
        Metric.cthickening (4 * rho)
          (wz1Lemma23SnappedBaseSliceValues
            rho f cells baseHeightIndex baseGlobalBin : Set ℝ)

end

end Kakeya.Assouad
