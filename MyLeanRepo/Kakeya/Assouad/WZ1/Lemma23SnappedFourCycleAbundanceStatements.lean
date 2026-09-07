import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleStatements

/-!
# The two Cauchy--Schwarz counts in WZ1 Lemma 23

The paper first groups snapped cells by their exact local key
`(y-index, local scalar bin)`, then groups the resulting local pairs by
`(first height, second height, second global scalar bin)`.

This module freezes the concrete finite count using the actual snapped keys
and actual snapped four-cycles.  The geometric producers only need to bound
the number of local scalar bins on each retained y-layer and the number of
global scalar bins on each retained height.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Integer y-layers occupied by a finite snapped-cell family. -/
def wz1Lemma23SnappedYLayers
    (cells : Finset (ℤ × ℤ × ℤ)) : Finset ℤ :=
  cells.image fun idx => idx.2.1

/-- Integer height layers occupied by a finite snapped-cell family. -/
def wz1Lemma23SnappedHeights
    (cells : Finset (ℤ × ℤ × ℤ)) : Finset ℤ :=
  cells.image fun idx => idx.2.2

/-- Local scalar bins occupied on one exact snapped y-layer. -/
def wz1Lemma23SnappedLocalBinsAt
    (rho : ℝ) (g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) (y : ℤ) :
    Finset ℤ :=
  (cells.filter fun idx => idx.2.1 = y).image fun idx =>
    Int.floor
      (wz1Lemma23LocalCoordinate g
        (wz1Lemma23SnappedPoint rho idx) / rho)

/-- Global scalar bins occupied on one exact snapped height layer. -/
def wz1Lemma23SnappedGlobalBinsAt
    (rho : ℝ) (f : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ)) (z : ℤ) :
    Finset ℤ :=
  (cells.filter fun idx => idx.2.2 = z).image fun idx =>
    wz1Lemma23SnappedGlobalBin rho f idx

/--
Concrete two-stage Cauchy--Schwarz abundance for snapped four-cycles.

If every occupied y-layer has at most `localBinBound` local scalar bins and
every occupied height has at most `globalBinBound` global scalar bins, then
the actual snapped four-cycle count satisfies the paper's fourth-power
lower-count inequality.
-/
def WZ1Lemma23SnappedFourCycleAbundanceStatement : Prop :=
  ∀ (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localBinBound globalBinBound : ℕ),
    (∀ y ∈ wz1Lemma23SnappedYLayers cells,
      (wz1Lemma23SnappedLocalBinsAt
        rho g cells y).card ≤ localBinBound) →
    (∀ z ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho f cells z).card ≤ globalBinBound) →
      cells.card ^ 4 ≤
        ((wz1Lemma23SnappedYLayers cells).card *
          localBinBound) ^ 2 *
        ((wz1Lemma23SnappedHeights cells).card ^ 2 *
          globalBinBound) *
        (wz1Lemma23SnappedFourCycles rho f g cells).card

end

end Kakeya.Assouad
