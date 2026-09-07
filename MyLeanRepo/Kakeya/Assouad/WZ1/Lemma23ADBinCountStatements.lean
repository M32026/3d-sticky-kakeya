import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoveringNumberBridge
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Count scalar mesh bins in a WZ1 Lemma 23 AD set

The local and global grain relations use integer bins
`floor(value / rho)`.  A closed ball of radius `rho` in `ℝ` meets at most
three such bins.  Since every `IsADSet1` lies in `[-4,4]`, four unit balls
localize the AD covering bound.  Therefore a finite subset of the AD set
occupies at most

`12 * C * (1 / rho)^alpha`

mesh bins.

This is the quantitative bridge from the continuous local/global AD
certificates to the finite signature count in the four-cycle argument.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Integer `rho`-mesh bins occupied by a finite set of scalar values. -/
def wz1Lemma23ScalarBins
    (rho : ℝ) (values : Finset ℝ) : Finset ℤ :=
  values.image fun value => Int.floor (value / rho)

/--
A finite subset of a one-dimensional AD set occupies at most the stated
number of `rho`-mesh bins.
-/
def WZ1Lemma23ADBinCountStatement : Prop :=
  ∀ (rho alpha : ℝ) (C : ENNReal)
    (E : Set ℝ) (values : Finset ℝ),
    IsADSet1 E rho alpha C →
    rho ≤ 1 →
    (values : Set ℝ) ⊆ E →
      ((wz1Lemma23ScalarBins rho values).card : ENNReal) ≤
        12 * C * Kakeya.realRpowENN (1 / rho) alpha

end

end Kakeya.Assouad
