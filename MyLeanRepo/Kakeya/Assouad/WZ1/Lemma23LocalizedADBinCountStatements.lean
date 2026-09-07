import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ADBinCountStatements

/-!
# Localized scalar-bin counts for WZ1 Lemma 23

The first Cauchy--Schwarz step in Lemma 23 needs the number of local-grain
scalar bins inside one spatial ball of radius `R`, not the coarser global
count over all of `[-4,4]`.  The local clause of `IsADSet1` covers
`E ∩ closedBall center R` by at most `C * (R / rho)^alpha` radius-`rho`
balls, and each such ball meets at most three integer `rho`-mesh bins.
-/

namespace Kakeya.Assouad

noncomputable section

/--
A finite subset of one localized AD set occupies at most three times the
corresponding external covering-number bound.
-/
def WZ1Lemma23LocalizedADBinCountStatement : Prop :=
  ∀ (rho R alpha : ℝ) (C : ENNReal)
    (E : Set ℝ) (values : Finset ℝ) (center : ℝ),
    IsADSet1 E rho alpha C →
    rho ≤ R →
    R ≤ 1 →
    (values : Set ℝ) ⊆ E ∩ Metric.closedBall center R →
      ((wz1Lemma23ScalarBins rho values).card : ENNReal) ≤
        3 * C * Kakeya.realRpowENN (R / rho) alpha

end

end Kakeya.Assouad
