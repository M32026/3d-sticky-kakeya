import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Local AD covering upper bound for WZ Lemma 30

This is the subset-stable transition from a projected tube segment localized
inside one scalar ball to the corresponding `IsADSet1` covering bound.
-/

namespace Kakeya.Assouad

lemma IsADSet1.externalCoveringNumber_le_of_subset_closedBall
    {A E : Set ℝ} {rho alpha : ℝ} {C : ENNReal}
    (hAD : IsADSet1 A rho alpha C)
    (hEA : E ⊆ A)
    {center radius : ℝ}
    (hEball : E ⊆ Metric.closedBall center radius)
    (hrho_radius : rho ≤ radius)
    (hradius_one : radius ≤ 1) :
    (↑(Metric.externalCoveringNumber
      ⟨rho, hAD.1.le⟩ E) : ENNReal) ≤
        C * Kakeya.realRpowENN (radius / rho) alpha := by
  have hsubset :
      E ⊆ A ∩ Metric.closedBall center radius :=
    Set.subset_inter hEA hEball
  have hmono :
      Metric.externalCoveringNumber ⟨rho, hAD.1.le⟩ E ≤
        Metric.externalCoveringNumber ⟨rho, hAD.1.le⟩
          (A ∩ Metric.closedBall center radius) :=
    Metric.externalCoveringNumber_mono_set hsubset
  have hmono' :
      (↑(Metric.externalCoveringNumber
        ⟨rho, hAD.1.le⟩ E) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber
        ⟨rho, hAD.1.le⟩
          (A ∩ Metric.closedBall center radius)) : ENNReal) := by
    exact_mod_cast hmono
  have hrho_one : rho ≤ 1 :=
    hrho_radius.trans hradius_one
  exact hmono'.trans
    (hAD.2.2.2.2.2 rho hAD.1.le le_rfl hrho_one center radius
      hrho_radius hradius_one)

end Kakeya.Assouad
