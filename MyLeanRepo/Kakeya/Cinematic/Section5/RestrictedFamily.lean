import MyLeanRepo.Kakeya.Cinematic.Section5.RestrictedMetric
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialRectangleRefinement.DoublingCover

/-!
# Cinematic families in a restricted physical metric

The physical `C²` metric on a parameter subinterval is uniformly equivalent
to the ambient metric on a cinematic family. Consequently the diameter,
curvature lower bound, and doubling property transport with constants
depending only on the original `K` and `D`, not on the interval length.
-/

noncomputable section

namespace Kakeya.Cinematic

open C2Function

def IsRestrictedCinematicFamily
    (family : Set C2Function) (I : ParameterInterval) (K D : ℝ) : Prop :=
  (∀ ⦃f⦄, f ∈ family → ∀ ⦃g⦄, g ∈ family →
      restrictedC2Distance I f g ≤ K) ∧
  (∀ ⦃f⦄, f ∈ family → ∀ r : ℝ, 0 < r →
    ∃ centers : Set C2Function,
      centers.Finite ∧ centers ⊆ family ∧
      (centers.ncard : ℝ) ≤ D ∧
      ∀ ⦃g⦄, g ∈ family → restrictedC2Distance I f g ≤ r →
        ∃ h ∈ centers, restrictedC2Distance I h g ≤ r / 2) ∧
  (∀ ⦃f⦄, f ∈ family → ∀ ⦃g⦄, g ∈ family →
    ∀ x : I.LocalPoint,
      K⁻¹ * restrictedC2Distance I f g ≤ jetGap f g x.1)

lemma isRestrictedCinematicFamily_of_global
    {family : Set C2Function} {K D : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hfamily : IsCinematicFamily family K D)
    (I : ParameterInterval) :
    IsRestrictedCinematicFamily family I K
      (D * Real.rpow (6 * K) (Real.log D / Real.log 2)) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨?_, ?_, ?_⟩
  · intro f hf g hg
    exact
      (restrictedC2Distance_le I f g).trans
        (hfamily.1 hf hg)
  · intro f hf r hr
    let R : ℝ := 3 * K * r
    let small : ℝ := r / 2
    have hR : 0 < R := by
      dsimp only [R]
      positivity
    have hsmall : 0 < small := by
      dsimp only [small]
      positivity
    have hsmallR : small ≤ R := by
      dsimp only [small, R]
      nlinarith
    rcases polynomial_doubling_cover
        hfamily hD f hf R small hR hsmall hsmallR with
      ⟨centers, hcenters_sub, hcard, hcover⟩
    let centersSet : Set C2Function := centers
    have hfinite : centersSet.Finite := centers.finite_toSet
    refine ⟨centersSet, hfinite, hcenters_sub, ?_, ?_⟩
    · have hratio : R / small = 6 * K := by
        dsimp only [R, small]
        field_simp [hr.ne']
        ring
      have hcard' : (centers.card : ℝ) ≤
          D * Real.rpow (6 * K) (Real.log D / Real.log 2) := by
        rw [← hratio]
        exact hcard
      simpa [centersSet] using hcard'
    · intro g hg hlocal
      have hglobal : c2Distance f g ≤ R := by
        calc
          c2Distance f g ≤
              3 * K * restrictedC2Distance I f g :=
            c2Distance_le_three_mul_restrictedC2Distance
              hK hfamily hf hg I
          _ ≤ 3 * K * r := by gcongr
          _ = R := rfl
      rcases hcover g hg hglobal with ⟨h, hh, hdist⟩
      refine ⟨h, hh, ?_⟩
      exact
        (restrictedC2Distance_le I h g).trans
          (by simpa [small] using hdist)
  · intro f hf g hg x
    calc
      K⁻¹ * restrictedC2Distance I f g ≤
          K⁻¹ * c2Distance f g := by
        gcongr
        exact restrictedC2Distance_le I f g
      _ ≤ jetGap f g x.1 := hfamily.2.2 hf hg x.1

end Kakeya.Cinematic
