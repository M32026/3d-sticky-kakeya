module

/-
# Thickening Covering Bound

For the Route A rounding fix, we need to bound the dyadic covering number
of a δ-thickened 1D set.

## Key lemma

`Nreal δ (thickenSet δ A) ≤ 3 * Nreal δ A` for bounded `A`.

Proof: uses `SetDiscretizationBridge.thickening_covering_factor` with M=1.
Every point in the δ-thickening is within δ of a point in A, so the
factor is `2*1+1 = 3`.

## Factor 6 decomposition

1. Factor 2: scalar covering `|chartFullLambda| ≤ 1`
2. Factor 3: δ-thickening covering `N(thickenSet δ X) ≤ 3*N(X)`
3. Total: 2 × 3 = 6
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-- Explicit additive thickening of a real set. -/
def thickenSet (ε : ℝ) (A : Set ℝ) : Set ℝ :=
  {z | ∃ a ∈ A, |z - a| ≤ ε}

/-- Alias for `thickenSet`, used in Route B integration. -/
def intervalThicken (ε : ℝ) (A : Set ℝ) : Set ℝ :=
  thickenSet ε A

/-- Scaling a thickened set.

`scaleSet c (thickenSet ε A) = thickenSet (|c| * ε) (scaleSet c A)`.
Requires `0 ≤ ε`. -/
lemma scaleSet_thickenSet (c ε : ℝ) (A : Set ℝ) (hepsilon : 0 ≤ ε) :
    scaleSet c (thickenSet ε A) = thickenSet (|c| * ε) (scaleSet c A) := by
  ext z
  simp only [scaleSet, thickenSet, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨a, ha, hwa⟩, rfl⟩
    refine ⟨c * a, ⟨a, ha, rfl⟩, ?_⟩
    have h : |c * w - c * a| = |c| * |w - a| := by rw [← mul_sub, abs_mul]
    rw [h]; exact mul_le_mul_of_nonneg_left hwa (abs_nonneg c)
  · rintro ⟨u, ⟨a, ha, hu⟩, hz⟩
    by_cases hc : c = 0
    · -- c = 0
      have h_u0 : u = 0 := by
        have h : c * a = u := hu
        rw [hc] at h
        simpa [mul_zero] using Eq.symm h
      have hz' : |z - u| ≤ |c| * ε := hz
      rw [h_u0] at hz'
      have hz0 : z = 0 := by
        have h : |z| ≤ 0 := by simpa [hc, abs_zero] using hz'
        exact abs_nonpos_iff.mp h
      have h_aa : |a - a| ≤ ε := by
        have h : |a - a| = 0 := by simp
        rw [h]
        exact hepsilon
      have h_a_in : a ∈ thickenSet ε A := ⟨a, ha, h_aa⟩
      have h_goal : z ∈ scaleSet c (thickenSet ε A) := by
        rw [hz0, hc]
        exact ⟨a, h_a_in, by simp⟩
      exact h_goal
    · -- c ≠ 0
      have h4 : |z - u| ≤ |c| * ε := hz
      have h_eq : u = c * a := Eq.symm hu
      have h5 : |z - c * a| ≤ |c| * ε := by
        rw [h_eq] at h4
        exact h4
      have h_near : |z / c - a| ≤ ε := by
        have h6 : |z / c - a| = |z - c * a| / |c| := by
          have h7 : z / c - a = (z - c * a) / c := by field_simp [hc] <;> ring
          rw [h7, abs_div]
        rw [h6]
        have h_abs_pos : 0 < |c| := abs_pos.mpr hc
        calc |z - c * a| / |c|
            ≤ (|c| * ε) / |c| := by gcongr
          _ = ε := by field_simp [h_abs_pos.ne'] <;> ring
      have h_w_in : z / c ∈ thickenSet ε A := ⟨a, ha, h_near⟩
      have h_z_in : z ∈ scaleSet c (thickenSet ε A) := by
        exact ⟨z / c, h_w_in, by field_simp [hc] <;> ring⟩
      exact h_z_in

/-- Alias for `scaleSet_thickenSet`. -/
lemma scaleSet_intervalThicken (c ε : ℝ) (A : Set ℝ) (hepsilon : 0 ≤ ε) :
    scaleSet c (intervalThicken ε A) = intervalThicken (|c| * ε) (scaleSet c A) :=
  scaleSet_thickenSet c ε A hepsilon

/-- Covering number bound for δ-thickening of a bounded 1D set.

Every point in `thickenSet δ A` is within δ of a point in `A`, so by
`thickening_covering_factor` with `M=1`, the covering number increases
by at most a factor of `2*1+1 = 3`. -/
lemma Nreal_thicken_delta_le_three {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA : IsBounded A) :
    Nreal δ (thickenSet δ A) ≤ 3 * Nreal δ A := by
  have h_main : dyadicCoveringNumber δ (productLikeRealLineCopy (thickenSet δ A)) ≤
      (2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (productLikeRealLineCopy A) :=
    SetDiscretizationBridge.thickening_covering_factor hδ hA
      (fun p hp => by
        rcases hp with ⟨q, hq, hdist⟩
        exact ⟨q, hq, by simpa using hdist⟩)
  have h_eq1 : productLikeRealLineCopy (thickenSet δ A) = realLineCopy (thickenSet δ A) := by
    rfl
  have h_eq2 : productLikeRealLineCopy A = realLineCopy A := by rfl
  rw [h_eq1, h_eq2] at h_main
  have h4 := ENat.toENNReal_mono h_main
  have h6 : ENat.toENNReal ((2 * (1 : ℕ) + 1) * dyadicCoveringNumber δ (realLineCopy A)) =
      ENat.toENNReal (2 * (1 : ℕ) + 1) * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by
    rw [ENat.toENNReal_mul]
  have h7 : ENat.toENNReal (2 * (1 : ℕ) + 1) = (3 : ENNReal) := by
    norm_cast <;> decide
  rw [h6, h7] at h4
  exact h4

/-- Alias for `Nreal_thicken_delta_le_three`, used in Route B integration. -/
lemma intervalThicken_covering_bound {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA : IsBounded A) :
    Nreal δ (intervalThicken δ A) ≤ 3 * Nreal δ A :=
  Nreal_thicken_delta_le_three hδ hA

end ProductLikeIncidence.ProductReduction
