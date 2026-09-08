import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Self-containment under homothetic dilation

A tube is contained in any homothetic dilation of itself about its midpoint
with dilation factor `A ≥ 1`.

## Main result

`self_dilated_containment`: `T.carrier ⊆ dilatedTubeCarrier A T` for `1 ≤ A`.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

/-- Tube carriers are convex. -/
lemma deltaTube_carrier_convex' {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    Convex ℝ T.carrier := by
  have h1 : Convex ℝ (Kakeya.unitSegment T.base T.direction) := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rcases hy with ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have h_sum0 : 0 ≤ a * t + b * s := by positivity
    have h_sum1 : a * t + b * s ≤ 1 := by
      calc a * t + b * s ≤ a * 1 + b * 1 := by gcongr <;> linarith
        _ = 1 := by linarith
    refine ⟨a * t + b * s, ⟨h_sum0, h_sum1⟩, ?_⟩
    have h_eq : a • (T.base + t • T.direction) + b • (T.base + s • T.direction) =
        T.base + (a * t + b * s) • T.direction := by
      have h1 : a • (T.base + t • T.direction) = a • T.base + (a * t) • T.direction := by
        rw [smul_add, smul_smul]
      have h2 : b • (T.base + s • T.direction) = b • T.base + (b * s) • T.direction := by
        rw [smul_add, smul_smul]
      rw [h1, h2]
      have h3 : a • T.base + (a * t) • T.direction + (b • T.base + (b * s) • T.direction) =
          (a + b) • T.base + (a * t + b * s) • T.direction := by
        have h4 : a • T.base + (a * t) • T.direction + (b • T.base + (b * s) • T.direction) =
            (a • T.base + b • T.base) + ((a * t) • T.direction + (b * s) • T.direction) := by abel
        rw [h4, add_smul, add_smul]
      rw [h3, hab, one_smul]
    exact h_eq.symm
  exact Convex.cthickening h1 δ

/-- The midpoint of a tube lies in its carrier. -/
lemma tubeMidpoint_mem_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    tubeMidpoint T ∈ T.carrier := by
  have h_mid_on_seg : tubeMidpoint T ∈ Kakeya.unitSegment T.base T.direction := by
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp [tubeMidpoint] <;> abel
  have h_inf_zero : Metric.infEDist (tubeMidpoint T)
      (Kakeya.unitSegment T.base T.direction) = 0 :=
    Metric.infEDist_zero_of_mem h_mid_on_seg
  have h4 : Metric.infEDist (tubeMidpoint T)
      (Kakeya.unitSegment T.base T.direction) ≤ ENNReal.ofReal δ := by
    rw [h_inf_zero] <;> positivity
  exact h4

/-- **Self-containment under dilation.**

For any dilation factor `A ≥ 1`, a tube is contained in the homothetic
dilation of itself about its midpoint.

Proof: the tube carrier is convex and contains its midpoint. For any point
`x` in the tube, the point `y = midpoint + (1/A) • (x - midpoint)` is a
convex combination of `x` and the midpoint, hence lies in the tube. The
homothety with factor `A` maps `y` back to `x`. -/
lemma self_dilated_containment {ρ : ℝ} (A : ℝ) (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube ρ) :
    T.carrier ⊆ dilatedTubeCarrier A T := by
  have h_conv : Convex ℝ T.carrier := deltaTube_carrier_convex' T
  have h_mid : tubeMidpoint T ∈ T.carrier := tubeMidpoint_mem_carrier T
  intro x hx
  by_cases hA1 : A = 1
  · -- A = 1: homothety is identity
    rw [hA1]
    exact ⟨x, hx, by simp [dilatedTubeCarrier]⟩
  · have hA_pos : 0 < A := by linarith
    let a : ℝ := 1 - 1 / A
    let b : ℝ := 1 / A
    have ha_nonneg : 0 ≤ a := by
      dsimp only [a]
      have h : 1 / A ≤ 1 := by
        apply (div_le_one (by linarith)).mpr <;> linarith
      linarith
    have hb_nonneg : 0 ≤ b := by positivity
    have hab : a + b = 1 := by
      dsimp only [a, b] <;> ring
    let y : Point3 := a • tubeMidpoint T + b • x
    have h_y_in : y ∈ T.carrier :=
      h_conv h_mid hx ha_nonneg hb_nonneg hab
    have h4 : y - tubeMidpoint T = (1 / A) • (x - tubeMidpoint T) := by
      dsimp only [y, a, b]
      ext i
      simp [sub_smul, smul_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      <;> ring
    have h_map : AffineMap.homothety (tubeMidpoint T) A y = x := by
      rw [AffineMap.homothety_apply]
      have h3 : (A • (y -ᵥ tubeMidpoint T) +ᵥ tubeMidpoint T) =
          tubeMidpoint T + A • (y - tubeMidpoint T) := by
        ext i <;> simp <;> ring
      rw [h3]
      rw [h4, smul_smul]
      have h5 : A * (1 / A) = 1 := by field_simp [hA_pos.ne'] <;> ring
      rw [h5, one_smul] <;> abel
    exact ⟨y, h_y_in, h_map⟩

end Kakeya.Streamlined.GeometricLemmas
