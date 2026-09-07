import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.Perimeter

variable {n : ℕ}

/-! # Perimeter Measure Properties

Properties of the local De Giorgi perimeter `perimeterIn S Ω`.

## Main results

- `perimeterIn_mono`: monotonicity in the domain
- `perimeterIn_ball_ae_continuous`: `r ↦ perimeterIn S (ball x₀ r)` is continuous a.e.
- `perimeterIn_ball_rightContinuous_ae`: right-continuity at a.e. radius

## References

- Maggi, *Sets of Finite Perimeter*, Chapter 12
- Ambrosio-Fusco-Pallara, *Functions of BV*, Chapter 2
-/

/-- **Monotonicity of local perimeter in the domain**.

If `Ω₁ ⊆ Ω₂`, then every test vector field supported in `Ω₁` is also supported
in `Ω₂`, so the supremum over the larger domain is at least as large. -/
lemma perimeterIn_mono {S : Set (E n)} {Ω₁ Ω₂ : Set (E n)} (h : Ω₁ ⊆ Ω₂) :
    perimeterIn S Ω₁ ≤ perimeterIn S Ω₂ := by
  rw [perimeterIn, perimeterIn]
  apply iSup_le
  intro Φ₁
  let Φ₂ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω₂} :=
    ⟨Φ₁.val, Φ₁.property.trans h⟩
  have h_eq : (ENNReal.ofReal |∫ x in S, divergence Φ₁.val.toFun x|) =
      (ENNReal.ofReal |∫ x in S, divergence Φ₂.val.toFun x|) := by rfl
  rw [h_eq]
  exact le_iSup (fun (Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω₂}) =>
    ENNReal.ofReal |∫ x in S, divergence Φ.val.toFun x|) Φ₂

/-- The function `r ↦ perimeterIn S (ball x₀ r)` is monotone. -/
lemma perimeterIn_ball_monotone (S : Set (E n)) (x₀ : E n) :
    Monotone (fun r : ℝ => perimeterIn S (ball x₀ r)) := by
  intro r₁ r₂ h
  have hball : ball x₀ r₁ ⊆ ball x₀ r₂ := by
    intro x hx
    have hdist : dist x x₀ < r₁ := by simpa [ball] using hx
    have hdist2 : dist x x₀ < r₂ := by
      exact hdist.trans_le h
    simpa [ball] using hdist2
  exact perimeterIn_mono hball

/-- **A.e. continuity of perimeter in the radius**.

The function `r ↦ perimeterIn S (ball x₀ r)` is monotone, hence has at most
countably many discontinuities by `Monotone.countable_not_continuousAt`.
A countable set has Lebesgue measure zero, so the function is continuous a.e. -/
lemma perimeterIn_ball_ae_continuous (S : Set (E n)) (x₀ : E n) :
    ∀ᵐ (r : ℝ), ContinuousAt (fun r : ℝ => perimeterIn S (ball x₀ r)) r := by
  let f : ℝ → ENNReal := fun r => perimeterIn S (ball x₀ r)
  have h_mono : Monotone f := perimeterIn_ball_monotone S x₀
  have h_count : Set.Countable {x : ℝ | ¬ContinuousAt f x} :=
    h_mono.countable_not_continuousAt
  have h_null : volume {x : ℝ | ¬ContinuousAt f x} = 0 := by
    exact h_count.measure_zero volume
  have h_ae : ∀ᵐ (r : ℝ), ContinuousAt f r := by
    rw [ae_iff]
    exact h_null
  exact h_ae

/-- **Right-continuity at a.e. radius**.

For a.e. `r`, as `ε → 0+`, `perimeterIn S (ball x₀ (r + ε)) → perimeterIn S (ball x₀ r)`.

This follows from a.e. continuity of `r ↦ perimeterIn S (ball x₀ r)`. -/
lemma perimeterIn_ball_rightContinuous_ae (S : Set (E n)) (x₀ : E n) :
    ∀ᵐ (r : ℝ), Tendsto (fun ε : ℝ => perimeterIn S (ball x₀ (r + ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (perimeterIn S (ball x₀ r))) := by
  let f : ℝ → ENNReal := fun r => perimeterIn S (ball x₀ r)
  have h_ae := perimeterIn_ball_ae_continuous S x₀
  filter_upwards [h_ae] with r hr
  have h_cont : ContinuousAt f r := hr
  have h1 : Tendsto (fun ε : ℝ => r + ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds r) := by
    have h_cont : Continuous (fun ε : ℝ => r + ε) := by fun_prop
    have h_at0 : ContinuousAt (fun ε : ℝ => r + ε) 0 := h_cont.continuousAt
    have h_tendsto : Tendsto (fun ε : ℝ => r + ε) (nhds 0) (nhds r) := by
      simpa [add_zero] using h_at0.tendsto
    exact h_tendsto.mono_left nhdsWithin_le_nhds
  exact h_cont.tendsto.comp h1

end Geometry.Perimeter
