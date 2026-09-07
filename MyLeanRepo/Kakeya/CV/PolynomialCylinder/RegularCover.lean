import MyLeanRepo.Kakeya.CV.PolynomialCylinder.DirectionCovers

/-!
# Unified direction-tagged regular cover

Combines the simultaneous graph-patch covers in the three coordinate
directions into one countable family. Every regular zero has a nonzero
gradient coordinate and hence belongs to a patch in the corresponding family.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

/-- Coordinate graph map selected by its regular derivative direction. -/
def dirGraphMap : Fin 3 → (Point 2 → ℝ) → Point 2 → Point 3
  | 0, g, y => xGraphMap g y
  | 1, g, y => yGraphMap g y
  | 2, g, y => graphMap g y

/-- A simultaneous graph patch tagged by its regular coordinate direction. -/
structure CoverPatch (k : ℕ) (P : PolynomialParameterization k) where
  dir : Fin 3
  V : Set (CoefficientSpace P.dim)
  A : Set (Point 2)
  g : CoefficientSpace P.dim → Point 2 → ℝ
  hV_open : IsOpen V
  hA_open : IsOpen A
  hg_smooth : ContDiffOn ℝ 1
    (fun p : CoefficientSpace P.dim × Point 2 => g p.1 p.2) (V ×ˢ A)
  h_zero : ∀ x ∈ V, ∀ y ∈ A,
    polynomialValue (parameterPolynomial P x)
      (dirGraphMap dir (g x) y) = 0
  h_reg : ∀ x ∈ V, ∀ y ∈ A,
    (polynomialGradient (parameterPolynomial P x)
      (dirGraphMap dir (g x) y)) dir ≠ 0

/-- Countable simultaneous cover of the regular zero sets by
direction-tagged graph patches. -/
theorem exists_countable_regular_cover (P : PolynomialParameterization k) :
    ∃ patches : ℕ → CoverPatch k P,
      ∀ (x : CoefficientSpace P.dim) (z : Point 3),
        polynomialValue (parameterPolynomial P x) z = 0 →
        polynomialGradient (parameterPolynomial P x) z ≠ 0 →
        ∃ n : ℕ, x ∈ (patches n).V ∧
          ∃ y ∈ (patches n).A,
            z = dirGraphMap (patches n).dir ((patches n).g x) y := by
  obtain ⟨zpatches, hzcover⟩ := exists_countable_zgraph_cover P
  obtain ⟨xpatches, hxcover⟩ := exists_countable_xgraph_cover P
  obtain ⟨ypatches, hycover⟩ := exists_countable_ygraph_cover P
  let toZPatch (n : ℕ) : CoverPatch k P :=
    { dir := 2
      V := (zpatches n).V
      A := (zpatches n).A
      g := (zpatches n).g
      hV_open := (zpatches n).hV_open
      hA_open := (zpatches n).hA_open
      hg_smooth := (zpatches n).hg_smooth
      h_zero := (zpatches n).h_zero
      h_reg := (zpatches n).h_reg }
  let toXPatch (n : ℕ) : CoverPatch k P :=
    { dir := 0
      V := (xpatches n).V
      A := (xpatches n).A
      g := (xpatches n).g
      hV_open := (xpatches n).hV_open
      hA_open := (xpatches n).hA_open
      hg_smooth := (xpatches n).hg_smooth
      h_zero := (xpatches n).h_zero
      h_reg := (xpatches n).h_reg }
  let toYPatch (n : ℕ) : CoverPatch k P :=
    { dir := 1
      V := (ypatches n).V
      A := (ypatches n).A
      g := (ypatches n).g
      hV_open := (ypatches n).hV_open
      hA_open := (ypatches n).hA_open
      hg_smooth := (ypatches n).hg_smooth
      h_zero := (ypatches n).h_zero
      h_reg := (ypatches n).h_reg }
  let patches : ℕ → CoverPatch k P := fun n =>
    if n % 3 = 0 then toZPatch (n / 3)
    else if n % 3 = 1 then toXPatch (n / 3)
    else toYPatch (n / 3)
  have hpatch0 : ∀ n, patches (3 * n) = toZPatch n := by
    intro n
    have hmod : (3 * n) % 3 = 0 := by omega
    have hdiv : (3 * n) / 3 = n := by omega
    simp [patches, hmod, hdiv]
  have hpatch1 : ∀ n, patches (3 * n + 1) = toXPatch n := by
    intro n
    have hmod : (3 * n + 1) % 3 = 1 := by omega
    have hdiv : (3 * n + 1) / 3 = n := by omega
    simp [patches, hmod, hdiv]
  have hpatch2 : ∀ n, patches (3 * n + 2) = toYPatch n := by
    intro n
    have hmod : (3 * n + 2) % 3 = 2 := by omega
    have hdiv : (3 * n + 2) / 3 = n := by omega
    simp [patches, hmod, hdiv]
  refine ⟨patches, ?_⟩
  intro x z hzero hgrad
  by_cases h₂ :
      (polynomialGradient (parameterPolynomial P x) z) 2 ≠ 0
  · obtain ⟨n, hxV, y, hyA, heq⟩ := hzcover x z hzero h₂
    have hp : patches (3 * n) = toZPatch n := hpatch0 n
    refine ⟨3 * n, ?_, y, ?_, ?_⟩
    · rw [hp]
      exact hxV
    · rw [hp]
      exact hyA
    · rw [hp]
      simpa [toZPatch, dirGraphMap] using heq
  · by_cases h₀ :
        (polynomialGradient (parameterPolynomial P x) z) 0 ≠ 0
    · obtain ⟨n, hxV, y, hyA, heq⟩ := hxcover x z hzero h₀
      have hp : patches (3 * n + 1) = toXPatch n := hpatch1 n
      refine ⟨3 * n + 1, ?_, y, ?_, ?_⟩
      · rw [hp]
        exact hxV
      · rw [hp]
        exact hyA
      · rw [hp]
        simpa [toXPatch, dirGraphMap] using heq
    · have h₁ :
          (polynomialGradient (parameterPolynomial P x) z) 1 ≠ 0 := by
        have h₂' :
            (polynomialGradient (parameterPolynomial P x) z) 2 = 0 :=
          not_ne_iff.mp h₂
        have h₀' :
            (polynomialGradient (parameterPolynomial P x) z) 0 = 0 :=
          not_ne_iff.mp h₀
        by_contra h₁'
        apply hgrad
        ext j
        fin_cases j <;> assumption
      obtain ⟨n, hxV, y, hyA, heq⟩ := hycover x z hzero h₁
      have hp : patches (3 * n + 2) = toYPatch n := hpatch2 n
      refine ⟨3 * n + 2, ?_, y, ?_, ?_⟩
      · rw [hp]
        exact hxV
      · rw [hp]
        exact hyA
      · rw [hp]
        simpa [toYPatch, dirGraphMap] using heq

end Kakeya.CV
