import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses

/-!
# Graph lenses from localized zeros

Two ordered zeros with no zero between them determine a graph lens.
-/

namespace Kakeya.Cinematic

open Set

lemma graphLens_of_two_localized_zeros
    {f g : C2Function} (hne : f ≠ g)
    {h : ℝ → ℝ}
    (heval : ∀ x : UnitPoint, h (x : ℝ) = f x - g x)
    {z₁ z₂ : ℝ}
    (hz₁ : z₁ ∈ Icc (0 : ℝ) 1)
    (hz₂ : z₂ ∈ Icc (0 : ℝ) 1)
    (hlt : z₁ < z₂)
    (hzero₁ : h z₁ = 0)
    (hzero₂ : h z₂ = 0)
    (hbetween :
      ∀ x : ℝ, z₁ < x → x < z₂ → h x ≠ 0) :
    ∃ L : GraphLens,
      L.f = f ∧
      L.g = g ∧
      (L.left : ℝ) = z₁ ∧
      (L.right : ℝ) = z₂ := by
  let left : UnitPoint := ⟨z₁, hz₁⟩
  let right : UnitPoint := ⟨z₂, hz₂⟩
  have heq_left : f left = g left := by
    have hvalue := heval left
    change h z₁ = f left - g left at hvalue
    rw [hzero₁] at hvalue
    linarith
  have heq_right : f right = g right := by
    have hvalue := heval right
    change h z₂ = f right - g right at hvalue
    rw [hzero₂] at hvalue
    linarith
  let L : GraphLens :=
    { f := f
      g := g
      f_ne_g := hne
      left := left
      right := right
      left_lt_right := by
        simpa [left, right] using hlt
      eq_left := heq_left
      eq_right := heq_right
      no_interior_intersection := by
        intro x hx_left hx_right heq
        have hx_left' : z₁ < (x : ℝ) := by
          simpa [left] using hx_left
        have hx_right' : (x : ℝ) < z₂ := by
          simpa [right] using hx_right
        have hzero : h (x : ℝ) = 0 := by
          rw [heval x, heq, sub_self]
        exact hbetween (x : ℝ) hx_left' hx_right' hzero }
  exact ⟨L, rfl, rfl, rfl, rfl⟩

lemma graphLens_of_negative_between
    {f g : C2Function} (hne : f ≠ g)
    {h : ℝ → ℝ}
    (heval : ∀ x : UnitPoint, h (x : ℝ) = f x - g x)
    {z₁ z₂ : ℝ}
    (hz₁ : z₁ ∈ Icc (0 : ℝ) 1)
    (hz₂ : z₂ ∈ Icc (0 : ℝ) 1)
    (hlt : z₁ < z₂)
    (hzero₁ : h z₁ = 0)
    (hzero₂ : h z₂ = 0)
    (hbetween :
      ∀ x : ℝ, z₁ < x → x < z₂ → h x < 0) :
    ∃ L : GraphLens,
      L.f = f ∧
      L.g = g ∧
      (L.left : ℝ) = z₁ ∧
      (L.right : ℝ) = z₂ := by
  apply graphLens_of_two_localized_zeros hne heval
    hz₁ hz₂ hlt hzero₁ hzero₂
  intro x hx₁ hx₂ hzero
  have hneg := hbetween x hx₁ hx₂
  linarith

lemma graphLens_of_positive_between
    {f g : C2Function} (hne : f ≠ g)
    {h : ℝ → ℝ}
    (heval : ∀ x : UnitPoint, h (x : ℝ) = f x - g x)
    {z₁ z₂ : ℝ}
    (hz₁ : z₁ ∈ Icc (0 : ℝ) 1)
    (hz₂ : z₂ ∈ Icc (0 : ℝ) 1)
    (hlt : z₁ < z₂)
    (hzero₁ : h z₁ = 0)
    (hzero₂ : h z₂ = 0)
    (hbetween :
      ∀ x : ℝ, z₁ < x → x < z₂ → 0 < h x) :
    ∃ L : GraphLens,
      L.f = f ∧
      L.g = g ∧
      (L.left : ℝ) = z₁ ∧
      (L.right : ℝ) = z₂ := by
  apply graphLens_of_two_localized_zeros hne heval
    hz₁ hz₂ hlt hzero₁ hzero₂
  intro x hx₁ hx₂ hzero
  have hpos := hbetween x hx₁ hx₂
  linarith

end Kakeya.Cinematic
