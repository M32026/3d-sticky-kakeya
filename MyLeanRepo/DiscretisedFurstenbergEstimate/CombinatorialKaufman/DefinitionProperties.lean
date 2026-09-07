module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Properties of the core definitions for the Combinatorial Kaufman Decomposition

This module proves basic properties of `chordSlope`, `chordValue`,
`EpsilonLinear`, and `EpsilonSuperlinear`.

## Main results
- `EpsilonLinear.impSuperlinear`: `EpsilonLinear` implies `EpsilonSuperlinear`
- `chordValue_left`: `chordValue f a b a = f a`
- `chordValue_right`: `chordValue f a b b = f b` (when `a ≠ b`)
- `chordSlope_le_two`: chord slope ≤ 2 for 2-Lipschitz functions
- `chordSlope_nonneg`: chord slope ≥ 0 for monotone functions
- `chordSlope_convex`: chord slope over [a,b] is a weighted average of slopes over [a,x] and [x,b]
-/

noncomputable section

open Real Set

/-- `EpsilonLinear` implies `EpsilonSuperlinear` with the same parameters. -/
lemma EpsilonLinear.impSuperlinear {f : ℝ → ℝ} {ε a b : ℝ}
    (h : EpsilonLinear f ε a b) : EpsilonSuperlinear f ε a b := by
  intro x hx
  have h1 : |f x - chordValue f a b x| ≤ ε * (b - a) := h x hx
  have h2 : -(ε * (b - a)) ≤ f x - chordValue f a b x := by
    linarith [abs_le.mp h1]
  linarith

/-- The chord value at the left endpoint equals `f a`. -/
lemma chordValue_left (f : ℝ → ℝ) (a b : ℝ) :
    chordValue f a b a = f a := by
  simp [chordValue, sub_self]

/-- The chord value at the right endpoint equals `f b` when `a ≠ b`. -/
lemma chordValue_right (f : ℝ → ℝ) (a b : ℝ) (hne : a ≠ b) :
    chordValue f a b b = f b := by
  have h : b - a ≠ 0 := by
    intro h'
    apply hne
    linarith
  have h_main : chordValue f a b b = f a + chordSlope f a b * (b - a) := by
    simp [chordValue]
    <;> ring
  rw [h_main]
  have h2 : chordSlope f a b * (b - a) = f b - f a := by
    dsimp only [chordSlope]
    field_simp [h] <;> ring
  rw [h2] <;> ring

/-- The chord slope is nonnegative when `f` is monotone on `[a,b]` and `a < b`. -/
lemma chordSlope_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hmon : MonotoneOn f (Set.Icc a b)) :
    0 ≤ chordSlope f a b := by
  have ha : a ∈ Set.Icc a b := by exact ⟨by linarith, by linarith⟩
  have hb : b ∈ Set.Icc a b := by exact ⟨by linarith, by linarith⟩
  have h1 : f a ≤ f b := hmon ha hb (by linarith)
  have h2 : 0 < b - a := by linarith
  dsimp only [chordSlope]
  exact div_nonneg (by linarith) (by linarith)

/-- The chord slope is at most 2 when `f` is 2-Lipschitz on `[a,b]` and `a < b`. -/
lemma chordSlope_le_two {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hlip : LipschitzOnWith 2 f (Set.Icc a b)) :
    chordSlope f a b ≤ 2 := by
  have ha : a ∈ Set.Icc a b := by exact ⟨by linarith, by linarith⟩
  have hb : b ∈ Set.Icc a b := by exact ⟨by linarith, by linarith⟩
  have h_dist : dist (f b) (f a) ≤ (2 : ℝ) * dist b a :=
    (lipschitzOnWith_iff_dist_le_mul.mp hlip) b hb a ha
  have h1 : |f b - f a| ≤ 2 * |b - a| := by
    simpa [Real.dist_eq] using h_dist
  have h2 : 0 < b - a := by linarith
  have h3 : |b - a| = b - a := by
    rw [abs_of_pos] <;> linarith
  have h4 : f b - f a ≤ 2 * (b - a) := by
    linarith [abs_le.mp h1]
  dsimp only [chordSlope]
  have h5 : (f b - f a) / (b - a) ≤ 2 := by
    calc
      (f b - f a) / (b - a) ≤ (2 * (b - a)) / (b - a) := by gcongr
      _ = 2 := by
        field_simp [h2.ne'] <;> ring
  exact h5

/-- The chord slope over `[a,b]` is a weighted average of the chord slopes
over `[a,x]` and `[x,b]`. -/
lemma chordSlope_convex {f : ℝ → ℝ} {a x b : ℝ} (hax : a < x) (hxb : x < b) :
    chordSlope f a b =
      ((x - a) / (b - a)) * chordSlope f a x +
      ((b - x) / (b - a)) * chordSlope f x b := by
  have h1 : a ≠ x := by linarith
  have h2 : x ≠ b := by linarith
  have h3 : a ≠ b := by linarith
  have h4 : b - a > 0 := by linarith
  have h5 : x - a > 0 := by linarith
  have h6 : b - x > 0 := by linarith
  dsimp only [chordSlope]
  field_simp [h4.ne', h5.ne', h6.ne']
  <;> ring

/-- A version of slope convexity expressed without division:
`(b - a) * chordSlope f a b = (x - a) * chordSlope f a x + (b - x) * chordSlope f x b`. -/
lemma chordSlope_convex' {f : ℝ → ℝ} {a x b : ℝ} (hax : a < x) (hxb : x < b) :
    (b - a) * chordSlope f a b =
      (x - a) * chordSlope f a x + (b - x) * chordSlope f x b := by
  have h4 : b - a > 0 := by linarith
  have h5 : x - a > 0 := by linarith
  have h6 : b - x > 0 := by linarith
  dsimp only [chordSlope]
  field_simp [h4.ne', h5.ne', h6.ne'] <;> ring

/-- If `f` is 2-Lipschitz and monotone on `[a,b]` with `a < b`, then
`0 ≤ chordSlope f a b ≤ 2`. -/
lemma chordSlope_bounds {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hlip : LipschitzOnWith 2 f (Set.Icc a b))
    (hmon : MonotoneOn f (Set.Icc a b)) :
    0 ≤ chordSlope f a b ∧ chordSlope f a b ≤ 2 :=
  ⟨chordSlope_nonneg hab hmon, chordSlope_le_two hab hlip⟩

end
