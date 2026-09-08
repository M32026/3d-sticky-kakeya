import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedCopies

/-!
# Multiscale composed translation shifts

Given `M` scales with radii `ρ_k` and copy counts `J_k`, construct a total
shift function indexed by `Fin (∏ J_k)` where each total shift is the sum
of per-scale independent shifts:

    shift(j₀, ..., j_{M-1}) = v₀(j₀) + ... + v_{M-1}(j_{M-1})

This is the data structure for the multi-scale random translation proof
(GWZ Section 7, Lemma `lemmasubsticky`).

## Main definitions

- `multiscaleTotalJ J = ∏ k, J k`
- `multiscaleTotalRadius ρ = ∑ k, ρ k`
- `multiscaleShiftFun v`: the composed shift function
- `multiscaleShiftFun_norm_le`: norm bound on composed shifts
-/

namespace Kakeya.Streamlined.RandomTranslation

open BigOperators

/-- Total number of composed shifts across `M` scales. -/
def multiscaleTotalJ {M : ℕ} (J : Fin M → ℕ) : ℕ :=
  ∏ k : Fin M, J k

/-- Sum of all scale radii. -/
def multiscaleTotalRadius {M : ℕ} (ρ : Fin M → ℝ) : ℝ :=
  ∑ k : Fin M, ρ k

/-- Composed shift function: given per-scale shift functions `v k`,
produce a total shift for each tuple of per-scale indices.

Uses `finPiFinEquiv` to identify `Fin (∏ J k)` with `(k : Fin M) → Fin (J k)`.
-/
def multiscaleShiftFun {M : ℕ} {J : Fin M → ℕ}
    (v : (k : Fin M) → (Fin (J k) → Point3)) :
    Fin (multiscaleTotalJ J) → Point3 :=
  fun i =>
    let choices : (k : Fin M) → Fin (J k) := finPiFinEquiv.symm i
    ∑ k : Fin M, v k (choices k)

/-- Norm bound on composed shifts: the total shift norm is at most the
sum of per-scale radius bounds. -/
lemma multiscaleShiftFun_norm_le {M : ℕ} {ρ : Fin M → ℝ} {J : Fin M → ℕ}
    (v : (k : Fin M) → (Fin (J k) → Point3))
    (h_norm : ∀ k j, ‖v k j‖ ≤ ρ k) :
    ∀ i : Fin (multiscaleTotalJ J),
      ‖multiscaleShiftFun v i‖ ≤ multiscaleTotalRadius ρ := by
  intro i
  let choices : (k : Fin M) → Fin (J k) := finPiFinEquiv.symm i
  have h1 : ‖∑ k : Fin M, v k (choices k)‖ ≤ ∑ k : Fin M, ‖v k (choices k)‖ :=
    norm_sum_le Finset.univ (fun k => v k (choices k))
  have h2 : ∑ k : Fin M, ‖v k (choices k)‖ ≤ ∑ k : Fin M, ρ k := by
    apply Finset.sum_le_sum
    intro k _
    exact h_norm k (choices k)
  simpa [multiscaleShiftFun, multiscaleTotalRadius] using le_trans h1 h2

/-- Apply multiscale composed shifts to a tube family, producing
`translatedCopies` with the total number of copies. -/
def multiscaleTranslatedCopies {δ : ℝ} (F : TubeFamily δ)
    {M : ℕ} {J : Fin M → ℕ}
    (v : (k : Fin M) → (Fin (J k) → Point3)) :
    TubeFamily δ :=
  translatedCopies F (multiscaleTotalJ J) (multiscaleShiftFun v)

/-- If the total radius is at most 9, every translated copy of a unit-ball
family lies in the radius-10 ball. -/
lemma multiscaleTranslatedCopies_in_ball_ten
    {δ : ℝ} {F : TubeFamily δ}
    (hF_unit : TubeFamily.IsInUnitBall F)
    {M : ℕ} {ρ : Fin M → ℝ} {J : Fin M → ℕ}
    (v : (k : Fin M) → (Fin (J k) → Point3))
    (h_total_radius : multiscaleTotalRadius ρ ≤ 9)
    (h_norm : ∀ k j, ‖v k j‖ ≤ ρ k) :
    ∀ i, ((multiscaleTranslatedCopies F v).tube i).carrier ⊆
        Metric.closedBall (0 : Point3) 10 := by
  have h_shift_le_nine : ∀ j : Fin (multiscaleTotalJ J),
      ‖multiscaleShiftFun v j‖ ≤ 9 := by
    intro j
    have h : ‖multiscaleShiftFun v j‖ ≤ multiscaleTotalRadius ρ :=
      multiscaleShiftFun_norm_le v h_norm j
    exact le_trans h h_total_radius
  exact translatedCopies_in_ball_ten hF_unit h_shift_le_nine

end Kakeya.Streamlined.RandomTranslation
