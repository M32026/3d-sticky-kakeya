/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalCriticalImage

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

noncomputable section

/-- Given `i : Fin (m + 1)` and `j : Fin (m + 1)` with `j ≠ i`, map `j` to `Fin m`. -/
def fin_remove {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 1)) (h : j ≠ i) : Fin m :=
  Classical.choose (Fin.exists_succAbove_eq h)

lemma succAbove_fin_remove {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 1)) (h : j ≠ i) :
    Fin.succAbove i (fin_remove i j h) = j :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

lemma fin_remove_succAbove {m : ℕ} (i : Fin (m + 1)) (k : Fin m) :
    fin_remove i (Fin.succAbove i k) (Fin.succAbove_ne i k) = k := by
  apply Fin.succAbove_right_injective
  rw [succAbove_fin_remove]

/-- Given `i : Fin (m + 1)`, projection from `Fin (m + 1) → ℝ` to `Fin m → ℝ` that drops coordinate `i`. -/
def pi_drop_coord {m : ℕ} (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun k : Fin m => x (Fin.succAbove i k)

/-- Given `i : Fin (m + 1)`, inclusion from `Fin m → ℝ` to `Fin (m + 1) → ℝ` that inserts 0 at coordinate `i`. -/
def pi_insert_zero {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  fun j : Fin (m + 1) => if h : j = i then 0 else y (fin_remove i j h)

lemma pi_insert_zero_drop_coord {m : ℕ} (i : Fin (m + 1))
    (x : Fin (m + 1) → ℝ) (hx : x i = 0) :
    pi_insert_zero i (pi_drop_coord i x) = x := by
  funext j
  by_cases h : j = i
  · rw [h]
    simp [pi_insert_zero, hx]
  · have h2 : pi_insert_zero i (pi_drop_coord i x) j = (pi_drop_coord i x) (fin_remove i j h) := by
      simp [pi_insert_zero, h]
    rw [h2]
    have h3 : (pi_drop_coord i x) (fin_remove i j h) = x (Fin.succAbove i (fin_remove i j h)) := by
      rfl
    rw [h3, succAbove_fin_remove i j h]

lemma pi_drop_coord_insert_zero {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) :
    pi_drop_coord i (pi_insert_zero i y) = y := by
  funext k
  have h_ne : (Fin.succAbove i k) ≠ i := Fin.succAbove_ne i k
  have h1 : pi_drop_coord i (pi_insert_zero i y) k = (pi_insert_zero i y) (Fin.succAbove i k) := by rfl
  rw [h1]
  have h2 : (pi_insert_zero i y) (Fin.succAbove i k) = y (fin_remove i (Fin.succAbove i k) h_ne) := by
    simp [pi_insert_zero, h_ne]
  rw [h2, fin_remove_succAbove i k]

/-- `pi_drop_coord` is a linear map. -/
def pi_drop_coord_linear {m : ℕ} (i : Fin (m + 1)) :
    ((Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :=
  { toFun := pi_drop_coord i
    map_add' := by
      intro x y
      funext k
      simp [pi_drop_coord]
    map_smul' := by
      intro c x
      funext k
      simp [pi_drop_coord]
      }

/-- `pi_insert_zero` is a linear map. -/
def pi_insert_zero_linear {m : ℕ} (i : Fin (m + 1)) :
    ((Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) :=
  { toFun := pi_insert_zero i
    map_add' := by
      intro y1 y2
      funext j
      simp [pi_insert_zero]
      split_ifs <;> simp
    map_smul' := by
      intro c y
      funext j
      simp [pi_insert_zero] }

/-- `pi_drop_coord` is continuous. -/
lemma pi_drop_coord_continuous {m : ℕ} (i : Fin (m + 1)) :
    Continuous (pi_drop_coord i) :=
  (pi_drop_coord_linear i).continuous_of_finiteDimensional

/-- `pi_insert_zero` is continuous. -/
lemma pi_insert_zero_continuous {m : ℕ} (i : Fin (m + 1)) :
    Continuous (pi_insert_zero i) :=
  (pi_insert_zero_linear i).continuous_of_finiteDimensional

/-- `pi_drop_coord` is `ContDiff ℝ ∞`. -/
lemma pi_drop_coord_contDiff {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (pi_drop_coord i) :=
  let clm : ((Fin (m + 1) → ℝ) →L[ℝ] (Fin m → ℝ)) :=
    ⟨pi_drop_coord_linear i, pi_drop_coord_continuous i⟩
  clm.contDiff

/-- `pi_insert_zero` is `ContDiff ℝ ∞`. -/
lemma pi_insert_zero_contDiff {m : ℕ} (i : Fin (m + 1)) :
    ContDiff ℝ ∞ (pi_insert_zero i) :=
  let clm : ((Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)) :=
    ⟨pi_insert_zero_linear i, pi_insert_zero_continuous i⟩
  clm.contDiff

end


end ForMathlib.Analysis.Calculus.Sard
