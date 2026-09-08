/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Linarith

/-!
# Abstract bootstrap on a half-open interval

`Kakeya.ioc_subset_of_sub_mem_of_monotoneOn` turns a self-improving step into a statement on
a whole half-open interval: a set that is up-closed, contains the right endpoint, and is
closed under a strictly positive monotone downward step contains the entire interval.

Both bootstraps of the development use it: Main Lemma 1 with left endpoint `β`
(`Kakeya.KatzTaoEstimate.frostmanEstimate`) and the outer Katz-Tao bootstrap with left
endpoint `0` (`Kakeya.katzTaoEstimateDimensionThree`).
-/

@[expose] public section

namespace Kakeya

/-- Abstract bootstrap on `(β, 1]`. If `s ⊆ ℝ` is up-closed, contains `1`, and is
closed under `γ ↦ γ - f γ` on `Set.Ioc β 1` for an `f` that is monotone and strictly
positive on `Set.Ioc β 1`, then `s` contains all of `Set.Ioc β 1`.

The argument is the infimum argument: if `γ₀ ∈ Set.Ioc β 1` were missing from `s`, the
infimum `α` of `s ∩ Set.Icc γ₀ 1` would admit an element `γ` of that set with
`γ < α + f α`, and then `γ - f γ < α` would either land below `γ₀` (giving `γ₀ ∈ s` by
up-closedness) or contradict the definition of `α`. -/
lemma ioc_subset_of_sub_mem_of_monotoneOn {β : ℝ} {s : Set ℝ} {f : ℝ → ℝ}
    (h1 : ∀ γ γ', γ ≤ γ' → γ ∈ s → γ' ∈ s)
    (h2 : 1 ∈ s) (h3 : ∀ γ ∈ Set.Ioc β 1, γ ∈ s → γ - f γ ∈ s)
    (h4 : MonotoneOn f (Set.Ioc β 1))
    (h5 : ∀ γ ∈ Set.Ioc β 1, f γ > 0) : Set.Ioc β 1 ⊆ s := by
  intro γ₀ hγ₀
  set S : Set ℝ := s ∩ Set.Icc γ₀ 1
  have hS_bdd : BddBelow S := ⟨γ₀, fun _ h => h.2.1⟩
  have hS_one : (1:ℝ) ∈ S := ⟨h2, hγ₀.2, le_rfl⟩
  have hS_ne : S.Nonempty := ⟨1, hS_one⟩
  set α : ℝ := sInf S
  have hα_le : α ≤ 1 := csInf_le hS_bdd hS_one
  have hα_Ioc : α ∈ Set.Ioc β 1 :=
    ⟨hγ₀.1.trans_le (le_csInf hS_ne fun _ h => h.2.1), hα_le⟩
  obtain ⟨γ, hγ_S, hγ_lt⟩ : ∃ γ ∈ S, γ < α + f α :=
    exists_lt_of_csInf_lt hS_ne (lt_add_of_pos_right α (h5 _ hα_Ioc))
  have hγ_Ioc : γ ∈ Set.Ioc β 1 := ⟨hγ₀.1.trans_le hγ_S.2.1, hγ_S.2.2⟩
  have hsub_s : γ - f γ ∈ s := h3 γ hγ_Ioc hγ_S.1
  have hsub_lt : γ - f γ < α := sub_lt_iff_lt_add.mpr
    (hγ_lt.trans_le (add_le_add_right (h4 hα_Ioc hγ_Ioc (csInf_le hS_bdd hγ_S)) α))
  refine h1 _ _ (le_of_not_gt fun h => ?_) hsub_s
  exact hsub_lt.not_ge (csInf_le hS_bdd ⟨hsub_s, h.le, hsub_lt.le.trans hα_le⟩)

end Kakeya
