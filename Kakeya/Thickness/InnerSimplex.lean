/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Topology.Metric
public import Kakeya.Thickness.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Inner simplex

We show the existence of a simplex contained in a given set of comparable size.
This inner simplex underlies the lower volume bound `Convex.ethickness_prod_le_volume`.

## TODOs

* Golf the proof of `exists_simplex_of_lt_ethickness`

-/

@[expose] public section

open Metric

variable
  {E} [NormedAddCommGroup E] [Module ℝ E]

/- Helper: Fin.snoc image of Iic -/
private lemma snoc_image_Iic_castSucc_eq {E : Type*} {m : ℕ} (f : Fin (m + 1) → E) (a : E)
    (j : Fin (m + 1)) : (Fin.snoc f a) '' (Set.Iic (j.castSucc : Fin (m + 2))) =
    f '' (Set.Iic j) := by
  ext
  simp only [Set.mem_image, Set.mem_Iic]
  refine ⟨fun ⟨x, hx1, hx2⟩ ↦ ?_, fun ⟨x, hx1, hx2⟩ ↦ ⟨x.castSucc,
    Fin.castSucc_le_castSucc_iff.2 hx1, by simp [hx2]⟩⟩
  let i : Fin (m + 1) := ⟨x.val, Fin.le_iff_val_le_val.1 hx1 |>.trans_lt <|
    (Fin.val_castSucc j).symm ▸ j.2⟩
  refine ⟨i, Fin.le_iff_val_le_val.2 <| Fin.le_iff_val_le_val.1 hx1, ?_⟩
  rwa [show x = i.castSucc by simp [i], Fin.snoc_castSucc] at hx2

/- Helper: snoc image of Iic (last m).castSucc = range -/
private lemma snoc_image_Iic_last_castSucc_eq_range {E : Type*} {m : ℕ} (f : Fin (m + 1) → E)
    (a : E) : (Fin.snoc f a) '' (Set.Iic ((Fin.last m).castSucc : Fin (m + 2))) =
    Set.range f := by simp [snoc_image_Iic_castSucc_eq, Set.ext_iff, Fin.le_last]

/-- Given lower bounds on `ethickness`, we can find a simplex of correponding size
whore vertices are in the given set. -/
theorem exists_simplex_of_lt_ethickness {n} {s : Set E} (hs : s.Nonempty)
    {r : Fin n → ENNReal} (hr : ∀ i, r i < ethickness ℝ s i) :
    ∃ p : Fin (n + 1) → E, (∀ i, p i ∈ s) ∧
      (∀ i : Fin n, r i < infEDist (p i.succ)
    (affineSpan ℝ (p '' Set.Iic i.castSucc))) := by
  suffices main : ∀ m, (hmn : m ≤ n) →
      ∃ p : Fin (m + 1) → E, (∀ i, p i ∈ s) ∧
        (∀ i : Fin m, r (i.castLE hmn) < Metric.infEDist (p i.succ)
          (affineSpan ℝ (p '' Set.Iic i.castSucc))) by
    exact main n le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨x, hx⟩ := hs
    use fun _ => x
    simpa
  | succ m ih =>
    intro hm_succ
    have hm_lt : m < n := Nat.lt_of_succ_le hm_succ
    obtain ⟨p, hp_mem, hp_dist⟩ := ih hm_lt.le
    let A := affineSpan ℝ (Set.range p)
    have hA_rank : Module.rank ℝ A.direction ≤ m := by
      rw [direction_affineSpan]
      have : Module.Finite ℝ (vectorSpan ℝ (Set.range p)) :=
        inferInstance
      rw [← Module.finrank_eq_rank]
      exact_mod_cast
        finrank_vectorSpan_range_le ℝ p (Fintype.card_fin (m + 1))
    obtain ⟨x, hx_s, hx_not_thick⟩ := exists_not_in_cthickening (hr ⟨m, hm_lt⟩) hA_rank
    set p' : Fin (m + 2) → E := Fin.snoc p x with hp'_def
    have h_range : Set.range p' = insert x (Set.range p) := by
      simp [p', Fin.range_snoc]
    refine ⟨p', ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [p', Fin.snoc_last]; exact hx_s
      · intro j
        simp only [p', Fin.snoc_castSucc]; exact hp_mem j
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · have h1 : p' (Fin.last m).succ = x := by
          simp only [p']
          have : (Fin.last m : Fin (m + 1)).succ =
              Fin.last (m + 1) := by
            ext; simp [Fin.last]
          rw [this, Fin.snoc_last]
        rw [h1, snoc_image_Iic_last_castSucc_eq_range p x]
        apply lt_infEDist_of_not_mem_cthickening (ne_top_of_lt <| hr _) hx_not_thick
      · intro j
        have h1 : p' (j.castSucc : Fin (m + 1)).succ = p j.succ := by
          simp only [p']
          have : ((j.castSucc : Fin (m + 1)).succ :
              Fin (m + 2)) =
              (j.succ : Fin (m + 1)).castSucc := by
            ext; simp [Fin.succ, Fin.castSucc]
          rw [this, Fin.snoc_castSucc]
        rw [h1, snoc_image_Iic_castSucc_eq p x j.castSucc]
        exact hp_dist j
