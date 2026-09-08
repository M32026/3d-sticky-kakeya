/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
import Kakeya.DimensionThree.Plank.ThickenedGeometry
public import Mathlib.Data.Finset.Pairwise

/-!

# Thickened-plank representatives

Construction of a maximal pairwise essentially-distinct family of standard thickened planks and
assignment of every plank to a comparable active representative.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- A coarse pairwise essentially-distinct ensemble of typed thickened representatives exists with
one uniform comparability constant. -/
theorem exists_thickenedRepr :
    ∃ cThk : ℝ≥0, 1 ≤ cThk ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1),
        0 < a → a / b ≤ θ → Nonempty (ThickenedRepr s V θ hθ1 cThk) := by
  obtain ⟨Ceq, hCeq, hEq⟩ := equalScaleThickening_twoSidedDilation
  refine ⟨Ceq, hCeq, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 ha hθa
  have hb : 0 < b := ha.trans_le hab
  have hθ : 0 < θ := (div_pos ha hb).trans_le hθa
  have haθb : a ≤ θ * b := (div_le_iff₀ hb).mp hθa
  classical
  let Tp : ι → ThickenedPlank θ b hθ1 hb1 := fun i ↦ (V i).thickened θ hθ1
  let T : ι → EnsemblePrism := fun i ↦ (Tp i).toPrismNDim
  let Rel : ι → ι → Prop := fun i j ↦ PrismNDim.IsEssentiallyDistinct (T i) (T j)
  let good : Finset (Finset ι) := s.powerset.filter fun M ↦ (M : Set ι).Pairwise Rel
  have hmem : ∀ N : Finset ι, N ∈ good ↔ N ⊆ s ∧ (N : Set ι).Pairwise Rel := fun _ ↦
    Finset.mem_filter.trans (and_congr_left' Finset.mem_powerset)
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image good Finset.card
    ⟨∅, (hmem ∅).2 ⟨Finset.empty_subset s, Finset.coe_empty ▸ Set.pairwise_empty Rel⟩⟩
  obtain ⟨hMs, hMED⟩ := (hmem M).1 hM
  have hcover : ∀ i ∈ s, ∃ m ∈ M, ¬ Rel i m := by
    intro i hi
    by_cases hiM : i ∈ M
    · exact ⟨i, hiM, not_isEssentiallyDistinct_thickened_self (V i) hθ1 hθ hb⟩
    have hpair : ¬ (insert i (M : Set ι)).Pairwise Rel := fun hp ↦ by
      have hle := hmax (insert i M) <| (hmem _).2
        ⟨Finset.insert_subset hi hMs, Finset.coe_insert i M ▸ hp⟩
      rw [Finset.card_insert_of_notMem hiM] at hle
      exact Nat.not_succ_le_self _ hle
    rw [Set.pairwise_insert] at hpair
    push Not at hpair
    obtain ⟨m, hm, -, hbad⟩ := hpair hMED
    exact ⟨m, hm, fun hmi ↦ hbad hmi (PrismNDim.IsEssentiallyDistinct.symm hmi)⟩
  choose! sel hselM hnd using hcover
  have key := fun i (hi : i ∈ s) ↦
    mul_one Ceq ▸ hEq hθ1 hθ hb (V i) (V (sel i)) (hnd i hi) 1 le_rfl
  exact ⟨{
    sel := sel
    repr := fun i ↦ Tp (sel i)
    repr_eq := fun _ _ ↦ rfl
    notEssentiallyDistinct_repr := hnd
    subset_repr := fun i hi ↦ ((subset_thickened (V i) haθb hθ1).trans
      ((T i).self_subset_dilation le_rfl)).trans (key i hi).2
    repr_subset_thickened := fun i hi ↦
      ((T (sel i)).self_subset_dilation le_rfl).trans (key i hi).1
    pairwise_repr := fun i hi j hj hij ↦
      hMED (hselM i hi) (hselM j hj) fun h ↦ hij (congrArg Tp h) }⟩

end Plank

end

end
