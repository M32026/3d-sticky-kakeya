/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.WZCanonicalClasses

/-!
# Global scale crossing for the WZ rho selection

The crossing is stated without division.  The finite selection lemmas choose one global hierarchy
level and distinguish a crossing at the first-failure level from a strictly coarser crossing whose
immediately finer predecessor fails.
-/

@[expose] public section

namespace Kakeya.WangZahl

noncomputable section

open Tube

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Cross-multiplied form of `tauCard / rhoCard >= theta * (rho / tau)^2`. -/
def GlobalCrossing (theta tau rho tauCard rhoCard : NNReal) : Prop :=
  theta * rho ^ 2 * rhoCard <= tau ^ 2 * tauCard

/-- The WZ global crossing at hierarchy level `a`, using one fixed retained tau-node family. -/
def hierarchyGlobalCrossing {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (b : Nat) (tauNodes : Finset ι)
    (theta : NNReal) (a : Nat) : Prop :=
  GlobalCrossing theta (_root_.Tube.gridScale delta N b) (_root_.Tube.gridScale delta N a)
    tauNodes.card (activeRhoParents U b a tauNodes).card

/-- An absolute tau-cardinality lower bound supplies the crossing at the top grid scale. -/
theorem hierarchyGlobalCrossing_zero_of_cardLower
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C theta : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {b : Nat} (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hcardLower : theta * C <= (_root_.Tube.gridScale delta N b) ^ 2 * tauNodes.card) :
    hierarchyGlobalCrossing U b tauNodes theta 0 := by
  have hactive : activeRhoParents U b 0 tauNodes ⊆ U.cover.indexSet 0 :=
    activeRhoParents_subset_indexSet U hs (Nat.zero_le N) hb htau
  have hactiveCard :
      ((activeRhoParents U b 0 tauNodes).card : NNReal) <= C := by
    calc
      ((activeRhoParents U b 0 tauNodes).card : NNReal) <=
          ((U.cover.indexSet 0).card : NNReal) := by
        exact_mod_cast Finset.card_le_card hactive
      _ <= C := _root_.Kakeya.MultiScaleFac.card_parent_zero_le U hs hball
  unfold hierarchyGlobalCrossing GlobalCrossing
  simp only [_root_.Tube.gridScale_zero, one_pow, mul_one]
  exact (mul_le_mul_right hactiveCard theta).trans hcardLower

/-- A finite interval with at least one crossing has a last crossing. -/
theorem exists_lastCrossing {Crosses : Nat -> Prop} {sigma : Nat}
    (hex : ∃ a, a <= sigma ∧ Crosses a) :
    ∃ a, a <= sigma ∧ Crosses a ∧ ∀ j, a < j -> j <= sigma -> ¬ Crosses j := by
  classical
  let candidates := (Finset.range (sigma + 1)).filter Crosses
  have hcandidates : candidates.Nonempty := by
    obtain ⟨a, ha, hcross⟩ := hex
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ha), hcross⟩⟩
  let a := candidates.max' hcandidates
  have ha_mem : a ∈ candidates := Finset.max'_mem candidates hcandidates
  have ha_data := Finset.mem_filter.mp ha_mem
  refine ⟨a, Nat.le_of_lt_succ (Finset.mem_range.mp ha_data.1), ha_data.2, ?_⟩
  intro j haj hj hcross
  have hj_mem : j ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj), hcross⟩
  exact (not_le_of_gt haj) (Finset.le_max' candidates j hj_mem)

/-- The last crossing is direct at `sigma`, or its immediately finer predecessor fails. -/
theorem exists_lastCrossing_direct_or_succ_failure
    {Crosses : Nat -> Prop} {sigma : Nat}
    (hex : ∃ a, a <= sigma ∧ Crosses a) :
    ∃ a, a <= sigma ∧ Crosses a ∧
      (a = sigma ∨ (a < sigma ∧ ¬ Crosses (a + 1))) := by
  obtain ⟨a, ha, hcross, hlast⟩ := exists_lastCrossing hex
  refine ⟨a, ha, hcross, ?_⟩
  rcases ha.eq_or_lt with rfl | ha_lt
  · exact Or.inl rfl
  · exact Or.inr ⟨ha_lt, hlast (a + 1) (Nat.lt_succ_self a) ha_lt⟩

/-- Select the last global hierarchy crossing at or below the first-failure index. -/
theorem exists_hierarchyGlobalCrossing_direct_or_succ_failure
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) {b sigma : Nat} (tauNodes : Finset ι)
    (theta : NNReal)
    (hex : ∃ a, a <= sigma ∧ hierarchyGlobalCrossing U b tauNodes theta a) :
    ∃ a, a <= sigma ∧ hierarchyGlobalCrossing U b tauNodes theta a ∧
      (a = sigma ∨
        (a < sigma ∧ ¬ hierarchyGlobalCrossing U b tauNodes theta (a + 1))) :=
  exists_lastCrossing_direct_or_succ_failure hex

/-- Select rho once the producer supplies the absolute tau-cardinality lower bound. -/
theorem exists_hierarchyGlobalCrossing_of_cardLower
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C theta : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {b sigma : Nat} (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hcardLower : theta * C <= (_root_.Tube.gridScale delta N b) ^ 2 * tauNodes.card) :
    ∃ a, a <= sigma ∧ hierarchyGlobalCrossing U b tauNodes theta a ∧
      (a = sigma ∨
        (a < sigma ∧ ¬ hierarchyGlobalCrossing U b tauNodes theta (a + 1))) :=
  exists_hierarchyGlobalCrossing_direct_or_succ_failure U tauNodes theta
    ⟨0, Nat.zero_le sigma,
      hierarchyGlobalCrossing_zero_of_cardLower U hs hball hb htau hcardLower⟩

end

end Kakeya.WangZahl
