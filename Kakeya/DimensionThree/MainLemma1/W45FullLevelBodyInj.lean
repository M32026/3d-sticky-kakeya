/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.W44FullNodeTransport

/-!
# Exact terminal-card transport for body-injective source families

The WZ middle consumer itself does not require essential distinctness.  For a source family whose
convex bodies are injectively indexed, terminal hierarchy assignment is injective because each
source body equals its assigned terminal-node body.  Thus the terminal node count is exactly the
source count, which is the only transport needed to consume a full-level canonical Q-band.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody

namespace Kakeya.ml1Boot.W45FullLevelBodyInj

noncomputable section

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem terminal_assign_injOn_of_body_injOn
    {iota : Type*} {delta C : NNReal} {s : Finset iota}
    (V : iota -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hbody : Set.InjOn (fun i => (V i).toConvexSpaceBody) (s : Set iota)) :
    Set.InjOn (U.cover.assign N) (s : Set iota) := by
  intro i hi i' hi' hass
  apply hbody hi hi'
  calc
    (V i).toConvexSpaceBody =
        (W44FullNode.fullNodeFamily V hN U (U.cover.assign N i)).toConvexSpaceBody :=
      W44FullNode.leaf_body_eq_assigned_fullNode V hN U hi
    _ = (W44FullNode.fullNodeFamily V hN U (U.cover.assign N i')).toConvexSpaceBody := by
      rw [hass]
    _ = (V i').toConvexSpaceBody :=
      (W44FullNode.leaf_body_eq_assigned_fullNode V hN U hi').symm

theorem terminal_index_card_eq_of_body_injOn
    {iota : Type*} {delta C : NNReal} {s : Finset iota}
    (V : iota -> ShadedTube delta E) {N : Nat} (hN : 0 < N)
    (U : _root_.Tube.UniformTubeSet s (fun i => (V i).toTube) N C)
    (hs : s.Nonempty)
    (hbody : Set.InjOn (fun i => (V i).toConvexSpaceBody) (s : Set iota)) :
    (U.cover.indexSet N).card = s.card := by
  classical
  symm
  apply Finset.card_bij (fun i _ => U.cover.assign N i)
  · exact fun i hi => U.cover.assign_mem N le_rfl i hi
  · intro i hi i' hi' hass
    exact terminal_assign_injOn_of_body_injOn V hN U hbody hi hi' hass
  · intro j hj
    obtain ⟨i, hiClass⟩ :=
      _root_.Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent U le_rfl hs hj
    have hi : i ∈ s ∧ U.cover.assign N i = j := by
      simpa [_root_.Tube.coverClass] using Finset.mem_filter.mp hiClass
    exact ⟨i, hi.1, hi.2⟩

#print axioms terminal_assign_injOn_of_body_injOn
#print axioms terminal_index_card_eq_of_body_injOn

end

end Kakeya.ml1Boot.W45FullLevelBodyInj
