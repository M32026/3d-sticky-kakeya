/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Functional ancestor chains

`Kakeya.chainFun` walks a chain of node families downward through a *functional* projection, so
the caller can name the fibres.  This is the shape the multiscale counting engine of GWZ Lemma 7.4
(`Kakeya.ParentBodyDensity`) consumes; nothing here mentions a tube.
-/

@[expose] public section


open MeasureTheory Real

open scoped ENNReal NNReal

namespace Tube

/-- The scale-`k` ancestor of a leaf `w : κ (Fin.last M)`, obtained by iterating the projection
*function* `proj`.  Unlike `chainOf` this involves no choice, so `chainFun_castSucc` below
identifies each step on the nose. -/
def chainFun {M : ℕ} {κ : Fin (M + 1) → Type*}
    (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc)
    (k : Fin (M + 1)) (w : κ (Fin.last M)) : κ k :=
  Fin.reverseInduction (motive := fun k => κ k) w (fun i a => proj i a) k

@[simp]
theorem chainFun_last {M : ℕ} {κ : Fin (M + 1) → Type*}
    (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc) (w : κ (Fin.last M)) :
    chainFun proj (Fin.last M) w = w := by
  unfold chainFun
  exact Fin.reverseInduction_last (motive := fun k => κ k)

/-- One step of the chain, on the nose: this is the property `chainOf` cannot have. -/
theorem chainFun_castSucc {M : ℕ} {κ : Fin (M + 1) → Type*}
    (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc) (m : Fin M) (w : κ (Fin.last M)) :
    chainFun proj m.castSucc w = proj m (chainFun proj m.succ w) := by
  unfold chainFun
  exact Fin.reverseInduction_castSucc (motive := fun k => κ k) m

/-- The chain stays inside a prescribed family of nodes. -/
theorem chainFun_mem {M : ℕ} {κ : Fin (M + 1) → Type*}
    (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc)
    (P : ∀ k : Fin (M + 1), Set (κ k))
    (hproj_mem : ∀ m : Fin M, ∀ n ∈ P m.succ, proj m n ∈ P m.castSucc)
    (k : Fin (M + 1)) (w : κ (Fin.last M)) (hw : w ∈ P (Fin.last M)) :
    chainFun proj k w ∈ P k := by
  refine Fin.reverseInduction (motive := fun k => chainFun proj k w ∈ P k) ?_ ?_ k
  · rw [chainFun_last]
    exact hw
  · intro i ih
    rw [chainFun_castSucc]
    exact hproj_mem i _ ih

/-- Telescoped monotonicity: a per-step inequality for any `α`-valued observable `f` telescopes
along the chain.  Instantiated at `f k n = (tb k n).toConvexSpaceBody` this is the engine's
`leaf body ≤ ancestor body`. -/
theorem chainFun_le {M : ℕ} {κ : Fin (M + 1) → Type*} {α : Type*} [Preorder α]
    (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc)
    (P : ∀ k : Fin (M + 1), Set (κ k))
    (hproj_mem : ∀ m : Fin M, ∀ n ∈ P m.succ, proj m n ∈ P m.castSucc)
    (f : ∀ k : Fin (M + 1), κ k → α)
    (hstep : ∀ m : Fin M, ∀ n ∈ P m.succ, f m.succ n ≤ f m.castSucc (proj m n))
    (k : Fin (M + 1)) (w : κ (Fin.last M)) (hw : w ∈ P (Fin.last M)) :
    f (Fin.last M) w ≤ f k (chainFun proj k w) := by
  refine Fin.reverseInduction
    (motive := fun k => f (Fin.last M) w ≤ f k (chainFun proj k w)) ?_ ?_ k
  · rw [chainFun_last]
  · intro i ih
    refine ih.trans ?_
    rw [chainFun_castSucc]
    exact hstep i _ (chainFun_mem proj P hproj_mem i.succ w hw)

end Tube
