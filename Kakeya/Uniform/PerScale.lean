/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.IsUniformAtScale
public import Kakeya.Shading

/-!
# The per-scale reading of GWZ Definitions 2.1 and 2.2

Additional estimates, which states parts of Section 6
against the per-scale reading of uniformity rather than against the multiscale hierarchy
`Tube.UniformTubeSet` used in `Kakeya/Uniform.lean` and `Kakeya/ShadedUniform.lean`.

Only the two *definitions* are ported.

Consequently `Kakeya.ShadedTube.IsUniform` has, in this development, no producer: every statement
below that quotes it quotes it as a *hypothesis*.
-/

@[expose] public section

open MeasureTheory

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasureSpace E] {ι : Type*} {δ : NNReal}

/-- **GWZ Definition 2.1, read scale by scale.**  `T` is a `C`-uniform family of `δ`-tubes over
`scales` when at every scale in `scales` the family is uniform at that scale. -/
def IsUniform (s : Finset ι) (T : ι → Tube δ E) (scales : Set NNReal) (C : NNReal) : Prop :=
  ∀ ρ ∈ scales, Nonempty (IsUniformAtScale s T ρ C)

end Tube

namespace ShadedTube

open Classical in
/-- **GWZ Definition 2.2, read scale by scale.**  A shaded family `(T, Y)` is `C`-uniform on
`scales`: the underlying tubes are uniform, and a single per-scale branching count is comparable,
up to `C`, to the branching count of the fibre of every point of the shading. -/
structure IsUniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [MeasureSpace E] {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → ShadedTube δ E)
    (scales : Set NNReal) (C : NNReal) where
  /-- The underlying tube family is uniform (Definition 2.2, first bullet). -/
  tubeUniform : Tube.IsUniform s (fun i => (T i).toTube) scales C
  /-- A single per-scale branching function, shared across all points of the shading. -/
  branchingN : ∀ ρ ∈ scales, NNReal
  /-- At each point `x` of the shading and each scale `ρ`, the fibre of `x` is uniform at `ρ`. -/
  localUniform : ∀ x ∈ (⋃ i ∈ s, (T i).shade), ∀ ρ ∈ scales,
    Tube.IsUniformAtScale {i ∈ s | x ∈ (T i).shade} (fun i => (T i).toTube) ρ C
  /-- The shared count is at most a factor `C` above each local branching number. -/
  branchingN_le : ∀ x (hx : x ∈ (⋃ i ∈ s, (T i).shade)) ρ (hρ : ρ ∈ scales),
    branchingN ρ hρ ≤ C * (localUniform x hx ρ hρ).branchingN
  /-- Each local branching number is at most a factor `C` above the shared count. -/
  le_branchingN : ∀ x (hx : x ∈ (⋃ i ∈ s, (T i).shade)) ρ (hρ : ρ ∈ scales),
    (localUniform x hx ρ hρ).branchingN ≤ C * branchingN ρ hρ

end ShadedTube

end
