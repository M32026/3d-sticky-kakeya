/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.JointRefinement
public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCountLoose

/-!
# The parent side of conjunct 5: what `LooseRhoParentData` needs, compiled

`Kakeya.VeryNotSticky.LooseRhoParentData δ ζ exscalb η Kpar s T` asks for a parent `sPar ⊇ s`
carrying (i) containment in `B₁` and `Δ_max ≤ δ^{-η}`, (ii) the
retention `δ^{2η} |sPar| ≤ |s|`, (iii) a **loose** Definition-2.1 datum at a constant
`1 ≤ Cpar ≤ δ^{-η}`, and (iv) the essentially-distinct all-used `ρ`-count `ρ^{-2-ζ} ≤ |tρ|` on
`sPar` at every window scale.

Two compiled facts pin the obstruction to a single clause.

* `looseRhoParentData_of_binders` — **the minimal repair**.  If the *given* family `s` (the one
  Lemma 9.1's hypotheses speak about) carries a loose Definition-2.1 datum at `1 ≤ C ≤ δ^{-η}`,
  then every retained subfamily `s' ⊆ s` (`δ^{2η}|s| ≤ |s'|`, tubes unchanged) has
  `LooseRhoParentData` with `sPar := s`, word for word as
  `Kakeya.VeryNotSticky.rhoParentData_of_binders` does it for the exact binder.  The loose datum
  is transported along the tube identity by `Kakeya.JointRefine.retubeLoose`.  So a loose
  uniformity binder on Lemma 9.1's input — the same statement-level move F12a made for the exact
  one — closes the parent side with no new mathematics; the reduction can supply it by
  `Kakeya.JointRefine.exists_joint_refinement`, which produces both data at once.

* `looseRhoParentData_self_of_count` — **the self route, and its one residue**.  Taking
  `sPar := s'` itself, every clause but (iv) is supplied by the loose datum
  `Kakeya.JointRefine.exists_joint_refinement` puts on `s'` (the retention is trivial at
  `δ^{2η} ≤ 1`).  What is missing is exactly the count **on the refined family**, and that clause
  is not subfamily-monotone: a node of `tρ` whose only witness is pruned leaves `tρ`.  Nothing in
  `exists_joint_refinement`'s cardinality retention bounds how many nodes that costs, and the
  exact route never needed it because its parent is the given `s`.

Neither theorem changes a existing statement; `LooseRhoParentData` is consumed at its existing text.
-/

@[expose] public section

open MeasureTheory Kakeya.LooseUniform Kakeya.VeryNotSticky

namespace Kakeya.JointRefine

universe u

variable {ι : Type u}

/-- **The minimal repair.**  A loose Definition-2.1 binder on the *given* family transports to
`LooseRhoParentData` on any retained subfamily, with `sPar := s`, exactly as the exact binder does
in `Kakeya.VeryNotSticky.rhoParentData_of_binders`. -/
theorem looseRhoParentData_of_binders {δ : NNReal} {ζ exscal η Kpar : ℝ} {s s' : Finset ι}
    {T T' : ι → ShadedTube δ E3} (hsub : s' ⊆ s)
    (htube : ∀ i, (T' i).toTube = (T i).toTube)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (LooseUniformTubeSet s (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Kpar C))
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    (hret : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal)) :
    LooseRhoParentData δ ζ exscal η Kpar s' T' := by
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcar : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  obtain ⟨C, hC1, hCδ, ⟨𝒰⟩⟩ := huni
  refine ⟨s, hsub, fun i hi => (hcar i) ▸ hball i hi, ?_, hret,
    ⟨C, hC1, hCδ, ⟨retubeLoose (fun i => htube i) 𝒰⟩⟩, ?_⟩
  · rw [Kakeya.maxDensity_congr (fun i _ => hbody i)]; exact hmax
  · intro ρ hρ
    obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ hρ
    refine ⟨κ, tρ, Tρ, hED, ?_, hcard⟩
    intro j hj
    obtain ⟨i, hi, hle⟩ := hused j hj
    exact ⟨i, hi, (hbody i) ▸ hle⟩

/-- **The self route.**  With `sPar := s'`, everything but the count on `s'` is supplied by a loose
datum on `s'` at a constant `≤ δ^{-η}`; the count on the *refined* family is the one clause the
joint refinement does not transport. -/
theorem looseRhoParentData_self_of_count {δ : NNReal} (hδ1 : δ ≤ 1) {ζ exscal η Kpar : ℝ}
    (hη : 0 ≤ η) {s' : Finset ι} {T' : ι → ShadedTube δ E3}
    (hball : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (LooseUniformTubeSet s' (fun i ↦ (T' i).toTube) (Tube.ssfGridLen δ) Kpar C))
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (T' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    LooseRhoParentData δ ζ exscal η Kpar s' T' := by
  refine ⟨s', Finset.Subset.refl _, hball, hmax, ?_, huni, hcount⟩
  have h1 : (δ : ENNReal) ^ (2 * η) ≤ 1 :=
    ENNReal.rpow_le_one (by exact_mod_cast hδ1) (by linarith)
  calc (δ : ENNReal) ^ (2 * η) * (s'.card : ENNReal) ≤ 1 * (s'.card : ENNReal) := by gcongr
    _ = (s'.card : ENNReal) := one_mul _

end Kakeya.JointRefine

end
