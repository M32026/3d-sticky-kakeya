/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloorObstruction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFill
public import Kakeya.RelativePlankRefutation

/-!
# `S1` is a re-statement, not a bridge

 leaves the `(F)` branch of the floor route owing one row
(`hwinfloor`'s conjunct 1): the dividing-scales twin
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` on
`Kakeya.ML2Core.refinedHierarchy 𝒰 hS' hhom hW`, while the only producer in the tree,
`Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow` (through
`Kakeya.ML2Inputs.DividingScalesOutputLevels` and `hpkg`), delivers it on `𝒲.tubeUniform` for a
hierarchy `𝒲` it **constructs** on its own subfamily `u'`.  the vehicle
`isKatzTaoDividingWindowLevels_of_cover_eq` closes the gap **given** the two identities

* `u' = S'`, and
* `𝒲.tubeUniform.cover = (refinedHierarchy 𝒰 hS' hhom hW).cover`.

This file measures both,.  The answer is **no on both counts, and the cover identity is
false of the construction**, so `S1` is a statement question about the `(F)` payload, not a bridge.

## What is proved here

* `Kakeya.ML2Core.refinedHierarchy_cover_is_ambient` — the `(F)` side, recorded: the refined
  hierarchy's `assign` and `tube` are the **ambient** `𝒰`'s verbatim and its `indexSet` is the
  ambient assignment's image of `S'`.  *(family `S'`; shading `W`; every level `k`.)*
* `Kakeya.S1CE.S1CoverBridge` / `not_S1CoverBridge` — the cover identity, stated over every
  structural clause the producer's output asserts about `(u', W)` relative to `(s, V)`, and
  **refuted** by a nonempty witness family with two hierarchies whose node labels differ.
  *(family `u' = s = Finset.range 1`; shading: the fully shaded witness tube on both sides;
  level pair: every level — the two `assign`s differ at every `k`.)*
* `Kakeya.S1CE.S1FamilyBridge` / `not_S1FamilyBridge` — the family identity `u' = S'`: the two
  selections are independent existentials and nothing relates them.
* `Kakeya.S1CE.producer_runs_on_refinedHierarchy` — the answer to "can the producer be applied
  *to* `refinedHierarchy`?".  **Yes, it type-checks; no, it does not help**: the conclusion is a
  twin on a *fresh* hierarchy `𝒰''` over a *fresh* subfamily `s'' ⊆ S'`, exactly the object the
  refutation above says is unrelated to `refinedHierarchy`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody StickyKakeya
open Tube (gridScale gridScale_self gridScale_antitone GridCoverSystem)
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## 1. The `(F)` side: the refined hierarchy's cover *is* the ambient one -/

section FSide

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The `(F)` branch's hierarchy, read at its cover.**  `Kakeya.ML2Core.refinedHierarchy` keeps
the ambient assignment and the ambient node tubes untouched and only shrinks the index set to the
occupied nodes of `S'`.  So `hwinfloor`'s conjunct 1 is a statement about the **ambient site's**
cover, not about any cover a producer may build.

*Family:* `S'`.  *Shading:* `W`.  *Level pair:* every level `k` (the equalities are pointwise in
`k`, so they hold for the window's `(a, b)` and for the band's `(p, c)` alike). -/
theorem refinedHierarchy_cover_is_ambient
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)) :
    (refinedHierarchy 𝒰 hS' hhom hW).cover.assign = 𝒰.cover.assign ∧
      (refinedHierarchy 𝒰 hS' hhom hW).cover.tube = 𝒰.cover.tube :=
  ⟨rfl, rfl⟩

/-- The third component of the same reading: the refined index set is the ambient assignment's
image of `S'`, stated membership-wise so that no `DecidableEq` instance is fixed. -/
theorem mem_refinedHierarchy_indexSet_iff
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)) (k : ℕ) (j : ι) :
    j ∈ (refinedHierarchy 𝒰 hS' hhom hW).cover.indexSet k ↔ ∃ i ∈ S', 𝒰.cover.assign k i = j := by
  classical
  exact Finset.mem_image

end FSide

end Kakeya.ML2Core

namespace Kakeya.S1CE

open Kakeya.PersistPlankCE Kakeya.ML2Core

/-! ## 2. The witness: one nonempty family, two hierarchies, two node labels -/

/-- The witness cover: one node, **labelled `c`**, at every grid scale, over `Nn` copies of the
fully shaded `δ`-tube of `Kakeya.PersistPlankCE`.  At `c = 0` this is
`Kakeya.PersistPlankCE.CEgrid`; the label is the only thing that moves. -/
noncomputable def CEgridAt (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M c : ℕ) :
    GridCoverSystem (Finset.range Nn) (fun _ : ℕ => (ST δ).toTube) M where
  indexSet := fun _ => {c}
  assign := fun _ _ => c
  tube := fun k _ => Kakeya.PersistPlankCE.T (gridScale δ M k)
  assign_mem := fun _ _ _ _ => Finset.mem_singleton_self c
  le_tube_assign := fun k hk _ _ => T_mono (Kakeya.PersistPlankCE.delta_le_gridScale hδ0 hδ1 hk)
  nested := fun _ _ _ _ _ _ _ => rfl
  tube_nested := fun k _ _ _ => T_mono (gridScale_antitone hδ0 hδ1 M (Nat.le_succ k))

theorem coverClassAt_eq (Nn c : ℕ) :
    Tube.coverClass (Finset.range Nn) (fun _ : ℕ => c) c = Finset.range Nn := by
  simp [Tube.coverClass]

theorem CEgridAt_indexSet (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M c k : ℕ) :
    (CEgridAt δ hδ0 hδ1 Nn M c).indexSet k = {c} := rfl

theorem CEgridAt_assign (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M c k : ℕ) :
    (CEgridAt δ hδ0 hδ1 Nn M c).assign k = fun _ : ℕ => c := rfl

/-- Definition 2.1 uniformity of the witness cover, at constant `1`, for **every** label `c`. -/
noncomputable def CEunifAt (δ : ℝ≥0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (Nn M c : ℕ) :
    Tube.UniformTubeSet (Finset.range Nn) (fun _ : ℕ => (ST δ).toTube) M 1 where
  cover := CEgridAt δ hδ0 hδ1 Nn M c
  branchingN := fun _ => (Nn : ℝ≥0)
  tube_injOn := by
    intro k hk a ha b hb _
    simp only [CEgridAt_indexSet, Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  boundedOverlap := by
    intro k hk V
    rw [CEgridAt_indexSet]
    have h : (({c} : Finset ℕ).filter (fun j => ∃ i ∈ Finset.range Nn,
        (ST δ).toConvexSpaceBody ≤ ((CEgridAt δ hδ0 hδ1 Nn M c).tube k j).toConvexSpaceBody ∧
        (ST δ).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ ({c} : Finset ℕ).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : (({c} : Finset ℕ)).card = 1 := rfl
    rw [h2] at h
    exact_mod_cast h
  card_class_le := by
    intro k hk j hj
    have hj0 : j = c := Finset.mem_singleton.mp (by rwa [CEgridAt_indexSet] at hj)
    subst hj0
    rw [CEgridAt_assign, coverClassAt_eq]
    simp
  le_card_class := by
    intro k hk j hj
    have hj0 : j = c := Finset.mem_singleton.mp (by rwa [CEgridAt_indexSet] at hj)
    subst hj0
    rw [CEgridAt_assign, coverClassAt_eq]
    simp

/-! ## 3. The cover identity `S1` needs, and its refutation -/

/-- **The cover identity  item 1, stated over everything the
producer's output asserts.**

`Kakeya.ML2Inputs.DividingScalesOutputLevels` and `hpkg` give, about the constructed hierarchy
`𝒲` relative to the site's family `(u, V)`: a subfamily `u' ⊆ u`, its nonemptiness, a shading `W`
on the *same* tubes and *inside* the site's shades, and `𝒲 : ShadedUniformTubeSet u' W (ssfGridLen
δ) Cw` — at a constant `Cw` (there `max C 4`) unrelated to the site's `Cu`.  The `(F)` branch needs
the twin on `refinedHierarchy`, whose `assign` **is** `𝒰.cover.assign`
(`Kakeya.ML2Core.refinedHierarchy_cover_is_ambient`), so the row `S1` owes is exactly this one.

Class-homogeneity of the site on `u'` is granted as well — it is what the `(F)` branch has to
supply anyway to name `refinedHierarchy`, so granting it makes the refutation stronger.

*Family:* `u'` inside `u`.  *Shading:* `W` inside `V`.  *Level pair:* all — the equality is of the
whole `assign` field. -/
def S1CoverBridge : Prop :=
  ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
  ∀ (Cu Cw : ℝ≥0) (u u' : Finset ℕ)
    (V W : ℕ → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (𝒰 : Tube.UniformTubeSet u (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (𝒲 : ShadedTube.ShadedUniformTubeSet u' W (Tube.ssfGridLen δ) Cw),
    u' ⊆ u → u'.Nonempty →
    (∀ i, (W i).toTube = (V i).toTube) → (∀ i, (W i).shade ⊆ (V i).shade) →
    IsClassHomogeneousOn 𝒰 u' →
    𝒲.tubeUniform.cover.assign = 𝒰.cover.assign

/-- **The cover identity is FALSE of the construction.**

Witness, at `δ = 1`: the family is `Finset.range 1` — **nonempty**, and `u' = u`, so the family row
`u' = S'` is not what fails here; the shading is the fully shaded witness tube on both sides, so
`W = V` and both shading rows hold with equality; class-homogeneity holds by
`Kakeya.ML2Core.isClassHomogeneousOn_self`.  The site's hierarchy labels its single node `1`, the
constructed one labels its single node `0`, and the two assignments differ at every level.

This is exactly the freedom `Kakeya.StickyKakeya.dividingScalesKatzTao` uses: its output hierarchy
is built by the stopping time, and the ambient hierarchy it is handed is never read for it. -/
theorem not_S1CoverBridge : ¬ S1CoverBridge := by
  intro h
  have hu : (Finset.range 1).Nonempty := ⟨0, by simp⟩
  have := h 1 one_pos le_rfl 1 1 (Finset.range 1) (Finset.range 1)
    (fun _ => ST 1) (fun _ => ST 1)
    (CEunifAt 1 one_pos le_rfl 1 (Tube.ssfGridLen 1) 1)
    (CEshadedUnif 1 one_pos le_rfl 1 (Tube.ssfGridLen 1))
    (Finset.Subset.refl _) hu (fun _ => rfl) (fun _ => subset_rfl)
    (isClassHomogeneousOn_self _)
  have h00 : (0 : ℕ) = 1 := congrFun (congrFun this 0) 0
  exact absurd h00 (by decide)

/-- **Firing control for `not_S1CoverBridge`, part 1: the same shape is provable on the `(F)`
side.**  With the constructed hierarchy replaced by the one the `(F)` branch actually names, the
identity is `rfl`.  So the refutation above is about the producer's freedom, not about the shape of
the statement. -/
theorem s1CoverBridge_holds_for_refinedHierarchy
    {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (V i).toTube)) :
    (refinedHierarchy 𝒰 hS' hhom hW).cover.assign = 𝒰.cover.assign := rfl

/-- **Firing control for `not_S1CoverBridge`, part 2: the witness's two objects agree when the
labels agree.**  So the disagreement in `not_S1CoverBridge` is caused by the node label alone and
not by a mismatch of definitions or of instances. -/
theorem witness_assign_agrees_at_label_zero :
    (CEshadedUnif 1 one_pos le_rfl 1 (Tube.ssfGridLen 1)).tubeUniform.cover.assign
      = (CEunifAt 1 one_pos le_rfl 1 (Tube.ssfGridLen 1) 0).cover.assign := rfl

/-- The `tube` row of the vehicle's three, on the same witness: it **holds** there.  So the
identity that fails is `assign` (and with it `indexSet`), not `tube` — the sharp answer to "state
exactly which identity fails". -/
theorem witness_tube_agrees :
    (CEshadedUnif 1 one_pos le_rfl 1 (Tube.ssfGridLen 1)).tubeUniform.cover.tube
      = (CEunifAt 1 one_pos le_rfl 1 (Tube.ssfGridLen 1) 1).cover.tube := rfl

/-- The `indexSet` row fails on the same witness, at every level. -/
theorem witness_indexSet_differs (k : ℕ) :
    (CEshadedUnif 1 one_pos le_rfl 1 (Tube.ssfGridLen 1)).tubeUniform.cover.indexSet k
      ≠ (CEunifAt 1 one_pos le_rfl 1 (Tube.ssfGridLen 1) 1).cover.indexSet k := by
  intro h
  have h0 : (0 : ℕ) ∈
      (CEunifAt 1 one_pos le_rfl 1 (Tube.ssfGridLen 1) 1).cover.indexSet k := by
    rw [← h]; exact Finset.mem_singleton_self 0
  have h1 : (0 : ℕ) ∈ ({1} : Finset ℕ) := h0
  simp at h1

/-! ## 4. The family identity `u' = S'` -/

/-- **The family identity, stated over everything that relates the two selections.**  The
producer's `u'` is chosen inside the site's family; the `(F)` branch's `S'` is chosen by the
refinement `hdev` inside the same family.  Nothing else relates them. -/
def S1FamilyBridge : Prop :=
  ∀ (S u' S' : Finset ℕ), u' ⊆ S → S' ⊆ S → u'.Nonempty → S'.Nonempty → u' = S'

theorem not_S1FamilyBridge : ¬ S1FamilyBridge := by
  intro h
  have := h {0, 1} {0} {1} (by decide) (by decide) ⟨0, by decide⟩ ⟨1, by decide⟩
  simp at this

/-- Firing control: the same shape **is** provable when the two selections are tied, so
`not_S1FamilyBridge` measures the missing tie and not a defect of the shape. -/
theorem s1FamilyBridge_holds_when_tied (u' S' : Finset ℕ) (h : u' = S') : u' = S' := h

/-! ## 5. Can the producer be run *on* the refined hierarchy?  Yes — and it does not help -/

section ProducerOnRefined

open Kakeya.ML2Reduction

universe w

/-- **The dividing-scales producer accepts `Kakeya.ML2Core.refinedHierarchy` as its uniformity
input.**  This is `Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow` applied at
`s := S'`, `T := fun i => (W i).toTube` and `hunif := refinedHierarchy 𝒰 hS' hhom hW`.

**And it does not deliver `S1`.**  Read the conclusion: the twin (or the every-scale alternative)
lands on a hierarchy `𝒰''` the producer *builds*, over a family `s'' ⊆ S'` it *selects* — not on
the `refinedHierarchy` that was handed in.  Together with `Kakeya.S1CE.not_S1CoverBridge` this is
the answer to "is `S1` a bridge or a re-statement": **a re-statement**.

*Family:* input `S'`, output `s'' ⊆ S'`.  *Shading:* `W` on both.  *Level pair:* the output window
`(a, b)` with rung index `m`, chosen by the producer. -/
theorem producer_runs_on_refinedHierarchy (Cu : ℝ≥0) {ε₂ : ℝ} (hε₂ : 0 < ε₂) :
    ∃ (C δ₀ : ℝ≥0) (Kl cl : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type w} {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 →
        (∀ k < ML2Reduction.stepCount ε₂,
          η k ≤ ML2Reduction.epsDiv (ML2Reduction.stepCount ε₂) * η (k + 1)) →
        η (ML2Reduction.stepCount ε₂) ≤ ML2Reduction.epsDiv (ML2Reduction.stepCount ε₂) →
      ∀ (u : Finset ι) (V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (𝒰 : Tube.UniformTubeSet u (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu)
        (S' : Finset ι) (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
        (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (hW : (fun i => (W i).toTube) = (fun i => (V i).toTube)),
        (∀ i ∈ S', (W i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (S' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct ((W i).carrier) ((W j).carrier)) →
        Kakeya.maxDensity S' (fun i => (W i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
        ∃ s'' ⊆ S',
          (S'.card : ENNReal) ≤ totalLoss C Kl cl δ * (s''.card : ENNReal) ∧
          ∃ 𝒰'' : Tube.UniformTubeSet s'' (fun i => (W i).toTube) (Tube.ssfGridLen δ) C,
            (𝒰''.IsKatzTaoAtEveryScale
                  ((C : ENNReal) * totalLoss C Kl cl δ * ENNReal.ofReal ((δ : ℝ) ^ (-ε₂)))
              ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰''
                  ((C : ENNReal) * totalLoss C Kl cl δ) η
                  (ML2Reduction.epsDiv (ML2Reduction.stepCount ε₂))
                  (ML2Reduction.stepCount ε₂) a b m) := by
  obtain ⟨C, δ₀, Kl, cl, hC, hδ₀0, hδ₀1, hmain⟩ :=
    ML2Reduction.exists_dichotomy_katzTaoDividingWindow.{w}
      (E := EuclideanSpace ℝ (Fin 3)) (by simp) Cu hε₂
  refine ⟨C, δ₀, Kl, cl, hC, hδ₀0, hδ₀1, ?_⟩
  intro ι δ hδ0 hδd η hη0 hηstep hηN u V 𝒰 S' hS' hhom W hW hball hED hdens
  exact hmain (ι := ι) (δ := δ) hδ0 hδd η hη0 hηstep hηN S' (fun i => (W i).toTube)
    hball hED (refinedHierarchy 𝒰 hS' hhom hW) hdens

/-- **Firing control for `producer_runs_on_refinedHierarchy`: the input slot is inert.**  The
identical conclusion follows from an *arbitrary* hierarchy on `S'` — the refined one is in no way
privileged, so no choice of input hierarchy can make the producer return its output on that input.
This is the form of the structural measurement that
`Kakeya.StickyKakeya.dividingScalesKatzTao` reads its ambient hierarchy argument only to borrow a
tube family on the empty case. -/
theorem producer_runs_on_any_hierarchy (Cu : ℝ≥0) {ε₂ : ℝ} (hε₂ : 0 < ε₂) :
    ∃ (C δ₀ : ℝ≥0) (Kl cl : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type w} {δ : ℝ≥0}, 0 < δ → δ ≤ δ₀ →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 →
        (∀ k < ML2Reduction.stepCount ε₂,
          η k ≤ ML2Reduction.epsDiv (ML2Reduction.stepCount ε₂) * η (k + 1)) →
        η (ML2Reduction.stepCount ε₂) ≤ ML2Reduction.epsDiv (ML2Reduction.stepCount ε₂) →
      ∀ (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (_𝒱 : Tube.UniformTubeSet S' (fun i => (W i).toTube) (Tube.ssfGridLen δ) Cu),
        (∀ i ∈ S', (W i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (S' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct ((W i).carrier) ((W j).carrier)) →
        Kakeya.maxDensity S' (fun i => (W i).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
        ∃ s'' ⊆ S',
          (S'.card : ENNReal) ≤ totalLoss C Kl cl δ * (s''.card : ENNReal) ∧
          ∃ 𝒰'' : Tube.UniformTubeSet s'' (fun i => (W i).toTube) (Tube.ssfGridLen δ) C,
            (𝒰''.IsKatzTaoAtEveryScale
                  ((C : ENNReal) * totalLoss C Kl cl δ * ENNReal.ofReal ((δ : ℝ) ^ (-ε₂)))
              ∨ ∃ a b m : ℕ, ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰''
                  ((C : ENNReal) * totalLoss C Kl cl δ) η
                  (ML2Reduction.epsDiv (ML2Reduction.stepCount ε₂))
                  (ML2Reduction.stepCount ε₂) a b m) := by
  obtain ⟨C, δ₀, Kl, cl, hC, hδ₀0, hδ₀1, hmain⟩ :=
    ML2Reduction.exists_dichotomy_katzTaoDividingWindow.{w}
      (E := EuclideanSpace ℝ (Fin 3)) (by simp) Cu hε₂
  refine ⟨C, δ₀, Kl, cl, hC, hδ₀0, hδ₀1, ?_⟩
  intro ι δ hδ0 hδd η hη0 hηstep hηN S' W 𝒱 hball hED hdens
  exact hmain (ι := ι) (δ := δ) hδ0 hδd η hη0 hηstep hηN S' (fun i => (W i).toTube)
    hball hED 𝒱 hdens

end ProducerOnRefined

/-! ## 6. The same measurement at `hfill`'s reading node -/

section ReadingNode

open Kakeya.ML2Reduction

universe u

/-- **The reading-node analogue of `Kakeya.S1CE.S1CoverBridge`.**  `hfill` (`FillAt 𝒰 κ a m' jp`)
is a statement about nodes of the `(F)` hierarchy, whose index sets are the ambient site's
(`Kakeya.ML2Core.mem_refinedHierarchy_indexSet_iff`).  For the dividing-scales producer to *select*
such a node — coarser or not — its own hierarchy would have to have the same nodes. -/
def HFillReadingNodeBridge : Prop :=
  ∀ (δ : ℝ≥0), 0 < δ → δ ≤ 1 →
  ∀ (Cu Cw : ℝ≥0) (u u' : Finset ℕ)
    (V W : ℕ → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (𝒰 : Tube.UniformTubeSet u (fun i => (V i).toTube) (Tube.ssfGridLen δ) Cu)
    (𝒲 : ShadedTube.ShadedUniformTubeSet u' W (Tube.ssfGridLen δ) Cw),
    u' ⊆ u → u'.Nonempty →
    (∀ i, (W i).toTube = (V i).toTube) → (∀ i, (W i).shade ⊆ (V i).shade) →
    IsClassHomogeneousOn 𝒰 u' →
    ∀ k : ℕ, 𝒲.tubeUniform.cover.indexSet k = 𝒰.cover.indexSet k

/-- **The producer selects no node of the `(F)` hierarchy.**  Same witness as
`Kakeya.S1CE.not_S1CoverBridge`: the two hierarchies' node sets are `{0}` and `{1}` at every level.
So `hfill`'s reading node — at any level, coarser or not — is not something the dividing-scales
producer can supply; the owner of `hfill` is a producer over the *ambient site's* hierarchy.

*Family:* `u' = u = Finset.range 1`.  *Shading:* the fully shaded witness tube on both sides.
*Level pair:* every level `k`. -/
theorem not_HFillReadingNodeBridge : ¬ HFillReadingNodeBridge := by
  intro h
  have hu : (Finset.range 1).Nonempty := ⟨0, by simp⟩
  have hk := h 1 one_pos le_rfl 1 1 (Finset.range 1) (Finset.range 1)
    (fun _ => ST 1) (fun _ => ST 1)
    (CEunifAt 1 one_pos le_rfl 1 (Tube.ssfGridLen 1) 1)
    (CEshadedUnif 1 one_pos le_rfl 1 (Tube.ssfGridLen 1))
    (Finset.Subset.refl _) hu (fun _ => rfl) (fun _ => subset_rfl)
    (isClassHomogeneousOn_self _) 0
  exact witness_indexSet_differs 0 hk

/-- **The tree's own constructed dividing-window instance sits at coarse level `a = 0`.**  This is
`Kakeya.ML2Core.gridModel_window` restated with its `a` slot displayed, so that the level bound
below is about a realisable window and not about a vacuous case. -/
theorem landed_window_model_has_coarse_level_zero {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {K : ℕ}
    (hN0 : 0 < Tube.ssfGridLen δ)
    {C : NNReal} (hC1 : 1 ≤ C) {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K)
    (hne : s'.Nonempty)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {η : ℕ → ℝ} (hη0 : 0 ≤ η 0) (hη1 : 0 ≤ η 1) {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 2)
    (hη1e : η 1 ≤ e) {Nsp : ℕ} (hNsp : 0 < Nsp)
    (hR : (δ : ℝ) + 6 * δ * K ≤ (δ : ℝ) ^ (1 - e))
    (hsmall : (δ : ℝ) ^ e ≤ 1 / 2)
    (hcount : ((1 : ℝ) / δ) ^ e * (4 * (Tube.volume_le.C 3 : ℝ) * (C : ℝ) ^ 2)
      ≤ (s'.card : ℝ) * (Tube.le_volume.c 3 : ℝ)) :
    ML2Reduction.IsKatzTaoDividingWindow 𝒰 (C : ENNReal) η e Nsp 0 (Tube.ssfGridLen δ) 0 :=
  gridModel_window hδ0 hδ1 hN0 hC1 hs' hne 𝒰 hη0 hη1 he0 he1 hη1e hNsp hR hsmall hcount

/-- **The twin bounds its coarse level `a` only from above**: `a < b ≤ ssfGridLen δ`, and nothing
else in the structure mentions `a` alone.  So `a = 0` is not excluded by the window. -/
theorem window_bounds_coarse_level_only_from_above
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ Cst : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cst} {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ}
    {N a b m : ℕ}
    (h : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m) :
    a < b ∧ b ≤ Tube.ssfGridLen δ :=
  ⟨h.coarse_lt_fine, h.fine_le_gridLen⟩

/-- **At `a = 0` there is no strictly coarser reading level.**  With ``'s conclusion — that
`hvol` forces the reading node strictly coarser than the node being filled, and `F4a` fills at the
window's own coarse level `a` — this says the `(F)` route's `hfill` has no reading node available
whenever the window is at `a = 0`, which `landed_window_model_has_coarse_level_zero` shows is a
realisable window. -/
theorem no_strictly_coarser_level_at_zero (k : ℕ) : ¬ k < 0 := Nat.not_lt_zero k

/-- Firing control for the line above: strictly coarser levels do exist as soon as `a ≥ 1`, so the
statement measures the degenerate window and not an arithmetic triviality about `<`. -/
theorem some_strictly_coarser_level_at_one : ∃ k : ℕ, k < 1 := ⟨0, Nat.zero_lt_one⟩

/-- **`hvol` read at the node being filled is a measure equality**, self-contained: the maximizer's
hull sits inside the reading node, so if the reading node *is* the node being filled then
`Kakeya.ML2Core.fillAt_of_biasedMaximizer`'s `hvol` pins the two volumes together.  Stated with the
containment as a hypothesis so that this leaf depends on no auxiliary file.

*Family:* the hierarchy's own node families.  *Shading:* none — this is a statement about node
tubes.  *Level pair:* `(q, c)` — the filled level `q` and the cell level `c`. -/
theorem volume_eq_of_hvol_at_filled_node
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒰 : Tube.UniformTubeSet s T N C) {c q : ℕ} {jq : ι} {t : Finset ι}
    (hsub : (t.convexHull_biUnion
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
      ⊆ (𝒰.cover.tube q jq).carrier)
    (hvol : volume (𝒰.cover.tube q jq).carrier
      ≤ volume (t.convexHull_biUnion
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier) :
    volume (t.convexHull_biUnion
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)).carrier
      = volume (𝒰.cover.tube q jq).carrier :=
  le_antisymm (measure_mono hsub) hvol

end ReadingNode

end Kakeya.S1CE

end
