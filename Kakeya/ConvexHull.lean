/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Convex.Body
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.Hull
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Normed.Module.Basic

/-!
Convex hull of a finite number of convex body is a convex body.
-/

@[expose] public section

namespace Convexity

section AffineImage

variable
  {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
  {W Q : Type*} [AddCommGroup W] [Module ℝ W] [AddTorsor W Q]

/-- An affine map of real affine spaces commutes with taking convex hulls. This is the
`Convexity.convexHull` analogue of `AffineMap.image_convexHull`; it is stated for a bundled
`AffineMap` because `Convexity.IsAffineMap` does not yet subsume affine maps of affine spaces. -/
theorem affineMap_image_convexHull (f : P →ᵃ[ℝ] Q) (s : Set P) :
    f '' convexHull ℝ s = convexHull ℝ (f '' s) :=
  Set.Subset.antisymm
    (Set.image_subset_iff.2 <| convexHull_min
      ((Set.subset_preimage_image f s).trans (Set.preimage_mono subset_convexHull_self))
      (IsConvexSet.affineMap_preimage f IsConvexSet.convexHull))
    (convexHull_min (Set.image_mono subset_convexHull_self)
      (IsConvexSet.affineMap_image f IsConvexSet.convexHull))

end AffineImage

section VectorSpace

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- In a real vector space the convex-space hull `Convexity.convexHull` agrees with the usual
`convexHull`, so the whole mathlib convexity API transfers across `isConvexSet_iff_convex`. -/
theorem convexHull_eq_convexHull (s : Set W) :
    convexHull ℝ s = _root_.convexHull ℝ s :=
  Set.Subset.antisymm
    (Convexity.convexHull_min (subset_convexHull ℝ s) (convex_convexHull ℝ s).isConvexSet)
    (_root_.convexHull_min Convexity.subset_convexHull_self Convexity.IsConvexSet.convexHull.convex)

end VectorSpace

end Convexity

/-- Extending a function by zero along an embedding leaves its total sum unchanged. -/
private lemma sum_extend_zero {ι κ M : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid M]
    (e : ι ↪ κ) (f : ι → M) :
    ∑ j, Function.extend ⇑e f (0 : κ → M) j = ∑ i, f i :=
  (Finset.sum_of_injOn ⇑e (Set.injOn_of_injective e.injective)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun b _ hb => Function.extend_apply' f (0 : κ → M) b fun ⟨a, ha⟩ =>
      hb ⟨a, Finset.mem_coe.2 (Finset.mem_univ a), ha⟩)
    (fun a _ => (e.injective.extend_apply f (0 : κ → M) a).symm)).symm

/-- A predicate satisfied by a function and by the default value is satisfied by the extension. -/
private lemma extend_prop {ι κ M : Type*} (e : ι ↪ κ) (f : ι → M) (g : κ → M) (P : M → Prop)
    (hf : ∀ i, P (f i)) (hg : ∀ j, P (g j)) (j : κ) :
    P (Function.extend ⇑e f g j) := by
  classical
  by_cases hj : ∃ a, e a = j
  · obtain ⟨a, rfl⟩ := hj
    rw [e.injective.extend_apply]
    exact hf a
  · rw [Function.extend_apply' f g j hj]
    exact hg j

/-- Extending pointwise a scalar multiplication: weights extended by zero against points extended
by an arbitrary constant. -/
private lemma extend_smul_extend {ι κ R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (e : ι ↪ κ) (w : ι → R) (z : ι → M) (c : M) (j : κ) :
    Function.extend ⇑e w (0 : κ → R) j • Function.extend ⇑e z (fun _ => c) j
      = Function.extend ⇑e (fun i => w i • z i) (0 : κ → M) j := by
  classical
  by_cases hj : ∃ a, e a = j
  · obtain ⟨a, rfl⟩ := hj
    simp only [e.injective.extend_apply]
  · rw [Function.extend_apply' w _ j hj, Function.extend_apply' z _ j hj,
      Function.extend_apply' (fun i => w i • z i) _ j hj]
    exact zero_smul R c

/-- In a finite-dimensional real normed vector space the convex hull of a compact set is compact.
Proved from Carathéodory's theorem: the hull is the image of the compact set
`stdSimplex ℝ (Fin (d + 1)) ×ˢ sᶠⁱⁿ` under the continuous map taking weights and points to the
corresponding convex combination. -/
theorem IsCompact.convexHull {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] {s : Set W} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank ℝ W = d := ⟨_, rfl⟩
  have himg := ((isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin (d + 1))).prod
    (isCompact_univ_pi fun _ => hs)).image
    (f := fun p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → W) => ∑ i, p.1 i • p.2 i) (by fun_prop)
  convert himg using 1
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨ι, hFI, z, w, hrange, hAf, hwpos, hwsum, hwzsum⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    letI : Fintype ι := hFI
    obtain ⟨emb⟩ : Nonempty (ι ↪ Fin (d + 1)) :=
      Function.Embedding.nonempty_of_card_le (by
        rw [Fintype.card_fin, ← hd]
        exact hAf.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _)))
    refine ⟨(Function.extend ⇑emb w 0, Function.extend ⇑emb z fun _ => k₀),
      ⟨⟨extend_prop emb w 0 (0 ≤ ·) (fun i => (hwpos i).le) fun _ => le_rfl,
        (sum_extend_zero emb w).trans hwsum⟩,
        fun j _ => extend_prop emb z _ (· ∈ s) (fun i => hrange ⟨i, rfl⟩) (fun _ => hk₀) j⟩, ?_⟩
    exact (Finset.sum_congr rfl fun j _ => extend_smul_extend emb w z k₀ j).trans
      ((sum_extend_zero emb _).trans hwzsum)
  · rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ => hp1.1 i) hp1.2
      (fun i _ => subset_convexHull ℝ s (hp2 i (Set.mem_univ i)))

variable
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [PseudoMetricSpace E] [NormedAddTorsor V E]

/-- In a finite-dimensional real affine space, the convex hull of a compact set is compact.
Transported to the model vector space `V` along the affine isometry `(x₀ -ᵥ ·)`. -/
lemma IsCompact.isCompact_convexHull {K : Set E} (hK : IsCompact K) :
    IsCompact (Convexity.convexHull ℝ K) := by
  obtain ⟨x₀⟩ : Nonempty E := inferInstance
  set e : E ≃ᵃⁱ[ℝ] V := AffineIsometryEquiv.constVSub ℝ x₀
  rw [← e.toHomeomorph.isCompact_image (s := Convexity.convexHull ℝ K),
    show ⇑e.toHomeomorph = ⇑e.toAffineEquiv.toAffineMap from rfl,
    Convexity.affineMap_image_convexHull, Convexity.convexHull_eq_convexHull]
  exact IsCompact.convexHull (hK.image e.continuous)

namespace Finset
variable {ι : Type*} {s : Finset ι}

/-- The convex hull of the union `⋃ i ∈ s, K i` of a nonempty finite indexed family of
convex bodies, packaged as a convex body. -/
@[simps, nolint defsWithUnderscore]
def convexHull_biUnion' {s : Finset ι} (hs : s.Nonempty)
    (K : ι → ConvexSpaceBody E) : ConvexSpaceBody E where
  carrier := Convexity.convexHull ℝ <| ⋃ i ∈ s, (K i).carrier
  convex' := Convexity.IsConvexSet.convexHull
  isCompact' := IsCompact.isCompact_convexHull <| s.isCompact_biUnion fun i _ => (K i).isCompact
  nonempty' := Convexity.Set.Nonempty.convexHull'
      <| Set.nonempty_biUnion.2 ⟨_, hs.choose_spec, (K _).nonempty'⟩


/-- The convex hull of a finite indexed union of convex bodies, if this is a nontrivial union;
  the singleton {0} otherwise. -/
@[nolint defsWithUnderscore]
noncomputable def convexHull_biUnion (s : Finset ι) (K : ι → ConvexSpaceBody E) :
    ConvexSpaceBody E :=
  if hs : s.Nonempty then convexHull_biUnion' hs K else Classical.arbitrary (ConvexSpaceBody E)

@[simp]
lemma convexHull_biUnion_of_nonempty (hs : s.Nonempty) (K : ι → ConvexSpaceBody E) :
    convexHull_biUnion s K = convexHull_biUnion' hs K := by
  simp [convexHull_biUnion, hs]

theorem Nonempty.convexHull_biUnion_carrier (hs : s.Nonempty) (K : ι → ConvexSpaceBody E) :
    (convexHull_biUnion s K).carrier = Convexity.convexHull ℝ (⋃ i ∈ s, (K i).carrier) := by
  rw [convexHull_biUnion_of_nonempty hs]; rfl

theorem le_convexHull_biUnion (K : ι → ConvexSpaceBody E)
    ⦃i : ι⦄ (hi : i ∈ s) : K i ≤ convexHull_biUnion s K := by
  unfold convexHull_biUnion
  rw [dif_pos ⟨i, hi⟩]
  exact fun _ hx =>
    Convexity.subset_convexHull_self (Set.subset_biUnion_of_mem hi hx)

/-- If all K i are in a convex set B, then convexHull_biUnion is also in B. -/
theorem Nonempty.convexHull_biUnion_subset_iff (hs : s.Nonempty)
    (K : ι → ConvexSpaceBody E) {B : Set E} (hB : Convexity.IsConvexSet ℝ B) :
    (convexHull_biUnion s K).carrier ⊆ B ↔ ∀ i ∈ s, (K i).carrier ⊆ B := by
  simp [convexHull_biUnion_of_nonempty hs, hB.convexHull_subset_iff]

theorem Nonempty.convexHull_biUnion_le_iff (hs : s.Nonempty)
    (K : ι → ConvexSpaceBody E) (B : ConvexSpaceBody E) :
    convexHull_biUnion s K ≤ B ↔ ∀ i ∈ s, K i ≤ B :=
  hs.convexHull_biUnion_subset_iff K B.isConvexSet

/-- Blueprint `lem:hullSingleton`: the hull `W_{i}` of a singleton subfamily is the body `K i`
itself, since a convex body is its own convex hull. -/
@[simp, nolint simpNF]
theorem convexHull_biUnion_singleton (K : ι → ConvexSpaceBody E) (i : ι) :
    convexHull_biUnion {i} K = K i := by
  ext1
  change (convexHull_biUnion {i} K).carrier = (K i).carrier
  rw [(Finset.singleton_nonempty i).convexHull_biUnion_carrier, Finset.set_biUnion_singleton]
  exact (K i).isConvexSet.convexHull_eq_self

end Finset
