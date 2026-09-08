/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.CoreAtScale
public import Kakeya.DimensionThree.MainLemma2.ThinCore
public import Kakeya.DimensionThree.MainLemma2.ThinCentredMult
public import Kakeya.DimensionThree.MainLemma2.ThinCellVolume
public import Kakeya.DimensionThree.MainLemma2.ThinFullness

/-!
# The factor family of the thin-case factoring step

`Kakeya.ThinCase.factoringApply` is the application of GWZ Proposition 5.1 — in the tree, the
`ShadedBody.outerFactoringFamily` pipeline of `Kakeya/Factoring/Multiplicity.lean` — to the
factoring `𝕋_B = ⨆_{W ∈ 𝕎_B} 𝕋_{B,W}` of clause (C4) of Configuration `hyp:ml2setup`.

Every entry point of that pipeline takes a `ShadedBody.FactorFamily` together with
`ShadedBody.FactorFamily.InnerIsDiscretizedAtScale`, whose two fields are

* `subset_unitBall` — every inner body lies in `Metric.closedBall 0 1`, and
* `le_scale` — every inner body has shortest affine scale at least the discretization scale.

This file builds that family and both fields out of the hypotheses of `factoringApply`.

Two points are worth recording.

**The centre.** `factoringApply` localises its bodies in a ball `Metric.closedBall z 1` with `z`
*existentially quantified*, because nothing in the data distinguishes the origin; the pipeline
insists on the origin. The family built here is therefore the translate of the data by `-z`, and
the translation-invariance lemmas of the first section are what make that free. Transporting the
pipeline's *output* back by `+z` is the business of the eventual proof of `factoringApply`, not of
this file.

**The scale.** `le_scale` is *not* a consequence of the hypotheses of `factoringApply`: those
bound the affine thicknesses of the segments only from above (`hle` puts a segment inside its
body, `hdims` compares segments with one another), so a segment may be an arbitrarily small ball
inside its body. It is therefore taken here as an explicit hypothesis `hscale`, at a scale `δ₀`
which the caller chooses. At the sole call site `Kakeya.ThinCase.perBall` the available value is
`δ₀ = δ / C₀`, from `Kakeya.ThinCase.IsBallFactoring.thick`
(`HasThicknesses (Y p).carrier C₀ ![r₁, δ, δ]` gives `C₀⁻¹ δ ≤ τ_k` at every rank, using
`δ ≤ a ≤ b ≤ r₁`); the constant `C₀` cannot be removed, which is why the scale is a parameter and
not `δ` itself.
-/

@[expose] public section

namespace Kakeya.ThinCase

open MeasureTheory Metric Set ShadedBody Kakeya
open scoped Pointwise

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- The convex body underlying a translated shaded body is the translate of its convex body. -/
lemma toConvexSpaceBody_translate (W : ShadedBody E) (v : E) :
    (W.translate v).toConvexSpaceBody = W.toConvexSpaceBody.translate v := by
  ext1
  show v +ᵥ W.carrier = (v + ·) '' W.carrier
  rw [← Set.image_vadd]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Translating a bounded set keeps it bounded. -/
lemma isBounded_image_add_left (v : E) {X : Set E} (hX : Bornology.IsBounded X) :
    Bornology.IsBounded ((v + ·) '' X) := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall (0 : E) |>.mp hX
  refine Metric.isBounded_iff_subset_closedBall v |>.mpr ⟨r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hr hx
  simp only [Metric.mem_closedBall, dist_zero_right] at hx'
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx'

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Affine thickness is translation invariant.** Both inequalities come from
`LipschitzWith.ethickness_image_le` applied to the affine equivalence `x ↦ v + x`, which is an
isometry, and to its inverse. -/
lemma ethickness_image_add_left (v : E) (X : Set E) (n : ℕ) :
    Metric.ethickness ℝ ((v + ·) '' X) n = Metric.ethickness ℝ X n := by
  have key : ∀ (w : E) (Y : Set E),
      Metric.ethickness ℝ ((w + ·) '' Y) n ≤ Metric.ethickness ℝ Y n := by
    intro w Y
    have hL : LipschitzWith 1 ⇑((AffineEquiv.constVAdd ℝ E w).toAffineMap) := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      simp [AffineEquiv.constVAdd, dist_eq_norm]
    have h := hL.ethickness_image_le (𝕜 := ℝ) Y n
    have hmap : ⇑((AffineEquiv.constVAdd ℝ E w).toAffineMap) = (w + ·) := by
      funext x; simp [AffineEquiv.constVAdd]
    rw [hmap] at h
    simpa using h
  refine le_antisymm (key v X) ?_
  have h2 := key (-v) ((v + ·) '' X)
  rw [Set.image_image] at h2
  simpa using h2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The shortest affine scale is translation invariant. -/
lemma ethickness_scale_image_add_left (v : E) (X : Set E) :
    Metric.ethickness.scale ℝ ((v + ·) '' X) = Metric.ethickness.scale ℝ X := by
  unfold Metric.ethickness.scale
  exact Finset.inf_congr rfl (fun n _ => ethickness_image_add_left v X n)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Affine thickness is translation invariant, in the `ℝ`-valued form. -/
lemma thickness_image_add_left (v : E) {X : Set E} (hX : Bornology.IsBounded X) (n : ℕ) :
    Metric.thickness ℝ ((v + ·) '' X) n = Metric.thickness ℝ X n := by
  rw [← Metric.toReal_ethickness (isBounded_image_add_left v hX),
    ← Metric.toReal_ethickness hX, ethickness_image_add_left v X n]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Closed metric collars commute with translation. -/
lemma cthickening_image_add_left (v : E) (r : ℝ) (X : Set E) :
    (v + ·) '' (Metric.cthickening r X) = Metric.cthickening r ((v + ·) '' X) := by
  simpa using Metric.image_cthickening_isometryEquiv (IsometryEquiv.addLeft v) r X

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The scale of a convex body is translation invariant. -/
lemma scale_translate (K : ConvexSpaceBody E) (v : E) :
    (K.translate v).scale = K.scale :=
  thickness_image_add_left v K.isCompact'.isBounded _

omit [MeasurableSpace E] [BorelSpace E] in
/-- Closed collars commute with translation, at the level of convex bodies. -/
lemma cthickening_translate (K : ConvexSpaceBody E) (r : ℝ) (v : E) :
    (K.cthickening r).translate v = (K.translate v).cthickening r := by
  ext1
  exact cthickening_image_add_left v r K.carrier

/-- Volume is translation invariant, in the form the shade of a translated body needs. -/
lemma volume_image_add_left (v : E) (X : Set E) :
    volume ((v + ·) '' X) = volume X := by
  rw [Set.image_add_left]
  exact measure_preimage_add volume (-v) X

end Transport

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {σ ω : Type*} [DecidableEq ω]

/-- **The factor family of `Kakeya.ThinCase.factoringApply`**: the segments `𝕋_B` as inner
bodies, the factoring bodies `𝕎_B` as outer bodies, the block map as parent, all translated by
`-z` so that the localisation ball `Metric.closedBall z 1` of `factoringApply`'s `hloc` becomes
the unit ball the Proposition 5.1 pipeline asks for. -/
def thinFactorFamily (segs : Finset σ) (Y : σ → ShadedBody E)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody E) (blk : σ → ω) (z : E)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)) :
    ShadedBody.FactorFamily E σ ω where
  innerSet := segs
  innerBody := fun p => (Y p).translate (-z)
  outerSet := bodies
  outerBody := fun j => (Wb j).translate (-z)
  parent := blk
  parent_mem := hblk
  inner_le_parent := fun p hp => by
    rw [toConvexSpaceBody_translate]
    exact translate_le_translate _ (hle p hp)

variable {segs : Finset σ} {Y : σ → ShadedBody E} {bodies : Finset ω}
  {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {z : E}
  {hblk : ∀ p ∈ segs, blk p ∈ bodies}
  {hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)}

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_innerSet :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).innerSet = segs := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_outerSet :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).outerSet = bodies := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_parent :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).parent = blk := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_innerBody (p : σ) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).innerBody p = (Y p).translate (-z) := rfl

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
@[simp] lemma thinFactorFamily_outerBody (j : ω) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).outerBody j = (Wb j).translate (-z) := rfl

omit [FiniteDimensional ℝ E] in
lemma thinFactorFamily_fiber (j : ω) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).fiber j =
      segs.filter (fun p => blk p = j) := by
  classical
  simp [ShadedBody.FactorFamily.fiber, thinFactorFamily]

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
/-- **Step 1 of the proof of `Kakeya.ThinCase.factoringApply`: the family is inner-discretized.**

`subset_unitBall` is `hloc` together with `hle`, read after the translation by `-z`; `le_scale`
is the hypothesis `hscale`, which is *not* derivable from the other hypotheses of
`factoringApply` (see the module docstring). -/
theorem thinFactorFamily_innerIsDiscretizedAtScale [Nontrivial E] {δ₀ : NNReal}
    (hloc : ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1)
    (hscale : ∀ p ∈ segs, (δ₀ : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀ where
  subset_unitBall := by
    intro p hp
    have hsub : (Y p).carrier ⊆ Metric.closedBall z 1 := fun x hx =>
      hloc (blk p) (hblk p hp) (hle p hp hx)
    show ((-z) + ·) '' (Y p).carrier ⊆ Metric.closedBall 0 1
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hsub hx
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx' ⊢
    simpa [add_comm, ← sub_eq_add_neg] using hx' 
  le_scale := by
    intro p hp
    show (δ₀ : ENNReal) ≤ Metric.ethickness.scale ℝ (((-z) + ·) '' (Y p).carrier)
    rw [ethickness_scale_image_add_left]
    exact hscale p hp

omit [FiniteDimensional ℝ E] [DecidableEq ω] in
/-- The `hdims` hypothesis of `factoringApply` is exactly `InnerHasSimilarShape 2` for the family
(affine thickness being translation invariant). -/
theorem thinFactorFamily_innerHasSimilarShape
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerHasSimilarShape 2 := by
  intro p hp q hq k
  have hp' : Metric.thickness ℝ (((-z) + ·) '' (Y p).carrier) k
      = Metric.thickness ℝ (Y p).carrier k :=
    thickness_image_add_left _ (Y p).isCompact'.isBounded k
  have hq' : Metric.thickness ℝ (((-z) + ·) '' (Y q).carrier) k
      = Metric.thickness ℝ (Y q).carrier k :=
    thickness_image_add_left _ (Y q).isCompact'.isBounded k
  have h := hdims p hp q hq k
  show Metric.thickness ℝ (((-z) + ·) '' (Y p).carrier) k ≤
    ((2 : NNReal) : ℝ) • Metric.thickness ℝ (((-z) + ·) '' (Y q).carrier) k
  rw [hp', hq']
  simpa [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul] using h

/-- The `hFr` hypothesis of `factoringApply` is exactly `HasFrostmanFibers CF` for the family
(the Frostman property being translation invariant). -/
theorem thinFactorFamily_hasFrostmanFibers {CF : NNReal}
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn (segs.filter fun p => blk p = j)
      (fun p => (Y p).toConvexSpaceBody) (Wb j) CF) :
    (thinFactorFamily segs Y bodies Wb blk z hblk hle).HasFrostmanFibers CF := by
  intro j hj
  rw [thinFactorFamily_fiber]
  have h := (hFr j hj).translate (-z)
  simpa only [thinFactorFamily_innerBody, thinFactorFamily_outerBody,
    toConvexSpaceBody_translate] using h

end Family


/-! ### The Proposition 5.1 output, transported back

`ShadedBody.outerFactoringFamily` runs the Step 0 - Step 5 pipeline on the translated family;
its output lives in translated coordinates, and the definitions below translate it back by `+z`.
Every clause of `Kakeya.ThinCase.factoringApply` that the pipeline supplies without a further
pigeonhole is then read off. -/

section Pipeline

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {σ ω : Type*} [DecidableEq ω]
  {segs : Finset σ} {Y : σ → ShadedBody E} {bodies : Finset ω}
  {Wb : ω → ConvexSpaceBody E} {blk : σ → ω} {z : E}
  {hblk : ∀ p ∈ segs, blk p ∈ bodies}
  {hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)}
  {δ₀ w₁ : NNReal}

/-- `0 < w₁` from the scale window, the form the `AtScale` pipeline asks for. -/
theorem thinPipeline_w₁_pos (hδ₀ : 0 < δ₀) (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : 0 < w₁ :=
  lt_of_lt_of_le hδ₀ hw₁.1

/-- The output of the corrected GWZ Proposition 5.1 at the thin-case family, in translated
coordinates.

This is `ShadedBody.outerThickFamilyAtScale`, the **weighted** pipeline, not
`ShadedBody.outerFactoringFamily`. The two differ by the eccentricity datum `D`, and taking the
weighted one is what makes `ShadedBody.factoringAndMultPropCoreAtScale` — and with it conjunct (i)
of `Kakeya.ThinCase.factoringApply`, its `thick_fullness` field — available at all. The datum is
`Kakeya.ThinCase.thinVolumeRatio`, built from `factoringApply`'s own `hdims` and `hFr`. -/
noncomputable def thinPipeline (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : ShadedFactorFamily E σ ω :=
  ShadedBody.outerThickFamilyAtScale (thinFactorFamily segs Y bodies Wb blk z hblk hle)
    hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁)

variable {hδ₀ : 0 < δ₀}
  {hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀}
  {D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle)}
  {hw₁ : w₁ ∈ Set.Icc δ₀ 1}

/-- The refined family of segments `𝕋'_B ⊆ 𝕋_B` returned by the pipeline. -/
noncomputable def thinSegs' (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : Finset σ :=
  (thinPipeline hδ₀ hdisc D hw₁).innerSet

/-- The retained family of bodies `𝕎'_B ⊆ 𝕎_B` returned by the pipeline. -/
noncomputable def thinBodies' (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : Finset ω :=
  (thinPipeline hδ₀ hdisc D hw₁).outerSet

/-- The refined shading `Y'` on the segments, translated back to the original position. -/
noncomputable def thinY' (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : σ → ShadedBody E :=
  fun p => ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).translate z

/-- The induced shading `Y_{𝕎'}` on the enlarged bodies, translated back. -/
noncomputable def thinW (hδ₀ : 0 < δ₀)
    (hdisc : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerIsDiscretizedAtScale δ₀)
    (D : ShadedBody.OuterInnerVolumeRatio (thinFactorFamily segs Y bodies Wb blk z hblk hle))
    (hw₁ : w₁ ∈ Set.Icc δ₀ 1) : ω → ShadedBody E :=
  fun j => ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).translate z

/-- Clause (a): the refined segments form a subfamily. -/
theorem thinSegs'_subset : thinSegs' hδ₀ hdisc D hw₁ ⊆ segs := by
  intro p hp
  unfold thinSegs' thinPipeline at hp
  rw [ShadedBody.outerThickFamilyAtScale_innerSet_eq_filter] at hp
  exact (Finset.mem_filter.mp hp).1

/-- Clause (b): the retained bodies form a subfamily. -/
theorem thinBodies'_subset : thinBodies' hδ₀ hdisc D hw₁ ⊆ bodies :=
  ShadedBody.outerThickFamilyAtScale_outerSet_subset _ hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁)

/-- Clause (c): the refinement changes the shadings, never the carriers. -/
theorem thinY'_toConvexSpaceBody (p : σ) :
    (thinY' hδ₀ hdisc D hw₁ p).toConvexSpaceBody = (Y p).toConvexSpaceBody := by
  unfold thinY' thinPipeline
  rw [toConvexSpaceBody_translate,
    ShadedBody.outerThickFamilyAtScale_innerBody_toConvexSpaceBody]
  show (((Y p).translate (-z)).toConvexSpaceBody).translate z = (Y p).toConvexSpaceBody
  rw [toConvexSpaceBody_translate, ConvexSpaceBody.translate_neg_cancel]

/-- Clause (d): the refined shadings shrink. -/
theorem thinY'_shade_subset {p : σ} (hp : p ∈ thinSegs' hδ₀ hdisc D hw₁) :
    (thinY' hδ₀ hdisc D hw₁ p).shade ⊆ (Y p).shade := by
  have h := (ShadedBody.outerThickFamilyAtScale_isCRefinement
    (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁)).1.2 p hp
  have hsub : ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).shade ⊆ ((-z) + ·) '' (Y p).shade :=
    h.2
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hsub hx
  simpa using hy

/-- Both halves of the enlargement sandwich, as an equality: the outer bodies of the pipeline
are exactly the enlargements `N_{τ₂(Wb j)}(Wb j)`. -/
theorem thinW_toConvexSpaceBody (j : ω) :
    (thinW hδ₀ hdisc D hw₁ j).toConvexSpaceBody = (Wb j).cthickening (Wb j).scale := by
  unfold thinW thinPipeline
  rw [toConvexSpaceBody_translate,
    ShadedBody.outerThickFamilyAtScale_outerBody_toConvexSpaceBody]
  show ((((Wb j).translate (-z)).cthickening (((Wb j).translate (-z))).scale)).translate z
    = (Wb j).cthickening (Wb j).scale
  rw [scale_translate, cthickening_translate,
    ConvexSpaceBody.translate_neg_cancel]

omit [Nontrivial E] in
/-- The shade of a translated shaded body has the same volume. -/
lemma volume_shade_translate (W : ShadedBody E) (v : E) :
    volume (W.translate v).shade = volume W.shade := by
  show volume ((v + ·) '' W.shade) = volume W.shade
  exact volume_image_add_left v W.shade

/-- The parent map of the pipeline output is the block map. -/
theorem thinPipeline_parent : (thinPipeline hδ₀ hdisc D hw₁).parent = blk :=
  ShadedBody.outerThickFamilyAtScale_parent _ hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁)

/-- The lower half of the enlargement sandwich. -/
theorem Wb_le_thinW (j : ω) : Wb j ≤ (thinW hδ₀ hdisc D hw₁ j).toConvexSpaceBody := by
  rw [thinW_toConvexSpaceBody]
  exact (Wb j).self_le_cthickening _

/-- The upper half of the enlargement sandwich, with equality. -/
theorem thinW_le_cthickening (j : ω) :
    (thinW hδ₀ hdisc D hw₁ j).toConvexSpaceBody ≤ (Wb j).cthickening (Wb j).scale :=
  le_of_eq (thinW_toConvexSpaceBody j)

/-- **Clause (vi) of `Kakeya.ThinCase.factoringApply`, at the honest pipeline loss.**

This is the mass half of `ShadedBody.outerThickFamilyAtScale_isCRefinement`, read back through
the translation. The loss is now the *weighted* pipeline's
`ShadedBody.factoringCoreAtScaleRefinementConstant` rather than
`ShadedBody.outerFactoringFamily_refinement.c`. -/
theorem thinRefinement_mass :
    ((ShadedBody.factoringCoreAtScaleUniformRefinementConstant (Module.finrank ℝ E)
          segs.card
          (ShadedBody.OuterInnerVolumeRatio.exponent D) w₁ : NNReal) : ENNReal)
        * ∑ p ∈ segs, volume (Y p).shade
      ≤ ∑ p ∈ thinSegs' hδ₀ hdisc D hw₁, volume (thinY' hδ₀ hdisc D hw₁ p).shade := by
  have h := (ShadedBody.outerThickFamilyAtScale_isCRefinement_of_lossBound
    (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁)
      (ShadedBody.FactoringAtScaleLossBound.uniform
        (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
          (thinPipeline_w₁_pos hδ₀ hw₁))).2
  have hl : ∑ p ∈ segs,
      volume ((thinFactorFamily segs Y bodies Wb blk z hblk hle).innerBody p).shade
        = ∑ p ∈ segs, volume (Y p).shade :=
    Finset.sum_congr rfl fun p _ => volume_shade_translate (Y p) (-z)
  have hr : ∑ p ∈ thinSegs' hδ₀ hdisc D hw₁, volume (thinY' hδ₀ hdisc D hw₁ p).shade
      = ∑ p ∈ (thinPipeline hδ₀ hdisc D hw₁).innerSet,
          volume ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).shade :=
    Finset.sum_congr rfl fun p _ => volume_shade_translate _ z
  rw [hr, ← hl]
  exact h

/-- **Clause (ii) of `Kakeya.ThinCase.factoringApply`**: every shaded point of a retained
segment is a shaded point of the outer body of its block, and that block is retained. -/
theorem thinShadingContainment {p : σ} (hp : p ∈ thinSegs' hδ₀ hdisc D hw₁) :
    blk p ∈ thinBodies' hδ₀ hdisc D hw₁ ∧
      (thinY' hδ₀ hdisc D hw₁ p).shade ⊆ (thinW hδ₀ hdisc D hw₁ (blk p)).shade := by
  have hmem := (thinPipeline hδ₀ hdisc D hw₁).parent_mem p hp
  rw [thinPipeline_parent] at hmem
  refine ⟨hmem, ?_⟩
  have hsub := (thinPipeline hδ₀ hdisc D hw₁).shade_subset_parent p hp
  rw [thinPipeline_parent] at hsub
  show (z + ·) '' ((thinPipeline hδ₀ hdisc D hw₁).innerBody p).shade ⊆
    (z + ·) '' ((thinPipeline hδ₀ hdisc D hw₁).outerBody (blk p)).shade
  exact Set.image_mono hsub

/-- The fibre of the pipeline output over a body is the block of retained segments. -/
theorem thinPipeline_fiber (j : ω) :
    (thinPipeline hδ₀ hdisc D hw₁).fiber j
      = (thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j) := by
  classical
  ext p
  simp [ShadedFactorFamily.fiber, thinSegs', thinPipeline_parent (hδ₀ := hδ₀) (hdisc := hdisc)
    (D := D) (hw₁ := hw₁)]

/-- **Clause (v) of `Kakeya.ThinCase.factoringApply`**, from
`ShadedBody.outerThickFamilyAtScale_outerShade_subset`, read back through the translation. -/
theorem thinW_shade_subset (j : ω) :
    (thinW hδ₀ hdisc D hw₁ j).shade ⊆
      Metric.cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
        (ShadedBody.iUnionShade ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
          (thinY' hδ₀ hdisc D hw₁)) := by
  classical
  have hscaleq : ((thinFactorFamily segs Y bodies Wb blk z hblk hle).outerBody j).scale
      = Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1) :=
    scale_translate (Wb j) (-z)
  have hsub : ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).shade ⊆
      Metric.cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
        (⋃ i ∈ (thinPipeline hδ₀ hdisc D hw₁).fiber j,
          ((thinPipeline hδ₀ hdisc D hw₁).innerBody i).shade) := by
    have := ShadedBody.outerThickFamilyAtScale_outerShade_subset
      (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁ (thinPipeline_w₁_pos hδ₀ hw₁) j
    rwa [hscaleq] at this
  show (z + ·) '' ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).shade ⊆ _
  refine (Set.image_mono hsub).trans ?_
  rw [cthickening_image_add_left]
  have himg : (z + ·) '' (⋃ i ∈ (thinPipeline hδ₀ hdisc D hw₁).fiber j,
        ((thinPipeline hδ₀ hdisc D hw₁).innerBody i).shade)
      ⊆ ShadedBody.iUnionShade ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
          (thinY' hδ₀ hdisc D hw₁) := by
    rw [thinPipeline_fiber]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨x, hxi, rfl⟩⟩
  exact fun x hx => Metric.cthickening_subset_of_subset _ himg hx

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Pointwise multiplicity is translation covariant. -/
lemma pointwiseMultiplicity_translate {ι : Type*} (t : Finset ι) (V : ι → ShadedBody E) (v x : E) :
    ShadedBody.pointwiseMultiplicity t (fun i => (V i).translate v) (v + x)
      = ShadedBody.pointwiseMultiplicity t V x := by
  classical
  show ({i ∈ t | (v + x) ∈ ((V i).translate v).shade}).card
    = ({i ∈ t | x ∈ (V i).shade}).card
  congr 1
  refine Finset.filter_congr (fun i _ => ?_)
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := add_left_cancel hyx
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **Clause (iii)(b) of `Kakeya.ThinCase.factoringApply`**: GWZ Item 4, transported back.

The weighted pipeline states it sharply — `ShadedBody.outerThickFamilyAtScale_fiber_multiplicity`
pins the fibre multiplicity to a single dyadic block `[2 ^ k, 2 ^ (k+1))` with `k` the
*weighted pipeline exponent*, the same `k` for every fibre. Reading `μinner := 2 ^ k` turns that
into the two-sided form the conjunct asks for, at the factor `2` the `hCcore2` binder pays for. -/
theorem thinInnerConstMult :
    ∃ μinner : NNReal, ∀ j ∈ thinBodies' hδ₀ hdisc D hw₁,
      ∀ x ∈ ShadedBody.iUnionShade ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
          (thinY' hδ₀ hdisc D hw₁),
        (ShadedBody.pointwiseMultiplicity
            ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
            (thinY' hδ₀ hdisc D hw₁) x : NNReal) ≤ 2 * μinner ∧
          μinner ≤ 2 * (ShadedBody.pointwiseMultiplicity
            ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j))
            (thinY' hδ₀ hdisc D hw₁) x : NNReal) := by
  classical
  set k : ℕ := (thinFactorFamily segs Y bodies Wb blk z hblk hle).weightedPipelineExponent
    hδ₀ hdisc D (w₁ : ℝ) (by exact_mod_cast thinPipeline_w₁_pos hδ₀ hw₁) with hk
  refine ⟨(2 : NNReal) ^ k, ?_⟩
  intro j hj x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨x₀, hx₀, rfl⟩ : ∃ x₀, x₀ ∈ ((thinPipeline hδ₀ hdisc D hw₁).innerBody i).shade ∧
      z + x₀ = x := hxi
  have hmem : x₀ ∈ ShadedBody.iUnionShade ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
      (thinPipeline hδ₀ hdisc D hw₁).innerBody := by
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hx₀⟩
    rw [thinPipeline_fiber]
    exact hi
  have hmult : ShadedBody.pointwiseMultiplicity
      ((thinSegs' hδ₀ hdisc D hw₁).filter (fun p => blk p = j)) (thinY' hδ₀ hdisc D hw₁) (z + x₀)
      = ShadedBody.pointwiseMultiplicity ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
          (thinPipeline hδ₀ hdisc D hw₁).innerBody x₀ := by
    rw [thinPipeline_fiber]
    exact pointwiseMultiplicity_translate _ _ z x₀
  rw [hmult]
  obtain ⟨hlow, hhigh⟩ := ShadedBody.outerThickFamilyAtScale_fiber_multiplicity
    (F := thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁) hmem
  set m : ℕ := ShadedBody.pointwiseMultiplicity ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
    (thinPipeline hδ₀ hdisc D hw₁).innerBody x₀ with hm
  have hlow' : 2 ^ k ≤ m := hlow
  have hhigh' : m < 2 ^ (k + 1) := hhigh
  constructor
  · have : m ≤ 2 * 2 ^ k := by
      have : m < 2 * 2 ^ k := by simpa [pow_succ, two_mul, Nat.mul_comm] using hhigh'
      exact this.le
    calc ((m : ℕ) : NNReal) ≤ ((2 * 2 ^ k : ℕ) : NNReal) := by exact_mod_cast this
      _ = 2 * (2 : NNReal) ^ k := by push_cast; ring
  · calc (2 : NNReal) ^ k = ((2 ^ k : ℕ) : NNReal) := by push_cast; ring
      _ ≤ ((m : ℕ) : NNReal) := by exact_mod_cast hlow'
      _ ≤ 2 * ((m : ℕ) : NNReal) := by
          nth_rewrite 1 [← one_mul (((m : ℕ) : NNReal))]
          gcongr <;> norm_num

/-- **Conjunct (i) of `Kakeya.ThinCase.factoringApply`, in summed form.**

This is `ShadedBody.outerThickFamilyAtScale_fullness` — the aggregate Córdoba estimate of the
*weighted* pipeline — transported back through the translation by `+z`. It is the whole of
conjunct (i)'s content, and it is the single reason for moving `Kakeya.ThinCase.thinPipeline` onto
`ShadedBody.outerThickFamilyAtScale`: the unweighted `ShadedBody.outerFactoringFamily` has no such
estimate, and reconstructing one by hand runs into a per-block retention obstruction that the
weighted pipeline simply does not have.

The exponent it delivers is `2 η`, not `3 η`: with `hfullness : δ ^ η ≤ Cfull * fullness segs Y`
the squared `fullness segs Y` on the left turns directly into `δ ^ (2 * η)`. Conjunct (i) asks for
`δ ^ (3 * η)`, which is *weaker* — but deducing it needs `δ ^ (3 * η) ≤ δ ^ (2 * η)`, i.e. `0 ≤ η`,
which is true at every call site and is **not** among `factoringApply`'s binders. See the note in
`Kakeya/DimensionThree/MainLemma2/ThinAssembly.lean`. -/
theorem thinFullness_sum (hdim : Module.finrank ℝ E = 3)
    (hshape : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerHasSimilarShape 2)
    {CF : ENNReal}
    (hFrostman : (thinFactorFamily segs Y bodies Wb blk z hblk hle).HasFrostmanFibers CF) :
    (ShadedBody.factoringCoreAtScaleFullnessConstant
        (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
          (thinPipeline_w₁_pos hδ₀ hw₁) : ENNReal) * CF⁻¹ *
        (ShadedBody.fullness segs Y : ENNReal) ^ 2 *
          (∑ j ∈ thinBodies' hδ₀ hdisc D hw₁, volume (thinW hδ₀ hdisc D hw₁ j).carrier)
      ≤ ∑ j ∈ thinBodies' hδ₀ hdisc D hw₁, volume (thinW hδ₀ hdisc D hw₁ j).shade := by
  have hbase := ShadedBody.outerThickFamilyAtScale_fullness
    (F := thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁) hdim hshape hFrostman
  have hin : (ShadedBody.fullness
      (thinFactorFamily segs Y bodies Wb blk z hblk hle).innerSet
      (thinFactorFamily segs Y bodies Wb blk z hblk hle).innerBody : ENNReal)
      = (ShadedBody.fullness segs Y : ENNReal) := by
    rw [ShadedBody.fullness_def, ShadedBody.fullness_def]
    congr 1
    · exact Finset.sum_congr rfl fun p _ => volume_shade_translate (Y p) (-z)
    · exact Finset.sum_congr rfl fun p _ => by
        show volume (((Y p).translate (-z)).toConvexSpaceBody).carrier = volume (Y p).carrier
        rw [toConvexSpaceBody_translate]
        exact Kakeya.volume_translate (Y p).toConvexSpaceBody (-z)
  have hcar : ∑ j ∈ thinBodies' hδ₀ hdisc D hw₁, volume (thinW hδ₀ hdisc D hw₁ j).carrier
      = ∑ j ∈ (thinPipeline hδ₀ hdisc D hw₁).outerSet,
          volume ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).carrier :=
    Finset.sum_congr rfl fun j _ => by
      show volume ((((thinPipeline hδ₀ hdisc D hw₁).outerBody j).translate z).toConvexSpaceBody).carrier = _
      rw [toConvexSpaceBody_translate]
      exact Kakeya.volume_translate _ z
  have hsh : ∑ j ∈ thinBodies' hδ₀ hdisc D hw₁, volume (thinW hδ₀ hdisc D hw₁ j).shade
      = ∑ j ∈ (thinPipeline hδ₀ hdisc D hw₁).outerSet,
          volume ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).shade :=
    Finset.sum_congr rfl fun j _ => volume_shade_translate _ z
  rw [hcar, hsh, ← hin]
  exact hbase

/-- **The outer body of the weighted pipeline IS the induced shading of its own fibre.**

`ShadedBody.productiveThickBody` is *defined* as `ShadedBody.inducedShading` of the productive
fibre, so this is the two rewrites that expose it through `ShadedBody.outerThickFamilyAtScale`.

It is the missing link of conjunct (i)'s last step. `Kakeya.ThinCase.thinFullness_sum` bounds the
fullness of `Kakeya.ThinCase.thinW`, the pipeline's own outer family, while
`Kakeya.ThinCase.exists_factoringApplyData` returns the *cell* shading; the transport between them
is `Kakeya.ThinCase.sum_volume_inducedShading_le_mul_sum_volume_cellShade` followed by
`Kakeya.ThinCase.fullness_cellShading_ge`, whose `hcar` holds on the nose because both carriers are
`(Wb j).cthickening (Wb j).scale`. That transport is stated for an `inducedShading`, which is what
this lemma supplies. -/
theorem thinPipeline_outerBody_eq_inducedShading (j : ω) :
    (thinPipeline hδ₀ hdisc D hw₁).outerBody j
      = ShadedBody.inducedShading ((thinPipeline hδ₀ hdisc D hw₁).fiber j)
          (thinPipeline hδ₀ hdisc D hw₁).innerBody
          ((thinFactorFamily segs Y bodies Wb blk z hblk hle).outerBody j) := by
  unfold thinPipeline
  rw [ShadedBody.outerThickFamilyAtScale, ShadedBody.productiveThickFamily_fiber_eq,
    ShadedBody.productiveThickFamily_innerBody]
  rfl

/-- **GWZ 9.5 equation (95), per block.**

GWZ applies Proposition 5.1 and reads the retention off as a *conclusion*:
`λ(W'_B, Y_{W'_B}) ⪆ δ^{2η}`. Our rendering proves it in two forms, and the **per-block** one is
`ShadedBody.outerThickFamilyAtScale_blockFullness`; this is its transport through the translation
by `+z`.

The per-block form is what matters here. The aggregate form
(`Kakeya.ThinCase.thinFullness_sum`) is a single inequality between two sums over the whole
retained body set, so restricting it to a subfamily cuts the numerator *and* the denominator and
does not transfer. The per-block form restricts to **any** subfamily for free — in particular to
the `Kakeya.ThinCase.exists_factoringApplyData` shrink `{j ∈ b₁ | (A j ∩ reg).Nonempty}` — because
it is a separate inequality at each `j`.

`ShadedBody.finalFiberFullnessAtScale` is the density of the *final* shading in the *complete
original* fibre, so this is a genuine per-fibre retention statement and not a restatement of the
input hypothesis. -/
theorem thinBlockFullness (hdim : Module.finrank ℝ E = 3)
    (hshape : (thinFactorFamily segs Y bodies Wb blk z hblk hle).InnerHasSimilarShape 2)
    {CF : ENNReal}
    (hFrostman : (thinFactorFamily segs Y bodies Wb blk z hblk hle).HasFrostmanFibers CF) :
    ∀ j ∈ thinBodies' hδ₀ hdisc D hw₁,
      CF⁻¹ * (ShadedBody.finalFiberFullnessAtScale
            (thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
            (thinPipeline_w₁_pos hδ₀ hw₁) j : ENNReal) ^ 2 *
          volume (thinW hδ₀ hdisc D hw₁ j).carrier
        ≤ (ShadedBody.lambdaInducedSingleWUniform.C : ENNReal) *
            ((ShadedBody.OuterInnerVolumeRatio.exponent D : ENNReal) + 1) *
          volume (thinW hδ₀ hdisc D hw₁ j).shade := by
  intro j hj
  have hbase := ShadedBody.outerThickFamilyAtScale_blockFullness
    (F := thinFactorFamily segs Y bodies Wb blk z hblk hle) hδ₀ hdisc D w₁
      (thinPipeline_w₁_pos hδ₀ hw₁) hdim hshape hFrostman j hj
  have hcar : volume (thinW hδ₀ hdisc D hw₁ j).carrier
      = volume ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).carrier := by
    show volume ((((thinPipeline hδ₀ hdisc D hw₁).outerBody j).translate z).toConvexSpaceBody).carrier = _
    rw [toConvexSpaceBody_translate]
    exact Kakeya.volume_translate _ z
  have hsh : volume (thinW hδ₀ hdisc D hw₁ j).shade
      = volume ((thinPipeline hδ₀ hdisc D hw₁).outerBody j).shade :=
    volume_shade_translate _ z
  rw [hcar, hsh]
  exact hbase

end Pipeline

/-! ### The step-1 gate: `le_scale` is not derivable

The construction above takes `hscale` as a hypothesis. This section shows, by counterexample,
that it has to: no hypothesis of `Kakeya.ThinCase.factoringApply` bounds the affine thickness of
a segment from *below*. -/

section Gate

open scoped NNReal

/-- The three-dimensional model space used by the counterexample. -/
abbrev GateE3 := EuclideanSpace ℝ (Fin 3)

lemma finrank_GateE3 : Module.finrank ℝ GateE3 = 3 := by simp

/-- **The step-1 gate, as a `Prop`.**

Every hypothesis of `Kakeya.ThinCase.factoringApply` (in its repaired, `hloc`-carrying form),
followed by the `le_scale` field of `ShadedBody.FactorFamily.InnerIsDiscretizedAtScale δ` for the
inner family `(segs, Y)`.  If this were provable, no new binder would be needed. -/
def LeScaleDerivable : Prop :=
  ∀ {σ ω : Type} [DecidableEq ω] (segs : Finset σ) (Y : σ → ShadedBody GateE3)
    (bodies : Finset ω) (Wb : ω → ConvexSpaceBody GateE3) (blk : σ → ω)
    {δ w₁ : NNReal} {η : ℝ} {CF Cfull Ccore : NNReal},
    0 < δ → δ ≤ w₁ → w₁ ≤ 1 → 1 ≤ CF →
    2 ≤ Ccore →
    (ShadedBody.outerFactoringFamily_refinement.c 3 segs.card δ)⁻¹ ≤ Ccore →
    ShadedBody.outerFactoringFamily_outerConstMultFat.c 3 bodies.card δ ≤ Ccore →
    ((Nat.log 2 bodies.card + 1 : ℕ) : NNReal) ≤ Ccore →
    ((Nat.log 2 ⌈CF⌉₊ + 1 : ℕ) : NNReal) ≤ Ccore →
    (∀ p ∈ segs, blk p ∈ bodies) →
    (∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)) →
    (∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier) →
    (∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn (segs.filter fun p => blk p = j)
      (fun p => (Y p).toConvexSpaceBody) (Wb j) CF) →
    (∀ j ∈ bodies,
      Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ GateE3 - 1) ≤ 2 * w₁ ∧
        (w₁ : ℝ) ≤ 2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ GateE3 - 1)) →
    (∃ z : GateE3, ∀ j ∈ bodies, (Wb j).carrier ⊆ Metric.closedBall z 1) →
    (∀ p ∈ segs,
      (δ : ENNReal) ^ η * volume (Y p).carrier ≤ (Cfull : ENNReal) * volume (Y p).shade) →
    ((δ : ENNReal) ^ η ≤ (Cfull : ENNReal) * (fullness segs Y : ENNReal)) →
    ∀ p ∈ segs, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (Y p).carrier

/-- The body used both as the single segment and as the single factoring body. -/
noncomputable def qball : ConvexSpaceBody GateE3 := ConvexSpaceBody.closedBall 0 (1/4) (by norm_num)

@[simp] lemma qball_carrier : qball.carrier = Metric.closedBall (0 : GateE3) (1/4) := rfl

noncomputable def qseg : ShadedBody GateE3 where
  toConvexSpaceBody := qball
  shade := Metric.closedBall (0 : GateE3) (1/4)
  measurableSet_shade := measurableSet_closedBall
  shade_subset := le_rfl

@[simp] lemma qseg_carrier : (qseg).carrier = Metric.closedBall (0 : GateE3) (1/4) := rfl
@[simp] lemma qseg_shade : (qseg).shade = Metric.closedBall (0 : GateE3) (1/4) := rfl
@[simp] lemma qseg_body : (qseg).toConvexSpaceBody = qball := rfl

lemma volume_qball_pos : 0 < volume (Metric.closedBall (0 : GateE3) (1/4)) :=
  Metric.measure_closedBall_pos volume 0 (by norm_num)

lemma volume_qball_ne_top : volume (Metric.closedBall (0 : GateE3) (1/4)) ≠ ⊤ :=
  (measure_closedBall_lt_top).ne

/-- The single-segment family is `1`-Frostman in the body, which is the segment itself. -/
lemma frostman_qseg :
    ConvexSpaceBody.IsFrostmanIn (({()} : Finset Unit)) (fun _ => qball) qball 1 := by
  classical
  intro K' hK'
  have hden : densityIn ({()} : Finset Unit) (fun _ => qball) qball = 1 := by
    rw [densityIn_of_all_le (fun i _ => le_rfl)]
    simp only [Finset.sum_singleton]
    exact ENNReal.div_self volume_qball_pos.ne' volume_qball_ne_top
  rw [hden, mul_one]
  by_cases hle : qball ≤ K'
  · rw [densityIn_of_all_le (fun i _ => hle)]
    simp only [Finset.sum_singleton]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    exact measure_mono (show (qball).carrier ⊆ K'.carrier from hle)
  · have hempty : ({i ∈ ({()} : Finset Unit) | (fun _ => qball) i ≤ K'}) = ∅ := by
      ext i; simp [hle]
    have : densityIn ({()} : Finset Unit) (fun _ => qball) K' = 0 := by
      unfold densityIn
      rw [hempty, Finset.sum_empty, ENNReal.zero_div]
    rw [this]
    exact zero_le_one

lemma fullness_qseg : (fullness ({()} : Finset Unit) (fun _ => qseg) : ENNReal) = 1 := by
  rw [ShadedBody.coe_fullness]
  show (∑ i ∈ ({()} : Finset Unit), volume (qseg).shade) /
    (∑ i ∈ ({()} : Finset Unit), volume (qseg).carrier) = 1
  simp only [Finset.sum_singleton, qseg_shade, qseg_carrier]
  exact ENNReal.div_self volume_qball_pos.ne' volume_qball_ne_top

/-- **Step-1 gate outcome: `le_scale` is NOT derivable from the hypotheses of
`Kakeya.ThinCase.factoringApply`.**

The hypotheses bound the affine thicknesses of the segments only from *above* — `hle` puts each
segment inside its body and `hdims` compares segments with each other — so a segment may be an
arbitrarily small ball inside its body.  Here the single segment *is* its body, a ball of radius
`1/4`, while `δ = w₁ = 1/2`. -/
theorem le_scale_not_derivable : ¬ LeScaleDerivable := by
  intro H
  have hfr : Module.finrank ℝ GateE3 = 3 := finrank_GateE3
  obtain ⟨hc2, hcref, hcmult, hcdyad⟩ :=
    Kakeya.ThinCase.factoringApplyCore_spec 3 1 1 (1/2 : NNReal)
  have hcard : ({()} : Finset Unit).card = 1 := rfl
  have hone : (1 : NNReal) ≤ Kakeya.ThinCase.factoringApplyCore 3 1 1 (1/2 : NNReal) :=
    Kakeya.ThinCase.one_le_factoringApplyCore 3 1 1 (1/2 : NNReal)
  have hmain := H (σ := Unit) (ω := Unit) ({()} : Finset Unit) (fun _ => qseg)
      ({()} : Finset Unit) (fun _ => qball) (fun _ => ())
      (δ := (1/2 : NNReal)) (w₁ := (1/2 : NNReal)) (η := (0 : ℝ))
      (CF := 1) (Cfull := 1)
      (Ccore := Kakeya.ThinCase.factoringApplyCore 3 1 1 (1/2 : NNReal))
      (by norm_num) le_rfl (by norm_num) le_rfl
      hc2 (by rw [hcard]; exact hcref) (by rw [hcard]; exact hcmult)
      (by rw [hcard]; exact hcdyad)
      (by simpa using hone)
      (fun p _ => Finset.mem_singleton_self ())
      (fun p _ => le_rfl)
      (fun p _ q _ k => by
        simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
        linarith [Metric.thickness_nonneg (𝕜 := ℝ) (qseg).carrier k])
      (fun j _ => frostman_qseg)
      (fun j _ => by
        refine ⟨?_, ?_⟩
        · have h : Metric.thickness ℝ (Metric.closedBall (0 : GateE3) (1/4))
              (Module.finrank ℝ GateE3 - 1) ≤ (1/4 : ℝ) :=
            Metric.thickness_le_of_subset_closedBall (x := (0 : GateE3)) le_rfl (by norm_num) _
          have : ((1:NNReal)/2 : ℝ) = 1/2 := by norm_num
          simp only [qball_carrier, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
          linarith
        · have h := Metric.thickness_closedBall_ge (x := (0 : GateE3)) (r := (1/4 : ℝ))
            (by norm_num) (k := Module.finrank ℝ GateE3 - 1) (by omega)
          simp only [qball_carrier, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
          linarith)
      ⟨0, fun j _ => by
        simpa using Metric.closedBall_subset_closedBall (α := GateE3) (by norm_num : (1/4 : ℝ) ≤ 1)⟩
      (fun p _ => by simp)
      (by rw [ENNReal.rpow_zero, fullness_qseg]; simp)
      () (Finset.mem_singleton_self ())
  have hle : Metric.ethickness.scale ℝ (qseg).carrier ≤ ((1/4 : NNReal) : ENNReal) := by
    refine le_trans (Metric.ethickness.scale_le (𝕜 := ℝ) _ (n := 0) (by omega)) ?_
    simpa using Metric.ethickness_closedBall_le (𝕜 := ℝ) (x := (0 : GateE3)) (1/4 : NNReal) 0
  have hbad : (((1/2 : NNReal)) : ENNReal) ≤ (((1/4 : NNReal)) : ENNReal) := le_trans hmain hle
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hbad
  norm_num at hbad

end Gate

end Kakeya.ThinCase
