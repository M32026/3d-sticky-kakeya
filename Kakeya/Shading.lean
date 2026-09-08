/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Scale
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
In this file we define the structure `ShadedBody`.
-/

@[expose] public section

open Module Metric MeasureTheory Convexity

/-- A shaded body is the data of a convex body and a measurable subset of it, called shading. -/
structure ShadedBody (E : Type*) [TopologicalSpace E] [MeasurableSpace E]
    [ConvexSpace ℝ E]
    extends ConvexSpaceBody E where
  /-- Shading -/
  shade : Set E
  /-- Shading is measurable -/
  measurableSet_shade : MeasurableSet shade
  /-- Shading is a subset of the carrier -/
  shade_subset : shade ⊆ carrier

namespace ShadedBody

/-- `U(𝒱, Y)` from [GWZ, Eq (4)]: the union `⋃_{W ∈ 𝒱} Y(W)` of the shadings of a
shaded family `(𝒱, Y)`. -/
abbrev iUnionShade {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) : Set E :=
  ⋃ i ∈ s, (V i).shade

section RestrictShade

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]

/-- **Restriction of a shading to a measurable set** (blueprint `def:restrictShade`): the shaded
body with the same carrier as `W` and with shade `W.shade ∩ S`.

This packages a pattern written out inline several times in the development, the Step 3 inner body
`ShadedBody.step3InnerBody` being one occurrence; the existing call sites are left as they are. -/
def restrictShade (W : ShadedBody E) (S : Set E) (hS : MeasurableSet S) : ShadedBody E where
  toConvexSpaceBody := W.toConvexSpaceBody
  shade := W.shade ∩ S
  measurableSet_shade := W.measurableSet_shade.inter hS
  shade_subset := fun _ hx ↦ W.shade_subset hx.1

@[simp]
theorem toConvexSpaceBody_restrictShade (W : ShadedBody E) (S : Set E) (hS : MeasurableSet S) :
    (W.restrictShade S hS).toConvexSpaceBody = W.toConvexSpaceBody := by
  rfl

@[simp]
theorem shade_restrictShade (W : ShadedBody E) (S : Set E) (hS : MeasurableSet S) :
    (W.restrictShade S hS).shade = W.shade ∩ S := by
  rfl

/-- Restricting a shade to a closed set preserves closedness of the shade. -/
theorem isClosed_shade_restrictShade {W : ShadedBody E} {S : Set E}
    (hS : MeasurableSet S) (hW : IsClosed W.shade) (hSclosed : IsClosed S) :
    IsClosed (W.restrictShade S hS).shade := by
  rw [shade_restrictShade]
  exact hW.inter hSclosed

/-- **Restriction commutes with the shaded union** (blueprint `lem:iUnionShadeRestrictShade`):
restricting every shade of a family to `S` intersects the shaded union with `S`. -/
theorem iUnionShade_restrictShade {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) (S : Set E)
    (hS : MeasurableSet S) :
    iUnionShade s (fun i ↦ (V i).restrictShade S hS) = iUnionShade s V ∩ S := by
  ext x
  simp [iUnionShade, shade_restrictShade]
  tauto

end RestrictShade

end ShadedBody

/-- A shaded δ-tube is a δ-tube with a shading. -/
structure ShadedTube (δ : NNReal) (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [MeasurableSpace E] extends Tube δ E, ShadedBody E

attribute [nolint docBlame] ShadedTube.toShadedBody

namespace ShadedBody

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E]
  {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)

/-- `fullness` as `ENNReal`, used to define fullness. -/
noncomputable abbrev fullness' (s : Finset ι) (V : ι → ShadedBody E) : ENNReal :=
  (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)

/-- `fullness s V` is as most 1 -/
theorem fullness'_le_one (s : Finset ι) (V : ι → ShadedBody E) : fullness' s V ≤ 1 := by
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact Finset.sum_le_sum (fun i _ ↦ measure_mono (V i).shade_subset)

lemma fullness'_ne_top (s : Finset ι) (V : ι → ShadedBody E) : fullness' s V ≠ ⊤ :=
  fun h ↦ by simpa [h] using fullness'_le_one s V

/-- λ defined in [GWZ, Eq (5)] -/
noncomputable abbrev fullness (s : Finset ι) (V : ι → ShadedBody E) : NNReal :=
  (fullness' s V).toNNReal

lemma coe_fullness (s : Finset ι) (V : ι → ShadedBody E) : fullness s V = fullness' s V :=
  ENNReal.coe_toNNReal (fullness'_ne_top s V)

theorem fullness_def (s : Finset ι) (V : ι → ShadedBody E) :
    fullness s V = (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) :=
  coe_fullness s V

theorem fullness_le_one (s : Finset ι) (V : ι → ShadedBody E) : fullness s V ≤ 1 :=
  ENNReal.coe_le_coe.1 <| coe_fullness s V ▸ fullness'_le_one s V

-- TODO collect here lemmas (like those in Density.lean) about fullness
/-
@[simp]
theorem fullness_empty : fullness ∅ V = 0 := by
  simp
-/

/-- Total shading volume is `fullness s V` times total volume -/
theorem sum_volumeReal_shade_eq_fullness_mul [IsFiniteMeasureOnCompacts (volume : Measure E)] :
    ∑ i ∈ s, volume (V i).shade = fullness s V * ∑ i ∈ s, volume (V i).carrier := by
  rw [fullness_def, ENNReal.div_mul_cancel' (eq_bot_mono (Finset.sum_le_sum fun i _ ↦
    measure_mono (V i).shade_subset))]
  exact fun h ↦ False.elim <| (V (ENNReal.sum_eq_top.1 h).choose).1.3.measure_ne_top
    (ENNReal.sum_eq_top.1 h).choose_spec.2

/-- A lower bound on the fullness and a uniform lower bound on the carrier volumes give a
lower bound on the total shading volume. -/
theorem coe_fullness_mul_le_sum_volume_shade [IsFiniteMeasureOnCompacts (volume : Measure E)]
    {a : NNReal} {c : ENNReal} (h : a ≤ fullness s V)
    (hc : ∀ i ∈ s, c ≤ volume (V i).carrier) :
    (a : ENNReal) * (s.card * c) ≤ ∑ i ∈ s, volume (V i).shade := by
  rw [sum_volumeReal_shade_eq_fullness_mul s V, ← nsmul_eq_mul]
  exact mul_le_mul' (ENNReal.coe_le_coe.mpr h) (Finset.card_nsmul_le_sum s _ c hc)

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  (s : Finset ι)
  (V : ι → ShadedBody E)
  (W : ConvexSpaceBody E)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Shaded unions are bounded** (blueprint `lem:isBoundedIUnionShade`): each shade lies in the
compact carrier of its body, and a finite union of bounded sets is bounded. -/
theorem isBounded_iUnionShade : Bornology.IsBounded (iUnionShade s V) := by
  rw [Bornology.isBounded_biUnion_finset]
  intro i hi
  exact (V i).isCompact'.isBounded.subset (V i).shade_subset

/-- The shading induced by a family on the controlled enlargement of an outer body, as adapted
from [GWZ, Definition 5.7]. If `r` is the shortest affine thickness of `W`, its carrier is
`N_r(W)` and its shade is `N_{2r}(U(𝒱, Y)) ∩ N_r(W)`.

**Why the shading radius is `2 r` and not GWZ's `r`, which is a real constraint and not a choice.**
GWZ Definition 5.7 and Remark 5.4 both give `Y_W(W) = W ∩ N_{w₁}(U(V_W, Y_V))` with `w₁` the
shortest dimension of `W`, and GWZ 9.5 reads it identically ("the a-neighborhood"). In GWZ the
Proposition 5.1 scale parameter and each body's own shortest dimension are the *same* symbol `w₁`.
Here they are **two different quantities**, related only by
`ShadedBody.FactorFamily.OuterIsAtScale 2 w₁`, which gives `w₁ / 2 ≤ W.scale ≤ 2 * w₁` — a
factor-`2` slack in both directions.

That slack is what the `2` pays for. Narrowing the radius to `r` was tried: the Córdoba chain of
`Kakeya/DimensionThree/InducedShading.lean` survives it (the lifted union there is thickened at
`r / 2`, so it fits at `r` too), but
`ShadedBody.outerFactoringFamily_local_balls` in `Kakeya/Factoring/Multiplicity.lean` does not:
it places a point `w` with `dist w y < w₁` — `w₁` being the *cover ball's* radius, i.e. the
pipeline scale — into the outer shade of `y`'s block, so the collar must have radius at least `w₁`,
while GWZ's radius `W.scale` is only guaranteed to be `≥ w₁ / 2`. The shortfall is exactly a factor
`2`, attained when `W.scale = w₁ / 2`.

So removing the `2` requires tightening `OuterIsAtScale 2 w₁` to `OuterIsAtScale 1 w₁`
(`W.scale = w₁`, GWZ's own convention) rather than editing this definition. **The cost of keeping
it** is that the outer multiplicity decouples from the count of GWZ Proposition 5.1 item (iii),
which is taken over `B(x, w₁)`: a shade at radius `2 * W.scale` can reach `4 w₁`, leaving a fringe
of outer multiplicity `1`, which is why item (3) is not available for this family at an absolute
constant. -/
noncomputable def inducedShading : ShadedBody E :=
  let r := W.scale
  { toConvexSpaceBody := W.cthickening r
    shade := Metric.cthickening (2 * r) (⋃ i ∈ s, (V i).shade) ∩ Metric.cthickening r W.carrier
    measurableSet_shade :=
      isClosed_cthickening.measurableSet.inter isClosed_cthickening.measurableSet
    shade_subset := Set.inter_subset_right }

theorem toConvexSpaceBody_inducedShading :
    (inducedShading s V W).toConvexSpaceBody =
      W.cthickening W.scale := by
  rfl

theorem shade_inducedShading : (inducedShading s V W).shade =
    Metric.cthickening (2 * W.scale)
      (⋃ i ∈ s, (V i).shade) ∩ Metric.cthickening W.scale W.carrier :=
  rfl

/-- If every body of the family `(𝒱, Y)` lies in `W`, then the `τ_{n-1}(W)`-thickening of the
shaded union `U(𝒱, Y)` is contained in the shading induced on the enlargement of `W`.

The two containments are the radius comparison `τ_{n-1}(W) ≤ 2 τ_{n-1}(W)`, which uses
`Metric.thickness_nonneg`, and `U(𝒱, Y) ⊆ W`, which uses `ShadedBody.shade_subset`. -/
theorem cthickening_scale_iUnionShade_subset_shade_inducedShading
    (hVW : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ W) :
    Metric.cthickening W.scale (iUnionShade s V) ⊆ (inducedShading s V W).shade := by
  have hWscale_nonneg : 0 ≤ W.scale := by
    dsimp [ConvexSpaceBody.scale]
    exact Metric.thickness_nonneg _ _
  have hU_sub : iUnionShade s V ⊆ W.carrier := by
    change ⋃ i ∈ s, (V i).shade ⊆ W.carrier
    apply Set.iUnion₂_subset
    intro i hi
    apply (V i).shade_subset.trans
    exact (SetLike.coe_subset_coe.mpr (hVW i hi))
  rw [ShadedBody.shade_inducedShading]
  intro x hx
  exact ⟨Metric.cthickening_mono (by nlinarith [hWscale_nonneg]) _ hx,
    Metric.cthickening_subset_of_subset W.scale hU_sub hx⟩

open Classical in
/-- **The blockwise induced shadings dominate the shaded union** (adapted from [GWZ,
Definition 5.7]). Let `(𝒱, Y)` be a finite family of shaded bodies indexed by `s`, let `𝒲` be a
finite family of convex bodies indexed by `t`, and let `p : ι → κ` send `s` into `t` with
`V i ≤ W (p i)` for `i ∈ s`. Shading each enlargement `Ñ_{r j}(W j)` by the shading induced by the
fiber `{i ∈ s | p i = j}` gives `U(𝒱, Y) ⊆ U(𝒲̃, Y_𝒲̃)`.

Stated in unbundled form, so that it also applies to families that are not packaged as a
`ShadedBody.FactorFamily` (whose declaration depends on this file). -/
theorem iUnionShade_subset_iUnionShade_inducedShading {κ : Type*} (t : Finset κ)
    (Wout : κ → ConvexSpaceBody E) (p : ι → κ) (hp : ∀ i ∈ s, p i ∈ t)
    (hVW : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ Wout (p i)) :
    iUnionShade s V ⊆
      iUnionShade t (fun j ↦ inducedShading {i ∈ s | p i = j} V (Wout j)) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hi, hxi⟩
  rw [Set.mem_iUnion₂]
  refine ⟨p i, hp i hi, ?_⟩
  rw [shade_inducedShading]
  constructor
  · apply Metric.self_subset_cthickening
    rw [Set.mem_iUnion₂]
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩, hxi⟩
  · exact Metric.self_subset_cthickening (Wout (p i)).carrier
      (SetLike.coe_subset_coe.mp (hVW i hi) ((V i).shade_subset hxi))

end ShadedBody

namespace ShadedBody
variable
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E]

open scoped Pointwise in
/-- Translation `v +ᵥ W` of a shaded body `W` by a vector `v`, translating both the
underlying convex body and its shade. -/
@[simps!]
def vadd (W : ShadedBody E) (v : E) : ShadedBody E where
  toConvexSpaceBody := W.toConvexSpaceBody.vadd v
  shade := v +ᵥ W.shade
  measurableSet_shade := (measurableEmbedding_addLeft v).measurableSet_image' W.measurableSet_shade
  shade_subset := Set.image_mono W.shade_subset

/-- Translation of a shaded body by a vector. -/
@[simps!]
def translate (W : ShadedBody E) (v : E) : ShadedBody E where
  __ := W.vadd v
  shade := (v + ·) '' W.shade
  measurableSet_shade := (measurableEmbedding_addLeft v).measurableSet_image' W.measurableSet_shade
  shade_subset := Set.image_mono W.shade_subset

end ShadedBody

namespace ShadedTube

variable
  {δ : NNReal}
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E]

open scoped Pointwise in
/-- Translation `v +ᵥ S` of a shaded `δ`-tube `S` by a vector `v`, translating both the
underlying tube and its shade. -/
@[simps!]
def vadd (S : ShadedTube δ E) (v : E) : ShadedTube δ E where
  toTube := S.toTube.vadd v
  shade := v +ᵥ S.shade
  measurableSet_shade := (measurableEmbedding_addLeft v).measurableSet_image' S.measurableSet_shade
  shade_subset := Set.image_mono S.shade_subset

/-- Translation of a shaded `δ`-tube by a vector. -/
@[simps!]
def translate (S : ShadedTube δ E) (v : E) : ShadedTube δ E where
  __ := S.vadd v
  shade := (v + ·) '' S.shade
  measurableSet_shade := (measurableEmbedding_addLeft v).measurableSet_image' S.measurableSet_shade
  shade_subset := Set.image_mono S.shade_subset

end ShadedTube

namespace ShadedBody

section TranslationInvariance

open MeasureTheory

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Fullness is invariant under per-body translations. -/
lemma fullness_translate {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) (v : ι → E) :
    fullness s (fun i => (V i).translate (v i)) = fullness s V := by
  rw [← ENNReal.coe_inj, fullness_def, fullness_def]
  congr! 2 <;> simp

/-- Fullness is invariant under translation by a single constant vector. -/
lemma fullness_translate_const {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) (v : E) :
    fullness s (fun i => (V i).translate v) = fullness s V :=
  fullness_translate s V (fun _ => v)

end TranslationInvariance

section Refinement

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  (s' : Finset ι) (V' : ι → ShadedBody E) (s : Finset ι) (V : ι → ShadedBody E)

/--
We say that $(\VV', Y')$ is a refinement of $(\VV, Y)$
if $\VV'\subset\VV$ and $Y'(V) \subset Y(V)$ for each $V \in \VV'$.
-/
def IsRefinement : Prop :=
  s' ⊆ s ∧ ∀ i ∈ s', (V' i).toConvexSpaceBody = (V i).toConvexSpaceBody ∧ (V' i).shade ⊆ (V i).shade

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Restricting the shades is a refinement** (blueprint `lem:isRefinementRestrictShade`): the
index set and the carriers are unchanged and the shades shrink. -/
theorem isRefinement_restrictShade (S : Set E) (hS : MeasurableSet S) :
    IsRefinement s (fun i ↦ (V i).restrictShade S hS) s V := by
  constructor
  · exact Finset.Subset.refl s
  · intro i hi
    constructor
    · rfl
    · intro x hx
      exact hx.1

/-- **The induced shading is monotone under refinement**: refining the shading family shrinks
the shading it induces on the enlargement of a fixed convex body `W`.

Only the two clauses `s' ⊆ s` and `Y' i ⊆ Y i` of `ShadedBody.IsRefinement` are used; the
carrier-equality clause does not enter. The carriers of the two induced bodies are moreover equal,
both being `Ñ_{τ_{n-1}(W)}(W)`, which holds by `rfl` and is therefore not recorded as a separate
declaration. -/
theorem shade_inducedShading_mono_of_isRefinement (W : ConvexSpaceBody E)
    (h : IsRefinement s' V' s V) :
    (inducedShading s' V' W).shade ⊆ (inducedShading s V W).shade := by
  rw [shade_inducedShading, shade_inducedShading]
  rcases h with ⟨hs's, hineq⟩
  apply Set.inter_subset_inter_left
  exact Metric.cthickening_subset_of_subset (2 * W.scale) (by
    apply Set.iUnion₂_subset
    intro i hi
    exact Set.subset_iUnion₂_of_subset i (hs's hi) (hineq i hi).2)

end Refinement

section CRefinement

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  (s' : Finset ι) (V' : ι → ShadedBody E) (s : Finset ι) (V : ι → ShadedBody E)

/--
For $c>0$, we say that $(\VV', Y')$ is a $c$-refinement of $(\VV,Y)$
if $\sum_{\VV'}|Y'(V)|\geq c \sum_{\VV}|Y(V)|$.
-/
def IsCRefinement (c : NNReal) : Prop :=
  IsRefinement s' V' s V ∧
  c * ∑ i ∈ s, volume (V i).shade ≤ ∑ i ∈ s', volume (V' i).shade

/-- **A refinement with a mass inequality is a `c`-refinement** (blueprint
`lem:isCRefinementOfSumLe`): the packaging step of every pigeonholing in the construction.

No positivity of `C` is required: for `C = 0` the `NNReal` inverse is `0` and the conclusion is
trivial. -/
theorem isCRefinement_of_isRefinement_of_sum_le {C : NNReal}
    (href : IsRefinement s' V' s V)
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ (C : ENNReal) * ∑ i ∈ s', volume (V' i).shade) :
    IsCRefinement s' V' s V C⁻¹ := by
  refine ⟨href, ?_⟩
  by_cases hC : C = 0
  · subst C
    simp
  · rw [ENNReal.coe_inv hC]
    exact (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hC) ENNReal.coe_ne_top).mpr hmass

/-- A `c`-refinement retains at least a `c` fraction of the original fullness. -/
theorem IsCRefinement.mul_fullness_le {c : NNReal}
    (hV : 0 < ∑ i ∈ s, volume (V i).carrier) (h : IsCRefinement s' V' s V c) :
    c * fullness s V ≤ fullness s' V' := by
  have _hD_pos : (0 : ENNReal) ≤ ∑ i ∈ s, volume (V i).carrier := le_of_lt hV
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, fullness_def, fullness_def]
  have hcarrier : ∀ i ∈ s', volume (V' i).carrier = volume (V i).carrier :=
    fun i hi => by rw [h.1.2 i hi |>.1]
  have hD : (∑ i ∈ s', volume (V' i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier := by
    calc
      (∑ i ∈ s', volume (V' i).carrier) = ∑ i ∈ s', volume (V i).carrier :=
        Finset.sum_congr rfl (fun i hi => hcarrier i hi)
      _ ≤ ∑ i ∈ s, volume (V i).carrier :=
        Finset.sum_le_sum_of_subset h.1.1
  calc
    (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)) =
        ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) := by
      rw [div_eq_mul_inv, ← mul_assoc, ← div_eq_mul_inv]
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / (∑ i ∈ s, volume (V i).carrier) :=
      ENNReal.div_le_div_right h.2 _
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / (∑ i ∈ s', volume (V' i).carrier) :=
      ENNReal.div_le_div le_rfl hD

end CRefinement

section RefinementLemmas

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Refinements compose. -/
theorem IsRefinement.trans {s'' s' s : Finset ι} {V'' V' V : ι → ShadedBody E}
    (h₁ : IsRefinement s'' V'' s' V') (h₂ : IsRefinement s' V' s V) :
    IsRefinement s'' V'' s V := by
  refine ⟨h₁.1.trans h₂.1, fun i hi => ?_⟩
  obtain ⟨hbody₁, hshade₁⟩ := h₁.2 i hi
  obtain ⟨hbody₂, hshade₂⟩ := h₂.2 i (h₁.1 hi)
  exact ⟨hbody₁.trans hbody₂, hshade₁.trans hshade₂⟩

/-- **Composition of `c` refinements** (blueprint `lem:cRefinementTrans`): if `(𝒱'', Y'')` is a
`c₂` refinement of `(𝒱', Y')` and `(𝒱', Y')` is a `c₁` refinement of `(𝒱, Y)`, then `(𝒱'', Y'')`
is a `c₁ * c₂` refinement of `(𝒱, Y)`. -/
theorem IsCRefinement.trans {s'' s' s : Finset ι} {V'' V' V : ι → ShadedBody E}
    {c₁ c₂ : NNReal}
    (h₂ : IsCRefinement s'' V'' s' V' c₂) (h₁ : IsCRefinement s' V' s V c₁) :
    IsCRefinement s'' V'' s V (c₁ * c₂) := by
  obtain ⟨⟨hs''s', h₂ref⟩, h₂mass⟩ := h₂
  obtain ⟨⟨hs's, h₁ref⟩, h₁mass⟩ := h₁
  refine ⟨⟨hs''s'.trans hs's, fun i hi ↦
    ⟨(h₂ref i hi).1.trans (h₁ref i (hs''s' hi)).1,
      (h₂ref i hi).2.trans (h₁ref i (hs''s' hi)).2⟩⟩, ?_⟩
  calc (c₁ * c₂ : ENNReal) * ∑ i ∈ s, volume (V i).shade
      = (c₂ : ENNReal) * ((c₁ : ENNReal) * ∑ i ∈ s, volume (V i).shade) := by
        simp [mul_assoc, mul_left_comm]
    _ ≤ (c₂ : ENNReal) * ∑ i ∈ s', volume (V' i).shade := mul_le_mul_right h₁mass _
    _ ≤ ∑ i ∈ s'', volume (V'' i).shade := h₂mass

/-- A `c`-refinement is a `c'`-refinement for every smaller `c'`. -/
theorem IsCRefinement.mono {s' s : Finset ι} {V' V : ι → ShadedBody E} {c c' : NNReal}
    (hc : c' ≤ c) (h : IsCRefinement s' V' s V c) : IsCRefinement s' V' s V c' := by
  refine ⟨h.1, le_trans (by gcongr) h.2⟩

/-- A shaded family is a `1`-refinement of itself. -/
theorem IsCRefinement.refl (s : Finset ι) (V : ι → ShadedBody E) :
    IsCRefinement s V s V 1 := by
  refine ⟨?_, ?_⟩
  · exact ⟨Finset.Subset.rfl, fun _ _ ↦ ⟨rfl, Set.Subset.rfl⟩⟩
  · simp

end RefinementLemmas

end ShadedBody

/-!
# Real-valued fullness helpers
-/

@[expose] public section

open MeasureTheory ShadedBody


namespace Kakeya

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Real-valued version of `ShadedBody.sum_volumeReal_shade_eq_fullness_mul`:
the sum of `volume.real` of shades equals `fullness` times the sum of `volume.real` of
carriers, provided that the carrier sum is positive.
TODO: Examine consumers of this lemma, get rid of `volume.real`, then delete this lemma. -/
lemma _sum_shade_eq_fullness_mul_sum_carrier
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E)
    (_hpos : 0 < ∑ i ∈ s, volume.real (V i).carrier) :
    (∑ i ∈ s, volume.real (V i).shade) =
      (ShadedBody.fullness s V : ℝ) * ∑ i ∈ s, volume.real (V i).carrier := by
  have hcar : ∀ i ∈ s, volume (V i).carrier ≠ ⊤ := fun i _ ↦ (V i).isCompact'.measure_ne_top
  have hsh : ∀ i ∈ s, volume (V i).shade ≠ ⊤ := fun i hi ↦
    ne_top_of_le_ne_top (hcar i hi) (measure_mono (V i).shade_subset)
  simp only [measureReal_def, ← ENNReal.toReal_sum hsh, ← ENNReal.toReal_sum hcar,
    ShadedBody.sum_volumeReal_shade_eq_fullness_mul s V, ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- Carrier-sum pigeon bound `∑_{s} carrier ≤ M·δ^(-η) · ∑_{s'} carrier`,
derived from the shade pigeon `∑_{s} shade ≤ M · ∑_{s'} shade` and the
fullness lower bound `fullness s V ≥ δ^η`. -/
lemma carrier_pigeon_bound
    {ι : Type*} {s s' : Finset ι} (hs_ne : s.Nonempty)
    (V : ι → ShadedBody E)
    (hT_vol_pos : ∀ i ∈ s, 0 < volume.real (V i).carrier)
    {δ : NNReal} {η : ℝ} (hδ_pos : 0 < (δ : ℝ))
    {M : ℕ} (hM_pos_real : (0 : ℝ) < M)
    (hFull : ShadedBody.fullness s V ≥ δ ^ η)
    (h_pig_shade : (∑ i ∈ s, volume.real (V i).shade) ≤
      (M : ℝ) * (∑ i ∈ s', volume.real (V i).shade)) :
    (∑ i ∈ s, volume.real (V i).carrier) ≤
      (M : ℝ) * (δ : ℝ) ^ (-η) * (∑ i ∈ s', volume.real (V i).carrier) := by
  have h_carrier_pos : 0 < (∑ i ∈ s, volume.real (V i).carrier) :=
    Finset.sum_pos hT_vol_pos hs_ne
  rw [Real.rpow_neg hδ_pos.le, mul_right_comm, ← div_eq_mul_inv,
    le_div_iff₀ (Real.rpow_pos_of_pos hδ_pos _), mul_comm _ ((δ : ℝ) ^ η)]
  calc (δ : ℝ) ^ η * (∑ i ∈ s, volume.real (V i).carrier)
      ≤ (∑ i ∈ s, volume.real (V i).shade) := by
        rw [_sum_shade_eq_fullness_mul_sum_carrier (E := E) s V h_carrier_pos]
        exact mul_le_mul_of_nonneg_right
          (by simpa using NNReal.coe_le_coe.mpr hFull) h_carrier_pos.le
    _ ≤ (M : ℝ) * (∑ i ∈ s', volume.real (V i).shade) := h_pig_shade
    _ ≤ (M : ℝ) * (∑ i ∈ s', volume.real (V i).carrier) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ENNReal.toReal_mono
          (V i).isCompact'.measure_lt_top.ne
          (MeasureTheory.measure_mono (V i).shade_subset)) hM_pos_real.le

end Kakeya
