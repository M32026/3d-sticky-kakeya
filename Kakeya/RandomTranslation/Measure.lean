/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Kakeya.Shading

/-!
# Uniform random translations — the sample space

The abstract class `HasUniformTranslation`, the tube-in-set probability bounds
it immediately yields, and the two product constructions used to run `J`
independent motions (`productMeasure`) or `M` scales of `J` motions each
(`productMeasureIndexed`) on a single probability space.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory

namespace Kakeya

/-! The random construction below only uses translations. This lightweight
wrapper preserves the existing call sites while avoiding the general affine
isometry infrastructure formerly provided by `Kakeya.Translation`. -/

/-- A translation, represented by its translation vector. -/
structure Translation (E : Type*) [NormedAddCommGroup E] where
  /-- The vector added to every point. -/
  translation : E

namespace Translation

variable {E : Type*} [NormedAddCommGroup E]

instance : CoeFun (Translation E) (fun _ => E → E) where
  coe φ x := φ.translation + x

lemma dist_map (φ : Translation E) (x y : E) : dist (φ x) (φ y) = dist x y :=
  dist_add_left _ _ _

/-- Translate a set by `φ`. -/
def actSet (φ : Translation E) (s : Set E) : Set E := φ '' s

@[simp] lemma actSet_def (φ : Translation E) (s : Set E) : φ.actSet s = φ '' s := rfl

variable [NormedSpace ℝ E] [ProperSpace E]

/-- Translate a convex body by `φ`. -/
noncomputable def actConvexBody (φ : Translation E)
    (K : ConvexSpaceBody E) : ConvexSpaceBody E :=
  K.translate φ.translation

/-- Translate a tube by `φ`. -/
noncomputable def actTube {δ : NNReal} (φ : Translation E) (T : Tube δ E) : Tube δ E :=
  T.translate φ.translation

variable [MeasurableSpace E] [BorelSpace E]

/-- Translate a shaded tube by `φ`. -/
noncomputable def actShadedTube {δ : NNReal} (φ : Translation E)
    (T : ShadedTube δ E) : ShadedTube δ E :=
  T.translate φ.translation

lemma actShadedTube_carrier {δ : NNReal} (φ : Translation E) (T : ShadedTube δ E) :
    (φ.actShadedTube T).carrier = φ '' T.carrier := rfl

@[simp] lemma actShadedTube_shade {δ : NNReal} (φ : Translation E) (T : ShadedTube δ E) :
    (φ.actShadedTube T).shade = φ '' T.shade := rfl

@[simp] lemma actShadedTube_toTube {δ : NNReal} (φ : Translation E) (T : ShadedTube δ E) :
    (φ.actShadedTube T).toTube = φ.actTube T.toTube := rfl

lemma actShadedTube_toConvexBody {δ : NNReal} (φ : Translation E)
    (T : ShadedTube δ E) :
    (φ.actShadedTube T).toConvexSpaceBody = φ.actConvexBody T.toConvexSpaceBody := rfl

end Translation

namespace Translation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma volume_image_eq (φ : Translation E) (s : Set E) : volume (φ '' s) = volume s :=
  MeasureTheory.measure_image_add _ _ _

@[simp] lemma volume_actConvexBody (φ : Translation E) (K : ConvexSpaceBody E) :
    volume (φ.actConvexBody K).carrier = volume K.carrier :=
  MeasureTheory.measure_image_add _ _ _

lemma volume_actShadedTube_carrier {δ : NNReal}
    (φ : Translation E) (T : ShadedTube δ E) :
    volume (φ.actShadedTube T).carrier = volume T.carrier :=
  MeasureTheory.measure_image_add _ _ _

lemma volume_actShadedTube_shade {δ : NNReal}
    (φ : Translation E) (T : ShadedTube δ E) :
    volume (φ.actShadedTube T).shade = volume T.shade :=
  MeasureTheory.measure_image_add _ _ _

end Translation

/-- An abstract sample space carrying a uniform random translation of `E`.

This class records:
- a probability measure `measure` on `Ω`;
- a random translation `shift : Ω → Translation E` whose pointwise evaluation
  `ω ↦ shift ω x` is measurable for every `x`;
- a positive constant `uniformConstant` (depending on `E`);
- the *uniform point image bound* `prob_point_in_set`: for any `x` in the
  closed unit ball and any measurable `K ⊆ B(0, 2)`,
  `P {ω | shift ω x ∈ K} ≤ ENNReal.ofReal uniformConstant * volume K`.

This is precisely what is needed in the proof of [GWZ, Lemma 3.8] to derive
the tube probability bounds. The canonical instance samples the translation
vector uniformly from `B(0, 1)`.
-/
class HasUniformTranslation (Ω : Type*) [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] where
  /-- Probability measure on the sample space. -/
  measure : Measure Ω
  /-- The probability measure has total mass 1. -/
  [isProbabilityMeasure : IsProbabilityMeasure measure]
  /-- The random translation. -/
  shift : Ω → Translation E
  /-- Pointwise evaluation `ω ↦ shift ω x` is measurable for every `x`. -/
  measurable_apply : ∀ x : E, Measurable (fun ω => shift ω x)
  /-- The uniform constant (depending only on the dimension of `E`). -/
  uniformConstant : ℝ
  /-- The uniform constant is positive. -/
  uniformConstantPos : 0 < uniformConstant
  /-- Uniform point image bound: for any `x : E` and any measurable `K` of
      finite volume, the probability that `R x ∈ K` is at most
      `ENNReal.ofReal uniformConstant * volume K`.

      The restricted form used in [GWZ, Lemma 3.8] only needs `x` in the closed
      unit ball and `K ⊆ B(0, 2)`. The strictly-general signature here is
      equivalent for the canonical translation instance (whose proof never
      uses either ball constraint) and is what radius-`R` callers need. -/
  prob_point_in_set : ∀ (x : E),
    ∀ {K : Set E}, MeasurableSet K → volume K ≠ ⊤ →
    measure {ω | shift ω x ∈ K} ≤ ENNReal.ofReal uniformConstant * volume K

namespace HasUniformTranslation

variable
  {Ω : Type*} [MeasurableSpace Ω]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [HasUniformTranslation Ω E]

attribute [instance] HasUniformTranslation.isProbabilityMeasure

section TubeBounds

variable {δ : NNReal}

/-- **Tube-in-set probability bound.**

If `T` is a δ-tube containing some point `xT` in the closed unit ball, then for
every measurable `K ⊆ B(0, 2)` the probability that `R(T) ⊆ K` is at most
`ENNReal.ofReal uniformConstant · volume K`.

This is derived from `prob_point_in_set` by the trivial inclusion
`{ω | R(T) ⊆ K} ⊆ {ω | R(xT) ∈ K}` whenever `xT ∈ T`.

This lemma is the abstract content of inequality `(probRTinKa)` in the proof
of [GWZ, Lemma 3.8]. -/
lemma prob_actSet_subset_le (T : Tube δ E) (xT : E) (hxT : xT ∈ T.carrier)
    (_hxBall : xT ∈ Metric.closedBall (0 : E) 1)
    {K : Set E} (hK : MeasurableSet K) (hKsub : K ⊆ Metric.closedBall (0 : E) 2) :
    (HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω)
        {ω | Translation.actSet (HasUniformTranslation.shift ω) T.carrier ⊆ K} ≤
      ENNReal.ofReal (HasUniformTranslation.uniformConstant Ω E) * volume K := by
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKsub) measure_closedBall_lt_top)
  refine (MeasureTheory.measure_mono ?_).trans
    (HasUniformTranslation.prob_point_in_set (Ω := Ω) (E := E) xT hK hKtop)
  intro ω hω
  exact hω ⟨xT, hxT, rfl⟩

/-- **General-radius tube-in-set probability bound.**

Same as `prob_actSet_subset_le`, but without the `xT ∈ B(0,1)` /
`K ⊆ B(0,2)` constraints: only `volume K ≠ ⊤` is needed. Used by the
radius-2 enclosing-ball variant of
`RandomTranslation.exists_refinement`. -/
lemma prob_actSet_subset_le_general (T : Tube δ E) (xT : E) (hxT : xT ∈ T.carrier)
    {K : Set E} (hK : MeasurableSet K) (hKtop : volume K ≠ ⊤) :
    (HasUniformTranslation.measure (Ω := Ω) (E := E) : Measure Ω)
        {ω | Translation.actSet (HasUniformTranslation.shift ω) T.carrier ⊆ K} ≤
      ENNReal.ofReal (HasUniformTranslation.uniformConstant Ω E) * volume K := by
  refine (MeasureTheory.measure_mono ?_).trans
    (HasUniformTranslation.prob_point_in_set (Ω := Ω) (E := E) xT hK hKtop)
  intro ω hω
  exact hω ⟨xT, hxT, rfl⟩

end TubeBounds

end HasUniformTranslation

/-! ### Product of `J` independent copies of the random translation -/

namespace HasUniformTranslation

/-- The product probability measure on `Fin J → Ω`: `J` independent copies of
the underlying probability measure on `Ω`. -/
noncomputable def productMeasure (Ω : Type*) [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [HasUniformTranslation Ω E] (J : ℕ) :
    Measure (Fin J → Ω) :=
  Measure.pi (fun _ : Fin J => HasUniformTranslation.measure (Ω := Ω) (E := E))

instance productMeasure_isProbabilityMeasure
    (Ω : Type*) [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [HasUniformTranslation Ω E] (J : ℕ) :
    IsProbabilityMeasure (productMeasure Ω E J) := by
  unfold productMeasure
  infer_instance

section Product

variable
  {Ω : Type*} [MeasurableSpace Ω]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [HasUniformTranslation Ω E]

/-- The marginal of the product measure on the `j`-th coordinate is the underlying
probability measure on `Ω`. -/
lemma productMeasure_map_eval (J : ℕ) (j : Fin J) :
    (productMeasure Ω E J).map (Function.eval j) =
      HasUniformTranslation.measure (Ω := Ω) (E := E) :=
  (MeasureTheory.measurePreserving_eval
    (μ := fun _ : Fin J => HasUniformTranslation.measure (Ω := Ω) (E := E)) j).map_eq

end Product

/-! ### Indexed product of `M` independent random translations

For the joint (multi-scale) random-translation argument in
`subStickyFrostmanLemma`, we need a *single* probability space on which
all `M` scales' random motions live simultaneously, so that a union
bound over per-scale "good events" yields a deterministic joint witness.

`productMeasureIndexed Ω E J` builds that space as a double `Measure.pi`:
the outer `Measure.pi` is over `Fin M` (scales), and the inner factor at
scale `k` is `productMeasure Ω E (J k)`.  Probability-measure instance,
marginal-via-eval, and the multi-scale union bound are thin wrappers
around Mathlib's `Measure.pi`. -/

section ProductIndexed

variable
  {Ω : Type*} [MeasurableSpace Ω]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [HasUniformTranslation Ω E]

/-- The `Fin M`-indexed product of `productMeasure Ω E (J k)`: a single
probability space on which all `M` per-scale random translations live
simultaneously. -/
noncomputable def productMeasureIndexed (Ω : Type*) [MeasurableSpace Ω]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [HasUniformTranslation Ω E] {M : ℕ} (J : Fin M → ℕ) :
    Measure (∀ k : Fin M, Fin (J k) → Ω) :=
  Measure.pi (fun k : Fin M => productMeasure Ω E (J k))

instance productMeasureIndexed_isProbabilityMeasure {M : ℕ} (J : Fin M → ℕ) :
    IsProbabilityMeasure (productMeasureIndexed Ω E J) := by
  unfold productMeasureIndexed
  infer_instance

/-- The `k`-th marginal of `productMeasureIndexed` is `productMeasure Ω E (J k)`. -/
lemma productMeasureIndexed_map_eval {M : ℕ} (J : Fin M → ℕ) (k : Fin M) :
    (productMeasureIndexed Ω E J).map (Function.eval k) =
      productMeasure Ω E (J k) :=
  (MeasureTheory.measurePreserving_eval
    (μ := fun k : Fin M => productMeasure Ω E (J k)) k).map_eq

/-- The pullback of a measurable event under the `k`-th coordinate projection
has the same joint measure as the original event under
`productMeasure Ω E (J k)`. -/
lemma productMeasureIndexed_preimage_eval
    {M : ℕ} (J : Fin M → ℕ) (k : Fin M)
    {B : Set (Fin (J k) → Ω)} (hB : MeasurableSet B) :
    productMeasureIndexed Ω E J (Function.eval k ⁻¹' B) =
      productMeasure Ω E (J k) B := by
  rw [← productMeasureIndexed_map_eval (Ω := Ω) (E := E) J k]
  exact (Measure.map_apply (measurable_pi_apply k) hB).symm

/-- **Union bound across scales.**  If `Bad k ⊆ Fin (J k) → Ω` are per-scale
"bad" events with `productMeasure Ω E (J k) (Bad k) ≤ ε k`, then their
pullbacks to the joint space cover a set whose joint measure is bounded
by `∑ k, ε k`.  Used to combine the per-scale failure budgets into one joint
budget for the multi-scale random-translation argument. -/
lemma productMeasureIndexed_union_bound
    {M : ℕ} (J : Fin M → ℕ) (Bad : ∀ k : Fin M, Set (Fin (J k) → Ω))
    (hBad : ∀ k : Fin M, MeasurableSet (Bad k))
    (ε : Fin M → ENNReal)
    (hε : ∀ k : Fin M, productMeasure Ω E (J k) (Bad k) ≤ ε k) :
    productMeasureIndexed Ω E J
        (⋃ k : Fin M, Function.eval k ⁻¹' Bad k) ≤
      ∑ k : Fin M, ε k := by
  classical
  have hrw : (⋃ k : Fin M, Function.eval k ⁻¹' Bad k) =
      ⋃ k ∈ (Finset.univ : Finset (Fin M)),
        Function.eval k ⁻¹' Bad k := by
    simp
  rw [hrw]
  refine (MeasureTheory.measure_biUnion_finset_le
            (μ := productMeasureIndexed Ω E J)
            (Finset.univ : Finset (Fin M))
            (fun k => Function.eval k ⁻¹' Bad k)).trans ?_
  refine Finset.sum_le_sum ?_
  intro k _
  rw [productMeasureIndexed_preimage_eval (Ω := Ω) (E := E) J k (hBad k)]
  exact hε k

/-- Measurability of the joint Bad set built by pullback-union from per-scale
Bad sets.  Required to feed the joint Bad into the union-bound lemma. -/
lemma measurableSet_productMeasureIndexed_unionBad
    {M : ℕ} (J : Fin M → ℕ) (Bad : ∀ k : Fin M, Set (Fin (J k) → Ω))
    (hBad : ∀ k : Fin M, MeasurableSet (Bad k)) :
    MeasurableSet
        (⋃ k : Fin M, Function.eval k ⁻¹' Bad k :
          Set (∀ k : Fin M, Fin (J k) → Ω)) :=
  MeasurableSet.iUnion fun k =>
    (measurable_pi_apply k) (hBad k)

end ProductIndexed

end HasUniformTranslation

end Kakeya
