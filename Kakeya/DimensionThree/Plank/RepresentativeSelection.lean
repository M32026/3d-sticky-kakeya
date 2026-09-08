/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FibrePacking
public import Kakeya.DimensionThree.Plank.TypicalAngleTransfer
public import Kakeya.DimensionThree.Plank.AnchorCarrier
public import Kakeya.DimensionThree.Plank.TypedAnchorPrism
public import Kakeya.DimensionThree.Plank.ThickenedRepr

/-!
# Representative selection for GWZ Lemma 6.13

This file is intentionally downstream of the geometric and dense-box modules.  Keeping the witness
construction and final existential assembly here makes the dependency direction explicit.

`Kakeya.DimensionThree.Plank.AngleConcentration` is imported for the angular concentration input
`Plank.exists_typicalIntersectionAngle_of_stableFibres`, which supplies the `hconc` hypothesis of
`Plank.denseBoxEstimate_boxNormalised` on the Item 2 branch of the assembly.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- Internal helper for the witness assembly: a `c`-refinement transports the fullness lower
bound.  Since `s' ⊆ s` with equal carriers on `s'` shrinks the carrier denominator while the
`c`-mass bound lower-bounds the shade numerator, `c * fullness s V ≤ fullness s' V'`. -/
private theorem refinement_fullness_le
    {s' s : Finset ι} {V' V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {c : ℝ≥0}
    (h : ShadedBody.IsCRefinement s' V' s V c) :
    c * ShadedBody.fullness s V ≤ ShadedBody.fullness s' V' := by
  obtain ⟨⟨hsub, hbody⟩, hmass⟩ := h
  have hDS' : ∑ i ∈ s', volume (V' i).carrier ≤ ∑ i ∈ s, volume (V i).carrier :=
    (Finset.sum_congr rfl fun i hi => by rw [(hbody i hi).1]).le.trans
      (Finset.sum_le_sum_of_subset hsub)
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.fullness_def s V,
    ShadedBody.fullness_def s' V', ← mul_div_assoc]
  exact (ENNReal.div_le_div_right hmass _).trans (ENNReal.div_le_div_left hDS' _)

/-! ### Pointwise fibre retention

A global mass refinement `IsCRefinement s₂ Y s Y c` says nothing about *individual points*: the
retained family `s₂` may miss almost all planks through some `x ∈ ⋃_{i∈s₂}(Y i).shade`.  But any
typical-angle restoration across a good refinement needs exactly such a pointwise statement, and it
is a genuine hypothesis, not a consequence.

The fix is to delete the bad points rather than the bad planks: restrict every surviving shading to
the *good region* `G` where the retained pointwise multiplicity is at least a `q`-fraction of the
original one.  On the complement the retained multiplicity is by definition `< q ·` the original, so
integrating the multiplicity shows the deleted mass is at most `q ·` the total.  This costs `q` in
the refinement constant, which is why the construction needs `q < c`. -/

/-- The pointwise shading count as an `ℝ≥0∞`-valued function: the sum of the indicators of the
shadings.  This is `pointwiseMultiplicity` in a form that is manifestly measurable and integrates
against `volume`. -/
private noncomputable def shadeCountE (t : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (x : EuclideanSpace ℝ (Fin 3)) : ENNReal :=
  ∑ i ∈ t, (Y i).shade.indicator (fun _ => (1 : ENNReal)) x

private theorem measurable_shadeCountE (t : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) : Measurable (shadeCountE t Y) :=
  Finset.measurable_sum _ fun i _ => measurable_const.indicator (Y i).measurableSet_shade

/-- The shading count is the cardinality of the shade fibre. -/
private theorem shadeCountE_eq_card (t : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (x : EuclideanSpace ℝ (Fin 3)) :
    shadeCountE t Y x = ((shadeFibre t Y x).card : ENNReal) := by
  simp [shadeCountE, shadeFibre, Set.indicator_apply, Finset.sum_boole]

/-- Fubini for the shading count: the total shading mass inside a measurable set `B` is the
integral of the pointwise multiplicity over `B`. -/
private theorem sum_volume_shade_inter_eq_lintegral (t : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {B : Set (EuclideanSpace ℝ (Fin 3))}
    (_hB : MeasurableSet B) :
    ∑ i ∈ t, volume ((Y i).shade ∩ B) = ∫⁻ x in B, shadeCountE t Y x := by
  unfold shadeCountE
  rw [lintegral_finsetSum _ fun i _ => measurable_const.indicator (Y i).measurableSet_shade]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_indicator (Y i).measurableSet_shade]
  simp [Measure.restrict_restrict (Y i).measurableSet_shade, Set.inter_comm]

/-- Total shading mass is finite: each shading sits inside a compact convex carrier.

Public because the `htop` hypothesis of `Plank.exists_goodSlabPrune` and of every other
`ENNReal`-cancellation step in the Lemma 6.13 assembly is exactly this. -/
theorem sum_volume_shade_ne_top (t : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∑ i ∈ t, volume (Y i).shade ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun i _ =>
    ne_top_of_le_ne_top (Y i).1.3.measure_ne_top (measure_mono (Y i).shade_subset)

/-- The mass a `q`-threshold deletion can destroy is at most `q` times the total mass. -/
private theorem sum_volume_shade_inter_compl_le (s s₂ : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {q : ℝ≥0}
    {G : Set (EuclideanSpace ℝ (Fin 3))} (hGmeas : MeasurableSet G)
    (hG : ∀ x ∈ Gᶜ, shadeCountE s₂ Y x ≤ (q : ENNReal) * shadeCountE s Y x) :
    ∑ i ∈ s₂, volume ((Y i).shade ∩ Gᶜ) ≤ (q : ENNReal) * ∑ i ∈ s, volume (Y i).shade := by
  calc
    ∑ i ∈ s₂, volume ((Y i).shade ∩ Gᶜ) = ∫⁻ x in Gᶜ, shadeCountE s₂ Y x :=
      sum_volume_shade_inter_eq_lintegral s₂ Y hGmeas.compl
    _ ≤ ∫⁻ x in Gᶜ, (q : ENNReal) * shadeCountE s Y x :=
      setLIntegral_mono (measurable_const.mul (measurable_shadeCountE s Y)) hG
    _ = (q : ENNReal) * ∫⁻ x in Gᶜ, shadeCountE s Y x :=
      lintegral_const_mul _ (measurable_shadeCountE s Y)
    _ ≤ (q : ENNReal) * ∫⁻ x, shadeCountE s Y x :=
      mul_le_mul_right (setLIntegral_le_lintegral Gᶜ (shadeCountE s Y)) _
    _ = (q : ENNReal) * ∑ i ∈ s, volume (Y i).shade := by
      rw [← setLIntegral_univ, ← sum_volume_shade_inter_eq_lintegral s Y MeasurableSet.univ]
      simp

open scoped Classical in
/-- **Good-point refinement.**  Given a mass refinement `(s₂, Y)` of `(s, Y)` with constant `c`, and
a retention threshold `q < c`, restricting every surviving shading to the good region
`G = {x | q · μ(s,Y)(x) ≤ μ(s₂,Y)(x)}` produces a `(c - q)`-refinement whose surviving point fibres
each keep a `q`-fraction of the original fibre.  This is the honest source of a pointwise fibre
retention hypothesis; per-plank mass comparability is *not* available
(`HasCConstantMultiplicity` controls the pointwise multiplicity on the union, not the individual
shading volumes).

Public because it is the only aggregate-to-pointwise bridge in the development.  Any later deletion
that has to keep a two-sided predicate alive — `Kakeya.IsTypicalPlankAngle` or
`ShadedBody.HasCConstantMultiplicity`, whose transports
(`Plank.isTypicalPlankAngle_of_fibreRetention`,
`Plank.hasCConstantMultiplicity_of_fibreRetention_real`) both consume exactly the `hkeep` clause
returned here — must route through this theorem, because a class-wise deletion cannot produce
`hkeep` on its own: the class realising a pointwise fibre retention moves with the point.  Note the
cost: the shadings shrink to the good region, so any clause about the *old* shadings has to be
re-established for `Y₂` using the returned `hshade`. -/
theorem exists_goodPoint_refinement {s s₂ : Finset ι} (hs₂ : s₂ ⊆ s)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {q c : ℝ≥0} (hqc : q < c)
    (href : ShadedBody.IsCRefinement s₂ Y s Y c) :
    ∃ Y₂ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ i, (Y₂ i).toConvexSpaceBody = (Y i).toConvexSpaceBody) ∧
      (∀ i, (Y₂ i).shade ⊆ (Y i).shade) ∧
      ShadedBody.IsCRefinement s₂ Y₂ s Y (c - q) ∧
      (∀ x ∈ ⋃ i ∈ s₂, (Y₂ i).shade,
        (q : ℝ) * ((shadeFibre s Y x).card : ℝ) ≤ ((shadeFibre s₂ Y₂ x).card : ℝ)) := by
  classical
  set G : Set (EuclideanSpace ℝ (Fin 3)) :=
    {x | (q : ENNReal) * shadeCountE s Y x ≤ shadeCountE s₂ Y x} with hG_def
  have hGmeas : MeasurableSet G :=
    measurableSet_le (measurable_const.mul (measurable_shadeCountE s Y))
      (measurable_shadeCountE s₂ Y)
  set Y₂ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i =>
    { toConvexSpaceBody := (Y i).toConvexSpaceBody
      shade := (Y i).shade ∩ G
      measurableSet_shade := (Y i).measurableSet_shade.inter hGmeas
      shade_subset := Set.inter_subset_left.trans (Y i).shade_subset } with hY₂_def
  have hY₂shade : ∀ i, (Y₂ i).shade = (Y i).shade ∩ G := fun _ => rfl
  refine ⟨Y₂, fun _ => rfl, fun _ => Set.inter_subset_left,
    ⟨⟨hs₂, fun i _ => ⟨rfl, Set.inter_subset_left⟩⟩, ?_⟩, ?_⟩
  · -- Mass: what survives is the total on `s₂` minus what the deletion destroys.
    set M : ENNReal := ∑ i ∈ s, volume (Y i).shade with hM_def
    have hsplit : (∑ i ∈ s₂, volume ((Y i).shade ∩ G)) +
        (∑ i ∈ s₂, volume ((Y i).shade ∩ Gᶜ)) = ∑ i ∈ s₂, volume (Y i).shade := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by
        rw [← Set.sdiff_eq]; exact measure_inter_add_sdiff₀ _ hGmeas.nullMeasurableSet
    have hbad : (∑ i ∈ s₂, volume ((Y i).shade ∩ Gᶜ)) ≤ (q : ENNReal) * M :=
      sum_volume_shade_inter_compl_le s s₂ Y hGmeas fun _ hx => (not_le.mp (by exact hx)).le
    have hbadtop : (∑ i ∈ s₂, volume ((Y i).shade ∩ Gᶜ)) ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (sum_volume_shade_ne_top s Y)) hbad
    refine (ENNReal.add_le_add_iff_right hbadtop).mp ?_
    rw [hsplit]
    calc ((c - q : ℝ≥0) : ENNReal) * M + (∑ i ∈ s₂, volume ((Y i).shade ∩ Gᶜ))
        ≤ ((c - q : ℝ≥0) : ENNReal) * M + (q : ENNReal) * M := by gcongr
      _ = (c : ENNReal) * M := by rw [← add_mul, ← ENNReal.coe_add, tsub_add_cancel_of_le hqc.le]
      _ ≤ ∑ i ∈ s₂, volume (Y i).shade := href.2
  · -- Pointwise retention: a surviving point lies in `G`, which is the retention inequality.
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hxG : x ∈ G := ((hY₂shade i) ▸ hxi).2
    have hfib : shadeFibre s₂ Y₂ x = shadeFibre s₂ Y x := by
      ext j; simp [mem_shadeFibre, hY₂shade j, hxG]
    rw [hG_def, Set.mem_setOf_eq, shadeCountE_eq_card, shadeCountE_eq_card] at hxG
    have hnn : q * ((shadeFibre s Y x).card : ℝ≥0) ≤ ((shadeFibre s₂ Y x).card : ℝ≥0) := by
      exact_mod_cast hxG
    rw [hfib]
    exact_mod_cast hnn

/-- **The reserve scale absorbs the sharp pigeonhole loss, at every `a` (extra69,
`rem:outScaleLeHalfMulReserve`).**

Suppose the retained pigeonhole fraction `cGood` obeys the *sharp* bound
`(Cres · plankAngleScaleA a)⁻¹ ≤ cGood`.  Then for every `kappa ≥ 4 · Cres` the output scale
`Aout(a) = max 2 (plankAngleScaleA a)` fits inside the deletion budget
`(cGood / 2) · plankReserveScale kappa a`.

Writing `A = plankAngleScaleA a ≥ 1` the chain is
`Aout ≤ 2 · A = (4 · Cres · A ^ 2) / (2 · Cres · A) ≤ (kappa · A ^ 2) / (2 · Cres · A)
  = (2 · Cres · A)⁻¹ · kappa · A ^ 2 ≤ (cGood / 2) · kappa · A ^ 2`,
the last step being the sharp bound.  Nothing here restricts `a`: this is exactly the step that
fails when `cGood` is controlled only by the polynomial bound `cη · a ^ η`, whose reciprocal grows
like a power of `a⁻¹` and cannot be absorbed by the sub-polynomial `kappa · A ^ 2`.

The statement carries a free multiplier `m ≥ 1`, which is what lets a *second*, later deletion be
paid for: the witness can then deliver its typical angle at the enlarged scale `m · Aout(a)` rather
than at `Aout(a)`, and since `Kakeya.IsTypicalPlankAngle.mono_scale` *lowers* the scale, a
conclusion at a larger scale is strictly stronger and leaves `m` in reserve.  At `m = 1` the
chain above is recovered verbatim; in general `4 · Cres` is replaced by `4 · m · Cres`, so
`kappa ≥ 4 · m · Cres`
suffices, and `kappa` is fixed before every geometric datum.  No smallness hypothesis on `a` is
introduced. -/
theorem outScale_le_half_mul_reserve_mul {Cres cGood : ℝ≥0} (hCres : 0 < Cres)
    {m : ℝ} (hm : 1 ≤ m)
    {kappa : ℝ} (hkappa : 4 * m * (Cres : ℝ) ≤ kappa) {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1)
    (hsharp : (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood) :
    m * max 2 (plankAngleScaleA a) ≤ ((cGood : ℝ) / 2) * plankReserveScale kappa a := by
  set A := plankAngleScaleA a with hA_def
  have hA1 : 1 < A := one_lt_plankAngleScaleA ha ha1
  have hCresR : (0 : ℝ) < Cres := hCres
  have hprod : (0 : ℝ) < (Cres : ℝ) * A := mul_pos hCresR (by linarith)
  have hcG : (0 : ℝ) ≤ cGood := cGood.coe_nonneg
  -- The sharp bound, transported to `ℝ` and cleared of the inverse.
  have hkey : 1 ≤ (cGood : ℝ) * ((Cres : ℝ) * A) := by
    have h := NNReal.coe_le_coe.mpr hsharp
    rw [NNReal.coe_inv, NNReal.coe_mul, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ A)] at h
    have := mul_le_mul_of_nonneg_right h hprod.le
    rwa [inv_mul_cancel₀ hprod.ne'] at this
  -- LHS: `max 2 A ≤ 2 * A`, scaled by `m ≥ 1`.
  refine le_trans (b := 2 * m * A) ?_ ?_
  · nlinarith [max_le (by linarith : (2 : ℝ) ≤ 2 * A) (by linarith : A ≤ 2 * A)]
  -- RHS: `4 · m · Cres ≤ kappa` plus the sharp bound absorb the factor `2 * m * A`.
  · rw [plankReserveScale, ← hA_def]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (cGood : ℝ) / 2)
        (mul_self_nonneg A)) (sub_nonneg.mpr hkappa),
      mul_nonneg (by nlinarith : (0 : ℝ) ≤ 2 * m * A) (sub_nonneg.mpr hkey)]

open scoped Classical in
/-- **Reserve-preserving deletion.**

Given a `c`-refinement `(s₂, Y')` of `(s, Y')` and a retention threshold `q < c`, restricting the
shadings to the good region (`Kakeya.exists_goodPoint_refinement`) produces a `(c - q)`-refinement
whose surviving fibres each keep a `q`-fraction, and `Plank.isTypicalPlankAngle_of_fibreRetention`
then transports the two-sided `Kakeya.IsTypicalPlankAngle` from the stability clause of the
undeleted family at the *reserve* scale
`Kakeya.plankReserveScale kappa a = kappa · plankAngleScaleA a ^ 2` — which is exactly what
`Kakeya.findingTypicalAngleOfIntersection_stable_reserve` supplies.  The pointwise retention
inequality `q · #𝒫_{Y'}(x) ≤ #𝒫_{Y₂}(x)` is *returned* rather than consumed: it is the hypothesis
`hret` of `Plank.hasCConstantMultiplicity_of_fibreRetention_real`, so the witness must hand it out
for the relative constant-multiplicity transport to be usable downstream.

The only arithmetic input is the multiplicative budget `hbudget`,
`m · Aout(a) ≤ q · R_kappa(a)`, whose supplier is `Kakeya.outScale_le_half_mul_reserve_mul`.  No
relation between `q` and any fixed power of `plankAngleScaleA a` is asked, and in particular there
is **no smallness threshold on `a`**: an earlier form took `q ≥ A(a)⁻¹`, which forced the retention
to dominate `exp(-(log a⁻¹)^(1/2))` and hence forced `a < a₀`.  Here the reserve scale absorbs the
retention instead, and `kappa` is chosen before every geometric datum.

The output scale is the *enlarged* `m · Aout(a)`, with `Aout(a) = max 2 (plankAngleScaleA a)`, for
any `1 ≤ m` the reserve can pay for.  Using `Aout(a)` rather than `plankAngleScaleA a` keeps the
`2 ≤ A` hypothesis of the downstream consumers available, and
`Kakeya.IsTypicalPlankAngle.mono_scale` recovers the conclusion at any smaller scale.

The surplus `m` is what makes a later deletion possible at all.  A conclusion at a larger stability
scale is
strictly stronger — `Kakeya.IsTypicalPlankAngle.mono_scale` lowers the scale — so the surplus factor
`m` is a genuine reserve: a downstream deletion retaining a `q₂`-fraction pointwise can run
`Plank.isTypicalPlankAngle_of_fibreRetention` with `B := m · Aout(a)` and still deliver `Aout(a)`,
provided `m ≥ q₂⁻¹`.  For a half-retention prune `m = 2` suffices.

Without this, the reserve is exhausted by the witness's own pigeonhole deletion and no second
deletion can keep the two-sided predicate alive. -/
theorem typicalAngleAfterReserveDeletion_reserve
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s s₂ : Finset ι} (hs₂ : s₂ ⊆ s) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (θ C : ℝ≥0) {kappa : ℝ} (hkappa : 1 ≤ kappa)
    {m : ℝ} (hm : 1 ≤ m) {q c : ℝ≥0} (hqc : q < c)
    (hbudget : m * max 2 (plankAngleScaleA a) ≤ (q : ℝ) * plankReserveScale kappa a)
    (href : ShadedBody.IsCRefinement s₂ Y' s Y' c)
    (hstab : ∀ x ∈ ⋃ i ∈ s, (Y' i).shade, ∀ t ⊆ shadeFibre s Y' x,
      (plankReserveScale kappa a)⁻¹ * ((shadeFibre s Y' x).card : ℝ) ≤ (t.card : ℝ) →
        θ ≤ C * maxPlankAngle P t ∧ maxPlankAngle P t ≤ C * θ) :
    ∃ Y₂ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ i, (Y₂ i).toConvexSpaceBody = (Y' i).toConvexSpaceBody) ∧
      (∀ i, (Y₂ i).shade ⊆ (Y' i).shade) ∧
      ShadedBody.IsCRefinement s₂ Y₂ s Y' (c - q) ∧
      IsTypicalPlankAngle s₂ Y₂ P θ C (Real.toNNReal (m * max 2 (plankAngleScaleA a))) ∧
      (∀ x ∈ ⋃ i ∈ s₂, (Y₂ i).shade,
        (q : ℝ) * ((shadeFibre s Y' x).card : ℝ) ≤ ((shadeFibre s₂ Y₂ x).card : ℝ)) := by
  obtain ⟨Y₂, hbody, hshade, href₂, hkeep⟩ := exists_goodPoint_refinement hs₂ Y' hqc href
  have h0max : (0 : ℝ) ≤ max 2 (plankAngleScaleA a) := le_trans zero_le_two (le_max_left _ _)
  have hAcoe : ((Real.toNNReal (m * max 2 (plankAngleScaleA a)) : ℝ≥0) : ℝ)
      = m * max 2 (plankAngleScaleA a) :=
    Real.coe_toNNReal _ (mul_nonneg (by linarith) h0max)
  have hBcoe : ((Real.toNNReal (plankReserveScale kappa a) : ℝ≥0) : ℝ)
      = plankReserveScale kappa a :=
    Real.coe_toNNReal _ (mul_nonneg (by linarith) (mul_self_nonneg _))
  refine ⟨Y₂, hbody, hshade, href₂,
    Plank.isTypicalPlankAngle_of_fibreRetention s s₂ hs₂ Y' Y₂ P θ C _
      (Real.toNNReal (plankReserveScale kappa a)) (q : ℝ) ?_ (by rw [hAcoe, hBcoe]; exact hbudget)
      (fun i _ => hshade i) hkeep
      (fun x hx t ht h => hstab x hx t ht (by rwa [hBcoe] at h)), hkeep⟩
  rw [← NNReal.coe_le_coe, NNReal.coe_one, hAcoe]
  exact le_trans (le_trans one_le_two (le_max_left _ _)) (le_mul_of_one_le_left h0max hm)

/-- **The one-sided stop-scale stability clause survives a deletion whose retained fraction fits
the scale budget.**

The stop-scale analogue of `Plank.isTypicalPlankAngle_of_fibreRetention`: same hypotheses, but the
conclusion is the *one-sided* comparability `θ ≤ K · M(P, t)` at a fixed angular constant `K`,
rather than the two-sided `Kakeya.IsTypicalPlankAngle` predicate.  This is the shape that
`Kakeya.findingTypicalAngleOfIntersection_stable_reserve` delivers at
`K = 2 · Kakeya.plankAngleScaleB a`, and the constant `K` is carried through untouched — the
deletion is paid for entirely out of the scale budget `A ≤ q · B`, never out of `K`.

The two-sided transport cannot be reused here: it is stated for the `ℝ≥0`-valued comparability of
`Kakeya.IsTypicalPlankAngle`, whereas the stop scale `2 · plankAngleScaleB a` is a genuine real
with no `ℝ≥0` packaging in the source clause. -/
theorem stopScaleStability_of_fibreRetention {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s s₂ : Finset ι) (hs₂ : s₂ ⊆ s)
    (Y₁ Y₂ : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (P : ι → Plank a b hab hb1) (θ : ℝ≥0) (K A B q : ℝ) (hA : 1 ≤ A) (hBpos : 0 < B)
    (hbudget : A ≤ q * B)
    (hshade : ∀ i ∈ s₂, (Y₂ i).shade ⊆ (Y₁ i).shade)
    (hkeep : ∀ x ∈ ⋃ i ∈ s₂, (Y₂ i).shade,
      q * ((shadeFibre s Y₁ x).card : ℝ) ≤ ((shadeFibre s₂ Y₂ x).card : ℝ))
    (hstab : ∀ x ∈ ⋃ i ∈ s, (Y₁ i).shade, ∀ t ⊆ shadeFibre s Y₁ x,
      B⁻¹ * ((shadeFibre s Y₁ x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) ≤ K * ((maxPlankAngle P t : ℝ≥0) : ℝ)) :
    ∀ x ∈ ⋃ i ∈ s₂, (Y₂ i).shade, ∀ t ⊆ shadeFibre s₂ Y₂ x,
      A⁻¹ * ((shadeFibre s₂ Y₂ x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) ≤ K * ((maxPlankAngle P t : ℝ≥0) : ℝ) := by
  intro x hx t ht hfrac
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hBinv : B⁻¹ ≤ A⁻¹ * q := by
    rw [inv_le_iff_one_le_mul₀ hBpos, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hApos, one_mul]
    exact hbudget
  have hxU₁ : x ∈ ⋃ i ∈ s, (Y₁ i).shade := by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨i, hs₂ hi, hshade i hi hxi⟩
  have hsubfib : shadeFibre s₂ Y₂ x ⊆ shadeFibre s Y₁ x := fun j hj => by
    rw [mem_shadeFibre] at hj ⊢; exact ⟨hs₂ hj.1, hshade j hj.1 hj.2⟩
  refine hstab x hxU₁ t (ht.trans hsubfib) ?_
  calc B⁻¹ * ((shadeFibre s Y₁ x).card : ℝ)
      ≤ A⁻¹ * q * ((shadeFibre s Y₁ x).card : ℝ) :=
        mul_le_mul_of_nonneg_right hBinv (Nat.cast_nonneg _)
    _ = A⁻¹ * (q * ((shadeFibre s Y₁ x).card : ℝ)) := mul_assoc _ _ _
    _ ≤ A⁻¹ * ((shadeFibre s₂ Y₂ x).card : ℝ) :=
        mul_le_mul_of_nonneg_left (hkeep x hx) (inv_nonneg.2 hApos.le)
    _ ≤ (t.card : ℝ) := hfrac

open scoped Classical in
/-- **The fibre-size pigeonhole, with both the sharp and the polynomial retention bound (extra69,
`rem:pigeonholeOfPhiPackingSharp`).**

`Plank.ThickenedRepr.pigeonhole_of_phi_packing` with the *sharp* dyadic bound exposed alongside the
polynomial one.  The underlying pigeonhole
`Plank.ThickenedRepr.pigeonholeThickenedMultiplicity` returns
`((Nat.log 2 K : ℝ≥0) + 1)⁻¹ ≤ cGood` with equality at the chosen dyadic level, for the concrete cap
`K = ⌈Cpack · a ^ (-D)⌉₊`.  That `K` is internal to this wrapper, so the sharp bound is exposed in
the equivalent scale-free form
`(Cres · plankAngleScaleA a)⁻¹ ≤ cGood`,
obtained by composing it with `Kakeya.exists_natLog_succ_le_mul_plankAngleScaleA`, whose constant
`Cres` depends only on the packing data `(Cpack, D)` and which carries **no smallness threshold on
`a`**.

Both bounds are genuinely needed and neither replaces the other.

*The sharp bound is the only one that can control the reserve scale.*  The deletion budget of
`Kakeya.typicalAngleAfterReserveDeletion_reserve` asks, at `m = 1`, for
`Aout(a) ≤ (cGood / 2) · kappa · A(a) ^ 2`,
i.e. for `2 · Aout(a) / cGood` to be at most `kappa · A(a) ^ 2`.  With the sharp bound this is
`≤ 4 · Cres · A(a) ^ 2` (`Kakeya.outScale_le_half_mul_reserve_mul` at `m = 1`), so a `kappa` fixed
before every
geometric datum suffices.  With the polynomial bound it would be `≥ 2 · Aout(a) / (cη · a ^ η)`,
which is polynomial in `a⁻¹` and is therefore **not** absorbable into `kappa · A(a) ^ 2` for any
`kappa`, nor into the sub-polynomial `a ^ ε` budget of the final assembly.

*The polynomial bound is the only one that yields uniform refinement constants.*  The final
constants `cP` and `cLam` of `Kakeya.representativeWitness_strong_uniform` are declared as
fixed multiples of `a ^ (4η) · a ^ ε`, and it is `cη · a ^ η ≤ cGood` that supplies the powers
of `a`; the sharp bound gives only `(Cres · A(a))⁻¹`, which is not of that shape. -/
private theorem pigeonhole_of_phi_packing_sharp (cThk : ℝ≥0) (hcThk : 1 ≤ cThk)
    {η : ℝ} (hη : 0 < η) :
    ∃ cη Cres : ℝ≥0, 0 < cη ∧ 0 < Cres ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
        (R : Plank.ThickenedRepr s V θ hθ1 cThk)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
        0 < a → a < 1 →
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          PrismNDim.IsEssentiallyDistinct (V i).toPrismNDim (V j).toPrismNDim) →
        ∃ (s₂ : Finset ι) (N : ℕ) (cGood cN : ℝ≥0),
          s₂ ⊆ s ∧ 1 ≤ N ∧ 1 ≤ cN ∧ cN ≤ 2 ∧ cη * a ^ η ≤ cGood ∧
          (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood ∧
          ShadedBody.IsCRefinement s₂ Y s Y cGood ∧
          (∀ Q ∈ R.indexSet, (s₂.filter (fun i => R.repr i = Q)).Nonempty →
            (N : ℝ) / (cN : ℝ) ≤ ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ∧
              ((s₂.filter (fun i => R.repr i = Q)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) := by
  obtain ⟨Cpack, D, -, hbound⟩ := Plank.ThickenedRepr.phi_packing_bound cThk hcThk
  obtain ⟨cη, hcη0, hlog⟩ := Plank.exists_log_loss_lower_bound hη (2 * Cpack + 1) D
  obtain ⟨Cres_real, hCres_real_pos, hres⟩ :=
    exists_natLog_succ_le_mul_plankAngleScaleA ((2 * Cpack + 1 : ℝ≥0) : ℝ) D
  set Cres : ℝ≥0 := Real.toNNReal Cres_real with hCres_def
  have hCres_pos : 0 < Cres := Real.toNNReal_pos.mpr hCres_real_pos
  refine ⟨cη, Cres, hcη0, hCres_pos, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 R Y ha0 ha1 hED
  have ha1le : a ≤ 1 := hab.trans hb1
  have hK : ∀ i ∈ s, R.phi i ≤ ⌈Cpack * a ^ (-(D : ℝ))⌉₊ := fun i hi =>
    (Nat.ceil_natCast (R.phi i)).symm.le.trans
      (Nat.ceil_mono (hbound s V θ hθ1 R ha0 hED i hi))
  set K : ℕ := ⌈Cpack * a ^ (-(D : ℝ))⌉₊ with hK_def
  obtain ⟨s₂, N, cGood, cN, hsub, hN, hcN, hcN2, hcGood_log, href, hfib⟩ :=
    R.pigeonholeThickenedMultiplicity Y K hK
  -- hcGood_log : ((Nat.log 2 K : ℝ≥0) + 1)⁻¹ ≤ cGood
  have hK_nn : (K : ℝ≥0) ≤ (2 * Cpack + 1) * a ^ (-(D : ℝ)) := by
    have hpow1 : (1 : ℝ≥0) ≤ a ^ (-(D : ℝ)) := by
      simpa using NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1le (neg_nonpos.mpr (Nat.cast_nonneg D))
    calc (K : ℝ≥0) ≤ Cpack * a ^ (-(D : ℝ)) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
      _ ≤ Cpack * a ^ (-(D : ℝ)) + a ^ (-(D : ℝ)) := by gcongr
      _ ≤ (2 * Cpack + 1) * a ^ (-(D : ℝ)) := by
        rw [add_mul, one_mul]; gcongr; exact le_mul_of_one_le_left zero_le one_le_two
  have h_nnreal_ineq : (Nat.log 2 K : ℝ≥0) + 1 ≤ Cres * Real.toNNReal (plankAngleScaleA a) := by
    rw [← NNReal.coe_le_coe]
    push_cast [hCres_def, Real.coe_toNNReal _ hCres_real_pos.le,
      Real.coe_toNNReal _ (zero_lt_one.trans (one_lt_plankAngleScaleA ha0 ha1)).le]
    exact hres (a := a) ha0 ha1 K (by exact_mod_cast hK_nn)
  have hcGood_sharp : (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood :=
    (inv_anti₀ (by positivity) h_nnreal_ineq).trans hcGood_log
  exact ⟨s₂, N, cGood, cN, hsub, hN, hcN, hcN2,
    (hlog a ha0 ha1le K hK_nn).trans hcGood_log, hcGood_sharp, href, hfib⟩

open scoped Classical in
/-- **The witness with the strong refinement coefficient and the anchor/carrier data exposed
(extra69, `rem:plankReductionWitnessStrong`).**

`Kakeya.representativeWitness_strong_uniform` declares its three quantitative clauses at
`c · a ^ (4η) · a ^ ε`.  Reading its own proof, the genuine composed coefficient is
`cAngle · (cGood - q)` with `q = cGood / 2`, and the two inputs `Cuni⁻¹ · a ^ ε ≤ cAngle` and
`cη · a ^ η ≤ cGood` bound it
below by `(cη · Cuni⁻¹ / 2) · a ^ η · a ^ ε` — **one** power of `η`.  The declared `a ^ (4η)` is a
pure weakening via `a ≤ 1`, and it discards `a ^ (3η)` of slack that Item 4 needs.  This
declaration returns everything `Kakeya.representativeWitness_strong_uniform` returns, including
the weakened clauses, and in addition:

* the strong coefficient `rRef` itself, with `ShadedBody.IsCRefinement s' Y'' s Y rRef`, `0 < rRef`,
  the *structural identity* `rRef = (cGood - q) · cAngle`, and the uniform lower bound
  `Cref⁻¹ · a ^ η · a ^ ε ≤ rRef` with `Cref` in the *outer* existential, so it is fixed before any
  configuration is seen.  The identity holds by `rfl` where the existential is introduced and costs
  nothing, but it is what lets a caller re-derive the coefficient's lower bound at an exponent of
  its *own* choosing: composed with `Kakeya.exists_absorb_strongRefinementCoeff` it gives
  `Cref'⁻¹ · a ^ η' · a ^ ε ≤ rRef` for every `η' > 0`.  The `η` in the bound returned here is not
  forced by the geometry — it is the exponent of the *polynomial* pigeonhole branch, and the sharp
  branch is sub-polynomial;
* the strong cardinality clause at `a ^ (2η) · a ^ ε` and the strong fullness clause at `rRef`;
* the fibre-pigeonhole coefficient `cGood` with **both** of its lower bounds, the polynomial
  `cEta · a ^ η ≤ cGood` and the sharp `(Cres · A(a))⁻¹ ≤ cGood`, the retained fraction
  `q = cGood / 2` with `0 < q`, and the pointwise fibre-retention inequality.  The last three are
  exactly the hypotheses of `Plank.hasCConstantMultiplicity_of_fibreRetention_real`;
* the anchor/carrier data of `Plank.ThickenedAnchorCarrierData`, at the uniform constant
  `Ccarrier = max cThk (4 · (2 · Cang₂ + 4 · Cθ) + 8)`, which dominates the
  representative-comparability constant `cThk` (needed for the shading to sit in the carrier at
  all), the good-cover dilation `4 · Cang + 8`, its
  `Cang₂` form, and the *enlarged* good-cover dilation `4 · Cang' + 8` at
  `Cang' = 2 · Cang₂ + 4 · Cθ`, which is the angle constant of the slab-local enlargement
  `Plank.mem_inSlabFamilyC_of_mem_shadeFibre_slabLocal`.  With it come the exact anchor
  volume `|Qanchor t| = 8θb²` and the step-5 carrier-volume bound
  `(θb/a) · 8ab ≤ |Qcarrier t|`, which is `hcarrierVolume` of
  `Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio`.

*The sharp bound is still the only one controlling the reserve scale.*  The polynomial bound
`cEta · a ^ η ≤ cGood` supplies the uniform constants `cP`, `cLam` and `Cref`; the sharp bound
`(Cres · A(a))⁻¹ ≤ cGood` is what `Kakeya.outScale_le_half_mul_reserve_mul` needs, and it cannot be
replaced by the polynomial one, whose reciprocal is a power of `a⁻¹`.  Here its free multiplier is
the already uniform pointwise overlap `Nov`: choosing `kappa ≥ 4 · Nov · Cres` returns typical angle
at `Nov · max 2 A(a)`.  The old `max 2 A(a)` conclusion is retained by
`Kakeya.IsTypicalPlankAngle.mono_scale`, so existing consumers do not lose information while a later
overlap-costing deletion receives the stronger clause.  There is still **no smallness threshold
`a < a₀`**.

*No parent constant-multiplicity statement is returned.*  The incoming typical-angle refinement is
a hypothesis, and nothing in the construction produces a
`ShadedBody.HasCConstantMultiplicity s Y C`, so the transport of
`Plank.hasCConstantMultiplicity_of_fibreRetention` has to be fed its scale hypothesis from
elsewhere.  Only the retention half is available here.

*The typed anchor view and the counting overlap bound.*  Three further clauses are returned, all
free from the construction, and all needed by the internal Item 2 clause:

* the **typed** `Prism3D (θ·b) b 1` view `Pr` of the anchor, with `(Pr t)_{nd} = Qθ t` on `𝒯`.  The
  anchor *is* the undilated thickening of the selected plank, so the typed reading is the same
  prism at a more informative type (`Plank.exists_typedAnchorPrism`);
* its **slab angle** `∠(Pr (repr i), Sl (slabOf (repr i))) ≤ Cang₂ · θ`, at the enlarged uniform
  constant `Cang₂ = 2·Cang + 16` that is now also returned, with `Cang ≤ Cang₂`,
  `4·Cang₂ + 8 ≤ Ccarrier`, `4·(2·Cang₂ + 4·Cθ) + 8 ≤ Ccarrier` and
  `4·(2·(2·Cang₂ + 4·Cθ) + 16) + 8 ≤ Ccarrier` (so
  `Ccarrier = max cThk (4·(2·(2·Cang₂ + 4·Cθ) + 16) + 8)` dominates every dilation scale in play,
  including the slab-local enlargement's and the *anchor-angle* enlargement).
  The enlargement is the price of the quasi-triangle inequality
  `Prism3D.angle_le_two_mul_add_angle` chaining the fibre member's own `Cang·θ` bound with the `8·θ`
  separation of two non-essentially-distinct thickenings;

* the **pointwise, slab-free** form of the same bound,
  `∠(Pr (repr i), Sl S) ≤ 2·∠(P i, Sl S) + 16·θ` for *every* `i ∈ s'` and *every* `S`
  (`Plank.angle_typedAnchor_le_two_mul_add`).  The clause above is useless to the slab-local
  assembly, which needs the anchor's angle at a slab that `slabOf` did **not** assign it to: a
  plank can lie geometrically in the enlarged slab family of `S` while its anchor was assigned
  elsewhere.  This clause is the same geometry stated without the assignment, and it is what the
  slab-local layer turns into the anchor-angle input of the internal Item 2 clause at the constant
  `2·Cang' + 16`;
* the **pointwise slab-overlap bound** `Nov`, also in the outer existential: at every point at most
  `Nov` of the slabs of `𝒮` have that point in their slab-family union
  (`Plank.slab_pointwise_overlap_le`).  This is the counting form of the overlap that the slab-local
  fullness layer turns into a bound with no `|𝒮|` loss; the aggregate `cOv` clause is the measure
  form and does not imply it. -/
theorem representativeWitness_strong_uniform (Cgeom : ℝ≥0) :
    ∃ (cThk Cset Cang Cang2 cOv cN Ccarrier : ℝ≥0) (Nov : ℕ),
      1 ≤ cThk ∧ 1 ≤ Cset ∧ 1 ≤ Cang ∧ 1 ≤ Cang2 ∧ Cang ≤ Cang2 ∧ 1 ≤ Nov ∧
      0 < cOv ∧ 1 ≤ cN ∧ cN ≤ 2 ∧
      1 ≤ Ccarrier ∧
      cThk ≤ Ccarrier ∧ 4 * Cang + 8 ≤ Ccarrier ∧ 4 * Cang2 + 8 ≤ Ccarrier ∧
      4 * (2 * Cang2 + 4 * Cgeom) + 8 ≤ Ccarrier ∧
      4 * (2 * (2 * Cang2 + 4 * Cgeom) + 16) + 8 ≤ Ccarrier ∧
      ∀ {η ε : ℝ}, 0 < η → 0 < ε →
      ∃ (cEta Cres : ℝ≥0) (kappa : ℝ),
        0 < cEta ∧ 0 < Cres ∧ 1 ≤ kappa ∧ 4 * (Nov : ℝ) * (Cres : ℝ) ≤ kappa ∧
      ∀ (Ctyp Cuni : ℝ≥0), 1 ≤ Cuni →
      ∃ (cP cLam Cref : ℝ≥0), 0 < cP ∧ 0 < cLam ∧ 1 ≤ Cref ∧
      ∀ {ι : Type*} (s : Finset ι)
        (Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (P : ι → Plank a b hab hb1)
        (θ : ℝ≥0) (hθ1 : θ ≤ 1) (cAngle cLamY : ℝ≥0),
        0 < a → a < 1 →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) →
        0 < cAngle → Cuni⁻¹ * a ^ ε ≤ cAngle → ShadedBody.IsCRefinement s Y' s Y cAngle →
        a / b ≤ θ → HasMaxPlankAngleBound s Y' P θ Cgeom →
        (∀ x ∈ ⋃ i ∈ s, (Y' i).shade, ∀ t ⊆ shadeFibre s Y' x,
          (plankReserveScale kappa a)⁻¹ * ((shadeFibre s Y' x).card : ℝ)
              ≤ (t.card : ℝ) →
            θ ≤ Ctyp * a ^ (-ε) * maxPlankAngle P t ∧
              maxPlankAngle P t ≤ Ctyp * a ^ (-ε) * θ) →
        (∀ i ∈ s, (Y' i).shade ⊆ (P i).carrier) →
        0 < cLamY → a ^ η ≤ cLamY → cLamY ≤ ShadedBody.fullness s Y →
        (∀ i ∈ s, 8 * (a : ENNReal) * (b : ENNReal) ≤ volume (Y' i).carrier) →
    ∃ (s' : Finset ι) (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (N : ℕ)
      (𝒯 : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
      (repr : ι → Plank.ThickenedPlank θ b hθ1 hb1)
      (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1) (𝒮 : Finset (Slab θ hθ1))
      (rRef cGood q : ℝ≥0)
      (acd : Plank.ThickenedAnchorCarrierData (Plank.ThickenedPlank θ b hθ1 hb1)
        s' Y'' Ccarrier cN N)
      (Pr : Plank.ThickenedPlank θ b hθ1 hb1 →
        Prism3D (θ * b) b 1 (Plank.thickenedWidth_le hθ1) hb1)
      (R : Plank.ThickenedRepr s' P θ hθ1 cThk),
      s' ⊆ s ∧
      (∀ i, (Y'' i).toConvexSpaceBody = (Y' i).toConvexSpaceBody) ∧
      (∀ i, (Y'' i).shade ⊆ (Y' i).shade) ∧
      ShadedBody.IsCRefinement s' Y'' s Y (cLam * a ^ (4 * η) * a ^ ε) ∧
      (cP * a ^ (4 * η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) ∧
      (cLam * a ^ (4 * η) * a ^ ε) * ShadedBody.fullness s Y ≤ ShadedBody.fullness s' Y'' ∧
      HasMaxPlankAngleBound s' Y'' P θ Cgeom ∧
      IsTypicalPlankAngle s' Y'' P θ (Ctyp * a ^ (-ε))
        (Real.toNNReal (max 2 (plankAngleScaleA a))) ∧
      1 ≤ N ∧
      𝒯 = s'.image repr ∧
      𝒮 = 𝒯.image slabOf ∧
      ((↑𝒯 : Set (Plank.ThickenedPlank θ b hθ1 hb1)).Pairwise
        (fun t u => PrismNDim.IsEssentiallyDistinct t.toPrismNDim u.toPrismNDim)) ∧
      ((↑𝒮 : Set (Slab θ hθ1)).Pairwise
        (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim)) ∧
      (∀ i ∈ s', repr i ∈ 𝒯 ∧
        (P i).carrier ⊆ ((repr i).toPrismNDim.dilation cThk).carrier ∧
        (((repr i)).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((P i).thickened θ hθ1).toPrismNDim.dilation cThk).carrier) ∧
      (∀ i ∈ s', slabOf (repr i) ∈ 𝒮 ∧
        i ∈ Plank.inSlabFamilyC Cset Cang s' P (slabOf (repr i))) ∧
      (cOv : ENNReal) *
          (∑ S ∈ 𝒮, volume (⋃ i ∈ Plank.inSlabFamilyC Cset Cang s' P S, (Y'' i).shade)) ≤
        volume (⋃ i ∈ s', (Y'' i).shade) ∧
      (∀ t ∈ 𝒯, (s'.filter (fun i => repr i = t)).Nonempty ∧
        (N : ℝ) / (cN : ℝ) ≤ ((s'.filter (fun i => repr i = t)).card : ℝ) ∧
          ((s'.filter (fun i => repr i = t)).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) ∧
      ShadedBody.IsCRefinement s' Y'' s Y rRef ∧
      0 < rRef ∧
      rRef = (cGood - q) * cAngle ∧
      Cref⁻¹ * a ^ η * a ^ ε ≤ rRef ∧
      (cP * a ^ (2 * η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) ∧
      rRef * ShadedBody.fullness s Y ≤ ShadedBody.fullness s' Y'' ∧
      q = cGood / 2 ∧ 0 < cGood ∧ 0 < q ∧
      cEta * a ^ η ≤ cGood ∧
      (Cres * Real.toNNReal (plankAngleScaleA a))⁻¹ ≤ cGood ∧
      (∀ x ∈ ⋃ i ∈ s', (Y'' i).shade,
        (q : ℝ) * ((shadeFibre s Y' x).card : ℝ) ≤ ((shadeFibre s' Y'' x).card : ℝ)) ∧
      (∀ i ∈ s', (Y'' i).shade ⊆
        (((repr i).toPrismNDim.dilation Ccarrier).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ t ∈ 𝒯, volume (t.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) ∧
      (∀ t ∈ 𝒯, ((θ * b / a : ℝ≥0) : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))
        ≤ volume ((t.toPrismNDim.dilation Ccarrier).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))) ∧
      acd.repr = repr ∧ acd.active = 𝒯 ∧
        acd.anchor = (fun t => (t : Plank.ThickenedPlank θ b hθ1 hb1).toPrismNDim) ∧
        acd.carrier =
          (fun t => (t : Plank.ThickenedPlank θ b hθ1 hb1).toPrismNDim.dilation Ccarrier) ∧
      (∀ t ∈ 𝒯, (Pr t).toPrismNDim = t.toPrismNDim) ∧
      (∀ i ∈ s', Prism3D.angle (Pr (repr i)) (slabOf (repr i))
        ≤ (Cang2 : ℝ) * (θ : ℝ)) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3),
        (𝒮.filter fun S => x ∈ ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s' P S,
          (Y'' i).shade).card ≤ Nov) ∧
      (∀ (S : Slab θ hθ1), ∀ i ∈ s', Prism3D.angle (Pr (repr i)) S
        ≤ 2 * Prism3D.angle (P i) S + 16 * (θ : ℝ)) ∧
      R.repr = repr ∧
      R.indexSet = 𝒯 ∧
      IsTypicalPlankAngle s' Y'' P θ (Ctyp * a ^ (-ε))
        (Real.toNNReal ((Nov : ℝ) * max 2 (plankAngleScaleA a))) := by
  classical
  -- Constants obtained before the configuration
  obtain ⟨cThk, hcThk, hER⟩ := Plank.exists_thickenedRepr
  obtain ⟨cOv, Cset, Cang, hcOv, hCset, hCang, hSMD⟩ :=
    Plank.slabMassDecomposition cThk Cgeom hcThk
  obtain ⟨Nov, hNov, hOverlap⟩ := Plank.slab_pointwise_overlap_le Cgeom Cset Cang hCang
  set Cang2 : ℝ≥0 := 2 * Cang + 16 with hCang2_def
  set Ccarrier := max cThk (4 * (2 * (2 * Cang2 + 4 * Cgeom) + 16) + 8) with hCcarrier_def
  -- `X ≤ 2 * X + Y` in `ℝ≥0`, the only inequality the constant bookkeeping below needs.
  have hle2 : ∀ X Y : ℝ≥0, X ≤ 2 * X + Y := fun X Y => by
    rw [two_mul]; exact le_add_self.trans le_self_add
  have hCang2_one : (1 : ℝ≥0) ≤ Cang2 := by
    rw [hCang2_def]; exact (by norm_num : (1 : ℝ≥0) ≤ 16).trans le_add_self
  have hCang_le_Cang2 : Cang ≤ Cang2 := by rw [hCang2_def]; exact hle2 Cang 16
  have hcThk_le_Ccarrier : cThk ≤ Ccarrier := le_max_left _ _
  have hCcarrier_one : (1 : ℝ≥0) ≤ Ccarrier := hcThk.trans hcThk_le_Ccarrier
  have hCang3Le_Ccarrier : 4 * (2 * (2 * Cang2 + 4 * Cgeom) + 16) + 8 ≤ Ccarrier := le_max_right _ _
  have hCang2EnlLe_Ccarrier : 4 * (2 * Cang2 + 4 * Cgeom) + 8 ≤ Ccarrier :=
    (add_le_add (mul_le_mul' le_rfl (hle2 _ 16)) le_rfl).trans hCang3Le_Ccarrier
  have hCang2Le_Ccarrier : 4 * Cang2 + 8 ≤ Ccarrier :=
    (add_le_add (mul_le_mul' le_rfl (hle2 Cang2 (4 * Cgeom))) le_rfl).trans hCang2EnlLe_Ccarrier
  have hCangLe_Ccarrier : 4 * Cang + 8 ≤ Ccarrier :=
    (add_le_add (mul_le_mul' le_rfl hCang_le_Cang2) le_rfl).trans hCang2Le_Ccarrier
  refine ⟨cThk, Cset, Cang, Cang2, cOv, 2, Ccarrier, Nov,
    hcThk, hCset, hCang, hCang2_one, hCang_le_Cang2, hNov,
    hcOv, one_le_two, le_refl 2, hCcarrier_one,
    hcThk_le_Ccarrier, hCangLe_Ccarrier, hCang2Le_Ccarrier, hCang2EnlLe_Ccarrier,
    hCang3Le_Ccarrier, ?_⟩
  -- Only from here on do `η` and `ε` enter scope: everything above is absolute (it depends on
  -- `Cgeom` alone), which is what makes the outer constant block uniform in `η` and `ε`.
  intro η ε hη hε
  obtain ⟨cη, Cres, hcη, hCres, hPig⟩ :=
    pigeonhole_of_phi_packing_sharp cThk hcThk hη
  set kappa : ℝ := 4 * (Nov : ℝ) * (Cres : ℝ) + 1 with hkappa_def
  have hkappa1 : (1 : ℝ) ≤ kappa := by
    rw [hkappa_def]; exact Plank.one_le_four_mul_natCast_mul_add_one Nov Cres
  have hkappaNov : 4 * (Nov : ℝ) * (Cres : ℝ) ≤ kappa := by
    rw [hkappa_def]; exact le_add_of_nonneg_right zero_le_one
  refine ⟨cη, Cres, kappa, hcη, hCres, hkappa1, hkappaNov, ?_⟩
  intro Ctyp Cuni hCuni
  set cP := cη * Cuni⁻¹ / 2 with hcP_def
  set cLam := cη * Cuni⁻¹ / 2 with hcLam_def
  set Cref := max 1 (cη * Cuni⁻¹ / 2)⁻¹ with hCref_def
  have hCref_one : (1 : ℝ≥0) ≤ Cref := le_max_left _ _
  have hCuni_inv_pos : (0 : ℝ≥0) < Cuni⁻¹ := inv_pos.mpr (lt_of_lt_of_le one_pos hCuni)
  have hcP_pos : (0 : ℝ≥0) < cη * Cuni⁻¹ / 2 := by positivity
  refine ⟨cP, cLam, Cref, hcP_pos, hcP_pos, hCref_one, ?_⟩
  intro ι s Y Y' a b hab hb1 P θ hθ1 cAngle cLamY ha0 ha1 hed hcAngle hcAngleLB
    hrefAngle hθa hangS hstabRes hYP' hcLamY hlamYlb hlamY hcarvol
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  -- derive a ≤ θ from a / b ≤ θ and b ≤ 1
  have haθ : a ≤ θ :=
    ((div_le_iff₀ hb0).mp hθa).trans (by simpa using mul_le_mul' (le_refl θ) hb1)
  have ha1le : a ≤ 1 := hab.trans hb1
  -- Step 1: thickened representatives on the full family.
  obtain ⟨R⟩ := hER s P θ hθ1 ha0 hθa
  -- Step 2: convert essential-distinctness hypothesis to the form needed by the pigeonhole.
  have hED : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      PrismNDim.IsEssentiallyDistinct (P i).toPrismNDim (P j).toPrismNDim :=
    fun i hi j hj hne => by
      simpa [PrismNDim.IsEssentiallyDistinct] using
        hed (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hne
  -- Step 3: the dyadic fibre-size pigeonhole (retains mass, fixes the fibre size),
  -- returning both the polynomial and the sharp retention bound.
  obtain ⟨s₂, N, cGood, cN, hs₂sub, hN, hcN, hcN2, hcGood, hcGoodSharp, href₂, hfibcard⟩ :=
    hPig s P θ hθ1 R Y' ha0 ha1 hED
  have hcGoodpos : 0 < cGood := lt_of_lt_of_le (by positivity) hcGood
  have hshadePY' : ∀ i ∈ s₂, (Y' i).shade ⊆ (P i).carrier :=
    fun i hi => hYP' i (hs₂sub hi)
  -- Step 4: the good-point deletion at the retained fraction `q = cGood / 2`, paid for by the
  -- reserve scale through the sharp pigeonhole bound.
  set q : ℝ≥0 := cGood / 2 with hq_def
  have hqc : q < cGood := by rw [hq_def]; exact NNReal.half_lt_self hcGoodpos.ne'
  have hmNov : (1 : ℝ) ≤ (Nov : ℝ) := by exact_mod_cast hNov
  have hbudget : (Nov : ℝ) * max 2 (plankAngleScaleA a) ≤
      (q : ℝ) * plankReserveScale kappa a := by
    have htemp := outScale_le_half_mul_reserve_mul hCres hmNov hkappaNov ha0 ha1 hcGoodSharp
    simpa [hq_def, NNReal.coe_div] using htemp
  obtain ⟨Y'', hbody, hshade, href'', htypReserve, hkeep⟩ :=
    typicalAngleAfterReserveDeletion_reserve hs₂sub Y' P θ (Ctyp * a ^ (-ε)) hkappa1 hmNov
      hqc hbudget href₂ hstabRes
  have hAout_pos : 0 < Real.toNNReal (max 2 (plankAngleScaleA a)) :=
    Real.toNNReal_pos.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hAout_nonneg : (0 : ℝ) ≤ max 2 (plankAngleScaleA a) :=
    le_trans (by norm_num) (le_max_left _ _)
  have htyp : IsTypicalPlankAngle s₂ Y'' P θ (Ctyp * a ^ (-ε))
      (Real.toNNReal (max 2 (plankAngleScaleA a))) :=
    htypReserve.mono_scale hAout_pos
      (Real.toNNReal_mono (le_mul_of_one_le_left hAout_nonneg hmNov))
  -- Step 5: the angle input.  Only the *upper* bound is needed, and it is monotone, so the
  -- deletion costs nothing here.
  have hangS₂ : HasMaxPlankAngleBound s₂ Y'' P θ Cgeom :=
    hangS.mono hs₂sub (fun i hi => hshade i)
  have hshadeP : ∀ i ∈ s₂, (Y'' i).shade ⊆ (P i).carrier :=
    fun i hi => (hshade i).trans (hYP' i (hs₂sub hi))
  -- Step 6: the slab decomposition on the refined family.
  obtain ⟨SA, hSpair, hG1⟩ := hSMD s₂ P Y'' θ hθ1 (R.restrict hs₂sub) ha0 haθ hangS₂ hshadeP
  -- Step 7: the plank volume, and the derived total-mass lower bound.
  have hvol : ∀ i, volume (P i).carrier = 8 * (a : ENNReal) * (b : ENNReal) := fun i => by
    rw [Prism3D.volume_carrier (P i)]; simp
  have hVne : (8 * (a : ENNReal) * (b : ENNReal)) ≠ 0 := by
    have : (a : ENNReal) ≠ 0 := by exact_mod_cast ha0.ne'
    have hb : (b : ENNReal) ≠ 0 := by exact_mod_cast hb0.ne'
    simp [this, hb]
  have hVtop : (8 * (a : ENNReal) * (b : ENNReal)) ≠ ⊤ := by
    simp [ENNReal.mul_ne_top, ENNReal.coe_ne_top]
  have hfullY' : cAngle * cLamY ≤ ShadedBody.fullness s Y' :=
    le_trans (by gcongr) (refinement_fullness_le hrefAngle)
  have hmass : ((cAngle * cLamY : ℝ≥0) : ENNReal) *
      ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))
      ≤ ∑ i ∈ s, volume (Y' i).shade :=
    ShadedBody.coe_fullness_mul_le_sum_volume_shade s Y' hfullY' hcarvol
  -- Step 8: cardinality retention (still using Y' mass, which dominates Y'' mass).
  have hupper : ∑ i ∈ s₂, volume (Y' i).shade
      ≤ (s₂.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    calc ∑ i ∈ s₂, volume (Y' i).shade
        ≤ ∑ _i ∈ s₂, (8 * (a : ENNReal) * (b : ENNReal)) :=
          Finset.sum_le_sum fun i hi => (measure_mono (hshadePY' i hi)).trans (hvol i).le
      _ = (s₂.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hVX : (8 * (a : ENNReal) * (b : ENNReal)) *
        ((((cGood * (cAngle * cLamY)) * (s.card : ℝ≥0) : ℝ≥0)) : ENNReal)
      ≤ (8 * (a : ENNReal) * (b : ENNReal)) * (((s₂.card : ℝ≥0)) : ENNReal) := by
    calc (8 * (a : ENNReal) * (b : ENNReal)) *
            ((((cGood * (cAngle * cLamY)) * (s.card : ℝ≥0) : ℝ≥0)) : ENNReal)
        = (cGood : ENNReal) * (((cAngle * cLamY : ℝ≥0) : ENNReal) *
            ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))) := by
          push_cast; ring
      _ ≤ (cGood : ENNReal) * (∑ i ∈ s, volume (Y' i).shade) := by gcongr
      _ ≤ ∑ i ∈ s₂, volume (Y' i).shade := href₂.2
      _ ≤ (s₂.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := hupper
      _ = (8 * (a : ENNReal) * (b : ENNReal)) * (((s₂.card : ℝ≥0)) : ENNReal) := by
          push_cast; ring
  have hcard : (cGood * (cAngle * cLamY)) * (s.card : ℝ≥0) ≤ (s₂.card : ℝ≥0) := by
    have h := (ENNReal.mul_le_mul_iff_right hVne hVtop).mp hVX
    exact_mod_cast h
  -- Step 9: the deletion cost.  With `q = cGood / 2` the surviving refinement constant is
  -- `cGood - q = cGood / 2`, still bounded below by half the polynomial retention.
  have hq_half : cGood - q = cGood / 2 := by
    rw [hq_def]; exact tsub_eq_of_eq_add (add_halves cGood).symm
  have hgood2 : cη * a ^ η / 2 ≤ cGood - q := by rw [hq_half]; gcongr
  -- Step 10: the composed refinement.  The `a ^ η` bound is the genuine one; the `a ^ (4 * η)`
  -- and `a ^ (2 * η)` clauses are pure weakenings of it through `a ≤ 1`.
  have ha_pow_ineq : a ^ (4 * η) ≤ a ^ η :=
    NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1le (by linarith)
  have ha_pow_2η : a ^ (4 * η) ≤ a ^ (2 * η) :=
    NNReal.rpow_le_rpow_of_exponent_ge ha0 ha1le (by linarith)
  have ha_pow_sq : a ^ (2 * η) = a ^ η * a ^ η := by
    rw [show (2 * η : ℝ) = η + η by ring, NNReal.rpow_add ha0.ne']
  have h_const_ref_eta : (cη * Cuni⁻¹ / 2) * a ^ η * a ^ ε ≤ (cGood - q) * cAngle :=
    calc (cη * Cuni⁻¹ / 2) * a ^ η * a ^ ε = (cη * a ^ η / 2) * (Cuni⁻¹ * a ^ ε) := by ring
      _ ≤ (cGood - q) * cAngle := mul_le_mul' hgood2 hcAngleLB
  have h_const_ref : (cη * Cuni⁻¹ / 2) * a ^ (4 * η) * a ^ ε ≤ (cGood - q) * cAngle :=
    (mul_le_mul' (mul_le_mul' le_rfl ha_pow_ineq) le_rfl).trans h_const_ref_eta
  have hcomp : ShadedBody.IsCRefinement s₂ Y'' s Y ((cGood - q) * cAngle) := by
    simpa [mul_comm] using href''.trans hrefAngle
  have h_refinement : ShadedBody.IsCRefinement s₂ Y'' s Y (cLam * a ^ (4 * η) * a ^ ε) :=
    ⟨hcomp.1, (mul_le_mul' (ENNReal.coe_le_coe.mpr h_const_ref) le_rfl).trans hcomp.2⟩
  -- Step 11: cardinality retention
  have hcard_const_strong :
      (cη * Cuni⁻¹ / 2) * a ^ (2 * η) * a ^ ε ≤ cGood * (cAngle * cLamY) :=
    calc (cη * Cuni⁻¹ / 2) * a ^ (2 * η) * a ^ ε
        = ((cη * Cuni⁻¹ / 2) * a ^ η * a ^ ε) * a ^ η := by rw [ha_pow_sq]; ring
      _ ≤ ((cGood - q) * cAngle) * cLamY := mul_le_mul' h_const_ref_eta hlamYlb
      _ ≤ cGood * (cAngle * cLamY) := by rw [mul_assoc]; exact mul_le_mul' tsub_le_self le_rfl
  have hcard_const : (cη * Cuni⁻¹ / 2) * a ^ (4 * η) * a ^ ε ≤ cGood * (cAngle * cLamY) :=
    (mul_le_mul' (mul_le_mul' le_rfl ha_pow_2η) le_rfl).trans hcard_const_strong
  have h_card_retention : (cP * a ^ (4 * η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s₂.card : ℝ≥0) :=
    (mul_le_mul' hcard_const le_rfl).trans hcard
  -- Step 12: fullness transport
  have h_lam_fullness : (cLam * a ^ (4 * η) * a ^ ε) * ShadedBody.fullness s Y ≤
      ShadedBody.fullness s₂ Y'' :=
    refinement_fullness_le h_refinement
  -- Step 13: the subset inclusion 𝒮 ⊆ SA.used.
  have hsub𝒮 : (R.restrict hs₂sub).indexSet.image SA.slabOf ⊆ SA.used := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨t, ht, rfl⟩ := hS
    rw [Plank.ThickenedRepr.indexSet, Finset.mem_image] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact SA.slabOf_mem i hi
  -- The strong refinement coefficient `rRef` and the constants attached to it.
  set rRef : ℝ≥0 := (cGood - q) * cAngle with hrRef_def
  have hpos_rRef : 0 < rRef := mul_pos (tsub_pos_of_lt hqc) hcAngle
  have hCref_inv_le_cP : Cref⁻¹ ≤ cη * Cuni⁻¹ / 2 := by
    have h := inv_anti₀ (inv_pos.mpr hcP_pos) (le_max_right 1 (cη * Cuni⁻¹ / 2)⁻¹)
    rwa [inv_inv] at h
  have hCref_lower : Cref⁻¹ * a ^ η * a ^ ε ≤ rRef :=
    (mul_le_mul' (mul_le_mul' hCref_inv_le_cP le_rfl) le_rfl).trans h_const_ref_eta
  have h_card_retention_strong :
      (cP * a ^ (2 * η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s₂.card : ℝ≥0) :=
    (mul_le_mul' hcard_const_strong le_rfl).trans hcard
  -- Strong fullness transport at rRef
  have h_rRef_fullness : rRef * ShadedBody.fullness s Y ≤ ShadedBody.fullness s₂ Y'' :=
    refinement_fullness_le hcomp
  -- Shading containment in the dilated carrier
  have h_shade_carrier : ∀ i ∈ s₂, (Y'' i).shade ⊆
      (((R.repr i).dilation Ccarrier).carrier : Set (EuclideanSpace ℝ (Fin 3))) := fun i hi =>
    (hshadeP i hi).trans (((R.restrict hs₂sub).subset_repr i hi).trans
      (PrismNDim.dilation_carrier_mono (R.repr i).toPrismNDim hcThk_le_Ccarrier))
  -- Anchor volume: Qθ = id, so the anchor is the undilated representative
  have h_anchor_vol : ∀ t ∈ (R.restrict hs₂sub).indexSet,
      volume (t.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) :=
    Plank.volume_indexSet_eq (R.restrict hs₂sub)
  -- Carrier volume lower bound: use ratio_mul_plankVolume_ennreal then the anchor volume
  have h_carrier_vol : ∀ t ∈ (R.restrict hs₂sub).indexSet,
      ((θ * b / a : ℝ≥0) : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))
      ≤ volume ((t.toPrismNDim.dilation Ccarrier).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    fun t ht => by
      rw [Plank.ratio_mul_plankVolume_ennreal (ne_of_gt ha0), ← h_anchor_vol t ht]
      exact measure_mono (PrismNDim.self_subset_dilation t.toPrismNDim hCcarrier_one)
  -- Build the thickened anchor carrier data
  have h𝒯_active : (R.restrict hs₂sub).indexSet = s₂.image R.repr := by
    simp [Plank.ThickenedRepr.indexSet, Plank.ThickenedRepr.restrict_repr]
  have hfibreClause : ∀ t ∈ (R.restrict hs₂sub).indexSet,
      (s₂.filter (fun i => R.repr i = t)).Nonempty ∧
      (N : ℝ) / ((2 : ℝ≥0) : ℝ) ≤ ((s₂.filter (fun i => R.repr i = t)).card : ℝ) ∧
      ((s₂.filter (fun i => R.repr i = t)).card : ℝ) ≤ ((2 : ℝ≥0) : ℝ) * (N : ℝ) := by
    intro t ht
    rw [Plank.ThickenedRepr.indexSet, Finset.mem_image] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    have h_nonempty : (s₂.filter (fun j => R.repr j = R.repr i)).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
    obtain ⟨hfib_low, hfib_high⟩ := hfibcard _
      (by rw [Plank.ThickenedRepr.indexSet]; exact Finset.mem_image_of_mem _ (hs₂sub hi))
      h_nonempty
    have hcNpos : (0 : ℝ) < (cN : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos hcN
    have hcN2R : (cN : ℝ) ≤ ((2 : ℝ≥0) : ℝ) := by exact_mod_cast hcN2
    exact ⟨h_nonempty, le_trans (by gcongr) hfib_low, hfib_high.trans (by gcongr)⟩
  obtain ⟨acd, hacd₁, hacd₂, hacd₃, hacd₄⟩ :=
    Plank.exists_thickenedAnchorCarrierData (τ := Plank.ThickenedPlank θ b hθ1 hb1) s₂ Y'' R.repr
      (R.restrict hs₂sub).indexSet (fun t : Plank.ThickenedPlank θ b hθ1 hb1 => t.toPrismNDim)
      Ccarrier 2 N hCcarrier_one
      h𝒯_active (R.restrict hs₂sub).indexSet_pairwise h_shade_carrier hfibreClause
  have hθ0 : 0 < θ := lt_of_lt_of_le ha0 haθ
  obtain ⟨Pr, hPrEq, hPrAngle⟩ :=
    Plank.exists_typedAnchorPrism (R.restrict hs₂sub) hθ0 hb0
  -- Build the final existential
  refine ⟨s₂, Y'', N,
    (R.restrict hs₂sub).indexSet, R.repr, SA.slabOf,
    (R.restrict hs₂sub).indexSet.image SA.slabOf,
    rRef, cGood, q, acd, Pr, R.restrict hs₂sub,
    hs₂sub, hbody, hshade, h_refinement, h_card_retention,
    h_lam_fullness, hangS₂, htyp, hN,
    ?_, ?_, (R.restrict hs₂sub).indexSet_pairwise, ?_, ?_, ?_, ?_, hfibreClause,
    hcomp, hpos_rRef, hrRef_def, hCref_lower, h_card_retention_strong, h_rRef_fullness,
    hq_def, hcGoodpos, ?_, hcGood, hcGoodSharp, hkeep,
    h_shade_carrier, ?_, ?_,
    hacd₁, hacd₂, hacd₃, hacd₄, ?_, ?_, ?_, ?_, ?_, ?_, htypReserve⟩
  · -- 𝒯 = s'.image repr
    simp [Plank.ThickenedRepr.indexSet, Plank.ThickenedRepr.restrict_repr]
  · -- 𝒮 = 𝒯.image slabOf
    rfl
  · -- `𝒮` is pairwise essentially distinct
    simpa using hSpair.mono (Finset.coe_subset.mpr hsub𝒮)
  · -- plank / representative clause (directed)
    exact fun i hi => ⟨(R.restrict hs₂sub).repr_mem_indexSet hi,
      (R.restrict hs₂sub).subset_repr i hi, (R.restrict hs₂sub).repr_subset_thickened i hi⟩
  · -- slab membership
    exact fun i hi => ⟨Finset.mem_image_of_mem SA.slabOf
      ((R.restrict hs₂sub).repr_mem_indexSet hi), SA.mem_inSlabFamily i hi⟩
  · -- Shrinking the index set from `SA.used` to `𝒮` only decreases the left-hand sum.
    refine le_trans ?_ hG1
    gcongr
  · -- 0 < q
    rw [hq_def]; positivity
  · -- anchor volume
    exact fun t ht => by simpa using h_anchor_vol t ht
  · -- carrier volume bound
    exact fun t ht => by simpa using h_carrier_vol t ht
  · -- the typed anchor view sits over the anchor
    exact fun t ht => by simpa using hPrEq t ht
  · -- the typed anchor's slab angle, at the enlarged uniform constant `Cang2`
    intro i hi
    have hfam : ∀ j ∈ s₂, (R.restrict hs₂sub).repr j = R.repr i →
        j ∈ Plank.inSlabFamilyC Cset Cang s₂ P (SA.slabOf (R.repr i)) :=
      fun j hj hjeq => hjeq ▸ SA.mem_inSlabFamily j hj
    rw [show ((Cang2 : ℝ≥0) : ℝ) = 2 * (Cang : ℝ) + 16 by rw [hCang2_def]; push_cast; ring]
    simpa using hPrAngle Cset Cang (SA.slabOf (R.repr i)) (R.repr i)
      ((R.restrict hs₂sub).repr_mem_indexSet hi) hfam
  · -- the pointwise slab-overlap bound, restricted from `SA.used` to `𝒮`
    exact fun x => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hsub𝒮))
      (hOverlap s₂ P Y'' hθ1 (R.restrict hs₂sub).repr SA hθ0 hangS₂ hshadeP hSpair x)
  · -- the typed anchor's angle to an *arbitrary* slab, pointwise in the plank
    exact Plank.angle_typedAnchor_le_two_mul_add (R.restrict hs₂sub) hθ0 hb0 Pr hPrEq
  · -- the returned `ThickenedRepr` carries the same representative map
    exact Plank.ThickenedRepr.restrict_repr R hs₂sub
  · -- the returned `ThickenedRepr` carries the same active family
    simp

/- Historical design check for the superseded delta-parameterized statement of GWZ Lemma 6.13:
reduction of a plank incidence problem to a thickened-plank/slab incidence
problem.  The geometric work is supplied by the upstream geometry modules; this declaration
performs the final witness construction and assembly.

As in `representativeWitness_strong_uniform`, the plank/representative containment is
`cThk`-dilated and slab membership is the controlled `Plank.inSlabFamilyC Cset Cang`.  The paper
suppresses these fixed comparability constants; see the note on
`representativeWitness_strong_uniform` for why exact containment and strict slab membership are
not available.

Two interface changes relative to the earlier statement.

*Shaded planks.*  The input is a family of `ShadedPlank`s rather than a plank family `P` plus an
unrelated `ShadedBody` family `Y` plus coherence hypotheses.  `ShadedPlank` bundles the plank and
the shading over one `ConvexSpaceBody`, exactly as `ShadedTube` does for tubes, so
`(Y i).shade ⊆ (P i).carrier` becomes the structure field `shade_subset` and the carrier equality
`(Y i).carrier = (P i).carrier` becomes definitional.  The hypothesis `hYP` therefore disappears,
and the carrier-volume coherence that the witness needs (`8ab ≤ volume (Y i).carrier`) is now a
theorem, `ShadedPlank.volume_carrier`.  The low-level witness API stays unbundled: it still takes
separate `V` and `Y` arguments, which the assembly supplies as `ShadedPlank.planks Y` and
`ShadedPlank.bodies Y`.

*Uniform angle constant.*  `Cθ` is quantified **before** the index type and the finite
configuration, alongside `c₂`, `c₄`, `cNmax` and `cOvMin`.  This is not bookkeeping: it is the sole
source of nondegeneracy for the typical-angle data.  `HasMaxPlankAngleBound s' Y' P θ Cθ` asserts
only `maxPlankAngle P (𝒫_{Y'}(x)) ≤ Cθ · θ` pointwise, and `maxPlankAngle` is capped at `1` by
construction (`Kakeya.maxPlankAngle_mem_Icc`).  So if `Cθ` were chosen after the configuration, one
could take `Cθ ≥ (a / b)⁻¹` and the clause would hold for *every* `θ ≥ a / b`, in particular for the
content-free minimum `θ = a / b` with `N = 1`; the angle clause would then assert nothing at all
about the actual angular geometry of the family.  Fixing `Cθ` first forbids this: `θ` must be at
least `Cθ⁻¹` times the genuine maximal plank angle at every retained point, so the selected `θ`
really is the family's angle scale up to an absolute factor.  The constant is achievable
absolutely — `Kakeya.findingTypicalAngleOfIntersection` produces the upper bound with `Cθ = 1`,
because `Kakeya.constantTypicalAngle` picks `θ` as the upper endpoint of the dyadic angle band and
spends its factor `2` only on the lower bound `θ ≤ 2 · maxPlankAngle`.  No lower bound on `N` and
no ad hoc exclusion of `θ = a / b` is added; the nondegeneracy comes from the uniform `Cθ` alone.

*Two-sided typical angle.*  The angle conclusion is the two-sided
`Kakeya.IsTypicalPlankAngle s' Y' (ShadedPlank.planks Y) θ (Cθ * a ^ (-ε))
(Real.toNNReal (plankAngleScaleA a))`.  It asserts both `θ ≤ Cθ · a ^ (-ε) · maxPlankAngle` and
`maxPlankAngle ≤ Cθ · a ^ (-ε) · θ` on every shade fibre of the refined family, *and* the same
two-sided comparison on every sub-fibre retaining a `(Real.toNNReal (plankAngleScaleA a))⁻¹`
fraction of that fibre — the stability clause, at stability scale
`Real.toNNReal (plankAngleScaleA a)`.  The one-sided `Kakeya.HasMaxPlankAngleBound` is what the slab
layer consumes and is monotone under refinement, but it is strictly weaker, and the lower bound is
what stops the content-free choice `θ = a / b`.  Restoring the lower bound after the fibre
pigeonhole is the pointwise fibre-retention step of
`Kakeya.representativeWitness_strong_uniform`, which pays for it out of the reserve scale
`Kakeya.plankReserveScale kappa a` and therefore needs no smallness threshold on `a`; the
witness delivers the clause at `max 2 (plankAngleScaleA a)`, and
`Kakeya.IsTypicalPlankAngle.mono_scale` brings it back down to `plankAngleScaleA a` here.

*Uniform density constants.*  `c₂` and `C₄` — the two constants carrying the actual density content
of items 2 and 4 — are quantified **before** the index type and the finite configuration.  They may
depend only on `η` and on absolute geometric constants; they may not depend on `a`, `b`, `N`,
`C₀`, `s`, `Y`, `θ`, or the selected slabs.  Without this order the statement is nearly vacuous:
`c₂` could be taken to be the actual infimum of the finitely many fullnesses and `C₄` whatever
cancels the crude bound, and neither clause would assert anything uniform.

*Item 4's constant is declared as an upper bound, and its coefficient carries `a ^ (-ε)`.*  `C₄`
multiplies the right-hand side of an *upper* bound on `μ(s, Y)`, so `0 < C₄` bounds nothing and
would leave arbitrarily strong claims admissible; the clause is therefore stated with `1 ≤ C₄`, the
discipline already used for `Cθ`, `cThk`, `Cset`, `Cang` and `cN`.  The coefficient also carries an
explicit `a ^ (-ε)` beside the paper's `a ^ (-(4η))`.  That factor is the reciprocal of the
typical-angle refinement loss `a ^ ε` which the symbolic reduction
`Kakeya.multiplicityReduction_of_refinement_and_fullness_ratio` reads off the strong refinement
coefficient `rRef`, and it cannot be folded into the `a ^ (-(4η))`: `ε` and `η` are quantified
independently, so no fixed multiple of `η` dominates `ε` and `a ^ (-ε)` is bounded by no
`a ^ (-Cη)` uniformly in the two exponents.  The exponent of `a` stays at the paper's `4η`, which is
reachable once the refinement loss is charged at its true sub-polynomial rate through
`Kakeya.exists_absorb_strongRefinementCoeff`.

To make `C₄` definable from uniform data, two auxiliary uniform constants are exposed alongside it,
`cNmax` and `cOvMin`, together with the conclusions `cN ≤ cNmax` and `cOvMin ≤ c₃`.  These are the
"fibre" and "overlap" constants that the multiplicity-reduction algebra multiplies together, and
both are genuinely uniform: `Plank.ThickenedRepr.pigeonholeThickenedMultiplicity` returns the
literal `cN = 2`, and `Plank.slabMassDecomposition` binds its overlap constant before the
configuration.  The remaining factor in `C₄`, the refinement constant `cLam`, is *not* uniformly
bounded below — it carries the dyadic pigeonhole loss `(log₂|s| + 1)⁻¹` and the typical-angle loss
`a ^ ε` — so the proof must absorb those into the `a ^ (-(4η)) · a ^ (-ε)` slack using the packing
bound `Plank.ThickenedRepr.phi_packing_bound`, which turns `log₂|s|` into a polynomial in `a⁻¹`,
`b⁻¹` and `θ⁻¹`.  `cLam` therefore stays at configuration level.

*The remaining comparability constants are uniform too.*  `cThk`, `Cset` and `Cang` are now
quantified alongside `c₂`, `C₄`, `cNmax`, `cOvMin` and `Cθ`, keeping `1 ≤ cThk`, `1 ≤ Cset`,
`1 ≤ Cang`.  This is the honest position rather than a strengthening for its own sake: they are
produced by `Plank.exists_thickenedRepr` and `Plank.exists_pairwiseDistinct_slabAssignment`, both of
which bind their constants before any configuration, so nothing is lost.  Left inside the inner
existential they were free weakening knobs — an arbitrarily large `cThk` makes the containment
`(Y i).carrier ⊆ (Qθ (repr i)).dilation cThk` and the comparability clause vacuous, and an
arbitrarily large `Cset`/`Cang` makes `Plank.inSlabFamilyC Cset Cang` the whole family, so the slab
clause and Item 2 would say nothing about the slab geometry.

*The Item 1 density constant is controlled from outside.*  `c₁` still has to be chosen after the
configuration (it inherits the ball-refinement losses), so instead of moving it out, a uniform
lower control `c1min` is quantified before the configuration with `0 < c1min`, and the conclusion
carries `c1min ≤ c₁`.  This is the same device already used for `cN ≤ cNmax` and `cOvMin ≤ c₃`.
Without it `0 < c₁` alone is a vacuity hole: `c₁` could be taken to be the actual infimum of the
finitely many captured density ratios and Item 1 would assert nothing uniform.

*Item 1 uses the literal dilation factor `3`.*  The configuration-level constant `K` is deleted and
the outer ball has radius `3 · (θ b)`.  The factor is not a free parameter: it is exactly what
`Plank.denseBall_arbitraryCentre_fullness` produces, where `3` comes from the triangle inequality
`B(c, r) ⊆ B(x, 3r)` for a retained dense ball `B(c, r)` containing a point of `B(x, r)`.  An
existentially quantified `K` would let the outer ball swallow the whole configuration.

*The active families are exactly the images.*  Two equalities are added, `𝒯 = s'.image repr` and
`𝒮 = 𝒯.image slabOf`.  Without them `𝒯` could carry spurious members with empty `repr`-fibres (on
which the fibre-cardinality clause is vacuous by its own `Nonempty` guard) and `𝒮` could carry
slabs assigned to nothing, so the per-slab clauses of Items 2 and 3 would range over indices
with no geometric content.  With them, every member of `𝒯` has a nonempty fibre and every
member of `𝒮` is the slab of an active representative.  Both hold for
`representativeWitness_strong_uniform` by construction.

*The slab family is nondegenerate.*  `𝒮` is pairwise essentially distinct as a family of prisms.
This is not new packing theory: `Plank.exists_pairwiseDistinct_slabAssignment` selects into a
maximal essentially-distinct family, `Plank.slabMassDecomposition` now returns that property, and
`representativeWitness_strong_uniform` threads it through.  The `Finset σ` structure of `𝒮`
alone gives nothing here: `σ` is an existentially quantified index type and `Sl` need not be
injective, so without this clause `Sl` could collapse all of `𝒮` onto a single slab, or onto
mutually non-distinct ones, and
the slab decomposition would carry no packing content at all.

*Carrier coherence for the thickened shading.*  The clause `(Yθ t).carrier = (Qθ t).carrier` on
`𝒯` is what pins `Yθ` to the representative prisms: without it `Yθ t` could be given a huge carrier
(making Item 2's fullness lower bound harder but Item 4's multiplicity comparison free) or a tiny
one.  It holds definitionally for the intended witness
`Plank.sharedSlabThickenedShadingDilation`
(`Plank.sharedSlabThickenedShadingDilation_carrier`), and it is what lets Item 2's aggregate
fullness bound be read against the representative prisms.

The `hcard` exponent is named `Nexp` so that it no longer shadows the fibre size `N`.

*The refinement losses are quantitative, and `C₀`, `Nexp` come first.*  The paper's conclusion is
`|𝒫'| ⪆ |𝒫|` and `λ(𝒫', Y') ⪆ λ(𝒫, Y)`, i.e. the two losses are sub-polynomial.  `0 < cP` and
`0 < cLam` do not formalise that: a positive constant chosen after the finite configuration can be
the actual retained fraction of that configuration.  Two uniform lower controls `cPmin` and
`cLamMin` are therefore quantified before the index type, and the conclusion carries
`cPmin · a ^ (4η) · a ^ η ≤ cP` and `cLamMin · a ^ (4η) · a ^ η ≤ cLam`.  For the uniform constants
to exist at all, the two data of the plank-count hypothesis, `C₀` and `Nexp`, must be fixed before
the configuration as well — the typical-angle refinement loss genuinely depends on them — so they
are now arguments of the theorem rather than universally quantified inside it.  `cPmin` and
`cLamMin` may depend only on `η`, `C₀`, `Nexp` and absolute geometric constants.

The two declared powers are the checked product of the three losses, with slack.  Taking `ε := η`
in GWZ Lemma 6.11 gives the typical-angle refinement loss
`C⁻¹ · a ^ η` with `C = C(η, C₀, Nexp) ≥ 2` uniform; `Plank.ThickenedRepr.pigeonhole_of_phi_packing`
gives the fibre-pigeonhole loss `cη · a ^ η` with `cη = cη(η)` uniform; and the incoming fullness
lower bound is `a ^ η`.  `Kakeya.representativeWitness_strong_uniform` composes exactly these:
its refinement/fullness constant is `cGood · cAngle ≥ (cη / C) · a ^ η · a ^ η` and its cardinality
constant is `cGood · cAngle · cLamY ≥ (cη / C) · a ^ (2η) · a ^ η`.  Since `a ≤ 1`, the stated
bounds with the exponent `4η` are weaker than those two, the remaining margin `a ^ (3η)`
resp. `a ^ (2η)` being what the two density-refinement steps (dense-ball restriction and the
good-cover fibre deletion) are allowed to spend.  What matters for fidelity is the shape: a fixed
uniform positive constant times *declared* powers of `a`, and no unconstrained positive
existential chosen after the configuration.

*Directed thickening containment.*  The plank/representative clause is the conjunction of the two
containments
`(Y i).carrier ⊆ (Qθ (repr i)).dilation cThk` and
`(Qθ (repr i)).carrier ⊆ ((𝒫 i)_θ).dilation cThk`,
rather than the second one weakened to the disjunction `PrismNDim.IsCComparable`, which leaves open
which containment holds and therefore supplies no upper control on the representative.  Both are
returned by `Kakeya.representativeWitness_strong_uniform` (they are the two containment fields of
`Plank.ThickenedRepr`); `Plank.ThickenedRepr.comparable` still recovers the undirected form.

*Nonempty fibres.*  Since `𝒯 = s'.image repr`, every `t ∈ 𝒯` has a nonempty `repr`-fibre in `s'`.
That is now part of the conclusion, and the fibre-cardinality bounds are stated unconditionally on
`𝒯` instead of under a `Nonempty` guard that would make them vacuous on a spurious member. -/
end Kakeya

end
