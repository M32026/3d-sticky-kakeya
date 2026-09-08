/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap
public import Kakeya.Multiplicity
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# Relative transport of constant multiplicity

Two reusable facts about `ShadedBody.HasCConstantMultiplicity`, both *relative*: they compare a
family with a refinement of itself, and neither produces a configuration-independent absolute
bound of the shape `∑_i |Y_i| ≤ Λ · |U|`.  (Such a bound does **not** follow from constant
multiplicity alone, and nothing here asserts one.)

* `Plank.hasCConstantMultiplicity_of_fibreRetention` transports constant multiplicity along a
  refinement that retains a `q`-fraction of every point fibre.  The scale degrades from `C` to
  `C / q`, but the statement is division-free (`C ≤ q * C'` in the hypothesis, conclusion at `C'`).

* `Plank.isCRefinement_restrictShade_of_dense` restricts every shading to a common measurable set
  `G` that captures a `ρ`-fraction of the *union*, and concludes that the restricted family is a
  `ρ / C`-refinement.  The mathematical content is
  `|U ∩ G| ≥ ρ|U| ⟹ ∑_i |Y_i ∩ G| ≥ (ρ/C) ∑_i |Y_i|`.  Again the statement is division-free
  (`ρ' * C ≤ ρ`).

The route for the second one is the layer-cake identity
`MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter` together with the *attained* minimum
`m = min_{y ∈ U} µ(y)` of the (integer-valued) pointwise multiplicity: constant multiplicity gives
both `m ≤ µ(x)` and `µ(x) ≤ C·m` on `U`, so
`∑_i |Y_i ∩ G| = ∫_{U ∩ G} µ ≥ m·|U ∩ G| ≥ mρ|U|` and `∑_i |Y_i| = ∫_U µ ≤ C·m·|U|`.  The factor
`C/m` here is *configuration dependent* — it is not, and must not be read as, a uniform packing
bound.  The degenerate cases (`U` empty, and `m = 0`) are handled by the total-mass-zero branch.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ### The pointwise multiplicity as an integrand -/

/-- The pointwise multiplicity is the cardinality of the shade fibre.  Both sides are the same
`Finset.filter`, so this is definitional; it is recorded as a lemma because the two spellings live
in different namespaces and are used interchangeably downstream. -/
theorem pointwiseMultiplicity_eq_shadeFibre_card (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (x : EuclideanSpace ℝ (Fin 3)) :
    ShadedBody.pointwiseMultiplicity s V x = (Kakeya.shadeFibre s V x).card := rfl

/-- The `ℝ≥0∞`-valued pointwise multiplicity of a shaded family is measurable: it is a finite sum
of indicators of the (measurable) shadings. -/
theorem measurable_pointwiseMultiplicity (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    Measurable (fun x => (ShadedBody.pointwiseMultiplicity s V x : ENNReal)) :=
  MeasureTheory.measurable_card_filter_mem s fun i _ => (V i).measurableSet_shade

/-- **Layer cake for a shaded family.**  The total shading mass inside an arbitrary set `B` is the
integral of the pointwise multiplicity over `B`.  Specialisation of
`MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter` to the shadings of a `ShadedBody`
family. -/
theorem sum_volume_shade_inter_eq_lintegral_multiplicity (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (B : Set (EuclideanSpace ℝ (Fin 3))) :
    ∑ i ∈ s, volume ((V i).shade ∩ B)
      = ∫⁻ x in B, (ShadedBody.pointwiseMultiplicity s V x : ENNReal) :=
  MeasureTheory.sum_measure_inter_eq_setLIntegral_card_filter (μ := volume) s
    (fun i _ => (V i).measurableSet_shade) B

/-! ### Fibre inclusion -/

/-- Pointwise fibre inclusion forces inclusion of the shading unions: a point of the smaller
family's union has a nonempty fibre there, hence a nonempty fibre for the larger family. -/
theorem biUnion_shade_subset_of_shadeFibre_subset {s s' : Finset ι}
    {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hfib : ∀ x, Kakeya.shadeFibre s' Y' x ⊆ Kakeya.shadeFibre s Y x) :
    (⋃ i ∈ s', (Y' i).shade) ⊆ ⋃ i ∈ s, (Y i).shade := by
  intro x hx
  obtain ⟨i, hi, hxsh⟩ := Set.mem_iUnion₂.mp hx
  have h := (Kakeya.mem_shadeFibre s Y x i).mp
    (hfib x ((Kakeya.mem_shadeFibre s' Y' x i).mpr ⟨hi, hxsh⟩))
  exact Set.mem_iUnion₂.mpr ⟨i, h.1, h.2⟩

/-! ### Phase 5a: transport of constant multiplicity through a fibre-retaining refinement -/

/-- **Transport of constant multiplicity, division-free form.**  Let `(s', Y')` shrink `(s, Y)`
pointwise (`hfib`) and retain a `q`-fraction of every point fibre on its own shading union
(`hret`).  If `(s, Y)` has constant multiplicity at scale `C` and `C ≤ q · C'`, then `(s', Y')` has
constant multiplicity at scale `C'`.

The proof is four inequalities: for `x, y` in the new union, `µ'(x) ≤ µ(x) ≤ C·µ(y)` and
`q·µ(y) ≤ µ'(y)`, so `q·µ'(x) ≤ C·µ'(y) ≤ q·C'·µ'(y)`, and `0 < q` cancels. -/
theorem hasCConstantMultiplicity_of_fibreRetention {s s' : Finset ι}
    {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {C C' q : ℝ≥0} (hq : 0 < q)
    (hC : ShadedBody.HasCConstantMultiplicity s Y C)
    (hfib : ∀ x, Kakeya.shadeFibre s' Y' x ⊆ Kakeya.shadeFibre s Y x)
    (hret : ∀ x ∈ ⋃ i ∈ s', (Y' i).shade,
      q * (ShadedBody.pointwiseMultiplicity s Y x : ℝ≥0)
        ≤ (ShadedBody.pointwiseMultiplicity s' Y' x : ℝ≥0))
    (hscale : C ≤ q * C') :
    ShadedBody.HasCConstantMultiplicity s' Y' C' := by
  intro x hxU' y hyU'
  have hUsub := biUnion_shade_subset_of_shadeFibre_subset hfib
  -- fibre inclusion gives µ'(x) ≤ µ(x), then constant multiplicity at scale `C`
  have hmu' : (ShadedBody.pointwiseMultiplicity s' Y' x : ℝ≥0) ≤
      C * (ShadedBody.pointwiseMultiplicity s Y y : ℝ≥0) :=
    (Nat.cast_le.2 (Finset.card_le_card (hfib x))).trans (hC (hUsub hxU') (hUsub hyU'))
  refine (mul_le_mul_iff_of_pos_left hq).mp ?_
  calc q * (ShadedBody.pointwiseMultiplicity s' Y' x : ℝ≥0)
      ≤ q * (C * (ShadedBody.pointwiseMultiplicity s Y y : ℝ≥0)) := mul_le_mul_right hmu' q
    _ = C * (q * (ShadedBody.pointwiseMultiplicity s Y y : ℝ≥0)) := mul_left_comm _ _ _
    _ ≤ C * (ShadedBody.pointwiseMultiplicity s' Y' y : ℝ≥0) := mul_le_mul_right (hret y hyU') C
    _ ≤ (q * C') * (ShadedBody.pointwiseMultiplicity s' Y' y : ℝ≥0) := mul_le_mul_left hscale _
    _ = q * (C' * (ShadedBody.pointwiseMultiplicity s' Y' y : ℝ≥0)) := mul_assoc _ _ _

/-- **Transport of constant multiplicity, real-valued retention hypothesis.**  The same statement
as `Plank.hasCConstantMultiplicity_of_fibreRetention` with the retention inequality phrased in `ℝ`
about the shade-fibre cardinalities, which is the shape produced by the good-point refinement. -/
theorem hasCConstantMultiplicity_of_fibreRetention_real {s s' : Finset ι}
    {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {C C' q : ℝ≥0} (hq : 0 < q)
    (hC : ShadedBody.HasCConstantMultiplicity s Y C)
    (hfib : ∀ x, Kakeya.shadeFibre s' Y' x ⊆ Kakeya.shadeFibre s Y x)
    (hret : ∀ x ∈ ⋃ i ∈ s', (Y' i).shade,
      (q : ℝ) * ((Kakeya.shadeFibre s Y x).card : ℝ)
        ≤ ((Kakeya.shadeFibre s' Y' x).card : ℝ))
    (hscale : C ≤ q * C') :
    ShadedBody.HasCConstantMultiplicity s' Y' C' := by
  refine hasCConstantMultiplicity_of_fibreRetention hq hC hfib (fun x hx => ?_) hscale
  rw [← NNReal.coe_le_coe]
  push_cast
  exact hret x hx

/-! ### Phase 5b: restriction to a common set of large relative measure -/

/-- The attained minimum of the pointwise multiplicity on a nonempty shading union.  The
multiplicity is `ℕ`-valued, so the infimum over a nonempty set is attained. -/
theorem exists_min_pointwiseMultiplicity (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hne : (⋃ i ∈ s, (V i).shade).Nonempty) :
    ∃ y ∈ ⋃ i ∈ s, (V i).shade, ∀ x ∈ ⋃ i ∈ s, (V i).shade,
      ShadedBody.pointwiseMultiplicity s V y ≤ ShadedBody.pointwiseMultiplicity s V x := by
  obtain ⟨y, hyU, hy⟩ := Nat.sInf_mem (hne.image (ShadedBody.pointwiseMultiplicity s V))
  exact ⟨y, hyU, fun x hxU => hy.trans_le (Nat.sInf_le ⟨x, hxU, rfl⟩)⟩

/-- **Upper bound for the total mass from constant multiplicity, at a reference point.**  If
`(s, V)` has constant multiplicity at scale `C` then, for any `y` in the shading union,
`∑_i |V_i| ≤ C · µ(y) · |U|`.

This is a *relative* bound: the factor `C · µ(y)` depends on the configuration through `µ(y)`.  It
is emphatically **not** a uniform bound `∑_i |V_i| ≤ Λ|U|` with `Λ` independent of the
configuration; no such bound follows from constant multiplicity. -/
theorem sum_volume_shade_le_of_hasCConstantMultiplicity (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {C : ℝ≥0}
    (hC : ShadedBody.HasCConstantMultiplicity s V C)
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ ⋃ i ∈ s, (V i).shade) :
    ∑ i ∈ s, volume (V i).shade
      ≤ (C : ENNReal) * (ShadedBody.pointwiseMultiplicity s V y : ENNReal)
          * volume (⋃ i ∈ s, (V i).shade) := by
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (V i).shade with hU
  calc ∑ i ∈ s, volume (V i).shade
      = ∑ i ∈ s, volume ((V i).shade ∩ U) :=
        Finset.sum_congr rfl fun i hi => by
          have h : (V i).shade ⊆ U := fun x hx => Set.mem_biUnion hi hx
          rw [Set.inter_eq_self_of_subset_left h]
    _ = ∫⁻ x in U, (ShadedBody.pointwiseMultiplicity s V x : ENNReal) :=
        sum_volume_shade_inter_eq_lintegral_multiplicity s V U
    _ ≤ ∫⁻ _ in U, (C : ENNReal) * (ShadedBody.pointwiseMultiplicity s V y : ENNReal) :=
        setLIntegral_mono_ae aemeasurable_const
          (ae_of_all _ fun x hx => by simpa using ENNReal.coe_le_coe.mpr (hC hx hy))
    _ = _ := setLIntegral_const _ _

/-- **Lower bound for the restricted mass from a minimising point.**  If `µ(y)` is minimal on the
shading union then `µ(y) · |U ∩ G| ≤ ∑_i |V_i ∩ G|` for every set `G`: integrate the constant
`µ(y)` against the layer-cake identity on `U ∩ G`. -/
theorem mul_volume_inter_le_sum_volume_shade_inter (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {y : EuclideanSpace ℝ (Fin 3)}
    (hmin : ∀ x ∈ ⋃ i ∈ s, (V i).shade,
      ShadedBody.pointwiseMultiplicity s V y ≤ ShadedBody.pointwiseMultiplicity s V x)
    (G : Set (EuclideanSpace ℝ (Fin 3))) :
    (ShadedBody.pointwiseMultiplicity s V y : ENNReal) * volume ((⋃ i ∈ s, (V i).shade) ∩ G)
      ≤ ∑ i ∈ s, volume ((V i).shade ∩ G) := by
  set U := ⋃ i ∈ s, (V i).shade
  calc (ShadedBody.pointwiseMultiplicity s V y : ENNReal) * volume (U ∩ G)
      = ∫⁻ _ in U ∩ G, (ShadedBody.pointwiseMultiplicity s V y : ENNReal) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in U ∩ G, (ShadedBody.pointwiseMultiplicity s V x : ENNReal) :=
        setLIntegral_mono_ae (measurable_pointwiseMultiplicity s V).aemeasurable.restrict
          (ae_of_all _ fun x hx => Nat.cast_le.mpr (hmin x hx.1))
    _ = ∑ i ∈ s, volume ((V i).shade ∩ (U ∩ G)) :=
        (sum_volume_shade_inter_eq_lintegral_multiplicity s V _).symm
    _ = ∑ i ∈ s, volume ((V i).shade ∩ G) :=
        Finset.sum_congr rfl fun i hi => by
          rw [← Set.inter_assoc, Set.inter_eq_self_of_subset_left
            (show (V i).shade ⊆ U from fun _ hx => Set.mem_biUnion hi hx)]

/-- **Common-set restriction under constant multiplicity, division-free form.**  Let `(s, Y)` have
constant multiplicity at scale `C`, and let `G` be a measurable set capturing a `ρ`-fraction of the
shading union, `ρ|U| ≤ |U ∩ G|`.  Then restricting every shading to `G` is a `ρ'`-refinement for
any `ρ'` with `ρ' · C ≤ ρ`.

Both degenerate cases are handled by the mass branch: if `U` is empty every `|Y_i|` vanishes and
the mass inequality is `0 ≤ 0`; if `U` is nonempty the minimum `m = µ(y)` of the pointwise
multiplicity is attained, and the chain
`ρ'∑_i|Y_i| ≤ ρ'·C·m·|U| ≤ ρ·m·|U| ≤ m·|U ∩ G| ≤ ∑_i|Y_i ∩ G|` closes with no need for `m ≠ 0`. -/
theorem isCRefinement_restrictShade_of_dense (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {C ρ ρ' : ℝ≥0}
    (hC : ShadedBody.HasCConstantMultiplicity s Y C)
    {G : Set (EuclideanSpace ℝ (Fin 3))} (hG : MeasurableSet G)
    (hdense : (ρ : ENNReal) * volume (⋃ i ∈ s, (Y i).shade)
      ≤ volume ((⋃ i ∈ s, (Y i).shade) ∩ G))
    (hscale : ρ' * C ≤ ρ) :
    ShadedBody.IsCRefinement s (fun i => ShadedBody.restrictShade (Y i) G hG) s Y ρ' := by
  refine ⟨⟨Finset.Subset.refl s, fun i _ => ⟨rfl, Set.inter_subset_left⟩⟩, ?_⟩
  by_cases hne : (⋃ i ∈ s, (Y i).shade).Nonempty
  · obtain ⟨y, hyU, hmin⟩ := exists_min_pointwiseMultiplicity s Y hne
    have h : (ρ' : ENNReal) * C ≤ (ρ : ENNReal) := by exact_mod_cast hscale
    refine (mul_le_mul_right (sum_volume_shade_le_of_hasCConstantMultiplicity s Y hC hyU)
      (ρ' : ENNReal)).trans
      (le_trans ?_ (mul_volume_inter_le_sum_volume_shade_inter s Y hmin G))
    calc (ρ' : ENNReal) * ((C : ENNReal) * (ShadedBody.pointwiseMultiplicity s Y y : ENNReal)
          * volume (⋃ i ∈ s, (Y i).shade))
        = (ShadedBody.pointwiseMultiplicity s Y y : ENNReal)
            * ((ρ' : ENNReal) * C * volume (⋃ i ∈ s, (Y i).shade)) := by ring
      _ ≤ (ShadedBody.pointwiseMultiplicity s Y y : ENNReal)
            * ((ρ : ENNReal) * volume (⋃ i ∈ s, (Y i).shade)) :=
          mul_le_mul_right (mul_le_mul_left h _) _
      _ ≤ (ShadedBody.pointwiseMultiplicity s Y y : ENNReal)
            * volume ((⋃ i ∈ s, (Y i).shade) ∩ G) := mul_le_mul_right hdense _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [Finset.sum_eq_zero fun i hi => by
      rw [Set.subset_eq_empty (fun _ hx => Set.mem_biUnion hi hx) hne, measure_empty], mul_zero]
    exact zero_le

end Plank

end
