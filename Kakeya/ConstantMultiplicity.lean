/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Multiplicity
public import Kakeya.Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Log

/-!
# Dyadic pigeonhole: a constant-multiplicity refinement

This file proves that every shaded family `(𝒱, Y)` has a refinement `(𝒱, Y')` of constant
multiplicity (within a factor `2`), keeping at least a `1 / (⌊log₂ |𝒱|⌋ + 1)` fraction of the
shading mass. This is the dyadic-pigeonholing step (GWZ blueprint, pigeonholing item (ii)) used,
e.g., in the proof of GWZ Lemma 6.11.

The argument partitions space by the dyadic band of the pointwise multiplicity
`μ(x) = |{i : x ∈ Y(i)}|`: the level sets `X j = {x : ⌊log₂ μ(x)⌋ = j}` partition `U(𝒱, Y)`, and
one band carries a `≥ 1/(#bands)` fraction of the total mass. Restricting each shading to that
band gives the refinement, on which `μ` varies by less than a factor `2`.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **Constant-multiplicity refinement (dyadic pigeonhole), with the band exposed.**

Identical to `ShadedBody.exists_constantMultiplicity_refinement` except that it also returns the
*band* `X` on which the refinement is supported, together with the defining equation
`(V' i).shade = (V i).shade ∩ X` for **every** `i`.

Exposing `X` is what makes the band composable with later restrictions. The refinement relation
`IsRefinement s V' s V` alone is one-sided — it says each shade shrank, not that they all shrank
by intersecting with one common set — so from it one cannot conclude that the pointwise
multiplicity of `V'` agrees with that of `V` anywhere, and a two-sided per-block multiplicity
statement about `V` (such as GWZ Proposition 5.1 Item 4, here
`Kakeya.ThinCase.thinInnerConstMult`) cannot be transported across the band. With `X` in hand it
transports on all of `X` by `Kakeya.ThinCase.pointwiseMultiplicity_of_shade_inter`, and it goes on
transporting across every further common restriction.

The equation is stated for all `i`, not only for `i ∈ s`, because the construction restricts every
index; consumers that quantify over a subfamily of `s` therefore need no side condition. -/
lemma exists_constantMultiplicity_refinement_band (s : Finset ι) (V : ι → ShadedBody E) :
    ∃ (V' : ι → ShadedBody E) (X : Set E),
      MeasurableSet X ∧
      (∀ i, (V' i).shade = (V i).shade ∩ X) ∧
      IsRefinement s V' s V ∧
      HasCConstantMultiplicity s V' 2 ∧
      (∑ i ∈ s, volume (V i).shade)
        ≤ (Nat.log 2 s.card + 1) • ∑ i ∈ s, volume (V' i).shade := by
  -- The pointwise multiplicity, as a measurable `ℕ`-valued function.
  set mu : E → ℕ := fun x => pointwiseMultiplicity s V x
  have hmu_meas : Measurable mu := measurable_pointwiseMultiplicity s V
  -- Dyadic level sets `X j = {x : ⌊log₂ μ(x)⌋ = j}`, indexed by the bands `0, …, ⌊log₂ s.card⌋`.
  set Bands : Finset ℕ := Finset.range (Nat.log 2 s.card + 1)
  set X : ℕ → Set E := fun j => mu ⁻¹' {k | Nat.log 2 k = j}
  have hcard : Bands.card = Nat.log 2 s.card + 1 := Finset.card_range _
  have hX_meas : ∀ j, MeasurableSet (X j) := fun _ => hmu_meas trivial
  have hX_disj : (↑Bands : Set ℕ).PairwiseDisjoint X := fun j _ k _ hjk =>
    Set.disjoint_left.2 fun _ (hj : Nat.log 2 _ = j) (hk : Nat.log 2 _ = k) =>
      hjk (hj.symm.trans hk)
  -- The mass of each shading splits over the bands, which cover it.
  have hsplit : ∀ i ∈ s,
      volume (V i).shade = ∑ j ∈ Bands, volume ((V i).shade ∩ X j) := by
    intro i _
    have hunion : (⋃ j ∈ Bands, ((V i).shade ∩ X j)) = (V i).shade :=
      Set.Subset.antisymm (Set.iUnion₂_subset fun _ _ => Set.inter_subset_left) fun x hx =>
        Set.mem_iUnion₂.2 ⟨Nat.log 2 (mu x), Finset.mem_range.2 (Nat.lt_succ_of_le
          (Nat.log_mono_right (pointwiseMultiplicity_le_card s V x))), hx, rfl⟩
    exact (congrArg volume hunion).symm.trans (measure_biUnion_finset
      (fun _ hp _ hq hpq =>
        (hX_disj hp hq hpq).mono Set.inter_subset_right Set.inter_subset_right)
      fun j _ => (V i).measurableSet_shade.inter (hX_meas j))
  -- Pigeonhole: pick the band of maximal mass.
  obtain ⟨j, -, hjmax⟩ :=
    Finset.exists_max_image Bands (fun j => ∑ i ∈ s, volume ((V i).shade ∩ X j))
      (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero _))
  -- The refinement: restrict each shading to the chosen band.
  set V' : ι → ShadedBody E := fun i =>
    { V i with
      shade := (V i).shade ∩ X j
      measurableSet_shade := (V i).measurableSet_shade.inter (hX_meas j)
      shade_subset := Set.inter_subset_left.trans (V i).shade_subset }
  have hshade : ∀ i, (V' i).shade = (V i).shade ∩ X j := fun _ => rfl
  refine ⟨V', X j, hX_meas j, hshade,
    ⟨subset_rfl, fun i _ => ⟨rfl, Set.inter_subset_left⟩⟩, ?_, ?_⟩
  · -- Constant multiplicity up to a factor `2`.
    -- On the chosen band, the pointwise multiplicity of `V'` agrees with `μ`.
    have hpm : ∀ z ∈ X j, pointwiseMultiplicity s V' z = mu z := fun z hzX =>
      congrArg Finset.card (by
        ext k
        simp only [Finset.mem_filter, hshade k, Set.mem_inter_iff, hzX, and_true])
    intro x hx y hy
    obtain ⟨-, -, -, hxX⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨iy, hiy, hys, hyX⟩ := Set.mem_iUnion₂.1 hy
    have hxlog : Nat.log 2 (mu x) = j := hxX
    have hylog : Nat.log 2 (mu y) = j := hyX
    rw [hpm x hxX, hpm y hyX]
    exact_mod_cast le_two_mul_of_log_two_eq
      (Finset.card_ne_zero.2 ⟨iy, Finset.mem_filter.2 ⟨hiy, hys⟩⟩) (hxlog.trans hylog.symm)
  · -- Mass retained: at least a `1/(⌊log₂ s.card⌋ + 1)` fraction.
    calc ∑ i ∈ s, volume (V i).shade
        = ∑ j ∈ Bands, ∑ i ∈ s, volume ((V i).shade ∩ X j) :=
          (Finset.sum_congr rfl hsplit).trans Finset.sum_comm
      _ ≤ Bands.card • ∑ i ∈ s, volume ((V i).shade ∩ X j) :=
          Finset.sum_le_card_nsmul _ _ _ hjmax
      _ = (Nat.log 2 s.card + 1) • ∑ i ∈ s, volume (V' i).shade := by rw [hcard]

/-- **Constant-multiplicity refinement (dyadic pigeonhole).**
Every shaded family `(s, V)` admits a refinement `(s, V')` that has constant multiplicity up to a
factor `2` and retains at least a `1 / (⌊log₂ s.card⌋ + 1)` fraction of the shading mass. -/
lemma exists_constantMultiplicity_refinement (s : Finset ι) (V : ι → ShadedBody E) :
    ∃ V' : ι → ShadedBody E,
      IsRefinement s V' s V ∧
      HasCConstantMultiplicity s V' 2 ∧
      (∑ i ∈ s, volume (V i).shade)
        ≤ (Nat.log 2 s.card + 1) • ∑ i ∈ s, volume (V' i).shade := by
  obtain ⟨V', -, -, -, href, hmult, hmass⟩ := exists_constantMultiplicity_refinement_band s V
  exact ⟨V', href, hmult, hmass⟩

end ShadedBody

namespace Kakeya

variable {ι : Type*}

/-- **Pigeonhole over a finite measurable cell decomposition.** If a measurable map `f` sends every
point of the shaded region `U(s, Ya)` into a nonempty finite set `Cells` of values, then the level
sets `f ⁻¹' {k}`, `k ∈ Cells`, partition each shading, so some single cell carries at least a
`1 / |Cells|` fraction of the total shading mass. -/
lemma exists_cell_sum_volume_ge {κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (s : Finset ι)
    (Ya : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (Cells : Finset κ) (hCells : Cells.Nonempty)
    (f : EuclideanSpace ℝ (Fin 3) → κ) (hf : Measurable f)
    (hmem : ∀ x ∈ ⋃ i ∈ s, (Ya i).shade, f x ∈ Cells) :
    ∃ k ∈ Cells, (∑ i ∈ s, volume (Ya i).shade)
      ≤ Cells.card • ∑ i ∈ s, volume ((Ya i).shade ∩ f ⁻¹' {k}) := by
  have hmeas : ∀ k : κ, MeasurableSet (f ⁻¹' {k}) := fun k => hf (.singleton k)
  have hdisj : (↑Cells : Set κ).PairwiseDisjoint (fun k => f ⁻¹' {k}) := fun k _ l _ hkl =>
    Set.disjoint_left.2 fun _ (hk : f _ = k) (hl : f _ = l) => hkl (hk.symm.trans hl)
  have hsplit : ∀ i ∈ s,
      volume (Ya i).shade = ∑ k ∈ Cells, volume ((Ya i).shade ∩ f ⁻¹' {k}) := by
    intro i hi
    have hunion : (⋃ k ∈ Cells, ((Ya i).shade ∩ f ⁻¹' {k})) = (Ya i).shade :=
      Set.Subset.antisymm (Set.iUnion₂_subset fun _ _ => Set.inter_subset_left) fun x hx =>
        Set.mem_iUnion₂.2 ⟨f x, hmem x (Set.mem_iUnion₂.2 ⟨i, hi, hx⟩), hx, rfl⟩
    exact (congrArg volume hunion).symm.trans (measure_biUnion_finset
      (fun _ hp _ hq hpq => (hdisj hp hq hpq).mono Set.inter_subset_right Set.inter_subset_right)
      fun k _ => (Ya i).measurableSet_shade.inter (hmeas k))
  obtain ⟨k, hkC, hkmax⟩ :=
    Finset.exists_max_image Cells (fun k => ∑ i ∈ s, volume ((Ya i).shade ∩ f ⁻¹' {k})) hCells
  exact ⟨k, hkC, ((Finset.sum_congr rfl hsplit).trans Finset.sum_comm).trans_le
    (Finset.sum_le_card_nsmul _ _ _ hkmax)⟩

/-- **Restricting every shading to a fixed measurable set gives a refinement.** On the restricted
shaded region every point lies in the restricting set, lay already in the original shaded region,
and has an unchanged fibre. -/
lemma exists_restrict_refinement (s : Finset ι)
    (Ya : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) :
    ∃ V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ i, (V' i).shade = (Ya i).shade ∩ A) ∧
      ShadedBody.IsRefinement s V' s Ya ∧
      (∀ x ∈ ⋃ i ∈ s, (V' i).shade, x ∈ A ∧ x ∈ ⋃ i ∈ s, (Ya i).shade) ∧
      (∀ x ∈ ⋃ i ∈ s, (V' i).shade, shadeFibre s V' x = shadeFibre s Ya x) := by
  refine ⟨fun i =>
    { Ya i with
      shade := (Ya i).shade ∩ A
      measurableSet_shade := (Ya i).measurableSet_shade.inter hA
      shade_subset := Set.inter_subset_left.trans (Ya i).shade_subset },
    fun _ => rfl, ⟨subset_rfl, fun i _ => ⟨rfl, Set.inter_subset_left⟩⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨hix.2, Set.mem_iUnion₂.2 ⟨i, hi, hix.1⟩⟩
  · intro x hx
    obtain ⟨i, -, hix⟩ := Set.mem_iUnion₂.1 hx
    ext k
    rw [mem_shadeFibre, mem_shadeFibre]
    exact ⟨fun ⟨hks, hk⟩ => ⟨hks, hk.1⟩, fun ⟨hks, hk⟩ => ⟨hks, hk, hix.2⟩⟩

end Kakeya
