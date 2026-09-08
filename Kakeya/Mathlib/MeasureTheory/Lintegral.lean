/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lower integrals over finite unions

Finite subadditivity of the lower integral `∫⁻ x in A, f x ∂μ` in the set `A`. It requires neither
measurability of `f` or of the sets nor disjointness of the pieces: the only properties used are
monotonicity of `Measure.restrict` in the set and monotonicity of the lower integral in the measure.

## Main statements

* `MeasureTheory.lintegral_biUnion_finset_le` (blueprint `lem:lintegralFinsetBiUnionLe`).

The pigeonhole consequence, that some piece of a finite cover carries at least the average of the
integral over the covered set, is `MeasureTheory.exists_card_inv_mul_setLIntegral_le` in
`Kakeya.Pigeonhole`, where the general pigeonholing lemmas are collected.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {ι : Type*}

/-- **Subadditivity of the lower integral over a finite union** (blueprint
`lem:lintegralFinsetBiUnionLe`).

This is `MeasureTheory.measure_biUnion_finset_le` with the measure of a set replaced by the lower
integral over it. Neither measurability of `f` or of the `A c`, nor disjointness of the `A c`, is
required. -/
theorem lintegral_biUnion_finset_le (μ : Measure X) (T : Finset ι) (A : ι → Set X)
    (f : X → ℝ≥0∞) :
    ∫⁻ x in ⋃ c ∈ T, A c, f x ∂μ ≤ ∑ c ∈ T, ∫⁻ x in A c, f x ∂μ := by
  -- T is finite, hence countable as a set
  haveI : Countable (T : Set ι) := T.countable_toSet.to_subtype
  -- Rewrite the finite union as a union over the subtype (T : Set ι)
  calc
    ∫⁻ x in ⋃ c ∈ T, A c, f x ∂μ
        = ∫⁻ x in ⋃ (c : (T : Set ι)), A c, f x ∂μ := by
      -- Set.biUnion_eq_iUnion rewrites the union over a set into a union over the subtype
      simpa using congrArg (fun s : Set X => ∫⁻ x in s, f x ∂μ)
        (Set.biUnion_eq_iUnion (T : Set ι) (fun c _ => A c))
    _ ≤ ∑' (c : (T : Set ι)), ∫⁻ x in A c, f x ∂μ :=
      lintegral_iUnion_le (fun (c : (T : Set ι)) => A c) f
    _ = ∑ c ∈ T, ∫⁻ x in A c, f x ∂μ := by
      -- Finset.tsum_subtype' converts the tsum over the subtype to a finite sum
      simpa using Finset.tsum_subtype' T (fun c => ∫⁻ x in A c, f x ∂μ)

/-! ### Covers and bounded overlap

Two facts about a finite family of subsets of a measure space: the trivial direction of a cover,
and the whole content of a bounded-overlap hypothesis. Neither mentions a metric; both are used by
the ball refinement of Step 5 of the factoring construction. -/

/-- **A covered set is controlled by its pieces** (blueprint
`lem:measureLeSumMeasureInterOfSubsetBiUnion`). No measurability hypothesis is needed. -/
theorem measure_le_sum_measure_inter_of_subset_biUnion (μ : Measure X) (T : Finset ι)
    (B : ι → Set X) {A : Set X} (hA : A ⊆ ⋃ c ∈ T, B c) :
    μ A ≤ ∑ c ∈ T, μ (A ∩ B c) := by
  calc
    μ A = μ (⋃ c ∈ T, A ∩ B c) := by
      congr 1
      calc
        A = A ∩ (⋃ c ∈ T, B c) := by
          exact (Set.inter_eq_self_of_subset_left hA).symm
        _ = ⋃ c ∈ T, A ∩ B c := by
          simpa using (Set.inter_iUnion₂ (s := A) (t := fun c (_ : c ∈ T) => B c))
    _ ≤ ∑ c ∈ T, μ (A ∩ B c) :=
      measure_biUnion_finset_le T (fun c => A ∩ B c)

open Classical in
/-- **A sum of measures as an integral of a count** (blueprint
`lem:sumMeasureInterEqLintegralCard`): only measurability of the pieces `A ∩ B c` is used. -/
theorem sum_measure_inter_eq_lintegral_card_filter (μ : Measure X) (T : Finset ι)
    (B : ι → Set X) (A : Set X) (hAB : ∀ c ∈ T, MeasurableSet (A ∩ B c)) :
    ∑ c ∈ T, μ (A ∩ B c)
      = ∫⁻ x, (({c ∈ T | x ∈ A ∩ B c}.card : ℕ) : ℝ≥0∞) ∂μ := by
  have hmeas : ∀ c ∈ T, Measurable ((A ∩ B c).indicator (1 : X → ENNReal)) :=
    fun c hc => measurable_const.indicator (hAB c hc)
  calc ∑ c ∈ T, μ (A ∩ B c)
      = ∑ c ∈ T, ∫⁻ x, (A ∩ B c).indicator (1 : X → ENNReal) x ∂μ := by
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [lintegral_indicator_one (hAB c hc)]
    _ = ∫⁻ x, ∑ c ∈ T, (A ∩ B c).indicator (1 : X → ENNReal) x ∂μ := by
        rw [lintegral_finsetSum T hmeas]
    _ = ∫⁻ x, (({c ∈ T | x ∈ A ∩ B c}.card : ℕ) : ℝ≥0∞) ∂μ := by
        refine lintegral_congr fun x => ?_
        simp [Set.indicator_apply, Finset.sum_boole]

open Classical in
/-- A pointwise cardinality bound controls the total measure of a finite family of measurable
sets contained in a common measurable set. -/
theorem sum_measure_le_mul_measure_of_card_le (μ : Measure X) (s : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) {F : Set X} (hF : MeasurableSet F)
    (hsub : ∀ i ∈ s, A i ⊆ F) {M : ENNReal}
    (hM : ∀ x ∈ F, ({i ∈ s | x ∈ A i}.card : ENNReal) ≤ M) :
    ∑ i ∈ s, μ (A i) ≤ M * μ F := by
  have key : ∑ i ∈ s, μ (A i ∩ F) = ∫⁻ x in F, ({i ∈ s | x ∈ A i}.card : ENNReal) ∂μ := by
    have hmeas : ∀ i ∈ s, Measurable ((A i).indicator (fun _ => (1 : ENNReal))) :=
      fun i hi => measurable_const.indicator (hA i hi)
    calc
      ∑ i ∈ s, μ (A i ∩ F)
        = ∑ i ∈ s, ∫⁻ x in F, (A i).indicator (fun _ => (1 : ENNReal)) x ∂μ := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [setLIntegral_indicator (hA i hi) (fun _ => (1 : ENNReal)),
            setLIntegral_const, one_mul]
      _ = ∫⁻ x in F, ∑ i ∈ s, (A i).indicator (fun _ => (1 : ENNReal)) x ∂μ := by
          rw [lintegral_finsetSum (μ := μ.restrict F) s hmeas]
      _ = ∫⁻ x in F, ({i ∈ s | x ∈ A i}.card : ENNReal) ∂μ := by
          refine setLIntegral_congr_fun hF ?_
          intro x _
          simp only [Set.indicator_apply, Finset.sum_boole]
  calc
    ∑ i ∈ s, μ (A i)
      = ∑ i ∈ s, μ (A i ∩ F) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Set.inter_eq_self_of_subset_left (hsub i hi)]
    _ = ∫⁻ x in F, ({i ∈ s | x ∈ A i}.card : ENNReal) ∂μ := key
    _ ≤ ∫⁻ x in F, M ∂μ := by
        refine setLIntegral_mono_ae (g := fun _ => M) aemeasurable_const ?_
        exact Filter.Eventually.of_forall (fun x hx => hM x hx)
    _ = M * μ F := by rw [setLIntegral_const]

open Classical in
omit [MeasurableSpace X] in
/-- **The count is dominated by the overlap bound** (blueprint
`lem:cardFilterMemInterLeMulIndicator`).

The hypothesis `T' ⊆ T` cannot be dropped: an index set disjoint from `T` carries no overlap bound
at all. -/
theorem card_filter_mem_inter_le_mul_indicator {T T' : Finset ι} (hT' : T' ⊆ T)
    (B : ι → Set X) (A : Set X) {K : ℕ} (hK : ∀ x, ({c ∈ T | x ∈ B c}.card) ≤ K) (x : X) :
    (({c ∈ T' | x ∈ A ∩ B c}.card : ℕ) : ℝ≥0∞)
      ≤ (K : ℝ≥0∞) * (A ∩ ⋃ c ∈ T', B c).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ A ∩ ⋃ c ∈ T', B c
  · have hsub : {c ∈ T' | x ∈ A ∩ B c} ⊆ {c ∈ T | x ∈ B c} := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      exact ⟨hT' hc.1, hc.2.2⟩
    have hbound : ({c ∈ T' | x ∈ A ∩ B c}.card : ℕ) ≤ K :=
      le_trans (Finset.card_le_card hsub) (hK x)
    rw [Set.indicator_of_mem hx]
    simpa using (mod_cast hbound)
  · rw [Set.indicator_of_notMem hx]
    rw [Finset.card_eq_zero.mpr
      (Finset.eq_empty_iff_forall_notMem.mpr (fun c hc => by
        have hc' : c ∈ T' ∧ x ∈ A ∩ B c := Finset.mem_filter.mp hc
        exact hx ⟨hc'.2.1, Set.mem_biUnion hc'.1 hc'.2.2⟩))]
    simp

open Classical in
/-- **Bounded overlap turns a sum of pieces into a single mass** (blueprint
`lem:sumMeasureInterLeMulMeasureInterBiUnion`). -/
theorem sum_measure_inter_le_mul_measure_inter_biUnion (μ : Measure X) {T T' : Finset ι}
    (hT' : T' ⊆ T) (B : ι → Set X) (hB : ∀ c, MeasurableSet (B c)) {A : Set X}
    (hA : MeasurableSet A) {K : ℕ} (hK : ∀ x, ({c ∈ T | x ∈ B c}.card) ≤ K) :
    ∑ c ∈ T', μ (A ∩ B c) ≤ (K : ℝ≥0∞) * μ (A ∩ ⋃ c ∈ T', B c) := by
  calc
    ∑ c ∈ T', μ (A ∩ B c)
        = ∫⁻ x, (({c ∈ T' | x ∈ A ∩ B c}.card : ℕ) : ℝ≥0∞) ∂μ := by
          exact sum_measure_inter_eq_lintegral_card_filter μ T' B A (fun c hc => hA.inter (hB c))
    _ ≤ ∫⁻ x, (K : ℝ≥0∞) * (A ∩ ⋃ c ∈ T', B c).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ := by
          exact lintegral_mono (fun x => card_filter_mem_inter_le_mul_indicator hT' B A hK x)
    _ = (K : ℝ≥0∞) * μ (A ∩ ⋃ c ∈ T', B c) := by
          have hmeas : MeasurableSet (A ∩ ⋃ c ∈ T', B c) :=
            hA.inter (Finset.measurableSet_biUnion T' (fun c _ => hB c))
          rw [← lintegral_indicator_const hmeas (K : ℝ≥0∞)]
          exact lintegral_congr (fun x => by
            by_cases hx : x ∈ (A ∩ ⋃ c ∈ T', B c) <;> simp [Set.indicator, hx])


open Classical in
/-- **Multiplicity-integral identity**: the sum of per-set volumes equals the
integral of the pointwise multiplicity `#{i ∈ t : x ∈ A i}`.  Used to turn the
per-fibre cardinality bound `|g F| ≥ |F|/D^(M-1)` into a shade-SUM bound. -/
lemma sum_volume_eq_lintegral_card {E : Type*} [MeasureSpace E] {ι : Type*}
    (t : Finset ι) (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∑ i ∈ t, volume (A i)
      = ∫⁻ x, ((t.filter (fun i => x ∈ A i)).card : ENNReal) := by
  classical
  have hpt : ∀ x : E, ((t.filter (fun i => x ∈ A i)).card : ENNReal)
      = ∑ i ∈ t, (A i).indicator (1 : E → ENNReal) x := by
    intro x
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Set.indicator_apply]
    by_cases h : x ∈ A i <;> simp [h]
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_finsetSum t (fun i _ => measurable_one.indicator (hA i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.lintegral_indicator_one (hA i)]

end MeasureTheory
