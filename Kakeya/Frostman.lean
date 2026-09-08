/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Pigeonhole
public import Kakeya.Thickness.Basic
public import Mathlib.Order.Partition.Finpartition
public import Kakeya.Mathlib.Finpartition

/-!
  In this file we define and collect basic properties of the notion of
  C convex Frostman
-/

@[expose] public section

open MeasureTheory Real Metric Kakeya
namespace ConvexSpaceBody

variable
  {E : Type*} [TopologicalSpace E] [Convexity.ConvexSpace ℝ E]
  [MeasureSpace E] {ι : Type*}

/-- The notion of C-convex-Frostman defined in [GWZ, Definition 3.2] -/
def IsFrostmanIn (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) (C : ENNReal) :=
  ∀ K', K' ≤ K → densityIn s W K' ≤ C * densityIn s W K

theorem IsFrostmanIn.of_volume_eq_zero {K : ConvexSpaceBody E} (hK : volume K.carrier = 0) :
    IsFrostmanIn s W K C := fun _ hK' ↦
  densityIn_eq_zero_of_volume_eq_zero (measure_mono_null hK' hK) ▸ zero_le

/-- The Frostman property is monotone in the constant: if a family is `C`-Frostman in `K`
and `C ≤ C'`, then it is `C'`-Frostman in `K`. -/
theorem IsFrostmanIn.mono {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    {C C' : ENNReal} (h : IsFrostmanIn s W K C) (hC : C ≤ C') :
    IsFrostmanIn s W K C' := fun K' hK' => (h K' hK').trans (by gcongr)
/-- The Frostman constant `C_F(𝕍,K)` of [GWZ, Definition 3.2] as a number: the least `C` for
which the family `𝕍 = (W i)_{i ∈ s}` is `C`-convex-Frostman in `K`. -/
noncomputable def frostmanConstant (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) : ENNReal :=
  sInf {C : ENNReal | IsFrostmanIn s W K C}

/-- Easy half of the bridge between `frostmanConstant` and `IsFrostmanIn`. -/
theorem frostmanConstant_le_of_isFrostmanIn {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (h : IsFrostmanIn s W K C) :
    frostmanConstant s W K ≤ C :=
  sInf_le h

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- `frostmanConstant` computes the Frostman predicate: its defining infimum is attained. -/
theorem frostmanConstant_le_iff {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} :
    frostmanConstant s W K ≤ C ↔ IsFrostmanIn s W K C := by
  refine ⟨fun h K' hK' ↦ ?_, frostmanConstant_le_of_isFrostmanIn⟩
  rcases eq_or_ne (densityIn s W K) 0 with h0 | h0
  · simp [densityIn_eq_zero_of_le_of_eq_zero hK' h0]
  refine le_trans ?_ (mul_le_mul_left h _)
  rw [frostmanConstant, sInf_eq_iInf', ENNReal.iInf_mul_of_ne h0 (densityIn_ne_top s W K)]
  exact le_iInf fun a ↦ a.property K' hK'

/-- The Frostman constant is itself an admissible Frostman constant. -/
theorem isFrostmanIn_frostmanConstant {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} : IsFrostmanIn s W K (frostmanConstant s W K) :=
  frostmanConstant_le_iff.mp le_rfl

namespace IsFrostmanIn
variable {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}

noncomputable instance : DecidablePred fun i ↦ W i ≤ K := Classical.decPred _

/-- The constant `C` in `IsFrostmanIn s W K C` must be at least 1 unless density in `K` is zero -/
theorem one_le_or_densityIn_eq_zero (h : IsFrostmanIn s W K C) : 1 ≤ C ∨ densityIn s W K = 0 := by
  refine or_iff_not_imp_right.2 fun h' ↦ ?_
  rw [← ENNReal.mul_le_mul_iff_left h' (densityIn_ne_top s W K)]
  simpa using h K (le_refl _)

/-- This a formal consequece of `one_le_or_densityIn_eq_zero` -/
theorem one_le (h : IsFrostmanIn s W K C) (hd : 0 < densityIn s W K) : 1 ≤ C :=
  h.one_le_or_densityIn_eq_zero.resolve_right (ne_of_gt hd)

/-- Being Frostman passes to heavy subfamily, at a larger constant. -/
theorem of_subset (h : IsFrostmanIn s W K C) {t : Finset ι} {C' : ENNReal} (ht : t ⊆ s)
    (hvol : ∑ i ∈ s with W i ≤ K, volume (W i).carrier ≤
      C' * ∑ i ∈ t with W i ≤ K, volume (W i).carrier) :
    IsFrostmanIn t W K (C * C') := fun K' hK' ↦ by
  refine (densityIn_mono _ _ ht).trans <| (h K' hK').trans ?_
  grw [mul_assoc, densityIn_le_of_sum_le hvol]

/-- This is a special case of `IsFrostmanIn.of_subset`. -/
theorem of_le_of_subset (h : IsFrostmanIn s W K C) {t : Finset ι} {C' : ENNReal}
    (hW : ∀ i ∈ s, W i ≤ K) (ht : t ⊆ s)
    (hvol : ∑ i ∈ s, volume (W i).carrier ≤ C' * ∑ i ∈ t, volume (W i).carrier) :
    IsFrostmanIn t W K (C * C') := h.of_subset ht <| by
  rwa [Finset.filter_eq_self.2 hW, Finset.filter_eq_self.2 (fun i hi => hW i (ht hi))]

end IsFrostmanIn

/-- **Frostman control passes to a parent family when the fibre masses are comparable.**

This is GWZ Remark 3.3(A) in parent-map form.  It is placed in the Frostman layer because it is
independent of the Section-6 plank presentation and is also used by the generic flat-prism
aggregation. -/
theorem isFrostmanIn_parents_of_uniform_fibres
    {κ : Type*} [DecidableEq κ]
    {q : Finset ι} {out : Finset κ} {V : ι → ConvexSpaceBody E}
    {W : κ → ConvexSpaceBody E} {par : ι → κ} {fib : κ → Finset ι}
    {K : ConvexSpaceBody E} {C Cmass : ENNReal}
    (hFr : IsFrostmanIn q V K C)
    (hVpos : ∀ i ∈ q, 0 < volume (V i).carrier)
    (hpar : ∀ i ∈ q, par i ∈ out)
    (hVW : ∀ i ∈ q, V i ≤ W (par i))
    (hWK : ∀ j ∈ out, W j ≤ K)
    (hfib : ∀ j, fib j = ({i ∈ q | par i = j} : Finset ι))
    (hne : ∀ j ∈ out, (fib j).Nonempty)
    (hunif : ∀ j ∈ out, ∀ j' ∈ out,
      Kakeya.densityIn (fib j) V (W j) ≤
        Cmass * Kakeya.densityIn (fib j') V (W j')) :
    IsFrostmanIn out W K (Cmass * C) := by
  classical
  by_cases hK : volume K.carrier = 0
  · exact IsFrostmanIn.of_volume_eq_zero hK
  by_cases hq : q = ∅
  · have hout : out = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨i, hi⟩ := hne j hj
      rw [hfib, hq] at hi
      exact Finset.notMem_empty i hi
    subst out
    intro K' _
    simp [Kakeya.densityIn]
  have hout : out.Nonempty := by
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hq
    exact ⟨par i, hpar i hi⟩
  let f : κ → ENNReal := fun j ↦ Kakeya.densityIn (fib j) V (W j)
  set fmin : ENNReal := out.inf f with hfmin
  obtain ⟨j₀, hj₀, hfj₀⟩ := Finset.exists_mem_eq_inf out hout f
  have hfmin_le (j : κ) (hj : j ∈ out) : fmin ≤ f j := by
    rw [hfmin]
    exact Finset.inf_le hj
  have hf_le (j : κ) (hj : j ∈ out) : f j ≤ Cmass * fmin := by
    rw [hfmin, hfj₀]
    exact hunif j hj j₀ hj₀
  have hfmin_pos : 0 < fmin := by
    obtain ⟨i, hi⟩ := hne j₀ hj₀
    rw [hfmin, hfj₀]
    have hiRaw : i ∈ ({i ∈ q | par i = j₀} : Finset ι) := by
      rw [← hfib]
      exact hi
    have hi' : i ∈ q ∧ par i = j₀ := Finset.mem_filter.mp hiRaw
    exact (Kakeya.densityIn_pos_iff _ _ _).2
      ⟨i, hi, hVpos i hi'.1, by simpa [hi'.2] using hVW i hi'.1⟩
  have hall : ∀ i ∈ q, V i ≤ K :=
    fun i hi ↦ (hVW i hi).trans (hWK _ (hpar i hi))
  have hdensity : Kakeya.densityIn q V K ≤
      Cmass * fmin * Kakeya.densityIn out W K := by
    rw [← ENNReal.mul_le_mul_iff_left hK K.isCompact.measure_ne_top,
      ← Kakeya.sum_volume_eq_densityIn_mul_volume,
      Finset.filter_true_of_mem hall, mul_assoc,
      ← Kakeya.sum_volume_eq_densityIn_mul_volume' hWK, Finset.mul_sum,
      ← Finset.sum_fiberwise_of_maps_to hpar]
    refine Finset.sum_le_sum fun j hj ↦ ?_
    rw [← hfib, Kakeya.sum_volume_eq_densityIn_mul_volume'
      (fun i hi ↦ by
        have hiRaw : i ∈ ({i ∈ q | par i = j} : Finset ι) := by
          rw [← hfib]
          exact hi
        have hi' := Finset.mem_filter.mp hiRaw
        simpa [hi'.2] using hVW i hi'.1)]
    exact mul_le_mul_of_nonneg_right (hf_le j hj) bot_le
  have hsum_le (K' : ConvexSpaceBody E) :
      ∑ j ∈ out with W j ≤ K', ∑ i ∈ q with par i = j, volume (V i).carrier ≤
        ∑ i ∈ q with V i ≤ K', volume (V i).carrier := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    exact Finset.sum_le_sum_of_subset (by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, (hVW i hi.1).trans (Finset.mem_filter.mp hi.2).2⟩)
  intro K' hK'
  by_cases hK'0 : volume K'.carrier = 0
  · simpa [Kakeya.densityIn_eq_zero_of_volume_eq_zero hK'0]
  rw [← ENNReal.mul_le_mul_iff_right hfmin_pos.ne' (by
    rw [hfmin, hfj₀]
    exact Kakeya.densityIn_ne_top _ _ _),
    show fmin * (Cmass * C * Kakeya.densityIn out W K) =
      C * (Cmass * fmin * Kakeya.densityIn out W K) by ring]
  grw [← hdensity, ← hFr K' hK',
    ← ENNReal.mul_le_mul_iff_left hK'0 K'.isCompact.measure_ne_top,
    mul_assoc, ← Kakeya.sum_volume_eq_densityIn_mul_volume q V K',
    ← Kakeya.sum_volume_eq_densityIn_mul_volume out W K', Finset.mul_sum,
    ← hsum_le K']
  refine Finset.sum_le_sum fun j hj ↦ ?_
  replace hj := Finset.mem_of_mem_filter _ hj
  rw [← hfib j]
  grw [Kakeya.sum_volume_eq_densityIn_mul_volume'
    (fun i hi ↦ by
      have hiRaw : i ∈ ({i ∈ q | par i = j} : Finset ι) := by
        rw [← hfib]
        exact hi
      have hi' := Finset.mem_filter.mp hiRaw
      simpa [hi'.2] using hVW i hi'.1), hfmin_le j hj]

namespace IsFrostmanIn

/- (H.W.) Shall we rename this to of_empty_parts? -/
theorem of_parts_eq_empty [DecidableEq ι] {P : Finpartition s} {W : Finset ι → ConvexSpaceBody E}
    (hs : s = ∅) (C : ENNReal) : IsFrostmanIn P.parts W K C := fun K' _ ↦ by
  simp [show P.parts = ∅ by rw [Finpartition.parts_eq_empty_iff, hs]; rfl]

section TranslationInvariance

variable
  {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `IsFrostmanIn` is invariant under translating the test body and all bodies
    by the same constant vector. -/
lemma translate {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (h : IsFrostmanIn s W K C) (v : E) :
    IsFrostmanIn s (fun i => ConvexSpaceBody.translate (W i) v)
    (ConvexSpaceBody.translate K v) C := fun K' hK' ↦ by
  convert h (K'.translate (-v)) (ConvexSpaceBody.le_translate_iff v|>.1 hK') using 1
  · nth_rw 1 [← K'.translate_neg_cancel]
    exact densityIn_translate s W (ConvexSpaceBody.translate K' (-v)) v
  · rw [densityIn_translate s W K v]

/-- `IsFrostmanIn` after translating everything by the same vector is equivalent
    to the original. -/
lemma translate_iff {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (v : E) :
    IsFrostmanIn s (fun i => ConvexSpaceBody.translate (W i) v) (ConvexSpaceBody.translate K v) C ↔
      IsFrostmanIn s W K C := ⟨fun h => by
  simpa [ConvexSpaceBody.neg_translate_cancel] using h.translate (-v), fun h => h.translate v⟩

end TranslationInvariance

/-- **Bridge α (Frostman → maxDensity).** If `s` is `C`-convex Frostman in `K`
and every body in the family is contained in `K`, then `maxDensity s W` is at
most `C · densityIn s W K`. Used to convert `IsFrostmanIn` outputs of
`frostman_of_per_K_hitcount_chernoff` into `maxDensity` statements expected by
the random translation pipeline. -/
theorem maxDensity_le_of_carrier_subset
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}
    (hFr : IsFrostmanIn s W K C) (hWK : ∀ i ∈ s, W i ≤ K) :
    maxDensity s W ≤ C * densityIn s W K := by
  by_cases he : density_maximizer s W = ∅
  · simp [maxDensity_eq_zero_of_maximizer_eq_empty he]
  · rw [← densityIn_self_maximizer_eq]
    refine hFr _ ?_
    have hne : (density_maximizer s W).Nonempty := Finset.nonempty_iff_ne_empty.mpr he
    refine (hne.convexHull_biUnion_le_iff W K).mpr ?_
    intro i hi
    exact hWK i (density_maximizer_subset _ _ hi)

/-- **Bridge β (maxDensity → Frostman).** If `maxDensity s W ≤ C · densityIn s W K`,
then `s` is `C`-Frostman in `K`. This is the reverse of
`maxDensity_le_of_carrier_subset` and converts `random_translation_lemma`'s
`maxDensity` output into the `IsFrostmanIn` form needed downstream. -/
theorem of_maxDensity_le
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}
    (hMax : maxDensity s W ≤ C * densityIn s W K) :
    IsFrostmanIn s W K C :=
  fun K' _ => (le_maxDensity s W K').trans hMax

/-- Division-free entry point into the Frostman predicate.  This form is useful when the
reference body is only used to normalize the total mass: it avoids dividing by its volume and
makes all nonzero hypotheses explicit. -/
theorem of_maxDensity_mul_volume_le
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}
    (hWK : ∀ i ∈ s, W i ≤ K) (hK0 : volume K.carrier ≠ 0)
    (h : maxDensity s W * volume K.carrier ≤ C * ∑ i ∈ s, volume (W i).carrier) :
    IsFrostmanIn s W K C := by
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  apply of_maxDensity_le
  rw [densityIn_of_all_le hWK]
  have hrw : C * ((∑ i ∈ s, volume (W i).carrier) / volume K.carrier) =
      (C * ∑ i ∈ s, volume (W i).carrier) / volume K.carrier := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [hrw, ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)]
  exact h

/-- Division-free consequence of a Frostman hypothesis when every member lies in the reference
body. -/
theorem maxDensity_mul_volume_le
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}
    (hFr : IsFrostmanIn s W K C) (hWK : ∀ i ∈ s, W i ≤ K)
    (hK0 : volume K.carrier ≠ 0) :
    maxDensity s W * volume K.carrier ≤ C * ∑ i ∈ s, volume (W i).carrier := by
  calc
    maxDensity s W * volume K.carrier ≤ C * densityIn s W K * volume K.carrier := by
      gcongr
      exact hFr.maxDensity_le_of_carrier_subset hWK
    _ = C * ∑ i ∈ s, volume (W i).carrier := by
      rw [mul_assoc, densityIn_of_all_le hWK,
        ENNReal.div_mul_cancel hK0 K.isCompact.measure_ne_top]

/-- Change the ambient body in a Frostman estimate when every member of the family is
contained in both bodies. The Frostman constant changes by the ratio of their volumes. -/
theorem change_ambient
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K L : ConvexSpaceBody E} {C : ENNReal}
    (hFr : IsFrostmanIn s W K C)
    (hWK : ∀ i ∈ s, W i ≤ K) (hWL : ∀ i ∈ s, W i ≤ L)
    (hK_ne_zero : volume K.carrier ≠ 0) (hL_ne_zero : volume L.carrier ≠ 0) :
    IsFrostmanIn s W L (C * (volume L.carrier / volume K.carrier)) := by
  apply of_maxDensity_le
  have h_ratio : volume L.carrier / volume K.carrier *
      ((∑ i ∈ s, volume (W i).carrier) / volume L.carrier) =
      (∑ i ∈ s, volume (W i).carrier) / volume K.carrier := by
    rw [← ENNReal.mul_div_mul_comm (Or.inl hK_ne_zero) (Or.inl K.isCompact'.measure_ne_top),
      mul_comm (volume L.carrier) (∑ i ∈ s, volume (W i).carrier),
      ENNReal.mul_div_mul_right _ _ hL_ne_zero L.isCompact'.measure_ne_top]
  calc
    maxDensity s W ≤ C * densityIn s W K := hFr.maxDensity_le_of_carrier_subset hWK
    _ = C * ((∑ i ∈ s, volume (W i).carrier) / volume K.carrier) := by
      rw [densityIn_of_all_le hWK]
    _ = C * (volume L.carrier / volume K.carrier *
        ((∑ i ∈ s, volume (W i).carrier) / volume L.carrier)) := by rw [h_ratio]
    _ = (C * (volume L.carrier / volume K.carrier)) * densityIn s W L := by
      rw [densityIn_of_all_le hWL, mul_assoc]

/-- Pass a Frostman estimate to a heavy subfamily, translate it, and change the ambient body. -/
theorem translate_of_le_of_subset
    {s t : Finset ι} {W : ι → ConvexSpaceBody E} {K L : ConvexSpaceBody E}
    {C D : ENNReal} (hFr : IsFrostmanIn s W K C)
    (hWK : ∀ i ∈ s, W i ≤ K) (ht : t ⊆ s)
    (hvol : (∑ i ∈ s, volume (W i).carrier) ≤
      D * ∑ i ∈ t, volume (W i).carrier)
    (v : E) (hWL : ∀ i ∈ t, (W i).translate v ≤ L)
    (hK_ne_zero : volume K.carrier ≠ 0) (hL_ne_zero : volume L.carrier ≠ 0) :
    IsFrostmanIn t (fun i => (W i).translate v) L
      ((C * D) * (volume L.carrier / volume K.carrier)) := by
  have hFr' := (hFr.of_le_of_subset hWK ht hvol).translate v
  have hWK' : ∀ i ∈ t, (W i).translate v ≤ K.translate v := fun i hi =>
    translate_le_translate v (hWK i (ht hi))
  have hK'_ne_zero : volume (K.translate v).carrier ≠ 0 := by
    rw [volume_translate]
    exact hK_ne_zero
  simpa [volume_translate] using
    hFr'.change_ambient hWK' hWL hK'_ne_zero hL_ne_zero

section inherited_upwards
variable
  [DecidableEq ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma all_le_of_partition
    {s : Finset ι} (P : Finpartition s)
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    (hWK : ∀ t ∈ P.parts, W t ≤ K)
    (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t) :
    ∀ i ∈ s, V i ≤ K := fun i hi ↦ by
  rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hi
  obtain ⟨t, ht, hit⟩ := hi
  exact le_trans (hVW t ht i hit) (hWK t ht)

lemma sum_parts_sum_le {V : ι → ConvexSpaceBody E} (P : Finpartition s)
    {W : Finset ι → ConvexSpaceBody E} (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t)
    (K' : ConvexSpaceBody E) : ∑ t ∈ P.parts with W t ≤ K', ∑ i ∈ t, volume (V i).carrier ≤
    ∑ i ∈ s with V i ≤ K', volume (V i).carrier :=
  (Finset.sum_biUnion (s := {t ∈ P.parts | W t ≤ K'}) (f := fun i ↦ volume (V i).carrier)
    (P.disjoint.subset (Finset.coe_subset.2 (Finset.filter_subset _ _)))).symm.trans_le <|
  Finset.sum_le_sum_of_subset <| by
    -- this proof design is on purpose, do *NOT* change this into `simpa using ...`!
    simp only [Finset.subset_iff, Finset.mem_biUnion, Finset.mem_filter, id_eq,
      forall_exists_index, and_imp]
    exact fun i t ht ht' hi ↦ ⟨P.subset ht hi, (hVW t ht i hi).trans ht'⟩

/-- Special case of the inherited upward property. [GWZ, Remark 3.3(A)]
  If in addition the density `∑_{V ∈ V_t} |V| / |W t|` is approximately the same for each
  part `t`, then we may take `parts' = P.parts`, and `P.parts` is `O(C)`-Frostman in `K`. -/
theorem inherited_upwards_uniform
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {P : Finpartition s}
    {C C' : ENNReal} (h : IsFrostmanIn s V K C) (hV : ∀ i ∈ s, 0 < volume (V i).carrier)
    (hWK : ∀ t ∈ P.parts, W t ≤ K) (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t)
    (hunif : ∀ t ∈ P.parts, ∀ t' ∈ P.parts, densityIn t V (W t) ≤ C' * densityIn t' V (W t')) :
    IsFrostmanIn P.parts W K (C' * C) :=
  if hK : volume K.carrier = 0 then of_volume_eq_zero hK else if hs : s = ∅ then
    of_parts_eq_empty hs _ else fun K' hK' ↦ if hK'₀ : volume K'.carrier = 0 then
    densityIn_eq_zero_of_volume_eq_zero hK'₀ ▸ zero_le else by
  let f (t : Finset ι) := densityIn t V (W t)
  set f_min := P.parts.inf f with f_min_eq
  obtain ⟨t₀, ht₀, hft₀⟩ := Finset.exists_mem_eq_inf _ (P.parts_nonempty hs) f
  have hf_min (t) (ht : t ∈ P.parts) : f t ≤ C' * f_min := f_min_eq ▸ hft₀ ▸ hunif t ht t₀ ht₀
  have h₀ : 0 < f_min :=
    let hi := (P.nonempty_of_mem_parts ht₀).choose_spec
    f_min_eq ▸ hft₀ ▸ (densityIn_pos_iff t₀ V (W t₀)|>.2
      ⟨_, hi, hV _ (P.subset ht₀ hi), (hVW _ ht₀ _ hi)⟩)
  have h_density_V_K_le : densityIn s V K ≤ C' * f_min * densityIn P.parts W K := by
    rw [← ENNReal.mul_le_mul_iff_left hK K.3.measure_ne_top, ← sum_volume_eq_densityIn_mul_volume,
      Finset.filter_true_of_mem (all_le_of_partition P hWK hVW), P.sum_eq_sum_parts_sum,
      mul_assoc, ← sum_volume_eq_densityIn_mul_volume' hWK, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht ↦ sum_volume_eq_densityIn_mul_volume' (hVW t ht) ▸ ?_
    grw [← hf_min _ ht]
  rw [← ENNReal.mul_le_mul_iff_right h₀.ne.symm (f_min_eq ▸ hft₀ ▸ densityIn_ne_top _ _ _),
    show f_min * (C' * C * densityIn _ W K) = C * (C' * f_min * densityIn P.parts W K) by ring]
  grw [← h_density_V_K_le, ← h K' hK', ← ENNReal.mul_le_mul_iff_left hK'₀
    K'.isCompact'.measure_ne_top, mul_assoc, ← sum_volume_eq_densityIn_mul_volume s V K',
    ← sum_volume_eq_densityIn_mul_volume P.parts W K', Finset.mul_sum, ← sum_parts_sum_le P hVW K']
  refine Finset.sum_le_sum fun t ht ↦ ?_
  replace ht := Finset.mem_of_mem_filter _ ht
  grw [sum_volume_eq_densityIn_mul_volume' (hVW t ht), f_min_eq, Finset.inf_le ht]

/-- The closed ball of radius `R` about the origin has volume at most `(2R) ^ n`: it is contained
in the axis-aligned cube of half-width `R`. -/
private lemma volume_closedBall_le_two_mul_pow_finrank (R : NNReal) :
    volume (Metric.closedBall (0 : E) (R : ℝ)) ≤
      ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E := by
  rw [Measure.addHaar_closedBall' volume (0 : E) (R.coe_nonneg)]
  calc
    ENNReal.ofReal ((R : ℝ) ^ Module.finrank ℝ E) * volume (Metric.closedBall (0 : E) 1)
        ≤ ENNReal.ofReal ((R : ℝ) ^ Module.finrank ℝ E) * 2 ^ Module.finrank ℝ E := by
          gcongr
          exact volume_closedBall_le_two_pow_finrank (E := E)
    _ = ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E := by
      rw [ENNReal.ofReal_pow R.coe_nonneg, ← mul_pow]
      congr 1
      norm_num [mul_comm]

private noncomputable abbrev le_densityIn_of_le_scale.c (n : ℕ) (δ R : NNReal) : NNReal :=
  lt_volume_convexHull.c n * δ ^ n / (2 * R) ^ n

omit [DecidableEq ι] in
/-- A quantitative lower bound on `densityIn s V K` when each `V i` has thickness at least `δ`
  and `K` is contained in the closed ball of radius `R` about the origin. -/
private lemma le_densityIn_of_le_scale [Nontrivial E]
    {V : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {δ R : NNReal} (hR : 0 < R)
    (hV : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)
    (hVK : ∀ i ∈ s, V i ≤ K) (hK : K.carrier ⊆ Metric.closedBall 0 (R : ℝ))
    {i : ι} (hi : i ∈ s) :
    le_densityIn_of_le_scale.c (Module.finrank ℝ E) δ R ≤ densityIn s V K := by
  have hvol_K : volume K.carrier ≤ ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E :=
    (measure_mono hK).trans (volume_closedBall_le_two_mul_pow_finrank (R := R))
  have hvol_Vi : lt_volume_convexHull.c (Module.finrank ℝ E)
      * δ ^ (Module.finrank ℝ E) ≤ volume (V i).carrier := by
    calc
      _  ≤ lt_volume_convexHull.c (Module.finrank ℝ E)
          * ethickness.scale ℝ (V i).carrier ^ (Module.finrank ℝ E) := by
          gcongr; exact hV i hi
      _ ≤ volume (V i).carrier := (V i).convex.le_volume_of_pow_scale
  have hc_coe : ((le_densityIn_of_le_scale.c (Module.finrank ℝ E) δ R : NNReal) : ENNReal) =
      (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ Module.finrank ℝ E
        / ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E := by
    unfold le_densityIn_of_le_scale.c
    rw [ENNReal.coe_div (pow_ne_zero _ (by positivity)), ENNReal.coe_mul,
      ENNReal.coe_pow, ENNReal.coe_pow]
  rw [hc_coe]
  exact (ENNReal.div_le_div hvol_Vi hvol_K).trans (le_densityIn s V K hi (hVK i hi))

/-- The explicit constant appearing in the `inherited_upwards` Frostman estimate, as a
function of the dimension `n`, the cardinality `card`, and the scale `δ`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev inherited_upwards.C (n : ℕ) (card : ℕ) (δ : NNReal) : NNReal :=
  2 * Real.toNNReal (1 + Real.logb 2
    ((card : ℝ) * 2 ^ n / ((lt_volume_convexHull.c n : ℝ) * (δ : ℝ) ^ n)))

omit [DecidableEq ι] in
private lemma inherited_upwards.C_coe (n card : ℕ) (δ : NNReal) :
    ((inherited_upwards.C n card δ : NNReal) : ENNReal) =
      2 * ENNReal.ofReal (1 + Real.logb 2
        ((card : ℝ) * 2 ^ n / ((lt_volume_convexHull.c n : ℝ) * (δ : ℝ) ^ n))) := by
  unfold inherited_upwards.C
  push_cast
  rfl

/-- The explicit constant appearing in the `inherited_upwards'` Frostman estimate, as a function of
the dimension `n`, the cardinality `card`, the scale `δ`, and the radius `R` of the ambient ball
containing `K`.  Compared with `inherited_upwards.C` it picks up the extra additive loss
`2 * n * Real.logb 2 R`, because the pigeonhole floor `c n * δ ^ n / (2 * R) ^ n` shrinks by the
factor `R ^ n` when the ambient ball grows from radius `1` to radius `R`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev inherited_upwards.C' (n : ℕ) (card : ℕ) (δ R : NNReal) : NNReal :=
  2 * Real.toNNReal (1 + Real.logb 2
    ((card : ℝ) * (2 * R : ℝ) ^ n / ((lt_volume_convexHull.c n : ℝ) * (δ : ℝ) ^ n)))

omit [DecidableEq ι] in
/-- At radius `R = 1` the generalized constant is the original one. -/
lemma inherited_upwards.C_eq_C'_one (n card : ℕ) (δ : NNReal) :
    inherited_upwards.C n card δ = inherited_upwards.C' n card δ 1 := by
  unfold inherited_upwards.C inherited_upwards.C'
  congr 2
  norm_num

omit [DecidableEq ι] in
private lemma inherited_upwards.C_coe' (n card : ℕ) (δ R : NNReal) :
    ((inherited_upwards.C' n card δ R : NNReal) : ENNReal) =
      2 * ENNReal.ofReal (1 + Real.logb 2
        ((card : ℝ) * (2 * R : ℝ) ^ n / ((lt_volume_convexHull.c n : ℝ) * (δ : ℝ) ^ n))) := by
  unfold inherited_upwards.C'
  push_cast
  rfl

omit [DecidableEq ι] in
/-- Rewrite `inherited_upwards.C' n card δ R * C'` in the form `2 * (C' * L)`, where `L` is the
dyadic logarithm factor returned by the pigeonhole step. The hypotheses `ha` and `hL` are the
defining equalities for `a` and `L`. -/
private lemma inherited_upwards.C_mul_eq' {C' : ENNReal} {a : NNReal} {L : ENNReal}
    (n card : ℕ) (δ R : NNReal)
    (ha : a = lt_volume_convexHull.c n * δ ^ n / (2 * R) ^ n)
    (hL : L = ENNReal.ofReal (1 + Real.logb 2 (((card : NNReal) : ℝ) / (a : ℝ)))) :
    (inherited_upwards.C' n card δ R : NNReal) * C' = 2 * (C' * L) := by
  rw [inherited_upwards.C_coe', hL, ha]
  push_cast
  rw [div_div_eq_mul_div]
  ring

/-- The inherited upward property of C-convex Frostman sets :
  Suppose `V = ⊔_{W ∈ W} V_W` is `C`-Frostman inside `K`, where each `W ∈ W` is
  contained in `K` and `V ⊆ W` for each `V ∈ V_W`.
  Then there is a subset `W' ⊆ W` that is `⪅ C`-Frostman in `K`. [GWZ, Remark 3.3(A)]

  Here the ambient body `K` is only required to lie in the closed ball of radius `R` about the
  origin, and the loss `inherited_upwards.C'` degrades logarithmically in `R`. -/
theorem inherited_upwards' [Nontrivial E]
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    {P : Finpartition s}
    {C : ENNReal} {δ R : NNReal} (hδ : 0 < δ) (hR : 0 < R)
    (h : IsFrostmanIn s V K C)
    (hV : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)
    (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t)
    (hWK : ∀ t ∈ P.parts, W t ≤ K)
    (hK : K.carrier ⊆ Metric.closedBall 0 (R : ℝ)) :
    ∃ (t : Finset (Finset ι)), t ⊆ P.parts ∧
      IsFrostmanIn t W K (inherited_upwards.C' (Module.finrank ℝ E) s.card δ R * C) := by
  set n := Module.finrank ℝ E
  set a : NNReal := lt_volume_convexHull.c n * δ ^ n / (2 * R) ^ n with ha_def
  set f : Finset ι → ENNReal := fun t => densityIn t V (W t)
  set w : Finset ι → ENNReal := fun t => ∑ i ∈ t, volume (V i).carrier
  have ha_pos : 0 < a := by
    rw [ha_def]
    exact div_pos (mul_pos (lt_volume_convexHull.c_pos n) (pow_pos hδ n))
      (pow_pos (mul_pos two_pos hR) n)
  have hf_Icc : ∀ t ∈ P.parts,
      f t ∈ Set.Icc ((a : NNReal) : ENNReal) (((s.card : NNReal) : ENNReal)) := fun t ht => by
    obtain ⟨i₀, hi₀⟩ := P.nonempty_of_mem_parts ht
    constructor
    · exact le_densityIn_of_le_scale hR (fun i hi => hV i (P.subset ht hi)) (hVW t ht)
        ((SetLike.coe_subset_coe.mpr (hWK t ht)).trans hK) hi₀
    · push_cast
      exact (densityIn_le_card t V (W t)).trans (mod_cast Finset.card_le_card (P.subset ht))
  obtain ⟨parts', hparts'_sub, hsum, hunif⟩ :=
    ENNReal.dyadic_pigeonhole₁'' P.parts w f ha_pos hf_Icc
  refine ⟨parts', hparts'_sub, ?_⟩
  set L : ENNReal :=
    ENNReal.ofReal (1 + Real.logb 2 (((s.card : NNReal) : ℝ) / (a : ℝ))) with hL_def
  set s' := parts'.sup id
  have hs'_sub_s : s' ⊆ s :=
    P.sup_parts ▸ (Finset.sup_mono hparts'_sub : parts'.sup id ≤ P.parts.sup id)
  let P' : Finpartition s' := P.ofSubset hparts'_sub rfl
  rw [inherited_upwards.C_mul_eq' n s.card δ R ha_def hL_def]
  apply inherited_upwards_uniform (P := P')
  · apply h.of_le_of_subset (all_le_of_partition P hWK hVW) hs'_sub_s
    rw [P.sum_eq_sum_parts_sum (fun i => volume (V i).carrier),
      P'.sum_eq_sum_parts_sum (fun i => volume (V i).carrier)]
    exact hsum
  · intro i hi
    apply (V i).convex.volume_pos_of_scale_ne_zero
    exact ne_bot_of_le_ne_bot (by simpa using hδ.ne') (hV i (hs'_sub_s hi))
  · exact fun t ht => hWK t (hparts'_sub ht)
  · exact fun t ht i hi => hVW t (hparts'_sub ht) i hi
  · exact hunif

/-- The inherited upward property of C-convex Frostman sets :
  Suppose `V = ⊔_{W ∈ W} V_W` is `C`-Frostman inside `K`, where each `W ∈ W` is
  contained in `K` and `V ⊆ W` for each `V ∈ V_W`.
  Then there is a subset `W' ⊆ W` that is `⪅ C`-Frostman in `K`. [GWZ, Remark 3.3(A)]

  This is the `R = 1` case of `inherited_upwards'`. -/
theorem inherited_upwards [Nontrivial E]
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    {P : Finpartition s}
    {C : ENNReal} {δ : NNReal} (hδ : 0 < δ)
    (h : IsFrostmanIn s V K C)
    (hV : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)
    (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t)
    (hWK : ∀ t ∈ P.parts, W t ≤ K)
    (hK : K.carrier ⊆ Metric.closedBall 0 1) :
    ∃ (t : Finset (Finset ι)), t ⊆ P.parts ∧
      IsFrostmanIn t W K (inherited_upwards.C (Module.finrank ℝ E) s.card δ * C) := by
  rw [inherited_upwards.C_eq_C'_one (Module.finrank ℝ E) s.card δ]
  exact inherited_upwards' (hδ := hδ) (hR := zero_lt_one) (h := h) (hV := hV) (hVW := hVW)
    (hWK := hWK) (hK := by simpa using hK)

end inherited_upwards

end IsFrostmanIn

/-- When the anchor body contains every member of the family, the Frostman constant is the ratio
of the maximal density to the anchor density. -/
theorem frostmanConstant_eq_maxDensity_div {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (hd : 0 < densityIn s W K) (hWK : ∀ i ∈ s, W i ≤ K) :
    frostmanConstant s W K = maxDensity s W / densityIn s W K := by
  have hne : densityIn s W K ≠ ⊤ := densityIn_ne_top s W K
  refine le_antisymm (frostmanConstant_le_of_isFrostmanIn (IsFrostmanIn.of_maxDensity_le
    (ENNReal.div_mul_cancel hd.ne' hne).ge)) ((ENNReal.div_le_iff hd.ne' hne).mpr
      (isFrostmanIn_frostmanConstant.maxDensity_le_of_carrier_subset hWK))

/-!
### The Frostman constant as a value

Definition~`IsFrostmanIn` is a *predicate*.  Several statements in Section 8 of the
adapted blueprint need *lower* bounds on the Frostman constant, which the predicate
alone cannot express.  We therefore introduce the constant as an `ENNReal`-valued
quantity, defined as the infimum of the admissible constants.
-/

section FrostmanConst

variable
  {E : Type*} [TopologicalSpace E] [Convexity.ConvexSpace ℝ E]
  [MeasureSpace E] {ι : Type*}

/-- The Frostman constant `C_F(𝕍, K)` of the finite family of convex bodies
`𝕍 = (W i)_{i ∈ s}` relative to the convex body `K`: the infimum, taken in `[0, ∞]`,
of all constants `C` for which the family is `C`-convex Frostman in `K`.
Since the infimum is taken in `ENNReal` it is always defined. -/
noncomputable def frostmanConstIn (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) : ENNReal :=
  sInf {C : ENNReal | IsFrostmanIn s W K C}

/-- `frostmanConstIn` and `ConvexSpaceBody.frostmanConstant` are two names for one notion: both
are the infimum in `[0, ∞]` of the admissible Frostman constants, and the equality is `rfl`.

The development carries both spellings because different chains grew around them —
`StickyKakeya.IsFrostmanDividingBlock.frostman_lower` measures with `frostmanConstant` while
`Kakeya.ml1Boot.IsCaseTwoData` measures with `frostmanConstIn` — and this lemma is the single
place where the two seams are crossed.  No third spelling should be introduced. -/
theorem frostmanConstIn_eq_frostmanConstant (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) : frostmanConstIn s W K = frostmanConstant s W K := rfl

variable {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}

/-- If the family is `C`-Frostman in `K`, then its Frostman constant is at most `C`. -/
theorem frostmanConstIn_le (h : IsFrostmanIn s W K C) : frostmanConstIn s W K ≤ C :=
  sInf_le h

/-- **The empty family has Frostman constant `0` in every body** (blueprint
`lem:ml1bootEmptyFamilyFrostmanZero`).

Every density `Δ(∅, K')` vanishes, so the empty family is `C`-Frostman in `K` for every `C ≥ 0`
and the constant, being the least such `C`, is `0`.

The point of stating it is that *upper* bounds are free at an empty family: any
`frostmanConstIn ∅ W K ≤ B` holds with nothing to prove.  This is what makes the empty branch of
`Kakeya.ml1Boot.IsFibrewiseEmptyOrShare` harmless, and it is the half of blueprint
`lem:ml1bootAbsentParentFibre` that is a fact about Frostman constants alone, with no parent
family in it; the other half — that a node no retained leaf lies over carries an empty fibre — is
`Kakeya.ml1Boot.fibre_eq_empty_of_notMem`.

Nothing of the kind is true on the *lower* side: a lower bound at an empty family is false, not
free. -/
theorem frostmanConstIn_empty : frostmanConstIn (∅ : Finset ι) W K = 0 := by
  refine le_antisymm ?_ bot_le
  apply frostmanConstIn_le
  intro K' _
  simp [Kakeya.densityIn]

/-- Auxiliary lemma: density is invariant under reindexing by a bijection. -/
private lemma densityIn_reindex {ι' : Type*} {t : Finset ι'} {e : ι' → ι} (he : Set.BijOn e t s)
    (K' : ConvexSpaceBody E) : densityIn t (W ∘ e) K' = densityIn s W K' := by
  simp only [densityIn]
  congr 1
  apply Finset.sum_bij (fun i hi => e i)
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi_t, hi_le⟩
    refine Finset.mem_filter.mpr ⟨?_, hi_le⟩
    have hi_t' : i ∈ (t : Set ι') := Finset.mem_coe.mpr hi_t
    have he_i_s : e i ∈ (s : Set ι) := he.mapsTo hi_t'
    exact Finset.mem_coe.mp he_i_s
  · intro a ha₁ b ha₂ h
    rcases Finset.mem_filter.mp ha₁ with ⟨ha_t, ha_le⟩
    rcases Finset.mem_filter.mp ha₂ with ⟨hb_t, hb_le⟩
    have ha_t' : a ∈ (t : Set ι') := Finset.mem_coe.mpr ha_t
    have hb_t' : b ∈ (t : Set ι') := Finset.mem_coe.mpr hb_t
    exact he.injOn ha_t' hb_t' h
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hb_s, hb_le⟩
    have hb_s' : b ∈ (s : Set ι) := Finset.mem_coe.mpr hb_s
    obtain ⟨a, ha_t', ha_eq⟩ := he.surjOn hb_s'
    have ha_t : a ∈ t := Finset.mem_coe.mp ha_t'
    have ha_le : W (e a) ≤ K' := by
      rw [ha_eq]
      exact hb_le
    refine ⟨a, Finset.mem_filter.mpr ⟨ha_t, ha_le⟩, ha_eq⟩
  · intro i hi
    rfl

/-- **Reindexing the Frostman property along a bijection.**  If `e` restricts to a bijection
from `t` onto `s`, then the reindexed family `W ∘ e` is `C`-Frostman in `K` if and only if
`W` is. -/
theorem IsFrostmanIn.reindex {ι' : Type*} {t : Finset ι'} {e : ι' → ι}
    (he : Set.BijOn e t s) :
    IsFrostmanIn t (W ∘ e) K C ↔ IsFrostmanIn s W K C := by
  constructor
  · intro h K' hK'
    simpa [densityIn_reindex he] using h K' hK'
  · intro h K' hK'
    simpa [densityIn_reindex he] using h K' hK'

/-- Reindexing along a bijection leaves the Frostman constant unchanged. -/
theorem frostmanConstIn_reindex {ι' : Type*} {t : Finset ι'} {e : ι' → ι}
    (he : Set.BijOn e t s) :
    frostmanConstIn t (W ∘ e) K = frostmanConstIn s W K :=
  congrArg sInf (Set.ext fun _ => IsFrostmanIn.reindex (s := s) (W := W) (K := K) (he := he))

end FrostmanConst

/-- The dimensional constant `c` in `card_ge_of_frostmanConstIn_le`: the volume
`3 * Tube.le_volume.c n` of the closed unit ball of an `n`-dimensional inner product space,
divided by the constant `Tube.volume_le.C n` of the tube volume upper bound. -/
noncomputable abbrev card_ge_of_frostmanConstIn_le.C (n : ℕ) : NNReal :=
  3 * Tube.le_volume.c n / Tube.volume_le.C n

section FrostmanConstValue

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}
  {s s' : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}

/-- A single test body witnessing a strict failure of the `C`-Frostman inequality gives a
lower bound `C ≤ C_F(𝕍, K)` on the Frostman constant. -/
theorem le_frostmanConstIn_of_lt_densityIn {K' : ConvexSpaceBody E} (hK' : K' ≤ K)
    (h : C * densityIn s W K < densityIn s W K') :
    C ≤ frostmanConstIn s W K := by
  unfold frostmanConstIn
  refine le_sInf ?_
  intro C'' hC''
  have hC''K' : densityIn s W K' ≤ C'' * densityIn s W K := hC'' K' hK'
  have h_lt : C * densityIn s W K < C'' * densityIn s W K :=
    lt_of_lt_of_le h hC''K'
  apply le_of_not_gt
  intro hC''ltC
  have hle : C'' * densityIn s W K ≤ C * densityIn s W K :=
    mul_le_mul_left (le_of_lt hC''ltC) (densityIn s W K)
  have : C * densityIn s W K < C * densityIn s W K := h_lt.trans_le hle
  exact lt_irrefl _ this

/-- The infimum defining `frostmanConstIn` is attained: a family is always
`C_F(𝕍, K)`-Frostman in `K`. -/
theorem isFrostmanIn_frostmanConstIn (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) : IsFrostmanIn s W K (frostmanConstIn s W K) := by
  intro K' hK'
  let S : Set ENNReal := {C | IsFrostmanIn s W K C}
  have hS : frostmanConstIn s W K = sInf S := rfl
  by_cases hd : densityIn s W K = 0
  · -- case d = 0
    have hsumK : (∑ i ∈ s with W i ≤ K, volume (W i).carrier) = 0 := by
      rw [sum_volume_eq_densityIn_mul_volume, hd, zero_mul]
    have hsumK' : (∑ i ∈ s with W i ≤ K', volume (W i).carrier) = 0 := by
      have hle : (∑ i ∈ s with W i ≤ K', volume (W i).carrier) ≤
          ∑ i ∈ s with W i ≤ K, volume (W i).carrier :=
        Finset.sum_le_sum_of_subset (by
          intro i hi
          simp only [Finset.mem_filter] at hi ⊢
          exact ⟨hi.1, le_trans hi.2 hK'⟩)
      have h0 : 0 ≤ (∑ i ∈ s with W i ≤ K', volume (W i).carrier) := by
        apply zero_le
      refine le_antisymm ?_ h0
      exact hle.trans hsumK.le
    have hd' : densityIn s W K' = 0 := by
      dsimp [densityIn]
      rw [hsumK']
      simp
    simp [hS, hd, hd']
  · -- case d ≠ 0
    have hd_ne_top : densityIn s W K ≠ ⊤ := densityIn_ne_top s W K
    have hd_div : densityIn s W K' / densityIn s W K ≤ sInf S := by
      apply le_sInf
      intro C hC
      have hC' : IsFrostmanIn s W K C := hC
      have hineq : densityIn s W K' ≤ C * densityIn s W K := hC' K' hK'
      rw [ENNReal.div_le_iff_le_mul (Or.inl hd) (Or.inl hd_ne_top)]
      exact hineq
    rw [← ENNReal.div_le_iff_le_mul (Or.inl hd) (Or.inl hd_ne_top)]
    exact hd_div

/-- Converse of `frostmanConstIn_le`: a bound on the Frostman constant gives the
Frostman property.  Together with `frostmanConstIn_le` this makes
`frostmanConstIn s W K ≤ C` and `IsFrostmanIn s W K C` interchangeable. -/
theorem isFrostmanIn_of_frostmanConstIn_le (h : frostmanConstIn s W K ≤ C) :
    IsFrostmanIn s W K C :=
  (isFrostmanIn_frostmanConstIn s W K).mono h

/-- If every member of the family lies in `K' ≤ K`, the two ambient densities differ exactly
by the volume ratio.  This is the first half of `frostmanConstIn_ambient_mono`. -/
theorem densityIn_eq_volume_ratio_mul_densityIn {K' : ConvexSpaceBody E} (hK' : K' ≤ K)
    (hK'vol : volume K'.carrier ≠ 0) (hWK' : ∀ i ∈ s, W i ≤ K') :
    densityIn s W K' = volume K.carrier / volume K'.carrier * densityIn s W K := by
  have hWK : ∀ i ∈ s, W i ≤ K := fun i hi => (hWK' i hi).trans hK'
  have hvK : volume K.carrier ≠ 0 := by
    intro hzero
    apply hK'vol
    exact measure_mono_null (SetLike.coe_subset_coe.mpr hK') hzero
  have hvKtop : volume K.carrier ≠ ⊤ := K.isCompact'.measure_ne_top
  have hK'voltop : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_ne_top
  rw [densityIn_of_all_le hWK', densityIn_of_all_le hWK]
  set SW := ∑ i ∈ s, volume (W i).carrier with hSW
  set vK := volume K.carrier with hvK_def
  set vK' := volume K'.carrier with hvK'_def
  calc
    SW / vK' = (SW * vK) / (vK' * vK) := by
      rw [ENNReal.mul_div_mul_right SW vK' (c := vK) hvK hvKtop]
    _ = (vK * SW) / (vK' * vK) := by rw [mul_comm SW vK]
    _ = (vK / vK') * (SW / vK) := by
      rw [ENNReal.mul_div_mul_comm (Or.inl hK'vol) (Or.inl hK'voltop)]
    _ = (vK / vK') * (SW / vK) := rfl

/-- Replacing a test body `K''` by its intersection with `K'` can only increase the density,
provided every member of the family already lies in `K'`.  This is the second half of
`frostmanConstIn_ambient_mono`; the intersection is formed with `ConvexSpaceBody.inter`, whose
nonemptiness hypothesis `hne` is an explicit argument.  (At the call site it is supplied by a
member of the family contained in `K''`, but the proof below does not need such a member.) -/
theorem densityIn_le_densityIn_inter {K' K'' : ConvexSpaceBody E}
    (hWK' : ∀ i ∈ s, W i ≤ K')
    (hne : (K''.carrier ∩ K'.carrier).Nonempty) :
    densityIn s W K'' ≤ densityIn s W (ConvexSpaceBody.inter K'' K' hne) := by
  set L := ConvexSpaceBody.inter K'' K' hne with hL
  have hfilter : (s.filter fun i => W i ≤ K'') = (s.filter fun i => W i ≤ L) := by
    refine Finset.filter_congr fun i hi => ?_
    constructor
    · intro hW_i_K''
      have hW_i_K' : W i ≤ K' := hWK' i hi
      have h_carrier : (W i).carrier ⊆ L.carrier := by
        calc
          (W i).carrier ⊆ K''.carrier ∩ K'.carrier :=
            Set.subset_inter (SetLike.coe_subset_coe.mpr hW_i_K'')
              (SetLike.coe_subset_coe.mpr hW_i_K')
          _ = L.carrier := by simp [L, ConvexSpaceBody.inter_carrier]
      exact SetLike.coe_subset_coe.mp h_carrier
    · intro hW_i_L
      have hW_i_K'' : (W i).carrier ⊆ K''.carrier := by
        calc
          (W i).carrier ⊆ L.carrier := SetLike.coe_subset_coe.mpr hW_i_L
          _ = K''.carrier ∩ K'.carrier := by simp [L, ConvexSpaceBody.inter_carrier]
          _ ⊆ K''.carrier := Set.inter_subset_left
      exact SetLike.coe_subset_coe.mp hW_i_K''
  have hvol : volume L.carrier ≤ volume K''.carrier := by
    calc
      volume L.carrier = volume (K''.carrier ∩ K'.carrier) := by
        simp [L, ConvexSpaceBody.inter_carrier]
      _ ≤ volume K''.carrier := measure_mono Set.inter_subset_left
  dsimp [densityIn]
  rw [hfilter]
  exact ENNReal.div_le_div_left hvol (∑ i ∈ s with W i ≤ L, volume (W i).carrier)

/-- **Enlarging the ambient body.**  If every member of the family is contained in a
convex body `K'` of positive volume and `K' ≤ K`, then the Frostman constant relative to
`K` is controlled by the one relative to `K'`, at the cost of the volume ratio
`|K| / |K'|`. -/
theorem frostmanConstIn_ambient_mono {K' : ConvexSpaceBody E} (hK' : K' ≤ K)
    (hK'vol : volume K'.carrier ≠ 0) (hWK' : ∀ i ∈ s, W i ≤ K') :
    frostmanConstIn s W K ≤
      volume K.carrier / volume K'.carrier * frostmanConstIn s W K' := by
  set r := volume K.carrier / volume K'.carrier
  set C' := frostmanConstIn s W K'
  have h_allWK : ∀ i ∈ s, W i ≤ K := fun i hi => le_trans (hWK' i hi) hK'
  have hKvol_ne_zero : volume K.carrier ≠ 0 := by
    refine mt (fun hzero => ?_) hK'vol
    exact measure_mono_null hK' hzero
  have hKvol_ne_top : volume K.carrier ≠ ⊤ := K.isCompact'.measure_ne_top
  have hK'vol_ne_top : volume K'.carrier ≠ ⊤ := K'.isCompact'.measure_ne_top
  have hFr : IsFrostmanIn s W K' C' := isFrostmanIn_frostmanConstIn s W K'
  have hS_eq : densityIn s W K' = r * densityIn s W K := by
    have h_eq_mul : densityIn s W K' * volume K'.carrier = densityIn s W K * volume K.carrier := by
      calc
        densityIn s W K' * volume K'.carrier = (∑ i ∈ s, volume (W i).carrier) := by
          rw [sum_volume_eq_densityIn_mul_volume' hWK']
        _ = densityIn s W K * volume K.carrier := by
          rw [sum_volume_eq_densityIn_mul_volume' h_allWK]
    calc
      densityIn s W K' = densityIn s W K' * 1 := by simp
      _ = densityIn s W K' * (volume K'.carrier * (volume K'.carrier)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hK'vol hK'vol_ne_top]
      _ = (densityIn s W K' * volume K'.carrier) * (volume K'.carrier)⁻¹ := by ring
      _ = (densityIn s W K * volume K.carrier) * (volume K'.carrier)⁻¹ := by rw [h_eq_mul]
      _ = densityIn s W K * (volume K.carrier * (volume K'.carrier)⁻¹) := by ring
      _ = densityIn s W K * (volume K.carrier / volume K'.carrier) := by
        rfl
      _ = (volume K.carrier / volume K'.carrier) * densityIn s W K := mul_comm _ _
      _ = r * densityIn s W K := rfl
  have h_key : IsFrostmanIn s W K (r * C') := by
    intro K'' hK''
    by_cases hempty : familyIn s W K'' = ∅
    · have h_num : (∑ i ∈ s with W i ≤ K'', volume (W i).carrier) = 0 := by
        dsimp [familyIn] at hempty ⊢
        simp [hempty]
      simp [densityIn, h_num]
    · have hne_nonempty : (familyIn s W K'').Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨i₀, hi₀⟩ := hne_nonempty
      rcases Finset.mem_filter.mp hi₀ with ⟨hi₀_mem_s, hi₀le⟩
      have hi₀le' : W i₀ ≤ K' := hWK' i₀ hi₀_mem_s
      have h_sub_W0 : (W i₀ : Set E) ⊆ (K'' : Set E) ∩ (K' : Set E) :=
        Set.subset_inter (by exact hi₀le) (by exact hi₀le')
      have hne_inter : (K''.carrier ∩ K'.carrier).Nonempty :=
        (W i₀).nonempty'.mono h_sub_W0
      let L := ConvexSpaceBody.inter K'' K' hne_inter
      have hLK'' : L ≤ K'' := by
        have : (L : Set E) = (K'' : Set E) ∩ (K' : Set E) := by
          rfl
        -- (L : Set E) ⊆ (K'' : Set E)
        have hsub : (L : Set E) ⊆ (K'' : Set E) := by
          rw [this]
          exact Set.inter_subset_left
        exact SetLike.coe_subset_coe.mpr hsub
      have hL_K' : L ≤ K' := by
        have : (L : Set E) = (K'' : Set E) ∩ (K' : Set E) := by
          rfl
        have hsub : (L : Set E) ⊆ (K' : Set E) := by
          rw [this]
          exact Set.inter_subset_right
        exact SetLike.coe_subset_coe.mpr hsub
      have h_volL_le : volume L.carrier ≤ volume K''.carrier := by
        calc
          volume L.carrier = volume (K''.carrier ∩ K'.carrier) := by
            simp [L, ConvexSpaceBody.inter_carrier]
          _ ≤ volume K''.carrier := measure_mono Set.inter_subset_left
      have h_familyIn : familyIn s W K'' = familyIn s W L := by
        dsimp [familyIn]
        apply Finset.filter_congr
        intro i hi
        constructor
        · intro hW_K''
          have hW_K' : W i ≤ K' := hWK' i hi
          have h_sub : (W i : Set E) ⊆ (L : Set E) := by
            calc
              (W i : Set E) ⊆ (K'' : Set E) ∩ (K' : Set E) :=
                Set.subset_inter hW_K'' hW_K'
              _ = (L : Set E) := by rfl
          exact SetLike.coe_subset_coe.mpr h_sub
        · intro hW_L
          exact le_trans hW_L hLK''
      have h_density : densityIn s W K'' ≤ densityIn s W L := by
        have h_num_eq : (∑ i ∈ s with W i ≤ K'', volume (W i).carrier) =
            (∑ i ∈ s with W i ≤ L, volume (W i).carrier) := by
          simpa [familyIn] using congrArg (fun t => ∑ i ∈ t, volume (W i).carrier) h_familyIn
        dsimp [densityIn]
        rw [h_num_eq]
        apply ENNReal.div_le_div_left h_volL_le
      calc
        densityIn s W K'' ≤ densityIn s W L := h_density
        _ ≤ C' * densityIn s W K' := hFr L hL_K'
        _ = C' * (r * densityIn s W K) := by rw [hS_eq]
        _ = (r * C') * densityIn s W K := by ring
  exact frostmanConstIn_le h_key

/-- **Frostman constant of a large subfamily.**  If all the bodies of a nonempty family
have the same positive volume, are contained in a convex body `K` of positive volume, and
`s'` is a subfamily with `κ * |s| ≤ |s'|` for some `κ ≠ 0`, then the Frostman constant
of the subfamily is at most `κ⁻¹` times that of the whole family.  (The blueprint's
`κ ≤ 1` is automatic from `hs'` and `hcard`, so it is not assumed; neither are the
blueprint's positivity clauses `v ≠ 0` and `|K| ≠ 0`, which the proof does not use.) -/
theorem frostmanConstIn_subfamily_le {v κ : ENNReal} (hs : s.Nonempty)
    (hvol : ∀ i ∈ s, volume (W i).carrier = v)
    (hWK : ∀ i ∈ s, W i ≤ K)
    (hs' : s' ⊆ s) (hκ : κ ≠ 0) (hcard : κ * s.card ≤ s'.card) :
    frostmanConstIn s' W K ≤ κ⁻¹ * frostmanConstIn s W K := by
  set C := frostmanConstIn s W K with hC
  have hCfrostman : IsFrostmanIn s W K C := isFrostmanIn_frostmanConstIn s W K
  have hκ_top : κ ≠ ⊤ := by
    intro hκtop
    have hcard0 : (s.card : ENNReal) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hs
    have htop : (κ : ENNReal) * (s.card : ENNReal) = ⊤ := by
      simp [hκtop, hcard0]
    have htop_le : (⊤ : ENNReal) ≤ (s'.card : ENNReal) :=
      calc
        (⊤ : ENNReal) = (κ : ENNReal) * (s.card : ENNReal) := by
          simp [hκtop, hcard0]
        _ ≤ (s'.card : ENNReal) := hcard
    have hfinite : (s'.card : ENNReal) < ⊤ := by
      simp
    exact not_lt.mpr htop_le hfinite
  -- compute densityIn for s and s' in terms of s.card, s'.card, v, and |K|
  have hsum_s : ∑ i ∈ s, volume (W i).carrier = (s.card : ENNReal) * v := by
    calc
      ∑ i ∈ s, volume (W i).carrier = ∑ i ∈ s, v := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hvol i hi]
      _ = (s.card : ENNReal) * v := by simp
  have hsum_s' : ∑ i ∈ s', volume (W i).carrier = (s'.card : ENNReal) * v := by
    calc
      ∑ i ∈ s', volume (W i).carrier = ∑ i ∈ s', v := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hvol i (hs' hi)]
      _ = (s'.card : ENNReal) * v := by simp
  have hdensity_s : densityIn s W K = (s.card * v) / volume K.carrier := by
    rw [densityIn_of_all_le hWK, hsum_s]
  have hdensity_s' : densityIn s' W K = (s'.card * v) / volume K.carrier := by
    rw [densityIn_of_all_le (fun i hi => hWK i (hs' hi)), hsum_s']
  have hcard_density : κ * densityIn s W K ≤ densityIn s' W K := by
    rw [hdensity_s, hdensity_s']
    have h_mul : κ * (s.card * v) ≤ s'.card * v := by
      calc
        κ * (s.card * v) = (κ * s.card) * v := by ring
        _ ≤ (s'.card : ENNReal) * v := mul_le_mul_left hcard v
    calc
      κ * ((s.card * v) / volume K.carrier) = (κ * (s.card * v)) / volume K.carrier := by
        simp [ENNReal.div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm]
      _ ≤ (s'.card * v) / volume K.carrier := ENNReal.div_le_div h_mul (le_refl _)
  have h_density_le : densityIn s W K ≤ κ⁻¹ * densityIn s' W K := by
    calc
      densityIn s W K = (κ⁻¹ * κ) * densityIn s W K := by
        simp [ENNReal.inv_mul_cancel hκ hκ_top]
      _ = κ⁻¹ * (κ * densityIn s W K) := by ring
      _ ≤ κ⁻¹ * densityIn s' W K := by
        gcongr
  have h_frostman_subfamily : IsFrostmanIn s' W K (κ⁻¹ * C) := by
    intro K' hK'
    calc
      densityIn s' W K' ≤ densityIn s W K' := (densityIn_mono W K') hs'
      _ ≤ C * densityIn s W K := hCfrostman K' hK'
      _ ≤ C * (κ⁻¹ * densityIn s' W K) := by
        gcongr
      _ = (κ⁻¹ * C) * densityIn s' W K := by ring
  exact frostmanConstIn_le h_frostman_subfamily

/-- **Two-sided transport of the Frostman constant.**  Let `W` and `V` be two families of
convex bodies indexed by the same finite set `s`, all contained in a convex body `K` of
positive volume, with `1 ≤ C`.  Assume

* `W i ≤ V i` and `|V i| ≤ C * |W i|` for every `i ∈ s`;
* every convex body `K' ≤ K` admits a convex body `L ≤ K` with `K' ≤ L`,
  `|L| ≤ C * |K'|`, and `V i ≤ L` for every `i ∈ s` with `W i ≤ K'`.

Then the Frostman constants of the two families are comparable:
`C_F(𝕎, K) ≤ C² · C_F(𝕍, K)` and `C_F(𝕍, K) ≤ C · C_F(𝕎, K)`.

The lower bound is stated in the multiplicative form `C_F(𝕎, K) ≤ C ^ 2 * C_F(𝕍, K)`
rather than as `(C ^ 2)⁻¹ * C_F(𝕎, K) ≤ C_F(𝕍, K)`, since the two are equivalent for
`1 ≤ C` but the multiplicative form stays informative when `C = ⊤`.  The hypothesis
`W i ≤ K` is omitted: it follows from `hWV` and `hVK`.  The blueprint's positivity clause
`|K| ≠ 0` is omitted as well: the proof does not use it. -/
theorem frostmanConstIn_ge_of_comparable {V : ι → ConvexSpaceBody E}
    (hC : 1 ≤ C)
    (hVK : ∀ i ∈ s, V i ≤ K)
    (hWV : ∀ i ∈ s, W i ≤ V i)
    (hvol : ∀ i ∈ s, volume (V i).carrier ≤ C * volume (W i).carrier)
    (hdilate : ∀ K' ≤ K, ∃ L ≤ K, K' ≤ L ∧ volume L.carrier ≤ C * volume K'.carrier ∧
      ∀ i ∈ s, W i ≤ K' → V i ≤ L) :
    frostmanConstIn s W K ≤ C ^ 2 * frostmanConstIn s V K ∧
      frostmanConstIn s V K ≤ C * frostmanConstIn s W K := by
  have hWK : ∀ i ∈ s, W i ≤ K := fun i hi => (hWV i hi).trans (hVK i hi)
  have h_volW_le_V : ∀ i ∈ s, volume (W i).carrier ≤ volume (V i).carrier :=
    fun i hi => measure_mono (hWV i hi)
  have h_sumW_le_sumV : ∑ i ∈ s, volume (W i).carrier ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum fun i hi => h_volW_le_V i hi
  have h_sumV_le_C_mul_sumW :
      ∑ i ∈ s, volume (V i).carrier ≤ C * ∑ i ∈ s, volume (W i).carrier := by
    calc
      ∑ i ∈ s, volume (V i).carrier ≤ ∑ i ∈ s, C * volume (W i).carrier :=
        Finset.sum_le_sum fun i hi => hvol i hi
      _ = C * ∑ i ∈ s, volume (W i).carrier := by simp [Finset.mul_sum]
  -- densityIn s W K ≤ densityIn s V K
  have h_densityW_le_V : densityIn s W K ≤ densityIn s V K := by
    rw [densityIn_of_all_le hWK, densityIn_of_all_le hVK]
    exact ENNReal.div_le_div h_sumW_le_sumV (le_refl _)
  -- densityIn s V K ≤ C * densityIn s W K
  have h_densityV_le_C_mul_W : densityIn s V K ≤ C * densityIn s W K := by
    calc
      densityIn s V K = (∑ i ∈ s, volume (V i).carrier) / volume K.carrier := by
        rw [densityIn_of_all_le hVK]
      _ ≤ (C * ∑ i ∈ s, volume (W i).carrier) / volume K.carrier :=
        ENNReal.div_le_div_right h_sumV_le_C_mul_sumW _
      _ = C * ((∑ i ∈ s, volume (W i).carrier) / volume K.carrier) := by
        calc
          (C * ∑ i ∈ s, volume (W i).carrier) / volume K.carrier
              = (C * ∑ i ∈ s, volume (W i).carrier) * (volume K.carrier)⁻¹ := rfl
          _ = C * ((∑ i ∈ s, volume (W i).carrier) * (volume K.carrier)⁻¹) := by
            simp [mul_assoc]
          _ = C * ((∑ i ∈ s, volume (W i).carrier) / volume K.carrier) := rfl
      _ = C * densityIn s W K := by rw [densityIn_of_all_le hWK]
  -- Second conjunct: C_F(V,K) ≤ C * C_F(W,K)
  have h_second : frostmanConstIn s V K ≤ C * frostmanConstIn s W K := by
    have h_isFrostmanW : IsFrostmanIn s W K (frostmanConstIn s W K) :=
      isFrostmanIn_frostmanConstIn s W K
    have h_isFrostmanV : IsFrostmanIn s V K (C * frostmanConstIn s W K) := by
      intro K' hK'
      calc
        densityIn s V K' ≤ C * densityIn s W K' := by
          rw [densityIn_le_iff]
          calc
            ∑ i ∈ s with V i ≤ K', volume (V i).carrier
                ≤ ∑ i ∈ s with V i ≤ K', C * volume (W i).carrier :=
              Finset.sum_le_sum fun i hi => hvol i ((Finset.mem_filter.mp hi).1)
            _ = C * ∑ i ∈ s with V i ≤ K', volume (W i).carrier := by
              simp [Finset.mul_sum]
            _ ≤ C * ∑ i ∈ s with W i ≤ K', volume (W i).carrier := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hsub : (s.filter fun i => V i ≤ K') ⊆ (s.filter fun i => W i ≤ K') := by
                intro i hi
                rcases Finset.mem_filter.mp hi with ⟨hi_s, hi_V⟩
                refine Finset.mem_filter.mpr ⟨hi_s, (hWV i hi_s).trans hi_V⟩
              exact Finset.sum_le_sum_of_subset hsub
            _ = (C * densityIn s W K') * volume K'.carrier := by
              calc
                C * ∑ i ∈ s with W i ≤ K', volume (W i).carrier
                    = C * (densityIn s W K' * volume K'.carrier) := by
                  rw [sum_volume_eq_densityIn_mul_volume]
                _ = (C * densityIn s W K') * volume K'.carrier := by ring
        _ ≤ C * (frostmanConstIn s W K * densityIn s W K) := by
          gcongr
          exact h_isFrostmanW K' hK'
        _ = C * frostmanConstIn s W K * densityIn s W K := by ring
        _ ≤ C * frostmanConstIn s W K * densityIn s V K := by
          gcongr
    exact frostmanConstIn_le h_isFrostmanV
  -- First conjunct: C_F(W,K) ≤ C^2 * C_F(V,K)
  have h_first : frostmanConstIn s W K ≤ C ^ 2 * frostmanConstIn s V K := by
    have h_isFrostmanV : IsFrostmanIn s V K (frostmanConstIn s V K) :=
      isFrostmanIn_frostmanConstIn s V K
    have h_isFrostmanW : IsFrostmanIn s W K (C ^ 2 * frostmanConstIn s V K) := by
      intro K'' hK''
      by_cases hK''vol0 : volume K''.carrier = 0
      · rw [densityIn_eq_zero_of_volume_eq_zero hK''vol0]
        exact zero_le
      obtain ⟨L, hL, hK''L, hvolL, hWL⟩ := hdilate K'' hK''
      have hK''vol_ne_top : volume K''.carrier ≠ ⊤ := K''.isCompact.measure_ne_top
      have hLvol_ne_top : volume L.carrier ≠ ⊤ := L.isCompact.measure_ne_top
      have hLvol_ne_zero : volume L.carrier ≠ 0 := by
        intro hzero
        apply hK''vol0
        exact measure_mono_null hK''L hzero
      have h_filter_subset : (s.filter fun i => W i ≤ K'') ⊆ (s.filter fun i => V i ≤ L) := by
        intro i hi
        rcases Finset.mem_filter.mp hi with ⟨hi_s, hi_W⟩
        refine Finset.mem_filter.mpr ⟨hi_s, hWL i hi_s hi_W⟩
      have h_sumW_subset : ∑ i ∈ s with W i ≤ K'', volume (W i).carrier
          ≤ ∑ i ∈ s with V i ≤ L, volume (V i).carrier :=
        (Finset.sum_le_sum_of_subset h_filter_subset).trans
          (Finset.sum_le_sum fun i hi => h_volW_le_V i ((Finset.mem_filter.mp hi).1))
      -- (C * a) / a = C when a ≠ 0, a ≠ ∞
      have h_div_C : (C * volume K''.carrier) / volume K''.carrier = C := by
        calc
          (C * volume K''.carrier) / volume K''.carrier
              = (C * volume K''.carrier) * (volume K''.carrier)⁻¹ := rfl
          _ = C * (volume K''.carrier * (volume K''.carrier)⁻¹) := by
            simp [mul_assoc]
          _ = C * 1 := by simp [ENNReal.mul_inv_cancel hK''vol0 hK''vol_ne_top]
          _ = C := by simp
      have h_ratio_le_C : (volume L.carrier) / volume K''.carrier ≤ C :=
        calc
          (volume L.carrier) / volume K''.carrier
              ≤ (C * volume K''.carrier) / volume K''.carrier :=
            ENNReal.div_le_div hvolL (le_refl _)
          _ = C := h_div_C
      set S := ∑ i ∈ s with V i ≤ L, volume (V i).carrier
      have h_ident : S / volume K''.carrier =
          densityIn s V L * ((volume L.carrier) / volume K''.carrier) := by
        have h_inv_mul : (volume L.carrier)⁻¹ * volume L.carrier = 1 :=
          ENNReal.inv_mul_cancel hLvol_ne_zero hLvol_ne_top
        calc
          S / volume K''.carrier = S * (volume K''.carrier)⁻¹ := rfl
          _ = S * (1) * (volume K''.carrier)⁻¹ := by simp
          _ = S * ((volume L.carrier)⁻¹ * volume L.carrier) * (volume K''.carrier)⁻¹ := by
            rw [← h_inv_mul]
          _ = (S * (volume L.carrier)⁻¹) * (volume L.carrier * (volume K''.carrier)⁻¹) := by
            simp [mul_assoc]
          _ = (S / volume L.carrier) * (volume L.carrier / volume K''.carrier) := rfl
          _ = densityIn s V L * ((volume L.carrier) / volume K''.carrier) := rfl
      calc
        densityIn s W K''
            = (∑ i ∈ s with W i ≤ K'', volume (W i).carrier) / volume K''.carrier := rfl
        _ ≤ (∑ i ∈ s with V i ≤ L, volume (V i).carrier) / volume K''.carrier :=
          ENNReal.div_le_div_right h_sumW_subset _
        _ = densityIn s V L * ((volume L.carrier) / volume K''.carrier) := h_ident
        _ ≤ densityIn s V L * C := by
          gcongr
        _ ≤ (frostmanConstIn s V K * densityIn s V K) * C := by
          gcongr
          exact h_isFrostmanV L hL
        _ = C * frostmanConstIn s V K * densityIn s V K := by ring
        _ ≤ C * frostmanConstIn s V K * (C * densityIn s W K) := by
          gcongr
        _ = C ^ 2 * frostmanConstIn s V K * densityIn s W K := by ring
    exact frostmanConstIn_le h_isFrostmanW
  exact ⟨h_first, h_second⟩

/-- The volume of the closed unit ball, in the spelling `3 * Tube.le_volume.c n` used by
`card_ge_of_frostmanConstIn_le.C`.  Compare the `hV₁` step of `Kakeya.Tube.card_le_of_densityIn_le`,
which performs the same computation with the equivalent spelling
`Tube.card_le_of_densityIn_le.C n * Tube.le_volume.c n`. -/
theorem volume_closedUnitBall_eq [Nontrivial E] :
    volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
      = ((3 * Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) := by
  calc
    volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
        = ENNReal.ofReal (Tube.BallVolume.V (Module.finrank ℝ E)) := by
          rw [ConvexSpaceBody.closedUnitBall_carrier, InnerProductSpace.volume_closedBall]
          simp only [ENNReal.ofReal_one, one_pow, one_mul]
    _ = ENNReal.ofReal (3 * Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
          rw [Tube.BallVolume.V_eq (Module.finrank ℝ E)]
    _ = ((3 * Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) := by
          simp

/-- **A Frostman bound forces many tubes.**  If a nonempty family of `δ`-tubes contained in
the closed unit ball has Frostman constant at most `δ ^ (-η)`, then
`δ ^ (n - 1) * |s| ≥ c(n) * δ ^ η`, where `n` is the ambient dimension.
For `n = 3` this reads `δ ^ 2 * |s| ≥ c(3) * δ ^ η`.  The blueprint's `0 ≤ η` is not
needed: the argument only rearranges `δ ^ (-η) * δ ^ η = 1`, which holds for all real `η`. -/
theorem card_ge_of_frostmanConstIn_le [Nontrivial E] {δ : NNReal} (hδ : δ ≠ 0) (hδ1 : δ ≤ 1)
    {T : ι → Tube δ E} {η : ℝ} (hs : s.Nonempty)
    (hT : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall)
    (h : frostmanConstIn s (fun i ↦ (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
      ≤ (δ : ENNReal) ^ (-η)) :
    (card_ge_of_frostmanConstIn_le.C (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ η
      ≤ (δ : ENNReal) ^ ((Module.finrank ℝ E : ℝ) - 1) * s.card := by
  set n := Module.finrank ℝ E
  set d : ENNReal := (δ : ENNReal)
  set W : ι → ConvexSpaceBody E := fun i ↦ (T i).toConvexSpaceBody
  set B₁ : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  set V₁ : ENNReal := volume B₁.carrier
  set A : ENNReal := (s.card : ENNReal)
  set M : ENNReal := (Tube.volume_le.C n : ENNReal)
  set X : ENNReal := A * M * d ^ (n - 1) with hX
  -- Basic non-degeneracy
  have hn : 1 ≤ n := by exact Module.finrank_pos
  have hd_ne : d ≠ 0 := by
    dsimp [d]
    exact ENNReal.coe_ne_zero.mpr hδ
  have hd_top : d ≠ ⊤ := by
    dsimp [d]
    exact ENNReal.coe_ne_top
  have hM_ne : M ≠ 0 := by
    dsimp [M]
    exact ENNReal.coe_ne_zero.mpr (by positivity : Tube.volume_le.C n ≠ 0)
  have hM_top : M ≠ ⊤ := by
    dsimp [M]
    exact ENNReal.coe_ne_top
  have hV₁_ne : V₁ ≠ 0 := by
    dsimp [V₁, B₁]
    exact ne_of_gt ConvexSpaceBody.closedUnitBall_volume_pos
  have hV₁_top : V₁ ≠ ⊤ := by
    dsimp [V₁, B₁]
    exact ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top
  -- Volume of the unit ball
  have hV₁eq : V₁ = ((3 * Tube.le_volume.c n : NNReal) : ENNReal) := by
    dsimp [V₁, B₁]
    exact volume_closedUnitBall_eq (E := E)
  -- The Frostman property
  have hFr : IsFrostmanIn s W B₁ (d ^ (-η)) := by
    simpa [W, B₁, d] using isFrostmanIn_of_frostmanConstIn_le h
  have hmax : maxDensity s W ≤ d ^ (-η) * densityIn s W B₁ := by
    simpa [W, B₁, d] using hFr.maxDensity_le_of_carrier_subset hT
  -- Each tube has positive volume
  have hvol_pos : ∀ i ∈ s, 0 < volume (W i).carrier := by
    intro i hi
    have hle := (T i).le_volume
    have hc_ne : (Tube.le_volume.c n : ENNReal) ≠ 0 := by
      exact ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos n).ne'
    have hpow_ne : d ^ (n - 1) ≠ 0 := ENNReal.pow_ne_zero hd_ne (n - 1)
    have hprod_pos : 0 < (Tube.le_volume.c n : ENNReal) * d ^ (n - 1) :=
      ENNReal.mul_pos hc_ne hpow_ne
    simpa [W, d] using hprod_pos.trans_le hle
  obtain ⟨i₀, hi₀⟩ := hs
  have h1 : 1 ≤ maxDensity s W := one_le_maxDensity ⟨i₀, hi₀, hvol_pos i₀ hi₀⟩
  -- density bound
  have hdens : densityIn s W B₁ ≤ X / V₁ := by
    rw [densityIn_of_all_le hT]
    gcongr
    calc
      (∑ i ∈ s, volume (W i).carrier) ≤ ∑ i ∈ s, (M * d ^ (n - 1)) := by
        exact Finset.sum_le_sum (fun i hi => by
          simpa [W, M, d] using Tube.volume_le hδ1 (T i))
      _ = A * (M * d ^ (n - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = X := by
        rw [hX, mul_assoc]
  -- main chain
  have hmain : 1 ≤ d ^ (-η) * (X / V₁) := by
    calc
      1 ≤ maxDensity s W := h1
      _ ≤ d ^ (-η) * densityIn s W B₁ := hmax
      _ ≤ d ^ (-η) * (X / V₁) := by gcongr
  -- exponent conversion
  have hpow : d ^ (n - 1 : ℕ) = d ^ ((n : ℝ) - 1) := by
    rw [← ENNReal.rpow_natCast d (n - 1)]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  -- cancellation d^η * d^(-η) = 1
  have hd_pow_ne_zero : d ^ η ≠ 0 := by
    intro h
    rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with (⟨hd0, _⟩ | ⟨hdtop, _⟩)
    · exact hd_ne hd0
    · exact hd_top hdtop
  have hd_pow_ne_top : d ^ η ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hd_ne hd_top
  have hcancel : d ^ η * d ^ (-η) = 1 := by
    calc
      d ^ η * d ^ (-η) = d ^ η * (d ^ η)⁻¹ := by rw [ENNReal.rpow_neg d η]
      _ = 1 := ENNReal.mul_inv_cancel hd_pow_ne_zero hd_pow_ne_top
  -- V₁ * d^η ≤ X
  have hVd : V₁ * d ^ η ≤ X := by
    calc
      V₁ * d ^ η = (V₁ * d ^ η) * 1 := by rw [mul_one]
      _ ≤ (V₁ * d ^ η) * (d ^ (-η) * (X / V₁)) := by
        gcongr
      _ = X := by
        calc
          (V₁ * d ^ η) * (d ^ (-η) * (X / V₁))
              = V₁ * ((d ^ η * d ^ (-η)) * (X / V₁)) := by ac_rfl
          _ = V₁ * (1 * (X / V₁)) := by rw [hcancel]
          _ = V₁ * (X / V₁) := by rw [one_mul]
          _ = X := ENNReal.mul_div_cancel hV₁_ne hV₁_top
  -- coefficient
  have hC_coe : (card_ge_of_frostmanConstIn_le.C n : ENNReal) = V₁ / M := by
    unfold card_ge_of_frostmanConstIn_le.C
    rw [ENNReal.coe_div (by positivity : (Tube.volume_le.C n : NNReal) ≠ 0), hV₁eq]
  -- final assembly
  calc
    (card_ge_of_frostmanConstIn_le.C n : ENNReal) * d ^ η = (V₁ / M) * d ^ η := by rw [hC_coe]
    _ = (V₁ * d ^ η) / M := by
      rw [div_eq_mul_inv, mul_assoc, mul_comm (M⁻¹) (d ^ η), ← mul_assoc, ← div_eq_mul_inv]
    _ ≤ d ^ ((n : ℝ) - 1) * A := by
      rw [ENNReal.div_le_iff hM_ne hM_top]
      calc
        V₁ * d ^ η ≤ X := hVd
        _ = A * M * d ^ (n - 1) := hX
        _ = A * M * d ^ ((n : ℝ) - 1) := by rw [hpow]
        _ = (d ^ ((n : ℝ) - 1) * A) * M := by ac_rfl

end FrostmanConstValue

end ConvexSpaceBody

/-!
# Frostman restriction and translation helpers
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter


namespace Kakeya

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `IsFrostmanIn` is monotone in the Frostman constant. -/
lemma isFrostmanIn_mono_helper
    {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C C' : ENNReal}
    (h : IsFrostmanIn s W K C) (hC : C ≤ C') :
    IsFrostmanIn s W K C' := fun K' hK' =>
  (h K' hK').trans (mul_le_mul_of_nonneg_right hC bot_le)

/-- If two body-families agree on `s`, the Frostman property transfers. -/
lemma isFrostmanIn_of_eqOn
    {ι : Type*} {s : Finset ι} {W W' : ι → ConvexSpaceBody E}
    (h : ∀ i ∈ s, W i = W' i) {K : ConvexSpaceBody E} {C : ENNReal}
    (hF : IsFrostmanIn s W K C) :
    IsFrostmanIn s W' K C := by
  intro K' hK'
  rw [← densityIn_eq_of_eqOn (E := E) s h K',
      ← densityIn_eq_of_eqOn (E := E) s h K]
  exact hF K' hK'

end Kakeya
