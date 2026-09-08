/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Real

/-!
  In this file we define and collect basic properties of the notion of
  C convex Katz-Tao
-/

@[expose] public section

open MeasureTheory Kakeya Convexity

namespace ConvexSpaceBody

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E]
  [MeasureSpace E]
  {ι : Type*}
  (s : Finset ι)
  (W : ι → ConvexSpaceBody E)

-- this should really be inline or abbrev
/-- The notion of C-convex-Katz-Tao defined in [GWZ, Definition 3.1] -/
def IsKatzTao (C : ENNReal) := maxDensity s W ≤ C

lemma IsKatzTao_def {C : ENNReal} : IsKatzTao s W C ↔ maxDensity s W ≤ C := Iff.rfl

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  {s : Finset ι}
  {W : ι → ConvexSpaceBody E}

theorem isKatzTao_iff (s : Finset ι) (W : ι → ConvexSpaceBody E) (C : ENNReal) : IsKatzTao s W C ↔
    ∀ K, ∑ i ∈ s with W i ≤ K, volume (W i).carrier ≤ C * volume K.carrier :=
  (maxDensity_le_iff s W C).trans <| forall_congr' fun _ ↦ densityIn_le_iff _ _ _ C

/-- The property of being C-Katz-Tao is inherited downwards:
    if V is C-Katz-Tao, then every subset V' ⊆ V is also C-Katz-Tao. -/
theorem IsKatzTao.subset {s' : Finset ι} {C : ENNReal}
    (h : IsKatzTao s W C) (hs : s' ⊆ s) : IsKatzTao s' W C :=
  (maxDensity_mono W hs).trans h

open Classical in
/-- Katz--Tao control is preserved by an injective reindexing of a finite subfamily. -/
theorem IsKatzTao.of_injOn_reindex
    {κ : Type*} {u : Finset κ} {e : ι → κ} {U : κ → ConvexSpaceBody E}
    {C : ENNReal} (h : IsKatzTao u U C)
    (hmem : ∀ i ∈ s, e i ∈ u) (hinj : Set.InjOn e ↑s) :
    IsKatzTao s (fun i ↦ U (e i)) C := by
  rw [isKatzTao_iff]
  intro K
  calc
    ∑ i ∈ s with U (e i) ≤ K, volume (U (e i)).carrier =
        ∑ j ∈ (s.filter fun i ↦ U (e i) ≤ K).image e,
          volume (U j).carrier := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      exact hinj (Finset.mem_coe.mpr (Finset.mem_filter.mp hi).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp hj).1) hij
    _ ≤ ∑ j ∈ u with U j ≤ K, volume (U j).carrier := by
      apply Finset.sum_le_sum_of_subset
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      exact Finset.mem_filter.mpr ⟨hmem i (Finset.mem_filter.mp hi).1,
        (Finset.mem_filter.mp hi).2⟩
    _ ≤ C * volume K.carrier := (isKatzTao_iff u U C).mp h K

/-- The Katz-Tao property is monotone in the constant: if `W` is C-Katz-Tao and `C ≤ C'`,
    then `W` is C'-Katz-Tao. -/
theorem IsKatzTao.mono {C C' : ENNReal}
    (h : IsKatzTao s W C) (hle : C ≤ C') : IsKatzTao s W C' := le_trans h hle

/-- If `W` indexed by `s` is C-Katz-Tao and every member is contained in `K` with volume
    at least `v`, then `|s| * v ≤ C * vol(K)` (as `ENNReal`). -/
theorem IsKatzTao.card_mul_le {C v : ENNReal} {K : ConvexSpaceBody E}
    (hKT : IsKatzTao s W C)
    (h_sub : ∀ i ∈ s, W i ≤ K)
    (h_vol_lb : ∀ i ∈ s, v ≤ volume (W i).carrier) :
    (s.card : ENNReal) * v ≤ C * volume K.carrier := by
  have hKT_unf := (isKatzTao_iff s W C).mp hKT K
  rw [Finset.filter_true_of_mem h_sub] at hKT_unf
  rw [show ((s.card : ENNReal) * v) = ∑ i ∈ s, v by
        rw [Finset.sum_const, nsmul_eq_mul]]
  exact (Finset.sum_le_sum h_vol_lb).trans hKT_unf

/-- ℝ-valued form of `card_mul_le`. Requires `C ≠ ⊤` so the right-hand side is meaningful
    after converting through `ENNReal.toReal`. -/
theorem IsKatzTao.card_mul_le_real {C : ENNReal} {v : ℝ} {K : ConvexSpaceBody E}
    (hKT : IsKatzTao s W C) (hC : C ≠ ⊤)
    (h_sub : ∀ i ∈ s, W i ≤ K)
    (h_vol_lb : ∀ i ∈ s, v ≤ volume.real (W i).carrier) :
    s.card * v ≤ C.toReal * volume.real K.carrier := by
  calc (s.card : ℝ) * v
      = ∑ _ ∈ s, v := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, volume.real (W i).carrier := Finset.sum_le_sum h_vol_lb
    _ = (∑ i ∈ s, volume (W i).carrier).toReal :=
        (ENNReal.toReal_sum fun i _ => (W i).isCompact.measure_ne_top).symm
    _ ≤ (C * volume K.carrier).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hC K.isCompact.measure_ne_top)
          (Finset.filter_true_of_mem h_sub ▸ (isKatzTao_iff s W C).mp hKT K)
    _ = C.toReal * volume.real K.carrier := ENNReal.toReal_mul

/-- ℝ-valued variant of `card_mul_le_real` solved for the cardinality. -/
theorem IsKatzTao.card_le_div_real {C : ENNReal} {v : ℝ} {K : ConvexSpaceBody E}
    (hKT : IsKatzTao s W C) (hC : C ≠ ⊤) (hv : 0 < v)
    (h_sub : ∀ i ∈ s, W i ≤ K)
    (h_vol_lb : ∀ i ∈ s, v ≤ volume.real (W i).carrier) :
    (s.card : ℝ) ≤ C.toReal * volume.real K.carrier / v := by
  rw [le_div_iff₀ hv]
  exact IsKatzTao.card_mul_le_real hKT hC h_sub h_vol_lb

end ConvexSpaceBody
