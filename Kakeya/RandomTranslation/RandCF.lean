/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.Counting
public import Kakeya.Tube.EDUpToMult
public import Kakeya.RandomTranslation.EDChernoffNet

/-!
# Random translation packing ([GWZ], Lemma 3.8, proved in §9)

This file proves `exists_randCF_translation_family`, which constructs a
Frostman-controlled, essentially distinct translated tube family. Here `randCF`
is the label for [GWZ, Lemma 3.8], and `CF` denotes the Frostman constant $C_F$.
-/

@[expose] public section

open MeasureTheory Metric ProbabilityTheory Topology Filter

namespace Kakeya

section RandCF

universe v

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 2500 in
-- The metric rewriting and final linear-arithmetic step need a small amount of extra elaboration.
/-- A translation based in the unit ball sends a tube in `B(0, 1)` into `B(0, 2)`. -/
private lemma translation_preserves_carrier_in_ball_plus_one
    {Ω : Type*} [MeasurableSpace Ω] [HasUniformTranslation Ω E]
    {δ : NNReal} (T : ShadedTube δ E)
    (hT_in : T.carrier ⊆ Metric.closedBall (0 : E) 1)
    (ω : Ω)
    (hω_in :
      HasUniformTranslation.shift (Ω := Ω) (E := E) ω (0 : E)
        ∈ Metric.closedBall (0 : E) 1) :
    ((HasUniformTranslation.shift (Ω := Ω) (E := E) ω).actShadedTube T).carrier
      ⊆ Metric.closedBall (0 : E) 2 := by
  rw [Translation.actShadedTube_carrier]
  rintro y ⟨x, hx, hyx⟩
  rw [← hyx, Metric.mem_closedBall]
  refine (dist_triangle _ (HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0) _).trans ?_
  rw [(HasUniformTranslation.shift (Ω := Ω) (E := E) ω).dist_map x 0]
  linarith [Metric.mem_closedBall.mp (hT_in hx), Metric.mem_closedBall.mp hω_in]

set_option maxHeartbeats 5000 in
-- Expanding the product-family sums and translating both measures exceeds the default budget.
/-- Product translation preserves the fullness of a shaded tube family. -/
private lemma fullness_eq_under_product_translation
    {Ω : Type*} [MeasurableSpace Ω] [HasUniformTranslation Ω E]
    {δ : NNReal}
    {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E)
    (J : ℕ) (hJ_pos : 0 < J)
    (ω : Fin J → Ω) :
    ShadedBody.fullness (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
            (T p.1)).toShadedBody) =
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) := by
  set V : ι → ShadedBody E := fun i => (T i).toShadedBody
  set V' : (ι × Fin J) → ShadedBody E :=
    fun p => ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
      (T p.1)).toShadedBody
  have key : ∀ f : ShadedBody E → Set E,
      (∀ (i : ι) (j : Fin J), volume (f (V' (i, j))) = volume (f (V i))) →
      ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (f (V' p)) =
        (J : ENNReal) * ∑ i ∈ s, volume (f (V i)) := fun f hf => by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp_rw [hf i]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.coe_inj, ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  unfold ShadedBody.fullness'
  rw [key (fun B => B.shade) fun _ _ => Translation.volume_actShadedTube_shade _ _,
    key (fun B => B.carrier) fun _ _ => Translation.volume_actShadedTube_carrier _ _,
    ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hJ_pos.ne') (ENNReal.natCast_ne_top _)]

set_option maxHeartbeats 20000 in
-- The multiplicity comparison requires several finite-sum and ENNReal-to-real conversions.
/-- Product translation does not decrease the multiplicity of a shaded tube family. -/
private lemma multiplicity_le_under_product_translation
    {Ω : Type*} [MeasurableSpace Ω] [HasUniformTranslation Ω E]
    {δ : NNReal}
    {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E)
    (J : ℕ) (hJ_pos : 0 < J)
    (ω : Fin J → Ω) :
    ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      ShadedBody.multiplicity (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
            (T p.1)).toShadedBody) := by
  set V : ι → ShadedBody E := fun i => (T i).toShadedBody with hV_def
  set V' : (ι × Fin J) → ShadedBody E :=
    fun p => ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
      (T p.1)).toShadedBody with hV'_def
  have hcard : (Finset.univ : Finset (Fin J)).card = J := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hJ_pos_real : (0 : ℝ) < (J : ℝ) := Nat.cast_pos.mpr hJ_pos
  have hnum :
      ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume.real (V' p).shade =
        (J : ℝ) * ∑ i ∈ s, volume.real (V i).shade := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∀ j, volume.real (V' (i, j)).shade = volume.real (V i).shade :=
      fun j => by
        change (volume (V' (i, j)).shade).toReal = (volume (V i).shade).toReal
        exact congrArg ENNReal.toReal
          (Translation.volume_actShadedTube_shade _ _)
    simp_rw [h1]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hfin_un : volume (⋃ i ∈ s, (V i).shade) ≠ ⊤ := by
    have hsubset : (⋃ i ∈ s, (V i).shade) ⊆ ⋃ i ∈ s, (V i).carrier :=
      Set.iUnion₂_mono fun i _ => (V i).shade_subset
    have hcompact : IsCompact (⋃ i ∈ s, (V i).carrier) :=
      s.isCompact_biUnion fun i _ => (V i).isCompact'
    exact ne_top_of_le_ne_top hcompact.measure_lt_top.ne
      (MeasureTheory.measure_mono hsubset)
  have hsubset_union : (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ⊆
      ⋃ j ∈ (Finset.univ : Finset (Fin J)),
        HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) '' (⋃ i ∈ s, (V i).shade) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.mpr ⟨p.2, Finset.mem_univ _, ?_⟩
    have hxp' : x ∈ HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2) '' (V p.1).shade := by
      change x ∈ ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
          (T p.1)).shade at hxp
      rw [Translation.actShadedTube_shade] at hxp
      exact hxp
    rcases hxp' with ⟨y, hy, hxy⟩
    exact ⟨y, Set.mem_iUnion₂.mpr ⟨p.1, (Finset.mem_product.mp hp).1, hy⟩, hxy⟩
  have hden_le_meas :
      volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ≤
        (J : ENNReal) * volume (⋃ i ∈ s, (V i).shade) := by
    have h1 : volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ≤
        volume (⋃ j ∈ (Finset.univ : Finset (Fin J)),
          HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) '' (⋃ i ∈ s, (V i).shade)) :=
      MeasureTheory.measure_mono hsubset_union
    have hsub :
        volume (⋃ j ∈ (Finset.univ : Finset (Fin J)),
            HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) '' (⋃ i ∈ s, (V i).shade)) ≤
          ∑ j ∈ (Finset.univ : Finset (Fin J)),
            volume (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) ''
              (⋃ i ∈ s, (V i).shade)) :=
      MeasureTheory.measure_biUnion_finset_le (Finset.univ : Finset (Fin J)) _
    have heq_each : ∀ j : Fin J,
        volume (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) '' (⋃ i ∈ s, (V i).shade)) =
          volume (⋃ i ∈ s, (V i).shade) :=
      fun j => Translation.volume_image_eq _ _
    simp_rw [heq_each] at hsub
    rw [Finset.sum_const, hcard] at hsub
    have hsub' : volume (⋃ j ∈ (Finset.univ : Finset (Fin J)),
            HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) '' (⋃ i ∈ s, (V i).shade)) ≤
          (J : ENNReal) * volume (⋃ i ∈ s, (V i).shade) := by
      simpa [nsmul_eq_mul] using hsub
    exact le_trans h1 hsub'
  have hden_le :
      volume.real (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ≤
        (J : ℝ) * volume.real (⋃ i ∈ s, (V i).shade) := by
    unfold MeasureTheory.Measure.real
    have hRHS_ne_top : (J : ENNReal) * volume (⋃ i ∈ s, (V i).shade) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hfin_un
    have h := ENNReal.toReal_mono hRHS_ne_top hden_le_meas
    rw [ENNReal.toReal_mul] at h
    have hJtoReal : ((J : ENNReal)).toReal = (J : ℝ) := by simp
    rw [hJtoReal] at h
    exact h
  set A : ℝ := ∑ i ∈ s, volume.real (V i).shade with hA_def
  set B : ℝ := volume.real (⋃ i ∈ s, (V i).shade) with hB_def
  set B' : ℝ := volume.real (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade)
    with hB'_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hB_nn : 0 ≤ B := ENNReal.toReal_nonneg
  have hB'_nn : 0 ≤ B' := ENNReal.toReal_nonneg
  have hA_le_cardB : A ≤ s.card * B := by
    have hfin : ∀ i ∈ s, volume (V i).shade ≠ ⊤ := by
      intro i _
      exact ne_top_of_le_ne_top (V i).isCompact'.measure_lt_top.ne
        (MeasureTheory.measure_mono (V i).shade_subset)
    have h_le : ∀ i ∈ s, volume (V i).shade ≤ volume (⋃ j ∈ s, (V j).shade) := by
      intro i hi
      exact MeasureTheory.measure_mono fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
    simp only [hA_def, hB_def]
    unfold MeasureTheory.Measure.real
    rw [← ENNReal.toReal_sum hfin]
    have : ∑ i ∈ s, volume (V i).shade ≤ s.card * volume (⋃ j ∈ s, (V j).shade) := by
      calc ∑ i ∈ s, volume (V i).shade
          ≤ ∑ _ ∈ s, volume (⋃ j ∈ s, (V j).shade) := Finset.sum_le_sum h_le
        _ = s.card * volume (⋃ j ∈ s, (V j).shade) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have h_top : (s.card : ENNReal) * volume (⋃ j ∈ s, (V j).shade) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hfin_un
    have htoReal := ENNReal.toReal_mono h_top this
    rw [ENNReal.toReal_mul] at htoReal
    have hcardtoReal : ((s.card : ENNReal)).toReal = (s.card : ℝ) := by simp
    rw [hcardtoReal] at htoReal
    exact htoReal
  have hfin_un' : volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ≠ ⊤ := by
    have hsubset : (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ⊆
        ⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).carrier :=
      Set.iUnion₂_mono fun p _ => (V' p).shade_subset
    have hcompact : IsCompact
        (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).carrier) :=
      (s ×ˢ Finset.univ).isCompact_biUnion fun p _ => (V' p).isCompact'
    exact ne_top_of_le_ne_top hcompact.measure_lt_top.ne
      (MeasureTheory.measure_mono hsubset)
  have hfin_sumS : ∑ i ∈ s, volume (V i).shade ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun i _ => ?_
    exact ne_top_of_le_ne_top (V i).isCompact'.measure_lt_top.ne
      (MeasureTheory.measure_mono (V i).shade_subset)
  have hfin_sumS' : ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (V' p).shade ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun p _ => ?_
    exact ne_top_of_le_ne_top (V' p).isCompact'.measure_lt_top.ne
      (MeasureTheory.measure_mono (V' p).shade_subset)
  have h_real : A / B ≤ (J : ℝ) * A / B' := by
    by_cases hB_zero : B = 0
    · have hA_zero : A = 0 := le_antisymm (by rw [hB_zero] at hA_le_cardB; linarith) hA_nn
      rw [hA_zero]; simp
    · have hB_pos : 0 < B := lt_of_le_of_ne hB_nn (Ne.symm hB_zero)
      by_cases hB'_zero : B' = 0
      · have hB'_meas_zero :
            volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) = 0 := by
          by_contra h
          have : 0 < B' := ENNReal.toReal_pos h hfin_un'
          linarith
        have h_each_zero : ∀ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)),
            volume.real (V' p).shade = 0 := by
          intro p hp
          have hsubset : (V' p).shade ⊆
              ⋃ q ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' q).shade :=
            fun x hx => Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩
          have : volume (V' p).shade = 0 :=
            MeasureTheory.measure_mono_null hsubset hB'_meas_zero
          unfold MeasureTheory.Measure.real
          rw [this]; simp
        have hsum_zero : ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)),
            volume.real (V' p).shade = 0 := Finset.sum_eq_zero h_each_zero
        rw [hnum] at hsum_zero
        have hA_zero : A = 0 := by
          rcases mul_eq_zero.mp hsum_zero with h | h
          · exact absurd h (Nat.cast_ne_zero.mpr hJ_pos.ne')
          · exact h
        rw [hA_zero]; simp
      · have hB'_pos : 0 < B' := lt_of_le_of_ne hB'_nn (Ne.symm hB'_zero)
        rw [div_le_div_iff₀ hB_pos hB'_pos]
        calc A * B' ≤ A * ((J : ℝ) * B) :=
                mul_le_mul_of_nonneg_left hden_le hA_nn
          _ = (J : ℝ) * A * B := by ring
  change (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade) ≤
    (∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (V' p).shade) /
      volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade)
  have hLHS_ne_top : (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade) ≠ ⊤ := by
    by_cases hB : volume (⋃ i ∈ s, (V i).shade) = 0
    · have hsum_zero : ∑ i ∈ s, volume (V i).shade = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hsub : (V i).shade ⊆ ⋃ j ∈ s, (V j).shade :=
          fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
        exact MeasureTheory.measure_mono_null hsub hB
      simp [hsum_zero]
    · exact ENNReal.div_ne_top hfin_sumS hB
  have hRHS_ne_top :
      (∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (V' p).shade) /
        volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) ≠ ⊤ := by
    by_cases hB' : volume (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) = 0
    · have hsum_zero : ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (V' p).shade = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hsub : (V' p).shade ⊆
            ⋃ q ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' q).shade :=
          fun x hx => Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩
        exact MeasureTheory.measure_mono_null hsub hB'
      simp [hsum_zero]
    · exact ENNReal.div_ne_top hfin_sumS' hB'
  rw [← ENNReal.toReal_le_toReal hLHS_ne_top hRHS_ne_top]
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  rw [ENNReal.toReal_sum (fun i _ => ne_top_of_le_ne_top (V i).isCompact'.measure_lt_top.ne
        (MeasureTheory.measure_mono (V i).shade_subset))]
  rw [ENNReal.toReal_sum (fun p _ => ne_top_of_le_ne_top (V' p).isCompact'.measure_lt_top.ne
        (MeasureTheory.measure_mono (V' p).shade_subset))]
  change (∑ i ∈ s, volume.real (V i).shade) / volume.real (⋃ i ∈ s, (V i).shade) ≤
    (∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume.real (V' p).shade) /
      volume.real (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade)
  rw [show (∑ i ∈ s, volume.real (V i).shade) = A from rfl,
      show volume.real (⋃ i ∈ s, (V i).shade) = B from rfl,
      show volume.real (⋃ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), (V' p).shade) = B' from rfl,
      hnum]
  exact h_real

set_option maxHeartbeats 2500 in
-- Normalizing the Frostman constants through ENNReal multiplication needs a tight local budget.
/-- Converts density bounds on a finite test net into a Frostman bound for the family. -/
private lemma frostman_of_per_K_hitcount_chernoff
    [ProperSpace E]
    {δ : NNReal} (_hδ_pos : 0 < (δ : ℝ)) (_hδ_lt_one : (δ : ℝ) < 1)
    {η : ℝ} (_hη : 0 < η)
    {ι' : Type v} (s' : Finset ι')
    (T' : ι' → ShadedTube δ E)
    (_hT'_ball : ∀ i ∈ s', (T' i).carrier ⊆ Metric.closedBall (0 : E) 2)
    (NetF : Finset (ConvexSpaceBody E))
    (C_cover : ℝ) (_hC_cover_pos : 0 < C_cover)
    (_hNetF_cover :
      ∀ K' : ConvexSpaceBody E,
        K' ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) →
        ∃ K ∈ NetF,
          K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) ∧
          densityIn s' (fun i ↦ (T' i).toConvexSpaceBody) K'
            ≤ ENNReal.ofReal C_cover * densityIn s' (fun i ↦ (T' i).toConvexSpaceBody) K)
    (_hHitCount :
      ∀ K ∈ NetF,
        densityIn s' (fun i ↦ (T' i).toConvexSpaceBody) K
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
            densityIn s' (fun i ↦ (T' i).toConvexSpaceBody)
              (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)))) :
    ConvexSpaceBody.IsFrostmanIn s' (fun i ↦ (T' i).toConvexSpaceBody)
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
  intro K' hK'
  obtain ⟨K, hK_mem, -, hcov⟩ := _hNetF_cover K' hK'
  have hC_ne : C_cover ≠ 0 := _hC_cover_pos.ne'
  calc densityIn s' (fun i ↦ (T' i).toConvexSpaceBody) K'
      ≤ ENNReal.ofReal C_cover * densityIn s' (fun i ↦ (T' i).toConvexSpaceBody) K := hcov
    _ ≤ ENNReal.ofReal C_cover *
          (ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
            densityIn s' (fun i ↦ (T' i).toConvexSpaceBody)
              (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)))) :=
        mul_le_mul_right (_hHitCount K hK_mem) _
    _ = ENNReal.ofReal ((δ : ℝ) ^ (-η)) *
          densityIn s' (fun i ↦ (T' i).toConvexSpaceBody)
            (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul _hC_cover_pos.le,
          mul_div_cancel₀ _ hC_ne]

set_option maxHeartbeats 20000 in
-- The eventual-bound calculation unfolds several asymptotic estimates and nonlinear identities.
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Eventually bounds the residual polylogarithmic term by `δ ^ (-η)`. -/
private lemma randCF_residual_envelope
    (_hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    {CF : ℝ} (hCF : 1 ≤ CF)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol)
    (uc : ℝ) (_huc_pos : 0 < uc)
    (C_cover_env : ℝ) (hC_cover_env_pos : 0 < C_cover_env)
    (vol_B1 vol_B2 : ℝ) (hvol_B1_pos : 0 < vol_B1) (hvol_B2_pos : 0 < vol_B2) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) *
          (max (uc * (⌈CF⌉₊ : ℝ))
            (CF * M_vol / (c_vol * vol_B1)) + 1) *
          vol_B2 * M_vol * C_cover_env
        < δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol := by
  set Mgeom : ℝ := netGeomConstantM E with hMgeom_def
  have hMgeom_pos : 0 < Mgeom := netGeomConstantM_pos E
  have hCF_pos : 0 < CF := lt_of_lt_of_le one_pos hCF
  have hCFceil_pos : 0 < (⌈CF⌉₊ : ℝ) := by
    have h : 0 < ⌈CF⌉₊ := Nat.ceil_pos.mpr hCF_pos
    exact_mod_cast h
  set L : ℝ :=
      (max (uc * (⌈CF⌉₊ : ℝ))
          (CF * M_vol / (c_vol * vol_B1)) + 1) *
        vol_B2 * M_vol * C_cover_env with hL_def
  have hCpack_nn :
      0 ≤ CF * M_vol / (c_vol * vol_B1) := by
    apply div_nonneg
    · exact mul_nonneg hCF_pos.le hM_vol_pos.le
    · exact (mul_pos hc_vol_pos hvol_B1_pos).le
  have hmax_nn :
      0 ≤ max (uc * (⌈CF⌉₊ : ℝ))
            (CF * M_vol / (c_vol * vol_B1)) :=
    le_max_of_le_right hCpack_nn
  have hL_pos : 0 < L := by
    change 0 <
      (max (uc * (⌈CF⌉₊ : ℝ))
          (CF * M_vol / (c_vol * vol_B1)) + 1) *
        vol_B2 * M_vol * C_cover_env
    have h1 :
        0 < max (uc * (⌈CF⌉₊ : ℝ))
              (CF * M_vol / (c_vol * vol_B1)) + 1 := by linarith
    positivity
  set R : ℝ := (⌈CF⌉₊ : ℝ) * c_vol with hR_def
  have hR_pos : 0 < R := mul_pos hCFceil_pos hc_vol_pos
  have h_rpow_neg_eta : Tendsto (fun δ : ℝ => δ ^ (-η)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη)
  have h_log_littleO_eta :
      (fun δ : ℝ => |Real.log δ| ^ (1 : ℝ)) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-η)) :=
    isLittleO_abs_log_rpow_rpow_nhdsGT_zero (1 : ℝ) (neg_neg_iff_pos.mpr hη)
  have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
    eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
  set B : ℝ := Mgeom * L with hB_def
  have hB_pos : 0 < B := mul_pos hMgeom_pos hL_pos
  have hB_nonneg : 0 ≤ B := hB_pos.le
  have hA_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0, L ≤ (1/2) * R * δ ^ (-η) := by
    have htend : Tendsto (fun δ : ℝ => (1/2) * R * δ ^ (-η)) (𝓝[>] 0) atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < (1/2) * R) h_rpow_neg_eta
    exact htend.eventually_ge_atTop L
  have hB_log_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      B * Real.log (1 / δ) ≤ (1/2) * R * δ ^ (-η) := by
    have hlittle : (fun δ : ℝ => |Real.log δ|) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-η)) := by
      have := h_log_littleO_eta
      simpa [Real.rpow_one] using this
    have hε : 0 < R / (2 * (B + 1)) := by
      apply div_pos hR_pos
      linarith
    have h_eventually_abs : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        ‖|Real.log δ|‖ ≤ (R / (2 * (B + 1))) * ‖δ ^ (-η)‖ :=
      hlittle.def hε
    filter_upwards [h_eventually_abs, h_in_unit] with δ h1 hδmem
    obtain ⟨hδpos, hδlt1⟩ := hδmem
    have hpow_nonneg : 0 ≤ δ ^ (-η) := Real.rpow_nonneg hδpos.le _
    have hpow_abs : ‖δ ^ (-η)‖ = δ ^ (-η) := Real.norm_of_nonneg hpow_nonneg
    have habs_abs : ‖|Real.log δ|‖ = |Real.log δ| := by
      rw [Real.norm_eq_abs, abs_abs]
    rw [hpow_abs, habs_abs] at h1
    have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub]
    have hlogδ_neg : Real.log δ < 0 := Real.log_neg hδpos hδlt1
    have habs_eq : |Real.log δ| = -Real.log δ := abs_of_neg hlogδ_neg
    have hlog_inv_eq : Real.log (1 / δ) = |Real.log δ| := by rw [hlog_eq, habs_eq]
    rw [hlog_inv_eq]
    have hBp1_pos : 0 < B + 1 := by linarith
    calc B * |Real.log δ|
        ≤ (B + 1) * |Real.log δ| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (B + 1) * ((R / (2 * (B + 1))) * δ ^ (-η)) :=
          mul_le_mul_of_nonneg_left h1 hBp1_pos.le
      _ = ((B + 1) * (R / (2 * (B + 1)))) * δ ^ (-η) := by ring
      _ = (1/2) * R * δ ^ (-η) := by
          have h2ne : (2 * (B + 1)) ≠ 0 := by
            have : 0 < 2 * (B + 1) := by linarith
            exact this.ne'
          field_simp
  filter_upwards [hA_eventually, hB_log_eventually, h_in_unit]
    with δ hAev hBlog hδmem
  obtain ⟨hδpos, hδlt1⟩ := hδmem
  have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
    rw [show (1 : ℝ) / δ = δ⁻¹ from one_div δ, Real.log_inv]
    have : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδlt1.le
    linarith
  have hMgeom_log_nn : 0 ≤ Mgeom * Real.log (1 / δ) :=
    mul_nonneg hMgeom_pos.le hlog_nonneg
  have hceil_strict : (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) <
      Mgeom * Real.log (1 / δ) + 1 :=
    Nat.ceil_lt_add_one hMgeom_log_nn
  have hLHS_lt :
      (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) * L
        < (Mgeom * Real.log (1 / δ) + 1) * L :=
    (mul_lt_mul_of_pos_right hceil_strict hL_pos)
  have hexpand :
      (Mgeom * Real.log (1 / δ) + 1) * L = L + B * Real.log (1 / δ) := by
    change (Mgeom * Real.log (1 / δ) + 1) * L = L + (Mgeom * L) * Real.log (1 / δ)
    ring
  rw [hexpand] at hLHS_lt
  have hAB_le : L + B * Real.log (1 / δ) ≤ R * δ ^ (-η) := by
    have hsum : (1/2) * R * δ ^ (-η) + (1/2) * R * δ ^ (-η) = R * δ ^ (-η) := by ring
    linarith
  have hgoal_pre : (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) * L < R * δ ^ (-η) :=
    lt_of_lt_of_le hLHS_lt hAB_le
  change (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) *
        (max (uc * (⌈CF⌉₊ : ℝ))
          (CF * M_vol / (c_vol * vol_B1)) + 1) *
        vol_B2 * M_vol * C_cover_env
      < δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol
  have hMgeom_eq : netGeomConstantM E = Mgeom := rfl
  rw [hMgeom_eq]
  have hLHS_eq :
      (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) *
        (max (uc * (⌈CF⌉₊ : ℝ))
          (CF * M_vol / (c_vol * vol_B1)) + 1) *
        vol_B2 * M_vol * C_cover_env
      = (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) * L := by
    change (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) *
        (max (uc * (⌈CF⌉₊ : ℝ))
          (CF * M_vol / (c_vol * vol_B1)) + 1) *
        vol_B2 * M_vol * C_cover_env
      = (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) *
          ((max (uc * (⌈CF⌉₊ : ℝ))
            (CF * M_vol / (c_vol * vol_B1)) + 1) *
          vol_B2 * M_vol * C_cover_env)
    ring
  rw [hLHS_eq]
  have hRHS_eq :
      δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol = δ ^ (-η) * R := by
    change δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol = δ ^ (-η) * ((⌈CF⌉₊ : ℝ) * c_vol)
    ring
  rw [hRHS_eq]
  have hcomm : R * δ ^ (-η) = δ ^ (-η) * R := by ring
  linarith

set_option maxHeartbeats 80000 in
-- Combining the independent eventual smallness estimates is expensive but isolated to this lemma.
/-- Bundles the eventual smallness estimates required by the `randCF` argument. -/
private lemma randCF_smallness_envelope
    (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    {CF : ℝ} (hCF : 1 ≤ CF)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol)
    (C_pack_ext : ℕ) (_hC_pack_ext_pos : 0 < C_pack_ext)
    (M_ED : ℕ) (_hM_ED_pos : 0 < M_ED)
    (_hM_ED_ge_JC_pack : ⌈CF⌉₊ * C_pack_ext < M_ED) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      Real.exp 11
          + max ((netGeomConstantC E) * M_vol * CF / c_vol) 1
              * 2 ^ Module.finrank ℝ E
          + ((netGeomConstantM E) + (Module.finrank ℝ E : ℝ)) * Real.log (1 / δ)
            ≤ δ ^ (-(η / 2)) ∧
      δ ≤ c_vol ∧
      (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF
            * (2 ^ Module.finrank ℝ E)
          ≤ δ ^ (-η) ∧
      M_vol * δ ^ (Module.finrank ℝ E - 1) *
          (2 ^ Module.finrank ℝ E *
            volume.real (Metric.closedBall (0 : E) 1))
          * 2 * netGeomConstantC E
          ≤ δ ^ (-η) * (c_vol * δ ^ (Module.finrank ℝ E - 1)) *
              (1 / (2 * (⌈CF⌉₊ : ℝ) *
                (volume.real (Metric.closedBall (0 : E) 1))⁻¹)) ∧
      2 * netGeomConstantC E * δ ^ Module.finrank ℝ E ≤
          1 / (2 * (⌈CF⌉₊ : ℝ) *
            (volume.real (Metric.closedBall (0 : E) 1))⁻¹) ∧
      ((max M_ED C_pack_ext : ℕ) : ℝ) *
          (((max M_ED C_pack_ext : ℕ) : ℝ) +
           (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) +
           (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
        ≤ δ ^ (-η) ∧
      netGeomConstantC E * Real.exp (10 * Real.exp 1) *
          δ ^ (netGeomConstantM E - netGeomConstantMRaw E)
        ≤ 1/3 := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Cgeom : ℝ := netGeomConstantC E with hCgeom_def
  set Mgeom : ℝ := netGeomConstantM E with hMgeom_def
  set volB : ℝ := volume.real (Metric.closedBall (0 : E) 1) with hvolB_def
  have hCgeom_pos : 0 < Cgeom := netGeomConstantC_pos E
  have hMgeom_pos : 0 < Mgeom := netGeomConstantM_pos E
  have hvolB_pos : 0 < volB := by
    refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
    exact (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hη2_pos : 0 < η / 2 := by positivity
  have h_rpow_neg_eta : Tendsto (fun δ : ℝ => δ ^ (-η)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη)
  have h_rpow_neg_eta_half : Tendsto (fun δ : ℝ => δ ^ (-(η / 2))) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη2_pos)
  have h_log_littleO_eta_half :
      (fun δ : ℝ => |Real.log δ| ^ (1 : ℝ)) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-(η / 2))) :=
    isLittleO_abs_log_rpow_rpow_nhdsGT_zero (1 : ℝ) (neg_neg_iff_pos.mpr hη2_pos)
  have h_log_littleO_eta :
      (fun δ : ℝ => |Real.log δ| ^ (1 : ℝ)) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-η)) :=
    isLittleO_abs_log_rpow_rpow_nhdsGT_zero (1 : ℝ) (neg_neg_iff_pos.mpr hη)
  have h_conj1 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Real.exp 11
        + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n
        + (Mgeom + (n : ℝ)) * Real.log (1 / δ)
        ≤ δ ^ (-(η / 2)) := by
    set A : ℝ := Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n with hA_def
    set B : ℝ := Mgeom + (n : ℝ) with hB_def
    have hA_nonneg : 0 ≤ A := by
      change 0 ≤ Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n
      have h1 : 0 ≤ Real.exp 11 := (Real.exp_pos 11).le
      have h2 : 0 ≤ max (Cgeom * M_vol * CF / c_vol) 1 :=
        le_max_of_le_right (by norm_num : (0 : ℝ) ≤ 1)
      have h3 : 0 ≤ (2 : ℝ) ^ n := by positivity
      have h4 : 0 ≤ max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n := mul_nonneg h2 h3
      linarith
    have hB_nonneg : 0 ≤ B := by
      change 0 ≤ Mgeom + (n : ℝ)
      have : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith [hMgeom_pos.le]
    have hA_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        A ≤ (1/2) * δ ^ (-(η / 2)) := by
      have htend : Tendsto (fun δ : ℝ => (1/2) * δ ^ (-(η / 2)))
          (𝓝[>] 0) atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2) h_rpow_neg_eta_half
      exact htend.eventually_ge_atTop A
    have hB_log_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        B * Real.log (1 / δ) ≤ (1/2) * δ ^ (-(η / 2)) := by
      have hlittle : (fun δ : ℝ => |Real.log δ|) =o[𝓝[>] 0]
          (fun δ : ℝ => δ ^ (-(η / 2))) := by
        have := h_log_littleO_eta_half
        simpa [Real.rpow_one] using this
      have hε : 0 < (1 : ℝ) / (2 * (B + 1)) := by
        apply div_pos one_pos
        linarith [hB_nonneg]
      have h_eventually_abs : ∀ᶠ δ : ℝ in 𝓝[>] 0,
          ‖|Real.log δ|‖ ≤ (1 / (2 * (B + 1))) * ‖δ ^ (-(η / 2))‖ :=
        hlittle.def hε
      have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ < 1 := by
        have h_mem : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
          eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
        exact h_mem.mono fun δ hδ => ⟨hδ.1, hδ.2⟩
      filter_upwards [h_eventually_abs, h_in_unit] with δ h1 h2
      obtain ⟨hδpos, hδlt1⟩ := h2
      have hpow_nonneg : 0 ≤ δ ^ (-(η / 2)) := Real.rpow_nonneg hδpos.le _
      have hpow_abs : ‖δ ^ (-(η / 2))‖ = δ ^ (-(η / 2)) :=
        Real.norm_of_nonneg hpow_nonneg
      have habs_abs : ‖|Real.log δ|‖ = |Real.log δ| := by
        rw [Real.norm_eq_abs, abs_abs]
      rw [hpow_abs, habs_abs] at h1
      have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub]
      have hlogδ_neg : Real.log δ < 0 := Real.log_neg hδpos hδlt1
      have habs_eq : |Real.log δ| = -Real.log δ := abs_of_neg hlogδ_neg
      have hlog_inv_eq : Real.log (1 / δ) = |Real.log δ| := by rw [hlog_eq, habs_eq]
      rw [hlog_inv_eq]
      have hBp1_pos : 0 < B + 1 := by linarith [hB_nonneg]
      calc B * |Real.log δ|
          ≤ (B + 1) * |Real.log δ| := by
            have : B ≤ B + 1 := by linarith
            exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ ≤ (B + 1) * ((1 / (2 * (B + 1))) * δ ^ (-(η / 2))) :=
            mul_le_mul_of_nonneg_left h1 hBp1_pos.le
        _ = ((B + 1) * (1 / (2 * (B + 1)))) * δ ^ (-(η / 2)) := by ring
        _ = (1 / 2) * δ ^ (-(η / 2)) := by congr 1; field_simp
    filter_upwards [hA_eventually, hB_log_eventually] with δ hA hBlog
    change Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n
          + (Mgeom + (n : ℝ)) * Real.log (1 / δ) ≤ δ ^ (-(η / 2))
    have hLHS_eq : Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n
          + (Mgeom + (n : ℝ)) * Real.log (1 / δ) = A + B * Real.log (1 / δ) := by
      change Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n
          + (Mgeom + (n : ℝ)) * Real.log (1 / δ)
            = (Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n)
              + (Mgeom + (n : ℝ)) * Real.log (1 / δ)
      ring
    rw [hLHS_eq]
    linarith
  have h_conj2 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ c_vol := by
    have h_mem : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) c_vol :=
      eventually_mem_set.mpr (Ioo_mem_nhdsGT hc_vol_pos)
    exact h_mem.mono fun δ hδ => hδ.2.le
  have h_conj3 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF * (2 ^ n)
        ≤ δ ^ (-η) := by
    set K3 : ℝ := (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF * (2 ^ n)
    exact h_rpow_neg_eta.eventually_ge_atTop K3
  have h_conj4 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      M_vol * δ ^ (n - 1) * (2 ^ n * volB) * 2 * Cgeom
        ≤ δ ^ (-η) * (c_vol * δ ^ (n - 1)) *
            (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹)) := by
    have hCF_pos : 0 < CF := lt_of_lt_of_le one_pos hCF
    have hCFceil_pos : 0 < (⌈CF⌉₊ : ℝ) := by
      have h : 0 < ⌈CF⌉₊ := Nat.ceil_pos.mpr hCF_pos
      exact_mod_cast h
    set L : ℝ := M_vol * (2 ^ n * volB) * 2 * Cgeom with hL_def
    have hL_pos : 0 < L := by
      change 0 < M_vol * (2 ^ n * volB) * 2 * Cgeom
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      positivity
    set R : ℝ := c_vol * (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹)) with hR_def
    have hR_pos : 0 < R := by
      change 0 < c_vol * (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹))
      have hvolBinv_pos : 0 < volB⁻¹ := inv_pos.mpr hvolB_pos
      have hfrac : 0 < 1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹) := by positivity
      exact mul_pos hc_vol_pos hfrac
    have h_const_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0, L ≤ R * δ ^ (-η) := by
      have htend : Tendsto (fun δ : ℝ => R * δ ^ (-η)) (𝓝[>] 0) atTop :=
        Filter.Tendsto.const_mul_atTop hR_pos h_rpow_neg_eta
      exact htend.eventually_ge_atTop L
    have h_pos_mem : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
    filter_upwards [h_const_eventually, h_pos_mem] with δ hLR hδpos
    have hδpow_nonneg : 0 ≤ δ ^ (n - 1) := pow_nonneg hδpos.le _
    have hLHS_eq : M_vol * δ ^ (n - 1) * (2 ^ n * volB) * 2 * Cgeom
        = L * δ ^ (n - 1) := by
      change M_vol * δ ^ (n - 1) * (2 ^ n * volB) * 2 * Cgeom
            = (M_vol * (2 ^ n * volB) * 2 * Cgeom) * δ ^ (n - 1)
      ring
    have hRHS_eq : δ ^ (-η) * (c_vol * δ ^ (n - 1)) *
          (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹))
        = R * δ ^ (-η) * δ ^ (n - 1) := by
      change δ ^ (-η) * (c_vol * δ ^ (n - 1)) *
            (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹))
          = (c_vol * (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹))) * δ ^ (-η) * δ ^ (n - 1)
      ring
    rw [hLHS_eq, hRHS_eq]
    exact mul_le_mul_of_nonneg_right hLR hδpow_nonneg
  have h_conj5 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      2 * Cgeom * δ ^ n ≤ 1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹) := by
    have hCF_pos : 0 < CF := lt_of_lt_of_le one_pos hCF
    have hCFceil_pos : 0 < (⌈CF⌉₊ : ℝ) := by
      have h : 0 < ⌈CF⌉₊ := Nat.ceil_pos.mpr hCF_pos
      exact_mod_cast h
    have hvolBinv_pos : 0 < volB⁻¹ := inv_pos.mpr hvolB_pos
    have hRconst : 0 < 1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹) := by positivity
    have hn_pos : 0 < n := lt_trans one_pos hn
    have h_tend_pow : Tendsto (fun δ : ℝ => 2 * Cgeom * δ ^ n) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun δ : ℝ => δ ^ n) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun δ : ℝ => δ ^ n) (𝓝 (0 : ℝ)) (𝓝 (0 ^ n : ℝ)) :=
          (continuous_pow n).tendsto 0
        rw [show ((0 : ℝ) ^ n) = 0 from zero_pow hn_pos.ne'] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun δ : ℝ => 2 * Cgeom * δ ^ n) (𝓝[>] 0)
          (𝓝 (2 * Cgeom * 0)) := h1.const_mul (2 * Cgeom)
      simpa using h2
    exact (h_tend_pow.eventually (eventually_lt_nhds hRconst)).mono fun _ h => h.le
  have h_conj6 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ((max M_ED C_pack_ext : ℕ) : ℝ) *
        (((max M_ED C_pack_ext : ℕ) : ℝ) +
          (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) +
          (⌈10 * Real.exp 1 + Real.log (3 * Cgeom)⌉₊ : ℝ) + 1) + 1
        ≤ δ ^ (-η) := by
    set M : ℝ := ((max M_ED C_pack_ext : ℕ) : ℝ) with hM_def
    set C0 : ℝ := (⌈10 * Real.exp 1 + Real.log (3 * Cgeom)⌉₊ : ℝ) with hC0_def
    have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
    have hC0_nonneg : 0 ≤ C0 := Nat.cast_nonneg _
    have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
      eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
    set A : ℝ := M * (M + C0 + 2) + 1 with hA_def
    set B : ℝ := M * Mgeom with hB_def
    have hA_nonneg : 0 ≤ A := by
      change 0 ≤ M * (M + C0 + 2) + 1
      have h1 : 0 ≤ M + C0 + 2 := by linarith
      have h2 : 0 ≤ M * (M + C0 + 2) := mul_nonneg hM_nonneg h1
      linarith
    have hB_nonneg : 0 ≤ B := mul_nonneg hM_nonneg hMgeom_pos.le
    have hA_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0, A ≤ (1/2) * δ ^ (-η) := by
      have htend : Tendsto (fun δ : ℝ => (1/2) * δ ^ (-η)) (𝓝[>] 0) atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2) h_rpow_neg_eta
      exact htend.eventually_ge_atTop A
    have hB_log_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        B * Real.log (1 / δ) ≤ (1/2) * δ ^ (-η) := by
      have hlittle : (fun δ : ℝ => |Real.log δ|) =o[𝓝[>] 0]
          (fun δ : ℝ => δ ^ (-η)) := by
        have := h_log_littleO_eta
        simpa [Real.rpow_one] using this
      have hε : 0 < (1 : ℝ) / (2 * (B + 1)) := by
        apply div_pos one_pos
        linarith [hB_nonneg]
      have h_eventually_abs : ∀ᶠ δ : ℝ in 𝓝[>] 0,
          ‖|Real.log δ|‖ ≤ (1 / (2 * (B + 1))) * ‖δ ^ (-η)‖ :=
        hlittle.def hε
      filter_upwards [h_eventually_abs, h_in_unit] with δ h1 hδmem
      obtain ⟨hδpos, hδlt1⟩ := hδmem
      have hpow_nonneg : 0 ≤ δ ^ (-η) := Real.rpow_nonneg hδpos.le _
      have hpow_abs : ‖δ ^ (-η)‖ = δ ^ (-η) := Real.norm_of_nonneg hpow_nonneg
      have habs_abs : ‖|Real.log δ|‖ = |Real.log δ| := by
        rw [Real.norm_eq_abs, abs_abs]
      rw [hpow_abs, habs_abs] at h1
      have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
        rw [Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub]
      have hlogδ_neg : Real.log δ < 0 := Real.log_neg hδpos hδlt1
      have habs_eq : |Real.log δ| = -Real.log δ := abs_of_neg hlogδ_neg
      have hlog_inv_eq : Real.log (1 / δ) = |Real.log δ| := by rw [hlog_eq, habs_eq]
      rw [hlog_inv_eq]
      have hBp1_pos : 0 < B + 1 := by linarith [hB_nonneg]
      calc B * |Real.log δ|
          ≤ (B + 1) * |Real.log δ| := by
            have : B ≤ B + 1 := by linarith
            exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ ≤ (B + 1) * ((1 / (2 * (B + 1))) * δ ^ (-η)) :=
            mul_le_mul_of_nonneg_left h1 hBp1_pos.le
        _ = ((B + 1) * (1 / (2 * (B + 1)))) * δ ^ (-η) := by ring
        _ = (1 / 2) * δ ^ (-η) := by congr 1; field_simp
    filter_upwards [hA_eventually, hB_log_eventually, h_in_unit] with δ hA hBlog hδmem
    obtain ⟨hδpos, hδlt1⟩ := hδmem
    have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
      rw [show (1 : ℝ) / δ = δ⁻¹ from one_div δ]
      rw [Real.log_inv]
      have : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδlt1.le
      linarith
    have hMgeom_log_nonneg : 0 ≤ Mgeom * Real.log (1 / δ) :=
      mul_nonneg hMgeom_pos.le hlog_nonneg
    have hceil_bound : (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) ≤
        Mgeom * Real.log (1 / δ) + 1 := by
      have := Nat.ceil_lt_add_one hMgeom_log_nonneg
      linarith
    have hLHS_bound :
        M * (M + (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) + C0 + 1) + 1
          ≤ A + B * Real.log (1 / δ) := by
      have step1 : M + (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) + C0 + 1
          ≤ M + (Mgeom * Real.log (1 / δ) + 1) + C0 + 1 := by linarith
      have step2 : M * (M + (⌈Mgeom * Real.log (1 / δ)⌉₊ : ℝ) + C0 + 1)
          ≤ M * (M + (Mgeom * Real.log (1 / δ) + 1) + C0 + 1) :=
        mul_le_mul_of_nonneg_left step1 hM_nonneg
      have step3 : M * (M + (Mgeom * Real.log (1 / δ) + 1) + C0 + 1) + 1
          = A + B * Real.log (1 / δ) := by
        change M * (M + (Mgeom * Real.log (1 / δ) + 1) + C0 + 1) + 1
            = (M * (M + C0 + 2) + 1) + (M * Mgeom) * Real.log (1 / δ)
        ring
      linarith
    have hAB_le : A + B * Real.log (1 / δ) ≤ δ ^ (-η) := by
      have : (1/2) * δ ^ (-η) + (1/2) * δ ^ (-η) = δ ^ (-η) := by ring
      linarith
    linarith
  have h_conj7 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Cgeom * Real.exp (10 * Real.exp 1) *
        δ ^ (Mgeom - netGeomConstantMRaw E) ≤ 1/3 := by
    set slack : ℝ := Mgeom - netGeomConstantMRaw E with hslack_def
    have hslack_pos : 0 < slack := by
      rw [hslack_def, hMgeom_def]
      have := netGeomConstantM_gt_raw E
      linarith
    set K : ℝ := Cgeom * Real.exp (10 * Real.exp 1) with hK_def
    have hK_pos : 0 < K := by
      rw [hK_def]
      exact mul_pos hCgeom_pos (Real.exp_pos _)
    have h_tend : Tendsto (fun δ : ℝ => δ ^ slack) (𝓝[>] 0) (𝓝 0) := by
      have h_neg : Tendsto (fun δ : ℝ => δ ^ (-slack)) (𝓝[>] 0) atTop :=
        tendsto_rpow_neg_nhdsGT_zero (by linarith : -slack < 0)
      have h_inv : Tendsto (fun δ : ℝ => (δ ^ (-slack))⁻¹) (𝓝[>] 0) (𝓝 0) :=
        h_neg.inv_tendsto_atTop
      refine h_inv.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ_pos_w
      have hδ_pos_real : (0 : ℝ) < δ := hδ_pos_w
      have h_neg_eq : δ ^ (-slack) = (δ ^ slack)⁻¹ :=
        Real.rpow_neg hδ_pos_real.le slack
      rw [h_neg_eq, inv_inv]
    have h_tend_mul : Tendsto (fun δ : ℝ => K * δ ^ slack) (𝓝[>] 0) (𝓝 0) := by
      have := h_tend.const_mul K
      simpa using this
    have h_event : ∀ᶠ δ : ℝ in 𝓝[>] 0, K * δ ^ slack ≤ 1/3 := by
      have h13 : (0 : ℝ) < 1/3 := by norm_num
      have h_lt : ∀ᶠ δ : ℝ in 𝓝[>] 0, K * δ ^ slack < 1/3 := by
        have := h_tend_mul.eventually
          (eventually_lt_nhds (show (0 : ℝ) < 1/3 by norm_num))
        exact this
      filter_upwards [h_lt] with δ hδ
      exact hδ.le
    filter_upwards [h_event] with δ hδ
    exact hδ
  filter_upwards [h_conj1, h_conj2, h_conj3, h_conj4, h_conj5, h_conj6, h_conj7]
    with δ h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

set_option maxHeartbeats 400000 in
-- Splitting the linear-in-`CF` comparison off the polylog-versus-power estimate multiplies the
-- elaboration work of the non-uniform lemma.
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **`CF`-uniform residual envelope.**

Same conclusion as `Kakeya.randCF_residual_envelope`, but with the quantifier over the Frostman
constant `CF` moved *inside* the `∀ᶠ δ`, so that a single smallness threshold for `δ` serves
every `CF ≥ 1` at once.

No upper restriction on `CF` is needed here: both sides of the inequality are linear in `CF`
(the left through `max (uc * ⌈CF⌉₊) (CF * M_vol / (c_vol * vol_B1)) + 1 ≤ (A + 1) * CF` with
`A := max (2 * uc) (M_vol / (c_vol * vol_B1))`, using `⌈CF⌉₊ ≤ 2 * CF`; the right through
`⌈CF⌉₊ ≥ CF`), so after dividing by `CF` the claim reduces to the `CF`-free statement that
`⌈netGeomConstantM E * log (1 / δ)⌉₊ * (A + 1) * vol_B2 * M_vol * C_cover_env < δ ^ (-η) * c_vol`
eventually, which is the same polylog-versus-power comparison the non-uniform lemma makes. -/
private lemma randCF_residual_envelope_uniform
    (_hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol)
    (uc : ℝ) (huc_pos : 0 < uc)
    (C_cover_env : ℝ) (hC_cover_env_pos : 0 < C_cover_env)
    (vol_B1 vol_B2 : ℝ) (_hvol_B1_pos : 0 < vol_B1) (hvol_B2_pos : 0 < vol_B2) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      ∀ CF : ℝ, 1 ≤ CF →
      (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) *
          (max (uc * (⌈CF⌉₊ : ℝ))
            (CF * M_vol / (c_vol * vol_B1)) + 1) *
          vol_B2 * M_vol * C_cover_env
        < δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol := by
  set A : ℝ := max (2 * uc) (M_vol / (c_vol * vol_B1)) with hA_def
  have hA_pos : 0 < A := by
    rw [hA_def]
    exact lt_max_iff.mpr (Or.inl (mul_pos (by norm_num) huc_pos))
  have hA_ge_two : 2 * uc ≤ A := by rw [hA_def]; exact le_max_left _ _
  have hA_ge_pack : M_vol / (c_vol * vol_B1) ≤ A := by
    rw [hA_def]; exact le_max_right _ _
  set L : ℝ := (A + 1) * vol_B2 * M_vol * C_cover_env with hL_def
  have hL_pos : 0 < L := by
    rw [hL_def]
    have hA1 : 0 < A + 1 := by linarith
    positivity
  have h_rpow_neg_eta : Tendsto (fun δ : ℝ => δ ^ (-η)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη)
  have h_log_littleO_eta :
      (fun δ : ℝ => |Real.log δ| ^ (1 : ℝ)) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-η)) :=
    isLittleO_abs_log_rpow_rpow_nhdsGT_zero (1 : ℝ) (neg_neg_iff_pos.mpr hη)
  have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
    eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
  have hA_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0, L ≤ (1/2) * c_vol * δ ^ (-η) := by
    have htend : Tendsto (fun δ : ℝ => (1/2) * c_vol * δ ^ (-η)) (𝓝[>] 0) atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < (1/2) * c_vol)
        h_rpow_neg_eta
    exact htend.eventually_ge_atTop L
  have hB_log_eventually : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (netGeomConstantM E * L) * Real.log (1 / δ) ≤ (1/2) * c_vol * δ ^ (-η) := by
    have hlittle : (fun δ : ℝ => |Real.log δ|) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-η)) := by
      have := h_log_littleO_eta
      simpa [Real.rpow_one] using this
    have hML : 0 < netGeomConstantM E * L := mul_pos (netGeomConstantM_pos E) hL_pos
    have hε : 0 < c_vol / (2 * (netGeomConstantM E * L + 1)) := by
      have hin : 0 < 2 * (netGeomConstantM E * L + 1) := by linarith
      exact div_pos hc_vol_pos hin
    have h_eventually_abs : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        ‖|Real.log δ|‖ ≤ (c_vol / (2 * (netGeomConstantM E * L + 1))) * ‖δ ^ (-η)‖ :=
      hlittle.def hε
    filter_upwards [h_eventually_abs, h_in_unit] with δ h1 hδmem
    obtain ⟨hδpos, hδlt1⟩ := hδmem
    have hpow_nonneg : 0 ≤ δ ^ (-η) := Real.rpow_nonneg hδpos.le _
    have hpow_abs : ‖δ ^ (-η)‖ = δ ^ (-η) := Real.norm_of_nonneg hpow_nonneg
    have habs_abs : ‖|Real.log δ|‖ = |Real.log δ| := by
      rw [Real.norm_eq_abs, abs_abs]
    rw [hpow_abs, habs_abs] at h1
    have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub]
    have hlog_neg : Real.log δ < 0 := Real.log_neg hδpos hδlt1
    have habs_eq : |Real.log δ| = -Real.log δ := abs_of_neg hlog_neg
    have hlog_inv_eq : Real.log (1 / δ) = |Real.log δ| := by rw [hlog_eq, habs_eq]
    rw [hlog_inv_eq]
    have hbp1 : 0 < netGeomConstantM E * L + 1 := by linarith [hML]
    calc (netGeomConstantM E * L) * |Real.log δ|
        ≤ (netGeomConstantM E * L + 1) * |Real.log δ| := by
          exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (netGeomConstantM E * L + 1) *
            ((c_vol / (2 * (netGeomConstantM E * L + 1))) * δ ^ (-η)) :=
          mul_le_mul_of_nonneg_left h1 hbp1.le
      _ = ((netGeomConstantM E * L + 1) *
          (c_vol / (2 * (netGeomConstantM E * L + 1)))) * δ ^ (-η) := by ring
      _ = (1/2) * c_vol * δ ^ (-η) := by
          congr 1
          field_simp
  filter_upwards [hA_eventually, hB_log_eventually, h_in_unit]
    with δ hAev hBev hδmem
  obtain ⟨hδpos, hδlt1⟩ := hδmem
  have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
    rw [show (1 : ℝ) / δ = δ⁻¹ from one_div δ, Real.log_inv]
    have hle : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδlt1.le
    linarith
  let w : ℝ := (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ)
  have hbasic : w * L < δ ^ (-η) * c_vol := by
    have hlog0 : 0 ≤ netGeomConstantM E * Real.log (1 / δ) :=
      mul_nonneg (netGeomConstantM_pos E).le hlog_nonneg
    have hceil_lt : (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) <
        netGeomConstantM E * Real.log (1 / δ) + 1 :=
      Nat.ceil_lt_add_one hlog0
    have hstep1 : w * L < (netGeomConstantM E * Real.log (1 / δ) + 1) * L := by
      exact mul_lt_mul_of_pos_right hceil_lt hL_pos
    have hExp : (netGeomConstantM E * Real.log (1 / δ) + 1) * L
        = L + (netGeomConstantM E * L) * Real.log (1 / δ) := by ring
    rw [hExp] at hstep1
    have hAB : L + (netGeomConstantM E * L) * Real.log (1 / δ) ≤ (δ ^ (-η)) * c_vol := by
      have hhalf : (1/2) * c_vol * δ ^ (-η) + (1/2) * c_vol * δ ^ (-η)
          = δ ^ (-η) * c_vol := by ring
      nlinarith
    exact hstep1.trans_le hAB
  intro CF hCF
  have hCF_pos : 0 < CF := lt_of_lt_of_le one_pos hCF
  have hceil_le_two : (⌈CF⌉₊ : ℝ) ≤ 2 * CF := by
    have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ CF)
    nlinarith
  have hcf_le_ceil : CF ≤ (⌈CF⌉₊ : ℝ) := Nat.le_ceil CF
  let mf : ℝ := max (uc * (⌈CF⌉₊ : ℝ)) (CF * M_vol / (c_vol * vol_B1))
  have huc_le : uc * (⌈CF⌉₊ : ℝ) ≤ A * CF := by
    calc uc * (⌈CF⌉₊ : ℝ) ≤ uc * (2 * CF) :=
        mul_le_mul_of_nonneg_left hceil_le_two huc_pos.le
      _ = 2 * uc * CF := by ring
      _ ≤ A * CF := mul_le_mul_of_nonneg_right hA_ge_two hCF_pos.le
  have hpack_le : CF * M_vol / (c_vol * vol_B1) ≤ A * CF := by
    calc CF * M_vol / (c_vol * vol_B1)
        = (M_vol / (c_vol * vol_B1)) * CF := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ A * CF := mul_le_mul_of_nonneg_right hA_ge_pack hCF_pos.le
  have hmax_le : mf ≤ A * CF := max_le huc_le hpack_le
  have hmax_factor : mf + 1 ≤ (A + 1) * CF := by
    nlinarith [hmax_le, hCF]
  have hw_nonneg : 0 ≤ w := by
    dsimp [w]
    exact Nat.cast_nonneg _
  have hwmf : w * (mf + 1) ≤ w * ((A + 1) * CF) :=
    mul_le_mul_of_nonneg_left hmax_factor hw_nonneg
  have hQnn : 0 ≤ vol_B2 * M_vol * C_cover_env := by positivity
  have hle1 : w * (mf + 1) * vol_B2 * M_vol * C_cover_env ≤
      w * ((A + 1) * CF) * vol_B2 * M_vol * C_cover_env := by
    calc w * (mf + 1) * vol_B2 * M_vol * C_cover_env
        = (w * (mf + 1)) * (vol_B2 * M_vol * C_cover_env) := by ring
      _ ≤ (w * ((A + 1) * CF)) * (vol_B2 * M_vol * C_cover_env) :=
          mul_le_mul_of_nonneg_right hwmf hQnn
      _ = w * ((A + 1) * CF) * vol_B2 * M_vol * C_cover_env := by ring
  have hle2 : w * ((A + 1) * CF) * vol_B2 * M_vol * C_cover_env = CF * (w * L) := by
    rw [hL_def]
    ring
  have hmid : CF * (w * L) < CF * (δ ^ (-η) * c_vol) :=
    mul_lt_mul_of_pos_left hbasic hCF_pos
  have hdc : 0 ≤ δ ^ (-η) * c_vol := by
    exact mul_nonneg (Real.rpow_nonneg hδpos.le _) hc_vol_pos.le
  have hrhs : CF * (δ ^ (-η) * c_vol) ≤ δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol := by
    calc CF * (δ ^ (-η) * c_vol)
        = (δ ^ (-η) * c_vol) * CF := by ring
      _ ≤ (δ ^ (-η) * c_vol) * (⌈CF⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left hcf_le_ceil hdc
      _ = δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol := by ring
  exact (((hle1.trans_eq hle2).trans_lt hmid).trans_le hrhs)

set_option maxHeartbeats 1000000 in
-- Three independent eventual estimates, each with its own `rpow` exponent bookkeeping.
omit [MeasurableSpace E] [BorelSpace E] in
/-- Conjuncts 1-3 of `Kakeya.randCF_smallness_envelope_uniform`, uniformly in
`1 ≤ CF ≤ δ ^ (-η₀)`. -/
private lemma randCF_uniform_conj123
    (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    {η₀ : ℝ} (hη₀_pos : 0 < η₀) (hη₀_le_quarter : η₀ ≤ η / 4)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol)
    (C_pack_ext : ℕ) (hC_pack_ext_pos : 0 < C_pack_ext) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
      (Real.exp 11
          + max ((netGeomConstantC E) * M_vol * CF / c_vol) 1
              * 2 ^ Module.finrank ℝ E
          + ((netGeomConstantM E) + (Module.finrank ℝ E : ℝ)) * Real.log (1 / δ)
            ≤ δ ^ (-(η / 2))) ∧
      δ ≤ c_vol ∧
      ((C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF
            * (2 ^ Module.finrank ℝ E)
          ≤ δ ^ (-η)) := by
  set n : ℕ := Module.finrank ℝ E
  set Cgeom : ℝ := netGeomConstantC E
  set Mgeom : ℝ := netGeomConstantM E
  have hn_n : 0 < n := lt_trans (by norm_num : (0 : ℕ) < 1) hn
  have hCgeom_pos : 0 < Cgeom := netGeomConstantC_pos E
  have hMgeom_pos : 0 < Mgeom := netGeomConstantM_pos E
  have hη2_pos : 0 < η / 2 := by positivity
  have hη2_gt_η0 : 0 < η / 2 - η₀ := by linarith
  have hη_gt_η0 : 0 < η - η₀ := by linarith
  have h_pos_mem : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
    eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
  set K : ℝ := max (Cgeom * M_vol / c_vol) 1 with hK_def
  have hK_pos : 0 < K := by
    rw [hK_def]
    exact lt_max_iff.mpr (Or.inl (div_pos (mul_pos hCgeom_pos hM_vol_pos) hc_vol_pos))
  have hK_ge_one : (1 : ℝ) ≤ K := by
    rw [hK_def]
    exact le_max_right _ _
  have hK_ge_pack : Cgeom * M_vol / c_vol ≤ K := by
    rw [hK_def]
    exact le_max_left _ _
  set B : ℝ := Mgeom + (n : ℝ) with hB_def
  have hB_nonneg : 0 ≤ B := by
    rw [hB_def]
    exact add_nonneg hMgeom_pos.le (Nat.cast_nonneg _)
  -- (a) exponential constant
  have h_conj1_exp : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      Real.exp 11 ≤ (1 / 3) * δ ^ (-(η / 2)) := by
    have htend : Tendsto (fun δ : ℝ => (1 / 3) * δ ^ (-(η / 2))) (𝓝[>] 0) atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 3)
        (tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη2_pos))
    exact htend.eventually_ge_atTop (Real.exp 11)
  -- (b) CF-power term, CF-free
  have h_conj1_pow : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      K * 2 ^ n * δ ^ (-η₀) ≤ (1 / 3) * δ ^ (-(η / 2)) := by
    have hbig : ∀ᶠ δ : ℝ in 𝓝[>] 0, 3 * (K * 2 ^ n) ≤ δ ^ (-(η / 2 - η₀)) :=
      (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(η / 2 - η₀) < 0)).eventually_ge_atTop
        (3 * (K * 2 ^ n))
    filter_upwards [hbig, h_pos_mem] with δ hbig hδpos
    have hthird : K * 2 ^ n ≤ (1 / 3) * δ ^ (-(η / 2 - η₀)) := by
      have hq : (1 / 3) * (3 * (K * 2 ^ n)) = K * 2 ^ n := by ring
      rw [← hq]
      exact mul_le_mul_of_nonneg_left hbig (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hδpow_nonneg : 0 ≤ δ ^ (-η₀) := Real.rpow_nonneg hδpos.le _
    calc
      K * 2 ^ n * δ ^ (-η₀) = (K * 2 ^ n) * δ ^ (-η₀) := by ring
      _ ≤ ((1 / 3) * δ ^ (-(η / 2 - η₀))) * δ ^ (-η₀) := by
          exact mul_le_mul_of_nonneg_right hthird hδpow_nonneg
      _ = (1 / 3) * (δ ^ (-(η / 2 - η₀)) * δ ^ (-η₀)) := by ring
      _ = (1 / 3) * δ ^ (-(η / 2 - η₀) + -η₀) := by
        congr 1
        rw [← Real.rpow_add hδpos]
      _ = (1 / 3) * δ ^ (-(η / 2)) := by
        congr 1
        ring
  -- (c) logarithmic term
  have h_conj_log : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      B * Real.log (1 / δ) ≤ (1 / 3) * δ ^ (-(η / 2)) := by
    have hlittle : (fun δ : ℝ => |Real.log δ|) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-(η / 2))) := by
      have := isLittleO_abs_log_rpow_rpow_nhdsGT_zero (1 : ℝ) (neg_neg_iff_pos.mpr hη2_pos)
      simpa [Real.rpow_one] using this
    have hε : 0 < (1 : ℝ) / (3 * (B + 1)) := by
      refine div_pos one_pos ?_
      linarith [hB_nonneg]
    have h_eventually_abs : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        ‖|Real.log δ|‖ ≤ (1 / (3 * (B + 1))) * ‖δ ^ (-(η / 2))‖ :=
      hlittle.def hε
    filter_upwards [h_eventually_abs, h_in_unit] with δ habs hgmem
    obtain ⟨hδpos, hδlt1⟩ := hgmem
    have hpow_nonneg : 0 ≤ δ ^ (-(η / 2)) := Real.rpow_nonneg hδpos.le _
    have hpow_abs : ‖δ ^ (-(η / 2))‖ = δ ^ (-(η / 2)) := Real.norm_of_nonneg hpow_nonneg
    have habs_abs : ‖|Real.log δ|‖ = |Real.log δ| := by
      rw [Real.norm_eq_abs, abs_abs]
    rw [hpow_abs, habs_abs] at habs
    have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub]
    have hlogδ_neg : Real.log δ < 0 := Real.log_neg hδpos hδlt1
    have habs_eq : |Real.log δ| = -Real.log δ := abs_of_neg hlogδ_neg
    have hlog_inv : Real.log (1 / δ) = |Real.log δ| := by rw [hlog_eq, habs_eq]
    rw [hlog_inv]
    have hBp1_pos : 0 < B + 1 := by linarith [hB_nonneg]
    calc
      B * |Real.log δ|
          ≤ (B + 1) * |Real.log δ| := by
            have : B ≤ B + 1 := by linarith
            exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ ≤ (B + 1) * ((1 / (3 * (B + 1))) * δ ^ (-(η / 2))) := by
          exact mul_le_mul_of_nonneg_left habs hBp1_pos.le
      _ = (B + 1) * (1 / (3 * (B + 1))) * δ ^ (-(η / 2)) := by ring
      _ = (1 / 3) * δ ^ (-(η / 2)) := by congr 1; field_simp
  have h_conj1 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
        Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * 2 ^ n
            + (Mgeom + (n : ℝ)) * Real.log (1 / δ)
          ≤ δ ^ (-(η / 2)) := by
    filter_upwards [h_conj1_exp, h_conj1_pow, h_conj_log] with δ hδ_exp hδ_pow hδ_log
    intro CF hCF hCF_le
    have hCF_nonneg : 0 ≤ CF := by linarith
    have h2n_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
    have hmax_a : Cgeom * M_vol * CF / c_vol ≤ K * CF := by
      calc Cgeom * M_vol * CF / c_vol = (Cgeom * M_vol / c_vol) * CF := by ring
        _ ≤ K * CF := mul_le_mul_of_nonneg_right hK_ge_pack hCF_nonneg
    have hmax_b : (1 : ℝ) ≤ K * CF := by
      calc (1 : ℝ) ≤ K := hK_ge_one
        _ = K * 1 := by rw [mul_one]
        _ ≤ K * CF := mul_le_mul_of_nonneg_left hCF hK_pos.le
    have hmax_le : max (Cgeom * M_vol * CF / c_vol) 1 ≤ K * CF := max_le hmax_a hmax_b
    have hmax_le_pow : K * CF ≤ K * δ ^ (-η₀) :=
      mul_le_mul_of_nonneg_left hCF_le hK_pos.le
    have hterm : max (Cgeom * M_vol * CF / c_vol) 1 * (2 ^ n : ℝ)
        ≤ K * δ ^ (-η₀) * 2 ^ n := by
      calc max (Cgeom * M_vol * CF / c_vol) 1 * (2 ^ n : ℝ)
          ≤ (K * CF) * (2 ^ n : ℝ) :=
              mul_le_mul_of_nonneg_right hmax_le h2n_nonneg
        _ ≤ (K * δ ^ (-η₀)) * (2 ^ n : ℝ) :=
            mul_le_mul_of_nonneg_right hmax_le_pow h2n_nonneg
        _ = K * δ ^ (-η₀) * 2 ^ n := by ring
    have hBL : (Mgeom + (n : ℝ)) * Real.log (1 / δ) = B * Real.log (1 / δ) := by
      rw [hB_def]
    calc
      Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * (2 ^ n)
          + (Mgeom + (n : ℝ)) * Real.log (1 / δ)
          = Real.exp 11 + max (Cgeom * M_vol * CF / c_vol) 1 * (2 ^ n) + B * Real.log (1 / δ) := by
            rw [hBL]
      _ ≤ Real.exp 11 + K * δ ^ (-η₀) * 2 ^ n + B * Real.log (1 / δ) := by
            exact add_le_add (add_le_add (le_refl _) hterm) (le_refl _)
      _ = Real.exp 11 + K * 2 ^ n * δ ^ (-η₀) + B * Real.log (1 / δ) := by ring
      _ ≤ δ ^ (-(η / 2)) := by
            have hsum : (1 / 3) * δ ^ (-(η / 2)) + (1 / 3) * δ ^ (-(η / 2))
                + (1 / 3) * δ ^ (-(η / 2)) = δ ^ (-(η / 2)) := by ring
            linarith
  have h_conj2 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ c_vol := by
    have h_mem : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) c_vol :=
      eventually_mem_set.mpr (Ioo_mem_nhdsGT hc_vol_pos)
    exact h_mem.mono fun hδ hmem => hmem.2.le
  have h_conj3 : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
        (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF * (2 ^ n)
          ≤ δ ^ (-η) := by
    set C3 : ℝ := (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * (2 ^ n) with hC3_def
    have hC3_nonneg : 0 ≤ C3 := by
      rw [hC3_def]
      positivity
    have hbig : ∀ᶠ δ : ℝ in 𝓝[>] 0, C3 ≤ δ ^ (-(η - η₀)) :=
      (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(η - η₀) < 0)).eventually_ge_atTop C3
    filter_upwards [hbig, h_pos_mem] with δ hbig hδpos
    intro CF hCF hCF_le
    calc
      (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF * (2 ^ n)
          = C3 * CF := by
            rw [hC3_def]
            ring
      _ ≤ C3 * δ ^ (-η₀) := mul_le_mul_of_nonneg_left hCF_le hC3_nonneg
      _ ≤ δ ^ (-(η - η₀)) * δ ^ (-η₀) := by
            exact mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hδpos.le _)
      _ = δ ^ (-(η - η₀) + -η₀) := by
            rw [← Real.rpow_add hδpos]
      _ = δ ^ (-η) := by
            congr 1
            ring
  filter_upwards [h_conj1, h_conj2, h_conj3] with δ h1 h2 h3
  intro CF hCF hCF_le
  exact ⟨h1 CF hCF hCF_le, h2, h3 CF hCF hCF_le⟩

set_option maxHeartbeats 1000000 in
-- Clearing the `⌈CF⌉₊`-dependent denominators and cancelling the common `δ ^ (n-1)` factor is
-- expensive.
/-- Conjuncts 4-5 of `Kakeya.randCF_smallness_envelope_uniform`, uniformly in
`1 ≤ CF ≤ δ ^ (-η₀)`. -/
private lemma randCF_uniform_conj45
    (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    {η₀ : ℝ} (_hη₀_pos : 0 < η₀) (hη₀_le_quarter : η₀ ≤ η / 4) (hη₀_le_one : η₀ ≤ 1)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
      (M_vol * δ ^ (Module.finrank ℝ E - 1) *
          (2 ^ Module.finrank ℝ E *
            volume.real (Metric.closedBall (0 : E) 1))
          * 2 * netGeomConstantC E
          ≤ δ ^ (-η) * (c_vol * δ ^ (Module.finrank ℝ E - 1)) *
              (1 / (2 * (⌈CF⌉₊ : ℝ) *
                (volume.real (Metric.closedBall (0 : E) 1))⁻¹))) ∧
      (2 * netGeomConstantC E * δ ^ Module.finrank ℝ E ≤
          1 / (2 * (⌈CF⌉₊ : ℝ) *
            (volume.real (Metric.closedBall (0 : E) 1))⁻¹)) := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  set Cgeom : ℝ := netGeomConstantC E with hCgeom_def
  set volB : ℝ := volume.real (Metric.closedBall (0 : E) 1) with hvolB_def
  have hCgeom_pos : 0 < Cgeom := netGeomConstantC_pos E
  have hvolB_pos : 0 < volB := by
    refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
    exact (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hη34_pos : 0 < 3 * η / 4 := by positivity
  have h_rpow_neg_eta34 : Tendsto (fun δ : ℝ => δ ^ (-(3 * η / 4))) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη34_pos)
  have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
    eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
  set L : ℝ := M_vol * (2 ^ n * volB) * 2 * Cgeom with hL_def
  have hL_pos : 0 < L := by
    rw [hL_def]
    positivity
  have h_asym : ∀ᶠ δ : ℝ in 𝓝[>] 0, L ≤ (c_vol * volB / 4) * δ ^ (-(3 * η / 4)) := by
    have htend : Tendsto (fun δ : ℝ => (c_vol * volB / 4) * δ ^ (-(3 * η / 4)))
        (𝓝[>] 0) atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < c_vol * volB / 4) h_rpow_neg_eta34
    exact htend.eventually_ge_atTop L
  have h_bnd5 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ≤ volB / (8 * Cgeom) := by
    have h_mem : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) (volB / (8 * Cgeom)) :=
      eventually_mem_set.mpr (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < volB / (8 * Cgeom)))
    exact h_mem.mono fun δ hδ => hδ.2.le
  filter_upwards [h_asym, h_bnd5, h_in_unit] with δ hasym hbnd5 hδmem
  obtain ⟨hδpos, hδlt1⟩ := hδmem
  -- generic uniform bound on the ceiling
  intro CF hCF hCF_le
  have hCF_pos : 0 < CF := lt_of_lt_of_le one_pos hCF
  have hceil_pos : 0 < (⌈CF⌉₊ : ℝ) := by
    have h : 0 < ⌈CF⌉₊ := Nat.ceil_pos.mpr hCF_pos
    exact_mod_cast h
  have hceil_ne : (⌈CF⌉₊ : ℝ) ≠ 0 := ne_of_gt hceil_pos
  have hvolB_ne : volB ≠ 0 := hvolB_pos.ne'
  have hvolBinv_pos : 0 < volB⁻¹ := inv_pos.mpr hvolB_pos
  have hfrac : 1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹) = volB / (2 * (⌈CF⌉₊ : ℝ)) := by
    field_simp [hvolB_ne, hceil_ne]
  have h_ceil_pow : (⌈CF⌉₊ : ℝ) ≤ 2 * δ ^ (-η₀) := by
    have h_lt : (⌈CF⌉₊ : ℝ) < CF + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (lt_of_lt_of_le one_pos hCF))
    linarith
  refine ⟨?_, ?_⟩
  · -- conjunct 4
    have hLHS_eq : M_vol * δ ^ (n - 1) * (2 ^ n * volB) * 2 * Cgeom = L * δ ^ (n - 1) := by
      change M_vol * δ ^ (n - 1) * (2 ^ n * volB) * 2 * Cgeom =
        (M_vol * (2 ^ n * volB) * 2 * Cgeom) * δ ^ (n - 1)
      ring
    have hRHS_eq :
        δ ^ (-η) * (c_vol * δ ^ (n - 1)) * (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹))
          = (c_vol * (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹))) * δ ^ (-η) * δ ^ (n - 1) := by
      ring
    rw [hLHS_eq, hRHS_eq]
    have hL_le : L ≤ c_vol * (1 / (2 * (⌈CF⌉₊ : ℝ) * volB⁻¹)) * δ ^ (-η) := by
      rw [hfrac]
      calc
        L ≤ (c_vol * volB / 4) * δ ^ (-(3 * η / 4)) := hasym
        _ ≤ (c_vol * volB / 4) * δ ^ (η₀ - η) := by
          have h_le0 : δ ^ (-(3 * η / 4)) ≤ δ ^ (η₀ - η) :=
            Real.rpow_le_rpow_of_exponent_ge hδpos hδlt1.le
              (by linarith : η₀ - η ≤ -(3 * η / 4))
          exact mul_le_mul_of_nonneg_left h_le0 (by positivity : (0 : ℝ) ≤ c_vol * volB / 4)
        _ = (c_vol * volB / 4) * δ ^ η₀ * δ ^ (-η) := by
          have h_exp : δ ^ (η₀ - η) = δ ^ η₀ * δ ^ (-η) := by
            rw [show η₀ - η = η₀ + -η by ring]
            rw [Real.rpow_add hδpos]
          rw [h_exp]
          ring
        _ ≤ (c_vol * volB / 2) * (⌈CF⌉₊ : ℝ)⁻¹ * δ ^ (-η) := by
          have h_xd : (⌈CF⌉₊ : ℝ) * δ ^ η₀ ≤ 2 := by
            have h1 : (⌈CF⌉₊ : ℝ) * δ ^ η₀ ≤ 2 * δ ^ (-η₀) * δ ^ η₀ :=
              mul_le_mul_of_nonneg_right h_ceil_pow (Real.rpow_nonneg hδpos.le _)
            have h2 : 2 * δ ^ (-η₀) * δ ^ η₀ = 2 := by
              rw [mul_assoc]
              rw [← Real.rpow_add hδpos]
              have hzero : -η₀ + η₀ = 0 := by ring
              rw [hzero]
              simp
            rwa [h2] at h1
          have h_main_inv :
              (c_vol * volB / 4) * δ ^ η₀ ≤ (c_vol * volB / 2) * (⌈CF⌉₊ : ℝ)⁻¹ := by
            field_simp [hceil_ne]
            nlinarith [h_xd, hCgeom_pos]
          exact mul_le_mul_of_nonneg_right h_main_inv (Real.rpow_nonneg hδpos.le _)
        _ = c_vol * (volB / (2 * (⌈CF⌉₊ : ℝ))) * δ ^ (-η) := by
          field_simp [hceil_ne]
    exact mul_le_mul_of_nonneg_right hL_le (pow_nonneg hδpos.le _)
  · -- conjunct 5
    rw [hfrac]
    have hmul_pos : 0 < 2 * (⌈CF⌉₊ : ℝ) := by positivity
    have h5 : 2 * Cgeom * δ ^ n * (2 * (⌈CF⌉₊ : ℝ)) ≤ volB := by
      calc
        2 * Cgeom * δ ^ n * (2 * (⌈CF⌉₊ : ℝ)) ≤ 2 * Cgeom * δ ^ n * (2 * (2 * δ ^ (-η₀))) := by
          have h2x : 2 * (⌈CF⌉₊ : ℝ) ≤ 2 * (2 * δ ^ (-η₀)) := by linarith
          exact mul_le_mul_of_nonneg_left h2x (by positivity : 0 ≤ 2 * Cgeom * δ ^ n)
        _ = 8 * Cgeom * δ ^ n * δ ^ (-η₀) := by ring
        _ = 8 * Cgeom * δ ^ ((n : ℝ) - η₀) := by
          rw [← Real.rpow_natCast δ n]
          rw [mul_assoc]
          rw [← Real.rpow_add hδpos]
          congr 1
        _ ≤ 8 * Cgeom * δ ^ (1 : ℝ) := by
          have hE : (1 : ℝ) ≤ (n : ℝ) - η₀ := by
            have hn2 : 2 ≤ n := Nat.succ_le_of_lt hn
            have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
            linarith [hn2r, hη₀_le_one]
          have hle5 : δ ^ ((n : ℝ) - η₀) ≤ δ ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hδpos hδlt1.le hE
          exact mul_le_mul_of_nonneg_left hle5 (by positivity : 0 ≤ 8 * Cgeom)
        _ = 8 * Cgeom * δ := by rw [Real.rpow_one]
        _ ≤ volB := by
          have hC_ne : Cgeom ≠ 0 := hCgeom_pos.ne'
          calc 8 * Cgeom * δ ≤ 8 * Cgeom * (volB / (8 * Cgeom)) :=
                mul_le_mul_of_nonneg_left hbnd5 (mul_nonneg (by norm_num) hCgeom_pos.le)
            _ = volB := by field_simp [hC_ne]
    refine (le_div_iff₀ hmul_pos).mpr h5

set_option maxHeartbeats 1000000 in
-- The quadratic expansion produces four separate `rpow` comparisons that must be recombined.
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Conjunct 6 of `Kakeya.randCF_smallness_envelope_uniform`, uniformly in
`1 ≤ CF ≤ δ ^ (-η₀)`.  This is the quadratic-in-`CF` Chernoff cap, and the only conjunct whose
`CF`-dependence is worse than linear. -/
private lemma randCF_uniform_conj6
    {η : ℝ} (_hη : 0 < η)
    {η₀ : ℝ} (hη₀_pos : 0 < η₀) (hη₀_le_quarter : η₀ ≤ η / 4)
    (C_pack_ext : ℕ) (hC_pack_ext_pos : 0 < C_pack_ext) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
      ((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) *
          (((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) +
           (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) +
           (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
        ≤ δ ^ (-η) := by
  set C : ℝ := (C_pack_ext : ℝ) with hC_def
  have hC_ge_one : (1 : ℝ) ≤ C := by
    rw [hC_def]
    exact_mod_cast (Nat.succ_le_iff.mpr hC_pack_ext_pos)
  have hC_nonneg : 0 ≤ C := by linarith
  set Mgeom : ℝ := netGeomConstantM E with hMgeom_def
  have hMgeom_pos : 0 < Mgeom := by
    rw [hMgeom_def]
    exact netGeomConstantM_pos E
  set Q : ℝ := (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) with hQ_def
  have hQ_nonneg : 0 ≤ Q := by
    rw [hQ_def]
    exact Nat.cast_nonneg _
  have h_in_unit : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo (0 : ℝ) 1 :=
    eventually_mem_set.mpr (Ioo_mem_nhdsGT zero_lt_one)
  have hT_half : Tendsto (fun (δ : ℝ) => δ ^ (-(η / 2))) (𝓝[>] 0) atTop := by
    exact tendsto_rpow_neg_nhdsGT_zero (by linarith : -(η / 2) < 0)
  have hT_eta : Tendsto (fun (δ : ℝ) => δ ^ (-η)) (𝓝[>] 0) atTop := by
    exact tendsto_rpow_neg_nhdsGT_zero (by linarith : -η < 0)
  have hevt1 : ∀ᶠ (δ : ℝ) in 𝓝[>] 0, 36 * C ^ 2 ≤ δ ^ (-(η / 2)) :=
    hT_half.eventually_ge_atTop (36 * C ^ 2)
  have hevt2 : ∀ᶠ (δ : ℝ) in 𝓝[>] 0, 12 * C * Mgeom ≤ δ ^ (-(η / 2)) :=
    hT_half.eventually_ge_atTop (12 * C * Mgeom)
  have hevt3 : ∀ᶠ (δ : ℝ) in 𝓝[>] 0, 12 * C * (Q + 2) ≤ δ ^ (-(η / 2)) :=
    hT_half.eventually_ge_atTop (12 * C * (Q + 2))
  have hevt4 : ∀ᶠ (δ : ℝ) in 𝓝[>] 0, 4 ≤ δ ^ (-η) :=
    hT_eta.eventually_ge_atTop 4
  have hevtL : ∀ᶠ (δ : ℝ) in 𝓝[>] 0, Real.log (1 / δ) ≤ δ ^ (-(η / 4)) := by
    have hlittle : (fun δ : ℝ => |Real.log δ|) =o[𝓝[>] 0]
        (fun δ : ℝ => δ ^ (-(η / 4))) := by
      have := isLittleO_abs_log_rpow_rpow_nhdsGT_zero (1 : ℝ) (by linarith : -(η / 4) < 0)
      simpa [Real.rpow_one] using this
    have h_eventually_abs : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        ‖|Real.log δ|‖ ≤ 1 * ‖δ ^ (-(η / 4))‖ :=
      hlittle.def (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h_eventually_abs, h_in_unit] with δ habs hδmem
    obtain ⟨hδpos, hδlt1⟩ := hδmem
    have hpow_nonneg : 0 ≤ δ ^ (-(η / 4)) := Real.rpow_nonneg hδpos.le _
    have hpow_abs : ‖δ ^ (-(η / 4))‖ = δ ^ (-(η / 4)) := Real.norm_of_nonneg hpow_nonneg
    have habs_abs : ‖|Real.log δ|‖ = |Real.log δ| := by
      rw [Real.norm_eq_abs, abs_abs]
    rw [hpow_abs, habs_abs] at habs
    have hlog_eq : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div one_ne_zero hδpos.ne', Real.log_one, zero_sub]
    have hlogδ_neg : Real.log δ < 0 := Real.log_neg hδpos hδlt1
    have habs_eq : |Real.log δ| = -Real.log δ := abs_of_neg hlogδ_neg
    have hlog_inv_eq : Real.log (1 / δ) = |Real.log δ| := by rw [hlog_eq, habs_eq]
    rw [hlog_inv_eq]
    simpa using habs
  filter_upwards [hevt1, hevt2, hevt3, hevt4, hevtL, h_in_unit]
    with δ hEv1 hEv2 hEv3 hEv4 hEvL hδmem
  obtain ⟨hδpos, hδlt1⟩ := hδmem
  have hδle1 : δ ≤ 1 := hδlt1.le
  have hδp_one : (1 : ℝ) ≤ δ ^ (-η₀) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδpos hδle1 (by linarith)
  have hδp_nonneg : 0 ≤ δ ^ (-η₀) := Real.rpow_nonneg hδpos.le _
  have hδph_nonneg : 0 ≤ δ ^ (-(η / 2)) := Real.rpow_nonneg hδpos.le _
  set ℓ : ℝ := Real.log (1 / δ) with hℓ_def
  have hℓ_le : ℓ ≤ δ ^ (-(η / 4)) := by
    rwa [hℓ_def] at hEvL
  intro CF hCF hCF_le
  have hCF_pos : 0 < CF := lt_of_lt_of_le one_pos hCF
  have hCFceil_pos : 0 < (⌈CF⌉₊ : ℕ) := Nat.ceil_pos.mpr hCF_pos
  have hmax_eq : max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext = ⌈CF⌉₊ * C_pack_ext + 1 := by
    apply max_eq_left
    have hle_one : (1 : ℕ) ≤ ⌈CF⌉₊ := Nat.succ_le_iff.mpr hCFceil_pos
    calc
      C_pack_ext ≤ 1 * C_pack_ext := by rw [one_mul]
      _ ≤ ⌈CF⌉₊ * C_pack_ext := Nat.mul_le_mul_right C_pack_ext hle_one
      _ ≤ ⌈CF⌉₊ * C_pack_ext + 1 := by omega
  set M : ℝ := ((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) with hM_def
  set P : ℝ := (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) with hP_def
  change M * (M + P + Q + 1) + 1 ≤ δ ^ (-η)
  have hM_eq : M = (⌈CF⌉₊ : ℝ) * C + 1 := by
    rw [hM_def, hmax_eq]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hC_def]
  have hM_nonneg : 0 ≤ M := by
    rw [hM_def]
    exact Nat.cast_nonneg _
  have hP_nonneg : 0 ≤ P := by
    rw [hP_def]
    exact Nat.cast_nonneg _
  have hCeil_le : (⌈CF⌉₊ : ℝ) ≤ 2 * δ ^ (-η₀) := by
    have h_lt : (⌈CF⌉₊ : ℝ) < CF + 1 :=
      Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ CF)
    linarith
  have hCδ_one : (1 : ℝ) ≤ C * δ ^ (-η₀) := by
    calc (1 : ℝ) ≤ C := hC_ge_one
      _ = C * 1 := by rw [mul_one]
      _ ≤ C * δ ^ (-η₀) := mul_le_mul_of_nonneg_left hδp_one hC_nonneg
  have hM_le : M ≤ 3 * C * δ ^ (-η₀) := by
    calc
      M = (⌈CF⌉₊ : ℝ) * C + 1 := hM_eq
      _ ≤ (2 * δ ^ (-η₀)) * C + 1 := by
        have hmul : (⌈CF⌉₊ : ℝ) * C ≤ (2 * δ ^ (-η₀)) * C :=
          mul_le_mul_of_nonneg_right hCeil_le hC_nonneg
        linarith
      _ = 2 * C * δ ^ (-η₀) + 1 := by ring
      _ ≤ 3 * C * δ ^ (-η₀) := by linarith [hCδ_one]
  have hlog_nonneg : 0 ≤ ℓ := by
    rw [hℓ_def]
    rw [show (1 : ℝ) / δ = δ⁻¹ from one_div δ]
    rw [Real.log_inv]
    have : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδle1
    linarith
  have hMgeom_log_nn : 0 ≤ Mgeom * ℓ := mul_nonneg hMgeom_pos.le hlog_nonneg
  have hP_eq : P = (⌈Mgeom * ℓ⌉₊ : ℝ) := by
    rw [hP_def, hMgeom_def, hℓ_def]
  have hP_le : P ≤ Mgeom * ℓ + 1 := by
    have h_lt : (⌈Mgeom * ℓ⌉₊ : ℝ) < Mgeom * ℓ + 1 := Nat.ceil_lt_add_one hMgeom_log_nn
    rw [hP_eq]
    linarith
  set S : ℝ := 3 * C * δ ^ (-η₀) with hS_def
  have hS_nonneg : 0 ≤ S := by
    rw [hS_def]
    exact mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 3) hC_nonneg) hδp_nonneg
  have hinner : M + P + Q + 1 ≤ S + Mgeom * ℓ + Q + 2 := by
    linarith [hM_le, hP_le]
  have hres2_nonneg : 0 ≤ M + P + Q + 1 := by
    linarith [hM_nonneg, hP_nonneg, hQ_nonneg]
  have hcomp : M * (M + P + Q + 1) ≤ S * (S + Mgeom * ℓ + Q + 2) :=
    (mul_le_mul_of_nonneg_right hM_le hres2_nonneg).trans
      (mul_le_mul_of_nonneg_left hinner hS_nonneg)
  have h_phase_mul : δ ^ (-(η / 2)) * δ ^ (-(η / 2)) = δ ^ (-η) := by
    rw [← Real.rpow_add hδpos]
    congr 1
    ring
  have h_δsq : δ ^ (-η₀) * δ ^ (-η₀) = δ ^ (-(2 * η₀)) := by
    rw [← Real.rpow_add hδpos]
    congr 1
    ring
  have h_p2_le : δ ^ (-(2 * η₀)) ≤ δ ^ (-(η / 2)) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 (by linarith)
  have h_ell_le_half : δ ^ (-η₀) * ℓ ≤ δ ^ (-(η / 2)) := by
    have hstep : δ ^ (-η₀) * ℓ ≤ δ ^ (-η₀) * δ ^ (-(η / 4)) :=
      mul_le_mul_of_nonneg_left hℓ_le hδp_nonneg
    have hExp :
        δ ^ (-η₀) * δ ^ (-(η / 4)) ≤ δ ^ (-(η / 2)) := by
      have h1 : δ ^ (-η₀) * δ ^ (-(η / 4)) = δ ^ (-η₀ + -(η / 4)) := by
        rw [← Real.rpow_add hδpos]
      rw [h1]
      exact Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 (by linarith)
    exact hstep.trans hExp
  have h_δ₀_le_half : δ ^ (-η₀) ≤ δ ^ (-(η / 2)) := by
    exact Real.rpow_le_rpow_of_exponent_ge hδpos hδle1 (by linarith)
  set T1 : ℝ := 9 * C ^ 2 * δ ^ (-(2 * η₀)) with hT1_def
  set T2 : ℝ := 3 * C * Mgeom * (δ ^ (-η₀) * ℓ) with hT2_def
  set T3 : ℝ := 3 * C * (Q + 2) * δ ^ (-η₀) with hT3_def
  have hexp : S * (S + Mgeom * ℓ + Q + 2) = T1 + T2 + T3 := by
    rw [hS_def]
    calc
      (3 * C * δ ^ (-η₀)) * ((3 * C * δ ^ (-η₀)) + Mgeom * ℓ + Q + 2)
          = 9 * C ^ 2 * (δ ^ (-η₀) * δ ^ (-η₀)) + 3 * C * Mgeom * δ ^ (-η₀) * ℓ
              + 3 * C * (Q + 2) * δ ^ (-η₀) := by ring
      _ = T1 + T2 + T3 := by
        rw [h_δsq, hT1_def, hT2_def, hT3_def]
        ring
  have hTotal : M * (M + P + Q + 1) + 1 ≤ T1 + T2 + T3 + 1 := by
    have h1 : M * (M + P + Q + 1) + 1 ≤ S * (S + Mgeom * ℓ + Q + 2) + 1 := by
      linarith [hcomp]
    rwa [hexp] at h1
  have h9sq_nonneg : 0 ≤ 9 * C ^ 2 := by positivity
  have hT1_le : T1 ≤ (1 / 4) * δ ^ (-η) := by
    have hA9 : 9 * C ^ 2 ≤ (1 / 4) * δ ^ (-(η / 2)) := by
      linarith [hEv1]
    calc
      T1 = 9 * C ^ 2 * δ ^ (-(2 * η₀)) := hT1_def
      _ ≤ 9 * C ^ 2 * δ ^ (-(η / 2)) :=
        mul_le_mul_of_nonneg_left h_p2_le h9sq_nonneg
      _ ≤ (1 / 4) * δ ^ (-(η / 2)) * δ ^ (-(η / 2)) :=
        mul_le_mul_of_nonneg_right hA9 hδph_nonneg
      _ = (1 / 4) * (δ ^ (-(η / 2)) * δ ^ (-(η / 2))) := by ring
      _ = (1 / 4) * δ ^ (-η) := by rw [h_phase_mul]
  have hT2_nonneg : 0 ≤ 3 * C * Mgeom := by positivity
  have hT2_le : T2 ≤ (1 / 4) * δ ^ (-η) := by
    have hB3 : 3 * C * Mgeom ≤ (1 / 4) * δ ^ (-(η / 2)) := by
      linarith [hEv2]
    calc
      T2 = 3 * C * Mgeom * (δ ^ (-η₀) * ℓ) := hT2_def
      _ ≤ 3 * C * Mgeom * δ ^ (-(η / 2)) :=
        mul_le_mul_of_nonneg_left h_ell_le_half hT2_nonneg
      _ ≤ (1 / 4) * δ ^ (-(η / 2)) * δ ^ (-(η / 2)) :=
        mul_le_mul_of_nonneg_right hB3 hδph_nonneg
      _ = (1 / 4) * (δ ^ (-(η / 2)) * δ ^ (-(η / 2))) := by ring
      _ = (1 / 4) * δ ^ (-η) := by rw [h_phase_mul]
  have hT3_nonneg : 0 ≤ 3 * C * (Q + 2) := by positivity
  have hT3_le : T3 ≤ (1 / 4) * δ ^ (-η) := by
    have hC3 : 3 * C * (Q + 2) ≤ (1 / 4) * δ ^ (-(η / 2)) := by
      linarith [hEv3]
    calc
      T3 = 3 * C * (Q + 2) * δ ^ (-η₀) := hT3_def
      _ ≤ 3 * C * (Q + 2) * δ ^ (-(η / 2)) :=
        mul_le_mul_of_nonneg_left h_δ₀_le_half hT3_nonneg
      _ ≤ (1 / 4) * δ ^ (-(η / 2)) * δ ^ (-(η / 2)) :=
        mul_le_mul_of_nonneg_right hC3 hδph_nonneg
      _ = (1 / 4) * (δ ^ (-(η / 2)) * δ ^ (-(η / 2))) := by ring
      _ = (1 / 4) * δ ^ (-η) := by rw [h_phase_mul]
  have hOne : (1 : ℝ) ≤ (1 / 4) * δ ^ (-η) := by
    linarith [hEv4]
  have hSum : T1 + T2 + T3 + 1 ≤ δ ^ (-η) := by
    linarith [hT1_le, hT2_le, hT3_le, hOne]
  exact hTotal.trans hSum

set_option maxHeartbeats 400000 in
-- Inverting the `atTop` limit of `δ ^ (-slack)` needs a little extra elaboration.
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Conjunct 7 of `Kakeya.randCF_smallness_envelope_uniform`.  It does not involve `CF`. -/
private lemma randCF_uniform_conj7 :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      netGeomConstantC E * Real.exp (10 * Real.exp 1) *
          δ ^ (netGeomConstantM E - netGeomConstantMRaw E)
        ≤ 1/3 := by
  set slack : ℝ := netGeomConstantM E - netGeomConstantMRaw E with hslack_def
  have hslack_pos : 0 < slack := by
    rw [hslack_def]
    have := netGeomConstantM_gt_raw E
    linarith
  set K : ℝ := netGeomConstantC E * Real.exp (10 * Real.exp 1) with hK_def
  have h_tend : Tendsto (fun δ : ℝ => δ ^ slack) (𝓝[>] 0) (𝓝 0) := by
    have h_neg : Tendsto (fun δ : ℝ => δ ^ (-slack)) (𝓝[>] 0) atTop :=
      tendsto_rpow_neg_nhdsGT_zero (by linarith : -slack < 0)
    have h_inv : Tendsto (fun δ : ℝ => (δ ^ (-slack))⁻¹) (𝓝[>] 0) (𝓝 0) :=
      h_neg.inv_tendsto_atTop
    refine h_inv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ_pos_w
    have hδ_pos_real : (0 : ℝ) < δ := hδ_pos_w
    have h_neg_eq : δ ^ (-slack) = (δ ^ slack)⁻¹ :=
      Real.rpow_neg hδ_pos_real.le slack
    rw [h_neg_eq, inv_inv]
  have h_tend_mul : Tendsto (fun δ : ℝ => K * δ ^ slack) (𝓝[>] 0) (𝓝 0) := by
    have := h_tend.const_mul K
    simpa using this
  have h_event : ∀ᶠ δ : ℝ in 𝓝[>] 0, K * δ ^ slack ≤ 1/3 := by
    have h13 : (0 : ℝ) < 1/3 := by norm_num
    have h_lt : ∀ᶠ δ : ℝ in 𝓝[>] 0, K * δ ^ slack < 1/3 := by
      have := h_tend_mul.eventually
        (eventually_lt_nhds (show (0 : ℝ) < 1/3 by norm_num))
      exact this
    filter_upwards [h_lt] with δ hδ
    exact hδ.le
  filter_upwards [h_event] with δ hδ
  exact hδ

set_option maxHeartbeats 1000000 in
-- Merging two eventual statements over a long conjunction is elaboration-heavy.
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Conjuncts 6-7 of `Kakeya.randCF_smallness_envelope_uniform`, uniformly in
`1 ≤ CF ≤ δ ^ (-η₀)`.  Conjunct 6 is the quadratic-in-`CF` Chernoff cap. -/
private lemma randCF_uniform_conj67
    (_hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    {η₀ : ℝ} (hη₀_pos : 0 < η₀) (hη₀_le_quarter : η₀ ≤ η / 4)
    (C_pack_ext : ℕ) (hC_pack_ext_pos : 0 < C_pack_ext) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
      (((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) *
          (((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) +
           (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) +
           (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
        ≤ δ ^ (-η)) ∧
      (netGeomConstantC E * Real.exp (10 * Real.exp 1) *
          δ ^ (netGeomConstantM E - netGeomConstantMRaw E)
        ≤ 1/3) := by
  filter_upwards [randCF_uniform_conj6 (E := E) hη hη₀_pos hη₀_le_quarter
      C_pack_ext hC_pack_ext_pos,
    randCF_uniform_conj7 (E := E)] with δ h6 h7
  intro CF hCF hCF_le
  exact ⟨h6 CF hCF hCF_le, h7⟩

set_option maxHeartbeats 1000000 in
-- Assembling the seven-fold conjunction under a `filter_upwards` is elaboration-heavy.
/-- **`CF`-uniform smallness envelope.**

Same seven conjuncts as `Kakeya.randCF_smallness_envelope`, with the quantifier over the
Frostman constant `CF` moved *inside* the `∀ᶠ δ` and the threshold parameter `M_ED` inlined as
`⌈CF⌉₊ * C_pack_ext + 1` (its only admissible value, given
`⌈CF⌉₊ * C_pack_ext < M_ED` and minimality).

Uniformity is bought by restricting `CF` to the range `CF ≤ δ ^ (-η₀)`, for any fixed
`0 < η₀ ≤ min (η / 4) 1`.  This restriction is not an artefact of the proof:

* conjuncts 1, 3 and 4 are linear in `CF`, so they need `CF ≲ δ ^ (-η/2)`, `CF ≲ δ ^ (-η)` and
  `CF ≲ δ ^ (-η)` respectively;
* conjunct 6 is *quadratic* in `CF` (the Chernoff cap is `M_dim * M_inner` with
  `M_dim ≈ ⌈CF⌉₊ * C_pack_ext`), so it needs `CF ≲ δ ^ (-η/2) / C_pack_ext`;
* conjunct 5 needs `CF ≲ δ ^ (-n)`, whence the auxiliary requirement `η₀ ≤ 1 < n`.

The hypothesis `η₀ ≤ η / 4` is exactly what the quadratic conjunct 6 costs: being quadratic it
needs `2 η₀ ≤ η / 2`.  Replacing the Chernoff cap by the deterministic linear cap of
`Kakeya.isEDUpToMult_translate_product_of_thinBox_pack` would make conjunct 6 linear as well and
so admit `η₀` up to (just under) `η / 2`, at which point the constraint is conjunct 1 — a
*Frostman*-side Chernoff estimate, not an ED-side one.  So the deterministic cap is worth a
factor `2` in the admissible exponent, not a qualitatively wider range: no choice of ED cap
makes this lemma hold for all `CF ≥ 1`. -/
private lemma randCF_smallness_envelope_uniform
    (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η)
    {η₀ : ℝ} (hη₀_pos : 0 < η₀) (hη₀_le_quarter : η₀ ≤ η / 4) (hη₀_le_one : η₀ ≤ 1)
    (c_vol M_vol : ℝ) (hc_vol_pos : 0 < c_vol) (hM_vol_pos : 0 < M_vol)
    (C_pack_ext : ℕ) (hC_pack_ext_pos : 0 < C_pack_ext) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
      ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
      Real.exp 11
          + max ((netGeomConstantC E) * M_vol * CF / c_vol) 1
              * 2 ^ Module.finrank ℝ E
          + ((netGeomConstantM E) + (Module.finrank ℝ E : ℝ)) * Real.log (1 / δ)
            ≤ δ ^ (-(η / 2)) ∧
      δ ≤ c_vol ∧
      (C_pack_ext : ℝ) * (M_vol / c_vol) ^ (2 : ℕ) * CF
            * (2 ^ Module.finrank ℝ E)
          ≤ δ ^ (-η) ∧
      M_vol * δ ^ (Module.finrank ℝ E - 1) *
          (2 ^ Module.finrank ℝ E *
            volume.real (Metric.closedBall (0 : E) 1))
          * 2 * netGeomConstantC E
          ≤ δ ^ (-η) * (c_vol * δ ^ (Module.finrank ℝ E - 1)) *
              (1 / (2 * (⌈CF⌉₊ : ℝ) *
                (volume.real (Metric.closedBall (0 : E) 1))⁻¹)) ∧
      2 * netGeomConstantC E * δ ^ Module.finrank ℝ E ≤
          1 / (2 * (⌈CF⌉₊ : ℝ) *
            (volume.real (Metric.closedBall (0 : E) 1))⁻¹) ∧
      ((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) *
          (((max (⌈CF⌉₊ * C_pack_ext + 1) C_pack_ext : ℕ) : ℝ) +
           (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) +
           (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
        ≤ δ ^ (-η) ∧
      netGeomConstantC E * Real.exp (10 * Real.exp 1) *
          δ ^ (netGeomConstantM E - netGeomConstantMRaw E)
        ≤ 1/3 := by
  filter_upwards [randCF_uniform_conj123 (E := E) hn hη hη₀_pos hη₀_le_quarter
      c_vol M_vol hc_vol_pos hM_vol_pos C_pack_ext hC_pack_ext_pos,
    randCF_uniform_conj45 (E := E) hn hη hη₀_pos hη₀_le_quarter hη₀_le_one
      c_vol M_vol hc_vol_pos hM_vol_pos,
    randCF_uniform_conj67 (E := E) hn hη hη₀_pos hη₀_le_quarter
      C_pack_ext hC_pack_ext_pos]
  with δ h123 h45 h67
  intro CF hCF hCF_le
  obtain ⟨h1, h2, h3⟩ := h123 CF hCF hCF_le
  obtain ⟨h4, h5⟩ := h45 CF hCF hCF_le
  obtain ⟨h6, h7⟩ := h67 CF hCF hCF_le
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The ED failure count against a measurable reference set `K` is a measurable function of
the translation vector. -/
private lemma measurable_edFailCountSet
    {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) {K : Set E}
    (hK : MeasurableSet K) (c : ℝ) :
    Measurable (fun v : E => edFailCountSet s T K c v) := by
  classical
  have hMeas_per : ∀ i : ι,
      MeasurableSet {v : E | BadAgainstSet ((T i).translate v) K c} := by
    intro i
    set S : Set (E × E) := {p | -p.1 + p.2 ∈ (T i).carrier ∧ p.2 ∈ K} with hS_def
    have hS_meas : MeasurableSet S :=
      ((continuous_fst.neg.add continuous_snd).measurable
        (T i).isCompact.measurableSet).inter (measurable_snd hK)
    have hpre : ∀ v : E, Prod.mk v ⁻¹' S = ((T i).translate v).carrier ∩ K := by
      intro v
      ext x
      simp only [hS_def, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff,
        Tube.translate_carrier]
    have hf_ennreal : Measurable
        (fun v : E => volume (((T i).translate v).carrier ∩ K)) := by
      simpa [hpre] using
        measurable_measure_prodMk_left (ν := (volume : Measure E)) hS_meas
    have hSet : {v : E | BadAgainstSet ((T i).translate v) K c}
        = {v : E | ENNReal.ofReal c * volume (T i).carrier
            ≤ volume (((T i).translate v).carrier ∩ K)} := by
      have hvol : ∀ v : E, volume (((T i).translate v).carrier) = volume (T i).carrier :=
        fun v => by rw [Tube.translate_carrier, MeasureTheory.measure_preimage_add]
      ext v
      simp only [BadAgainstSet, Set.mem_setOf_eq, hvol v]
    rw [hSet]
    exact measurableSet_le measurable_const hf_ennreal
  have heq : (fun v : E => edFailCountSet s T K c v)
      = fun v : E => ∑ i ∈ s, if BadAgainstSet ((T i).translate v) K c then (1 : ℝ) else 0 := by
    funext v
    rw [edFailCountSet_eq_filter_card, Finset.card_filter]
    push_cast
    rfl
  rw [heq]
  exact Finset.measurable_sum s fun i _ =>
    Measurable.ite (hMeas_per i) measurable_const measurable_const

/-- Produces translations satisfying the ED-multiplicity and Frostman bounds by a joint
Chernoff and union-bound argument. -/
private lemma randCF_chernoff_witness
    {Ω : Type*} [MeasurableSpace Ω] [HasUniformTranslation Ω E]
    (hR0_law :
      (HasUniformTranslation.measure (Ω := Ω) (E := E)).map
          (fun ω : Ω => HasUniformTranslation.shift (Ω := Ω) (E := E) ω (0 : E))
        = uniformBallMeasure E)
    (hn : 1 < Module.finrank ℝ E)
    {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) (_hδ_lt_one : (δ : ℝ) < 1)
    {η : ℝ} (_hη : 0 < η)
    {CF : ℝ} (hCF : 1 ≤ CF)
    (c_vol M_vol : ℝ) (_hc_vol_pos : 0 < c_vol) (_hM_vol_pos : 0 < M_vol)
    (C_pack_ext : ℕ) (hC_pack_ext_pos : 0 < C_pack_ext)
    (M_ED : ℕ) (hM_ED_pos : 0 < M_ED)
    (_hM_ED_ge_JC_pack : ⌈CF⌉₊ * C_pack_ext < M_ED)
    (_hδ_M_cap_bound :
      ((max M_ED C_pack_ext : ℕ) : ℝ) *
          (((max M_ED C_pack_ext : ℕ) : ℝ) +
           (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) +
           (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
        ≤ δ ^ (-η))
    (hThinBox_pack :
      ∀ {ι_t : Type v} (s_t : Finset ι_t)
        (T_t : ι_t → Tube δ E) (T₀'_t : Tube δ E)
        (_hK_in_B2 : T₀'_t.carrier ⊆ Metric.closedBall (0 : E) (7 / 2))
        (_h_vol_ub :
          volume (Metric.cthickening (99 * δ) T₀'_t.carrier)
            ≤ ENNReal.ofReal (netVolThinConstantM E) *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        (v : E),
        (s_t : Set ι_t).Pairwise
          (fun i j => IsEssentiallyDistinct (T_t i).carrier (T_t j).carrier) →
        (@Finset.filter ι_t
            (fun i => BadAgainstSet ((T_t i).translate v)
              (Metric.cthickening (99 * δ) T₀'_t.carrier)
              (c_vol / (2 * M_vol)))
            (Classical.decPred _) s_t).card ≤ C_pack_ext)
    {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E)
    (_hT_ball : ∀ i, (T i).carrier ⊆ Metric.closedBall 0 1)
    (_hT_ED : (s : Set ι).Pairwise
      (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)))
    (_hT_Frost : ConvexSpaceBody.IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF))
    (_hT_full : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η)
    (hT_vol_lb : ∀ i ∈ s, c_vol * δ ^ (Module.finrank ℝ E - 1) ≤
        volume.real (T i).carrier)
    (hT_vol_ub : ∀ i ∈ s,
        volume.real (T i).carrier ≤ M_vol * δ ^ (Module.finrank ℝ E - 1))
    (hR_translate :
      ∀ (i : ι) (ω : Ω),
        ((HasUniformTranslation.shift (Ω := Ω) (E := E) ω).actShadedTube
          (T i)).carrier
            = ((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0)).carrier)
    (NetF : Finset (ConvexSpaceBody E))
    (C_cover : ℝ) (hC_cover_pos : 0 < C_cover)
    (hδ_residual_bound :
      (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) *
          (max (HasUniformTranslation.uniformConstant Ω E * (⌈CF⌉₊ : ℝ))
            (CF * M_vol / (c_vol *
              volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)) + 1) *
          volume.real
            (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier *
          M_vol * C_cover
        < δ ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol)
    (hNetF_cover :
      ∀ (ω : Fin ⌈CF⌉₊ → Ω)
        (_hBdd : ∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
          ∈ Metric.closedBall (0 : E) 1)
        (K' : ConvexSpaceBody E),
        K' ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) →
        ∃ K ∈ NetF,
          K ≤ ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)) ∧
          densityIn (s ×ˢ (Finset.univ : Finset (Fin ⌈CF⌉₊)))
              (fun p : ι × Fin ⌈CF⌉₊ =>
                ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                    (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K'
            ≤ ENNReal.ofReal C_cover *
              densityIn (s ×ˢ (Finset.univ : Finset (Fin ⌈CF⌉₊)))
                (fun p : ι × Fin ⌈CF⌉₊ =>
                  ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                      (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K)
    (hNetF_subset_B2 : ∀ K ∈ NetF, K.carrier ⊆ Metric.closedBall (0 : E) 2)
    (hTubeContainedSet_meas :
      ∀ K ∈ NetF, ∀ i ∈ s,
        MeasurableSet
          (HasUniformTranslation.tubeContainedSet (Ω := Ω) ((T i).toTube) K.carrier))
    (hs_card_pos : 0 < s.card)
    (hNetF_smallness :
      (NetF.card : ℝ) * Real.exp (10 * Real.exp 1 -
        (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ)) ≤ 1/3) :
    ∃ (ω : Fin ⌈CF⌉₊ → Ω) (M_cap : ℕ),
      ((M_cap : ℝ) + 1 ≤ δ ^ (-η)) ∧
      (∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
              ∈ Metric.closedBall (0 : E) 1) ∧
      IsEDUpToMult (s ×ˢ (Finset.univ : Finset (Fin ⌈CF⌉₊)))
        (fun p : ι × Fin ⌈CF⌉₊ =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
            (T p.1)).carrier) M_cap ∧
      ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin ⌈CF⌉₊)))
        (fun p : ι × Fin ⌈CF⌉₊ =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
            (T p.1)).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
        (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
  classical
  set J : ℕ := ⌈CF⌉₊ with hJ_def
  have hJ_pos : 0 < J := Nat.ceil_pos.mpr (by linarith : (0 : ℝ) < CF)
  haveI : NeZero J := ⟨Nat.pos_iff_ne_zero.mp hJ_pos⟩
  set C_pack : ℕ := C_pack_ext with hC_pack_def
  have _hC_pack_pos : 0 < C_pack := hC_pack_ext_pos
  set M_dim : ℕ := max M_ED C_pack with hM_dim_def
  have hM_dim_pos : 0 < M_dim := lt_of_lt_of_le hM_ED_pos (le_max_left _ _)
  have _hM_ED_le : M_ED ≤ M_dim := le_max_left _ _
  have _hC_pack_le : C_pack ≤ M_dim := le_max_right _ _
  set M_log_term : ℕ := ⌈netGeomConstantM E * Real.log (1/δ)⌉₊ with hM_log_term_def
  set M_const : ℕ := ⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊
    with hM_const_def
  set M_inner : ℕ := M_dim + M_log_term + M_const + 1 with hM_inner_def
  have hM_inner_pos : 0 < M_inner := by simp [hM_inner_def]
  set M_cap : ℕ := M_dim * M_inner with hM_cap_def
  have _hM_cap_pos : 0 < M_cap := by
    rw [hM_cap_def]; exact Nat.mul_pos hM_dim_pos hM_inner_pos
  have hM_cap_bound : (M_cap : ℝ) + 1 ≤ δ ^ (-η) := by
    have hcast : (M_cap : ℝ) =
        ((max M_ED C_pack_ext : ℕ) : ℝ) *
          (((max M_ED C_pack_ext : ℕ) : ℝ) +
           (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ) +
           (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) := by
      simp only [hM_cap_def, hM_inner_def, hM_dim_def, hM_log_term_def,
        hM_const_def, hC_pack_def]
      push_cast
      ring
    rw [hcast]
    exact _hδ_M_cap_bound
  obtain ⟨ω, hω_bdd, hω_frost, hω_ED⟩ : ∃ (ω : Fin J → Ω),
      (∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
              ∈ Metric.closedBall (0 : E) 1) ∧
      ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
            (T p.1)).toConvexSpaceBody)
        (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
        (ENNReal.ofReal ((δ : ℝ) ^ (-η))) ∧
      IsEDUpToMult (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p : ι × Fin J =>
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube
            (T p.1)).carrier) M_cap := by
      set μ : Measure (Fin J → Ω) :=
        HasUniformTranslation.productMeasure Ω E J with hμ_def
      set μE : Measure (Fin J → E) :=
        HasUniformTranslation.productMeasure E E J with hμE_def
      set c_bridge : ℝ := c_vol / (2 * M_vol) with hc_bridge_def
      have hc_bridge_pos : 0 < c_bridge := by
        rw [hc_bridge_def]
        exact div_pos _hc_vol_pos (by linarith)
      have _hM_dim_ge : (J : ℝ) * (C_pack : ℝ) < (M_dim : ℝ) := by
        have h1 : (J : ℝ) * (C_pack : ℝ) < (M_ED : ℝ) := by
          rw [hJ_def, hC_pack_def]
          exact_mod_cast _hM_ED_ge_JC_pack
        exact h1.trans_le (by exact_mod_cast _hM_ED_le)
      have _hB_s : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
        fun i _ => _hT_ball i
      have hδ_small_ed :
          (netGeomConstantC E) * δ ^ (-(netGeomConstantM E)) *
            Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) ≤ 1 / 3 := by
        have hC0_pos : 0 < netGeomConstantC E := netGeomConstantC_pos (E := E)
        set C₀ : ℝ := netGeomConstantC E with hC0_def
        set M₀ : ℝ := netGeomConstantM E with hM0_def
        have h3C0_pos : 0 < 3 * C₀ := by positivity
        have hδ_pow_pos : (0 : ℝ) < δ ^ M₀ := Real.rpow_pos_of_pos hδ_pos _
        have h_log_ge : M₀ * Real.log (1 / δ) ≤ (M_log_term : ℝ) := by
          rw [hM_log_term_def]; exact Nat.le_ceil _
        have h_const_ge : 10 * Real.exp 1 + Real.log (3 * C₀) ≤ (M_const : ℝ) := by
          rw [hM_const_def]; exact Nat.le_ceil _
        have hM_dim_nn : (0 : ℝ) ≤ (M_dim : ℝ) := Nat.cast_nonneg _
        have h_inner_cast :
            (M_inner : ℝ) = (M_dim : ℝ) + (M_log_term : ℝ) + (M_const : ℝ) + 1 := by
          rw [hM_inner_def]; push_cast; ring
        have h_exp_log_term_le : Real.exp (-(M_log_term : ℝ)) ≤ (δ : ℝ) ^ M₀ := by
          rw [one_div, Real.log_inv] at h_log_ge
          rw [Real.rpow_def_of_pos hδ_pos M₀]
          exact Real.exp_le_exp.mpr (by linarith)
        have h_exp_const_le :
            Real.exp (10 * Real.exp 1 - (M_const : ℝ)) ≤ 1 / (3 * C₀) := by
          calc Real.exp (10 * Real.exp 1 - (M_const : ℝ))
              ≤ Real.exp (-Real.log (3 * C₀)) := Real.exp_le_exp.mpr (by linarith)
            _ = 1 / (3 * C₀) := by rw [Real.exp_neg, Real.exp_log h3C0_pos, one_div]
        have h_exp_le : Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) ≤
            (δ : ℝ) ^ M₀ * (1 / (3 * C₀)) := by
          calc Real.exp (10 * Real.exp 1 - (M_inner : ℝ))
              ≤ Real.exp (-(M_log_term : ℝ)) *
                  Real.exp (10 * Real.exp 1 - (M_const : ℝ)) := by
                rw [← Real.exp_add]
                exact Real.exp_le_exp.mpr (by rw [h_inner_cast]; linarith)
            _ ≤ (δ : ℝ) ^ M₀ * (1 / (3 * C₀)) :=
                mul_le_mul h_exp_log_term_le h_exp_const_le (Real.exp_pos _).le
                  hδ_pow_pos.le
        have h_rhs_simp :
            C₀ * (δ : ℝ) ^ (-M₀) * ((δ : ℝ) ^ M₀ * (1 / (3 * C₀))) = 1 / 3 := by
          have hC0_ne : C₀ ≠ 0 := ne_of_gt hC0_pos
          have h_rpow_cancel : (δ : ℝ) ^ (-M₀) * (δ : ℝ) ^ M₀ = 1 := by
            rw [← Real.rpow_add hδ_pos]; simp
          field_simp
          rw [show (δ : ℝ) ^ (-M₀) * (δ : ℝ) ^ M₀ = 1 from h_rpow_cancel]
        calc C₀ * (δ : ℝ) ^ (-M₀) * Real.exp (10 * Real.exp 1 - (M_inner : ℝ))
            ≤ C₀ * (δ : ℝ) ^ (-M₀) * ((δ : ℝ) ^ M₀ * (1 / (3 * C₀))) :=
              mul_le_mul_of_nonneg_left h_exp_le (by positivity)
          _ = 1 / 3 := h_rhs_simp
      have hM_dim_ge_integral :
          ∀ (T₀'_t : Tube δ E),
            T₀'_t.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) →
            volume (Metric.cthickening (99 * δ) T₀'_t.carrier)
              ≤ ENNReal.ofReal (netVolThinConstantM E) *
                (δ : ENNReal) ^ (Module.finrank ℝ E - 1) →
            (J : ℝ) *
              (∫ v : E,
                edFailCountSet s (fun i => (T i).toTube)
                  (Metric.cthickening (99 * δ) T₀'_t.carrier) c_bridge
                  ((1 : ℝ) • v)
                  ∂(uniformBallMeasure E))
                < (M_dim : ℝ) := by
        intro T₀'_t hK_in_B2 h_vol_ub
        simp only [one_smul]
        have hpair : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct ((T i).toTube).carrier
              ((T j).toTube).carrier) := _hT_ED
        have hpoint : ∀ v : E,
            edFailCountSet s (fun i => (T i).toTube)
                (Metric.cthickening (99 * δ) T₀'_t.carrier) c_bridge v
              ≤ (C_pack : ℝ) := by
          intro v
          unfold edFailCountSet
          exact_mod_cast hThinBox_pack (ι_t := ι) s (fun i => (T i).toTube)
            T₀'_t hK_in_B2 h_vol_ub v hpair
        have hint_le :
            (∫ v : E,
                edFailCountSet s (fun i => (T i).toTube)
                  (Metric.cthickening (99 * δ) T₀'_t.carrier) c_bridge v
                  ∂(uniformBallMeasure E))
              ≤ (C_pack : ℝ) := by
          calc (∫ v : E,
                  edFailCountSet s (fun i => (T i).toTube)
                    (Metric.cthickening (99 * δ) T₀'_t.carrier) c_bridge v
                    ∂(uniformBallMeasure E))
                ≤ ∫ _ : E, (C_pack : ℝ) ∂(uniformBallMeasure E) := by
                  refine MeasureTheory.integral_mono_of_nonneg
                    (Filter.Eventually.of_forall (fun v =>
                      edFailCountSet_nonneg s (fun i => (T i).toTube)
                        (Metric.cthickening (99 * δ) T₀'_t.carrier) c_bridge v))
                    (MeasureTheory.integrable_const _) ?_
                  exact Filter.Eventually.of_forall hpoint
            _ = (C_pack : ℝ) := by
                  rw [MeasureTheory.integral_const]; simp
        have hJ_nn : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
        calc (J : ℝ) *
              (∫ v : E,
                edFailCountSet s (fun i => (T i).toTube)
                  (Metric.cthickening (99 * δ) T₀'_t.carrier) c_bridge v
                  ∂(uniformBallMeasure E))
              ≤ (J : ℝ) * (C_pack : ℝ) :=
                mul_le_mul_of_nonneg_left hint_le hJ_nn
          _ < (M_dim : ℝ) := _hM_dim_ge
      haveI : Nontrivial E :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (by omega : 0 < Module.finrank ℝ E)
      obtain ⟨NetED, hNetED_union, hNetED_meas, hNetED_sub, hNetED_vol, _hNetED_cover,
          hNetED_chernoff⟩ :=
        exists_chernoff_tube_net_with_ed_approx_thin (E := E) (c := c_bridge)
          hc_bridge_pos hδ_pos _hδ_lt_one hn s T _hB_s _hT_ED Ω J M_dim hM_dim_pos
          (1 : ℝ) (by norm_num : (0 : ℝ) < 1)
          hM_dim_ge_integral
          M_inner hM_inner_pos hδ_small_ed
      let BadEDEvent : Tube δ E → Set (Fin J → E) := fun T₀' =>
        {ω : Fin J → E |
          ∑ j : Fin J, productEdFailCountSet s (fun i => (T i).toTube)
            (Metric.cthickening (99 * δ) T₀'.carrier) c_bridge 1 J j ω
              > (M_cap : ℝ)}
      set BadED : Set (Fin J → E) := ⋃ T₀' ∈ NetED, BadEDEvent T₀' with hBadED_def
      have _hBadED_le_one_third : μE BadED ≤ ENNReal.ofReal (1/3) := by
        have hUnionBd : μE BadED ≤ ∑ T₀' ∈ NetED, μE (BadEDEvent T₀') := by
          rw [hBadED_def]
          exact MeasureTheory.measure_biUnion_finset_le NetED BadEDEvent
        have hM_dim_pos_real : (0 : ℝ) < (M_dim : ℝ) := by exact_mod_cast hM_dim_pos
        have hM_cap_eq : (M_cap : ℝ) / (M_dim : ℝ) = (M_inner : ℝ) := by
          have hne : (M_dim : ℝ) ≠ 0 := ne_of_gt hM_dim_pos_real
          rw [hM_cap_def]
          push_cast
          field_simp
        have hChernoffED : ∀ T₀' ∈ NetED,
            (μE (BadEDEvent T₀')).toReal ≤
              Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) := by
          intro T₀' hT₀'
          set K_thick : Set E := Metric.cthickening (99 * δ) T₀'.carrier
            with hK_thick_def
          have hK_meas : MeasurableSet K_thick :=
            isClosed_cthickening.measurableSet
          have hmeas_ed : Measurable
              (fun v : E =>
                edFailCountSet s (fun i => (T i).toTube) K_thick c_bridge v) :=
            measurable_edFailCountSet E s (fun i => (T i).toTube) hK_meas c_bridge
          have hM_upper : ∀ v : E,
              edFailCountSet s (fun i => (T i).toTube) K_thick c_bridge v
                ≤ (M_dim : ℝ) := by
            intro v
            have hpair : (s : Set ι).Pairwise
                (fun i j =>
                  IsEssentiallyDistinct ((fun i => (T i).toTube) i).carrier
                    ((fun i => (T i).toTube) j).carrier) := _hT_ED
            unfold edFailCountSet
            exact_mod_cast (hThinBox_pack s (fun i => (T i).toTube) T₀'
              (hNetED_sub T₀' hT₀') (hNetED_vol T₀' hT₀') v hpair).trans _hC_pack_le
          have hJm : (J : ℝ) *
              (∫ v : E,
                edFailCountSet s (fun i => (T i).toTube) K_thick c_bridge
                  ((1 : ℝ) • v) ∂(uniformBallMeasure E)) < (M_dim : ℝ) :=
            hNetED_chernoff T₀' hT₀'
          have hCh :
              ((HasUniformTranslation.productMeasure E E J)
                  {ω | ∑ j : Fin J,
                    productEdFailCountSet s (fun i => (T i).toTube)
                      K_thick c_bridge 1 J j ω > (M_cap : ℝ)}).toReal ≤
                Real.exp (10 * Real.exp 1 - (M_cap : ℝ) / (M_dim : ℝ)) :=
            productEdFailCountSet_chernoff_tail (E := E) hδ_pos
              s (fun i => (T i).toTube) K_thick c_bridge
              (1 : ℝ) (by norm_num : (0 : ℝ) < 1) (M_dim : ℝ) hM_dim_pos_real
              hM_upper hmeas_ed hJm (M_cap : ℝ)
          rw [hM_cap_eq] at hCh
          rwa [hμE_def]
        have hsum_real_bd : (∑ T₀' ∈ NetED, μE (BadEDEvent T₀')).toReal ≤ 1/3 := by
          rw [ENNReal.toReal_sum (fun _ _ => MeasureTheory.measure_ne_top _ _)]
          calc ∑ T₀' ∈ NetED, (μE (BadEDEvent T₀')).toReal
              ≤ ∑ T₀' ∈ NetED, Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) :=
                Finset.sum_le_sum (fun T₀' hT₀' => hChernoffED T₀' hT₀')
            _ = (NetED.card : ℝ) * Real.exp (10 * Real.exp 1 - (M_inner : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 1/3 := hNetED_union
        have hsum_ne_top : (∑ T₀' ∈ NetED, μE (BadEDEvent T₀')) ≠ ⊤ :=
          ENNReal.sum_ne_top.mpr (fun _ _ => MeasureTheory.measure_ne_top _ _)
        rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hsum_ne_top hUnionBd)]
        exact ENNReal.ofReal_le_ofReal
          ((ENNReal.toReal_mono hsum_ne_top hUnionBd).trans hsum_real_bd)
      have hBadED_Ω_le_one_third :
          μ {ω : Fin J → Ω |
              ∃ T₀' ∈ NetED, ∑ j : Fin J,
                productEdFailCountSet s (fun i => (T i).toTube)
                  (Metric.cthickening (99 * δ) T₀'.carrier) c_bridge 1 J j
                  (fun j => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)
                > (M_cap : ℝ)} ≤ ENNReal.ofReal (1/3) := by
        set Φ : (Fin J → Ω) → (Fin J → E) :=
          fun ω j => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
          with hΦ_def
        have hR0_meas :
            Measurable (fun ω' : Ω =>
              HasUniformTranslation.shift (Ω := Ω) (E := E) ω' (0 : E)) :=
          HasUniformTranslation.measurable_apply (Ω := Ω) (E := E) (0 : E)
        have hΦ_meas : Measurable Φ := by
          refine measurable_pi_iff.mpr (fun j => ?_)
          exact hR0_meas.comp (measurable_pi_apply j)
        have hset_eq :
            {ω : Fin J → Ω |
                ∃ T₀' ∈ NetED, ∑ j : Fin J,
                  productEdFailCountSet s (fun i => (T i).toTube)
                    (Metric.cthickening (99 * δ) T₀'.carrier) c_bridge 1 J j
                    (fun j => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)
                  > (M_cap : ℝ)} = Φ ⁻¹' BadED := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_preimage, hBadED_def,
            Set.mem_iUnion, exists_prop]
          rfl
        have hmeas_BadED : MeasurableSet BadED := by
          rw [hBadED_def]
          refine MeasurableSet.biUnion NetED.countable_toSet (fun T₀' _hT₀' => ?_)
          set K_thick : Set E := Metric.cthickening (99 * δ) T₀'.carrier
            with hK_thick_def
          have hK_meas : MeasurableSet K_thick :=
            isClosed_cthickening.measurableSet
          have hmeas_ed : Measurable
              (fun v : E =>
                edFailCountSet s (fun i => (T i).toTube) K_thick c_bridge v) :=
            measurable_edFailCountSet E s (fun i => (T i).toTube) hK_meas c_bridge
          have hsum_meas : Measurable
              (fun ω' : Fin J → E => ∑ j : Fin J,
                productEdFailCountSet s (fun i => (T i).toTube) K_thick
                  c_bridge 1 J j ω') := by
            refine Finset.measurable_sum _ (fun j _ => ?_)
            exact productEdFailCountSet_measurable s (fun i => (T i).toTube)
              K_thick c_bridge 1 hmeas_ed J j
          exact hsum_meas measurableSet_Ioi
        rw [hset_eq]
        rw [show μ = HasUniformTranslation.productMeasure Ω E J from hμ_def]
        rw [← MeasureTheory.Measure.map_apply hΦ_meas hmeas_BadED]
        have hpush :
            (HasUniformTranslation.productMeasure Ω E J).map Φ
              = HasUniformTranslation.productMeasure E E J := by
          unfold HasUniformTranslation.productMeasure
          have hΦ_eq : Φ = (fun ω : Fin J → Ω => fun j : Fin J =>
              (fun ω' : Ω => HasUniformTranslation.shift (Ω := Ω) (E := E) ω' (0 : E))
                (ω j)) := rfl
          rw [hΦ_eq]
          rw [MeasureTheory.Measure.pi_map_pi
            (μ := fun _ : Fin J => HasUniformTranslation.measure (Ω := Ω) (E := E))
            (f := fun _ : Fin J => fun ω' : Ω =>
              HasUniformTranslation.shift (Ω := Ω) (E := E) ω' (0 : E))
            (hμ := by
              intro _
              rw [hR0_law]
              infer_instance)
            (hf := fun _ => hR0_meas.aemeasurable)]
          congr 1
          funext _
          exact hR0_law
        rw [hpush]
        rw [← hμE_def]
        exact _hBadED_le_one_third
      have hBadOutside_zero :
          μ {ω : Fin J → Ω |
              ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                    Metric.closedBall (0 : E) 1} = 0 := by
        have hBall_meas : MeasurableSet (Metric.closedBall (0 : E) 1) :=
          Metric.isClosed_closedBall.measurableSet
        have hCompl_meas : MeasurableSet ((Metric.closedBall (0 : E) 1)ᶜ) :=
          hBall_meas.compl
        have hR0_meas :
            Measurable (fun ω' : Ω =>
              HasUniformTranslation.shift (Ω := Ω) (E := E) ω' (0 : E)) :=
          HasUniformTranslation.measurable_apply (Ω := Ω) (E := E) (0 : E)
        have hUnion_eq :
            {ω : Fin J → Ω |
                ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                      Metric.closedBall (0 : E) 1} =
              ⋃ j : Fin J,
                {ω : Fin J → Ω |
                  HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                    Metric.closedBall (0 : E) 1} := by
          ext ω; simp
        have hcoord_zero : ∀ j : Fin J,
            μ {ω : Fin J → Ω |
                HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                  Metric.closedBall (0 : E) 1} = 0 := by
          intro j
          have hpre :
              {ω : Fin J → Ω |
                  HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                    Metric.closedBall (0 : E) 1} =
                (Function.eval j : (Fin J → Ω) → Ω) ⁻¹'
                  ((fun ω' : Ω =>
                      HasUniformTranslation.shift (Ω := Ω) (E := E) ω' (0 : E))
                    ⁻¹' ((Metric.closedBall (0 : E) 1)ᶜ)) := by
            ext ω; simp [Function.eval]
          rw [hpre]
          have hmeas_eval : Measurable (Function.eval j : (Fin J → Ω) → Ω) :=
            measurable_pi_apply j
          have hpre_meas : MeasurableSet
              ((fun ω' : Ω =>
                  HasUniformTranslation.shift (Ω := Ω) (E := E) ω' (0 : E))
                ⁻¹' ((Metric.closedBall (0 : E) 1)ᶜ)) := hR0_meas hCompl_meas
          rw [← MeasureTheory.Measure.map_apply hmeas_eval hpre_meas]
          rw [show μ = HasUniformTranslation.productMeasure Ω E J from hμ_def]
          rw [HasUniformTranslation.productMeasure_map_eval]
          rw [← MeasureTheory.Measure.map_apply hR0_meas hCompl_meas, hR0_law]
          change ((volume (Metric.closedBall (0 : E) 1))⁻¹ •
                volume.restrict (Metric.closedBall (0 : E) 1))
                  ((Metric.closedBall (0 : E) 1)ᶜ) = 0
          rw [Measure.smul_apply, Measure.restrict_apply hCompl_meas]
          simp
        rw [hUnion_eq]
        exact measure_iUnion_null_iff.mpr hcoord_zero
      have hBadFrostman_le_one_third :
          ∃ (NetF : Finset (ConvexSpaceBody E)) (C_cover : ℝ) (_hC_cover_pos : 0 < C_cover)
            (_hNetF_cover :
              ∀ (ω : Fin J → Ω)
                (_hBdd : ∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
                  ∈ Metric.closedBall (0 : E) 1)
                (K' : ConvexSpaceBody E),
                K' ≤ ConvexSpaceBody.cthickening 1
                      (ConvexSpaceBody.closedUnitBall (E := E)) →
                ∃ K ∈ NetF,
                  K ≤ ConvexSpaceBody.cthickening 1
                        (ConvexSpaceBody.closedUnitBall (E := E)) ∧
                  densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                      (fun p : ι × Fin J =>
                        ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                            (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K'
                    ≤ ENNReal.ofReal C_cover *
                      densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                        (fun p : ι × Fin J =>
                          ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                              (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K),
            μ {ω : Fin J → Ω |
                ∃ K ∈ NetF,
                  ¬ (densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                        (fun p : ι × Fin J =>
                          ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                              (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K
                      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
                        densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                          (fun p : ι × Fin J =>
                            ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                                (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
                          (ConvexSpaceBody.cthickening 1
                            (ConvexSpaceBody.closedUnitBall (E := E))))}
              ≤ ENNReal.ofReal (1/3) := by
        refine ⟨NetF, C_cover, hC_cover_pos, hNetF_cover, ?_⟩
        let BadFrostmanEvent : ConvexSpaceBody E → Set (Fin J → Ω) := fun K =>
          {ω : Fin J → Ω |
            ¬ (densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                  (fun p : ι × Fin J =>
                    ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                        (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K
                ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
                  densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                    (fun p : ι × Fin J =>
                      ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                          (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
                    (ConvexSpaceBody.cthickening 1
                      (ConvexSpaceBody.closedUnitBall (E := E))))}
        set BadFrostman : Set (Fin J → Ω) :=
          ⋃ K ∈ NetF, BadFrostmanEvent K with hBadF_def
        have hset_eq :
            {ω : Fin J → Ω |
              ∃ K ∈ NetF,
                ¬ (densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                      (fun p : ι × Fin J =>
                        ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                            (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K
                    ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
                      densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                        (fun p : ι × Fin J =>
                          ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                              (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
                        (ConvexSpaceBody.cthickening 1
                          (ConvexSpaceBody.closedUnitBall (E := E))))}
              = BadFrostman := by
          ext ω
          simp only [BadFrostmanEvent, hBadF_def, Set.mem_iUnion, Set.mem_setOf_eq,
            exists_prop]
        rw [hset_eq]
        have hUnionBd :
            μ BadFrostman ≤ ∑ K ∈ NetF, μ (BadFrostmanEvent K) := by
          rw [hBadF_def]
          exact MeasureTheory.measure_biUnion_finset_le NetF BadFrostmanEvent
        have hChernoffF : ∀ K ∈ NetF,
            (μ (BadFrostmanEvent K)).toReal ≤
              Real.exp (10 * Real.exp 1 - (M_log_term : ℝ)) := by
          intro K _hK
          by_cases hvolK_small :
              volume.real K.carrier < c_vol * δ ^ (Module.finrank ℝ E - 1)
          · have hBadEmpty : BadFrostmanEvent K = ∅ := by
              ext ω
              simp only [Set.mem_empty_iff_false, iff_false]
              intro hω
              change ¬ _ ≤ _ at hω
              apply hω
              have h_no_contain :
                  ∀ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)),
                    ¬ ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                        (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody ≤ K := by
                rintro ⟨i, j⟩ hp hcont
                rw [Finset.mem_product] at hp
                obtain ⟨hi, _⟩ := hp
                have h_carr_sub :
                    ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                        (ω j)).actShadedTube (T i)).toConvexSpaceBody.carrier ⊆
                      K.carrier := hcont
                have h_F_le_K :
                    volume.real
                        ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                          (ω j)).actShadedTube (T i)).toConvexSpaceBody.carrier
                      ≤ volume.real K.carrier :=
                  measureReal_mono h_carr_sub
                    K.isCompact.measure_lt_top.ne
                have h_vol_eq :
                    volume.real
                        ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                          (ω j)).actShadedTube (T i)).toConvexSpaceBody.carrier
                      = volume.real (T i).carrier := by
                  rw [Translation.actShadedTube_toConvexBody]
                  change (volume _).toReal = (volume _).toReal
                  exact congrArg ENNReal.toReal
                    (Translation.volume_actConvexBody _ _)
                rw [h_vol_eq] at h_F_le_K
                have h_T_lb := hT_vol_lb i hi
                linarith
              have h_densityIn_zero :
                  densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                    (fun p : ι × Fin J =>
                      ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                          (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K
                    = 0 := by
                simp only [densityIn]
                rw [Finset.filter_false_of_mem h_no_contain]
                simp
              rw [h_densityIn_zero]
              exact bot_le
            rw [hBadEmpty]
            simp only [MeasureTheory.measure_empty, ENNReal.toReal_zero]
            exact (Real.exp_pos _).le
          · push Not at hvolK_small
            have hvolK_pos : 0 < volume.real K.carrier := by
              have hpow : 0 < δ ^ (Module.finrank ℝ E - 1) := pow_pos hδ_pos _
              have : 0 < c_vol * δ ^ (Module.finrank ℝ E - 1) :=
                mul_pos _hc_vol_pos hpow
              linarith
            have hK_in_B2 : K.carrier ⊆ Metric.closedBall (0 : E) 2 :=
              hNetF_subset_B2 K _hK
            have hK_meas : MeasurableSet K.carrier := K.isCompact.measurableSet
            let xT : ι → E := fun i => (T i).x
            have hxT_mem : ∀ i ∈ s, xT i ∈ ((T i).toTube).carrier := by
              intro i _hi
              rw [(T i).carrier_eq]
              refine Set.mem_iUnion₂.mpr ⟨(T i).x, left_mem_segment ℝ _ _, ?_⟩
              exact Metric.mem_closedBall_self (le_of_lt hδ_pos)
            have hxBall : ∀ i ∈ s, xT i ∈ Metric.closedBall (0 : E) 1 := by
              intro i hi
              exact _hT_ball i (hxT_mem i hi)
            have hMeas : ∀ i ∈ s,
                MeasurableSet
                  (HasUniformTranslation.tubeContainedSet (Ω := Ω) ((T i).toTube)
                    K.carrier) :=
              fun i hi => hTubeContainedSet_meas K _hK i hi
            have huc_pos : 0 < HasUniformTranslation.uniformConstant Ω E :=
              HasUniformTranslation.uniformConstantPos (Ω := Ω) (E := E)
            have huc_nn : 0 ≤ HasUniformTranslation.uniformConstant Ω E := huc_pos.le
            have hJ_nn : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
            have hcard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hs_card_pos
            have hcard_nn : 0 ≤ (s.card : ℝ) := hcard_pos.le
            have hvolB1_pos :
                0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
              rw [ConvexSpaceBody.closedUnitBall_carrier]
              refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
              exact (Metric.measure_closedBall_pos volume 0 one_pos).ne'
            set C_pack_raw : ℝ :=
              CF * M_vol /
                (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
              with hC_pack_raw_def
            have hC_pack_raw_pos : 0 < C_pack_raw := by
              rw [hC_pack_raw_def]
              refine div_pos (mul_pos (lt_of_lt_of_le one_pos hCF) _hM_vol_pos) ?_
              exact mul_pos _hc_vol_pos hvolB1_pos
            have hC_pack_raw_nn : 0 ≤ C_pack_raw := hC_pack_raw_pos.le
            set M_K : ℝ :=
              (max (HasUniformTranslation.uniformConstant Ω E * (J : ℝ))
                  C_pack_raw + 1) *
                (s.card : ℝ) * volume.real K.carrier
              with hM_K_def
            have hmax_nn :
                0 ≤ max (HasUniformTranslation.uniformConstant Ω E * (J : ℝ))
                    C_pack_raw := le_max_of_le_right hC_pack_raw_nn
            have hmax_pos :
                0 < max (HasUniformTranslation.uniformConstant Ω E * (J : ℝ))
                    C_pack_raw + 1 := by linarith
            have hM_K_pos : 0 < M_K := by
              rw [hM_K_def]
              exact mul_pos (mul_pos hmax_pos hcard_pos) hvolK_pos
            have hT_in_B1 :
                ∀ i ∈ s, (T i).toConvexSpaceBody ≤ ConvexSpaceBody.closedUnitBall (E := E) := by
              intro i _hi x hx
              have hx_carr : x ∈ (T i).carrier := hx
              have hball : x ∈ Metric.closedBall (0 : E) 1 := _hT_ball i hx_carr
              change x ∈ (ConvexSpaceBody.closedUnitBall (E := E)).carrier
              rw [ConvexSpaceBody.closedUnitBall_carrier]
              exact hball
            have hCF_nn : 0 ≤ CF := le_trans zero_le_one hCF
            have hM_vol_nn : 0 ≤ M_vol := _hM_vol_pos.le
            have hXM :
                ∀ (j : Fin J) (ω : Fin J → Ω),
                  (HasUniformTranslation.productTubeContainedCount
                      (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                      J j ω : ℝ) ≤ M_K := by
              intro j ωall
              have hED :
                  HasUniformTranslation.tubeContainedCount (Ω := Ω) s
                      (fun i => (T i).toTube) K.carrier (ωall j) *
                      (c_vol *
                        volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
                    ≤ CF * M_vol * (s.card : ℝ) * volume.real K.carrier :=
                Kakeya.HasUniformTranslation.tubeContainedCount_le_ED_packing
                  (Ω := Ω) (E := E) hδ_pos s T CF hCF_nn _hT_Frost hT_in_B1
                  c_vol M_vol _hc_vol_pos hM_vol_nn hT_vol_lb hT_vol_ub
                  hR_translate K (ωall j)
              have hpos :
                  0 < c_vol *
                    volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
                mul_pos _hc_vol_pos hvolB1_pos
              have hXj_le_pack :
                  HasUniformTranslation.tubeContainedCount (Ω := Ω) s
                      (fun i => (T i).toTube) K.carrier (ωall j)
                    ≤ C_pack_raw * (s.card : ℝ) * volume.real K.carrier := by
                have hrhs_eq :
                    C_pack_raw * (s.card : ℝ) * volume.real K.carrier =
                      (CF * M_vol * (s.card : ℝ) * volume.real K.carrier) /
                        (c_vol *
                          volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) := by
                  rw [hC_pack_raw_def]; field_simp
                rw [hrhs_eq, le_div_iff₀ hpos]
                linarith
              have h_le_max_p1 :
                  C_pack_raw ≤
                    max (HasUniformTranslation.uniformConstant Ω E * (J : ℝ))
                      C_pack_raw + 1 := by
                linarith [le_max_right
                  (HasUniformTranslation.uniformConstant Ω E * (J : ℝ)) C_pack_raw]
              have h_pack_le_M_K :
                  C_pack_raw * (s.card : ℝ) * volume.real K.carrier ≤ M_K := by
                rw [hM_K_def]
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right h_le_max_p1 hcard_nn) hvolK_pos.le
              change HasUniformTranslation.tubeContainedCount (Ω := Ω) s
                  (fun i => (T i).toTube) K.carrier (ωall j) ≤ M_K
              exact le_trans hXj_le_pack h_pack_le_M_K
            have hJmM :
                (J : ℝ) *
                  (HasUniformTranslation.uniformConstant Ω E *
                    (s.card : ℝ) * volume.real K.carrier) < M_K := by
              rw [hM_K_def]
              have h_lt :
                  HasUniformTranslation.uniformConstant Ω E * (J : ℝ) <
                    max (HasUniformTranslation.uniformConstant Ω E * (J : ℝ))
                      C_pack_raw + 1 := by
                linarith [le_max_left
                  (HasUniformTranslation.uniformConstant Ω E * (J : ℝ)) C_pack_raw]
              linarith [mul_lt_mul_of_pos_right
                (mul_lt_mul_of_pos_right h_lt hcard_pos) hvolK_pos]
            set S : ℝ := (M_log_term : ℝ) * M_K with hS_def
            have hBadF_subset :
                BadFrostmanEvent K ⊆
                  {ω : Fin J → Ω |
                      ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                            Metric.closedBall (0 : E) 1} ∪
                  {ω : Fin J → Ω | ∑ j : Fin J,
                    HasUniformTranslation.productTubeContainedCount
                      (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                      J j ω > S} := by
              intro ω hω
              change ¬ _ ≤ _ at hω
              by_cases hBdd :
                  ∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
                        ∈ Metric.closedBall (0 : E) 1
              · right
                push Not at hω
                change (S : ℝ) < ∑ j : Fin J,
                  HasUniformTranslation.productTubeContainedCount
                    (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                    J j ω
                set F : ι × Fin J → ConvexSpaceBody E := fun p =>
                  ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                    (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody
                  with hF_def
                set B2 : ConvexSpaceBody E :=
                  ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))
                  with hB2_def
                set sJ : Finset (ι × Fin J) :=
                  s ×ˢ (Finset.univ : Finset (Fin J)) with hsJ_def
                have hLB :
                    (densityIn sJ F B2).toReal * volume.real B2.carrier
                      ≥ (s.card : ℝ) * (J : ℝ) *
                        (c_vol * δ ^ (Module.finrank ℝ E - 1)) := by
                  have := HasUniformTranslation.productTubeContainedCount_density_lb_on_Bdd
                    (Ω := Ω) (E := E) hδ_pos s T c_vol _hc_vol_pos
                    hT_in_B1 hT_vol_lb hR_translate J ω hBdd
                  simpa [hF_def, hB2_def] using this
                have hω_ENN : ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
                      densityIn sJ F B2 < densityIn sJ F K := by
                  simpa [hF_def, hsJ_def, hB2_def] using hω
                have hdensFK_ne_top : densityIn sJ F K ≠ ⊤ :=
                  densityIn_ne_top sJ F K
                have hdensFB2_ne_top : densityIn sJ F B2 ≠ ⊤ :=
                  densityIn_ne_top sJ F B2
                have hω' : ((δ : ℝ) ^ (-η) / C_cover) *
                    (densityIn sJ F B2).toReal <
                    (densityIn sJ F K).toReal := by
                  have hxnn : 0 ≤ ((δ : ℝ) ^ (-η) / C_cover) :=
                    div_nonneg (Real.rpow_pos_of_pos hδ_pos _).le hC_cover_pos.le
                  have hmul_ne_top : ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
                      densityIn sJ F B2 ≠ ⊤ :=
                    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdensFB2_ne_top
                  have := (ENNReal.toReal_lt_toReal hmul_ne_top hdensFK_ne_top).mpr hω_ENN
                  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hxnn] at this
                  exact this
                have hvolB2_pos : 0 < volume.real B2.carrier := by
                  have hB2_carrier : B2.carrier = Metric.closedBall (0 : E) 2 := by
                    rw [hB2_def]
                    change Metric.cthickening 1
                      (ConvexSpaceBody.closedUnitBall (E := E)).carrier =
                        Metric.closedBall (0 : E) 2
                    rw [ConvexSpaceBody.closedUnitBall_carrier,
                      cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1)
                        (by norm_num : (0:ℝ) ≤ 1)]
                    norm_num
                  rw [hB2_carrier]
                  refine ENNReal.toReal_pos ?_
                    MeasureTheory.measure_closedBall_lt_top.ne
                  exact (Metric.measure_closedBall_pos volume 0
                    (by norm_num : (0:ℝ) < 2)).ne'
                have hdensK_eq :
                    (densityIn sJ F K).toReal * volume.real K.carrier =
                      ∑ p ∈ sJ.filter (fun p => F p ≤ K),
                        volume.real (F p).carrier := by
                  have hENN :=
                    (Kakeya.sum_volume_eq_densityIn_mul_volume sJ F K).symm
                  have hsum_ne : ∀ p ∈ sJ.filter (fun p => F p ≤ K),
                      volume (F p).carrier ≠ ⊤ := fun p _ =>
                    (F p).isCompact.measure_lt_top.ne
                  have h1 : ((densityIn sJ F K) * volume K.carrier).toReal =
                      (densityIn sJ F K).toReal * volume.real K.carrier := by
                    rw [ENNReal.toReal_mul]; rfl
                  have h2 :
                      (∑ p ∈ sJ.filter (fun p => F p ≤ K),
                        volume (F p).carrier).toReal =
                      ∑ p ∈ sJ.filter (fun p => F p ≤ K),
                        volume.real (F p).carrier :=
                    ENNReal.toReal_sum hsum_ne
                  rw [← h1, hENN, h2]
                have hvolF_le : ∀ p ∈ sJ.filter (fun p => F p ≤ K),
                    volume.real (F p).carrier ≤
                      M_vol * δ ^ (Module.finrank ℝ E - 1) := by
                  intro p hp
                  rw [Finset.mem_filter] at hp
                  obtain ⟨hp_mem, _⟩ := hp
                  rw [hsJ_def, Finset.mem_product] at hp_mem
                  obtain ⟨hi, _⟩ := hp_mem
                  have hvol_eq :
                      volume.real (F p).carrier = volume.real (T p.1).carrier := by
                    rw [hF_def]
                    change (volume _).toReal = (volume _).toReal
                    exact congrArg ENNReal.toReal
                      (Kakeya.Translation.volume_actShadedTube_carrier _ _)
                  rw [hvol_eq]
                  exact hT_vol_ub p.1 hi
                have hMvol_dn_nn :
                    0 ≤ M_vol * δ ^ (Module.finrank ℝ E - 1) := by
                  have : 0 < M_vol * δ ^ (Module.finrank ℝ E - 1) :=
                    mul_pos _hM_vol_pos (pow_pos hδ_pos _)
                  exact this.le
                have hsum_le_card :
                    (∑ p ∈ sJ.filter (fun p => F p ≤ K),
                      volume.real (F p).carrier) ≤
                      ((sJ.filter (fun p => F p ≤ K)).card : ℝ) *
                        (M_vol * δ ^ (Module.finrank ℝ E - 1)) := by
                  calc (∑ p ∈ sJ.filter (fun p => F p ≤ K),
                          volume.real (F p).carrier)
                      ≤ ∑ _p ∈ sJ.filter (fun p => F p ≤ K),
                          M_vol * δ ^ (Module.finrank ℝ E - 1) :=
                        Finset.sum_le_sum hvolF_le
                    _ = ((sJ.filter (fun p => F p ≤ K)).card : ℝ) *
                          (M_vol * δ ^ (Module.finrank ℝ E - 1)) := by
                        rw [Finset.sum_const, nsmul_eq_mul]
                have hfubini :
                    ∑ j : Fin J,
                      HasUniformTranslation.productTubeContainedCount
                        (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                        J j ω
                      = ((sJ.filter (fun p => F p ≤ K)).card : ℝ) := by
                  have heq_indicator : ∀ (p : ι × Fin J),
                      (HasUniformTranslation.tubeContainedSet
                          (Ω := Ω) ((T p.1).toTube) K.carrier).indicator
                          (fun _ : Ω => (1 : ℝ)) (ω p.2) =
                        (if F p ≤ K then (1 : ℝ) else 0) := by
                    intro p
                    by_cases hmem :
                        ω p.2 ∈ HasUniformTranslation.tubeContainedSet
                          (Ω := Ω) ((T p.1).toTube) K.carrier
                    · rw [Set.indicator_of_mem hmem]
                      have hF_le : F p ≤ K := by
                        rw [hF_def]
                        intro x hx
                        have hx' : x ∈ ((HasUniformTranslation.shift
                            (Ω := Ω) (E := E)
                              (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody.carrier :=
                          hx
                        rw [Translation.actShadedTube_toConvexBody] at hx'
                        change x ∈ (HasUniformTranslation.shift
                            (Ω := Ω) (E := E) (ω p.2)).actSet
                              (T p.1).toConvexSpaceBody.carrier at hx'
                        change (HasUniformTranslation.shift
                            (Ω := Ω) (E := E) (ω p.2)).actSet
                              ((T p.1).toTube).carrier ⊆ K.carrier at hmem
                        exact hmem hx'
                      rw [if_pos hF_le]
                    · rw [Set.indicator_of_notMem hmem]
                      have hF_not_le : ¬ F p ≤ K := by
                        intro hle
                        apply hmem
                        change (HasUniformTranslation.shift
                            (Ω := Ω) (E := E) (ω p.2)).actSet
                              ((T p.1).toTube).carrier ⊆ K.carrier
                        intro x hx
                        have : x ∈ ((HasUniformTranslation.shift
                            (Ω := Ω) (E := E)
                              (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody.carrier := by
                          rw [Translation.actShadedTube_toConvexBody]
                          exact hx
                        exact hle this
                      rw [if_neg hF_not_le]
                  calc ∑ j : Fin J,
                        HasUniformTranslation.productTubeContainedCount
                          (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                          J j ω
                      = ∑ j : Fin J, ∑ i ∈ s,
                          (HasUniformTranslation.tubeContainedSet
                            (Ω := Ω) ((T i).toTube) K.carrier).indicator
                            (fun _ : Ω => (1 : ℝ)) (ω j) := by
                        rfl
                    _ = ∑ p ∈ sJ,
                          (HasUniformTranslation.tubeContainedSet
                            (Ω := Ω) ((T p.1).toTube) K.carrier).indicator
                            (fun _ : Ω => (1 : ℝ)) (ω p.2) := by
                          rw [hsJ_def, Finset.sum_product_right]
                    _ = ∑ p ∈ sJ, (if F p ≤ K then (1 : ℝ) else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro p _; exact heq_indicator p
                    _ = ((sJ.filter (fun p => F p ≤ K)).card : ℝ) :=
                        Finset.sum_boole _ _
                have hC_cover_inv_nn : 0 ≤ (δ : ℝ) ^ (-η) / C_cover :=
                  div_nonneg (Real.rpow_pos_of_pos hδ_pos _).le hC_cover_pos.le
                have hdens_B2_ge :
                    (s.card : ℝ) * (J : ℝ) *
                        (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                          volume.real B2.carrier
                      ≤ (densityIn sJ F B2).toReal := by
                  rw [div_le_iff₀ hvolB2_pos]
                  exact hLB
                have hdensK_lb :
                    ((δ : ℝ) ^ (-η) / C_cover) *
                        ((s.card : ℝ) * (J : ℝ) *
                          (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                            volume.real B2.carrier)
                      < (densityIn sJ F K).toReal := by
                  calc ((δ : ℝ) ^ (-η) / C_cover) *
                          ((s.card : ℝ) * (J : ℝ) *
                            (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                              volume.real B2.carrier)
                      ≤ ((δ : ℝ) ^ (-η) / C_cover) * (densityIn sJ F B2).toReal :=
                        mul_le_mul_of_nonneg_left hdens_B2_ge hC_cover_inv_nn
                    _ < (densityIn sJ F K).toReal := hω'
                have hdensK_vol_lb :
                    ((δ : ℝ) ^ (-η) / C_cover) *
                        ((s.card : ℝ) * (J : ℝ) *
                          (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                            volume.real B2.carrier) *
                        volume.real K.carrier
                      < (densityIn sJ F K).toReal * volume.real K.carrier :=
                  (mul_lt_mul_iff_of_pos_right hvolK_pos).mpr hdensK_lb
                rw [hdensK_eq] at hdensK_vol_lb
                have hcount_lb :
                    ((δ : ℝ) ^ (-η) / C_cover) *
                        ((s.card : ℝ) * (J : ℝ) *
                          (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                            volume.real B2.carrier) *
                        volume.real K.carrier
                      < ((sJ.filter (fun p => F p ≤ K)).card : ℝ) *
                          (M_vol * δ ^ (Module.finrank ℝ E - 1)) :=
                  lt_of_lt_of_le hdensK_vol_lb hsum_le_card
                rw [← hfubini] at hcount_lb
                have hMvol_dn_pos : 0 < M_vol * δ ^ (Module.finrank ℝ E - 1) :=
                  mul_pos _hM_vol_pos (pow_pos hδ_pos _)
                set S_det : ℝ := ((δ : ℝ) ^ (-η) / C_cover) *
                  ((s.card : ℝ) * (J : ℝ) *
                    (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                      volume.real B2.carrier) *
                  volume.real K.carrier /
                  (M_vol * δ ^ (Module.finrank ℝ E - 1))
                  with hS_det_def
                have hSdet_lt :
                    S_det < ∑ j : Fin J,
                      HasUniformTranslation.productTubeContainedCount
                        (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                        J j ω := by
                  rw [hS_det_def]
                  rw [div_lt_iff₀ hMvol_dn_pos]
                  exact hcount_lb
                have hS_lt_S_det : (S : ℝ) < S_det := by
                  have hvolB2_ne : volume.real B2.carrier ≠ 0 := hvolB2_pos.ne'
                  have hMvol_ne : M_vol ≠ 0 := _hM_vol_pos.ne'
                  have hC_cover_ne : C_cover ≠ 0 := hC_cover_pos.ne'
                  have hα_ne : (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
                    (pow_pos hδ_pos _).ne'
                  have hres : (M_log_term : ℝ) *
                      (max (HasUniformTranslation.uniformConstant Ω E * (J : ℝ))
                        C_pack_raw + 1) *
                      volume.real B2.carrier * M_vol * C_cover
                    < δ ^ (-η) * (J : ℝ) * c_vol := by
                    have h := hδ_residual_bound
                    rw [show ((⌈CF⌉₊ : ℝ)) = (J : ℝ) from by rw [hJ_def]] at h
                    exact h
                  have hsv_pos : 0 < (s.card : ℝ) * volume.real K.carrier :=
                    mul_pos hcard_pos hvolK_pos
                  have hres_scaled :
                      ((M_log_term : ℝ) *
                          (max (HasUniformTranslation.uniformConstant Ω E *
                              (J : ℝ)) C_pack_raw + 1) *
                          volume.real B2.carrier * M_vol * C_cover) *
                            ((s.card : ℝ) * volume.real K.carrier)
                        < (δ ^ (-η) * (J : ℝ) * c_vol) *
                            ((s.card : ℝ) * volume.real K.carrier) :=
                    mul_lt_mul_of_pos_right hres hsv_pos
                  have hLHS_form :
                      ((M_log_term : ℝ) *
                          (max (HasUniformTranslation.uniformConstant Ω E *
                              (J : ℝ)) C_pack_raw + 1) *
                          volume.real B2.carrier * M_vol * C_cover) *
                            ((s.card : ℝ) * volume.real K.carrier)
                        = (S : ℝ) *
                            (volume.real B2.carrier * M_vol * C_cover) := by
                    change _ = (M_log_term : ℝ) * M_K * _
                    rw [hM_K_def]; ring
                  have hSdet_form :
                      S_det * (volume.real B2.carrier * M_vol * C_cover)
                        = (δ ^ (-η) * (J : ℝ) * c_vol) *
                            ((s.card : ℝ) * volume.real K.carrier) := by
                    rw [hS_det_def]
                    have hMα_ne : M_vol * δ ^ (Module.finrank ℝ E - 1) ≠ 0 :=
                      mul_ne_zero hMvol_ne hα_ne
                    have hSdet_single :
                        (δ ^ (-η) / C_cover) *
                            ((s.card : ℝ) * (J : ℝ) *
                              (c_vol * δ ^ (Module.finrank ℝ E - 1)) /
                                volume.real B2.carrier) *
                            volume.real K.carrier /
                            (M_vol * δ ^ (Module.finrank ℝ E - 1)) =
                          (δ ^ (-η) * (s.card : ℝ) * (J : ℝ) *
                              c_vol * δ ^ (Module.finrank ℝ E - 1) *
                              volume.real K.carrier) /
                            (C_cover * volume.real B2.carrier *
                              (M_vol * δ ^ (Module.finrank ℝ E - 1))) := by
                      rw [div_mul_div_comm, div_mul_eq_mul_div, div_div]
                      congr 1
                      ring
                    rw [hSdet_single]
                    rw [div_mul_eq_mul_div, div_eq_iff
                      (mul_ne_zero
                        (mul_ne_zero hC_cover_ne hvolB2_ne) hMα_ne)]
                    ring
                  rw [hLHS_form, ← hSdet_form] at hres_scaled
                  exact (mul_lt_mul_iff_of_pos_right
                    (mul_pos (mul_pos hvolB2_pos _hM_vol_pos) hC_cover_pos)).mp
                    hres_scaled
                exact lt_trans hS_lt_S_det hSdet_lt
              · left
                push Not at hBdd
                exact hBdd
            haveI hNeZeroJ : NeZero J := ⟨hJ_pos.ne'⟩
            have hChern :
                ((HasUniformTranslation.productMeasure Ω E J)
                    {ω : Fin J → Ω | ∑ j : Fin J,
                      HasUniformTranslation.productTubeContainedCount
                        (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                        J j ω > S}).toReal ≤
                  Real.exp (10 * Real.exp 1 - S / M_K) :=
              HasUniformTranslation.productTubeContainedCount_chernoff_tail_scaledM
                s (fun i => (T i).toTube) xT hxT_mem hxBall hK_meas hK_in_B2
                hMeas M_K hM_K_pos hXM hJmM S
            have hM_K_ne : M_K ≠ 0 := hM_K_pos.ne'
            have hS_div : S / M_K = (M_log_term : ℝ) := by
              rw [hS_def]; field_simp
            rw [hS_div] at hChern
            have hμ_eq : μ (BadFrostmanEvent K) ≤
                (HasUniformTranslation.productMeasure Ω E J)
                  {ω : Fin J → Ω | ∑ j : Fin J,
                    HasUniformTranslation.productTubeContainedCount
                      (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                      J j ω > S} := by
              have hStep1 : μ (BadFrostmanEvent K) ≤
                  μ ({ω : Fin J → Ω |
                        ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                              Metric.closedBall (0 : E) 1} ∪
                      {ω : Fin J → Ω | ∑ j : Fin J,
                        HasUniformTranslation.productTubeContainedCount
                          (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                          J j ω > S}) :=
                MeasureTheory.measure_mono hBadF_subset
              have hStep2 :
                  μ ({ω : Fin J → Ω |
                        ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                              Metric.closedBall (0 : E) 1} ∪
                      {ω : Fin J → Ω | ∑ j : Fin J,
                        HasUniformTranslation.productTubeContainedCount
                          (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                          J j ω > S})
                    ≤ μ {ω : Fin J → Ω |
                          ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                                Metric.closedBall (0 : E) 1}
                      + μ {ω : Fin J → Ω | ∑ j : Fin J,
                            HasUniformTranslation.productTubeContainedCount
                              (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                              J j ω > S} :=
                MeasureTheory.measure_union_le _ _
              rw [hBadOutside_zero, zero_add] at hStep2
              have hcombined := le_trans hStep1 hStep2
              rw [hμ_def] at hcombined
              exact hcombined
            have hμ_ne_top : μ (BadFrostmanEvent K) ≠ ⊤ :=
              MeasureTheory.measure_ne_top _ _
            have hCh_ne_top :
                (HasUniformTranslation.productMeasure Ω E J)
                    {ω : Fin J → Ω | ∑ j : Fin J,
                      HasUniformTranslation.productTubeContainedCount
                        (Ω := Ω) (E := E) s (fun i => (T i).toTube) K.carrier
                        J j ω > S} ≠ ⊤ :=
              MeasureTheory.measure_ne_top _ _
            exact le_trans (ENNReal.toReal_mono hCh_ne_top hμ_eq) hChern
        have hsum_real_bd :
            (∑ K ∈ NetF, μ (BadFrostmanEvent K)).toReal ≤ 1/3 := by
          rw [ENNReal.toReal_sum (fun _ _ => MeasureTheory.measure_ne_top _ _)]
          calc ∑ K ∈ NetF, (μ (BadFrostmanEvent K)).toReal
              ≤ ∑ K ∈ NetF, Real.exp (10 * Real.exp 1 - (M_log_term : ℝ)) :=
                Finset.sum_le_sum (fun K hK => hChernoffF K hK)
            _ = (NetF.card : ℝ) * Real.exp (10 * Real.exp 1 - (M_log_term : ℝ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 1/3 := hNetF_smallness
        have hsum_ne_top : (∑ K ∈ NetF, μ (BadFrostmanEvent K)) ≠ ⊤ :=
          ENNReal.sum_ne_top.mpr (fun _ _ => MeasureTheory.measure_ne_top _ _)
        rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hsum_ne_top hUnionBd)]
        exact ENNReal.ofReal_le_ofReal
          ((ENNReal.toReal_mono hsum_ne_top hUnionBd).trans hsum_real_bd)
      haveI : ProperSpace E := FiniteDimensional.proper ℝ E
      obtain ⟨NetF, C_cover, hC_cover_pos, hNetF_cover, hBadFrostman⟩ :=
        hBadFrostman_le_one_third
      set BadFrostmanΩ : Set (Fin J → Ω) :=
        {ω : Fin J → Ω |
            ∃ K ∈ NetF,
              ¬ (densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                    (fun p : ι × Fin J =>
                      ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                          (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K
                  ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
                    densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                      (fun p : ι × Fin J =>
                        ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                            (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
                      (ConvexSpaceBody.cthickening 1
                        (ConvexSpaceBody.closedUnitBall (E := E))))}
        with hBadFrostmanΩ_def
      set BadOutsideΩ : Set (Fin J → Ω) :=
        {ω : Fin J → Ω |
            ∃ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E) ∉
                  Metric.closedBall (0 : E) 1}
        with hBadOutsideΩ_def
      set BadEDΩ : Set (Fin J → Ω) :=
        {ω : Fin J → Ω |
            ∃ T₀' ∈ NetED, ∑ j : Fin J,
              productEdFailCountSet s (fun i => (T i).toTube)
                (Metric.cthickening (99 * δ) T₀'.carrier) c_bridge 1 J j
                (fun j => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)
              > (M_cap : ℝ)}
        with hBadEDΩ_def
      have hUnion_lt_one : μ (BadFrostmanΩ ∪ BadOutsideΩ ∪ BadEDΩ) < 1 := by
        have hle : μ (BadFrostmanΩ ∪ BadOutsideΩ ∪ BadEDΩ)
            ≤ ENNReal.ofReal (1/3) + ENNReal.ofReal (1/3) :=
          (MeasureTheory.measure_union_le _ _).trans (add_le_add
            ((MeasureTheory.measure_union_le _ _).trans
              (by rw [hBadOutside_zero, add_zero]; exact hBadFrostman))
            hBadED_Ω_le_one_third)
        refine hle.trans_lt ?_
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by norm_num)
      obtain ⟨ω, hω_compl⟩ : (BadFrostmanΩ ∪ BadOutsideΩ ∪ BadEDΩ)ᶜ.Nonempty := by
        refine Set.nonempty_compl.mpr fun hEq => ?_
        rw [hEq, MeasureTheory.measure_univ] at hUnion_lt_one
        exact lt_irrefl _ hUnion_lt_one
      have hω_notBadF : ω ∉ BadFrostmanΩ := fun h => hω_compl (Or.inl (Or.inl h))
      have hω_notBadOut : ω ∉ BadOutsideΩ := fun h => hω_compl (Or.inl (Or.inr h))
      have hω_notBadED : ω ∉ BadEDΩ := fun h => hω_compl (Or.inr h)
      have hω_bdd : ∀ j, HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) (0 : E)
          ∈ Metric.closedBall (0 : E) 1 := by
        intro j
        by_contra h
        exact hω_notBadOut ⟨j, h⟩
      have hω_hitK : ∀ K ∈ NetF,
          densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
              (fun p : ι × Fin J =>
                ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                    (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody) K
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η) / C_cover) *
              densityIn (s ×ˢ (Finset.univ : Finset (Fin J)))
                (fun p : ι × Fin J =>
                  ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                      (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
                (ConvexSpaceBody.cthickening 1
                  (ConvexSpaceBody.closedUnitBall (E := E))) := by
        intro K hK
        by_contra hgt
        exact hω_notBadF ⟨K, hK, hgt⟩
      set T'_ω : ι × Fin J → ShadedTube δ E :=
        fun p : ι × Fin J =>
          (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube (T p.1)
        with hT'_ω_def
      have hT'_ω_ball : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
          (T'_ω p).carrier ⊆ Metric.closedBall (0 : E) 2 := fun p _ =>
        translation_preserves_carrier_in_ball_plus_one E (T p.1) (_hT_ball p.1) (ω p.2)
          (hω_bdd p.2)
      have hω_frost :
          ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p : ι × Fin J => (T'_ω p).toConvexSpaceBody)
            (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
            (ENNReal.ofReal ((δ : ℝ) ^ (-η))) :=
        frostman_of_per_K_hitcount_chernoff (E := E) hδ_pos _hδ_lt_one _hη
          (s ×ˢ (Finset.univ : Finset (Fin J)))
          T'_ω hT'_ω_ball NetF C_cover hC_cover_pos
          (fun K' hK' => hNetF_cover ω hω_bdd K' hK') hω_hitK
      have hω_ED :
          IsEDUpToMult (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p : ι × Fin J => (T'_ω p).carrier) M_cap := by
        set V_lb : ℝ := c_vol * δ ^ (Module.finrank ℝ E - 1) with hV_lb_def
        set V_ub : ℝ := M_vol * δ ^ (Module.finrank ℝ E - 1) with hV_ub_def
        have hV_lb_pos : 0 < V_lb :=
          mul_pos _hc_vol_pos (pow_pos hδ_pos _)
        have hV_ub_pos : 0 < V_ub :=
          mul_pos _hM_vol_pos (pow_pos hδ_pos _)
        intro p₀ hp₀
        have hp₀_mem : p₀.1 ∈ s ∧ p₀.2 ∈ (Finset.univ : Finset (Fin J)) :=
          Finset.mem_product.mp hp₀
        change (notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p : ι × Fin J => (T'_ω p).carrier) (T'_ω p₀).carrier).card ≤ M_cap
        obtain ⟨T₀', hT₀'_mem, hT₀'_close⟩ :=
          _hNetED_cover ω hω_bdd p₀ hp₀_mem.1
        set K_thick : Set E := Metric.cthickening (99 * δ) T₀'.carrier
          with hK_thick_def
        have hcarrier_eq : ∀ p : ι × Fin J,
            (T'_ω p).carrier =
              ((T p.1).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2) 0)).carrier := by
          intro p
          rw [hT'_ω_def]
          exact hR_translate p.1 (ω p.2)
        have hTp_sub :
            ((T p₀.1).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier
              ⊆ K_thick := by
          rw [← hcarrier_eq p₀]
          exact hT₀'_close
        have hvol_tr_eq : ∀ (i : ι) (v : E),
            volume.real (((T i).toTube.translate v).carrier) =
              volume.real (T i).carrier := by
          intro i v
          rw [Tube.translate_carrier]
          change (volume _).toReal = (volume _).toReal
          rw [MeasureTheory.measure_preimage_add]
        have hc_bridge_eq : c_bridge = V_lb / (2 * V_ub) := by
          rw [hc_bridge_def, hV_lb_def, hV_ub_def]
          have hM_vol_ne : M_vol ≠ 0 := ne_of_gt _hM_vol_pos
          field_simp
        have h_per_index_bridge :
            ∀ (j : Fin J) (i : ι), i ∈ s →
              ¬ IsEssentiallyDistinct (T'_ω (i, j)).carrier (T'_ω p₀).carrier →
                BadAgainstSet
                  ((T i).toTube.translate
                    (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0))
                  K_thick c_bridge := by
          intro j i hi hnotED_V
          have hnotED' :
              ¬ IsEssentiallyDistinct
                (((T i).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)).carrier)
                (((T p₀.1).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier) := by
            rw [hcarrier_eq (i, j), hcarrier_eq p₀] at hnotED_V
            exact hnotED_V
          have hvol_lb_p₀ :
              V_lb ≤ volume.real
                (((T p₀.1).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier) := by
            rw [hvol_tr_eq p₀.1 _]
            exact hT_vol_lb p₀.1 hp₀_mem.1
          have hvol_ub_i :
              volume.real (((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)).carrier)
                ≤ V_ub := by
            rw [hvol_tr_eq i _]
            exact hT_vol_ub i hi
          have hvol_lb_p₀_enn :
              ENNReal.ofReal V_lb ≤ volume
                (((T p₀.1).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier) := by
            have hfin : volume (((T p₀.1).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier) ≠ ⊤ :=
              ((T p₀.1).toTube.translate _).isCompact.measure_lt_top.ne
            calc
              ENNReal.ofReal V_lb ≤ ENNReal.ofReal (volume.real
                  (((T p₀.1).toTube.translate
                    (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier)) :=
                ENNReal.ofReal_le_ofReal hvol_lb_p₀
              _ = volume (((T p₀.1).toTube.translate
                    (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0)).carrier) :=
                ENNReal.ofReal_toReal hfin
          have hvol_ub_i_enn :
              volume (((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)).carrier)
                ≤ ENNReal.ofReal V_ub := by
            have hfin : volume (((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)).carrier) ≠ ⊤ :=
              ((T i).toTube.translate _).isCompact.measure_lt_top.ne
            calc
              volume (((T i).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)).carrier) =
                  ENNReal.ofReal (volume.real (((T i).toTube.translate
                    (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)).carrier)) :=
                (ENNReal.ofReal_toReal hfin).symm
              _ ≤ ENNReal.ofReal V_ub := ENNReal.ofReal_le_ofReal hvol_ub_i
          have hbridge :=
            badAgainstSet_of_notED_subset_cthickening (δ := δ) hδ_pos
              ((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0))
              ((T p₀.1).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p₀.2) 0))
              K_thick V_lb V_ub hV_lb_pos hV_ub_pos
              hvol_lb_p₀_enn hvol_ub_i_enn hTp_sub hnotED'
          rw [← hc_bridge_eq] at hbridge
          exact hbridge
        set Sfull : Finset (ι × Fin J) :=
          ((s ×ˢ (Finset.univ : Finset (Fin J))).filter
            (fun p => BadAgainstSet
              ((T p.1).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2) 0))
              K_thick c_bridge))
          with hSfull_def
        have h_sub :
            notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
              (fun p : ι × Fin J => (T'_ω p).carrier) (T'_ω p₀).carrier
              ⊆ Sfull := by
          intro p hp
          have hp' : p ∈ s ×ˢ (Finset.univ : Finset (Fin J)) ∧
              ¬ IsEssentiallyDistinct (T'_ω p).carrier (T'_ω p₀).carrier := by
            unfold notEssDistinctSet at hp
            simpa using hp
          obtain ⟨hp_mem, hp_notED⟩ := hp'
          have hi_mem : p.1 ∈ s := (Finset.mem_product.mp hp_mem).1
          have hbad : BadAgainstSet
              ((T p.1).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2) 0))
              K_thick c_bridge := by
            exact h_per_index_bridge p.2 p.1 hi_mem hp_notED
          rw [hSfull_def, Finset.mem_filter]
          exact ⟨hp_mem, hbad⟩
        have hcard_sub :
            (notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
              (fun p : ι × Fin J => (T'_ω p).carrier) (T'_ω p₀).carrier).card
              ≤ Sfull.card := Finset.card_le_card h_sub
        let fibre : Fin J → Finset ι :=
          fun j => @Finset.filter ι
            (fun i => BadAgainstSet
              ((T i).toTube.translate
                (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0))
              K_thick c_bridge)
            (Classical.decPred _) s
        have hfibre_def : ∀ j : Fin J, fibre j =
            @Finset.filter ι
              (fun i => BadAgainstSet
                ((T i).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0))
                K_thick c_bridge)
              (Classical.decPred _) s :=
          fun _ => rfl
        have hSfull_card_eq :
            Sfull.card = ∑ j : Fin J, (fibre j).card := by
          rw [hSfull_def, Finset.card_filter, Finset.sum_product_right]
          exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
        have h_fibre_eq : ∀ j : Fin J, ((fibre j).card : ℝ) =
            productEdFailCountSet s (fun i => (T i).toTube) K_thick c_bridge 1 J j
              (fun j' => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j') 0) := by
          intro j
          change ((fibre j).card : ℝ) =
              edFailCountSet s (fun i => (T i).toTube) K_thick c_bridge
                ((1 : ℝ) • HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)
          rw [show ((1 : ℝ) • HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0)
                  = HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j) 0
                from one_smul _ _]
          rw [hfibre_def j, edFailCountSet_eq_filter_card]
        have hsum_bound :
            (∑ j : Fin J, ((fibre j).card : ℝ)) ≤ (M_cap : ℝ) := by
          have hω_le : ∑ j : Fin J,
              productEdFailCountSet s (fun i => (T i).toTube) K_thick
                c_bridge 1 J j
                (fun j' => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j') 0)
                ≤ (M_cap : ℝ) := by
            by_contra hgt
            push Not at hgt
            exact hω_notBadED ⟨T₀', hT₀'_mem, hgt⟩
          calc (∑ j : Fin J, ((fibre j).card : ℝ))
              = ∑ j : Fin J,
                  productEdFailCountSet s (fun i => (T i).toTube) K_thick
                    c_bridge 1 J j
                    (fun j' => HasUniformTranslation.shift (Ω := Ω) (E := E) (ω j') 0) :=
                Finset.sum_congr rfl (fun j _ => h_fibre_eq j)
            _ ≤ (M_cap : ℝ) := hω_le
        have hSfull_card_real : (Sfull.card : ℝ) ≤ (M_cap : ℝ) := by
          rw [hSfull_card_eq]
          push_cast
          exact hsum_bound
        have hSfull_card_nat : Sfull.card ≤ M_cap := Nat.cast_le.mp hSfull_card_real
        exact hcard_sub.trans hSfull_card_nat
      exact ⟨ω, hω_bdd, hω_frost, hω_ED⟩
  exact ⟨ω, M_cap, hM_cap_bound, hω_bdd, hω_ED, hω_frost⟩

/-- As `δ → 0⁺` the blow-up factor `δ ^ (-η)` eventually dominates any fixed constant. -/
private lemma eventually_le_rpow_neg
    {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), C ≤ δ ^ (-η) :=
  (tendsto_rpow_neg_nhdsGT_zero (neg_neg_iff_pos.mpr hη)).eventually_ge_atTop C

/-- **[GWZ, §9, `randCF`]** Constructs a translated product family with controlled cardinality,
ED multiplicity, Frostman density, fullness, and multiplicity. -/
theorem exists_randCF_translation_family
    [Nontrivial E]
    (η : ℝ) (hη : 0 < η) (CF : ℝ) (hCF : 1 ≤ CF) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube (Real.toNNReal δ) E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ConvexSpaceBody.IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∃ (ι' : Type v) (s' : Finset ι') (T' : ι' → ShadedTube (Real.toNNReal δ) E)
          (M_cap : ℕ),
        (s'.card : ℝ) ≤ (⌈CF⌉₊ : ℝ) * (s.card : ℝ) ∧
        ((M_cap : ℝ) + 1 ≤ δ ^ (-η)) ∧
        (∀ i, (T' i).carrier ⊆ Metric.closedBall 0 2) ∧
        IsEDUpToMult s' (fun i ↦ (T' i).carrier) M_cap ∧
        ConvexSpaceBody.IsFrostmanIn s' (fun i ↦ (T' i).toConvexSpaceBody)
          (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
          (ENNReal.ofReal (δ ^ (-η))) ∧
        ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) ≥ δ ^ η ∧
        ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          ShadedBody.multiplicity s' (fun i ↦ (T' i).toShadedBody) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set c_vol : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_vol_def
  have hc_vol_pos : 0 < c_vol := by
    rw [hc_vol_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hT_vol_lb_all : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := fun δ _ T => by
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne (Tube.le_volume (δ := δ) T)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
  set M_vol : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hM_vol_def
  have hM_vol_pos : 0 < M_vol := by
    rw [hM_vol_def]
    unfold Tube.volume_le.C
    push_cast
    positivity
  have hT_vol_ub_all : ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ T : Tube δ E,
      volume.real T.carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) :=
    fun δ _ hδ1 T => by
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      (Tube.volume_le hδ1 T)
    simpa [hM_vol_def, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_pow, MeasureTheory.Measure.real] using hreal
  rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne') with hfinrank_gt | hfinrank_eq
  · obtain ⟨C_dim, δ₀_thinBox, hC_dim_pos, hδ₀_thinBox_pos, _hδ₀_thinBox_le, hThinBox⟩ :=
      badAgainstSet_count_le_of_ED_thinBox E hfinrank_gt
    set C_pack_ext : ℕ :=
      ⌈(C_dim : ℝ) * netVolThinConstantM E ^ 2 /
        (c_vol / (2 * M_vol)) ^ (Module.finrank ℝ E)⌉₊ with hC_pack_ext_def
    have hC_pack_ext_pos : 0 < C_pack_ext := by
      rw [hC_pack_ext_def]
      exact Nat.ceil_pos.mpr (div_pos
        (mul_pos (by exact_mod_cast hC_dim_pos) (pow_pos (netVolThinConstantM_pos E) 2))
        (pow_pos (div_pos hc_vol_pos (by linarith)) _))
    set M_ED : ℕ := ⌈CF⌉₊ * C_pack_ext + 1 with hM_ED_def
    have hM_ED_pos : 0 < M_ED := by simp [hM_ED_def]
    have hM_ED_ge_JC_pack : ⌈CF⌉₊ * C_pack_ext < M_ED := by
      rw [hM_ED_def]; exact Nat.lt_succ_self _
    have hvolB1_pos_env :
        0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
      exact (Metric.measure_closedBall_pos volume 0 one_pos).ne'
    have hvolB2_pos_env :
        0 < volume.real
              (ConvexSpaceBody.cthickening 1
                (ConvexSpaceBody.closedUnitBall (E := E))).carrier := by
      change 0 < volume.real
        (Metric.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
      rw [ConvexSpaceBody.closedUnitBall_carrier,
        _root_.cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1)
          (by norm_num : (0:ℝ) ≤ 1)]
      refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
      refine (Metric.measure_closedBall_pos volume 0 ?_).ne'
      norm_num
    let huc_val : ℝ :=
      @HasUniformTranslation.uniformConstant E _ E _ _ _ _ _
        (instHasUniformTranslationSelf E)
    have huc_pos_env : 0 < huc_val :=
      @HasUniformTranslation.uniformConstantPos E _ E _ _ _ _ _
        (instHasUniformTranslationSelf E)
    filter_upwards
      [(self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ),
       (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one) :
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1),
       (nhdsWithin_le_nhds (Iio_mem_nhds hδ₀_thinBox_pos) :
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < δ₀_thinBox),
       randCF_smallness_envelope (E := E) hfinrank_gt hη hCF
         c_vol M_vol hc_vol_pos hM_vol_pos
         C_pack_ext hC_pack_ext_pos M_ED hM_ED_pos hM_ED_ge_JC_pack,
       randCF_residual_envelope (E := E) hfinrank_gt hη hCF
         c_vol M_vol hc_vol_pos hM_vol_pos
         huc_val huc_pos_env
         (netGeomConstantC E) (netGeomConstantC_pos E)
         (volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
         (volume.real
            (ConvexSpaceBody.cthickening 1
              (ConvexSpaceBody.closedUnitBall (E := E))).carrier)
         hvolB1_pos_env hvolB2_pos_env]
      with δ hδ_pos hδ_lt_one hδ_lt_δ₀_thinBox hδ_env hδ_residual
    intro ι s T hT_ball hT_ED hT_Frost hT_full
    obtain ⟨_hδ_small, _hδ_lt_cvol, _hδ_small_pack,
        _hδ_band_HIGH_ext, _hδ_lt_Vmax_half_ext, hδ_M_cap_bound,
        hδ_netF_smallness⟩ := hδ_env
    let Ω : Type _ := E
    let _instMeasΩ : MeasurableSpace Ω := (inferInstance : MeasurableSpace E)
    let _hUniform : HasUniformTranslation Ω E := inferInstance
    set J : ℕ := ⌈CF⌉₊ with hJ_def
    have hJ_pos : 0 < J := Nat.ceil_pos.mpr (by linarith : (0 : ℝ) < CF)
    set s' : Finset (ι × Fin J) :=
      s ×ˢ (Finset.univ : Finset (Fin J)) with hs'_def
    have hThinBox_pack :
        ∀ {ι_t : Type v} (s_t : Finset ι_t)
          (T_t : ι_t → Tube (Real.toNNReal δ) E) (T₀'_t : Tube (Real.toNNReal δ) E)
          (_hK_in_B2 : T₀'_t.carrier ⊆ Metric.closedBall (0 : E) (7 / 2))
          (_h_vol_ub :
            volume (Metric.cthickening
              (99 * ((Real.toNNReal δ : NNReal) : ℝ)) T₀'_t.carrier)
              ≤ ENNReal.ofReal (netVolThinConstantM E) *
                (Real.toNNReal δ : ENNReal) ^ (Module.finrank ℝ E - 1))
          (v : E),
          (s_t : Set ι_t).Pairwise
            (fun i j => IsEssentiallyDistinct (T_t i).carrier (T_t j).carrier) →
          (@Finset.filter ι_t
              (fun i => BadAgainstSet ((T_t i).translate v)
                (Metric.cthickening (99 * ((Real.toNNReal δ : NNReal) : ℝ)) T₀'_t.carrier)
                (c_vol / (2 * M_vol)))
              (Classical.decPred _) s_t).card ≤ C_pack_ext := by
      intro ι_t s_t T_t T₀'_t hK_in_B2 h_vol_ub v hED_t
      exact (hThinBox (ι := ι_t) (Real.toNNReal_pos.mpr hδ_pos)
        (by rw [Real.coe_toNNReal δ hδ_pos.le]; exact hδ_lt_δ₀_thinBox.le)
        s_t T_t T₀'_t hK_in_B2 (netVolThinConstantM E) (netVolThinConstantM_pos E)
        h_vol_ub v hED_t).trans (Nat.le_ceil _)
    have hR0_law :
        (HasUniformTranslation.measure (Ω := Ω) (E := E)).map
            (fun ω : Ω => HasUniformTranslation.shift (Ω := Ω) (E := E) ω (0 : E))
          = uniformBallMeasure E := by
      change (uniformBallMeasure E).map (fun t : E => t + 0) = uniformBallMeasure E
      simp
    have hδNN_pos_net : 0 < Real.toNNReal δ := Real.toNNReal_pos.mpr hδ_pos
    have hδNN_le_one_net : Real.toNNReal δ ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one, Real.coe_toNNReal δ hδ_pos.le]
      exact hδ_lt_one.le
    obtain ⟨KTest, hKT_sub, hKT_card, hKT_cover⟩ :=
      exists_netF_test_family.{v, _} E hδNN_pos_net hδNN_le_one_net
    let _NetF : Finset (ConvexSpaceBody E) := KTest
    let _C_cover : ℝ := netGeomConstantC E
    have _hC_cover_pos : (0 : ℝ) < _C_cover := netGeomConstantC_pos E
    have _hNetF_smallness :
        (_NetF.card : ℝ) * Real.exp (10 * Real.exp 1 -
          (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ)) ≤ 1/3 := by
      rw [Real.coe_toNNReal δ hδ_pos.le] at hKT_card
      have hexp_le :
          Real.exp (10 * Real.exp 1 - (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ))
            ≤ Real.exp (10 * Real.exp 1) * δ ^ netGeomConstantM E := by
        rw [show Real.log (1 / δ) = -Real.log δ by rw [one_div, Real.log_inv],
          Real.rpow_def_of_pos hδ_pos, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by
          linarith [Nat.le_ceil (netGeomConstantM E * -Real.log δ)])
      calc (_NetF.card : ℝ)
            * Real.exp (10 * Real.exp 1 - (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ))
          ≤ netGeomConstantC E * δ ^ (-netGeomConstantMRaw E)
              * (Real.exp (10 * Real.exp 1) * δ ^ netGeomConstantM E) :=
            mul_le_mul hKT_card hexp_le (Real.exp_pos _).le
              (mul_nonneg (netGeomConstantC_pos E).le (Real.rpow_nonneg hδ_pos.le _))
        _ = netGeomConstantC E * Real.exp (10 * Real.exp 1) *
              δ ^ (netGeomConstantM E - netGeomConstantMRaw E) := by
            rw [sub_eq_neg_add, Real.rpow_add hδ_pos]; ring
        _ ≤ 1/3 := hδ_netF_smallness
    have hδNN_coe_eq : ((Real.toNNReal δ : NNReal) : ℝ) = δ :=
      Real.coe_toNNReal δ hδ_pos.le
    have hT_vol_lb' : ∀ i ∈ s,
        c_vol * ((Real.toNNReal δ : NNReal) : ℝ) ^ (Module.finrank ℝ E - 1)
          ≤ volume.real (T i).carrier :=
      fun i _ => hT_vol_lb_all (Real.toNNReal δ) hδNN_pos_net (T i).toTube
    have hT_vol_ub' : ∀ i ∈ s,
        volume.real (T i).carrier ≤
          M_vol * ((Real.toNNReal δ : NNReal) : ℝ) ^ (Module.finrank ℝ E - 1) :=
      fun i _ => hT_vol_ub_all (Real.toNNReal δ) hδNN_pos_net hδNN_le_one_net (T i).toTube
    have hR_translate :
        ∀ (i : ι) (ω : Ω),
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) ω).actShadedTube
            (T i)).carrier
              = ((T i).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0)).carrier := by
      intro i ω'
      change (fun y : E => ω' + y) '' (T i).carrier =
        (fun y : E => (ω' + 0) + y) '' (T i).carrier
      simp
    have hδ_pos_NN_coe : 0 < ((Real.toNNReal δ : NNReal) : ℝ) := by rwa [hδNN_coe_eq]
    have hδ_lt_one_NN_coe : ((Real.toNNReal δ : NNReal) : ℝ) < 1 := by rwa [hδNN_coe_eq]
    have hδ_M_cap_bound' :
        ((max M_ED C_pack_ext : ℕ) : ℝ) *
            (((max M_ED C_pack_ext : ℕ) : ℝ) +
             (⌈netGeomConstantM E * Real.log (1 / ((Real.toNNReal δ : NNReal) : ℝ))⌉₊ : ℝ) +
             (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
          ≤ ((Real.toNNReal δ : NNReal) : ℝ) ^ (-η) := by
      rwa [hδNN_coe_eq]
    have hT_full' :
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
          ≥ (Real.toNNReal δ) ^ η := by
      have h1 :
          ((Real.toNNReal δ : NNReal) ^ η : ℝ)
            ≤ ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : NNReal) : ℝ) := by
        rwa [show ((Real.toNNReal δ : NNReal) ^ η : ℝ) = δ ^ η by rw [hδNN_coe_eq]]
      exact_mod_cast h1
    have hδ_residual' :
        (⌈netGeomConstantM E * Real.log (1 / ((Real.toNNReal δ : NNReal) : ℝ))⌉₊ : ℝ) *
            (max (HasUniformTranslation.uniformConstant Ω E * (⌈CF⌉₊ : ℝ))
              (CF * M_vol / (c_vol *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)) + 1) *
            volume.real
              (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier *
            M_vol * _C_cover
          < ((Real.toNNReal δ : NNReal) : ℝ) ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol := by
      rwa [hδNN_coe_eq]
    obtain ⟨ω, M_cap, hM_cap_bound, hω_ball, hω_ED, hω_Frost⟩ :=
      randCF_chernoff_witness (E := E) (Ω := Ω) (δ := Real.toNNReal δ) hR0_law
        hfinrank_gt hδ_pos_NN_coe hδ_lt_one_NN_coe hη hCF
        c_vol M_vol hc_vol_pos hM_vol_pos
        C_pack_ext hC_pack_ext_pos M_ED hM_ED_pos hM_ED_ge_JC_pack
        hδ_M_cap_bound' hThinBox_pack
        s T hT_ball hT_ED hT_Frost hT_full'
        hT_vol_lb' hT_vol_ub' hR_translate
        _NetF _C_cover _hC_cover_pos hδ_residual'
        (by
          intro ω _hBdd K' _hK'
          obtain ⟨K, hK_mem, hK_le⟩ :=
            hKT_cover (s ×ˢ (Finset.univ : Finset (Fin ⌈CF⌉₊)))
              (fun p : ι × Fin ⌈CF⌉₊ =>
                ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                    (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
              (fun p _ => translation_preserves_carrier_in_ball_plus_one E (T p.1)
                (hT_ball p.1) (ω p.2) (_hBdd p.2))
              (fun p _ => Tube.le_ethickness_scale ((HasUniformTranslation.shift
                (Ω := Ω) (E := E) (ω p.2)).actShadedTube (T p.1)).toTube)
          refine ⟨K, hK_mem, ?_, (le_maxDensity _ _ K').trans hK_le⟩
          intro x hxK
          change x ∈ Metric.cthickening 1 (Metric.closedBall (0 : E) 1)
          rw [_root_.cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1)
                (by norm_num : (0:ℝ) ≤ 1), show (1 : ℝ) + 1 = 2 by norm_num]
          exact hKT_sub K hK_mem hxK)
        hKT_sub
        (by
          intro K _hK i _hi
          refine IsClosed.measurableSet ?_
          have hset_eq :
              HasUniformTranslation.tubeContainedSet (Ω := E)
                  ((T i).toTube) K.carrier =
                ⋂ x ∈ ((T i).toTube).carrier,
                  {t : E | t + x ∈ K.carrier} := by
            ext t
            simp only [HasUniformTranslation.tubeContainedSet, Set.mem_setOf_eq,
              Translation.actSet, Set.image_subset_iff, Set.mem_iInter]
            refine ⟨fun h x hx => h hx, fun h x hx => h x hx⟩
          rw [hset_eq]
          refine isClosed_biInter fun x _hx => ?_
          have hcont : Continuous (fun t : E => t + x) :=
            continuous_id.add continuous_const
          exact K.isCompact.isClosed.preimage hcont)
        (by
          rcases Finset.eq_empty_or_nonempty s with hs_empty | hs_ne
          · rw [show ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) = 0 by
              rw [hs_empty]; simp] at hT_full
            simp only [NNReal.coe_zero] at hT_full
            linarith [Real.rpow_pos_of_pos hδ_pos η]
          · exact Finset.card_pos.mpr hs_ne)
        (by rw [hδNN_coe_eq]; exact _hNetF_smallness)
    set T' : (ι × Fin J) → ShadedTube (Real.toNNReal δ) E :=
      fun p : ι × Fin J =>
        (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube (T p.1)
      with hT'_def
    refine ⟨ι × Fin J, s', T', M_cap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hcard : s'.card = s.card * J := by
        rw [hs'_def, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      rw [hcard]
      push_cast
      rw [hJ_def, mul_comm]
    · rwa [hδNN_coe_eq] at hM_cap_bound
    · intro p
      exact translation_preserves_carrier_in_ball_plus_one (Ω := Ω) (E := E)
        (T p.1) (hT_ball p.1) (ω p.2) (hω_ball p.2)
    · exact hω_ED
    · rwa [hδNN_coe_eq] at hω_Frost
    · change ShadedBody.fullness s' (fun p : ι × Fin J => (T' p).toShadedBody) ≥ δ ^ η
      rw [hs'_def, hT'_def,
        fullness_eq_under_product_translation (Ω := Ω) (E := E) s T J hJ_pos ω]
      exact hT_full
    · change ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
           ShadedBody.multiplicity s' (fun p : ι × Fin J => (T' p).toShadedBody)
      rw [hs'_def, hT'_def]
      exact multiplicity_le_under_product_translation (Ω := Ω) (E := E) s T J hJ_pos ω
  · filter_upwards
      [(self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ),
       (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one) :
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1),
       eventually_le_rpow_neg hη 2, eventually_le_rpow_neg hη (CF * 2),
       eventually_le_rpow_neg hη (volume.real (Metric.closedBall (0 : E) 2) / c_vol)]
      with δ hδ_pos _hδ_lt_one h_two_le _h_CF2_le h_volB2_cvol_le
    intro ι s T hT_ball hT_ED hT_Frost hT_full
    refine ⟨ι, s, T, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_mul_of_one_le_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.ceil_pos.mpr (by linarith : (0 : ℝ) < CF))
    · rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]; exact h_two_le
    · intro i
      exact Set.Subset.trans (hT_ball i)
        (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))
    · intro i hi
      refine (Finset.card_le_card ?_).trans (Finset.card_singleton i).le
      intro j hj
      simp only [notEssDistinctSet, Finset.mem_filter] at hj
      by_contra hji
      exact hj.2 (hT_ED hj.1 hi (by simpa using hji))
    · set K1 : ConvexSpaceBody E :=
        ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      have hK1_carrier : K1.carrier = Metric.closedBall (0 : E) 2 := by
        change Metric.cthickening 1 (Metric.closedBall (0 : E) 1) = _
        rw [cthickening_closedBall (by norm_num : (0 : ℝ) ≤ 1)
              (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
      have hT_le_K1 : ∀ i, (T i).toConvexSpaceBody ≤ K1 := by
        intro i x hx
        change x ∈ K1.carrier
        rw [hK1_carrier]
        exact Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)
          (hT_ball i hx)
      have hT_vol_lb_real : ∀ i, c_vol ≤ volume.real (T i).carrier := fun i => by
        have hbnd' := hT_vol_lb_all (Real.toNNReal δ)
          (Real.toNNReal_pos.mpr hδ_pos) (T i).toTube
        rw [show Module.finrank ℝ E - 1 = 0 by omega] at hbnd'
        simpa using hbnd'
      have hT_vol_lb_enn : ∀ i, ENNReal.ofReal c_vol ≤ volume (T i).carrier := fun i => by
        rw [← ENNReal.ofReal_toReal
          (T i).toShadedBody.toConvexSpaceBody.isCompact'.measure_ne_top]
        exact ENNReal.ofReal_le_ofReal (hT_vol_lb_real i)
      intro K' _hK'_le_K1
      by_cases hany : ∃ i ∈ s, (fun i ↦ (T i).toConvexSpaceBody) i ≤ K'
      · obtain ⟨i₀, hi₀_s, hi₀_le⟩ := hany
        have hvol_K'_lb : ENNReal.ofReal c_vol ≤ volume K'.carrier :=
          (hT_vol_lb_enn i₀).trans (measure_mono hi₀_le)
        have h_num_le_full :
            (∑ i ∈ s with (fun i ↦ (T i).toConvexSpaceBody) i ≤ K',
              volume (T i).carrier) ≤
              (∑ i ∈ s, volume ((fun i ↦ (T i).toConvexSpaceBody) i).carrier) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        have h_full_eq :
            (∑ i ∈ s, volume ((fun i ↦ (T i).toConvexSpaceBody) i).carrier)
              = densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 * volume K1.carrier :=
          Kakeya.sum_volume_eq_densityIn_mul_volume'
            (fun i _ => hT_le_K1 i)
        have h_ratio_le_ENN :
            volume K1.carrier / ENNReal.ofReal c_vol
              ≤ ENNReal.ofReal (δ ^ (-η)) := by
          rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hc_vol_pos).ne'
              ENNReal.ofReal_ne_top, hK1_carrier,
            show volume (Metric.closedBall (0 : E) 2)
                = ENNReal.ofReal (volume.real (Metric.closedBall (0 : E) 2)) from
              (ENNReal.ofReal_toReal MeasureTheory.measure_closedBall_lt_top.ne).symm,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _)]
          exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc_vol_pos).mp h_volB2_cvol_le)
        calc densityIn s (fun i ↦ (T i).toConvexSpaceBody) K'
            = (∑ i ∈ s with (fun i ↦ (T i).toConvexSpaceBody) i ≤ K',
                volume (T i).carrier) / volume K'.carrier := rfl
          _ ≤ (∑ i ∈ s, volume ((fun i ↦ (T i).toConvexSpaceBody) i).carrier)
                / volume K'.carrier := ENNReal.div_le_div_right h_num_le_full _
          _ = (densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 * volume K1.carrier)
                / volume K'.carrier := by rw [h_full_eq]
          _ ≤ (densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 * volume K1.carrier)
                / ENNReal.ofReal c_vol :=
              ENNReal.div_le_div_left hvol_K'_lb _
          _ = densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 *
                (volume K1.carrier / ENNReal.ofReal c_vol) :=
              mul_div_assoc _ _ _
          _ ≤ densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 *
                ENNReal.ofReal (δ ^ (-η)) := mul_le_mul_right h_ratio_le_ENN _
          _ = ENNReal.ofReal (δ ^ (-η)) *
                densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 := mul_comm _ _
      · have h_zero : densityIn s (fun i ↦ (T i).toConvexSpaceBody) K' = 0 := by
          change (∑ i ∈ s with (fun i ↦ (T i).toConvexSpaceBody) i ≤ K',
              volume (T i).carrier) / volume K'.carrier = 0
          rw [Finset.filter_eq_empty_iff.mpr fun i hi h_le => hany ⟨i, hi, h_le⟩,
            Finset.sum_empty]
          exact ENNReal.zero_div
        rw [h_zero]
        exact bot_le
    · exact hT_full
    · exact le_refl _

set_option maxHeartbeats 1000000 in
-- The whole `randCF` construction is elaborated once more, now with `CF` bound inside the filter.
/-- **[GWZ, §9, `randCF`], uniformly in the Frostman constant over a range of scales.**

Identical conclusion to `Kakeya.exists_randCF_translation_family`, but with the quantifier over
the Frostman constant `CF` moved *inside* the `∀ᶠ δ`: one smallness threshold for `δ` serves
every `CF` in the range `1 ≤ CF ≤ δ ^ (-η₀)` at once.  Here `η₀` is any exponent with
`0 < η₀ ≤ min (η / 4) 1`.

**The range restriction is essential and is not an artefact of the proof.**  The construction
translates the family `⌈CF⌉₊` times, and the resulting `⌈CF⌉₊`-fold translate family has
ED-multiplicity `Ω(CF)` for *every* admissible choice of translation vectors: a parallel-packing
family of `⌈CF⌉₊` directions inside a `δ^(1/2)`-cap forces multiplicity `≥ c_n · ⌈CF⌉₊`.  Since
the conclusion charges the cap as `(M_cap : ℝ) + 1 ≤ δ ^ (-η)`, no `CF`-independent statement of
this shape can hold.  The upper limit of the range is what
`Kakeya.randCF_smallness_envelope_uniform` can carry; see its docstring for which conjunct
binds. -/
theorem exists_randCF_translation_family_uniform
    [Nontrivial E]
    (η : ℝ) (hη : 0 < η) {η₀ : ℝ} (hη₀_pos : 0 < η₀)
    (hη₀_le_quarter : η₀ ≤ η / 4) (hη₀_le_one : η₀ ≤ 1) :
    ∀ᶠ (δ : ℝ) in 𝓝[>] (0 : ℝ),
    ∀ CF : ℝ, 1 ≤ CF → CF ≤ δ ^ (-η₀) →
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube (Real.toNNReal δ) E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ConvexSpaceBody.IsFrostmanIn s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall (ENNReal.ofReal CF) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      ∃ (ι' : Type v) (s' : Finset ι') (T' : ι' → ShadedTube (Real.toNNReal δ) E)
          (M_cap : ℕ),
        (s'.card : ℝ) ≤ (⌈CF⌉₊ : ℝ) * (s.card : ℝ) ∧
        ((M_cap : ℝ) + 1 ≤ δ ^ (-η)) ∧
        (∀ i, (T' i).carrier ⊆ Metric.closedBall 0 2) ∧
        IsEDUpToMult s' (fun i ↦ (T' i).carrier) M_cap ∧
        ConvexSpaceBody.IsFrostmanIn s' (fun i ↦ (T' i).toConvexSpaceBody)
          (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
          (ENNReal.ofReal (δ ^ (-η))) ∧
        ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) ≥ δ ^ η ∧
        ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          ShadedBody.multiplicity s' (fun i ↦ (T' i).toShadedBody) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  set c_vol : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_vol_def
  have hc_vol_pos : 0 < c_vol := by
    rw [hc_vol_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hT_vol_lb_all : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := fun δ _ T => by
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne (Tube.le_volume (δ := δ) T)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
  set M_vol : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hM_vol_def
  have hM_vol_pos : 0 < M_vol := by
    rw [hM_vol_def]
    unfold Tube.volume_le.C
    push_cast
    positivity
  have hT_vol_ub_all : ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ T : Tube δ E,
      volume.real T.carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) :=
    fun δ _ hδ1 T => by
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      (Tube.volume_le hδ1 T)
    simpa [hM_vol_def, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_pow, MeasureTheory.Measure.real] using hreal
  rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hn.ne') with hfinrank_gt | hfinrank_eq
  · obtain ⟨C_dim, δ₀_thinBox, hC_dim_pos, hδ₀_thinBox_pos, _hδ₀_thinBox_le, hThinBox⟩ :=
      badAgainstSet_count_le_of_ED_thinBox E hfinrank_gt
    set C_pack_ext : ℕ :=
      ⌈(C_dim : ℝ) * netVolThinConstantM E ^ 2 /
        (c_vol / (2 * M_vol)) ^ (Module.finrank ℝ E)⌉₊ with hC_pack_ext_def
    have hC_pack_ext_pos : 0 < C_pack_ext := by
      rw [hC_pack_ext_def]
      exact Nat.ceil_pos.mpr (div_pos
        (mul_pos (by exact_mod_cast hC_dim_pos) (pow_pos (netVolThinConstantM_pos E) 2))
        (pow_pos (div_pos hc_vol_pos (by linarith)) _))
    have hvolB1_pos_env :
        0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
      exact (Metric.measure_closedBall_pos volume 0 one_pos).ne'
    have hvolB2_pos_env :
        0 < volume.real
              (ConvexSpaceBody.cthickening 1
                (ConvexSpaceBody.closedUnitBall (E := E))).carrier := by
      change 0 < volume.real
        (Metric.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
      rw [ConvexSpaceBody.closedUnitBall_carrier,
        _root_.cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1)
          (by norm_num : (0:ℝ) ≤ 1)]
      refine ENNReal.toReal_pos ?_ MeasureTheory.measure_closedBall_lt_top.ne
      refine (Metric.measure_closedBall_pos volume 0 ?_).ne'
      norm_num
    let huc_val : ℝ :=
      @HasUniformTranslation.uniformConstant E _ E _ _ _ _ _
        (instHasUniformTranslationSelf E)
    have huc_pos_env : 0 < huc_val :=
      @HasUniformTranslation.uniformConstantPos E _ E _ _ _ _ _
        (instHasUniformTranslationSelf E)
    filter_upwards
      [(self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ),
       (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one) :
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1),
       (nhdsWithin_le_nhds (Iio_mem_nhds hδ₀_thinBox_pos) :
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < δ₀_thinBox),
       randCF_smallness_envelope_uniform (E := E) hfinrank_gt hη hη₀_pos hη₀_le_quarter
         hη₀_le_one c_vol M_vol hc_vol_pos hM_vol_pos C_pack_ext hC_pack_ext_pos,
       randCF_residual_envelope_uniform (E := E) hfinrank_gt hη
         c_vol M_vol hc_vol_pos hM_vol_pos
         huc_val huc_pos_env
         (netGeomConstantC E) (netGeomConstantC_pos E)
         (volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
         (volume.real
            (ConvexSpaceBody.cthickening 1
              (ConvexSpaceBody.closedUnitBall (E := E))).carrier)
         hvolB1_pos_env hvolB2_pos_env]
      with δ hδ_pos hδ_lt_one hδ_lt_δ₀_thinBox hdev_u hres_u
    intro CF hCF hCF_le
    set M_ED : ℕ := ⌈CF⌉₊ * C_pack_ext + 1 with hM_ED_def
    have hM_ED_pos : 0 < M_ED := by simp [hM_ED_def]
    have hM_ED_ge_JC_pack : ⌈CF⌉₊ * C_pack_ext < M_ED := by
      rw [hM_ED_def]; exact Nat.lt_succ_self _
    have hδ_env := hdev_u CF hCF hCF_le
    have hδ_residual := hres_u CF hCF
    intro ι s T hT_ball hT_ED hT_Frost hT_full
    obtain ⟨_hδ_small, _hδ_lt_cvol, _hδ_small_pack,
        _hδ_band_HIGH_ext, _hδ_lt_Vmax_half_ext, hδ_M_cap_bound,
        hδ_netF_smallness⟩ := hδ_env
    let Ω : Type _ := E
    let _instMeasΩ : MeasurableSpace Ω := (inferInstance : MeasurableSpace E)
    let _hUniform : HasUniformTranslation Ω E := inferInstance
    set J : ℕ := ⌈CF⌉₊ with hJ_def
    have hJ_pos : 0 < J := Nat.ceil_pos.mpr (by linarith : (0 : ℝ) < CF)
    set s' : Finset (ι × Fin J) :=
      s ×ˢ (Finset.univ : Finset (Fin J)) with hs'_def
    have hThinBox_pack :
        ∀ {ι_t : Type v} (s_t : Finset ι_t)
          (T_t : ι_t → Tube (Real.toNNReal δ) E) (T₀'_t : Tube (Real.toNNReal δ) E)
          (_hK_in_B2 : T₀'_t.carrier ⊆ Metric.closedBall (0 : E) (7 / 2))
          (_h_vol_ub :
            volume (Metric.cthickening
              (99 * ((Real.toNNReal δ : NNReal) : ℝ)) T₀'_t.carrier)
              ≤ ENNReal.ofReal (netVolThinConstantM E) *
                (Real.toNNReal δ : ENNReal) ^ (Module.finrank ℝ E - 1))
          (v : E),
          (s_t : Set ι_t).Pairwise
            (fun i j => IsEssentiallyDistinct (T_t i).carrier (T_t j).carrier) →
          (@Finset.filter ι_t
              (fun i => BadAgainstSet ((T_t i).translate v)
                (Metric.cthickening (99 * ((Real.toNNReal δ : NNReal) : ℝ)) T₀'_t.carrier)
                (c_vol / (2 * M_vol)))
              (Classical.decPred _) s_t).card ≤ C_pack_ext := by
      intro ι_t s_t T_t T₀'_t hK_in_B2 h_vol_ub v hED_t
      exact (hThinBox (ι := ι_t) (Real.toNNReal_pos.mpr hδ_pos)
        (by rw [Real.coe_toNNReal δ hδ_pos.le]; exact hδ_lt_δ₀_thinBox.le)
        s_t T_t T₀'_t hK_in_B2 (netVolThinConstantM E) (netVolThinConstantM_pos E)
        h_vol_ub v hED_t).trans (Nat.le_ceil _)
    have hR0_law :
        (HasUniformTranslation.measure (Ω := Ω) (E := E)).map
            (fun ω : Ω => HasUniformTranslation.shift (Ω := Ω) (E := E) ω (0 : E))
          = uniformBallMeasure E := by
      change (uniformBallMeasure E).map (fun t : E => t + 0) = uniformBallMeasure E
      simp
    have hδNN_pos_net : 0 < Real.toNNReal δ := Real.toNNReal_pos.mpr hδ_pos
    have hδNN_le_one_net : Real.toNNReal δ ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one, Real.coe_toNNReal δ hδ_pos.le]
      exact hδ_lt_one.le
    obtain ⟨KTest, hKT_sub, hKT_card, hKT_cover⟩ :=
      exists_netF_test_family.{v, _} E hδNN_pos_net hδNN_le_one_net
    let _NetF : Finset (ConvexSpaceBody E) := KTest
    let _C_cover : ℝ := netGeomConstantC E
    have _hC_cover_pos : (0 : ℝ) < _C_cover := netGeomConstantC_pos E
    have _hNetF_smallness :
        (_NetF.card : ℝ) * Real.exp (10 * Real.exp 1 -
          (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ)) ≤ 1/3 := by
      rw [Real.coe_toNNReal δ hδ_pos.le] at hKT_card
      have hexp_le :
          Real.exp (10 * Real.exp 1 - (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ))
            ≤ Real.exp (10 * Real.exp 1) * δ ^ netGeomConstantM E := by
        rw [show Real.log (1 / δ) = -Real.log δ by rw [one_div, Real.log_inv],
          Real.rpow_def_of_pos hδ_pos, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by
          linarith [Nat.le_ceil (netGeomConstantM E * -Real.log δ)])
      calc (_NetF.card : ℝ)
            * Real.exp (10 * Real.exp 1 - (⌈netGeomConstantM E * Real.log (1 / δ)⌉₊ : ℝ))
          ≤ netGeomConstantC E * δ ^ (-netGeomConstantMRaw E)
              * (Real.exp (10 * Real.exp 1) * δ ^ netGeomConstantM E) :=
            mul_le_mul hKT_card hexp_le (Real.exp_pos _).le
              (mul_nonneg (netGeomConstantC_pos E).le (Real.rpow_nonneg hδ_pos.le _))
        _ = netGeomConstantC E * Real.exp (10 * Real.exp 1) *
              δ ^ (netGeomConstantM E - netGeomConstantMRaw E) := by
            rw [sub_eq_neg_add, Real.rpow_add hδ_pos]; ring
        _ ≤ 1/3 := hδ_netF_smallness
    have hδNN_coe_eq : ((Real.toNNReal δ : NNReal) : ℝ) = δ :=
      Real.coe_toNNReal δ hδ_pos.le
    have hT_vol_lb' : ∀ i ∈ s,
        c_vol * ((Real.toNNReal δ : NNReal) : ℝ) ^ (Module.finrank ℝ E - 1)
          ≤ volume.real (T i).carrier :=
      fun i _ => hT_vol_lb_all (Real.toNNReal δ) hδNN_pos_net (T i).toTube
    have hT_vol_ub' : ∀ i ∈ s,
        volume.real (T i).carrier ≤
          M_vol * ((Real.toNNReal δ : NNReal) : ℝ) ^ (Module.finrank ℝ E - 1) :=
      fun i _ => hT_vol_ub_all (Real.toNNReal δ) hδNN_pos_net hδNN_le_one_net (T i).toTube
    have hR_translate :
        ∀ (i : ι) (ω : Ω),
          ((HasUniformTranslation.shift (Ω := Ω) (E := E) ω).actShadedTube
            (T i)).carrier
              = ((T i).toTube.translate
                  (HasUniformTranslation.shift (Ω := Ω) (E := E) ω 0)).carrier := by
      intro i ω'
      change (fun y : E => ω' + y) '' (T i).carrier =
        (fun y : E => (ω' + 0) + y) '' (T i).carrier
      simp
    have hδ_pos_NN_coe : 0 < ((Real.toNNReal δ : NNReal) : ℝ) := by rwa [hδNN_coe_eq]
    have hδ_lt_one_NN_coe : ((Real.toNNReal δ : NNReal) : ℝ) < 1 := by rwa [hδNN_coe_eq]
    have hδ_M_cap_bound' :
        ((max M_ED C_pack_ext : ℕ) : ℝ) *
            (((max M_ED C_pack_ext : ℕ) : ℝ) +
             (⌈netGeomConstantM E * Real.log (1 / ((Real.toNNReal δ : NNReal) : ℝ))⌉₊ : ℝ) +
             (⌈10 * Real.exp 1 + Real.log (3 * netGeomConstantC E)⌉₊ : ℝ) + 1) + 1
          ≤ ((Real.toNNReal δ : NNReal) : ℝ) ^ (-η) := by
      rwa [hδNN_coe_eq]
    have hT_full' :
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
          ≥ (Real.toNNReal δ) ^ η := by
      have h1 :
          ((Real.toNNReal δ : NNReal) ^ η : ℝ)
            ≤ ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : NNReal) : ℝ) := by
        rwa [show ((Real.toNNReal δ : NNReal) ^ η : ℝ) = δ ^ η by rw [hδNN_coe_eq]]
      exact_mod_cast h1
    have hδ_residual' :
        (⌈netGeomConstantM E * Real.log (1 / ((Real.toNNReal δ : NNReal) : ℝ))⌉₊ : ℝ) *
            (max (HasUniformTranslation.uniformConstant Ω E * (⌈CF⌉₊ : ℝ))
              (CF * M_vol / (c_vol *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)) + 1) *
            volume.real
              (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall (E := E))).carrier *
            M_vol * _C_cover
          < ((Real.toNNReal δ : NNReal) : ℝ) ^ (-η) * (⌈CF⌉₊ : ℝ) * c_vol := by
      rwa [hδNN_coe_eq]
    obtain ⟨ω, M_cap, hM_cap_bound, hω_ball, hω_ED, hω_Frost⟩ :=
      randCF_chernoff_witness (E := E) (Ω := Ω) (δ := Real.toNNReal δ) hR0_law
        hfinrank_gt hδ_pos_NN_coe hδ_lt_one_NN_coe hη hCF
        c_vol M_vol hc_vol_pos hM_vol_pos
        C_pack_ext hC_pack_ext_pos M_ED hM_ED_pos hM_ED_ge_JC_pack
        hδ_M_cap_bound' hThinBox_pack
        s T hT_ball hT_ED hT_Frost hT_full'
        hT_vol_lb' hT_vol_ub' hR_translate
        _NetF _C_cover _hC_cover_pos hδ_residual'
        (by
          intro ω _hBdd K' _hK'
          obtain ⟨K, hK_mem, hK_le⟩ :=
            hKT_cover (s ×ˢ (Finset.univ : Finset (Fin ⌈CF⌉₊)))
              (fun p : ι × Fin ⌈CF⌉₊ =>
                ((HasUniformTranslation.shift (Ω := Ω) (E := E)
                    (ω p.2)).actShadedTube (T p.1)).toConvexSpaceBody)
              (fun p _ => translation_preserves_carrier_in_ball_plus_one E (T p.1)
                (hT_ball p.1) (ω p.2) (_hBdd p.2))
              (fun p _ => Tube.le_ethickness_scale ((HasUniformTranslation.shift
                (Ω := Ω) (E := E) (ω p.2)).actShadedTube (T p.1)).toTube)
          refine ⟨K, hK_mem, ?_, (le_maxDensity _ _ K').trans hK_le⟩
          intro x hxK
          change x ∈ Metric.cthickening 1 (Metric.closedBall (0 : E) 1)
          rw [_root_.cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1)
                (by norm_num : (0:ℝ) ≤ 1), show (1 : ℝ) + 1 = 2 by norm_num]
          exact hKT_sub K hK_mem hxK)
        hKT_sub
        (by
          intro K _hK i _hi
          refine IsClosed.measurableSet ?_
          have hset_eq :
              HasUniformTranslation.tubeContainedSet (Ω := E)
                  ((T i).toTube) K.carrier =
                ⋂ x ∈ ((T i).toTube).carrier,
                  {t : E | t + x ∈ K.carrier} := by
            ext t
            simp only [HasUniformTranslation.tubeContainedSet, Set.mem_setOf_eq,
              Translation.actSet, Set.image_subset_iff, Set.mem_iInter]
            refine ⟨fun h x hx => h hx, fun h x hx => h x hx⟩
          rw [hset_eq]
          refine isClosed_biInter fun x _hx => ?_
          have hcont : Continuous (fun t : E => t + x) :=
            continuous_id.add continuous_const
          exact K.isCompact.isClosed.preimage hcont)
        (by
          rcases Finset.eq_empty_or_nonempty s with hs_empty | hs_ne
          · rw [show ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) = 0 by
              rw [hs_empty]; simp] at hT_full
            simp only [NNReal.coe_zero] at hT_full
            linarith [Real.rpow_pos_of_pos hδ_pos η]
          · exact Finset.card_pos.mpr hs_ne)
        (by rw [hδNN_coe_eq]; exact _hNetF_smallness)
    set T' : (ι × Fin J) → ShadedTube (Real.toNNReal δ) E :=
      fun p : ι × Fin J =>
        (HasUniformTranslation.shift (Ω := Ω) (E := E) (ω p.2)).actShadedTube (T p.1)
      with hT'_def
    refine ⟨ι × Fin J, s', T', M_cap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hcard : s'.card = s.card * J := by
        rw [hs'_def, Finset.card_product, Finset.card_univ, Fintype.card_fin]
      rw [hcard]
      push_cast
      rw [hJ_def, mul_comm]
    · rwa [hδNN_coe_eq] at hM_cap_bound
    · intro p
      exact translation_preserves_carrier_in_ball_plus_one (Ω := Ω) (E := E)
        (T p.1) (hT_ball p.1) (ω p.2) (hω_ball p.2)
    · exact hω_ED
    · rwa [hδNN_coe_eq] at hω_Frost
    · change ShadedBody.fullness s' (fun p : ι × Fin J => (T' p).toShadedBody) ≥ δ ^ η
      rw [hs'_def, hT'_def,
        fullness_eq_under_product_translation (Ω := Ω) (E := E) s T J hJ_pos ω]
      exact hT_full
    · change ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
           ShadedBody.multiplicity s' (fun p : ι × Fin J => (T' p).toShadedBody)
      rw [hs'_def, hT'_def]
      exact multiplicity_le_under_product_translation (Ω := Ω) (E := E) s T J hJ_pos ω
  · filter_upwards
      [(self_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ),
       (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one) :
          ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1),
       eventually_le_rpow_neg hη 2,
       eventually_le_rpow_neg hη (volume.real (Metric.closedBall (0 : E) 2) / c_vol)]
      with δ hδ_pos _hδ_lt_one h_two_le h_volB2_cvol_le
    intro CF hCF hCF_le ι s T hT_ball hT_ED hT_Frost hT_full
    refine ⟨ι, s, T, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_mul_of_one_le_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.ceil_pos.mpr (by linarith : (0 : ℝ) < CF))
    · rw [show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]; exact h_two_le
    · intro i
      exact Set.Subset.trans (hT_ball i)
        (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))
    · intro i hi
      refine (Finset.card_le_card ?_).trans (Finset.card_singleton i).le
      intro j hj
      simp only [notEssDistinctSet, Finset.mem_filter] at hj
      by_contra hji
      exact hj.2 (hT_ED hj.1 hi (by simpa using hji))
    · set K1 : ConvexSpaceBody E :=
        ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E)
      have hK1_carrier : K1.carrier = Metric.closedBall (0 : E) 2 := by
        change Metric.cthickening 1 (Metric.closedBall (0 : E) 1) = _
        rw [cthickening_closedBall (by norm_num : (0 : ℝ) ≤ 1)
              (by norm_num : (0 : ℝ) ≤ 1)]
        norm_num
      have hT_le_K1 : ∀ i, (T i).toConvexSpaceBody ≤ K1 := by
        intro i x hx
        change x ∈ K1.carrier
        rw [hK1_carrier]
        exact Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)
          (hT_ball i hx)
      have hT_vol_lb_real : ∀ i, c_vol ≤ volume.real (T i).carrier := fun i => by
        have hbnd' := hT_vol_lb_all (Real.toNNReal δ)
          (Real.toNNReal_pos.mpr hδ_pos) (T i).toTube
        rw [show Module.finrank ℝ E - 1 = 0 by omega] at hbnd'
        simpa using hbnd'
      have hT_vol_lb_enn : ∀ i, ENNReal.ofReal c_vol ≤ volume (T i).carrier := fun i => by
        rw [← ENNReal.ofReal_toReal
          (T i).toShadedBody.toConvexSpaceBody.isCompact'.measure_ne_top]
        exact ENNReal.ofReal_le_ofReal (hT_vol_lb_real i)
      intro K' _hK'_le_K1
      by_cases hany : ∃ i ∈ s, (fun i ↦ (T i).toConvexSpaceBody) i ≤ K'
      · obtain ⟨i₀, hi₀_s, hi₀_le⟩ := hany
        have hvol_K'_lb : ENNReal.ofReal c_vol ≤ volume K'.carrier :=
          (hT_vol_lb_enn i₀).trans (measure_mono hi₀_le)
        have h_num_le_full :
            (∑ i ∈ s with (fun i ↦ (T i).toConvexSpaceBody) i ≤ K',
              volume (T i).carrier) ≤
              (∑ i ∈ s, volume ((fun i ↦ (T i).toConvexSpaceBody) i).carrier) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        have h_full_eq :
            (∑ i ∈ s, volume ((fun i ↦ (T i).toConvexSpaceBody) i).carrier)
              = densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 * volume K1.carrier :=
          Kakeya.sum_volume_eq_densityIn_mul_volume'
            (fun i _ => hT_le_K1 i)
        have h_ratio_le_ENN :
            volume K1.carrier / ENNReal.ofReal c_vol
              ≤ ENNReal.ofReal (δ ^ (-η)) := by
          rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hc_vol_pos).ne'
              ENNReal.ofReal_ne_top, hK1_carrier,
            show volume (Metric.closedBall (0 : E) 2)
                = ENNReal.ofReal (volume.real (Metric.closedBall (0 : E) 2)) from
              (ENNReal.ofReal_toReal MeasureTheory.measure_closedBall_lt_top.ne).symm,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos.le _)]
          exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc_vol_pos).mp h_volB2_cvol_le)
        calc densityIn s (fun i ↦ (T i).toConvexSpaceBody) K'
            = (∑ i ∈ s with (fun i ↦ (T i).toConvexSpaceBody) i ≤ K',
                volume (T i).carrier) / volume K'.carrier := rfl
          _ ≤ (∑ i ∈ s, volume ((fun i ↦ (T i).toConvexSpaceBody) i).carrier)
                / volume K'.carrier := ENNReal.div_le_div_right h_num_le_full _
          _ = (densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 * volume K1.carrier)
                / volume K'.carrier := by rw [h_full_eq]
          _ ≤ (densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 * volume K1.carrier)
                / ENNReal.ofReal c_vol :=
              ENNReal.div_le_div_left hvol_K'_lb _
          _ = densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 *
                (volume K1.carrier / ENNReal.ofReal c_vol) :=
              mul_div_assoc _ _ _
          _ ≤ densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 *
                ENNReal.ofReal (δ ^ (-η)) := mul_le_mul_right h_ratio_le_ENN _
          _ = ENNReal.ofReal (δ ^ (-η)) *
                densityIn s (fun i ↦ (T i).toConvexSpaceBody) K1 := mul_comm _ _
      · have h_zero : densityIn s (fun i ↦ (T i).toConvexSpaceBody) K' = 0 := by
          change (∑ i ∈ s with (fun i ↦ (T i).toConvexSpaceBody) i ≤ K',
              volume (T i).carrier) / volume K'.carrier = 0
          rw [Finset.filter_eq_empty_iff.mpr fun i hi h_le => hany ⟨i, hi, h_le⟩, Finset.sum_empty]
          exact ENNReal.zero_div
        rw [h_zero]
        exact bot_le
    · exact hT_full
    · exact le_refl _

end RandCF

end Kakeya
