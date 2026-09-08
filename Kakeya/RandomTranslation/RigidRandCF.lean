/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidFrostmanGood

/-!
# One rigid tuple that is simultaneously Frostman-good and ED-good

GWZ Lemma 3.8 needs a single tuple of rigid motions for which the randomised family satisfies *two*
unrelated conditions. This file intersects the two events.

## The probability budget

* event `A` — the Frostman conjunct, `Kakeya.rigid_frostman_bad_prob_lt`: `P(Aᶜ) < 1/4`;
* event `B` — the ED conjunct, `Kakeya.rigid_ed_bad_prob_lt`: `P(Bᶜ) < 1/4`;
* event `C` — the translation parts lie in `B₁`, which by
  `Kakeya.rigidPiMeasure_translation_outside_eq_zero` has `P(Cᶜ) = 0`.

No independence is claimed or needed. The union bound gives
`P(A ∩ B ∩ C) ≥ 1 - 1/4 - 1/4 - 0 = 1/2 > 0`, so the intersection is nonempty and a tuple can be
extracted. Both `1/4`s are slack: each event actually fails with probability below `1/10`.

## What the two events contribute

The Frostman conjunct's smallness threshold on `δ` is free of the Frostman constant because the
factor `J` cancels between the Chernoff cap and the ambient density (see `RigidFrostmanGood.lean`).
The ED conjunct's threshold `rigidMED C_EDlog δ = O(log (1/δ))` is free of it because random *rigid*
motions, unlike random translations, give the two-sided estimate GWZ (106)
`P[R(T) ⊆ 100 T₀] ≲ |T_δ|²` rather than only `≲ |T_δ|`. Together these are what make GWZ Lemma 3.9
uniform in `C_F`, replacing the old `M_ED := ⌈C_F⌉₊ · C_pack_ext + 1`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal}

/-- **Rigid motions preserve fullness.** Each of the `J` copies has the same shade volume and the
same carrier volume as the tube it came from, so both the numerator and the denominator of `λ` are
multiplied by `J`. -/
theorem fullness_rigidProduct {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (J : ℕ) (hJ : 0 < J) (ω : Fin J → unitary (E →L[ℝ] E) × E) :
    ShadedBody.fullness (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p => (rigidProduct T J ω p).toShadedBody)
      = ShadedBody.fullness s (fun i => (T i).toShadedBody) := by
  set V : ι → ShadedBody E := fun i => (T i).toShadedBody with hV_def
  set V' : (ι × Fin J) → ShadedBody E :=
    fun p => (rigidProduct T J ω p).toShadedBody with hV'_def
  have hcard : (Finset.univ : Finset (Fin J)).card = J := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.coe_inj, ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  unfold ShadedBody.fullness'
  have hnum_e :
      ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (V' p).shade =
        (J : ENNReal) * ∑ i ∈ s, volume (V i).shade := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∀ j, volume (V' (i, j)).shade = volume (V i).shade := by
      intro j
      change volume (rigidProduct T J ω (i, j)).shade = volume (T i).shade
      rw [rigidProduct_apply, ShadedTube.volume_rigidMove_shade]
    simp_rw [h1]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hden_e :
      ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume (V' p).carrier =
        (J : ENNReal) * ∑ i ∈ s, volume (V i).carrier := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∀ j, volume (V' (i, j)).carrier = volume (V i).carrier := by
      intro j
      change volume (rigidProduct T J ω (i, j)).carrier = volume (T i).carrier
      rw [rigidProduct_apply, ShadedTube.volume_rigidMove_carrier]
    simp_rw [h1]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  rw [hnum_e, hden_e]
  have hJ_ne_zero : (J : ENNReal) ≠ 0 := by
    exact_mod_cast hJ.ne'
  have hJ_ne_top : (J : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_div_mul_left _ _ hJ_ne_zero hJ_ne_top]

/-- **Rigid motions do not decrease multiplicity.** The shade mass grows by exactly `J` while the
union of the shades grows by at most `J`, so the ratio does not drop. -/
theorem multiplicity_le_rigidProduct {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (J : ℕ) (hJ : 0 < J) (ω : Fin J → unitary (E →L[ℝ] E) × E) :
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
      ≤ ShadedBody.multiplicity (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (rigidProduct T J ω p).toShadedBody) := by
  set V : ι → ShadedBody E := fun i => (T i).toShadedBody with hV_def
  set V' : (ι × Fin J) → ShadedBody E :=
    fun p => (rigidProduct T J ω p).toShadedBody with hV'_def
  have hcard : (Finset.univ : Finset (Fin J)).card = J := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hnum :
      ∑ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)), volume.real (V' p).shade =
        (J : ℝ) * ∑ i ∈ s, volume.real (V i).shade := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∀ j, volume.real (V' (i, j)).shade = volume.real (V i).shade :=
      fun j => by
        change (volume (V' (i, j)).shade).toReal = (volume (V i).shade).toReal
        exact congrArg ENNReal.toReal
          (ShadedTube.volume_rigidMove_shade (T i) (ω j).1 (ω j).2)
    simp_rw [h1]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hfin_un : volume (⋃ i ∈ s, (V i).shade) ≠ ⊤ := by
    have hsubset : (⋃ i ∈ s, (V i).shade) ⊆ ⋃ i ∈ s, (V i).carrier :=
      Set.iUnion₂_mono fun i _ => (V i).shade_subset
    have hcompact : IsCompact (⋃ i ∈ s, (V i).carrier) :=
      s.isCompact_biUnion fun i _ => (V i).isCompact'
    exact ne_top_of_le_ne_top hcompact.measure_lt_top.ne
      (MeasureTheory.measure_mono hsubset)
  have hsubset_union : (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ⊆
      ⋃ j ∈ (Finset.univ : Finset (Fin J)),
        Kakeya.rigidMap (ω j).1 (ω j).2 '' (⋃ i ∈ s, (V i).shade) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.mpr ⟨p.2, Finset.mem_univ _, ?_⟩
    have hxp' : x ∈ Kakeya.rigidMap (ω p.2).1 (ω p.2).2 '' (V p.1).shade := by
      change x ∈ ((T p.1).rigidMove (ω p.2).1 (ω p.2).2).shade at hxp
      rw [ShadedTube.rigidMove_shade] at hxp
      exact hxp
    rcases hxp' with ⟨y, hy, hxy⟩
    exact ⟨y, Set.mem_iUnion₂.mpr ⟨p.1, (Finset.mem_product.mp hp).1, hy⟩, hxy⟩
  have hden_le_meas :
      volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ≤
        (J : ENNReal) * volume (⋃ i ∈ s, (V i).shade) := by
    have h1 : volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ≤
        volume (⋃ j ∈ (Finset.univ : Finset (Fin J)),
          Kakeya.rigidMap (ω j).1 (ω j).2 '' (⋃ i ∈ s, (V i).shade)) :=
      MeasureTheory.measure_mono hsubset_union
    have h2 :
        volume (⋃ j ∈ (Finset.univ : Finset (Fin J)),
            Kakeya.rigidMap (ω j).1 (ω j).2 '' (⋃ i ∈ s, (V i).shade)) ≤
          ∑ j ∈ (Finset.univ : Finset (Fin J)),
            volume (Kakeya.rigidMap (ω j).1 (ω j).2 ''
              (⋃ i ∈ s, (V i).shade)) :=
      MeasureTheory.measure_biUnion_finset_le (Finset.univ : Finset (Fin J)) _
    have heq_each : ∀ j : Fin J,
        volume (Kakeya.rigidMap (ω j).1 (ω j).2 '' (⋃ i ∈ s, (V i).shade)) =
          volume (⋃ i ∈ s, (V i).shade) :=
      fun j => ShadedTube.volume_rigidMap_image (ω j).1 (ω j).2
        (⋃ i ∈ s, (V i).shade)
    simp_rw [heq_each] at h2
    rw [Finset.sum_const, hcard] at h2
    have h2' : volume (⋃ j ∈ (Finset.univ : Finset (Fin J)),
            Kakeya.rigidMap (ω j).1 (ω j).2 '' (⋃ i ∈ s, (V i).shade)) ≤
          (J : ENNReal) * volume (⋃ i ∈ s, (V i).shade) := by
      simpa [nsmul_eq_mul] using h2
    exact le_trans h1 h2'
  have hden_le :
      volume.real (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ≤
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
  set B' : ℝ := volume.real
      (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) with hB'_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
  have hB_nn : 0 ≤ B := ENNReal.toReal_nonneg
  have hB'_nn : 0 ≤ B' := ENNReal.toReal_nonneg
  have hA_le_cardB : A ≤ s.card * B := by
    have h_fin : ∀ i ∈ s, volume (V i).shade ≠ ⊤ := by
      intro i _
      exact ne_top_of_le_ne_top (V i).isCompact'.measure_lt_top.ne
        (MeasureTheory.measure_mono (V i).shade_subset)
    have h_le : ∀ i ∈ s, volume (V i).shade ≤ volume (⋃ j ∈ s, (V j).shade) := by
      intro i hi
      exact MeasureTheory.measure_mono fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
    simp only [hA_def, hB_def]
    unfold MeasureTheory.Measure.real
    rw [← ENNReal.toReal_sum h_fin]
    have h_sum_le :
        ∑ i ∈ s, volume (V i).shade ≤ s.card * volume (⋃ j ∈ s, (V j).shade) := by
      calc
        ∑ i ∈ s, volume (V i).shade
            ≤ ∑ _ ∈ s, volume (⋃ j ∈ s, (V j).shade) := Finset.sum_le_sum h_le
        _ = s.card * volume (⋃ j ∈ s, (V j).shade) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have h_top : (s.card : ENNReal) * volume (⋃ j ∈ s, (V j).shade) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hfin_un
    have htoReal := ENNReal.toReal_mono h_top h_sum_le
    rw [ENNReal.toReal_mul] at htoReal
    have hcardtoReal : ((s.card : ENNReal)).toReal = (s.card : ℝ) := by simp
    rw [hcardtoReal] at htoReal
    exact htoReal
  have hfin_un' :
      volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ≠ ⊤ := by
    have hsubset' : (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ⊆
        ⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).carrier :=
      Set.iUnion₂_mono fun p _ => (V' p).shade_subset
    have hcompact' : IsCompact
        (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).carrier) :=
      (s ×ˢ Finset.univ).isCompact_biUnion fun p _ => (V' p).isCompact'
    exact ne_top_of_le_ne_top hcompact'.measure_lt_top.ne
      (MeasureTheory.measure_mono hsubset')
  have hfin_sumS : ∑ i ∈ s, volume (V i).shade ≠ ⊤ := by
    refine ENNReal.sum_ne_top.mpr fun i _ => ?_
    exact ne_top_of_le_ne_top (V i).isCompact'.measure_lt_top.ne
      (MeasureTheory.measure_mono (V i).shade_subset)
  have hfin_sumS' : ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), volume (V' p).shade ≠ ⊤ := by
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
            volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) = 0 := by
          by_contra h
          have : 0 < B' := ENNReal.toReal_pos h hfin_un'
          linarith
        have h_each_zero : ∀ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
            volume.real (V' p).shade = 0 := by
          intro p hp
          have hsub : (V' p).shade ⊆
              ⋃ q ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' q).shade :=
            fun x hx => Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩
          have : volume (V' p).shade = 0 :=
            MeasureTheory.measure_mono_null hsub hB'_meas_zero
          unfold MeasureTheory.Measure.real
          rw [this]; simp
        have hsum_zero : ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))),
            volume.real (V' p).shade = 0 := Finset.sum_eq_zero h_each_zero
        rw [hnum] at hsum_zero
        have hA_zero : A = 0 := by
          rcases mul_eq_zero.mp hsum_zero with h | h
          · exact absurd h (Nat.cast_ne_zero.mpr hJ.ne')
          · exact h
        rw [hA_zero]; simp
      · have hB'_pos : 0 < B' := lt_of_le_of_ne hB'_nn (Ne.symm hB'_zero)
        rw [div_le_div_iff₀ hB_pos hB'_pos]
        calc
          A * B' ≤ A * ((J : ℝ) * B) :=
              mul_le_mul_of_nonneg_left hden_le hA_nn
          _ = (J : ℝ) * A * B := by ring
  change (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade) ≤
    (∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), volume (V' p).shade) /
      volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade)
  have hLHS_ne_top :
      (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade) ≠ ⊤ := by
    by_cases hB : volume (⋃ i ∈ s, (V i).shade) = 0
    · have hsum0 : ∑ i ∈ s, volume (V i).shade = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hsub : (V i).shade ⊆ ⋃ j ∈ s, (V j).shade :=
          fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
        exact MeasureTheory.measure_mono_null hsub hB
      simp [hsum0]
    · exact ENNReal.div_ne_top hfin_sumS hB
  have hRHS_ne_top :
      (∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), volume (V' p).shade) /
        volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) ≠ ⊤ := by
    by_cases hB' : volume (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) = 0
    · have hsum0 : ∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), volume (V' p).shade = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hsub : (V' p).shade ⊆
            ⋃ q ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' q).shade :=
          fun x hx => Set.mem_iUnion₂.mpr ⟨p, hp, hx⟩
        exact MeasureTheory.measure_mono_null hsub hB'
      simp [hsum0]
    · exact ENNReal.div_ne_top hfin_sumS' hB'
  rw [← ENNReal.toReal_le_toReal hLHS_ne_top hRHS_ne_top]
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  rw [ENNReal.toReal_sum (fun i _ => ne_top_of_le_ne_top (V i).isCompact'.measure_lt_top.ne
        (MeasureTheory.measure_mono (V i).shade_subset))]
  rw [ENNReal.toReal_sum (fun p _ => ne_top_of_le_ne_top (V' p).isCompact'.measure_lt_top.ne
        (MeasureTheory.measure_mono (V' p).shade_subset))]
  change (∑ i ∈ s, volume.real (V i).shade) / volume.real (⋃ i ∈ s, (V i).shade) ≤
    (∑ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), volume.real (V' p).shade) /
      volume.real (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade)
  rw [show (∑ i ∈ s, volume.real (V i).shade) = A from rfl,
      show volume.real (⋃ i ∈ s, (V i).shade) = B from rfl,
      show volume.real (⋃ p ∈ (s ×ˢ (Finset.univ : Finset (Fin J))), (V' p).shade) = B' from rfl,
      hnum]
  exact h_real

/-- **One rigid tuple satisfying both conjuncts of GWZ Lemma 3.8.**

The eventual `δ`-set is quantified *before* the family and carries no reference to the Frostman
constant; `J` is introduced only afterwards and is admissible for `J := ⌈C_F⌉₊`. The ED cap
`rigidMED C_EDlog δ` is `O(log (1/δ))` and is likewise free of the Frostman constant. -/
theorem exists_rigid_tuple_frostman_and_ed [Nontrivial E] (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η) :
    ∃ C_EDlog : ℝ, 0 < C_EDlog ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) →
      (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      0 < s.card →
      ∀ J : ℕ, 0 < J →
        (ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall).toReal ≤ (J : ℝ) →
        (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
        ∃ (NetT : Finset (Tube δ E)) (ω : Fin J → unitary (E →L[ℝ] E) × E),
          (∀ T₀ ∈ NetT, T₀.carrier ⊆ closedBall (0 : E) (7 / 2)) ∧
          (∀ T₀ : Tube δ E, T₀.carrier ⊆ closedBall (0 : E) 2 →
            ∃ T₀' ∈ NetT,
              T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ∧
          (∀ j, (ω j).2 ∈ closedBall (0 : E) 1) ∧
          ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
            (ConvexSpaceBody.cthickening 1
              (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
            (ENNReal.ofReal ((δ : ℝ) ^ (-η))) ∧
          (∀ T₀ ∈ NetT,
            ∑ j : Fin J, edBadCountAt s (fun i => (T i).toTube) T₀ J j ω
              ≤ ((rigidMED C_EDlog δ : ℕ) : ℝ)) := by
  classical
  obtain ⟨C_EDlog, hC_pos, hED_filter⟩ := rigid_ed_bad_prob_lt (E := E) hn
  refine ⟨C_EDlog, hC_pos, ?_⟩
  filter_upwards [rigid_frostman_bad_prob_lt (E := E) hn hη, hED_filter] with δ hF hED
  intro ι s T hT_ball hED_pairwise hs_card J hJ hJ_ge hJ_le
  obtain ⟨NetT, hNetB, happrox, hBadED⟩ :=
    hED s (fun i => (T i).toTube) (by simpa using hT_ball) (by simpa using hED_pairwise) J hJ
      (by simpa using hJ_le)
  set BadF : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ¬ ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (ENNReal.ofReal ((δ : ℝ) ^ (-η)))}
  set BadED : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ∃ T₀ ∈ NetT, ((rigidMED C_EDlog δ : ℕ) : ℝ) <
      ∑ j : Fin J, edBadCountAt s (fun i => (T i).toTube) T₀ J j ω}
  set Out : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ∃ j, (ω j).2 ∉ closedBall (0 : E) 1}
  let μ : Measure (Fin J → unitary (E →L[ℝ] E) × E) := rigidPiMeasure E J
  have hμuniv : μ Set.univ = 1 := by
    change rigidPiMeasure E J Set.univ = 1
    exact (inferInstance : IsProbabilityMeasure (rigidPiMeasure E J)).measure_univ
  have hunion : μ (BadF ∪ BadED ∪ Out) < 1 := by
    have hFm : μ BadF < ENNReal.ofReal (1 / 4) := by
      simpa [μ, BadF] using hF s T hT_ball hs_card J hJ hJ_ge
    have hEm : μ BadED < ENNReal.ofReal (1 / 4) := by
      simpa [μ, BadED] using hBadED
    have hOm : μ Out = 0 := by
      simpa [μ, Out] using rigidPiMeasure_translation_outside_eq_zero (E := E) J
    have hle : μ (BadF ∪ BadED ∪ Out) ≤ μ BadF + μ BadED + μ Out := by
      calc
        μ (BadF ∪ BadED ∪ Out) ≤ μ (BadF ∪ BadED) + μ Out :=
          measure_union_le (BadF ∪ BadED) Out
        _ ≤ (μ BadF + μ BadED) + μ Out :=
          add_le_add (measure_union_le BadF BadED) le_rfl
    have hFle : μ BadF ≤ ENNReal.ofReal (1 / 4) := le_of_lt hFm
    have hEle : μ BadED ≤ ENNReal.ofReal (1 / 4) := le_of_lt hEm
    have hleq : μ BadF + μ BadED + μ Out ≤
        ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + 0 := by
      exact add_le_add (add_le_add hFle hEle) hOm.le
    have hsum : ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + 0 =
        ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
        (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ)), add_zero]
      rw [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num]
    have hle2 : μ BadF + μ BadED + μ Out ≤ ENNReal.ofReal (1 / 2) := by
      rw [← hsum]
      exact hleq
    have hhalf : ENNReal.ofReal (1 / 2) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < (1 : ℝ))).mpr
        (by norm_num : (1 / 2 : ℝ) < 1)
    exact lt_of_le_of_lt (le_trans hle hle2) hhalf
  have hUneq : BadF ∪ BadED ∪ Out ≠ Set.univ := by
    intro hEq
    have : μ (BadF ∪ BadED ∪ Out) = 1 := by rw [hEq]; exact hμuniv
    exact (ne_of_lt hunion) this
  obtain ⟨ω, hωnot⟩ : ∃ ω, ω ∉ BadF ∪ BadED ∪ Out := by
    by_contra hbad
    have hAll : (BadF ∪ BadED ∪ Out) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro z
      by_contra hz
      exact hbad ⟨z, hz⟩
    exact hUneq hAll
  have hnotF : ω ∉ BadF := by
    intro hmem
    exact hωnot (by simp [hmem])
  have hnotED : ω ∉ BadED := by
    intro hmem
    exact hωnot (by simp [hmem])
  have hout : ω ∉ Out := by
    intro hmem
    exact hωnot (by simp [hmem])
  have hBall : ∀ j, (ω j).2 ∈ closedBall (0 : E) 1 := by
    intro j
    by_contra hb
    exact hout ⟨j, hb⟩
  have hFrost : ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
    by_contra hbad
    exact hnotF (by simpa [BadF] using hbad)
  have hEDgood : ∀ T₀ ∈ NetT,
      ∑ j : Fin J, edBadCountAt s (fun i => (T i).toTube) T₀ J j ω
        ≤ ((rigidMED C_EDlog δ : ℕ) : ℝ) := by
    intro T₀ hT₀
    have hnotBad : ¬ (((rigidMED C_EDlog δ : ℕ) : ℝ) <
        ∑ j : Fin J, edBadCountAt s (fun i => (T i).toTube) T₀ J j ω) := by
      by_contra hbad
      exact hnotED (by simpa [BadED] using ⟨T₀, hT₀, hbad⟩)
    exact not_lt.mp hnotBad
  exact ⟨NetT, ω, hNetB, happrox, hBall, hFrost, hEDgood⟩

end

end Kakeya

end
