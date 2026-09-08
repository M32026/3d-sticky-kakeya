/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidEDFail
public import Kakeya.RandomTranslation.RigidFrostmanGood
public import Kakeya.Tube.EDUpToMult

/-!
# The deterministic bridge: net-goodness ⇒ `IsEDUpToMult`

This is the deterministic half of the ED conjunct of GWZ Lemma 3.8, ported from the translation-only
`hω_ED` block of `RandCF.lean` (lines 2441-2670). The probabilistic input is
`Kakeya.rigid_edFail_bad_prob_lt`; this file converts it into the `IsEDUpToMult` predicate that
`Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` consumes.

## The argument, unchanged from the translation case

Fix a copy `Q = R_{ω j₀}(T i₀)` of the randomised family.

1. `Q` lies in `B(0,2)` (`Kakeya.rigidProduct_carrier_subset_closedBall_two`), so the thin-tube net
   supplies `T₀' ∈ NetT` with `Q.carrier ⊆ cthickening (99δ) T₀'.carrier`.
2. Any copy `P` failing to be essentially distinct from `Q` is `BadAgainstSet` against that thin
   box: this is `Kakeya.badAgainstSet_of_notED_subset_cthickening`, whose density threshold
   `c_low / (2 · c_up)` with `c_low = c_vol·δ^(n-1)`, `c_up = M_vol·δ^(n-1)` is exactly
   `Kakeya.edBridgeConstant E` — the `δ^(n-1)` factors cancel.
3. Hence the non-ED set injects into the union over `j` of the per-copy bad sets, whose
   cardinalities are by definition `Kakeya.edFailCount`.
4. Net-goodness bounds `∑ j, edFailCount … T₀' (ω j)` by `M`.

**The multiplicity is exactly `M`.** No dimensional constant is lost: steps 2-4 are an injection
followed by a fibrewise count, so `Cfixed = 1` and no additive term appears. This is why the final
ED cap is literally `rigidMED C_EDlog δ`, still `O(log (1/δ))` and still free of the Frostman
constant.

Only the volume comparability of the copies is used, so the original family's own
essential-distinctness and Frostman data are *not* needed here — they enter only through the
probabilistic input.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal}

/-- The bridge density threshold, as it arises from
`Kakeya.badAgainstSet_of_notED_subset_cthickening` with the two tube-volume constants scaled by
`δ^(n-1)`, equals the scale-free `Kakeya.edBridgeConstant`. -/
theorem edBridgeConstant_eq_scaled (hδ : 0 < δ) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ)
          * (δ : ℝ) ^ (Module.finrank ℝ E - 1) /
        (2 * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ)
          * (δ : ℝ) ^ (Module.finrank ℝ E - 1)))
      = edBridgeConstant E := by
  unfold edBridgeConstant
  have hδ_ne : (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≠ 0 := by
    exact pow_ne_zero _ (NNReal.coe_pos.mpr hδ).ne'
  have hM_vol_ne : ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ) ≠ 0 := by
    unfold Tube.volume_le.C
    push_cast
    positivity
  field_simp [hM_vol_ne, hδ_ne]

/-- Every copy of the randomised family that fails to be essentially distinct from a given copy is
`BadAgainstSet` against the thin box approximating that copy. -/
theorem badAgainstSet_of_notED_rigidProduct [Nontrivial E] (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} (T : ι → ShadedTube δ E) (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E)
    (K : Set E) (p₀ p : ι × Fin J)
    (hsub : (rigidProduct T J ω p₀).carrier ⊆ K)
    (hnotED : ¬ IsEssentiallyDistinct (rigidProduct T J ω p).carrier
      (rigidProduct T J ω p₀).carrier) :
    BadAgainstSet ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2) K (edBridgeConstant E) := by
  classical
  set c_vol : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_vol_def
  set M_vol : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hM_vol_def
  set c_low : ℝ := c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hc_low_def
  set c_up : ℝ := M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) with hc_up_def
  have hδ_real : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hc_vol_pos : 0 < c_vol := by
    rw [hc_vol_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hM_vol_pos : 0 < M_vol := by
    rw [hM_vol_def]
    unfold Tube.volume_le.C
    positivity
  have hδ_pow_pos : 0 < (δ : ℝ) ^ (Module.finrank ℝ E - 1) := pow_pos hδ_real _
  have hc_low_pos : 0 < c_low := by
    rw [hc_low_def]
    exact mul_pos hc_vol_pos hδ_pow_pos
  have hc_up_pos : 0 < c_up := by
    rw [hc_up_def]
    exact mul_pos hM_vol_pos hδ_pow_pos
  have hlow_enn : ENNReal.ofReal c_low =
      (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
    rw [hc_low_def, hc_vol_def]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
      ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ))]
    rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (δ : ℝ))]
    simp
  have hup_enn : ENNReal.ofReal c_up =
      (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
    rw [hc_up_def, hM_vol_def]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
      ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))]
    rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (δ : ℝ))]
    simp
  have hsub' : ((T p₀.1).toTube.rigidMove (ω p₀.2).1 (ω p₀.2).2).carrier ⊆ K := by
    simpa [rigidProduct_apply] using hsub
  have hnotED' : ¬ IsEssentiallyDistinct
      ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2).carrier
      ((T p₀.1).toTube.rigidMove (ω p₀.2).1 (ω p₀.2).2).carrier := by
    simpa [rigidProduct_apply] using hnotED
  have hvol_low : ENNReal.ofReal c_low ≤
      volume ((T p₀.1).toTube.rigidMove (ω p₀.2).1 (ω p₀.2).2).carrier := by
    rw [Kakeya.volume_rigidMove_carrier]
    rw [hlow_enn]
    exact Tube.le_volume ((T p₀.1).toTube)
  have hvol_up :
      volume ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2).carrier ≤ ENNReal.ofReal c_up := by
    rw [Kakeya.volume_rigidMove_carrier]
    rw [hup_enn]
    exact Tube.volume_le hδ1 ((T p.1).toTube)
  have hbridge :=
    badAgainstSet_of_notED_subset_cthickening (δ := δ) hδ
      ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2)
      ((T p₀.1).toTube.rigidMove (ω p₀.2).1 (ω p₀.2).2)
      K c_low c_up hc_low_pos hc_up_pos hvol_low hvol_up hsub' hnotED'
  have hc_eq : c_low / (2 * c_up) = edBridgeConstant E := by
    rw [hc_low_def, hc_vol_def, hc_up_def, hM_vol_def]
    exact edBridgeConstant_eq_scaled hδ
  rw [hc_eq] at hbridge
  exact hbridge

/-- **Fibrewise decomposition of a filtered product `Finset`.** Pure combinatorics, used to turn the
non-ED set of the randomised family into a sum of per-copy bad counts. -/
theorem card_filter_product_eq_sum {ι : Type*} {J : ℕ} (s : Finset ι)
    (P : ι → Fin J → Prop) :
    (@Finset.filter (ι × Fin J) (fun p => P p.1 p.2) (Classical.decPred _)
        (s ×ˢ (Finset.univ : Finset (Fin J)))).card
      = ∑ j : Fin J, (@Finset.filter ι (fun i => P i j) (Classical.decPred _) s).card := by
  classical
  rw [Finset.card_filter]
  rw [Finset.sum_product]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm

/-- **Net-goodness implies essential distinctness up to multiplicity `M`.**

The deterministic bridge of GWZ Lemma 3.8 for rigid copies. The multiplicity is exactly the
net-goodness threshold: no dimensional constant is lost. -/
theorem isEDUpToMult_rigidProduct_of_net_good [Nontrivial E] (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hT_ball : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1)
    (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E)
    (hω : ∀ j, (ω j).2 ∈ closedBall (0 : E) 1)
    (NetT : Finset (Tube δ E))
    (happrox : ∀ T₀ : Tube δ E, T₀.carrier ⊆ closedBall (0 : E) 2 →
      ∃ T₀' ∈ NetT, T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
    (M : ℕ)
    (hgood : ∀ T₀ ∈ NetT,
      ∑ j : Fin J, edFailCountAt s (fun i => (T i).toTube) T₀ J j ω ≤ (M : ℝ)) :
    IsEDUpToMult (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p => (rigidProduct T J ω p).carrier) M := by
  classical
  intro p₀ hp₀
  -- 1. the fixed copy lies in `B(0,2)`; the net supplies `T₀'`.
  have hB2 : (rigidProduct T J ω p₀).carrier ⊆ closedBall (0 : E) 2 :=
    rigidProduct_carrier_subset_closedBall_two s T hT_ball J ω hω p₀ (Finset.mem_product.mp hp₀).1
  obtain ⟨T₀', hT₀'_mem, hT₀'_close⟩ := happrox (rigidProduct T J ω p₀).toTube (by simpa using hB2)
  set K : Set E := Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier
  -- 2. the non-ED set injects into the bad set.
  have hsubset :
      notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (rigidProduct T J ω p).carrier) ((rigidProduct T J ω p₀).carrier)
        ⊆ @Finset.filter (ι × Fin J)
            (fun p => BadAgainstSet ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2) K
              (edBridgeConstant E))
            (Classical.decPred _) (s ×ˢ (Finset.univ : Finset (Fin J))) := by
    intro p hp
    have hp' : p ∈ s ×ˢ (Finset.univ : Finset (Fin J)) ∧
        ¬ IsEssentiallyDistinct (rigidProduct T J ω p).carrier (rigidProduct T J ω p₀).carrier := by
      unfold notEssDistinctSet at hp
      simpa only [Finset.mem_filter] using hp
    obtain ⟨hp_mem, hp_notED⟩ := hp'
    have hsub' : (rigidProduct T J ω p₀).carrier ⊆ K := by
      simpa using hT₀'_close
    have hbad : BadAgainstSet ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2) K
        (edBridgeConstant E) :=
      badAgainstSet_of_notED_rigidProduct hδ hδ1 T J ω K p₀ p hsub' hp_notED
    rw [Finset.mem_filter]
    exact ⟨hp_mem, hbad⟩
  -- 3. count.
  calc
    (notEssDistinctSet (s ×ˢ (Finset.univ : Finset (Fin J)))
        (fun p => (rigidProduct T J ω p).carrier) ((rigidProduct T J ω p₀).carrier)).card
        ≤ (@Finset.filter (ι × Fin J)
            (fun p => BadAgainstSet ((T p.1).toTube.rigidMove (ω p.2).1 (ω p.2).2) K
              (edBridgeConstant E))
            (Classical.decPred _) (s ×ˢ (Finset.univ : Finset (Fin J)))).card :=
          Finset.card_le_card hsubset
    _ = ∑ j : Fin J, edFailCount s (fun i => (T i).toTube) T₀' (ω j) := by
      rw [card_filter_product_eq_sum
        (P := fun i j => BadAgainstSet ((T i).toTube.rigidMove (ω j).1 (ω j).2) K
          (edBridgeConstant E))]
      simp [K, edFailCount]
    _ ≤ M := by
      exact Nat.cast_le.mp (by
        rw [Nat.cast_sum (R := ℝ)]
        simpa [edFailCountAt] using hgood T₀' hT₀'_mem)

end

end Kakeya

end
