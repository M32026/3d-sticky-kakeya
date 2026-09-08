/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.ConvexBody

/-!
# The deterministic Frostman packing count

`ConvexSpaceBody.IsFrostmanIn.card_le_of_subset` is the deterministic core of the GWZ §9
packing inequality: if the family `𝕎 = (W i)_{i ∈ s}` sits inside the unit ball, has comparable
member volumes `c·δ^(n-1) ≤ |W i| ≤ M·δ^(n-1)`, and is `C_F`-convex-Frostman in the
unit ball, then for
*every* convex test body `K`

`#{i ∈ s | W i ⊆ K} · (c · |B₁|) ≤ C_F · M · |s| · |K|`.

No hypothesis relates `K` to the unit ball, and no randomness is involved. The proof intersects `K`
with `B₁` (which changes neither side of the count, since every `W i` already lies in `B₁`), applies
the Frostman hypothesis to the intersection, and converts densities to cardinalities using the two
volume bounds.

This was previously inlined inside `Kakeya.HasUniformTranslation.tubeContainedCount_le_ED_packing`,
where the test body arose as a *translate* `K - v`. The rigid-motion argument needs it for a
*rotated* test body instead, so the geometry-free statement is factored out here.
-/

@[expose] public section

open MeasureTheory Metric Set Kakeya

namespace ConvexSpaceBody.IsFrostmanIn

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The deterministic Frostman packing count.** For a `C_F`-convex-Frostman family of comparable
convex bodies inside the unit ball, the number of members contained in an arbitrary convex test body
`K` is `≲ C_F · |s| · |K|`. -/
theorem card_le_of_subset [Nontrivial E]
    {δ : NNReal} (hδ_pos : (0 : ℝ) < (δ : ℝ))
    {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (CF : ℝ) (hCF_nn : 0 ≤ CF)
    (hFrost : ConvexSpaceBody.IsFrostmanIn s W ConvexSpaceBody.closedUnitBall
      (ENNReal.ofReal CF))
    (hW_in_B1 : ∀ i ∈ s, W i ≤ ConvexSpaceBody.closedUnitBall)
    (c_vol M_vol : ℝ) (_hc_vol_pos : 0 < c_vol) (hM_vol_nn : 0 ≤ M_vol)
    (hW_vol_lb :
      ∀ i ∈ s, c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real (W i).carrier)
    (hW_vol_ub :
      ∀ i ∈ s, volume.real (W i).carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1))
    (K : ConvexSpaceBody E) :
    (((@Finset.filter ι (fun i => W i ≤ K) (Classical.decPred _) s).card : ℝ)) *
        (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
      CF * M_vol * (s.card : ℝ) * volume.real K.carrier := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set k : ℕ := n - 1 with hk_def
  have hδk_pos : 0 < (δ : ℝ) ^ k := pow_pos hδ_pos k
  have hvolB_pos : 0 < volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
    have hpos : (0 : ENNReal) < volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
      ConvexSpaceBody.closedUnitBall_volume_pos
    have hne_top : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ ⊤ :=
      (ConvexSpaceBody.closedUnitBall (E := E)).isCompact'.measure_lt_top.ne
    exact ENNReal.toReal_pos hpos.ne' hne_top
  by_cases hempty : ∀ i ∈ s, ¬ W i ≤ K
  · have hfilter : s.filter (fun i => W i ≤ K) = ∅ :=
      Finset.filter_false_of_mem hempty
    rw [hfilter]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    have hCFM_nn : 0 ≤ CF * M_vol := mul_nonneg hCF_nn hM_vol_nn
    have hCFMs_nn : 0 ≤ CF * M_vol * (s.card : ℝ) :=
      mul_nonneg hCFM_nn (Nat.cast_nonneg _)
    exact mul_nonneg hCFMs_nn MeasureTheory.measureReal_nonneg
  · push Not at hempty
    obtain ⟨i₀, hi₀_mem, hi₀_le⟩ := hempty
    have hWi₀_in_B1 : W i₀ ≤ ConvexSpaceBody.closedUnitBall := hW_in_B1 i₀ hi₀_mem
    have hWi₀_sub_inter :
        (W i₀).carrier ⊆
          K.carrier ∩ (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
      intro x hx
      exact ⟨hi₀_le hx, hWi₀_in_B1 hx⟩
    set K_inter : ConvexSpaceBody E :=
      { carrier := K.carrier ∩ (ConvexSpaceBody.closedUnitBall (E := E)).carrier
        convex' :=
          K.convex'.inter (ConvexSpaceBody.closedUnitBall (E := E)).convex'
        isCompact' :=
          IsCompact.inter K.isCompact'
            (ConvexSpaceBody.closedUnitBall (E := E)).isCompact'
        nonempty' := (W i₀).nonempty'.mono hWi₀_sub_inter }
    have hK_inter_le_cUB : K_inter ≤ ConvexSpaceBody.closedUnitBall := fun x hx => hx.2
    have hK_inter_le_K : K_inter.carrier ⊆ K.carrier := fun _ hx => hx.1
    have h_filter_inter :
        s.filter (fun i => W i ≤ K) = s.filter (fun i => W i ≤ K_inter) := by
      apply Finset.filter_congr
      intro i hi
      refine ⟨fun hi_le => ?_, fun hi_le => ?_⟩
      · intro x hx
        exact ⟨hi_le hx, hW_in_B1 i hi hx⟩
      · intro x hx
        exact (hi_le hx).1
    have h_phase1 :
        ((s.filter (fun i => W i ≤ K_inter)).card : ℝ) *
            (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) ≤
          CF * M_vol * (s.card : ℝ) * volume.real K_inter.carrier := by
      have hvolK_inter_nn : 0 ≤ volume.real K_inter.carrier :=
        MeasureTheory.measureReal_nonneg
      have hkey :
          ((s.filter (fun i => W i ≤ K_inter)).card : ℝ) *
              (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) *
                (δ : ℝ) ^ k ≤
            CF * M_vol * (s.card : ℝ) * volume.real K_inter.carrier *
              (δ : ℝ) ^ k := by
        set S : Finset ι := s.filter (fun i => W i ≤ K_inter) with hS_def
        have hStepA :
            (S.card : ℝ) * (c_vol * (δ : ℝ) ^ k) ≤
              ∑ i ∈ S, volume.real (W i).carrier := by
          calc (S.card : ℝ) * (c_vol * (δ : ℝ) ^ k)
              = ∑ _ ∈ S, c_vol * (δ : ℝ) ^ k := by
                  rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ i ∈ S, volume.real (W i).carrier := by
                  apply Finset.sum_le_sum
                  intro i hi
                  exact hW_vol_lb i (Finset.mem_filter.mp hi).1
        have hSumE :
            (∑ i ∈ s with W i ≤ K_inter, volume (W i).carrier) =
              densityIn s W K_inter * volume K_inter.carrier :=
          Kakeya.sum_volume_eq_densityIn_mul_volume s W K_inter
        have hfilterSum :
            (∑ i ∈ S, volume.real (W i).carrier) =
              (∑ i ∈ s with W i ≤ K_inter, volume (W i).carrier).toReal := by
          simp only [hS_def, MeasureTheory.measureReal_def]
          rw [ENNReal.toReal_sum]
          intro i _
          exact (W i).isCompact'.measure_lt_top.ne
        have hStepB :
            ∑ i ∈ S, volume.real (W i).carrier =
              (densityIn s W K_inter).toReal * volume.real K_inter.carrier := by
          rw [hfilterSum, hSumE, ENNReal.toReal_mul]
          rfl
        have hStepC_ennreal :
            densityIn s W K_inter ≤
              ENNReal.ofReal CF * densityIn s W (ConvexSpaceBody.closedUnitBall (E := E)) :=
          hFrost K_inter hK_inter_le_cUB
        have hdensity_B_ne_top : densityIn s W (ConvexSpaceBody.closedUnitBall (E := E)) ≠ ⊤ :=
          densityIn_ne_top s W (ConvexSpaceBody.closedUnitBall (E := E))
        have hCF_ne_top : ENNReal.ofReal CF ≠ ⊤ := ENNReal.ofReal_ne_top
        have hStepC :
            (densityIn s W K_inter).toReal ≤
              CF * (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal := by
          have h1 := ENNReal.toReal_mono
            (ENNReal.mul_ne_top hCF_ne_top hdensity_B_ne_top) hStepC_ennreal
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCF_nn] at h1
          exact h1
        have hStepD :
            (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≤
              (s.card : ℝ) * (M_vol * (δ : ℝ) ^ k) := by
          have hSumE_B :
              (∑ i ∈ s, volume (W i).carrier) =
                densityIn s W (ConvexSpaceBody.closedUnitBall (E := E)) *
                  volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
            have h := Kakeya.sum_volume_eq_densityIn_mul_volume
              s W (ConvexSpaceBody.closedUnitBall (E := E))
            rwa [Finset.filter_true_of_mem (fun i hi => hW_in_B1 i hi)] at h
          have hfilterSum_B :
              (∑ i ∈ s, volume.real (W i).carrier) =
                (∑ i ∈ s, volume (W i).carrier).toReal := by
            simp only [MeasureTheory.measureReal_def]
            rw [ENNReal.toReal_sum]
            intro i _
            exact (W i).isCompact'.measure_lt_top.ne
          have hvolB_ne_top : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ ⊤ :=
            (ConvexSpaceBody.closedUnitBall (E := E)).isCompact'.measure_lt_top.ne
          have hsum_eq :
              ∑ i ∈ s, volume.real (W i).carrier =
                (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal *
                  volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
            rw [hfilterSum_B, hSumE_B, ENNReal.toReal_mul]
            rfl
          rw [← hsum_eq]
          calc (∑ i ∈ s, volume.real (W i).carrier)
              ≤ ∑ _ ∈ s, M_vol * (δ : ℝ) ^ k := by
                  apply Finset.sum_le_sum
                  intro i hi
                  exact hW_vol_ub i hi
            _ = (s.card : ℝ) * (M_vol * (δ : ℝ) ^ k) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
        have hCFvolK_inter_nn : 0 ≤ CF * volume.real K_inter.carrier :=
          mul_nonneg hCF_nn hvolK_inter_nn
        have hdensB_nn :
            0 ≤ (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal :=
          ENNReal.toReal_nonneg
        calc ((S.card : ℝ) *
                (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier))
              * (δ : ℝ) ^ k
            = ((S.card : ℝ) * (c_vol * (δ : ℝ) ^ k)) *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by ring
          _ ≤ (∑ i ∈ S, volume.real (W i).carrier) *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier :=
                mul_le_mul_of_nonneg_right hStepA hvolB_pos.le
          _ = ((densityIn s W K_inter).toReal * volume.real K_inter.carrier) *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
                rw [hStepB]
          _ ≤ (CF * (densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal *
                  volume.real K_inter.carrier) *
                volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier := by
                apply mul_le_mul_of_nonneg_right _ hvolB_pos.le
                exact mul_le_mul_of_nonneg_right hStepC hvolK_inter_nn
          _ = (CF * volume.real K_inter.carrier) *
                ((densityIn s W (ConvexSpaceBody.closedUnitBall (E := E))).toReal *
                  volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) := by ring
          _ ≤ (CF * volume.real K_inter.carrier) *
                ((s.card : ℝ) * (M_vol * (δ : ℝ) ^ k)) :=
                mul_le_mul_of_nonneg_left hStepD hCFvolK_inter_nn
          _ = CF * M_vol * (s.card : ℝ) * volume.real K_inter.carrier *
                (δ : ℝ) ^ k := by ring
      exact le_of_mul_le_mul_right hkey hδk_pos
    have hvol_inter_le : volume.real K_inter.carrier ≤ volume.real K.carrier :=
      MeasureTheory.measureReal_mono hK_inter_le_K K.isCompact'.measure_lt_top.ne
    have h_RHS_le :
        CF * M_vol * (s.card : ℝ) * volume.real K_inter.carrier ≤
          CF * M_vol * (s.card : ℝ) * volume.real K.carrier := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (mul_nonneg hCF_nn hM_vol_nn) (Nat.cast_nonneg _))
      exact hvol_inter_le
    calc ((s.filter (fun i => W i ≤ K)).card : ℝ) *
            (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier)
        = ((s.filter (fun i => W i ≤ K_inter)).card : ℝ) *
            (c_vol * volume.real (ConvexSpaceBody.closedUnitBall (E := E)).carrier) := by
            rw [h_filter_inter]
      _ ≤ CF * M_vol * (s.card : ℝ) * volume.real K_inter.carrier := h_phase1
      _ ≤ CF * M_vol * (s.card : ℝ) * volume.real K.carrier := h_RHS_le

end

end ConvexSpaceBody.IsFrostmanIn

end
