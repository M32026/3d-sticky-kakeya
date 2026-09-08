/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Mathlib.Analysis.EuclideanNet
public import Kakeya.Tube.EDPacking.PositionCount

/-!
# Counting pairwise-essentially-distinct δ-tubes inside an arbitrary set

`Kakeya.badAgainstSet_count_le_of_ED_thinBox` counts pairwise-ED δ-tubes overlapping a *thin box*
— the `99δ`-thickening of a δ-tube — where the direction of every bad tube is forced into a single
`O(δ)`-cap, so the direction factor collapses to `O(1)`. For an arbitrary target set `K` no such
collapse is available and a genuine direction count is needed.

This file supplies that count in the form the GWZ Appendix A cancellation actually consumes.
Writing `M := |K| / δ^(n-1)`, the bound proved here is

`#{i ∈ s | T i ⊆ K} ≤ C · M · δ^(-(n-1))`,

i.e. `#{i} ≲ |K| / δ^(2(n-1))`. Note this is *weaker* than GWZ's `(|K|/|T_δ|)² = M²`
whenever `|K| ≤ 1`, which is the only regime the application needs, and it suffices for

`Δ_max(𝕋) ≲ δ^(-(n-1))`

for every pairwise-ED family of δ-tubes. That maximal-density bound is the
ingredient behind the `J · 𝔼[X_j] ≲ 1` cancellation of GWZ Lemma 3.8, via
`C_F(𝕋) · Δ(𝕋, B₁) = Δ_max(𝕋)`.

## The two factors

Both already exist and are used as black boxes:

* **positions** — `Kakeya.position_count_le_of_bad_directionClass'` bounds the number of pairwise-ED
  tubes whose directions all lie in one `c_slide·δ`-cap and which each spend a `c`-fraction of their
  volume in `K`, by `C · M / c`. It takes an *arbitrary* compact measurable `K` with only the volume
  hypothesis, so nothing about it needs changing. Containment gives its overlap hypothesis with
  `c = 1`.
* **directions** — `Kakeya.EuclideanNet.exists_sphere_net` covers the unit sphere by
  `≲ (c_slide δ)^(-(n-1))` caps of radius `c_slide δ`. Every tube has a unit direction
  (`Tube.norm_direction`), so the family splits into that many direction classes.

The product of the two is the stated bound. No sharpness is attempted in either factor.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **Direction × position count for pairwise-ED δ-tubes contained in an arbitrary set.**
With `M` normalising the volume of `K` as `|K| ≤ M · δ^(n-1)`, a pairwise essentially distinct
family of δ-tubes all contained in `K` has at most `C · M · δ^(-(n-1))` members. -/
theorem card_le_of_ED_subset [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ℝ) (δ₀ : ℝ), 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {K : Set E} (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        {M : ℝ} (_hM_pos : 0 < M)
        (_hK_vol : volume K ≤ ENNReal.ofReal M *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        (_hsub : ∀ i ∈ s, (T i).carrier ⊆ K),
        (s.card : ℝ) ≤ C * M * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1)) := by
  classical
  obtain ⟨c_slide, C_pc, δ₀_pc, hc_slide, hC_pc, hδ₀_pc, hδ₀_pc1, hPC⟩ :=
    position_count_le_of_bad_directionClass' (E := E) hn
  set n : ℕ := Module.finrank ℝ E with hn_def
  set p : ℝ := -((n : ℝ) - 1) with hp_def
  set δ₀ : ℝ := min δ₀_pc (min 1 (1 / c_slide)) with hδ₀_def
  set C : ℝ := EuclideanNet.sphereNetConstant E * c_slide ^ p * (C_pc : ℝ) with hC_def
  have hC_pos : 0 < C := by
    rw [hC_def]
    have hsc : 0 < EuclideanNet.sphereNetConstant E := EuclideanNet.sphereNetConstant_pos (E := E)
    have hCp : 0 < (C_pc : ℝ) := by exact_mod_cast hC_pc
    positivity
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]
    have h1c : 0 < 1 / c_slide := by positivity
    exact lt_min hδ₀_pc (lt_min (by norm_num) h1c)
  have hδ₀_le : δ₀ ≤ 1 := by
    rw [hδ₀_def]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  refine ⟨C, δ₀, hC_pos, hδ₀_pos, hδ₀_le, ?_⟩
  intro δ hδ hδ_le ι s T hED K hK_meas hK_cpt M hM_pos hK_vol hsub
  have hδ_le_pc : (δ : ℝ) ≤ δ₀_pc := by
    rw [hδ₀_def] at hδ_le
    exact le_trans hδ_le (min_le_left _ _)
  set ε : ℝ := c_slide * (δ : ℝ) with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]
    positivity
  have hε_le1 : ε ≤ 1 := by
    rw [hε_def]
    have hδ_le_1c : (δ : ℝ) ≤ 1 / c_slide := by
      rw [hδ₀_def] at hδ_le
      exact le_trans hδ_le (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmsub : c_slide * (δ : ℝ) ≤ c_slide * (1 / c_slide) :=
      mul_le_mul_of_nonneg_left hδ_le_1c hc_slide.le
    calc
      c_slide * (δ : ℝ) ≤ c_slide * (1 / c_slide) := hmsub
      _ = 1 := by field_simp [hc_slide.ne']
  obtain ⟨U, hU_unit, hU_card, hU_cover⟩ :=
    EuclideanNet.exists_sphere_net (E := E) hε_pos hε_le1
  have hU_card_p : (U.card : ℝ) ≤ EuclideanNet.sphereNetConstant E * ε ^ p := by
    change (U.card : ℝ) ≤ EuclideanNet.sphereNetConstant E *
      ε ^ (-((Module.finrank ℝ E : ℝ) - 1))
    exact hU_card
  have hchoose : ∀ i : ι, ∃ u : E, u ∈ U ∧ ‖u - (T i).direction‖ ≤ ε := by
    intro i
    obtain ⟨u, hu, hle⟩ := hU_cover (T i).direction (Tube.norm_direction (T i))
    exact ⟨u, hu, hle⟩
  set f : ι → E := fun i => (hchoose i).choose with hf_def
  have hf_mem : ∀ i, f i ∈ U := fun i => (hchoose i).choose_spec.1
  have hf_close : ∀ i, ‖f i - (T i).direction‖ ≤ ε := fun i => (hchoose i).choose_spec.2
  have hcard : s.card = ∑ u ∈ U, (s.filter (fun i => f i = u)).card :=
    Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := U) (fun i _ => hf_mem i)
  have hfiber : ∀ u ∈ U, ((s.filter (fun i => f i = u)).card : ℝ) ≤ (C_pc : ℝ) * M := by
    intro u hu
    have hED' : ((s.filter (fun i => f i = u) : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
      exact hED.mono (Finset.coe_subset.mpr (Finset.filter_subset (s := s) (fun i => f i = u)))
    have he_unit : ‖u‖ = 1 := hU_unit u hu
    have h_dir_class : ∀ i ∈ (s.filter (fun i => f i = u)),
        min ‖(T i).direction - u‖ ‖(T i).direction + u‖ ≤ c_slide * (δ : ℝ) := by
      intro i hi
      have hfiu : f i = u := (Finset.mem_filter.mp hi).2
      have hclose : ‖u - (T i).direction‖ ≤ c_slide * (δ : ℝ) := by
        simpa [hfiu, hε_def] using hf_close i
      calc
        min ‖(T i).direction - u‖ ‖(T i).direction + u‖ ≤ ‖(T i).direction - u‖ :=
          min_le_left _ _
        _ = ‖u - (T i).direction‖ := norm_sub_rev (T i).direction u
        _ ≤ c_slide * (δ : ℝ) := hclose
    have hbad : ∀ i ∈ (s.filter (fun i => f i = u)),
        ENNReal.ofReal (1 : ℝ) * volume (T i).carrier ≤ volume ((T i).carrier ∩ K) := by
      intro i hi
      have hiu : i ∈ s := (Finset.mem_filter.mp hi).1
      have hsubi : (T i).carrier ⊆ K := hsub i hiu
      have hinter : (T i).carrier ∩ K = (T i).carrier := Set.inter_eq_self_of_subset_left hsubi
      simp [hinter]
    have result := hPC hδ hδ_le_pc (s.filter (fun i => f i = u)) T hED' he_unit h_dir_class
        hK_meas hK_cpt hM_pos hK_vol (c := (1 : ℝ)) (by norm_num : (0 : ℝ) < 1) hbad
    simpa using result
  have hcard_real : (s.card : ℝ) = ∑ u ∈ U, ((s.filter (fun i => f i = u)).card : ℝ) := by
    exact_mod_cast hcard
  have hsum_le :
      (∑ u ∈ U, ((s.filter (fun i => f i = u)).card : ℝ)) ≤ ∑ u ∈ U, ((C_pc : ℝ) * M) := by
    exact Finset.sum_le_sum (fun u hu => hfiber u hu)
  have hsum_eq : (∑ u ∈ U, (C_pc : ℝ) * M) = (U.card : ℝ) * ((C_pc : ℝ) * M) := by
    rw [Finset.sum_const]
    exact nsmul_eq_mul _ _
  have hU_card_step : (U.card : ℝ) * ((C_pc : ℝ) * M) ≤
      (EuclideanNet.sphereNetConstant E * ε ^ p) * ((C_pc : ℝ) * M) := by
    have hnz : 0 ≤ (C_pc : ℝ) * M := le_of_lt (mul_pos (by exact_mod_cast hC_pc) hM_pos)
    exact mul_le_mul_of_nonneg_right hU_card_p hnz
  calc
    (s.card : ℝ) = (∑ u ∈ U, ((s.filter (fun i => f i = u)).card : ℝ)) := hcard_real
    _ ≤ ∑ u ∈ U, ((C_pc : ℝ) * M) := hsum_le
    _ = (U.card : ℝ) * ((C_pc : ℝ) * M) := hsum_eq
    _ ≤ (EuclideanNet.sphereNetConstant E * ε ^ p) * ((C_pc : ℝ) * M) := hU_card_step
    _ = (EuclideanNet.sphereNetConstant E * (c_slide ^ p * (δ : ℝ) ^ p)) *
        ((C_pc : ℝ) * M) := by
      have hepow : ε ^ p = c_slide ^ p * (δ : ℝ) ^ p := by
        rw [hε_def]
        exact Real.mul_rpow hc_slide.le (show 0 ≤ (δ : ℝ) by positivity)
      rw [hepow]
    _ = C * M * (δ : ℝ) ^ p := by
      rw [hC_def]
      ring

/-- **Maximal density of a pairwise-ED family of δ-tubes.**
`Δ_max(𝕋) ≤ C · δ^(-(n-1))`. This is the form the GWZ Lemma 3.8 cancellation consumes: combined
with the identity `C_F(𝕋) · Δ(𝕋, B₁) = Δ_max(𝕋)` it turns `J · 𝔼[X_j] ≲ Δ_max(𝕋) · |T_δ|` into
`O(1)`, with no dependence on `J` or on the Frostman constant.

The bound holds for *every* convex test body, including those of volume `0` (where the density
degenerates to `0`), which is why no nondegeneracy hypothesis appears. -/
theorem maxDensity_le_of_ED [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ (C : ℝ) (δ₀ : ℝ), 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)),
        maxDensity s (fun i => (T i).toConvexSpaceBody)
          ≤ ENNReal.ofReal (C * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1))) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  let M_vol : ℝ := (Tube.volume_le.C n : ℝ)
  obtain ⟨C₁, δ₀, hC₁, hδ₀, hδ₀₁, hCard⟩ := card_le_of_ED_subset (E := E) hn
  refine ⟨C₁ * M_vol, δ₀, ?_, hδ₀, hδ₀₁, ?_⟩
  · have hMvol_pos : 0 < M_vol := by
      exact_mod_cast Tube.volume_le.C_pos n
    exact mul_pos hC₁ hMvol_pos
  · intro δ hδ hδ_le ι s T hED
    let W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
    rw [Kakeya.maxDensity_le_iff]
    intro K
    let sK : Finset ι := s.filter (fun i => W i ≤ K)
    let B0 : ENNReal := (Tube.volume_le.C n : ENNReal)
    let R : ENNReal := ENNReal.ofReal (C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)))
    by_cases hKvol0 : volume K.carrier = 0
    · have hdens : densityIn s W K = 0 := Kakeya.densityIn_eq_zero_of_volume_eq_zero hKvol0
      rw [hdens]
      exact zero_le
    · have hKvol_ne0 : volume K.carrier ≠ 0 := hKvol0
      have hKcpt_top : volume K.carrier ≠ ⊤ := K.isCompact.measure_lt_top.ne
      have hvol_posR : 0 < (volume K.carrier).toReal := ENNReal.toReal_pos hKvol_ne0 hKcpt_top
      have hδ_posR : 0 < (δ : ℝ) := by exact_mod_cast hδ
      set M : ℝ := (volume K.carrier).toReal / (δ : ℝ) ^ (n - 1) with hMdef
      have hM_pos : 0 < M := by
        rw [hMdef]
        exact div_pos hvol_posR (pow_pos hδ_posR _)
      have hpowδ : (δ : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hδ_posR.ne'
      have hprod : M * (δ : ℝ) ^ (n - 1) = (volume K.carrier).toReal := by
        rw [hMdef]
        field_simp [hpowδ]
      have hMvol_nonneg : 0 ≤ M_vol := NNReal.coe_nonneg _
      have hδ_ofReal : ENNReal.ofReal (δ : ℝ) = (δ : ENNReal) :=
        ENNReal.ofReal_eq_coe_nnreal δ.prop
      have hde : (δ : ENNReal) ^ (n - 1) = ENNReal.ofReal ((δ : ℝ) ^ (n - 1 : ℕ)) := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg δ)]
        rw [hδ_ofReal]
      have hvol_eq : ENNReal.ofReal M * (δ : ENNReal) ^ (n - 1) = volume K.carrier := by
        rw [hde]
        rw [← ENNReal.ofReal_mul (le_of_lt hM_pos)]
        rw [hprod]
        exact ENNReal.ofReal_toReal hKcpt_top
      have hK_meas : MeasurableSet K.carrier := K.isCompact.measurableSet
      have hK_cpt : IsCompact K.carrier := K.isCompact
      have hK_vol' : volume K.carrier ≤ ENNReal.ofReal M * (δ : ENNReal) ^ (n - 1) :=
        le_of_eq hvol_eq.symm
      have hED' : (sK : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
        exact hED.mono (Finset.coe_subset.mpr (Finset.filter_subset (s := s) (fun i => W i ≤ K)))
      have hsub : ∀ i ∈ sK, (T i).carrier ⊆ K.carrier := by
        intro i hi
        change (W i).carrier ⊆ K.carrier
        exact SetLike.coe_subset_coe.mpr ((Finset.mem_filter.mp hi).2)
      have hcardR : (sK.card : ℝ) ≤ C₁ * M * (δ : ℝ) ^ (-((n : ℝ) - 1)) := by
        exact hCard hδ hδ_le sK T hED' (K := K.carrier) hK_meas hK_cpt (M := M) hM_pos hK_vol' hsub
      have hnonneg : 0 ≤ M_vol * (δ : ℝ) ^ (n - 1) :=
        mul_nonneg hMvol_nonneg (pow_nonneg (show 0 ≤ (δ : ℝ) from NNReal.coe_nonneg _) _)
      have hreal_le : (sK.card : ℝ) * M_vol * (δ : ℝ) ^ (n - 1) ≤
          C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)) * (volume K.carrier).toReal := by
        calc
          (sK.card : ℝ) * M_vol * (δ : ℝ) ^ (n - 1)
              = (sK.card : ℝ) * (M_vol * (δ : ℝ) ^ (n - 1)) := by ring
          _ ≤ C₁ * M * (δ : ℝ) ^ (-((n : ℝ) - 1)) * (M_vol * (δ : ℝ) ^ (n - 1)) := by
            exact mul_le_mul_of_nonneg_right hcardR hnonneg
          _ = C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)) * (M * (δ : ℝ) ^ (n - 1)) := by ring
          _ = C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)) * (volume K.carrier).toReal := by rw [hprod]
      have hC1_nonneg : 0 ≤ C₁ := hC₁.le
      have hX_nonneg : 0 ≤ C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)) :=
        mul_nonneg (mul_nonneg hC1_nonneg hMvol_nonneg)
          (Real.rpow_nonneg (NNReal.coe_nonneg δ) (-((n : ℝ) - 1)))
      have hL : (sK.card : ENNReal) * B0 * (δ : ENNReal) ^ (n - 1) =
          ENNReal.ofReal ((sK.card : ℝ) * M_vol * (δ : ℝ) ^ (n - 1 : ℕ)) := by
        have hB0 : B0 = ENNReal.ofReal M_vol := by
          change (Tube.volume_le.C n : ENNReal) = ENNReal.ofReal (Tube.volume_le.C n : ℝ)
          exact (ENNReal.ofReal_eq_coe_nnreal (NNReal.coe_nonneg (Tube.volume_le.C n))).symm
        have hcard_ofReal : (sK.card : ENNReal) = ENNReal.ofReal (sK.card : ℝ) := by
          rw [ENNReal.ofReal_natCast]
        calc
          (sK.card : ENNReal) * B0 * (δ : ENNReal) ^ (n - 1)
              = ENNReal.ofReal (sK.card : ℝ) * ENNReal.ofReal M_vol *
                  ENNReal.ofReal ((δ : ℝ) ^ (n - 1 : ℕ)) := by
                rw [hcard_ofReal, hB0, hde]
          _ = ENNReal.ofReal ((sK.card : ℝ) * M_vol * (δ : ℝ) ^ (n - 1 : ℕ)) := by
                have hc0 : 0 ≤ (sK.card : ℝ) := Nat.cast_nonneg _
                rw [← ENNReal.ofReal_mul hc0]
                rw [← ENNReal.ofReal_mul (mul_nonneg hc0 hMvol_nonneg)]
      have hR : ENNReal.ofReal (C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)) *
          (volume K.carrier).toReal) = R * volume K.carrier := by
        calc
          ENNReal.ofReal (C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1)) * (volume K.carrier).toReal)
              = ENNReal.ofReal (C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1))) *
                  ENNReal.ofReal (volume K.carrier).toReal := by
                  rw [ENNReal.ofReal_mul hX_nonneg]
          _ = ENNReal.ofReal (C₁ * M_vol * (δ : ℝ) ^ (-((n : ℝ) - 1))) * volume K.carrier := by
                  conv_lhs =>
                    rw [ENNReal.ofReal_toReal hKcpt_top]
          _ = R * volume K.carrier := by rfl
      have hcardEN : (sK.card : ENNReal) * B0 * (δ : ENNReal) ^ (n - 1) ≤ R * volume K.carrier := by
        rw [hL, ← hR]
        exact ENNReal.ofReal_le_ofReal hreal_le
      have hvol_le : ∀ i ∈ sK, volume (W i).carrier ≤ B0 * (δ : ENNReal) ^ (n - 1) := by
        intro i hi
        have hδle1 : (δ : NNReal) ≤ 1 := by
          exact_mod_cast (le_trans hδ_le hδ₀₁ : (δ : ℝ) ≤ 1)
        exact Tube.volume_le hδle1 (T i)
      have hsum_le : (∑ i ∈ sK, volume (W i).carrier) ≤
          (sK.card : ENNReal) * B0 * (δ : ENNReal) ^ (n - 1) := by
        have hs := Finset.sum_le_card_nsmul sK (fun i => volume (W i).carrier)
          (B0 * (δ : ENNReal) ^ (n - 1)) hvol_le
        simpa [nsmul_eq_mul, mul_assoc] using hs
      rw [Kakeya.densityIn_le_iff s W K R]
      exact hsum_le.trans hcardEN

end

end Kakeya

end
