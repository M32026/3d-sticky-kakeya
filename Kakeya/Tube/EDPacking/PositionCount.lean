/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.EDPacking.PerpSeparation

/-!
# Position count: `#{bad tubes in a direction class} ≤ C₂ · M / c`

Volume double-counting argument for the position-count bound of bad tubes
within a direction class.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped InnerProductSpace RealInnerProductSpace

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-! ### Position count: `#{bad tubes in a direction class} ≤ C₂ · M / c`

Position-count half of the convex-projection-Fubini double-counting
argument in `badAgainstSet_count_le_of_ED_thinBox`
(`Kakeya/Tube/EDPacking/BadAgainstSet.lean`).

**Geometric content.** Fix a direction class (tubes whose directions
all lie inside a common `c_slide·δ`-cap). For pairwise-ED δ-tubes
`T₁, …, T_N` in this class, all bad against `K` with density `c`
(i.e. `vol(Tᵢ ∩ K) ≥ c · vol(Tᵢ)`) and with the thin-box volume bound
`vol(K) ≤ M · δ^(n-1)`, we have `N ≤ C₂ · M / c`.

**Proof outline (volume double counting).**
```
∑ᵢ vol(Tᵢ ∩ K) = ∫_K #{i : p ∈ Tᵢ} dp        (Fubini / indicator sum)
              ≤ multiplicity · vol(K)         (`multiplicity_le_of_ED_directionClass`)
              ≤ C_n · M · δ^(n-1).
```
Each `vol(Tᵢ ∩ K) ≥ c · vol(Tᵢ) = c · C_vol · δ^(n-1)` (tube volume
lower bound). Combining,
```
N · c · C_vol · δ^(n-1) ≤ C_n · M · δ^(n-1)   ⟹   N ≤ (C_n/C_vol) · M / c.
```

Combined with the direction count `N_dir ≤ C₁ · M / c` of
`bad_axial_angle_le`, this gives the total bound
`Bad.card ≤ N_dir · |Bad_e| ≤ C₁C₂ · M²/c²` used to close
`badAgainstSet_count_le_of_ED_thinBox`. -/

/-- **Volume sum equals integral of multiplicity (single direction class).**

`∑_i vol(Tᵢ ∩ K) = ∫_K (#{i : p ∈ Tᵢ.carrier}) dp` (Fubini / Tonelli
on the indicator-sum representation). -/
lemma sum_vol_inter_eq_integral_multiplicity
    {δ : NNReal} (_hδ : 0 < δ)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    {K : Set E} (_hK_meas : MeasurableSet K) :
    ∑ i ∈ s, volume ((T i).carrier ∩ K)
      = ∫⁻ p in K,
          ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
              (Classical.decPred _) s).card : ENNReal) := by
  classical
  have hinter_meas : ∀ i ∈ s, MeasurableSet ((T i).carrier ∩ K) :=
    fun i _ => (T i).isCompact.measurableSet.inter _hK_meas
  have hind_meas : ∀ i ∈ s,
      Measurable (((T i).carrier ∩ K).indicator (1 : E → ENNReal)) :=
    fun i hi => measurable_const.indicator (hinter_meas i hi)
  calc
    ∑ i ∈ s, volume ((T i).carrier ∩ K)
        = ∑ i ∈ s, ∫⁻ p,
            ((T i).carrier ∩ K).indicator (1 : E → ENNReal) p := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [lintegral_indicator_one (hinter_meas i hi)]
      _ = ∫⁻ p, ∑ i ∈ s,
            ((T i).carrier ∩ K).indicator (1 : E → ENNReal) p := by
          rw [lintegral_finsetSum s hind_meas]
      _ = ∫⁻ p in K,
            ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
                (Classical.decPred _) s).card : ENNReal) := by
          rw [← lintegral_indicator _hK_meas]
          refine lintegral_congr (fun p => ?_)
          by_cases hpK : p ∈ K
          · simp only [Set.indicator_of_mem hpK]
            rw [Finset.natCast_card_filter]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            by_cases hp : p ∈ (T i).carrier <;> simp [Set.indicator, hp, hpK]
          · simp [Set.indicator, hpK]

/-- **Position count: bad ED δ-tubes in a single direction class.**

For pairwise-ED δ-tubes whose directions lie in a `c_slide·δ`-cap
around `e`, all bad against `K` with density `c` and with
`vol(K) ≤ M · δ^(n-1)`, the count is `≤ C₂ · M / c`. -/
lemma position_count_le_of_bad_directionClass
    (_hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide : ℝ) (C : ℕ) (δ₀ : ℝ),
      0 < c_slide ∧ 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_dir_class : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * (δ : ℝ))
        {K : Set E}
        (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        {M : ℝ} (_hM_pos : 0 < M)
        (_hK_vol : volume K ≤ ENNReal.ofReal M *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        {c : ℝ} (_hc : 0 < c)
        (_hbad : ∀ i ∈ s,
            ENNReal.ofReal c * volume (T i).carrier ≤ volume ((T i).carrier ∩ K)),
        (s.card : ℝ) ≤ (C : ℝ) * M / c := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := by have := _hn; omega
  obtain ⟨c_slide, C_mult, δ₀, hc_slide_pos, hC_mult_pos, hδ₀_pos, hδ₀_le, hC_mult_bound⟩ :=
    multiplicity_le_of_ED_directionClass (E := E) _hn
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  set C_tube : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hC_tube_def
  have hC_tube_pos : 0 < C_tube := by
    rw [hC_tube_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hC_tube : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      C_tube * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ _ T
    have h := Tube.le_volume (δ := δ) T
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
    exact hreal
  refine ⟨c_slide, ⌈(C_mult : ℝ) / C_tube⌉₊ + 1, δ₀, hc_slide_pos, by omega,
    hδ₀_pos, hδ₀_le, ?_⟩
  intro δ hδ hδ_le ι s T hED e he_unit h_dir_class K hK_meas hK_cpt M hM_pos
    hK_vol_enn c hc hbad_enn
  have hK_vol : volume.real K ≤ M * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)) hK_vol_enn
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hM_pos.le, ENNReal.coe_toReal] using hreal
  have hbad : ∀ i ∈ s,
      c * volume.real (T i).carrier ≤ volume.real ((T i).carrier ∩ K) := by
    intro i hi
    have hinter_fin : volume ((T i).carrier ∩ K) ≠ ⊤ :=
      ne_top_of_le_ne_top (T i).isCompact.measure_lt_top.ne
        (measure_mono Set.inter_subset_left)
    have hreal := ENNReal.toReal_mono hinter_fin (hbad_enn i hi)
    simpa [Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hc.le] using hreal
  set N := s.card with hN_def
  have h_mult : ∀ p : E,
      ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
          (Classical.decPred _) s).card : ℝ) ≤ (C_mult : ℝ) := by
    intro p
    exact_mod_cast hC_mult_bound hδ hδ_le s T hED he_unit h_dir_class p
  have h_sum_eq :
      ∑ i ∈ s, volume.real ((T i).carrier ∩ K)
        = ∫ p in K,
            ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
                (Classical.decPred _) s).card : ℝ) := by
    have hT_meas : ∀ i, MeasurableSet ((T i).carrier) :=
      fun i => (T i).isCompact.measurableSet
    have h_integrand : ∀ p,
        ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
            (Classical.decPred _) s).card : ℝ) =
          ∑ i ∈ s, ((T i).carrier).indicator (fun _ => (1 : ℝ)) p := by
      intro p
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hp : p ∈ (T i).carrier <;> simp [hp]
    have h_indicator_integrable : ∀ i ∈ s,
        Integrable (fun p => ((T i).carrier).indicator (fun _ => (1 : ℝ)) p)
          (volume.restrict K) := by
      intro i _
      have h_inter_fin : (volume.restrict K) ((T i).carrier) ≠ ⊤ := by
        rw [Measure.restrict_apply (hT_meas i)]
        exact ((measure_mono Set.inter_subset_left).trans_lt
          (T i).isCompact.measure_lt_top).ne
      exact (integrableOn_const h_inter_fin).integrable_indicator (hT_meas i)
    calc
      ∑ i ∈ s, volume.real ((T i).carrier ∩ K)
          = ∑ i ∈ s, ∫ p in K,
              ((T i).carrier).indicator (fun _ => (1 : ℝ)) p := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [setIntegral_indicator (hT_meas i), Set.inter_comm,
              integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
        _ = ∫ p in K, ∑ i ∈ s,
              ((T i).carrier).indicator (fun _ => (1 : ℝ)) p := by
            rw [integral_finsetSum s h_indicator_integrable]
        _ = ∫ p in K,
              ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
                  (Classical.decPred _) s).card : ℝ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
            exact (h_integrand p).symm
  have hK_finmeas : volume K ≠ ⊤ := hK_cpt.measure_lt_top.ne
  have h_meas_fun : Measurable
      (fun p : E => ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
          (Classical.decPred _) s).card : ℝ)) := by
    have heq : (fun p : E => ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
          (Classical.decPred _) s).card : ℝ))
        = (fun p => ∑ i ∈ s, ((T i).carrier).indicator (fun _ => (1 : ℝ)) p) := by
      funext p
      rw [Finset.natCast_card_filter]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hp : p ∈ (T i).carrier
      · simp [hp]
      · simp [hp]
    rw [heq]
    refine Finset.measurable_sum s (fun i _ => ?_)
    have hT_meas : MeasurableSet ((T i).carrier) :=
      (T i).isCompact.measurableSet
    exact (measurable_const.indicator hT_meas)
  have h_intble : IntegrableOn
      (fun p => ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
          (Classical.decPred _) s).card : ℝ)) K volume := by
    refine Measure.integrableOn_of_bounded (M := (C_mult : ℝ))
      hK_finmeas h_meas_fun.aestronglyMeasurable ?_
    · refine Filter.Eventually.of_forall (fun p => ?_)
      have := h_mult p
      have h_nn : (0 : ℝ) ≤ ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
          (Classical.decPred _) s).card : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact this
  have h_int_le :
      ∫ p in K,
          ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
              (Classical.decPred _) s).card : ℝ)
        ≤ (C_mult : ℝ) * volume.real K := by
    have h1 : ∫ p in K,
        ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
            (Classical.decPred _) s).card : ℝ)
        ≤ ∫ _ in K, (C_mult : ℝ) :=
      setIntegral_mono_on h_intble (integrableOn_const hK_finmeas)
        hK_meas (fun p _ => h_mult p)
    have h2 : ∫ _ in K, (C_mult : ℝ) = volume.real K * (C_mult : ℝ) := by
      rw [setIntegral_const, smul_eq_mul]
    rw [h2, mul_comm] at h1
    exact h1
  have h_step34 : ∑ i ∈ s, volume.real ((T i).carrier ∩ K)
      ≤ (C_mult : ℝ) * M * (δ : ℝ) ^ (n - 1) := by
    calc ∑ i ∈ s, volume.real ((T i).carrier ∩ K)
        = ∫ p in K, ((@Finset.filter ι (fun i => p ∈ (T i).carrier)
            (Classical.decPred _) s).card : ℝ) := h_sum_eq
      _ ≤ (C_mult : ℝ) * volume.real K := h_int_le
      _ ≤ (C_mult : ℝ) * (M * (δ : ℝ) ^ (n - 1)) := by
          have : 0 ≤ (C_mult : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hK_vol this
      _ = (C_mult : ℝ) * M * (δ : ℝ) ^ (n - 1) := by ring
  have hδ_real_pos : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδpow_pos : 0 < (δ : ℝ) ^ (n - 1) := pow_pos hδ_real_pos _
  have h_step5 :
      (N : ℝ) * c * (C_tube * (δ : ℝ) ^ (n - 1)) ≤ ∑ i ∈ s, c * volume.real (T i).carrier := by
    have h_each : ∀ i ∈ s, c * (C_tube * (δ : ℝ) ^ (n - 1)) ≤ c * volume.real (T i).carrier := by
      intro i _
      have := hC_tube δ hδ (T i)
      exact mul_le_mul_of_nonneg_left this hc.le
    calc (N : ℝ) * c * (C_tube * (δ : ℝ) ^ (n - 1))
        = ∑ i ∈ s, c * (C_tube * (δ : ℝ) ^ (n - 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
      _ ≤ ∑ i ∈ s, c * volume.real (T i).carrier := Finset.sum_le_sum h_each
  have h_bad_sum : ∑ i ∈ s, c * volume.real (T i).carrier
      ≤ ∑ i ∈ s, volume.real ((T i).carrier ∩ K) :=
    Finset.sum_le_sum hbad
  have h_main : (N : ℝ) * c * (C_tube * (δ : ℝ) ^ (n - 1)) ≤ (C_mult : ℝ) * M * (δ : ℝ) ^ (n - 1) :=
    le_trans h_step5 (le_trans h_bad_sum h_step34)
  have h_main' : (N : ℝ) * c * C_tube ≤ (C_mult : ℝ) * M := by
    have h_eq1 : (N : ℝ) * c * (C_tube * (δ : ℝ) ^ (n - 1))
        = (N : ℝ) * c * C_tube * (δ : ℝ) ^ (n - 1) := by ring
    rw [h_eq1] at h_main
    exact le_of_mul_le_mul_right (by linarith) hδpow_pos
  have h_main'' : (N : ℝ) * c ≤ ((C_mult : ℝ) / C_tube) * M := by
    have h_eq : ((C_mult : ℝ) / C_tube) * M * C_tube = (C_mult : ℝ) * M := by
      field_simp
    have h_step : (N : ℝ) * c * C_tube ≤ ((C_mult : ℝ) / C_tube) * M * C_tube := by
      rw [h_eq]; exact h_main'
    exact le_of_mul_le_mul_right h_step hC_tube_pos
  set C : ℕ := ⌈(C_mult : ℝ) / C_tube⌉₊ + 1 with hC_def
  have hC_ge : ((C_mult : ℝ) / C_tube) ≤ (C : ℝ) := by
    have h1 : (C_mult : ℝ) / C_tube ≤ ⌈(C_mult : ℝ) / C_tube⌉₊ := Nat.le_ceil _
    have : ((⌈(C_mult : ℝ) / C_tube⌉₊ : ℕ) : ℝ) ≤ (C : ℝ) := by
      rw [hC_def]
      push_cast
      linarith
    linarith
  have h_main''' : (N : ℝ) * c ≤ (C : ℝ) * M := by
    have hM_nn : 0 ≤ M := hM_pos.le
    have : ((C_mult : ℝ) / C_tube) * M ≤ (C : ℝ) * M :=
      mul_le_mul_of_nonneg_right hC_ge hM_nn
    linarith
  rw [le_div_iff₀ hc]
  linarith

/-- **Composite position count for bad-tubes in a direction class.**

Restatement of `position_count_le_of_bad_directionClass` using
`BadAgainstSet` directly (the predicate consumed by the body of
`badAgainstSet_count_le_of_ED_thinBox`). -/
lemma position_count_le_of_bad_directionClass'
    (hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide : ℝ) (C : ℕ) (δ₀ : ℝ),
      0 < c_slide ∧ 0 < C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_dir_class : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ c_slide * (δ : ℝ))
        {K : Set E}
        (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        {M : ℝ} (_hM_pos : 0 < M)
        (_hK_vol : volume K ≤ ENNReal.ofReal M *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        {c : ℝ} (_hc : 0 < c)
        (_hbad : ∀ i ∈ s,
            volume ((T i).carrier ∩ K) ≥ ENNReal.ofReal c * volume (T i).carrier),
        (s.card : ℝ) ≤ (C : ℝ) * M / c := by
  obtain ⟨c_slide, C, δ₀, hc_slide_pos, hC_pos, hδ₀_pos, hδ₀_le, hC_bound⟩ :=
    position_count_le_of_bad_directionClass (E := E) hn
  refine ⟨c_slide, C, δ₀, hc_slide_pos, hC_pos, hδ₀_pos, hδ₀_le, ?_⟩
  intro δ hδ hδ_le ι s T hED e he_unit h_dir_class K hK_meas hK_cpt M hM_pos hK_vol c hc hbad
  exact hC_bound hδ hδ_le s T hED he_unit h_dir_class hK_meas hK_cpt hM_pos hK_vol hc hbad

end -- close noncomputable section
end Kakeya
