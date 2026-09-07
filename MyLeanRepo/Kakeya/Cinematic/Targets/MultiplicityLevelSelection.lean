import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Dyadic multiplicity-level selection

This is the measurable dyadic pigeonholing step used to create the initial
restricted weak-type shading in PYZ Section 5.
-/

namespace Kakeya.Cinematic

open MeasureTheory

theorem multiplicity_level_selection :
    MultiplicityLevelSelectionStatement := by
  classical
  intro delta _hdelta F E hE hE_finite
  dsimp only
  let m : ℝ × ℝ → ℝ := multiplicity F delta
  let g : ℝ × ℝ → ℝ := fun p => Real.rpow (m p) (3 / 2 : ℝ)
  let count : ℝ × ℝ → ℕ := fun p =>
    (F.toFinset.filter fun f => p ∈ graphNeighborhood f delta).card
  let levelCount : ℕ := Nat.log2 (F.card + 1) + 1
  let levels : Finset ℕ := Finset.range levelCount
  let layer : ℕ → Set (ℝ × ℝ) := fun j =>
    E ∩ {p |
      (((2 ^ j : ℕ) : ℝ)) ≤ m p ∧
        m p < (((2 ^ (j + 1) : ℕ) : ℝ))}
  have hcount (p : ℝ × ℝ) : m p = (count p : ℝ) := by
    dsimp only [m, count]
    change
      (∑ f ∈ F.toFinset,
        if p ∈ graphNeighborhood f delta then (1 : ℝ) else 0) =
          (((F.toFinset.filter fun f => p ∈ graphNeighborhood f delta).card : ℕ) : ℝ)
    exact Finset.sum_boole _ _
  have htoFinset_card : F.toFinset.card = F.card := by
    unfold FiniteFunctionFamily.toFinset FiniteFunctionFamily.card
    exact (Set.ncard_eq_toFinset_card F.carrier F.finite).symm
  have hcount_le (p : ℝ × ℝ) : count p ≤ F.card := by
    dsimp only [count]
    rw [← htoFinset_card]
    exact Finset.card_filter_le _ _
  have hm_nonneg (p : ℝ × ℝ) : 0 ≤ m p := by
    rw [hcount]
    positivity
  have hg_nonneg (p : ℝ × ℝ) : 0 ≤ g p := by
    dsimp only [g]
    exact Real.rpow_nonneg (hm_nonneg p) _
  have hm_measurable : Measurable m := by
    exact measurable_multiplicity F delta
  have hg_measurable : Measurable g := by
    dsimp only [g]
    exact
      (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp
        hm_measurable
  have hlayer_measurable (j : ℕ) : MeasurableSet (layer j) := by
    dsimp only [layer]
    exact hE.inter <|
      (measurableSet_le measurable_const hm_measurable).inter
        (measurableSet_lt hm_measurable measurable_const)
  have hg_bounded (p : ℝ × ℝ) :
      ‖g p‖ ≤ Real.rpow (F.card : ℝ) (3 / 2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg p)]
    dsimp only [g]
    apply Real.rpow_le_rpow (hm_nonneg p)
    · rw [hcount]
      exact_mod_cast hcount_le p
    · norm_num
  have hg_integrableOn_E : IntegrableOn g E := by
    apply Measure.integrableOn_of_bounded hE_finite.ne hg_measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => hg_bounded p
  have hg_integrableOn_layer (j : ℕ) : IntegrableOn g (layer j) :=
    hg_integrableOn_E.mono_set fun _ hp => hp.1
  by_cases htotal : (∫ p in E, g p) = 0
  · left
    simpa [g, m] using htotal
  right
  have hlevelCount_pos : 0 < levelCount := by
    dsimp only [levelCount]
    omega
  have hlevels_nonempty : levels.Nonempty := by
    dsimp only [levels]
    exact ⟨0, Finset.mem_range.mpr hlevelCount_pos⟩
  obtain ⟨j, hj_levels, hj_max⟩ :=
    Finset.exists_max_image levels (fun k => ∫ p in layer k, g p) hlevels_nonempty
  let mu : ℕ := 2 ^ j
  have hmu_pos : 0 < mu := by
    dsimp only [mu]
    positivity
  have hlayer_subset : layer j ⊆ E := by
    intro p hp
    exact hp.1
  have hlayer_bounds :
      ∀ p ∈ layer j,
        mu ≤ multiplicity F delta p ∧
          multiplicity F delta p < 2 * mu := by
    intro p hp
    have hp_layer := hp.2
    constructor
    · dsimp only [mu]
      simpa [m] using hp_layer.1
    · dsimp only [mu]
      rw [pow_succ] at hp_layer
      norm_num [mul_comm] at hp_layer ⊢
      simpa [m] using hp_layer.2
  have hpairwise :
      (↑levels : Set ℕ).Pairwise (Function.onFun Disjoint layer) := by
    intro a ha b hb hab
    change Disjoint (layer a) (layer b)
    rw [Set.disjoint_left]
    intro p hpa hpb
    have hpa' := hpa.2
    have hpb' := hpb.2
    rcases lt_or_gt_of_ne hab with hab_lt | hba_lt
    · have hab_succ : a + 1 ≤ b := by omega
      have hpow : (2 : ℕ) ^ (a + 1) ≤ 2 ^ b :=
        Nat.pow_le_pow_right (by omega) hab_succ
      have hpow_real :
          (((2 ^ (a + 1) : ℕ) : ℝ)) ≤ (((2 ^ b : ℕ) : ℝ)) := by
        exact_mod_cast hpow
      linarith [hpa'.2, hpb'.1, hpow_real]
    · have hba_succ : b + 1 ≤ a := by omega
      have hpow : (2 : ℕ) ^ (b + 1) ≤ 2 ^ a :=
        Nat.pow_le_pow_right (by omega) hba_succ
      have hpow_real :
          (((2 ^ (b + 1) : ℕ) : ℝ)) ≤ (((2 ^ a : ℕ) : ℝ)) := by
        exact_mod_cast hpow
      linarith [hpb'.2, hpa'.1, hpow_real]
  have hpositivePart :
      {p ∈ E | 0 < m p} = ⋃ k ∈ levels, layer k := by
    ext p
    constructor
    · intro hp
      have hcount_pos : 0 < count p := by
        change p ∈ E ∧ 0 < m p at hp
        rw [hcount p] at hp
        exact_mod_cast hp.2
      let k : ℕ := Nat.log2 (count p)
      have hk_lt : k < levelCount := by
        have hcount_succ : count p ≤ F.card + 1 :=
          (hcount_le p).trans (Nat.le_succ _)
        have hlog :
            Nat.log2 (count p) ≤ Nat.log2 (F.card + 1) := by
          rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
          exact Nat.log_mono_right hcount_succ
        dsimp only [k, levelCount]
        omega
      have hk_lower : (2 : ℕ) ^ k ≤ count p := by
        dsimp only [k]
        rw [Nat.log2_eq_log_two]
        exact Nat.pow_log_le_self 2 hcount_pos.ne'
      have hk_upper : count p < (2 : ℕ) ^ (k + 1) := by
        dsimp only [k]
        rw [Nat.log2_eq_log_two]
        simpa only [Nat.succ_eq_add_one] using
          Nat.lt_pow_succ_log_self Nat.one_lt_two (count p)
      simp only [Set.mem_iUnion]
      refine ⟨k, Finset.mem_range.mpr hk_lt, hp.1, ?_, ?_⟩
      · rw [hcount]
        exact_mod_cast hk_lower
      · rw [hcount]
        exact_mod_cast hk_upper
    · simp only [Set.mem_iUnion]
      rintro ⟨k, hk, hpE, hp_lower, _hp_upper⟩
      refine ⟨hpE, ?_⟩
      exact lt_of_lt_of_le (by positivity) hp_lower
  have hzeroPart_measurable : MeasurableSet {p ∈ E | m p = 0} := by
    exact hE.inter (hm_measurable (measurableSet_singleton 0))
  have hE_decomposition :
      E = {p ∈ E | 0 < m p} ∪ {p ∈ E | m p = 0} := by
    ext p
    constructor
    · intro hp
      rcases (hm_nonneg p).eq_or_lt with hp_zero | hp_pos
      · exact Or.inr ⟨hp, hp_zero.symm⟩
      · exact Or.inl ⟨hp, hp_pos⟩
    · rintro (hp | hp) <;> exact hp.1
  have hzero_integrand :
      ∀ p ∈ {p ∈ E | m p = 0}, g p = 0 := by
    intro p hp
    dsimp only [g]
    rw [hp.2]
    norm_num
  have htotal_sum :
      (∫ p in E, g p) = ∑ k ∈ levels, ∫ p in layer k, g p := by
    rw [hE_decomposition,
      MeasureTheory.integral_union_eq_left_of_forall hzeroPart_measurable hzero_integrand,
      hpositivePart]
    exact MeasureTheory.integral_biUnion_finset levels
      (fun k _ => hlayer_measurable k) hpairwise
      (fun k _ => hg_integrableOn_layer k)
  have hsum_le :
      (∑ k ∈ levels, ∫ p in layer k, g p) ≤
        levels.card • (∫ p in layer j, g p) := by
    exact Finset.sum_le_card_nsmul levels _ _ hj_max
  have hfinal :
      (∫ p in E, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
        ((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ) *
          ∫ p in layer j,
            Real.rpow (multiplicity F delta p) (3 / 2 : ℝ) := by
    calc
      ∫ p in E, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ) =
          ∫ p in E, g p := by rfl
      _ = ∑ k ∈ levels, ∫ p in layer k, g p := htotal_sum
      _ ≤ levels.card • (∫ p in layer j, g p) := hsum_le
      _ =
          ((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ) *
            ∫ p in layer j, g p := by
        rw [nsmul_eq_mul]
        congr 1
        dsimp only [levels, levelCount]
        rw [Finset.card_range]
      _ =
          ((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ) *
            ∫ p in layer j,
              Real.rpow (multiplicity F delta p) (3 / 2 : ℝ) := by
        rfl
  exact
    ⟨mu, hmu_pos, layer j, hlayer_measurable j, hlayer_subset,
      hlayer_bounds, hfinal⟩

end Kakeya.Cinematic
