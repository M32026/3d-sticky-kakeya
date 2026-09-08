import MyLeanRepo.Kakeya.Streamlined.MultiplicityHelpers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dyadic pigeonholing utilities

1. Dyadic decomposition of natural numbers
2. Dominant bin selection for finite sums
3. Logarithmic bounds
4. Multiplicity pigeonholing for shadings
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-! ### Dyadic decomposition -/

/-- Every positive natural number lies in a dyadic bin `[2^k, 2^(k+1))`. -/
lemma exists_dyadic_bin (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := by
  let k := Nat.log 2 n
  have h1 : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by linarith)
  have h2 : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  exact ⟨k, h1, h2⟩

/-! ### Dominant bin selection -/

/--
Given a finite family of nonnegative quantities and a bin assignment, there exists
a bin whose total, times the number of bins, is at least the grand total.
-/
lemma pigeonhole_bins {α : Type*} {s : Finset α} {a : α → ENNReal}
    {bin : α → ℕ} :
    ∃ k : ℕ,
      (∑ i ∈ s.filter (fun i => bin i = k), a i) * ((s.image bin).card : ENNReal) ≥
        ∑ i ∈ s, a i := by
  classical
  let B := s.image bin
  let x : ℕ → ENNReal := fun k => ∑ i ∈ s.filter (fun i => bin i = k), a i
  have h_main : ∑ k ∈ B, x k = ∑ i ∈ s, a i := by
    let t : ℕ → Finset α := fun k => s.filter (fun i => bin i = k)
    have h_disj : ∀ k1 ∈ B, ∀ k2 ∈ B, k1 ≠ k2 → Disjoint (t k1) (t k2) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have h1 : bin i = k1 := (Finset.mem_filter.mp hi1).2
      have h2 : bin i = k2 := (Finset.mem_filter.mp hi2).2
      exact hne (h1.symm.trans h2)
    have h_union : B.biUnion t = s := by
      apply Finset.ext
      intro i
      have h_iff : i ∈ B.biUnion t ↔ i ∈ s := by
        constructor
        · intro h
          rcases Finset.mem_biUnion.mp h with ⟨k, _hk, hik⟩
          exact (Finset.mem_filter.mp hik).1
        · intro hi
          have hbin : bin i ∈ B := Finset.mem_image.mpr ⟨i, hi, rfl⟩
          have hfil : i ∈ t (bin i) := by
            simpa [t] using hi
          exact Finset.mem_biUnion.mpr ⟨bin i, hbin, hfil⟩
      exact h_iff
    have h : ∑ k ∈ B, ∑ i ∈ t k, a i = ∑ i ∈ B.biUnion t, a i :=
      (Finset.sum_biUnion h_disj).symm
    rw [h, h_union]
  by_cases hB : B = ∅
  · have hs : s = ∅ := by simpa [B, Finset.image_eq_empty] using hB
    simp [hs]
    <;> exact ⟨0, by simp⟩
  · have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
    have h_exists : ∃ k ∈ B, ∀ j ∈ B, x j ≤ x k := by
      exact Finset.exists_max_image B x hBne
    rcases h_exists with ⟨k, hk, hmax⟩
    refine ⟨k, ?_⟩
    have h_sum : ∑ j ∈ B, x j ≤ ∑ j ∈ B, x k := by
      apply Finset.sum_le_sum
      intro j hj
      exact hmax j hj
    have h_count : ∑ j ∈ B, x k = (B.card : ENNReal) * x k := by
      rw [Finset.sum_const, mul_comm] <;> ring
    have h_goal : (B.card : ENNReal) * x k ≥ ∑ i ∈ s, a i := by
      calc ∑ i ∈ s, a i
        = ∑ j ∈ B, x j := h_main.symm
      _ ≤ ∑ j ∈ B, x k := h_sum
      _ = (B.card : ENNReal) * x k := h_count
    simpa [x, B, mul_comm] using h_goal

/-! ### Logarithmic bound -/

/--
For `n > 0` and `ε > 0`, there exists `C > 0` such that
`Nat.log 2 n + 1 ≤ C * n^ε`.
-/
lemma dyadic_levels_bound (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ (Nat.log 2 n + 1 : ℝ) ≤ C * (n : ℝ) ^ ε := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_pow : (2 : ℝ) ^ (Nat.log 2 n) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by linarith)
  have h1 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h_log_pow : Real.log ((2 : ℝ) ^ (Nat.log 2 n)) =
        (Nat.log 2 n : ℝ) * Real.log 2 := by
      rw [Real.log_pow] <;> norm_num
    have h : Real.log ((2 : ℝ) ^ (Nat.log 2 n)) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) h_pow
    rw [h_log_pow] at h
    exact h
  have h2 : Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := Real.log_le_rpow_div (by positivity) hε
  have h3 : (Nat.log 2 n : ℝ) ≤ (n : ℝ) ^ ε / (ε * Real.log 2) := by
    have h_div : ((Nat.log 2 n : ℝ) * Real.log 2) / Real.log 2 = (Nat.log 2 n : ℝ) := by
      field_simp [h_log2_pos.ne'] <;> ring
    calc (Nat.log 2 n : ℝ)
      = ((Nat.log 2 n : ℝ) * Real.log 2) / Real.log 2 := h_div.symm
    _ ≤ Real.log (n : ℝ) / Real.log 2 := by gcongr
    _ ≤ ((n : ℝ) ^ ε / ε) / Real.log 2 := by gcongr
    _ = (n : ℝ) ^ ε / (ε * Real.log 2) := by ring
  have h4 : (n : ℝ) ≥ 1 := by exact_mod_cast hn
  have h5 : (n : ℝ) ^ ε ≥ 1 := by
    have h6 : (n : ℝ) ≥ 1 := h4
    have h7 : (n : ℝ) ^ ε ≥ 1 ^ ε := by gcongr
    simpa using h7
  let C : ℝ := 1 / (ε * Real.log 2) + 1
  have hC_pos : 0 < C := by positivity
  have h9 : 1 ≤ (n : ℝ) ^ ε := h5
  have h10 : C * (n : ℝ) ^ ε = (n : ℝ) ^ ε / (ε * Real.log 2) + (n : ℝ) ^ ε := by
    have h11 : C * (n : ℝ) ^ ε = (1 / (ε * Real.log 2)) * (n : ℝ) ^ ε + 1 * (n : ℝ) ^ ε := by
      rw [add_mul]
      <;> ring
    rw [h11]
    have h12 : (1 / (ε * Real.log 2)) * (n : ℝ) ^ ε = (n : ℝ) ^ ε / (ε * Real.log 2) := by ring
    rw [h12]
    <;> ring
  have h6 : (Nat.log 2 n + 1 : ℝ) ≤ C * (n : ℝ) ^ ε := by
    rw [h10]
    have h7 : (Nat.log 2 n : ℝ) + 1 ≤ (n : ℝ) ^ ε / (ε * Real.log 2) + 1 := by linarith
    have h8 : (n : ℝ) ^ ε / (ε * Real.log 2) + 1 ≤ (n : ℝ) ^ ε / (ε * Real.log 2) + (n : ℝ) ^ ε := by
      gcongr
      <;> linarith
    linarith
  exact ⟨C, hC_pos, h6⟩

/-! ### Restricted shading -/

/-- Restrict a shading to a measurable set `S`. -/
def Shading.restrict {F : BodyFamily} (Y : Shading F) (S : Set Point3)
    (hS : MeasurableSet S) : Shading F where
  carrier := fun i => Y.carrier i ∩ S
  measurable_carrier := fun i => (Y.measurable_carrier i).inter hS
  subset_body := fun i => Set.inter_subset_left.trans (Y.subset_body i)

/-- The mass of a restricted shading equals the set-lintegral of the multiplicity. -/
lemma restrict_mass_eq_set_lintegral {F : BodyFamily} {Y : Shading F}
    {S : Set Point3} (hS : MeasurableSet S) :
    (Y.restrict S hS).mass = ∫⁻ x in S, (Y.pointMultiplicity x : ENNReal) := by
  let g : Point3 → ENNReal := fun x => (Y.pointMultiplicity x : ENNReal)
  let ind : (Fin F.card) → (Point3 → ENNReal) := fun i =>
    Set.indicator (Y.carrier i) (fun _ : Point3 => (1 : ENNReal))
  have h1 : g = fun x => ∑ i : Fin F.card, ind i x := by
    funext x
    exact pointMultiplicity_eq_sum_indicators Y x
  have h2 : (Y.restrict S hS).mass = ∑ i : Fin F.card, volume (Y.carrier i ∩ S) := by rfl
  rw [h2]
  have h3 : ∀ i : Fin F.card, volume (Y.carrier i ∩ S) = ∫⁻ x in S, ind i x := by
    intro i
    simp [ind, MeasureTheory.setLIntegral_indicator, Y.measurable_carrier i, hS]
  have h4 : ∑ i : Fin F.card, volume (Y.carrier i ∩ S) =
      ∑ i : Fin F.card, ∫⁻ x in S, ind i x := by
    apply Finset.sum_congr rfl
    intro i _
    exact h3 i
  rw [h4]
  have h5 : ∑ i : Fin F.card, ∫⁻ x in S, ind i x =
      ∫⁻ x in S, ∑ i : Fin F.card, ind i x := by
    have h6 : ∫⁻ x in S, ∑ i : Fin F.card, ind i x =
        ∑ i : Fin F.card, ∫⁻ x in S, ind i x := by
      exact MeasureTheory.lintegral_finsetSum (Finset.univ)
        (fun i _ => Measurable.indicator (by fun_prop) (Y.measurable_carrier i))
    exact h6.symm
  rw [h5]
  congr
  exact h1.symm

/-! ### Multiplicity pigeonholing -/

/--
The dyadic level set `{x | 2^k ≤ Y.pointMultiplicity x < 2^(k+1)}` is measurable.
-/
lemma multiplicity_level_set_measurable {F : BodyFamily} (Y : Shading F) (k : ℕ) :
    MeasurableSet {x : Point3 | 2 ^ k ≤ Y.pointMultiplicity x ∧
                                    Y.pointMultiplicity x < 2 ^ (k + 1)} := by
  let f : Point3 → ENNReal := fun x => (Y.pointMultiplicity x : ENNReal)
  have hf_meas : Measurable f := Shading.pointMultiplicity_measurable Y
  have h_eq : {x : Point3 | 2 ^ k ≤ Y.pointMultiplicity x ∧ Y.pointMultiplicity x < 2 ^ (k + 1)} =
      {x : Point3 | (2 ^ k : ENNReal) ≤ f x ∧ f x < (2 ^ (k + 1) : ENNReal)} := by
    ext x
    simp [f] <;> constructor <;> intro h <;> exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  rw [h_eq]
  have h1 : MeasurableSet {x : Point3 | (2 ^ k : ENNReal) ≤ f x} :=
    hf_meas measurableSet_Ici
  have h2 : MeasurableSet {x : Point3 | f x < (2 ^ (k + 1) : ENNReal)} :=
    hf_meas measurableSet_Iio
  exact h1.inter h2

/--
Dyadic multiplicity pigeonholing.

Given a shading `Y`, there exists a dyadic level `k` and a measurable set `Ω`
such that on `Ω` the pointwise multiplicity is in `[2^k, 2^(k+1))`, and the
restriction of `Y` to `Ω` has mass at least `Y.mass / (Nat.log 2 F.card + 1)`.
-/
lemma multiplicity_pigeonhole {F : BodyFamily} (Y : Shading F)
    (h_card : 0 < F.card) :
    ∃ (k : ℕ) (Ω : Set Point3) (hΩ : MeasurableSet Ω),
      (∀ x ∈ Ω, 2 ^ k ≤ Y.pointMultiplicity x ∧ Y.pointMultiplicity x < 2 ^ (k + 1)) ∧
      (Y.restrict Ω hΩ).mass * (Nat.log 2 F.card + 1 : ENNReal) ≥ Y.mass := by
  classical
  let K := Nat.log 2 F.card + 1
  let bins : Finset ℕ := Finset.range K
  let f : Point3 → ENNReal := fun x => (Y.pointMultiplicity x : ENNReal)
  have hf_meas : Measurable f := Shading.pointMultiplicity_measurable Y
  have h_max_mult : ∀ x : Point3, Y.pointMultiplicity x ≤ F.card := by
    intro x
    have h : (Finset.univ.filter fun i : Fin F.card => x ∈ Y.carrier i) ⊆ (Finset.univ : Finset (Fin F.card)) :=
      Finset.filter_subset _ _
    have h' : (Finset.univ.filter fun i : Fin F.card => x ∈ Y.carrier i).card ≤ Finset.univ.card :=
      Finset.card_le_card h
    have h_univ_card : (Finset.univ : Finset (Fin F.card)).card = F.card := by
      exact Finset.card_fin F.card
    rw [h_univ_card] at h'
    exact h'
  let Ω (k : ℕ) : Set Point3 :=
    {x | 2 ^ k ≤ Y.pointMultiplicity x ∧ Y.pointMultiplicity x < 2 ^ (k + 1)}
  have hΩ_eq : ∀ k, Ω k = {x : Point3 | (2 ^ k : ENNReal) ≤ f x ∧ f x < (2 ^ (k + 1) : ENNReal)} := by
    intro k
    ext x
    simp [Ω, f]
    <;> norm_cast
  have hΩ_meas : ∀ k, MeasurableSet (Ω k) := by
    intro k
    rw [hΩ_eq k]
    have h1 : MeasurableSet {x : Point3 | (2 ^ k : ENNReal) ≤ f x} := by
      exact hf_meas measurableSet_Ici
    have h2 : MeasurableSet {x : Point3 | f x < (2 ^ (k + 1) : ENNReal)} := by
      exact hf_meas measurableSet_Iio
    exact h1.inter h2
  let m (k : ℕ) : ENNReal := (Y.restrict (Ω k) (hΩ_meas k)).mass
  have h_disj : ∀ k1 ∈ bins, ∀ k2 ∈ bins, k1 ≠ k2 → Disjoint (Ω k1) (Ω k2) := by
    intro k1 _ k2 _ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : 2 ^ k1 ≤ Y.pointMultiplicity x := hx1.1
    have h2 : Y.pointMultiplicity x < 2 ^ (k1 + 1) := hx1.2
    have h3 : 2 ^ k2 ≤ Y.pointMultiplicity x := hx2.1
    have h4 : Y.pointMultiplicity x < 2 ^ (k2 + 1) := hx2.2
    by_cases h : k1 < k2
    · have h5 : 2 ^ (k1 + 1) ≤ 2 ^ k2 := by
        gcongr <;> omega
      linarith
    · have h6 : k2 < k1 := by omega
      have h7 : 2 ^ (k2 + 1) ≤ 2 ^ k1 := by
        gcongr <;> omega
      linarith
  have h_pointwise : ∀ (x : Point3), f x = ∑ k ∈ bins, Set.indicator (Ω k) f x := by
    intro x
    by_cases hfx : f x = 0
    · have h_nat : Y.pointMultiplicity x = 0 := by
        simpa [f, ENNReal.coe_eq_zero] using hfx
      have h_all_zero : ∀ k ∈ bins, Set.indicator (Ω k) f x = 0 := by
        intro k _
        have h_not : x ∉ Ω k := by
          intro h
          have h_pos : 0 < Y.pointMultiplicity x := by
            have h_pos2 : 0 < 2 ^ k := by positivity
            linarith [h.1]
          rw [h_nat] at h_pos <;> simpa using h_pos
        simp [Set.indicator_apply, h_not]
      have h_sum : ∑ k ∈ bins, Set.indicator (Ω k) f x = 0 := by
        rw [Finset.sum_congr rfl h_all_zero] <;> simp
      rw [h_sum, hfx]
    · have hfx' : 0 < f x := by
        by_contra h
        exact hfx (by simpa using h)
      have h_pos : 0 < Y.pointMultiplicity x := by
        by_contra h
        have h' : Y.pointMultiplicity x = 0 := by omega
        have h'' : f x = 0 := by
          simp [f, h']
        exact hfx h''
      have h_le : Y.pointMultiplicity x ≤ F.card := h_max_mult x
      let k0 := Nat.log 2 (Y.pointMultiplicity x)
      have hk1 : 2 ^ k0 ≤ Y.pointMultiplicity x := Nat.pow_log_le_self 2 (by omega)
      have hk2 : Y.pointMultiplicity x < 2 ^ (k0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h_log_mono : k0 ≤ Nat.log 2 F.card :=
        Nat.log_mono_right (h_max_mult x)
      have hk3 : k0 < K := by
        simp only [K] <;> omega
      have hk0_in : k0 ∈ bins := Finset.mem_range.mpr hk3
      have hx0 : x ∈ Ω k0 := ⟨hk1, hk2⟩
      have h_unique : ∀ k ∈ bins, x ∈ Ω k → k = k0 := by
        intro k hk_in hxk
        by_contra hne
        have h_disj' : Disjoint (Ω k) (Ω k0) := h_disj k hk_in k0 hk0_in hne
        exact Set.disjoint_left.mp h_disj' hxk hx0
      have h_sum : ∑ k ∈ bins, Set.indicator (Ω k) f x = f x := by
        rw [Finset.sum_eq_single_of_mem k0 hk0_in]
        · simp [Set.indicator_apply, hx0]
        · intro j _ hjne
          have h_not : x ∉ Ω j := by
            intro h
            exact hjne (h_unique j ‹_› h)
          simp [Set.indicator_apply, h_not]
      exact h_sum.symm
  have h_mass_eq : Y.mass = ∑ k ∈ bins, m k := by
    have h_f_def : (fun x : Point3 => (Y.pointMultiplicity x : ENNReal)) = f := by rfl
    have h1 : (∫⁻ x : Point3, (Y.pointMultiplicity x : ENNReal)) = Y.mass :=
      lintegral_pointMultiplicity_eq_mass Y
    have h1' : (∫⁻ x : Point3, f x) = Y.mass := by
      rw [← h_f_def]
      exact h1
    have h2 : ∫⁻ x, f x = ∫⁻ x, ∑ k ∈ bins, Set.indicator (Ω k) f x := by
      congr with x
      exact h_pointwise x
    have h3 : ∫⁻ x, ∑ k ∈ bins, Set.indicator (Ω k) f x =
        ∑ k ∈ bins, ∫⁻ x, Set.indicator (Ω k) f x := by
      apply MeasureTheory.lintegral_finsetSum
      intro k _
      exact hf_meas.indicator (hΩ_meas k)
    have h4 : ∑ k ∈ bins, ∫⁻ x, Set.indicator (Ω k) f x =
        ∑ k ∈ bins, ∫⁻ x in Ω k, f x := by
      apply Finset.sum_congr rfl
      intro k _
      exact MeasureTheory.lintegral_indicator (hΩ_meas k) f
    have h5 : ∑ k ∈ bins, ∫⁻ x in Ω k, f x = ∑ k ∈ bins, m k := by
      apply Finset.sum_congr rfl
      intro k _
      exact (restrict_mass_eq_set_lintegral (hΩ_meas k)).symm
    calc Y.mass
      = ∫⁻ x, f x := h1'.symm
    _ = ∫⁻ x, ∑ k ∈ bins, Set.indicator (Ω k) f x := h2
    _ = ∑ k ∈ bins, ∫⁻ x, Set.indicator (Ω k) f x := h3
    _ = ∑ k ∈ bins, ∫⁻ x in Ω k, f x := h4
    _ = ∑ k ∈ bins, m k := h5
  have hB_pos : 0 < bins.card := by
    simp [bins, K] <;> omega
  have h_exists : ∃ k ∈ bins, ∀ j ∈ bins, m j ≤ m k := by
    exact Finset.exists_max_image bins m (Finset.nonempty_iff_ne_empty.mpr (by simp [bins, K] <;> omega))
  rcases h_exists with ⟨k, hk, hmax⟩
  have h_sum : ∑ j ∈ bins, m j ≤ ∑ j ∈ bins, m k := by
    apply Finset.sum_le_sum
    intro j hj
    exact hmax j hj
  have h_count : ∑ j ∈ bins, m k = (bins.card : ENNReal) * m k := by
    rw [Finset.sum_const, mul_comm] <;> ring
  have h_final : (bins.card : ENNReal) * m k ≥ Y.mass := by
    calc Y.mass
      = ∑ j ∈ bins, m j := h_mass_eq
    _ ≤ ∑ j ∈ bins, m k := h_sum
    _ = (bins.card : ENNReal) * m k := h_count
  have h_K : (bins.card : ENNReal) = (K : ENNReal) := by
    simp [bins, Finset.card_range]
  have h_final2 : (K : ENNReal) * m k ≥ Y.mass := by
    rw [← h_K]
    exact h_final
  have h_comm : m k * (K : ENNReal) = (K : ENNReal) * m k := by ring
  have h_final3 : m k * (K : ENNReal) ≥ Y.mass := by
    rw [h_comm]
    exact h_final2
  have h_mk : m k = (Y.restrict (Ω k) (hΩ_meas k)).mass := by rfl
  have h_Kdef : (K : ENNReal) = (Nat.log 2 F.card + 1 : ENNReal) := by
    simp [K] <;> norm_cast
  rw [h_mk, h_Kdef] at h_final3
  exact ⟨k, Ω k, hΩ_meas k, fun x hx => hx, h_final3⟩

end Kakeya.Streamlined
