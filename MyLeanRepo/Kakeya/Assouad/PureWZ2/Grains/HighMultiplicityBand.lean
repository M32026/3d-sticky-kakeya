import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicBandSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# High-multiplicity dyadic band selection

Select a dyadic multiplicity band whose lower bound is at least `2^k_min`,
retaining at least `1 / (2 * (log₂ N + 1))` of the total mass.

Requires `2^k_min * volume(S.union) ≤ S.mass / 2`, ensuring that the
low-multiplicity bands contain at most half the mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset Classical ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Select a dyadic band at level `≥ k_min` with logarithmic mass retention.

Requires `2^k_min * volume(S.union) ≤ S.mass / 2`, ensuring that the
low-multiplicity bands contain at most half the mass. -/
lemma high_multiplicity_dyadic_band
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF_nonempty : F.Nonempty)
    (k_min : ℕ)
    (hS_finite : S.mass ≠ ⊤)
    (hT_mass : (2 ^ k_min : ENNReal) * volume S.union ≤ S.mass / 2) :
    ∃ (level : ℕ), k_min ≤ level ∧
      let S_k := wz1PaperDyadicBandSubshading S level
      WZ1PaperIsCubicalShading S_k ∧
      (∀ p ∈ S_k.union,
        (2 ^ level : ENNReal) ≤ (S_k.pointMultiplicity p : ENNReal) ∧
        (S_k.pointMultiplicity p : ENNReal) < (2 ^ (level + 1) : ENNReal)) ∧
      S.mass ≤ (2 * (Nat.log 2 F.card + 1 : ENNReal)) * S_k.mass := by
  let N : ℕ := F.card
  have hN_pos : 0 < N := hF_nonempty
  let numBands : ℕ := Nat.log 2 N + 1
  let band (k : ℕ) : Set Point3 := wz1PaperDyadicMultiplicityBand S k
  let bandMass (k : ℕ) : ENNReal := (wz1PaperDyadicBandSubshading S k).mass

  have h_meas : ∀ k, MeasurableSet (band k) :=
    fun k => wz1PaperDyadicMultiplicityBand_measurable S k

  have h_disj : ∀ (k l : ℕ), k ≠ l → Disjoint (band k) (band l) := by
    intro k l hne
    simp only [band, wz1PaperDyadicMultiplicityBand, Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_setOf_eq] at hx1 hx2
    have h_cases : k < l ∨ l < k := by omega
    rcases h_cases with (hkl | hlk)
    · have hkl' : k + 1 ≤ l := by omega
      have h1 : (2 ^ (k + 1) : ENNReal) ≤ (2 ^ l : ENNReal) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hkl'
      have h2 : (S.pointMultiplicity x : ENNReal) < (2 ^ (k + 1) : ENNReal) := hx1.2
      have h3 : (2 ^ l : ENNReal) ≤ (S.pointMultiplicity x : ENNReal) := hx2.1
      have h4 : (2 ^ l : ENNReal) < (2 ^ (k + 1) : ENNReal) := h3.trans_lt h2
      exact not_le.mpr h4 h1
    · have hlk' : l + 1 ≤ k := by omega
      have h1 : (2 ^ (l + 1) : ENNReal) ≤ (2 ^ k : ENNReal) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hlk'
      have h2 : (S.pointMultiplicity x : ENNReal) < (2 ^ (l + 1) : ENNReal) := hx2.2
      have h3 : (2 ^ k : ENNReal) ≤ (S.pointMultiplicity x : ENNReal) := hx1.1
      have h4 : (2 ^ k : ENNReal) < (2 ^ (l + 1) : ENNReal) := h3.trans_lt h2
      exact not_le.mpr h4 h1

  -- Mass decomposition: total mass = sum of band masses (borrowed from DyadicBandSelection)
  have h_mass_decomp : S.mass = ∑ k ∈ Finset.range numBands, bandMass k := by
    have h_cover : ∀ (i : Fin N), S.carrier i ⊆ ⋃ k ∈ Finset.range numBands, band k := by
      intro i p hp
      have h_mult_pos : 0 < S.pointMultiplicity p := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        exact Finset.card_pos.mpr ⟨i, by simpa using hp⟩
      let k := Nat.log 2 (S.pointMultiplicity p)
      have hk_lt : k < numBands := by
        have h1 : S.pointMultiplicity p ≤ N := by
          simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
          have h : (Finset.univ.filter (fun i : Fin F.card => p ∈ S.carrier i)).card ≤ (Finset.univ : Finset (Fin F.card)).card :=
            Finset.card_le_univ _
          have h' : (Finset.univ : Finset (Fin F.card)).card = F.card := by simp
          rw [h'] at h
          exact h
        have h2 : Nat.log 2 (S.pointMultiplicity p) ≤ Nat.log 2 N := Nat.log_mono_right h1
        omega
      have h_in_band : p ∈ band k := by
        simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq]
        have h3 : (2 ^ k : ℕ) ≤ S.pointMultiplicity p := Nat.pow_log_le_self 2 h_mult_pos.ne'
        have h4 : S.pointMultiplicity p < (2 ^ (k + 1) : ℕ) := Nat.lt_pow_succ_log_self (by norm_num) (S.pointMultiplicity p)
        exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
      exact Set.mem_iUnion₂.mpr ⟨k, by simpa [Finset.mem_range] using hk_lt, h_in_band⟩
    have h_per_source : ∀ (i : Fin N),
        volume (S.carrier i) = ∑ k ∈ Finset.range numBands, volume (S.carrier i ∩ band k) := by
      intro i
      have h_disj' : Set.PairwiseDisjoint (↑(Finset.range numBands))
          (fun k => S.carrier i ∩ band k) := by
        intro k _ l _ hne
        exact (h_disj k l hne).mono Set.inter_subset_right Set.inter_subset_right
      have h_meas' : ∀ k ∈ Finset.range numBands, MeasurableSet (S.carrier i ∩ band k) := by
        intro k _
        exact (S.measurable_carrier i).inter (h_meas k)
      have h_union : S.carrier i = ⋃ k ∈ Finset.range numBands, (S.carrier i ∩ band k) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hx
          have h := h_cover i hx
          rcases Set.mem_iUnion₂.mp h with ⟨k, hk, hxb⟩
          exact ⟨k, hk, hx, hxb⟩
        · rintro ⟨k, _, hx, _⟩
          exact hx
      have h2 : volume (⋃ k ∈ Finset.range numBands, (S.carrier i ∩ band k)) =
          ∑ k ∈ Finset.range numBands, volume (S.carrier i ∩ band k) :=
        MeasureTheory.measure_biUnion_finset h_disj' h_meas'
      have h3 : volume (S.carrier i) = volume (⋃ k ∈ Finset.range numBands, (S.carrier i ∩ band k)) :=
        congrArg volume h_union
      rwa [h3]
    calc
      S.mass
        = ∑ i : Fin N, volume (S.carrier i) := by rfl
      _ = ∑ i : Fin N, ∑ k ∈ Finset.range numBands, volume (S.carrier i ∩ band k) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_per_source i
      _ = ∑ k ∈ Finset.range numBands, ∑ i : Fin N, volume (S.carrier i ∩ band k) := by
          rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range numBands, bandMass k := by
          apply Finset.sum_congr rfl
          intro k _
          rfl

  -- For each band k, S_k.union = band k (as sets)
  have h_union_eq_band : ∀ k, (wz1PaperDyadicBandSubshading S k).union = band k := by
    intro k
    let S_k := wz1PaperDyadicBandSubshading S k
    ext p
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have h : p ∈ S_k.carrier i := hi
      simp only [S_k, wz1PaperDyadicBandSubshading, Set.mem_inter_iff] at h
      exact h.2
    · intro hpb
      have h_pos : 0 < S.pointMultiplicity p := by
        simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq] at hpb
        have h5 : (2 ^ k : ENNReal) ≤ (S.pointMultiplicity p : ENNReal) := hpb.1
        have h6 : (0 : ENNReal) < (2 ^ k : ENNReal) := by positivity
        exact_mod_cast h6.trans_le h5
      rcases Finset.card_pos.mp h_pos with ⟨i, hi⟩
      have h7 : p ∈ S.carrier i := by simpa [Kakeya.Streamlined.Shading.pointMultiplicity] using hi
      refine ⟨i, ?_⟩
      simp only [S_k, wz1PaperDyadicBandSubshading, Set.mem_inter_iff]
      exact ⟨h7, hpb⟩

  -- Point multiplicity of S_k equals S on its union
  have h_mult_eq : ∀ k p, p ∈ (wz1PaperDyadicBandSubshading S k).union →
      (wz1PaperDyadicBandSubshading S k).pointMultiplicity p = S.pointMultiplicity p := by
    intro k p hp
    let S_k := wz1PaperDyadicBandSubshading S k
    have hpb : p ∈ band k := by
      rw [h_union_eq_band k] at hp
      exact hp
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro j _
    have h1 : p ∈ S_k.carrier j ↔ p ∈ S.carrier j := by
      simp only [S_k, wz1PaperDyadicBandSubshading, Set.mem_inter_iff]
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, hpb⟩
    exact h1

  -- Mass of each band k is bounded by 2^(k+1) * volume(band k)
  have h_band_mass_le : ∀ k, bandMass k ≤ (2 ^ (k + 1) : ENNReal) * volume (band k) := by
    intro k
    let S_k := wz1PaperDyadicBandSubshading S k
    have h_mult : ∀ p ∈ S_k.union, (S_k.pointMultiplicity p : ENNReal) < (2 ^ (k + 1) : ENNReal) := by
      intro p hp
      have h_eq : S_k.pointMultiplicity p = S.pointMultiplicity p := h_mult_eq k p hp
      rw [h_eq]
      have hpb : p ∈ band k := by rw [h_union_eq_band k] at hp; exact hp
      simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq] at hpb
      exact hpb.2
    have h_mult_le : ∀ p ∈ S_k.union, (S_k.pointMultiplicity p : ENNReal) ≤ (2 ^ (k + 1) : ENNReal) :=
      fun p hp => (h_mult p hp).le
    have h : S_k.mass ≤ (2 ^ (k + 1) : ENNReal) * volume S_k.union :=
      mass_le_of_pointMultiplicity_le h_mult_le
    have h9 : volume S_k.union = volume (band k) := by rw [h_union_eq_band k]
    rw [h9] at h
    exact h

  -- Mass of bands below k_min is bounded by 2^k_min * volume(S.union)
  have h_low_mass : ∑ k ∈ Finset.range k_min, bandMass k ≤
      (2 ^ k_min : ENNReal) * volume S.union := by
    have h_per_band : ∀ k ∈ Finset.range k_min,
        bandMass k ≤ (2 ^ k_min : ENNReal) * volume (band k) := by
      intro k hk
      have h_k_lt : k < k_min := Finset.mem_range.mp hk
      have h_k1 : k + 1 ≤ k_min := by omega
      have h_pow : (2 ^ (k + 1) : ENNReal) ≤ (2 ^ k_min : ENNReal) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) h_k1
      calc
        bandMass k ≤ (2 ^ (k + 1) : ENNReal) * volume (band k) := h_band_mass_le k
        _ ≤ (2 ^ k_min : ENNReal) * volume (band k) := by gcongr
    have h_disj' : Set.PairwiseDisjoint (↑(Finset.range k_min)) band := by
      intro k _ l _ hne
      exact h_disj k l hne
    have h_meas' : ∀ k ∈ Finset.range k_min, MeasurableSet (band k) := by
      intro k _
      exact h_meas k
    have h_union_sub : (⋃ k ∈ Finset.range k_min, band k) ⊆ S.union := by
      intro x hx
      have h_exists : ∃ (j : ℕ), j ∈ Finset.range k_min ∧ x ∈ band j := by
        simpa [Set.mem_iUnion] using hx
      rcases h_exists with ⟨j, hj, hxj⟩
      have h_pos : 0 < S.pointMultiplicity x := by
        have h5 : (0 : ENNReal) < (2 ^ j : ENNReal) := by positivity
        have h6 : (2 ^ j : ENNReal) ≤ (S.pointMultiplicity x : ENNReal) := hxj.1
        exact_mod_cast h5.trans_le h6
      rcases Finset.card_pos.mp h_pos with ⟨i, hi⟩
      have h7 : x ∈ S.carrier i := by simpa [Kakeya.Streamlined.Shading.pointMultiplicity] using hi
      exact ⟨i, h7⟩
    calc
      ∑ k ∈ Finset.range k_min, bandMass k
        ≤ ∑ k ∈ Finset.range k_min, (2 ^ k_min : ENNReal) * volume (band k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact h_per_band k hk
      _ = (2 ^ k_min : ENNReal) * ∑ k ∈ Finset.range k_min, volume (band k) := by
          rw [Finset.mul_sum]
      _ = (2 ^ k_min : ENNReal) * volume (⋃ k ∈ Finset.range k_min, band k) := by
          rw [MeasureTheory.measure_biUnion_finset h_disj' h_meas']
      _ ≤ (2 ^ k_min : ENNReal) * volume S.union := by
          exact mul_le_mul_of_nonneg_left (MeasureTheory.measure_mono h_union_sub) (by positivity)

  by_cases h_empty : ¬ (Finset.Ico k_min numBands).Nonempty
  · -- No bands above k_min: all mass in low bands, so S.mass ≤ S.mass/2, hence mass = 0
    have h1 : numBands ≤ k_min := by
      by_contra h
      have h2 : k_min < numBands := by omega
      have h3 : (Finset.Ico k_min numBands).Nonempty := Finset.nonempty_Ico.mpr (by omega)
      exact h_empty h3
    have h2 : S.mass ≤ (2 ^ k_min : ENNReal) * volume S.union := by
      rw [h_mass_decomp]
      have h3 : Finset.range numBands ⊆ Finset.range k_min := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢ <;> omega
      have h4 : ∑ k ∈ Finset.range numBands, bandMass k ≤
            ∑ k ∈ Finset.range k_min, bandMass k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h3
          intro i _ _
          positivity
      calc
        ∑ k ∈ Finset.range numBands, bandMass k
          ≤ ∑ k ∈ Finset.range k_min, bandMass k := h4
        _ ≤ (2 ^ k_min : ENNReal) * volume S.union := h_low_mass
    have h5 : S.mass ≤ S.mass / 2 := h2.trans hT_mass
    have h6 : 2 * S.mass ≤ S.mass := by
      have h_div : S.mass / 2 = S.mass * (2 : ENNReal)⁻¹ := by rfl
      rw [h_div] at h5
      have h_mul : (2 : ENNReal) * S.mass ≤ (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹) := by
        gcongr
      have h_eq : (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹) = S.mass := by
        calc
          (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹)
            = S.mass * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by ring
          _ = S.mass * 1 := by
            have h_inv : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
              apply ENNReal.mul_inv_cancel <;> norm_num
            rw [h_inv]
          _ = S.mass := by rw [mul_one]
      rw [h_eq] at h_mul
      exact h_mul
    have h7 : S.mass + S.mass ≤ S.mass := by
      simpa [two_mul] using h6
    have h8 : S.mass ≤ 0 := by
      have h9 : S.mass + S.mass ≤ S.mass + 0 := by simpa using h7
      have h10 := (ENNReal.add_le_add_iff_left hS_finite).mp h9
      simpa using h10
    have h_mass_zero : S.mass = 0 := by simpa using h8
    let S_k := wz1PaperDyadicBandSubshading S k_min
    have h_mult_band : ∀ p ∈ S_k.union,
        (2 ^ k_min : ENNReal) ≤ (S_k.pointMultiplicity p : ENNReal) ∧
        (S_k.pointMultiplicity p : ENNReal) < (2 ^ (k_min + 1) : ENNReal) := by
      intro p hp
      have h_eq : S_k.pointMultiplicity p = S.pointMultiplicity p := h_mult_eq k_min p hp
      rw [h_eq]
      have hpb : p ∈ band k_min := by rw [h_union_eq_band k_min] at hp; exact hp
      simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq] at hpb
      exact ⟨hpb.1, hpb.2⟩
    refine ⟨k_min, by linarith, hcubical.dyadicBandSubshading k_min, h_mult_band, ?_⟩
    simp [h_mass_zero, bandMass]
  · -- Bands above k_min are nonempty
    have h_nonempty : (Finset.Ico k_min numBands).Nonempty := by tauto
    rcases Finset.exists_max_image (Finset.Ico k_min numBands) bandMass h_nonempty with
      ⟨level, hlevel, hmax⟩
    have h_kmin_le_level : k_min ≤ level := (Finset.mem_Ico.mp hlevel).1
    have h_kmin_lt_numBands : k_min < numBands :=
      Finset.nonempty_Ico.mp h_nonempty
    have h_card_le : (Finset.Ico k_min numBands).card ≤ numBands := by
      have h_sub : Finset.Ico k_min numBands ⊆ Finset.range numBands := by
        intro x hx
        simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
        exact hx.2
      have h : (Finset.Ico k_min numBands).card ≤ (Finset.range numBands).card := Finset.card_le_card h_sub
      rw [Finset.card_range] at h
      exact h
    have h_sum_split : ∑ k ∈ Finset.range numBands, bandMass k =
        (∑ k ∈ Finset.range k_min, bandMass k) +
        ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
      rw [Finset.sum_range_add_sum_Ico _ (le_of_lt h_kmin_lt_numBands)]
    have h_high_mass : S.mass / 2 ≤ ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
      have h_eq : S.mass = (∑ k ∈ Finset.range k_min, bandMass k) +
            ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
        rw [h_mass_decomp, h_sum_split]
      have h_le : S.mass ≤ (2 ^ k_min : ENNReal) * volume S.union +
            ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
        calc
          S.mass = (∑ k ∈ Finset.range k_min, bandMass k) +
                ∑ k ∈ Finset.Ico k_min numBands, bandMass k := h_eq
          _ ≤ (2 ^ k_min : ENNReal) * volume S.union +
                ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
            gcongr <;> exact h_low_mass
      have h' : S.mass ≤ S.mass / 2 + ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
        calc
          S.mass ≤ (2 ^ k_min : ENNReal) * volume S.union +
                  ∑ k ∈ Finset.Ico k_min numBands, bandMass k := h_le
          _ ≤ S.mass / 2 + ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
            gcongr <;> exact hT_mass
      let Y := S.mass / 2
      have hY_ne_top : Y ≠ ⊤ := ENNReal.mul_ne_top hS_finite (by norm_num)
      have h2Y : 2 * Y = S.mass := by
        dsimp only [Y]
        have h : (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹) = S.mass := by
          calc
            (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹)
              = S.mass * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by ring
            _ = S.mass * 1 := by
              have h_inv : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
                apply ENNReal.mul_inv_cancel <;> norm_num
              rw [h_inv]
            _ = S.mass := by rw [mul_one]
        exact h
      have h_imp : Y + Y ≤ Y + ∑ k ∈ Finset.Ico k_min numBands, bandMass k := by
        have h15 : Y + Y = 2 * Y := by simp [two_mul]
        rw [h15, h2Y]
        exact h'
      exact (ENNReal.add_le_add_iff_left hY_ne_top).mp h_imp
    have h_le : ∑ k ∈ Finset.Ico k_min numBands, bandMass k ≤
        ((Finset.Ico k_min numBands).card : ENNReal) * bandMass level := by
      calc
        ∑ k ∈ Finset.Ico k_min numBands, bandMass k
          ≤ ∑ k ∈ Finset.Ico k_min numBands, bandMass level := by
            apply Finset.sum_le_sum
            intro l hl
            exact hmax l hl
        _ = ((Finset.Ico k_min numBands).card : ENNReal) * bandMass level := by
          simp [Finset.sum_const] <;> ring
    have h_mass_retention : S.mass ≤ (2 * (numBands : ENNReal)) * bandMass level := by
      have h4 : S.mass / 2 ≤ (numBands : ENNReal) * bandMass level := by
        calc
          S.mass / 2 ≤ ∑ k ∈ Finset.Ico k_min numBands, bandMass k := h_high_mass
          _ ≤ ((Finset.Ico k_min numBands).card : ENNReal) * bandMass level := h_le
          _ ≤ (numBands : ENNReal) * bandMass level := by
            gcongr <;> exact_mod_cast h_card_le
      have h5 : 2 * (S.mass / 2) ≤ 2 * ((numBands : ENNReal) * bandMass level) := by gcongr
      have h6 : 2 * (S.mass / 2) = S.mass := by
        have h : (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹) = S.mass := by
          calc
            (2 : ENNReal) * (S.mass * (2 : ENNReal)⁻¹)
              = S.mass * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by ring
            _ = S.mass * 1 := by
              have h_inv : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
                apply ENNReal.mul_inv_cancel <;> norm_num
              rw [h_inv]
            _ = S.mass := by rw [mul_one]
        exact h
      rw [h6] at h5
      simpa [mul_assoc] using h5
    let S_k := wz1PaperDyadicBandSubshading S level
    have h_cubical_k : WZ1PaperIsCubicalShading S_k :=
      hcubical.dyadicBandSubshading level
    have h_mult_band : ∀ p ∈ S_k.union,
        (2 ^ level : ENNReal) ≤ (S_k.pointMultiplicity p : ENNReal) ∧
        (S_k.pointMultiplicity p : ENNReal) < (2 ^ (level + 1) : ENNReal) := by
      intro p hp
      have h_eq : S_k.pointMultiplicity p = S.pointMultiplicity p := h_mult_eq level p hp
      rw [h_eq]
      have hpb : p ∈ band level := by rw [h_union_eq_band level] at hp; exact hp
      simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq] at hpb
      exact ⟨hpb.1, hpb.2⟩
    exact ⟨level, h_kmin_le_level, h_cubical_k, h_mult_band, by
      simpa [numBands] using h_mass_retention⟩

end Kakeya.Assouad

end
