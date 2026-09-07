import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Dyadic band selection for paper tube shadings

Given a cubical paper tube shading, pigeonhole the point multiplicity into
dyadic bands and select one retaining at least `1 / (log₂ N + 1)` of the total
mass. The selected band subshading has constant multiplicity within factor 2.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset Classical
open scoped ENNReal

/-- Dyadic band pigeonhole: select a multiplicity band retaining mass.

Given a cubical shading `S` with `N` tubes, there exists a level `k` such that
the dyadic band subshading at level `k`:
1. Is cubical
2. Has point multiplicity in `[2^k, 2^(k+1))` on its union
3. Retains at least `1 / (log₂ N + 1)` of the original mass
-/
lemma exists_dyadic_band_with_mass_retention
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (hcubical : WZ1PaperIsCubicalShading S)
    (hF_nonempty : F.Nonempty) :
    ∃ (level : ℕ),
      let S_k := wz1PaperDyadicBandSubshading S level
      WZ1PaperIsCubicalShading S_k ∧
      (∀ p ∈ S_k.union,
        (2 ^ level : ℕ) ≤ S_k.pointMultiplicity p ∧
        S_k.pointMultiplicity p < 2 ^ (level + 1)) ∧
      S.mass ≤ ((Nat.log 2 F.card + 1 : ℕ) : ENNReal) * S_k.mass := by
  classical
  let N : ℕ := F.card
  have hN_pos : 0 < N := hF_nonempty
  let numBands : ℕ := Nat.log 2 N + 1

  let band (k : ℕ) : Set Point3 := wz1PaperDyadicMultiplicityBand S k
  let bandMass (k : ℕ) : ENNReal := (wz1PaperDyadicBandSubshading S k).mass

  -- Bands are pairwise disjoint
  have h_disj : ∀ (k l : ℕ), k ≠ l → Disjoint (band k) (band l) := by
    intro k l hne
    simp only [band, wz1PaperDyadicMultiplicityBand, Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_setOf_eq] at hx1 hx2
    have h_cases : k < l ∨ l < k := by omega
    rcases h_cases with (hkl | hlk)
    · -- k < l
      have h1 : (2 ^ (k + 1) : ENNReal) ≤ (2 ^ l : ENNReal) := by
        have hkl' : k + 1 ≤ l := by omega
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hkl'
      have h2 : (S.pointMultiplicity x : ENNReal) < (2 ^ (k + 1) : ENNReal) := hx1.2
      have h3 : (2 ^ l : ENNReal) ≤ (S.pointMultiplicity x : ENNReal) := hx2.1
      have h4 : (2 ^ l : ENNReal) < (2 ^ (k + 1) : ENNReal) := h3.trans_lt h2
      exact not_le.mpr h4 h1
    · -- l < k
      have h1 : (2 ^ (l + 1) : ENNReal) ≤ (2 ^ k : ENNReal) := by
        have hlk' : l + 1 ≤ k := by omega
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hlk'
      have h2 : (S.pointMultiplicity x : ENNReal) < (2 ^ (l + 1) : ENNReal) := hx2.2
      have h3 : (2 ^ k : ENNReal) ≤ (S.pointMultiplicity x : ENNReal) := hx1.1
      have h4 : (2 ^ k : ENNReal) < (2 ^ (l + 1) : ENNReal) := h3.trans_lt h2
      exact not_le.mpr h4 h1

  -- Bands cover every point with positive multiplicity
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
        have h' : (Finset.univ : Finset (Fin F.card)).card = F.card := by
          simp
        rw [h'] at h
        exact h
      have h2 : Nat.log 2 (S.pointMultiplicity p) ≤ Nat.log 2 N := Nat.log_mono_right h1
      omega
    have h_in_band : p ∈ band k := by
      simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq]
      have h3 : (2 ^ k : ℕ) ≤ S.pointMultiplicity p :=
        Nat.pow_log_le_self 2 h_mult_pos.ne'
      have h4 : S.pointMultiplicity p < (2 ^ (k + 1) : ℕ) :=
        Nat.lt_pow_succ_log_self (by norm_num) (S.pointMultiplicity p)
      exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
    exact Set.mem_iUnion₂.mpr ⟨k, by simpa [Finset.mem_range] using hk_lt, h_in_band⟩

  -- Mass decomposition: total mass = sum of band masses
  have h_mass_decomp : S.mass = ∑ k ∈ Finset.range numBands, bandMass k := by
    have h_per_source : ∀ (i : Fin N),
        volume (S.carrier i) =
          ∑ k ∈ Finset.range numBands, volume (S.carrier i ∩ band k) := by
      intro i
      have h_disj' : Set.PairwiseDisjoint (↑(Finset.range numBands))
          (fun k => S.carrier i ∩ band k) := by
        intro k _ l _ hne
        exact (h_disj k l hne).mono Set.inter_subset_right Set.inter_subset_right
      have h_meas : ∀ k ∈ Finset.range numBands,
          MeasurableSet (S.carrier i ∩ band k) := by
        intro k _
        exact (S.measurable_carrier i).inter (wz1PaperDyadicMultiplicityBand_measurable S k)
      have h_union : S.carrier i =
          ⋃ k ∈ Finset.range numBands, (S.carrier i ∩ band k) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        constructor
        · intro hx
          have h := h_cover i hx
          rcases Set.mem_iUnion₂.mp h with ⟨k, hk, hxb⟩
          exact ⟨k, hk, hx, hxb⟩
        · rintro ⟨k, _, hx, _⟩
          exact hx
      have h : volume (S.carrier i) =
          ∑ k ∈ Finset.range numBands, volume (S.carrier i ∩ band k) := by
        have h2 : volume (⋃ k ∈ Finset.range numBands, (S.carrier i ∩ band k)) =
            ∑ k ∈ Finset.range numBands, volume (S.carrier i ∩ band k) :=
          MeasureTheory.measure_biUnion_finset h_disj' h_meas
        have h3 : volume (S.carrier i) = volume (⋃ k ∈ Finset.range numBands, (S.carrier i ∩ band k)) :=
          congrArg volume h_union
        rwa [h3]
      exact h
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

  -- Pigeonhole: some band has at least average mass
  have h_nonempty_range : (Finset.range numBands).Nonempty :=
    Finset.nonempty_range_iff.mpr (by omega)
  have h_max : ∃ k ∈ Finset.range numBands,
      ∀ l ∈ Finset.range numBands, bandMass l ≤ bandMass k :=
    Finset.exists_max_image (Finset.range numBands) bandMass h_nonempty_range
  rcases h_max with ⟨level, hlevel, hmax⟩
  have h_le : ∑ l ∈ Finset.range numBands, bandMass l ≤ (numBands : ENNReal) * bandMass level := by
    calc
      ∑ l ∈ Finset.range numBands, bandMass l
        ≤ ∑ l ∈ Finset.range numBands, bandMass level := by
          apply Finset.sum_le_sum
          intro l hl
          exact hmax l hl
      _ = (numBands : ENNReal) * bandMass level := by
          simp [Finset.sum_const]
          <;> ring
  have h_mass_retention : S.mass ≤ (numBands : ENNReal) * bandMass level := by
    rw [h_mass_decomp]
    exact h_le

  let S_k := wz1PaperDyadicBandSubshading S level

  have h_cubical_k : WZ1PaperIsCubicalShading S_k :=
    hcubical.dyadicBandSubshading level

  have h_mult_band : ∀ p ∈ S_k.union,
      (2 ^ level : ℕ) ≤ S_k.pointMultiplicity p ∧
      S_k.pointMultiplicity p < 2 ^ (level + 1) := by
    intro p hp
    have h_in_band : p ∈ band level := by
      rcases hp with ⟨i, hi⟩
      exact hi.2
    have h_eq : S_k.pointMultiplicity p = S.pointMultiplicity p := by
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
          exact ⟨h, h_in_band⟩
      exact h1
    rw [h_eq]
    have h5 : p ∈ band level := h_in_band
    simp only [band, wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq] at h5
    exact ⟨by exact_mod_cast h5.1, by exact_mod_cast h5.2⟩

  exact ⟨level, h_cubical_k, h_mult_band, h_mass_retention⟩

end Kakeya.Assouad

end
