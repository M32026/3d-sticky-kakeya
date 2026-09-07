module

/-
  A7 physical S-set extraction: Phases 3-5 and main output.

  Contains the index growth/energy bound (Phase 3), index S-set (Phase 4),
  physical S-set (Phase 5), and the final `A7_physical_full_output`
  construction.

  This is the main production module for A7. Import this file to get
  `A7_physical_full_output`.

  Split from the original monolithic A7_PhysicalSSet.lean to reduce
  per-file elaboration memory.

  Whiteprint node: appendix_a_alternative / a7_physical_sset
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A7_ExtractionBase
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A7_PhysicalExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)
open DirecretisedFurstenbergEstimate.Phase2
open MainAppendix

namespace DirecretisedFurstenbergEstimate.AppendixA

noncomputable section

/-- Phase 3: Index ball growth and point energy bound. -/
lemma a7_index_growth_and_energy {Δ δ s t ε : ℝ} {a5 : A5_Output Δ δ s t ε}
    (hΔ_pos : 0 < Δ)
    (d : A7_ExtractionResult Δ δ s t ε a5) :
    (∀ q ∈ d.Q0, ∀ r : ℝ, Δ ≤ r →
      ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + d.A_idx * Real.rpow r d.u) ∧
    (∀ q ∈ d.Q0, pointEnergy d.u d.Q0 q ≤ d.A_idx) := by
  classical
  have h_growth_idx : ∀ q ∈ d.Q0, ∀ r : ℝ, Δ ≤ r →
      ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + d.A_idx * Real.rpow r d.u := by
    intro q hq r hr
    let c := squareCenter Δ q
    have hc : c ∈ d.Q0_phys := by
      rw [←d.hQ0_phys_eq]; exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h1 : ∀ q' ∈ d.Q0, dist q q' ≤ r → dist c (squareCenter Δ q') ≤ Real.sqrt 2 * Δ * r := by
      intro q' _ hle
      have h2 : dist c (squareCenter Δ q') ≤ Real.sqrt 2 * Δ * dist q q' := squareCenter_dist_upper hΔ_pos q q'
      calc dist c (squareCenter Δ q')
        ≤ Real.sqrt 2 * Δ * dist q q' := h2
      _ ≤ Real.sqrt 2 * Δ * r := by gcongr
    have h3 : (d.Q0.filter fun q' => dist q q' ≤ r).image (squareCenter Δ) ⊆
        d.Q0_phys.filter fun c' => dist c c' ≤ Real.sqrt 2 * Δ * r := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨q', hq', rfl⟩
      have h4 : dist q q' ≤ r := (Finset.mem_filter.mp hq').2
      have h5 : squareCenter Δ q' ∈ d.Q0_phys := by
        rw [←d.hQ0_phys_eq]; exact Finset.mem_image.mpr ⟨q', (Finset.mem_filter.mp hq').1, rfl⟩
      exact Finset.mem_filter.mpr ⟨h5, h1 q' (Finset.mem_filter.mp hq').1 h4⟩
    have h4 : ((d.Q0.filter fun q' => dist q q' ≤ r).card) ≤
        (d.Q0_phys.filter fun c' => dist c c' ≤ Real.sqrt 2 * Δ * r).card := by
      have h5 : ((d.Q0.filter fun q' => dist q q' ≤ r).image (squareCenter Δ)).card =
          (d.Q0.filter fun q' => dist q q' ≤ r).card := by
        rw [Finset.card_image_of_injective _ d.h_inj]
      rw [←h5]
      exact Finset.card_le_card h3
    have h6 : ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + d.A_idx * Real.rpow r d.u := by
      by_cases h_case : r < 1
      · -- r < 1
        have h_filter_le_one : (d.Q0.filter fun q' => dist q q' ≤ r).card ≤ 1 := by
          have h1 : ∀ q' ∈ d.Q0.filter (fun q' => dist q q' ≤ r), q' = q := by
            intro q' hq'
            have h2 : dist q q' ≤ r := (Finset.mem_filter.mp hq').2
            have h3 : dist q q' < 1 := by linarith
            have h4 : q' = q := by
              have h5 : dist q q' = max (|(q.1 : ℝ) - (q'.1 : ℝ)|) (|(q.2 : ℝ) - (q'.2 : ℝ)|) := by
                simp [dist] <;> rfl
              rw [h5] at h3
              have h6 : |(q.1 : ℝ) - (q'.1 : ℝ)| < 1 := by
                calc |(q.1 : ℝ) - (q'.1 : ℝ)| ≤ max (|(q.1 : ℝ) - (q'.1 : ℝ)|) (|(q.2 : ℝ) - (q'.2 : ℝ)|) := le_max_left _ _
                  _ < 1 := h3
              have h7 : |(q.2 : ℝ) - (q'.2 : ℝ)| < 1 := by
                calc |(q.2 : ℝ) - (q'.2 : ℝ)| ≤ max (|(q.1 : ℝ) - (q'.1 : ℝ)|) (|(q.2 : ℝ) - (q'.2 : ℝ)|) := le_max_right _ _
                  _ < 1 := h3
              have h8 : q.1 = q'.1 := by
                by_contra h
                have h11 : (1 : ℝ) ≤ |((q.1 : ℝ) - (q'.1 : ℝ))| := by
                  by_cases h12 : q.1 ≤ q'.1
                  · have h13 : q.1 < q'.1 := by omega
                    have h14 : (q'.1 - q.1 : ℤ) ≥ 1 := by omega
                    have h15 : (1 : ℝ) ≤ (q'.1 : ℝ) - (q.1 : ℝ) := by exact_mod_cast h14
                    have h16 : |((q.1 : ℝ) - (q'.1 : ℝ))| = (q'.1 : ℝ) - (q.1 : ℝ) := by
                      rw [abs_of_nonpos] <;> linarith
                    rw [h16]; linarith
                  · have h13 : q.1 > q'.1 := by omega
                    have h14 : (q.1 - q'.1 : ℤ) ≥ 1 := by omega
                    have h15 : (1 : ℝ) ≤ (q.1 : ℝ) - (q'.1 : ℝ) := by exact_mod_cast h14
                    have h16 : |((q.1 : ℝ) - (q'.1 : ℝ))| = (q.1 : ℝ) - (q'.1 : ℝ) := by
                      rw [abs_of_nonneg] <;> linarith
                    rw [h16]; linarith
                linarith
              have h9 : q.2 = q'.2 := by
                by_contra h
                have h11 : (1 : ℝ) ≤ |((q.2 : ℝ) - (q'.2 : ℝ))| := by
                  by_cases h12 : q.2 ≤ q'.2
                  · have h13 : q.2 < q'.2 := by omega
                    have h14 : (q'.2 - q.2 : ℤ) ≥ 1 := by omega
                    have h15 : (1 : ℝ) ≤ (q'.2 : ℝ) - (q.2 : ℝ) := by exact_mod_cast h14
                    have h16 : |((q.2 : ℝ) - (q'.2 : ℝ))| = (q'.2 : ℝ) - (q.2 : ℝ) := by
                      rw [abs_of_nonpos] <;> linarith
                    rw [h16]; linarith
                  · have h13 : q.2 > q'.2 := by omega
                    have h14 : (q.2 - q'.2 : ℤ) ≥ 1 := by omega
                    have h15 : (1 : ℝ) ≤ (q.2 : ℝ) - (q'.2 : ℝ) := by exact_mod_cast h14
                    have h16 : |((q.2 : ℝ) - (q'.2 : ℝ))| = (q.2 : ℝ) - (q'.2 : ℝ) := by
                      rw [abs_of_nonneg] <;> linarith
                    rw [h16]; linarith
                linarith
              exact Prod.ext h8.symm h9.symm
            exact h4
          have h_sub : (d.Q0.filter fun q' => dist q q' ≤ r) ⊆ {q} := by
            intro q' hq'
            exact Finset.mem_singleton.mpr (h1 q' hq')
          have h_card : (d.Q0.filter fun q' => dist q q' ≤ r).card ≤ ({q} : Finset (CoarseSquare Δ)).card :=
            Finset.card_le_card h_sub
          simpa using h_card
        have h_pos : 0 ≤ d.A_idx * Real.rpow r d.u := by
          exact mul_nonneg d.hA_idx_nonneg (Real.rpow_nonneg (by linarith) d.u)
        have h : ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 := by exact_mod_cast h_filter_le_one
        linarith
      · -- r ≥ 1
        have h_ge_one : 1 ≤ r := by linarith
        have h_radius_ge : Δ ≤ Real.sqrt 2 * Δ * r := by
          have h1 : 0 < Δ := hΔ_pos
          have h2 : 1 ≤ Real.sqrt 2 * r := by
            have h3 : 1 ≤ Real.sqrt 2 := by
              have h4 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
              have h5 : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h4
              have h6 : Real.sqrt 1 = 1 := Real.sqrt_one
              linarith
            nlinarith
          nlinarith
        have h_phys : ((d.Q0_phys.filter fun c' => dist c c' ≤ Real.sqrt 2 * Δ * r).card : ℝ) ≤
            1 + d.A_phys * Real.rpow (Real.sqrt 2 * Δ * r) d.u :=
          d.h_growth_phys c hc (Real.sqrt 2 * Δ * r) h_radius_ge
        have h7 : Real.rpow (Real.sqrt 2 * Δ * r) d.u = Real.rpow (Real.sqrt 2 * Δ) d.u * Real.rpow r d.u := by
          have h_nonneg1 : 0 ≤ Real.sqrt 2 * Δ := by positivity
          have h_nonneg2 : 0 ≤ r := by linarith
          have h_eq : Real.sqrt 2 * Δ * r = (Real.sqrt 2 * Δ) * r := by ring
          rw [h_eq]
          have h : ((Real.sqrt 2 * Δ) * r)^d.u = (Real.sqrt 2 * Δ)^d.u * r^d.u := Real.mul_rpow h_nonneg1 h_nonneg2
          exact h
        have h4' : ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ ((d.Q0_phys.filter fun c' => dist c c' ≤ Real.sqrt 2 * Δ * r).card : ℝ) := by
          exact_mod_cast h4
        rw [h7] at h_phys
        have h9 : 1 + d.A_phys * (Real.rpow (Real.sqrt 2 * Δ) d.u * Real.rpow r d.u) = 1 + d.A_idx * Real.rpow r d.u := by
          have h10 : Real.rpow (Real.sqrt 2 * Δ) d.u = (Real.sqrt 2 * Δ)^d.u := by rfl
          rw [d.hA_idx_def, h10] <;> ring
        rw [h9] at h_phys
        exact h4'.trans h_phys
    exact h6
  have h_pointEnergy : ∀ q ∈ d.Q0, pointEnergy d.u d.Q0 q ≤ d.A_idx := by
    intro q hq
    let c := squareCenter Δ q
    have hc : c ∈ d.Q0_phys := by
      rw [←d.hQ0_phys_eq]; exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h1 : pointEnergy d.u d.Q0 q ≤ pointEnergy d.u d.Q0_phys c * (Real.sqrt 2 * Δ)^d.u := by
      have h_image : (d.Q0.erase q).image (squareCenter Δ) = d.Q0_phys.erase c := by
        rw [←d.hQ0_phys_eq, Finset.image_erase d.h_inj]
      have h_sum : ∑ y ∈ d.Q0.erase q, Real.rpow (dist q y) (-d.u) ≤
          (Real.sqrt 2 * Δ)^d.u * ∑ z ∈ d.Q0_phys.erase c, Real.rpow (dist c z) (-d.u) := by
        have h3 : ∀ y ∈ d.Q0.erase q, Real.rpow (dist q y) (-d.u) ≤
            (Real.sqrt 2 * Δ)^d.u * Real.rpow (dist c (squareCenter Δ y)) (-d.u) := by
          intro y _
          have h4 : dist c (squareCenter Δ y) ≤ Real.sqrt 2 * Δ * dist q y :=
            squareCenter_dist_upper hΔ_pos q y
          have h5 : 0 < dist q y := by
            have h6 : y ≠ q := Finset.mem_erase.mp ‹y ∈ d.Q0.erase q› |>.1
            exact dist_pos.mpr (Ne.symm h6)
          have h7 : 0 < dist c (squareCenter Δ y) := by
            have h8 : squareCenter Δ y ≠ c := by
              intro h9; have h10 := d.h_inj h9; exact (Finset.mem_erase.mp ‹y ∈ d.Q0.erase q›).1 h10
            exact dist_pos.mpr (Ne.symm h8)
          have h10 : 0 < Real.sqrt 2 * Δ := by positivity
          have h11 : dist c (squareCenter Δ y) / (Real.sqrt 2 * Δ) ≤ dist q y := by
            calc dist c (squareCenter Δ y) / (Real.sqrt 2 * Δ)
              ≤ (Real.sqrt 2 * Δ * dist q y) / (Real.sqrt 2 * Δ) := by gcongr
            _ = dist q y := by field_simp [h10.ne'] <;> ring
          have h_neg_d_u : -d.u ≤ 0 := by linarith [d.hu_pos]
          have h12_pos : 0 < dist c (squareCenter Δ y) / (Real.sqrt 2 * Δ) := by positivity
          have h13 : Real.rpow (dist q y) (-d.u) ≤
              Real.rpow (dist c (squareCenter Δ y) / (Real.sqrt 2 * Δ)) (-d.u) :=
            Real.rpow_le_rpow_of_nonpos h12_pos h11 h_neg_d_u
          have h14 : Real.rpow (dist c (squareCenter Δ y) / (Real.sqrt 2 * Δ)) (-d.u) =
              (Real.sqrt 2 * Δ)^d.u * Real.rpow (dist c (squareCenter Δ y)) (-d.u) := by
            have h15 : Real.rpow (dist c (squareCenter Δ y) / (Real.sqrt 2 * Δ)) (-d.u) =
                Real.rpow (dist c (squareCenter Δ y)) (-d.u) / Real.rpow (Real.sqrt 2 * Δ) (-d.u) :=
              Real.div_rpow (by positivity) (by positivity) (-d.u)
            rw [h15]
            have h16 : Real.rpow (Real.sqrt 2 * Δ) (-d.u) = ((Real.sqrt 2 * Δ)^d.u)⁻¹ := by
              set x := Real.sqrt 2 * Δ with hx
              have hx_nonneg : 0 ≤ x := by positivity
              have hx_pos : 0 < x := by positivity
              have h_mul : x ^ (-d.u) * x ^ d.u = 1 := by
                rw [← Real.rpow_add hx_pos (-d.u) d.u]
                have h_sum : (-d.u) + d.u = 0 := by ring
                rw [h_sum, Real.rpow_zero]
              have h_pos2 : 0 < x ^ d.u := Real.rpow_pos_of_pos hx_pos d.u
              have h_eq : x ^ (-d.u) = (x ^ d.u)⁻¹ := eq_inv_of_mul_eq_one_left h_mul
              simpa [hx] using h_eq
            rw [h16]
            have h_pos : 0 < (Real.sqrt 2 * Δ)^d.u := by positivity
            field_simp [h_pos.ne'] <;> ring
          rw [h14] at h13; exact h13
        calc ∑ y ∈ d.Q0.erase q, Real.rpow (dist q y) (-d.u)
          ≤ ∑ y ∈ d.Q0.erase q, (Real.sqrt 2 * Δ)^d.u * Real.rpow (dist c (squareCenter Δ y)) (-d.u) :=
            Finset.sum_le_sum h3
        _ = (Real.sqrt 2 * Δ)^d.u * ∑ y ∈ d.Q0.erase q, Real.rpow (dist c (squareCenter Δ y)) (-d.u) := by
          rw [Finset.mul_sum]
        _ = (Real.sqrt 2 * Δ)^d.u * ∑ z ∈ (d.Q0.erase q).image (squareCenter Δ), Real.rpow (dist c z) (-d.u) := by
          rw [Finset.sum_image (fun x _ y _ h => d.h_inj h)] <;> rfl
        _ = (Real.sqrt 2 * Δ)^d.u * ∑ z ∈ d.Q0_phys.erase c, Real.rpow (dist c z) (-d.u) := by
          rw [h_image]
      have h_pe1 : pointEnergy d.u d.Q0 q = ∑ y ∈ d.Q0.erase q, Real.rpow (dist q y) (-d.u) := by rfl
      have h_pe2 : pointEnergy d.u d.Q0_phys c = ∑ z ∈ d.Q0_phys.erase c, Real.rpow (dist c z) (-d.u) := by rfl
      rw [h_pe1, h_pe2]
      have h_comm : (Real.sqrt 2 * Δ)^d.u * ∑ z ∈ d.Q0_phys.erase c, Real.rpow (dist c z) (-d.u) =
          (∑ z ∈ d.Q0_phys.erase c, Real.rpow (dist c z) (-d.u)) * (Real.sqrt 2 * Δ)^d.u := by ring
      rw [h_comm] at h_sum
      exact h_sum
    have h2 : pointEnergy d.u d.Q0_phys c ≤ d.A_phys := d.hPE_bound c hc
    calc pointEnergy d.u d.Q0 q
      ≤ pointEnergy d.u d.Q0_phys c * (Real.sqrt 2 * Δ)^d.u := h1
    _ ≤ d.A_phys * (Real.sqrt 2 * Δ)^d.u := by gcongr
    _ = d.A_idx := by
      exact d.hA_idx_def.symm
  exact ⟨h_growth_idx, h_pointEnergy⟩

/-- Phase 4: Index S-set constant bound. -/
lemma a7_index_sset {Δ δ s t ε : ℝ} {a5 : A5_Output Δ δ s t ε}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (h_small2 : 4 + 16 * (2 : ℝ)^(t - s) ≤ Real.rpow Δ (-4 * ε))
    (h_absorb : (6500 : ℝ) ≤ Real.rpow Δ (-ε))
    (d : A7_ExtractionResult Δ δ s t ε a5)
    (h_growth_idx : ∀ q ∈ d.Q0, ∀ r : ℝ, Δ ≤ r →
      ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + d.A_idx * Real.rpow r d.u) :
    d.A_idx ≤ 16 * (Real.sqrt 2)^d.u * Real.rpow Δ (-300 * ε) ∧
    IsDeltaSSet Δ d.u (Real.rpow Δ (-389 * ε)) (d.Q0 : Set (CoarseSquare Δ)) := by
  classical
  let N : ℝ := (d.Q0.card : ℝ)
  have hN_pos : 0 < N := by
    have h_card_Q0 : (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) ≤ (d.Q0.card : ℝ) := by
      rw [d.hQ0_card_eq]; exact d.h_card_lower
    have h4 : 0 < (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ_pos _)
    exact lt_of_lt_of_le h4 h_card_Q0
  have hN_lower : N ≥ (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) := by
    dsimp only [N]
    rw [d.hQ0_card_eq]
    exact d.h_card_lower
  have hNcover_lower : ENNReal.ofReal N ≤ Phase2.Ncover Δ (d.Q0 : Set (CoarseSquare Δ)) := by
    rw [ncover_coarse_eq_card hΔ_pos hΔ_lt_half] <;> simp [N]
  have h_raw_sset : IsDeltaSSet Δ d.u ((Real.rpow Δ (-d.u) + d.A_idx * (2 : ℝ)^d.u) / N) (d.Q0 : Set (CoarseSquare Δ)) :=
    ball_growth_to_sset_with_lower_bound hΔ_pos d.hu_pos d.hA_idx_nonneg hN_pos d.hQ0_nonempty hNcover_lower h_growth_idx
  have hA_idx_bound : d.A_idx ≤ 16 * (Real.sqrt 2)^d.u * Real.rpow Δ (-300 * ε) := by
    rw [d.hA_idx_def]
    have h1 : d.A_phys ≤ 16 * Real.rpow Δ (-d.u - 300 * ε) := d.hA_bound
    have h2 : (Real.sqrt 2 * Δ)^d.u = (Real.sqrt 2)^d.u * Real.rpow Δ d.u := by
      have h_nonneg1 : 0 ≤ Real.sqrt 2 := by positivity
      have h_nonneg2 : 0 ≤ Δ := by positivity
      exact Real.mul_rpow h_nonneg1 h_nonneg2
    have h4 : Real.rpow Δ d.u * Real.rpow Δ (-d.u - 300 * ε) = Real.rpow Δ (-300 * ε) := by
      have h5 := Real.rpow_add hΔ_pos d.u (-d.u - 300 * ε)
      have h6 : d.u + (-d.u - 300 * ε) = -300 * ε := by ring
      rw [h6] at h5
      exact h5.symm
    have h_sqrt2_nonneg : 0 ≤ Real.sqrt 2 := by positivity
    have h1_pos : 0 ≤ (Real.sqrt 2)^d.u := Real.rpow_nonneg h_sqrt2_nonneg d.u
    have h2_pos : 0 ≤ Real.rpow Δ d.u := Real.rpow_nonneg hΔ_pos.le d.u
    have h_pos_mul : 0 ≤ (Real.sqrt 2)^d.u * Real.rpow Δ d.u := mul_nonneg h1_pos h2_pos
    calc d.A_phys * (Real.sqrt 2 * Δ)^d.u
      = (Real.sqrt 2 * Δ)^d.u * d.A_phys := by ring
    _ = (Real.sqrt 2)^d.u * Real.rpow Δ d.u * d.A_phys := by rw [h2] <;> ring
    _ ≤ (Real.sqrt 2)^d.u * Real.rpow Δ d.u * (16 * Real.rpow Δ (-d.u - 300 * ε)) := by
      exact mul_le_mul_of_nonneg_left h1 h_pos_mul
    _ = 16 * (Real.sqrt 2)^d.u * (Real.rpow Δ d.u * Real.rpow Δ (-d.u - 300 * ε)) := by ring
    _ = 16 * (Real.sqrt 2)^d.u * Real.rpow Δ (-300 * ε) := by rw [h4]
  have h_u_lt_2 : d.u < 2 := d.hu_lt_two
  have h_u_le_2 : d.u ≤ 2 := h_u_lt_2.le
  have h2u_le_4 : (2 : ℝ)^d.u ≤ 4 := by
    have h : (2 : ℝ)^d.u ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h_u_le_2
    have h2 : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
    linarith
  have h_sqrt2_u_le_2 : (Real.sqrt 2)^d.u ≤ 2 := by
    have h_base : 1 ≤ Real.sqrt 2 := by
      have h4 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h5 : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h4
      have h6 : Real.sqrt 1 = 1 := Real.sqrt_one
      linarith
    have h1 : (Real.sqrt 2)^d.u ≤ (Real.sqrt 2)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h_base h_u_le_2
    have h2 : (Real.sqrt 2)^(2 : ℝ) = 2 := by
      have h3 : (Real.sqrt 2)^(2 : ℝ) = (Real.sqrt 2) ^ (2 : ℕ) := by norm_cast
      rw [h3]
      have h4 : (Real.sqrt 2) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      exact h4
    linarith
  have h_sset_constant : (Real.rpow Δ (-d.u) + d.A_idx * (2 : ℝ)^d.u) / N ≤ Real.rpow Δ (-389 * ε) := by
    have h2u_pos : 0 ≤ (2 : ℝ)^d.u := by positivity
    have h_num : Real.rpow Δ (-d.u) + d.A_idx * (2 : ℝ)^d.u ≤
        Real.rpow Δ (-d.u) + 16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε) := by
      have hA_mul : d.A_idx * (2 : ℝ)^d.u ≤ (16 * (Real.sqrt 2)^d.u * Real.rpow Δ (-300 * ε)) * (2 : ℝ)^d.u :=
        mul_le_mul_of_nonneg_right hA_idx_bound h2u_pos
      have h_final : (16 * (Real.sqrt 2)^d.u * Real.rpow Δ (-300 * ε)) * (2 : ℝ)^d.u =
          16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε) := by ring
      rw [h_final] at hA_mul
      exact add_le_add le_rfl hA_mul
    have h_denom : N ≥ (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) := hN_lower
    have h_pos_num : 0 ≤ Real.rpow Δ (-d.u) + d.A_idx * (2 : ℝ)^d.u := by
      have h1 : 0 ≤ Real.rpow Δ (-d.u) := Real.rpow_nonneg hΔ_pos.le _
      have h2 : 0 ≤ d.A_idx * (2 : ℝ)^d.u := mul_nonneg d.hA_idx_nonneg (by positivity)
      exact add_nonneg h1 h2
    have h_pos_denom : 0 < (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) :=
      mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ_pos _)
    have h_div : (Real.rpow Δ (-d.u) + d.A_idx * (2 : ℝ)^d.u) / N ≤
        (Real.rpow Δ (-d.u) + 16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε)) /
          ((1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)) := by
      let b := Real.rpow Δ (-d.u) + 16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε)
      have h_b_nonneg : 0 ≤ b := by
        dsimp only [b]
        have h1 : 0 ≤ Real.rpow Δ (-d.u) := Real.rpow_nonneg hΔ_pos.le (-d.u)
        have h_sqrt2_nonneg : 0 ≤ Real.sqrt 2 := by positivity
        have h2 : 0 ≤ (Real.sqrt 2)^d.u := Real.rpow_nonneg h_sqrt2_nonneg d.u
        have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
        have h3 : 0 ≤ (2 : ℝ)^d.u := Real.rpow_nonneg h2_nonneg d.u
        have h4 : 0 ≤ Real.rpow Δ (-300 * ε) := Real.rpow_nonneg hΔ_pos.le (-300 * ε)
        have h5 : 0 ≤ 16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε) := by
          positivity
        exact add_nonneg h1 h5
      have h1 : (Real.rpow Δ (-d.u) + d.A_idx * (2 : ℝ)^d.u) / N ≤ b / N :=
        div_le_div_of_nonneg_right h_num hN_pos.le
      have h2 : b / N ≤ b / ((1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)) :=
        div_le_div_of_nonneg_left h_b_nonneg h_pos_denom h_denom
      exact h1.trans h2
    have h_expand : (Real.rpow Δ (-d.u) + 16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε)) /
        ((1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)) =
        4 * Real.rpow Δ (-76 * ε) + 64 * (Real.sqrt 2 * 2 : ℝ)^d.u * Real.rpow Δ (d.u - 376 * ε) := by
      have h_pos1 : 0 < Real.rpow Δ (-d.u + 76 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h1 : Real.rpow Δ (-d.u) / Real.rpow Δ (-d.u + 76 * ε) = Real.rpow Δ (-76 * ε) := by
        have h_div := rpow_sub_eq hΔ_pos (-d.u) (-d.u + 76 * ε)
        have h_exp : (-d.u) - (-d.u + 76 * ε) = -76 * ε := by ring
        rw [h_div.symm, h_exp]
      have h2 : Real.rpow Δ (-300 * ε) / Real.rpow Δ (-d.u + 76 * ε) = Real.rpow Δ (d.u - 376 * ε) := by
        have h_div := rpow_sub_eq hΔ_pos (-300 * ε) (-d.u + 76 * ε)
        have h_exp : (-300 * ε) - (-d.u + 76 * ε) = d.u - 376 * ε := by ring
        rw [h_div.symm, h_exp]
      have h3 : (Real.sqrt 2)^d.u * (2 : ℝ)^d.u = (Real.sqrt 2 * 2 : ℝ)^d.u := by
        rw [←Real.mul_rpow (by positivity) (by positivity)] <;> ring
      have h_main : (Real.rpow Δ (-d.u) + 16 * (Real.sqrt 2)^d.u * (2 : ℝ)^d.u * Real.rpow Δ (-300 * ε)) /
          ((1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)) =
          4 * (Real.rpow Δ (-d.u) / Real.rpow Δ (-d.u + 76 * ε)) +
          64 * ((Real.sqrt 2)^d.u * (2 : ℝ)^d.u) * (Real.rpow Δ (-300 * ε) / Real.rpow Δ (-d.u + 76 * ε)) := by
        field_simp [h_pos1.ne'] <;> ring
      rw [h_main, h1, h2, h3] <;> ring
    rw [h_expand] at h_div
    have h3 : 4 * Real.rpow Δ (-76 * ε) + 64 * (Real.sqrt 2 * 2 : ℝ)^d.u * Real.rpow Δ (d.u - 376 * ε) ≤
        Real.rpow Δ (-389 * ε) := by
      have h_sqrt2_2_u_le_8 : (Real.sqrt 2 * 2 : ℝ)^d.u ≤ 8 := by
        have h1 : (Real.sqrt 2 * 2 : ℝ)^d.u ≤ (Real.sqrt 2 * 2 : ℝ)^(2 : ℝ) := by
          have h_base : 1 ≤ (Real.sqrt 2 * 2 : ℝ) := by
            have h1 : 1 ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
            have h4 : Real.sqrt 2 * 2 ≥ 2 := by linarith
            linarith
          exact Real.rpow_le_rpow_of_exponent_le h_base h_u_le_2
        have h2 : (Real.sqrt 2 * 2 : ℝ)^(2 : ℝ) = 8 := by
          have h_pos : 0 ≤ Real.sqrt 2 * 2 := by positivity
          have h_rpow : (Real.sqrt 2 * 2 : ℝ)^(2 : ℝ) = (Real.sqrt 2 * 2)^2 := by
            rw [Real.rpow_two]
          rw [h_rpow]
          have h_sq : (Real.sqrt 2 * 2)^2 = 8 := by
            have h : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
            nlinarith
          exact h_sq
        linarith
      have h4 : 64 * (Real.sqrt 2 * 2 : ℝ)^d.u * Real.rpow Δ (d.u - 376 * ε) ≤
          512 * Real.rpow Δ (-376 * ε) := by
        have h5 : (Real.sqrt 2 * 2 : ℝ)^d.u ≤ 8 := h_sqrt2_2_u_le_8
        have h6 : Real.rpow Δ (d.u - 376 * ε) ≤ Real.rpow Δ (-376 * ε) := by
          apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos
          · linarith [d.hu_pos]
          · linarith [d.hu_pos]
        have h_rpow_nonneg : 0 ≤ Real.rpow Δ (d.u - 376 * ε) := Real.rpow_nonneg hΔ_pos.le _
        calc 64 * (Real.sqrt 2 * 2 : ℝ)^d.u * Real.rpow Δ (d.u - 376 * ε)
          ≤ 64 * 8 * Real.rpow Δ (d.u - 376 * ε) := by gcongr <;> exact h_rpow_nonneg
        _ = 512 * Real.rpow Δ (d.u - 376 * ε) := by ring
        _ ≤ 512 * Real.rpow Δ (-376 * ε) := by gcongr <;> exact h_rpow_nonneg
      have h7 : 4 * Real.rpow Δ (-76 * ε) ≤ 4 * Real.rpow Δ (-376 * ε) := by
        gcongr
        apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos
        · linarith [hε_pos]
        · linarith [hε_pos]
      have h8 : 4 * Real.rpow Δ (-76 * ε) + 64 * (Real.sqrt 2 * 2 : ℝ)^d.u * Real.rpow Δ (d.u - 376 * ε) ≤
          516 * Real.rpow Δ (-376 * ε) := by linarith
      have h9 : 516 * Real.rpow Δ (-376 * ε) ≤ Real.rpow Δ (-389 * ε) := by
        have h10 : (516 : ℝ) ≤ Real.rpow Δ (-ε) := by
          have h11 : (6500 : ℝ) ≤ Real.rpow Δ (-ε) := h_absorb
          linarith
        have h12 : 516 * Real.rpow Δ (-376 * ε) ≤
            Real.rpow Δ (-ε) * Real.rpow Δ (-376 * ε) := by
          gcongr <;> exact Real.rpow_nonneg hΔ_pos.le _
        have h13 : Real.rpow Δ (-ε) * Real.rpow Δ (-376 * ε) = Real.rpow Δ (-377 * ε) := by
          have h_mul := Real.rpow_add hΔ_pos (-ε) (-376 * ε)
          have h_sum : (-ε) + (-376 * ε) = -377 * ε := by ring
          rw [h_sum] at h_mul; exact h_mul.symm
        rw [h13] at h12
        have h14 : Real.rpow Δ (-377 * ε) ≤ Real.rpow Δ (-389 * ε) := by
          apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos
          · linarith [hε_pos]
          · linarith [hε_pos]
        exact h12.trans h14
      exact h8.trans h9
    exact h_div.trans h3
  have hQ0_sset : IsDeltaSSet Δ d.u (Real.rpow Δ (-389 * ε)) (d.Q0 : Set (CoarseSquare Δ)) :=
    IsDeltaSSet.mono_const h_raw_sset h_sset_constant
  exact ⟨hA_idx_bound, hQ0_sset⟩

/-- Phase 5: Physical S-set for Q0_phys. -/
lemma a7_physical_sset {Δ δ s t ε : ℝ} {a5 : A5_Output Δ δ s t ε}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (h_absorb : (6500 : ℝ) ≤ Real.rpow Δ (-ε))
    (d : A7_ExtractionResult Δ δ s t ε a5) :
    IsDeltaSSet Δ d.u (Real.rpow Δ (-377 * ε)) (d.Q0_phys : Set Plane) := by
  classical
  have h_u_lt_2 : d.u < 2 := by
    rw [d.hu_eq] <;> linarith
  have h_u_le_2 : d.u ≤ 2 := h_u_lt_2.le
  have hQ0_phys_nonempty : d.Q0_phys.Nonempty := by
    have h_pos : 0 < (d.Q0_phys.card : ℝ) := by
      have h4 : 0 < (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ_pos _)
      exact lt_of_lt_of_le h4 d.h_card_lower
    exact Finset.card_pos.mp (by exact_mod_cast h_pos)
  have h_sep_phys : SeparatedAt Δ (d.Q0_phys : Set Plane) := by
    exact fun x hx y hy hne => d.hQsep (d.hQ0_sub_centers hx) (d.hQ0_sub_centers hy) hne
  have h_cover_lower_phys : (d.Q0_phys.card : ENNReal) ≤
      25 * Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) :=
    separated_card_le_25_mul_covering_nonstrict hΔ_pos h_sep_phys
  let N_phys : ℝ := (1 / 100 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)
  have hN_phys_pos : 0 < N_phys := mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ_pos _)
  have hN_phys_lower : ENNReal.ofReal N_phys ≤ Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) := by
    have h2 : (N_phys : ℝ) ≤ (d.Q0_phys.card : ℝ) / 25 := by
      dsimp only [N_phys]
      have h3 : (1 / 4 : ℝ) * Real.rpow Δ (-d.u + 76 * ε) ≤ (d.Q0_phys.card : ℝ) := d.h_card_lower
      have h4 : Real.rpow Δ (-d.u + 76 * ε) ≤ 4 * (d.Q0_phys.card : ℝ) := by linarith
      calc (1 / 100 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)
        ≤ (1 / 100 : ℝ) * (4 * (d.Q0_phys.card : ℝ)) := by gcongr
      _ = (d.Q0_phys.card : ℝ) / 25 := by ring
    have h_pos25 : (0 : ℝ) < 25 := by norm_num
    have h3 : ENNReal.ofReal ((d.Q0_phys.card : ℝ) / 25) =
        ENNReal.ofReal (d.Q0_phys.card : ℝ) / ENNReal.ofReal (25 : ℝ) :=
      ENNReal.ofReal_div_of_pos h_pos25
    have h4 : ENNReal.ofReal (25 : ℝ) = (25 : ENNReal) := by norm_cast
    have h5 : ENNReal.ofReal (d.Q0_phys.card : ℝ) = (d.Q0_phys.card : ENNReal) := by norm_cast
    have h6 : ENNReal.ofReal ((d.Q0_phys.card : ℝ) / 25) = (d.Q0_phys.card : ENNReal) / 25 := by
      rw [h3, h4, h5]
    have h7 : ENNReal.ofReal N_phys ≤ ENNReal.ofReal ((d.Q0_phys.card : ℝ) / 25) :=
      ENNReal.ofReal_le_ofReal h2
    rw [h6] at h7
    have h8 : (d.Q0_phys.card : ENNReal) ≤ 25 * Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) :=
      h_cover_lower_phys
    calc ENNReal.ofReal N_phys
      ≤ (d.Q0_phys.card : ENNReal) / 25 := h7
    _ ≤ (25 * Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane)) / 25 := by gcongr
    _ = Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) := by
      have h25_ne_zero : (25 : ENNReal) ≠ 0 := by norm_num
      have h25_ne_top : (25 : ENNReal) ≠ ⊤ := by norm_num
      have h_comm : (25 : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) =
          Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) * (25 : ENNReal) := by
        apply mul_comm
      rw [h_comm]
      have h_cancel : Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) * (25 : ENNReal) / (25 : ENNReal) =
          Metric.externalCoveringNumber Δ.toNNReal (d.Q0_phys : Set Plane) :=
        ENNReal.mul_div_cancel_right h25_ne_zero h25_ne_top
      exact h_cancel
  let A'_phys : ℝ := 16 * Real.rpow Δ (-d.u - 300 * ε)
  have hA'_phys_nonneg : 0 ≤ A'_phys := by
    dsimp only [A'_phys]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hΔ_pos.le _)
  have h_growth_phys' : ∀ q ∈ d.Q0_phys, ∀ r : ℝ, Δ ≤ r →
      ((d.Q0_phys.filter fun q' => dist q q' ≤ r).card : ℝ) ≤
        1 + A'_phys * Real.rpow r d.u := by
    intro q hq r hr
    have h := d.h_growth_phys q hq r hr
    have h_pos : 0 ≤ Real.rpow r d.u := Real.rpow_nonneg (by linarith) d.u
    have hA_le : d.A_phys ≤ A'_phys := by
      dsimp only [A'_phys]; exact d.hA_bound
    calc _ ≤ 1 + d.A_phys * Real.rpow r d.u := h
       _ ≤ 1 + A'_phys * Real.rpow r d.u := by
         have h_mul : d.A_phys * Real.rpow r d.u ≤ A'_phys * Real.rpow r d.u :=
           mul_le_mul_of_nonneg_right hA_le h_pos
         linarith
  let C_phys : ℝ := (Real.rpow Δ (-d.u) + A'_phys * (2 : ℝ)^d.u) / N_phys
  have h_sset_phys : IsDeltaSSet Δ d.u C_phys (d.Q0_phys : Set Plane) :=
    ball_growth_to_sset_with_lower_bound hΔ_pos d.hu_pos hA'_phys_nonneg hN_phys_pos hQ0_phys_nonempty
      hN_phys_lower h_growth_phys'
  have hC_phys_le6500 : C_phys ≤ 6500 * Real.rpow Δ (-376 * ε) := by
    dsimp only [C_phys, N_phys, A'_phys]
    have h_expand : (Real.rpow Δ (-d.u) + (16 * Real.rpow Δ (-d.u - 300 * ε)) * (2 : ℝ)^d.u) /
        ((1 / 100 : ℝ) * Real.rpow Δ (-d.u + 76 * ε)) =
        100 * (Real.rpow Δ (-76 * ε) + (16 * (2 : ℝ)^d.u) * Real.rpow Δ (-376 * ε)) := by
      have h_pos1 : 0 < Real.rpow Δ (-d.u + 76 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h1 : Real.rpow Δ (-d.u) / Real.rpow Δ (-d.u + 76 * ε) = Real.rpow Δ (-76 * ε) := by
        have h_div := rpow_sub_eq hΔ_pos (-d.u) (-d.u + 76 * ε)
        have h_exp : (-d.u) - (-d.u + 76 * ε) = -76 * ε := by ring
        rw [h_div.symm, h_exp]
      have h2 : Real.rpow Δ (-d.u - 300 * ε) / Real.rpow Δ (-d.u + 76 * ε) =
          Real.rpow Δ (-376 * ε) := by
        have h_div := rpow_sub_eq hΔ_pos (-d.u - 300 * ε) (-d.u + 76 * ε)
        have h_exp : (-d.u - 300 * ε) - (-d.u + 76 * ε) = -376 * ε := by ring
        rw [h_div.symm, h_exp]
      let D0 := Real.rpow Δ (-d.u + 76 * ε)
      have h_main : (Real.rpow Δ (-d.u) + (16 * Real.rpow Δ (-d.u - 300 * ε)) * (2 : ℝ)^d.u) /
          ((1 / 100 : ℝ) * D0) =
          100 * (Real.rpow Δ (-d.u) / D0 + (16 * (2 : ℝ)^d.u) * (Real.rpow Δ (-d.u - 300 * ε) / D0)) := by
        dsimp only [D0]
        field_simp [h_pos1.ne'] <;> ring
      rw [h_main, h1, h2] <;> ring
    rw [h_expand]
    have h3 : Real.rpow Δ (-76 * ε) ≤ Real.rpow Δ (-376 * ε) := by
      have h_exp : -376 * ε ≤ -76 * ε := by linarith [hε_pos]
      exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith [hε_pos]) h_exp
    have h4 : (16 * (2 : ℝ)^d.u) ≤ 64 := by
      have h : (2 : ℝ)^d.u ≤ 4 := by
        have h' : (2 : ℝ)^d.u ≤ (2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h_u_le_2
        have h'' : (2 : ℝ)^(2 : ℝ) = 4 := by norm_num
        linarith
      linarith
    have h5 : (16 * (2 : ℝ)^d.u) * Real.rpow Δ (-376 * ε) ≤ 64 * Real.rpow Δ (-376 * ε) := by
      gcongr
      <;> exact Real.rpow_nonneg hΔ_pos.le _
    have h6 : Real.rpow Δ (-76 * ε) + (16 * (2 : ℝ)^d.u) * Real.rpow Δ (-376 * ε) ≤
        65 * Real.rpow Δ (-376 * ε) := by
      have h7 : Real.rpow Δ (-76 * ε) ≤ Real.rpow Δ (-376 * ε) := h3
      linarith
    have h8 : 100 * (Real.rpow Δ (-76 * ε) + (16 * (2 : ℝ)^d.u) * Real.rpow Δ (-376 * ε)) ≤
        6500 * Real.rpow Δ (-376 * ε) := by
      calc _ ≤ 100 * (65 * Real.rpow Δ (-376 * ε)) := by gcongr
       _ = 6500 * Real.rpow Δ (-376 * ε) := by ring
    exact h8
  have hC_phys_final : C_phys ≤ Real.rpow Δ (-377 * ε) := by
    have h1 : C_phys ≤ 6500 * Real.rpow Δ (-376 * ε) := hC_phys_le6500
    have h2 : 6500 * Real.rpow Δ (-376 * ε) ≤
        Real.rpow Δ (-ε) * Real.rpow Δ (-376 * ε) := by
      have h3 : (6500 : ℝ) ≤ Real.rpow Δ (-ε) := h_absorb
      gcongr <;> exact Real.rpow_nonneg (by linarith) _
    have h4 : Real.rpow Δ (-ε) * Real.rpow Δ (-376 * ε) = Real.rpow Δ (-377 * ε) := by
      have h_mul : Real.rpow Δ ((-ε) + (-376 * ε)) = Real.rpow Δ (-ε) * Real.rpow Δ (-376 * ε) := Real.rpow_add hΔ_pos (-ε) (-376 * ε)
      have h_sum : (-ε) + (-376 * ε) = -377 * ε := by ring
      rw [h_sum] at h_mul
      exact h_mul.symm
    rw [h4] at h2
    exact le_trans h1 h2
  exact IsDeltaSSet.mono_const h_sset_phys hC_phys_final

/-- Main lemma: assemble all phases into A7_Output. -/
lemma A7_physical_full_output_main
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (a5 : A5_Output Δ δ s t ε)
    (hQset_bdd : ∀ p ∈ a5.Qset.image (squareCenter Δ), ‖p‖ ≤ 2)
    (hQset_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ a5.Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ a5.Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3)
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    (h_pack_absorb : (affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb : (affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^t + 1 ≤ Real.rpow Δ (-ε))
    (h_small_half : Real.rpow Δ ε ≤ 1 / 2)
    (h_small2 : 4 + 16 * (2 : ℝ)^(t - s) ≤ Real.rpow Δ (-4 * ε))
    (h_absorb : (6500 : ℝ) ≤ Real.rpow Δ (-ε))
    (h_slope_bound : ∀ T ∈ a5.C_global,
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3) :
    Nonempty (A7_Output Δ δ s t ε) := by
  classical
  let d := a7_extraction hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos
    hδ_pos hδ_le_Δ a5
    hQset_bdd hQset_le_3 h_log_absorb h_pack_absorb h_const_absorb h_small_half
  have ⟨h_growth_idx, h_pointEnergy⟩ := a7_index_growth_and_energy hΔ_pos d
  have ⟨hA_idx_bound, hQ0_sset⟩ := a7_index_sset hΔ_pos hΔ_lt_half hs hst ht2 hε_pos h_small2 h_absorb d h_growth_idx
  have hQ0_phys_sset := a7_physical_sset hΔ_pos hΔ_lt_half hs hst ht2 hε_pos h_absorb d
  have hT0_dirV_nonzero : (LemmaE.getDirV d.T0) 1 ≠ 0 := (h_slope_bound d.T0 d.hT0_in).1
  have hT0_slope_bound : |tubeSlope d.T0| ≤ 1 := (h_slope_bound d.T0 d.hT0_in).2.1
  have hT0_intercept_bound : |tubeIntercept d.T0| ≤ 3 := (h_slope_bound d.T0 d.hT0_in).2.2
  have hT0_in_Cpi : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ d.Q0),
      d.T0 ∈ (a5.perSquare Q (d.hQ0_sub_Qset hQ)).C_Q_pi := by
    intro Q hQ
    have hT_in_cpi : d.T0 ∈ a5Cpi a5 Q := d.hT0_incidence Q hQ
    have hQ_in_Qset : Q ∈ a5.Qset := d.hQ0_sub_Qset hQ
    rw [a5Cpi_eq a5 hQ_in_Qset] at hT_in_cpi
    exact (Finset.mem_inter.mp hT_in_cpi).1
  exact ⟨{
    a5 := a5
  , T0 := d.T0
  , Q0 := d.Q0
  , hQ0_sub := d.hQ0_sub_Qset
  , hT0_in_Cpi := hT0_in_Cpi
  , hT0_in_Cglobal := d.hT0_in
  , hQ0_card_lower := d.hQ0_card_lower_final
  , hQ0_sset := by
      have h_qs : IsDeltaSSet Δ d.u (Real.rpow Δ (-389 * ε)) (d.Q0 : Set (CoarseSquare Δ)) := hQ0_sset
      have h_eq : d.u = t - s := d.hu_eq
      rw [h_eq] at h_qs
      exact h_qs
  , h_pointEnergy_bound := d.A_idx
  , h_pointEnergy := by
      have h_pe : ∀ q ∈ d.Q0, pointEnergy d.u d.Q0 q ≤ d.A_idx := h_pointEnergy
      have h_eq : d.u = t - s := d.hu_eq
      intro q hq
      have h := h_pe q hq
      rw [h_eq] at h
      exact h
  , h_ballGrowth := by
      have h_bg : ∀ q ∈ d.Q0, ∀ (r : ℝ), Δ ≤ r →
          ((d.Q0.filter fun q' => dist q q' ≤ r).card : ℝ) ≤ 1 + d.A_idx * Real.rpow r d.u := h_growth_idx
      have h_eq : d.u = t - s := d.hu_eq
      intro q hq r hr
      have h := h_bg q hq r hr
      rw [h_eq] at h
      exact h
  , hT0_slope_bound := hT0_slope_bound
  , hT0_intercept_bound := hT0_intercept_bound
  , hT0_dirV_nonzero := hT0_dirV_nonzero
  , Q0_phys := d.Q0_phys
  , hQ0_phys_eq := d.hQ0_phys_eq.symm
  , hQ0_phys_sset := by
      have h_qps : IsDeltaSSet Δ d.u (Real.rpow Δ (-377 * ε)) (d.Q0_phys : Set Plane) := hQ0_phys_sset
      have h_eq : d.u = t - s := d.hu_eq
      rw [h_eq] at h_qps
      exact h_qps
  }⟩

/-- Construct a full A7_Output using physical extraction. -/
def A7_physical_full_output
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (a5 : A5_Output Δ δ s t ε)
    (hQset_bdd : ∀ p ∈ a5.Qset.image (squareCenter Δ), ‖p‖ ≤ 2)
    (hQset_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ a5.Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ a5.Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3)
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    (h_pack_absorb : (affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb : (affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^t + 1 ≤ Real.rpow Δ (-ε))
    (h_small_half : Real.rpow Δ ε ≤ 1 / 2)
    (h_small2 : 4 + 16 * (2 : ℝ)^(t - s) ≤ Real.rpow Δ (-4 * ε))
    (h_absorb : (6500 : ℝ) ≤ Real.rpow Δ (-ε))
    (h_slope_bound : ∀ T ∈ a5.C_global,
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3) :
    A7_Output Δ δ s t ε :=
  (A7_physical_full_output_main hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos
    hδ_pos hδ_le_Δ a5
    hQset_bdd hQset_le_3 h_log_absorb h_pack_absorb h_const_absorb
    h_small_half h_small2 h_absorb h_slope_bound).some

end

end DirecretisedFurstenbergEstimate.AppendixA
